import CsdLean4.Mathlib.QuantumInfo.Hadamard
import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost

/-!
# Measurement-based AND-uncomputation (Gidney's measure-and-correct gadget)

**Category:** 3-Local (QM-validity content; no CSD ontology).

This is the **amplitude-model** proof-of-concept for measurement-based uncomputation
(`specs` Tier-X measurement-adder fork, stage **L5-a**). An AND-ancilla holding `x ∧ y`
(computed earlier with a Toffoli, here entangled with the data) is uncomputed **without a
second Toffoli** by Gidney's gadget:

1. Apply Hadamard `H` to the ancilla and **measure it in the computational basis** (= an
   X-basis measurement of the original ancilla), obtaining outcome `m ∈ {0,1}` (each prob
   `1/2`). The post-measurement data picks up a phase `(-1)^{m·(x∧y)}`.
2. **Correction:** if `m = 1`, apply `CZ` to the data qubits `(x,y)`, multiplying by
   `(-1)^{x∧y}`, which cancels the phase.

Net (BOTH outcomes): the data returns to `Σ c_{xy}|x,y⟩` and the ancilla is reset to `|m⟩`
— the AND is uncomputed using **only Cliffords (H, CZ) + a measurement**, **zero Toffoli**.
That is the ~2× saving versus the unitary AND-uncompute, which costs one Toffoli.

## What is proved

- `measureUncompute_uncomputes` (THE headline): for **every** outcome `m` and **every**
  data superposition `c`, the corrected, projected state equals the uncomputed data with
  the ancilla reset to `|m⟩`, scaled by the outcome amplitude `(√2)⁻¹`. The phase
  cancellation `((-1)^{x∧y})² = 1` (the `m = 1` branch) is genuine, not asserted.
- `andInput_nontrivial`: the AND-entangled INPUT genuinely carries `a = x ∧ y`
  (non-vacuity: the uncompute is real work, not a trivial product).
- `gadgetGateList_zero_toffoli`: the gadget's gate list contains no Toffoli, whereas the
  unitary AND-uncompute contains one.
- `gadgetGateList_denotes_measureUncompute` (**L5-b, the operator↔list link**): folding the
  interpretation `GadgetGate.denote` of `gadgetGateList` (`hGate ↦ hadA`, `measGate ↦ projA m`,
  `czGate ↦ correctionMat m`) reproduces the `measureUncompute m` operator **exactly**. The
  equality is **definitional** (`rfl`): `measureUncompute m` is by definition the composition
  `correctionMat m ∘ projA m ∘ hadA`, so the cost-bearing gate list is a genuine decomposition
  of the operator, not a free-standing list.
- `measureUncompute_cost` (**L5-b, the 0-vs-1 Toffoli saving as an operator property**): the
  decomposition `gadgetGateList` of the `measureUncompute` operator has Toffoli count `0` (plus
  `1` measurement and `1` CNOT-equivalent for the conditional CZ, all single-qubit Cliffords
  free), whereas the unitary AND-uncompute's decomposition has Toffoli count `1`. The
  Toffoli-free property is now a property of the **operator** (via the link), not of a
  hand-written list.

## Representation choice

We use the **per-outcome partial-isometry** form (not a full CPTP `Channel`): on the
explicit 3-qubit space `QReg 3 = EuclideanSpace ℂ (Fin 3 → Fin 2)` (qubit `0 = x`,
`1 = y`, `2 = a`), each step is a `Matrix.toEuclideanLin` application — Hadamard on the
ancilla (`hadA`, entries the corpus `hadEntry = qmH`), the computational projector
(`projA m`), and the conditional CZ on the data (`correctionMat m`, `= qmCZ`-phase). This
is the cleanest faithful form the amplitude machinery supports; the X-basis phases are why
this lives in the amplitude model and NOT the Boolean reversible DSL.

## Scope (honest)

**L5-a** settled that measurement-based uncomputation is *verifiable in Lean* in the amplitude
model. **L5-b** (this file) closes the operator↔list gap: `gadgetGateList` is now **proven**
(definitionally) to be the decomposition of `measureUncompute`, so the 0-Toffoli cost is a
property of the *operator*, not a hand-written list, and the ~2× saving is stated in the corpus
`Reversible.Cost` model (0 Toffoli + 1 measurement + Cliffords, vs 1 Toffoli for the unitary
uncompute). This is a **per-AND-uncompute gate-cost** statement only. **Deferred:** L5-c (the
Boolean-arithmetic ↔ amplitude bridge — applying this to actual adders, the trusted-base
increase, the wall), L5-d (the measurement-based adder + circuit re-cost). No ECDSA resource
claim is made here.
-/

open scoped Matrix
open QuantumInfo
open CSD.Empirical.QM.Gates

namespace CSD.Empirical.QM

/-- The 3-qubit computational index type (`x`, `y`, ancilla `a`). -/
abbrev B3 := Fin 3 → Fin 2

/-! ## Coordinate primitives for `Matrix.toEuclideanLin` on `QReg 3` -/

/-- A diagonal register operator acts pointwise on amplitudes. -/
lemma toEuclideanLin_diagonal_apply (d : B3 → ℂ) (v : QReg 3) (z : B3) :
    Matrix.toEuclideanLin (Matrix.diagonal d) v z = d z * v z := by
  rw [Matrix.toLpLin_apply]
  simp [Matrix.mulVec_diagonal]

/-- A register operator applied to a computational basis state reads off the `w`-th column. -/
lemma toEuclideanLin_basisState (A : Matrix B3 B3 ℂ) (w z : B3) :
    Matrix.toEuclideanLin A (basisState w) z = A z w := by
  rw [Matrix.toLpLin_apply]
  show (A *ᵥ (basisState w).ofLp) z = A z w
  simp only [basisState, show (EuclideanSpace.single w (1 : ℂ)).ofLp = Pi.single w 1 from rfl,
    Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul]

/-- Coordinatewise scalar multiplication on `QReg 3`. -/
lemma smul_coord (c : ℂ) (v : QReg 3) (z : B3) : (c • v) z = c * v z := by
  simp

/-- Pointwise characterisation of a 3-qubit bitstring equality. -/
lemma b3_eq_iff (z : B3) (x y m : Fin 2) :
    z = ![x, y, m] ↔ z 0 = x ∧ z 1 = y ∧ z 2 = m := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext i; fin_cases i <;> simp_all

/-! ## The gadget components (gates on the 3-qubit register) -/

/-- The CZ phase on the data qubits: `(-1)^{x∧y}` (`x∧y = x·y` on `Fin 2`). -/
def czPhase (x y : Fin 2) : ℂ := (-1) ^ ((x : ℕ) * (y : ℕ))

/-- **Hadamard on the ancilla** (qubit 2), identity on the data qubits `(0,1)`. Its
qubit-2 block entries are the corpus single-qubit Hadamard entries (`hadEntry = qmH`). -/
noncomputable def hadA : Matrix B3 B3 ℂ :=
  Matrix.of fun z w => if z 0 = w 0 ∧ z 1 = w 1 then hadEntry (z 2) (w 2) else 0

lemma hadA_apply (z w : B3) :
    hadA z w = if z 0 = w 0 ∧ z 1 = w 1 then hadEntry (z 2) (w 2) else 0 := rfl

/-- **Computational projector** onto ancilla outcome `m` (the X-basis measurement after the
Hadamard). -/
noncomputable def projA (m : Fin 2) : Matrix B3 B3 ℂ :=
  Matrix.diagonal (fun z => if z 2 = m then 1 else 0)

/-- The **CZ on the data qubits** as a diagonal register operator: phase `(-1)^{x∧y}`. -/
noncomputable def czXY : Matrix B3 B3 ℂ :=
  Matrix.diagonal (fun z => czPhase (z 0) (z 1))

/-- **The conditional correction**: `CZ` on the data when `m = 1`, identity when `m = 0`. -/
noncomputable def correctionMat (m : Fin 2) : Matrix B3 B3 ℂ :=
  Matrix.diagonal (fun z => if m = 1 then czPhase (z 0) (z 1) else 1)

/-- The correction at outcome `1` is exactly the data CZ. -/
lemma correctionMat_one : correctionMat 1 = czXY := by
  simp [correctionMat, czXY]

/-- The correction at outcome `0` is the identity (no Toffoli, no Clifford applied). -/
lemma correctionMat_zero : correctionMat 0 = 1 := by
  simp [correctionMat, Matrix.diagonal_one]

/-- **The AND-entangled index** `![x, y, x∧y]`: data `(x,y)` with the ancilla carrying the
AND. -/
def andIdx (x y : Fin 2) : B3 := ![x, y, x * y]

@[simp] lemma andIdx_zero (x y : Fin 2) : andIdx x y 0 = x := rfl
@[simp] lemma andIdx_one (x y : Fin 2) : andIdx x y 1 = y := rfl
@[simp] lemma andIdx_two (x y : Fin 2) : andIdx x y 2 = x * y := rfl

/-! ## The gadget and the input/output states -/

/-- **The measure-and-correct gadget**, per outcome `m`: Hadamard the ancilla, project onto
ancilla `= m` (the X-basis measurement), then apply the `m`-conditional CZ correction. -/
noncomputable def measureUncompute (m : Fin 2) (ψ : QReg 3) : QReg 3 :=
  Matrix.toEuclideanLin (correctionMat m)
    (Matrix.toEuclideanLin (projA m)
      (Matrix.toEuclideanLin hadA ψ))

/-- **The AND-entangled input state** `Σ_{x,y} c_{xy} |x, y, x∧y⟩`: a data superposition
with the ancilla holding `x ∧ y` for each branch. -/
noncomputable def andInput (c : Fin 2 → Fin 2 → ℂ) : QReg 3 :=
  ∑ x : Fin 2, ∑ y : Fin 2, c x y • basisState (andIdx x y)

/-- **The uncomputed data**, ancilla reset to `|m⟩`: `Σ_{x,y} c_{xy} |x, y, m⟩`. -/
noncomputable def uncomputedData (c : Fin 2 → Fin 2 → ℂ) (m : Fin 2) : QReg 3 :=
  ∑ x : Fin 2, ∑ y : Fin 2, c x y • basisState ![x, y, m]

/-! ## Reuse / honesty bridges to the corpus Clifford gates -/

/-- The ancilla-Hadamard block entries are the corpus single-qubit Hadamard `qmH`. -/
lemma hadEntry_eq_qmH (a b : Fin 2) : hadEntry a b = qmH a b := by
  fin_cases a <;> fin_cases b <;>
    simp [hadEntry, qmH, Matrix.smul_apply] <;> ring

/-- The data-CZ phase matches the corpus controlled-Z `qmCZ` on its diagonal (phase flip on
`|11⟩`): the four computational diagonal values agree. -/
lemma czPhase_eq_qmCZ_diag :
    czPhase 0 0 = qmCZ 0 0 ∧ czPhase 0 1 = qmCZ 1 1 ∧
    czPhase 1 0 = qmCZ 2 2 ∧ czPhase 1 1 = qmCZ 3 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [czPhase, qmCZ, Matrix.of_apply]

/-! ## Per-component apply lemmas -/

lemma corr_apply (m : Fin 2) (v : QReg 3) (z : B3) :
    Matrix.toEuclideanLin (correctionMat m) v z
      = (if m = 1 then czPhase (z 0) (z 1) else 1) * v z := by
  rw [correctionMat, toEuclideanLin_diagonal_apply]

lemma proj_apply (m : Fin 2) (v : QReg 3) (z : B3) :
    Matrix.toEuclideanLin (projA m) v z = (if z 2 = m then 1 else 0) * v z := by
  rw [projA, toEuclideanLin_diagonal_apply]

/-- The `m = 0` numeric branch: the Hadamard projects the ancilla onto `|0⟩` with amplitude
`(√2)⁻¹`, independent of the data. -/
lemma hadEntry_zero_left (c : Fin 2) : hadEntry 0 c = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [hadEntry]

/-- **The genuine phase cancellation** (the `m = 1` branch): the `(-1)^{x∧y}` phase picked up
by the `|1⟩` projection is exactly cancelled by the data CZ, leaving amplitude `(√2)⁻¹` for
every data branch `(x,y)`. This is `((-1)^{x∧y})² = 1`. -/
lemma czPhase_mul_hadEntry (x y : Fin 2) :
    czPhase x y * hadEntry 1 (x * y) = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases x <;> fin_cases y <;> simp [czPhase, hadEntry] <;> ring

/-- The combined correction × Hadamard-projection amplitude, both outcomes: `(√2)⁻¹` for
every `m` and every data branch `(x,y)`. The `m = 0` branch is the clean projection
(`hadEntry_zero_left`); the `m = 1` branch is the genuine phase cancellation
(`czPhase_mul_hadEntry`). -/
lemma corr_had_eq (m x y : Fin 2) :
    (if m = 1 then czPhase x y else 1) * hadEntry m (x * y) = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases m
  · simpa using hadEntry_zero_left (x * y)
  · simpa using czPhase_mul_hadEntry x y

/-! ## The headline: per-basis correctness (genuine phase cancellation) -/

/-- **Per-basis-state uncompute.** For every outcome `m` and every data basis branch
`(x,y)`, the gadget maps the AND-entangled basis state `|x, y, x∧y⟩` to `(√2)⁻¹ |x, y, m⟩`
— data unchanged, ancilla reset, outcome-independent after the `m = 1` CZ correction. The
`m = 1` case is the genuine phase cancellation `czPhase x y · hadEntry 1 (x∧y) = (√2)⁻¹`. -/
lemma measureUncompute_basisState (m x y : Fin 2) :
    measureUncompute m (basisState (andIdx x y))
      = (Real.sqrt 2 : ℂ)⁻¹ • basisState ![x, y, m] := by
  ext z
  rw [measureUncompute, corr_apply, proj_apply, toEuclideanLin_basisState, hadA_apply,
    smul_coord, basisState_apply]
  simp only [andIdx_zero, andIdx_one, andIdx_two, b3_eq_iff]
  by_cases h0 : z 0 = x
  · by_cases h1 : z 1 = y
    · by_cases h2 : z 2 = m
      · rw [h0, h1, h2]
        simp only [and_self, if_true, one_mul, mul_one]
        exact corr_had_eq m x y
      · simp [h2]
    · simp [h1]
  · simp [h0]

/-! ## Linearity wrappers -/

lemma measureUncompute_smul (m : Fin 2) (a : ℂ) (v : QReg 3) :
    measureUncompute m (a • v) = a • measureUncompute m v := by
  simp only [measureUncompute, map_smul]

lemma measureUncompute_sum {ι : Type*} (s : Finset ι) (f : ι → QReg 3) (m : Fin 2) :
    measureUncompute m (∑ i ∈ s, f i) = ∑ i ∈ s, measureUncompute m (f i) := by
  simp only [measureUncompute, map_sum]

/-! ## THE headline theorem -/

/-- **`measureUncompute_uncomputes` (the deliverable).** For **every** measurement outcome
`m` and **every** data superposition `c`, the measure-and-correct gadget maps the
AND-entangled state `Σ c_{xy}|x,y⟩|x∧y⟩` to the uncomputed data with the ancilla reset to
`|m⟩`, `Σ c_{xy}|x,y⟩|m⟩`, scaled by the outcome amplitude `(√2)⁻¹`. The result is
**outcome-independent** (the `m = 1` CZ correction cancels the `(-1)^{x∧y}` phase): this is
the net "identity-on-data ⊗ ancilla-reset". -/
theorem measureUncompute_uncomputes (m : Fin 2) (c : Fin 2 → Fin 2 → ℂ) :
    measureUncompute m (andInput c) = (Real.sqrt 2 : ℂ)⁻¹ • uncomputedData c m := by
  rw [andInput, uncomputedData, Finset.smul_sum, measureUncompute_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [measureUncompute_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [measureUncompute_smul, measureUncompute_basisState, smul_comm]

/-! ## Non-vacuity: the AND ancilla is genuinely set -/

/-- **Non-vacuity.** The AND-entangled input genuinely carries `a = x ∧ y`: on the `|1,1⟩`
data branch the ancilla is `|1⟩` (the AND is set), so the entangled basis state is distinct
from the ancilla-reset state — the uncompute is real work, not a trivial product. -/
theorem andInput_nontrivial :
    andIdx 1 1 2 = 1 ∧ basisState (andIdx 1 1) ≠ basisState (![1, 1, 0] : B3) := by
  refine ⟨rfl, ?_⟩
  intro h
  have hne : andIdx 1 1 ≠ (![1, 1, 0] : B3) := by decide
  have hcoord := congrArg (fun v : QReg 3 => v (andIdx 1 1)) h
  simp only [basisState_apply, if_neg hne] at hcoord
  exact one_ne_zero hcoord

/-! ## Cost: zero Toffoli (the ~2× saving) -/

/-- An abstract gadget gate label, used only to state the Toffoli-count cost point. -/
inductive GadgetGate
  | hGate
  | czGate
  | measGate
  | toffoli
  deriving DecidableEq

/-- Whether a gate is a Toffoli. -/
def GadgetGate.isToffoli : GadgetGate → Bool
  | .toffoli => true
  | _ => false

/-- The measure-and-correct gadget's gate list: Hadamard, measurement, conditional CZ —
all Cliffords + a measurement, **no Toffoli**. -/
def gadgetGateList : List GadgetGate := [.hGate, .measGate, .czGate]

/-- The unitary AND-uncompute's gate list: one Toffoli. -/
def unitaryUncomputeGateList : List GadgetGate := [.toffoli]

/-- **The cost point (list form).** The measure-and-correct gadget's gate LIST (`[H, Meas, CZ]`)
contains **no Toffoli**, whereas the unitary AND-uncompute's list contains exactly one — the ~2×
(one-Toffoli) saving. This is a count over the gate lists; L5-b (`measureUncompute_cost` below)
upgrades it to a property of the `measureUncompute` OPERATOR via the link
`gadgetGateList_denotes_measureUncompute`. -/
theorem gadgetGateList_zero_toffoli :
    gadgetGateList.countP GadgetGate.isToffoli = 0 ∧
    unitaryUncomputeGateList.countP GadgetGate.isToffoli = 1 := by
  decide

/-! ## L5-b: the operator↔list link and the cost as an operator property -/

/-- **Interpretation of a gadget gate** as a register operator on `QReg 3`, parameterised by the
measurement outcome `m`: `hGate ↦ hadA`, `measGate ↦ projA m`, `czGate ↦ correctionMat m` (the
three `Matrix.toEuclideanLin` blocks that *define* `measureUncompute`). The `toffoli` label maps
to `id` — it is not part of *this* gadget's decomposition (it is the unitary route's gate), so it
plays no role in `gadgetGateList`; it is given a denotation only for totality. -/
noncomputable def GadgetGate.denote (g : GadgetGate) (m : Fin 2) : QReg 3 → QReg 3 :=
  match g with
  | .hGate => fun ψ => Matrix.toEuclideanLin hadA ψ
  | .measGate => fun ψ => Matrix.toEuclideanLin (projA m) ψ
  | .czGate => fun ψ => Matrix.toEuclideanLin (correctionMat m) ψ
  | .toffoli => id

/-- **Fold a gadget gate list into an operator**, applying gates left-to-right (head first). -/
noncomputable def denoteGadgetList (m : Fin 2) : List GadgetGate → QReg 3 → QReg 3
  | [], ψ => ψ
  | g :: gs, ψ => denoteGadgetList m gs (g.denote m ψ)

/-- **The operator↔list link (L5-b, the honesty fix).** Folding the interpretation of the
cost-bearing gate list `gadgetGateList = [hGate, measGate, czGate]` reproduces the
`measureUncompute m` operator **exactly**, for every input `ψ`.

This equality is **definitional** (`rfl`): `measureUncompute m ψ` is by definition the
composition `correctionMat m ∘ projA m ∘ hadA` applied to `ψ`, and `denoteGadgetList m
gadgetGateList ψ` unfolds to that same composition. The point is not a deep proof but to **tie**
the Toffoli-count statement (`gadgetGateList_zero_toffoli`) to the operator: `gadgetGateList` is a
genuine decomposition of `measureUncompute`, not a free-standing list. -/
theorem gadgetGateList_denotes_measureUncompute (m : Fin 2) (ψ : QReg 3) :
    denoteGadgetList m gadgetGateList ψ = measureUncompute m ψ := rfl

/-- **Per-gate fault-tolerant cost** in the corpus `Reversible.Cost` model. Following the corpus
convention (`Reversible.gateCost`: single-qubit Clifford `X` is *free*, two-qubit Clifford `CX`
costs one CNOT, `CCX` costs one Toffoli — the FT-expensive resource), the amplitude gadget gates
are billed: `hGate` (single-qubit Clifford) free; `czGate` (two-qubit Clifford CZ ≃ CNOT up to
single-qubit Cliffords) one CNOT; `measGate` one measurement; `toffoli` one Toffoli. No gate here
incurs a `T`-count beyond the Toffoli's own (kept in the `toffoli` field, Pass-1 model). -/
def gadgetGateCost : GadgetGate → Reversible.Cost
  | .hGate => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 0, tCount := 0, meas := 0 }
  | .czGate => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 1, tCount := 0, meas := 0 }
  | .measGate => { qubits := 0, ancilla := 0, toffoli := 0, toffoliDepth := 0, cnot := 0, tCount := 0, meas := 1 }
  | .toffoli => { qubits := 0, ancilla := 0, toffoli := 1, toffoliDepth := 1, cnot := 0, tCount := 0, meas := 0 }

/-- **The cost as an operator property (L5-b, the ~2× saving).** Via the link
`gadgetGateList_denotes_measureUncompute`, the decomposition `gadgetGateList` of the
`measureUncompute` operator costs, in the corpus `Reversible.Cost` model:

- **Toffoli `0`** (the FT-expensive resource) — `gadgetGateList` is Toffoli-free as an operator;
- **measurement `1`** — the single X-basis ancilla measurement;
- **CNOT `1`** — the conditional CZ correction (a two-qubit Clifford, counted but cheap);

whereas the unitary AND-uncompute's decomposition `unitaryUncomputeGateList` costs **Toffoli `1`**.
So the measurement-based route **saves the Toffoli** (0 vs 1) at the cost of one measurement plus
Cliffords — the ~2× per-AND-uncompute saving, with the measurement and Cliffords accounted as real
but cheap resources and the Toffoli as the FT-expensive one.

**Honest scope:** this is a **per-AND-uncompute gate-cost** statement. It is *not* an adder- or
circuit-level re-cost (that is L5-d), and it does not yet apply the gadget to Boolean arithmetic
(that is L5-c, the amplitude↔Boolean bridge wall). -/
theorem measureUncompute_cost :
    (gadgetGateList.map (fun g => (gadgetGateCost g).toffoli)).sum = 0 ∧
    (gadgetGateList.map (fun g => (gadgetGateCost g).meas)).sum = 1 ∧
    (gadgetGateList.map (fun g => (gadgetGateCost g).cnot)).sum = 1 ∧
    (unitaryUncomputeGateList.map (fun g => (gadgetGateCost g).toffoli)).sum = 1 := by
  decide

/-- **The Toffoli-free property of the operator (L5-b headline).** There is a decomposition of the
`measureUncompute m` operator (namely `gadgetGateList`, by `gadgetGateList_denotes_measureUncompute`)
whose `Reversible.Cost` Toffoli count is `0`. The 0-Toffoli is thus a property of the **operator**,
not of a free-standing gate list. -/
theorem measureUncompute_toffoli_eq_zero (m : Fin 2) :
    (∀ ψ : QReg 3, denoteGadgetList m gadgetGateList ψ = measureUncompute m ψ) ∧
      (gadgetGateList.map (fun g => (gadgetGateCost g).toffoli)).sum = 0 :=
  ⟨gadgetGateList_denotes_measureUncompute m, by decide⟩

end CSD.Empirical.QM
