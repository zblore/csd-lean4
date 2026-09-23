/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.Lift
public import CsdLean4.Mathlib.QuantumInfo.Hadamard

/-!
# Hybrid circuits: reversible gates and measure-and-correct gadgets on the full register

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

`Lift.lean` embeds one CCX into `QReg m` as a permutation matrix and notes that a mid-circuit
measurement gadget is **not** a permutation, so the basis-state induction that lifts a
permutation circuit "breaks at the replaced block". This module closes that gap without the
tensor factorisation the note anticipated: the gadget, per outcome, is a **monomial** operator —
it sends every computational basis state to a scalar multiple of a basis state — so the
induction goes through with a scalar carried along.

* `gateMat g` — **the general lift of a reversible gate**: the permutation matrix of its Boolean
  action `denoteGate g`, recast through `stateOfReg`/`regOfState`; `gateMat_basisState` is the
  basis-state rule, and `gateMat_CCX` checks it against the hand-built CCX unitary `ccxAtMat`.
* `measureCorrectMat pairs g mo` — **the measure-and-correct gadget** on the ancilla `g`, per
  outcome `mo`: Hadamard on `g`, projection of `g` onto `mo`, then a CZ on each pair of `pairs`
  when `mo = 1`. On a basis state it is `(phase · ⟨mo|H|w g⟩) • |update w g mo⟩`
  (`measureCorrectMat_basisState`); when the ancilla holds the parity of ANDs the corrections
  cancel, `w g = andParity pairs w`, the scalar is `(√2)⁻¹` for both outcomes
  (`measureCorrect_scalar`) — the genuine phase cancellation `((−1)^{p})² = 1`; when it does
  not, the `mo = 1` branch carries the sign `−(√2)⁻¹` (`measureCorrect_scalar_of_ne`) — the
  reason a gadget must be matched to what its ancilla holds.
* `HybridGate`, `hybridLin`, `shadow`, `WellFormed`, `gadgetCount` — a hybrid gate list, its
  register semantics (a linear map, first gate first), its **Boolean shadow** (a reversible gate
  acts by `denoteGate`, a gadget writes its outcome into the ancilla), and the well-formedness of
  a run on a basis input (every gadget meets an ancilla holding the parity its corrections
  cancel, on wires its corrections avoid).
* ★ `hybridLin_basisState` — **the hybrid amplitude equality**: on a well-formed basis input the
  hybrid circuit produces `(√2)⁻¹^{#gadgets} • |shadow⟩`; `hybridLin_sum` extends it by
  linearity to superpositions of well-formed inputs.

The consumer is the AND-adder with its Toffoli-free uncompute pass
(`Empirical/QM/MeasurementAdderHybrid.lean`), where the gadgets are matched to the majority
ancillas of the carry cells.

## Honest scope

The gadget is represented per outcome (a partial isometry), as in the measurement-gadget
modules it generalises; the two outcomes have probability `1/2` each, which the scalar
`(√2)⁻¹` records. Nothing here is about noise or about gate decompositions: `gateMat` is the
permutation a reversible gate *is* on the computational basis, and a hybrid list is costed by
its consumers.
-/

@[expose] public section

open scoped Matrix
open QuantumInfo

namespace Reversible

variable {m : ℕ}

/-! ## The recasts round-trip -/

@[simp] lemma stateOfReg_regOfState (s : State m) : stateOfReg (regOfState s) = s := by
  funext i
  cases h : s i <;> simp [stateOfReg, regOfState, h]

@[simp] lemma regOfState_stateOfReg (w : Fin m → Fin 2) : regOfState (stateOfReg w) = w := by
  funext i
  simp only [stateOfReg, regOfState]
  exact b3OfState_decide (w i)

/-! ## The general lift of a reversible gate -/

/-- **The permutation matrix of a reversible gate** on `QReg m`: the basis state `w` goes to the
basis state of the gate's Boolean action on `w`. -/
noncomputable def gateMat (g : Gate m) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  Matrix.of fun z w => if z = regOfState (denoteGate g (stateOfReg w)) then 1 else 0

lemma gateMat_apply (g : Gate m) (z w : Fin m → Fin 2) :
    gateMat g z w = if z = regOfState (denoteGate g (stateOfReg w)) then 1 else 0 := rfl

/-- The lifted gate permutes basis states by the gate's Boolean action. -/
lemma gateMat_basisState (g : Gate m) (w : Fin m → Fin 2) :
    Matrix.toEuclideanLin (gateMat g) (basisState w)
      = basisState (regOfState (denoteGate g (stateOfReg w))) := by
  ext z
  rw [toEuclideanLin_basisState_m, gateMat_apply, basisState_apply]

/-- The general lift agrees with the hand-built CCX unitary of `Lift.lean`. -/
lemma gateMat_CCX (wa wb wg : Fin m) (hga : wg ≠ wa) (hgb : wg ≠ wb) :
    gateMat (.CCX wa wb wg) = ccxAtMat wa wb wg := by
  ext z w
  rw [gateMat_apply, ccxAtMat_apply, ccxAt_eq_denote_recast wa wb wg hga hgb]
  rfl

/-! ## The measure-and-correct gadget at arbitrary wires -/

/-- The parity of ANDs a correction list reads: `⊕_{(x,y) ∈ pairs} w x ∧ w y`, as a `Fin 2`. -/
def andParity (pairs : List (Fin m × Fin m)) (w : Fin m → Fin 2) : Fin 2 :=
  (pairs.map fun p => w p.1 * w p.2).sum

/-- The correction phase at outcome `mo`: `(−1)^{mo · ⊕ ANDs}` — a CZ on each pair when
`mo = 1`, nothing when `mo = 0`. -/
def correctionPhase (pairs : List (Fin m × Fin m)) (mo : Fin 2) (w : Fin m → Fin 2) : ℂ :=
  (-1) ^ ((mo : ℕ) * (andParity pairs w : ℕ))

lemma neg_one_pow_fin_add (a b : Fin 2) :
    ((-1 : ℂ) ^ ((a + b : Fin 2) : ℕ)) = (-1) ^ (a : ℕ) * (-1) ^ (b : ℕ) := by
  rw [Fin.val_add, ← pow_add, neg_one_pow_eq_pow_mod_two (n := (a : ℕ) + b)]

lemma neg_one_pow_fin_mul (a b : Fin 2) :
    ((-1 : ℂ) ^ ((a * b : Fin 2) : ℕ)) = (-1) ^ ((a : ℕ) * (b : ℕ)) := by
  rw [Fin.val_mul, neg_one_pow_eq_pow_mod_two (n := (a : ℕ) * b)]

/-- The correction at outcome `1` is the product of the per-pair CZ phases. -/
lemma correctionPhase_one_eq_prod (pairs : List (Fin m × Fin m)) (w : Fin m → Fin 2) :
    correctionPhase pairs 1 w
      = (pairs.map fun p => ((-1 : ℂ) ^ ((w p.1 : ℕ) * (w p.2 : ℕ)))).prod := by
  unfold correctionPhase andParity
  induction pairs with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, ← ih,
      show ((1 : Fin 2) : ℕ) = 1 from rfl, one_mul, one_mul, neg_one_pow_fin_add,
      neg_one_pow_fin_mul]

/-- **The measure-and-correct gadget** on the ancilla wire `g` of `QReg m`, per outcome `mo`:
Hadamard on `g`, projection of `g` onto `mo`, then a CZ on each pair of `pairs` if `mo = 1`.
Entry `(z, w)`: nonzero only for `z = update w g mo`, where it is the correction phase at `z`
times the Hadamard entry `⟨mo|H|w g⟩`. -/
noncomputable def measureCorrectMat (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  Matrix.of fun z w =>
    if z = Function.update w g mo then correctionPhase pairs mo z * hadEntry mo (w g) else 0

lemma measureCorrectMat_apply (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2)
    (z w : Fin m → Fin 2) :
    measureCorrectMat pairs g mo z w
      = if z = Function.update w g mo then correctionPhase pairs mo z * hadEntry mo (w g)
        else 0 := rfl

/-- **The gadget is monomial:** a basis state goes to a scalar multiple of a basis state. -/
lemma measureCorrectMat_basisState (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2)
    (w : Fin m → Fin 2) :
    Matrix.toEuclideanLin (measureCorrectMat pairs g mo) (basisState w)
      = (correctionPhase pairs mo (Function.update w g mo) * hadEntry mo (w g))
          • basisState (Function.update w g mo) := by
  ext z
  rw [toEuclideanLin_basisState_m, PiLp.smul_apply, basisState_apply, smul_eq_mul,
    measureCorrectMat_apply]
  by_cases h : z = Function.update w g mo
  · rw [if_pos h, if_pos h, h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Corrections that avoid the ancilla read the same parity before and after the reset. -/
lemma andParity_update_of_forall_ne (pairs : List (Fin m × Fin m)) {g : Fin m}
    (hg : ∀ p ∈ pairs, p.1 ≠ g ∧ p.2 ≠ g) (w : Fin m → Fin 2) (mo : Fin 2) :
    andParity pairs (Function.update w g mo) = andParity pairs w := by
  unfold andParity
  congr 1
  refine List.map_congr_left fun p hp => ?_
  rw [Function.update_of_ne (hg p hp).1, Function.update_of_ne (hg p hp).2]

/-- **The gadget scalar on a well-formed input.** If the ancilla holds the parity its
corrections cancel, the scalar is `(√2)⁻¹` for both outcomes: the projection phase
`(−1)^{mo · w g}` and the correction phase `(−1)^{mo · parity}` cancel. -/
lemma measureCorrect_scalar (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2)
    (w : Fin m → Fin 2) (hg : ∀ p ∈ pairs, p.1 ≠ g ∧ p.2 ≠ g)
    (hw : w g = andParity pairs w) :
    correctionPhase pairs mo (Function.update w g mo) * hadEntry mo (w g)
      = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [correctionPhase, andParity_update_of_forall_ne pairs hg, ← hw, hadEntry, div_eq_mul_inv,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **The sign flip on an ill-formed input.** If the ancilla does not hold the parity the
corrections cancel, the `mo = 1` branch carries `−(√2)⁻¹`: a data-dependent relative phase. -/
lemma measureCorrect_scalar_of_ne (pairs : List (Fin m × Fin m)) (g : Fin m)
    (w : Fin m → Fin 2) (hg : ∀ p ∈ pairs, p.1 ≠ g ∧ p.2 ≠ g)
    (hw : w g ≠ andParity pairs w) :
    correctionPhase pairs 1 (Function.update w g 1) * hadEntry 1 (w g)
      = -(Real.sqrt 2 : ℂ)⁻¹ := by
  rw [correctionPhase, andParity_update_of_forall_ne pairs hg, hadEntry]
  revert hw
  generalize w g = x
  generalize andParity pairs w = y
  intro hw
  fin_cases x <;> fin_cases y <;> simp at hw ⊢
  rw [neg_div, one_div]

/-! ## Hybrid gate lists -/

/-- A hybrid gate: a reversible gate, or a measure-and-correct gadget with its outcome. -/
inductive HybridGate (m : ℕ)
  /-- A reversible gate, lifted as a permutation. -/
  | gate (g : Gate m)
  /-- The measure-and-correct gadget on ancilla `g` with corrections `pairs`, at outcome `mo`. -/
  | measure (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2)

/-- The register operator of a hybrid gate. -/
noncomputable def HybridGate.mat : HybridGate m → Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ
  | .gate g => gateMat g
  | .measure pairs g mo => measureCorrectMat pairs g mo

/-- The Boolean shadow of a hybrid gate on register indices: a reversible gate acts by its
`denoteGate`, a gadget writes its outcome into the ancilla. -/
def HybridGate.shadow : HybridGate m → (Fin m → Fin 2) → (Fin m → Fin 2)
  | .gate g, w => regOfState (denoteGate g (stateOfReg w))
  | .measure _ g mo, w => Function.update w g mo

/-- The register semantics of a hybrid gate list, first gate first. -/
noncomputable def hybridLin : List (HybridGate m) → (QReg m →ₗ[ℂ] QReg m)
  | [] => LinearMap.id
  | h :: rest => (hybridLin rest).comp (Matrix.toEuclideanLin h.mat)

lemma hybridLin_nil (ψ : QReg m) : hybridLin ([] : List (HybridGate m)) ψ = ψ := rfl

lemma hybridLin_cons (h : HybridGate m) (rest : List (HybridGate m)) (ψ : QReg m) :
    hybridLin (h :: rest) ψ = hybridLin rest (Matrix.toEuclideanLin h.mat ψ) := rfl

lemma hybridLin_append (l₁ l₂ : List (HybridGate m)) (ψ : QReg m) :
    hybridLin (l₁ ++ l₂) ψ = hybridLin l₂ (hybridLin l₁ ψ) := by
  induction l₁ generalizing ψ with
  | nil => rfl
  | cons h rest ih => rw [List.cons_append, hybridLin_cons, hybridLin_cons, ih]

/-- The Boolean shadow of a hybrid gate list. -/
def shadow (l : List (HybridGate m)) (w : Fin m → Fin 2) : Fin m → Fin 2 :=
  l.foldl (fun w h => h.shadow w) w

lemma shadow_nil (w : Fin m → Fin 2) : shadow ([] : List (HybridGate m)) w = w := rfl

lemma shadow_cons (h : HybridGate m) (rest : List (HybridGate m)) (w : Fin m → Fin 2) :
    shadow (h :: rest) w = shadow rest (h.shadow w) := rfl

lemma shadow_append (l₁ l₂ : List (HybridGate m)) (w : Fin m → Fin 2) :
    shadow (l₁ ++ l₂) w = shadow l₂ (shadow l₁ w) := by
  simp only [shadow, List.foldl_append]

/-- The number of gadgets in a hybrid gate list. -/
def gadgetCount : List (HybridGate m) → ℕ
  | [] => 0
  | .gate _ :: rest => gadgetCount rest
  | .measure _ _ _ :: rest => gadgetCount rest + 1

/-- **Well-formed run on a basis input:** every gadget meets an ancilla holding the parity its
corrections cancel, on wires its corrections avoid. -/
def WellFormed : List (HybridGate m) → (Fin m → Fin 2) → Prop
  | [], _ => True
  | .gate g :: rest, w => WellFormed rest (regOfState (denoteGate g (stateOfReg w)))
  | .measure pairs g mo :: rest, w =>
      (∀ p ∈ pairs, p.1 ≠ g ∧ p.2 ≠ g) ∧ w g = andParity pairs w
        ∧ WellFormed rest (Function.update w g mo)

lemma wellFormed_nil (w : Fin m → Fin 2) : WellFormed ([] : List (HybridGate m)) w := trivial

lemma wellFormed_gate_cons (g : Gate m) (rest : List (HybridGate m)) (w : Fin m → Fin 2) :
    WellFormed (.gate g :: rest) w ↔ WellFormed rest (regOfState (denoteGate g (stateOfReg w))) :=
  Iff.rfl

lemma wellFormed_measure_cons (pairs : List (Fin m × Fin m)) (g : Fin m) (mo : Fin 2)
    (rest : List (HybridGate m)) (w : Fin m → Fin 2) :
    WellFormed (.measure pairs g mo :: rest) w
      ↔ (∀ p ∈ pairs, p.1 ≠ g ∧ p.2 ≠ g) ∧ w g = andParity pairs w
          ∧ WellFormed rest (Function.update w g mo) :=
  Iff.rfl

/-! ## ★ The hybrid amplitude equality -/

/-- ★ **The hybrid amplitude equality on a well-formed basis input.** The hybrid circuit sends
the basis state `w` to `(√2)⁻¹^{#gadgets} • |shadow⟩`: each reversible gate permutes the basis
state, each gadget resets its ancilla to the outcome and contributes the scalar `(√2)⁻¹`. -/
theorem hybridLin_basisState : ∀ (l : List (HybridGate m)) (w : Fin m → Fin 2),
    WellFormed l w →
      hybridLin l (basisState w)
        = ((Real.sqrt 2 : ℂ)⁻¹) ^ gadgetCount l • basisState (shadow l w)
  | [], w, _ => by rw [hybridLin_nil, shadow_nil, gadgetCount, pow_zero, one_smul]
  | .gate g :: rest, w, h => by
    rw [wellFormed_gate_cons] at h
    rw [hybridLin_cons, HybridGate.mat, gateMat_basisState, hybridLin_basisState rest _ h,
      shadow_cons, HybridGate.shadow, gadgetCount]
  | .measure pairs g mo :: rest, w, h => by
    rw [wellFormed_measure_cons] at h
    obtain ⟨hg, hw, h⟩ := h
    rw [hybridLin_cons, HybridGate.mat, measureCorrectMat_basisState, map_smul,
      hybridLin_basisState rest _ h, measureCorrect_scalar pairs g mo w hg hw, smul_smul,
      shadow_cons, HybridGate.shadow, gadgetCount, pow_succ']

/-- The hybrid amplitude equality on a superposition of well-formed basis inputs. -/
theorem hybridLin_sum {ι : Type*} (l : List (HybridGate m)) (S : Finset ι)
    (c : ι → ℂ) (w : ι → Fin m → Fin 2) (h : ∀ i ∈ S, WellFormed l (w i)) :
    hybridLin l (∑ i ∈ S, c i • basisState (w i))
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ gadgetCount l
          • ∑ i ∈ S, c i • basisState (shadow l (w i)) := by
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hybridLin_basisState l (w i) (h i hi), smul_comm]

/-! ## Reversible prefixes -/

/-- The shadow of a reversible gate list is its Boolean semantics, recast. -/
lemma shadow_gate_list (c : Circuit m) (w : Fin m → Fin 2) :
    shadow (c.map HybridGate.gate) w = regOfState (denote c (stateOfReg w)) := by
  induction c generalizing w with
  | nil => rw [List.map_nil, shadow_nil, denote_nil, regOfState_stateOfReg]
  | cons g rest ih =>
    rw [List.map_cons, shadow_cons, ih, denote_cons, HybridGate.shadow, stateOfReg_regOfState]

/-- A reversible prefix only moves the basis input; well-formedness is decided after it. -/
lemma wellFormed_gate_list_append (c : Circuit m) (rest : List (HybridGate m))
    (w : Fin m → Fin 2) :
    WellFormed (c.map HybridGate.gate ++ rest) w
      ↔ WellFormed rest (regOfState (denote c (stateOfReg w))) := by
  induction c generalizing w with
  | nil => rw [List.map_nil, List.nil_append, denote_nil, regOfState_stateOfReg]
  | cons g rest' ih =>
    rw [List.map_cons, List.cons_append, wellFormed_gate_cons, ih, denote_cons,
      stateOfReg_regOfState]

lemma gadgetCount_gate_list_append (c : Circuit m) (rest : List (HybridGate m)) :
    gadgetCount (c.map HybridGate.gate ++ rest) = gadgetCount rest := by
  induction c with
  | nil => rfl
  | cons g rest' ih => rw [List.map_cons, List.cons_append, gadgetCount, ih]

end Reversible

end
