/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneCircuit
public import CsdLean4.Mathlib.QuantumInfo.LevelReduction

/-!
# The Steane machine: the gadget-set premise discharged

**Category:** 3-Local (Empirical, QM twin). BACKLOG #207 (QC chain, link 12).

`LevelReduction.lean` (#97) proved the threshold statement with its deterministic premise *named*:
a fault pattern that makes no gadget bad must give the ideal output. `ExtendedRectangle.lean` (#96)
produces corrected steps from three piecewise hypotheses — a recovery for a correctable set `D`, the
one-fault bound `DeviatesBy`, transversality `PropagatesD` — but said "no instance at a concrete
code". This module plugs in the Steane code and a gadget set, and discharges the premise.

* `pauliMat_mul_steaneProj`, ★ `logicalX_mul_steaneProj`, ★ `logicalZ_mul_steaneProj` — **the
  logical `X̄` and `Z̄` commute with the code projector**; `isCodeState_conj_of_mul_steaneProj` —
  so they keep code states in the code (`SteaneCircuit.lean`'s honest scope had this open);
* `Gadget` — **the gadget set**: the transversal `H̄`, `X̄`, `Z̄`; `Gadget.ideal`,
  ★★ `Gadget.isCodeState_ideal` — every gadget preserves the code; `Gadget.faulty`, `Gadget.step` —
  the gadget under a fault pattern of its seven locations, then the recovery;
* `locPat`, `isBad_one_eq`, `card_le_one_of_isBad_eq_false`, `exists_single_of_card_le_one` — **a
  level-one pattern that is not bad (`isBad 7 1`, the predicate the threshold counts) is at most one
  fault at one location**;
* `weightOne`, `id_mem_weightOne`, ★ `isRecovery_weightOne` — the correctable set (weight-one unitary
  errors) and the Steane recovery as #96's `IsRecovery`; ★★ `Gadget.propagatesD` —
  **transversality discharged** (`blockKron_mul_gateOf`: `g^{⊗7} M_q = (g M g†)_q g^{⊗7}`);
  ★★ `Gadget.deviatesBy_faulty` — **the one-fault bound discharged**;
* ★★★ `steane_gadgetSet_corrected` — **every good step of the gadget set is an `IsCorrectedStep`**,
  one recovery channel for all of them, by #96's `isCorrectedStep_rect`;
  `steane_gadgetSet_correctedAtLevel_zero` — the level reduction's level-`0` premise;
* ★★★ `steane_exRec` — **#96's extended rectangle at the Steane code**: a faulty leading recovery (any
  map leaving a weight-one deviation), or a faulty gadget, inside the rectangle is corrected; a faulty
  trailing recovery hands on a weight-one deviation;
* `machineCircuit`, `machineIdeal`, `idealRun_machineCircuit`; ★★★ `steane_machine` — **the
  premise discharged and the threshold statement for the Steane machine**: for every circuit of `N`
  gadgets from the set, unitary faults at their locations and an encoded input, a pattern with no bad
  gadget gives exactly the ideal output (through `correctedRun_eq_idealRun_of_level`), and under
  independent location faults of rate at most `p` the output is ideal with probability at least
  `1 − 21 N p²` (`codeCapacityBound_twentyOne_one`).

## Honest scope

⚠️ **Level one.** The pattern is `ConcatPat 7 1`: the seven locations of one transversal gadget.
The level reduction's recursion (`IsCorrectedAtLevel`) is generic and applies above level `0`, but
gadgets acting on the **concatenated** code `cProj k` — transversal gates on `7^k` qubits with
`PatErr`-shaped faults — are not built here; that is its own BACKLOG row.

⚠️ **The recovery in `steane_machine` is ideal.** Faults sit at the gadgets' locations. A faulty
recovery enters only through `steane_exRec`, as #96's `DeviatesBy` hypothesis on the recovery piece:
the recovery is not built as a circuit (both check bases, a decoder, a verified ancilla) whose own
fault locations are counted in the pattern. Those are their own BACKLOG rows.

⚠️ **One block, three gates.** `H̄`, `X̄`, `Z̄` act on a single block; this is not a universal gate
set. The two-block `CNOT̄` (`steane_faultyCNOT_recovery`) lives on a different register and is not
in the machine; nor are `S̄` or a fault-tolerant `T̄`. Each is its own BACKLOG row.

⚠️ **Independent noise and unitary faults**, as in #97: `circuitMeasure` is a product across gadgets
and locations, and each fault is a unitary single-qubit gate applied after the ideal one.

⚠️ **Maps, not channels**, for the ideal gadgets, as in #62 (d1); the recovery is a `Channel`.

References: D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008) 1207; P. Aliferis, D. Gottesman,
J. Preskill, Quantum Inf. Comput. 6 (2006) 97; `specs/BACKLOG.md` #207, #97, #96, #62;
`Mathlib/QuantumInfo/LevelReduction.lean`, `Mathlib/QuantumInfo/ExtendedRectangle.lean`,
`Empirical/QM/QEC/SteaneFaultyGate.lean`, `Empirical/QM/QEC/SteaneCircuit.lean`,
`Empirical/QM/QEC/SteaneArbitrary.lean` (`steane_recovery_unitary_qubit`);
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped ENNReal

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The logical `X̄` and `Z̄` preserve the code space -/

/-- **A Pauli commuting with every stabiliser commutes with the code projector.** -/
theorem pauliMat_mul_steaneProj {a b : Fin 7 → Fin 2}
    (h : ∀ x, bdot a (steaneB x) + bdot b (steaneA x) = 0) :
    pauliMat a b * steaneProj = steaneProj * pauliMat a b := by
  rw [steaneProj, stabMat, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [genMat, Matrix.mul_smul, Matrix.smul_mul, pauliMat_comm, h x, signChar_zero, one_smul]

/-- The all-ones label is orthogonal to every stabiliser label. -/
theorem bdot_allOnes_rowComb (c : Fin 3 → Fin 2) : bdot allOnes (rowComb c) = 0 := by
  rw [bdot_comm, bdot_rowComb_allOnes]

/-- ★ **The logical `X̄` commutes with the Steane code projector.** -/
theorem logicalX_mul_steaneProj :
    pauliMat allOnes 0 * steaneProj = steaneProj * pauliMat allOnes 0 :=
  pauliMat_mul_steaneProj fun x => by
    rw [bdot_zero_left, add_zero, steaneB, bdot_allOnes_rowComb]

/-- ★ **The logical `Z̄` commutes with the Steane code projector.** -/
theorem logicalZ_mul_steaneProj :
    pauliMat 0 allOnes * steaneProj = steaneProj * pauliMat 0 allOnes :=
  pauliMat_mul_steaneProj fun x => by
    rw [bdot_zero_left, zero_add, steaneA, bdot_allOnes_rowComb]

/-- **Conjugation by a matrix commuting with the code projector keeps code states in the code.** -/
theorem isCodeState_conj_of_mul_steaneProj {Q : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hQ : Q * steaneProj = steaneProj * Q) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : IsCodeState steaneProj ρ) : IsCodeState steaneProj (Q * ρ * Qᴴ) := by
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have hQ' : Qᴴ * steaneProj = steaneProj * Qᴴ := by
    have h := congrArg conjTranspose hQ
    rw [conjTranspose_mul, conjTranspose_mul, hP] at h
    exact h.symm
  unfold IsCodeState at hρ ⊢
  calc Q * ρ * Qᴴ = Q * (steaneProj * ρ * steaneProj) * Qᴴ := congrArg (fun σ => Q * σ * Qᴴ) hρ
    _ = (Q * steaneProj) * ρ * (steaneProj * Qᴴ) := by noncomm_ring
    _ = (steaneProj * Q) * ρ * (Qᴴ * steaneProj) := by rw [hQ, hQ']
    _ = steaneProj * (Q * ρ * Qᴴ) * steaneProj := by noncomm_ring

/-! ### The gadget set -/

/-- **The Steane gadget set**: the transversal Hadamard and the transversal logical `X̄` and `Z̄`,
each one single-qubit gate on each of the block's seven qubits. -/
inductive Gadget
  /-- The transversal Hadamard, the logical `H̄`. -/
  | had
  /-- The transversal `X`, the logical `X̄`. -/
  | x
  /-- The transversal `Z`, the logical `Z̄`. -/
  | z
  deriving DecidableEq

namespace Gadget

/-- The single-qubit gate a gadget applies at each of its seven locations. -/
def gate : Gadget → Matrix (Fin 2) (Fin 2) ℂ
  | had => hGateM
  | x => pX
  | z => pZ

/-- The ideal gadget, as a map on density operators. -/
def ideal (G : Gadget) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron (fun _ : Fin 7 => G.gate) * ρ * (blockKron (fun _ : Fin 7 => G.gate))ᴴ

/-- ★★ **Every gadget of the set keeps code states in the code** — the half of a corrected step
that lets gadgets compose. For the Hadamard this is `hadTransversal_code_state`; for `X̄` and `Z̄`
it is `logicalX_mul_steaneProj` / `logicalZ_mul_steaneProj`. -/
theorem isCodeState_ideal (G : Gadget) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : IsCodeState steaneProj ρ) : IsCodeState steaneProj (G.ideal ρ) := by
  cases G with
  | had => exact hadTransversal_code_state hρ
  | x =>
    show IsCodeState steaneProj (blockKron (fun _ : Fin 7 => pX) * ρ
      * (blockKron (fun _ : Fin 7 => pX))ᴴ)
    rw [blockKron_pX_eq_pauliMat]
    exact isCodeState_conj_of_mul_steaneProj logicalX_mul_steaneProj hρ
  | z =>
    show IsCodeState steaneProj (blockKron (fun _ : Fin 7 => pZ) * ρ
      * (blockKron (fun _ : Fin 7 => pZ))ᴴ)
    rw [blockKron_pZ_eq_pauliMat]
    exact isCodeState_conj_of_mul_steaneProj logicalZ_mul_steaneProj hρ

/-- **The gadget under a fault pattern**: `b q` says whether location `q` is faulty, and a faulty
location applies the fault `U q` after the ideal gate there. -/
def faulty (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 7 → Bool)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron (fun q => if b q then U q * G.gate else G.gate) * ρ
    * (blockKron (fun q => if b q then U q * G.gate else G.gate))ᴴ

/-- **The implemented step**: the gadget under its fault pattern, then the recovery channel. -/
def step (R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)) (G : Gadget)
    (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 7 → Bool)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  R.apply (G.faulty U b ρ)

end Gadget

/-! ### A good pattern has at most one faulty location -/

/-- A level-one pattern read as the faulty locations of a seven-location gadget. -/
def locPat (b : ConcatPat 7 1) : Fin 7 → Bool := b

/-- A level-one pattern is bad exactly when two or more of its locations are faulty. -/
theorem isBad_one_eq (b : ConcatPat 7 1) :
    isBad 7 1 b = decide (2 ≤ (Finset.univ.filter fun q : Fin 7 => locPat b q = true).card) := rfl

/-- A level-one pattern that is not bad has at most one faulty location. -/
theorem card_le_one_of_isBad_eq_false {b : ConcatPat 7 1} (hb : isBad 7 1 b = false) :
    (Finset.univ.filter fun q : Fin 7 => locPat b q = true).card ≤ 1 := by
  rw [isBad_one_eq, decide_eq_false_iff_not] at hb
  omega

/-- **At most one faulty location is one fault at one location**: the pattern's factor function is
the ideal gate everywhere except at one location `i`, where it is `E` after the gate, with `E` one
of the faults (or the identity, when no location is faulty). -/
theorem exists_single_of_card_le_one (g : Matrix (Fin 2) (Fin 2) ℂ)
    (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {b : Fin 7 → Bool} (hb : (Finset.univ.filter fun q : Fin 7 => b q = true).card ≤ 1) :
    ∃ (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ), E ∈ Matrix.unitaryGroup (Fin 2) ℂ
      ∧ (fun q => if b q then U q * g else g) = fun q => if q = i then E * g else g := by
  by_cases h : ∃ i, b i = true
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, U i, hU i, funext fun q => ?_⟩
    by_cases hq : q = i
    · subst hq
      simp [hi]
    · have hbq : b q = false := by
        by_contra hbq
        have hq' : b q = true := by simpa using hbq
        have hsub : ({i, q} : Finset (Fin 7)) ⊆ Finset.univ.filter fun q : Fin 7 => b q = true := by
          intro r hr
          rcases Finset.mem_insert.1 hr with rfl | hr
          · simpa using hi
          · rw [Finset.mem_singleton] at hr
            subst hr
            simpa using hq'
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_pair (Ne.symm hq)] at h2
        omega
      simp [hbq, hq]
  · simp only [not_exists] at h
    refine ⟨0, 1, one_mem _, funext fun q => ?_⟩
    have hbq : b q = false := by simpa using h q
    simp [hbq]

/-! ### The correctable set and the three piecewise properties -/

/-- **The Steane code's correctable set**: the weight-one unitary errors, as maps on density
operators — conjugation by a unitary single-qubit gate on one of the seven qubits. -/
def weightOne : Set (Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :=
  {f | ∃ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ), M ∈ Matrix.unitaryGroup (Fin 2) ℂ
    ∧ f = fun ρ => gateOf q M * ρ * (gateOf q M)ᴴ}

/-- "No error" is correctable. -/
theorem id_mem_weightOne : id ∈ weightOne :=
  ⟨0, 1, one_mem _, funext fun ρ => by simp [gateOf_one]⟩

/-- ★ **The Steane recovery is a recovery for the weight-one errors**, in the sense of #96's
`IsRecovery`. -/
theorem isRecovery_weightOne {R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)}
    (hR : ∀ ρ, ρ = steaneProj * ρ * steaneProj → ∀ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ),
      M ∈ Matrix.unitaryGroup (Fin 2) ℂ → R.apply (gateOf q M * ρ * (gateOf q M)ᴴ) = ρ) :
    IsRecovery steaneProj R.apply weightOne := by
  rintro E ⟨q, M, hM, rfl⟩ ρ hρ
  exact hR ρ hρ q M hM

namespace Gadget

/-- Each gadget's single-qubit gate is unitary (indeed a Hermitian involution). -/
theorem gate_conjTranspose_mul (G : Gadget) : G.gateᴴ * G.gate = 1 := by
  cases G with
  | had => exact hGateM_conjTranspose ▸ QuantumInfo.SU2.hGateM_mul_self
  | x =>
    have h : pXᴴ = pX := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pX]
    rw [gate, h, pX_mul_pX]
  | z =>
    have h : pZᴴ = pZ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pZ]
    rw [gate, h, pZ_mul_pZ]

theorem gate_mem_unitaryGroup (G : Gadget) : G.gate ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact G.gate_conjTranspose_mul)

/-- **A transversal gate carries a single-qubit gate to a single-qubit gate on the same qubit**:
`g^{⊗7} · M_q = (g M g†)_q · g^{⊗7}`. -/
theorem blockKron_mul_gateOf (G : Gadget) (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron (fun _ : Fin 7 => G.gate) * gateOf q M
      = gateOf q (G.gate * M * G.gateᴴ) * blockKron (fun _ : Fin 7 => G.gate) := by
  rw [← blockKron_single_eq_gateOf, blockKron_mul,
    ← blockKron_replace_eq_gateOf_mul (fun _ : Fin 7 => G.gate) q (G.gate * M * G.gateᴴ)]
  congr 1
  funext b
  by_cases h : b = q
  · rw [ite_eq_left h, ite_eq_left h, mul_assoc (G.gate * M), G.gate_conjTranspose_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_one]

/-- ★★ **Transversality, discharged**: every gadget of the set carries a weight-one error of a code
state to a weight-one error of its output — #96's `PropagatesD` at the Steane code. -/
theorem propagatesD (G : Gadget) : PropagatesD steaneProj weightOne G.ideal := by
  rintro _ ⟨q, M, hM, rfl⟩ ρ _
  have hM' : G.gate * M * G.gateᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    refine mul_mem (mul_mem G.gate_mem_unitaryGroup hM) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem G.gate_mem_unitaryGroup
  refine ⟨fun σ => gateOf q (G.gate * M * G.gateᴴ) * σ * (gateOf q (G.gate * M * G.gateᴴ))ᴴ,
    ⟨q, _, hM', rfl⟩, ?_⟩
  have h := G.blockKron_mul_gateOf q M
  show blockKron (fun _ : Fin 7 => G.gate) * (gateOf q M * ρ * (gateOf q M)ᴴ)
      * (blockKron (fun _ : Fin 7 => G.gate))ᴴ
    = gateOf q (G.gate * M * G.gateᴴ) * (blockKron (fun _ : Fin 7 => G.gate) * ρ
      * (blockKron (fun _ : Fin 7 => G.gate))ᴴ) * (gateOf q (G.gate * M * G.gateᴴ))ᴴ
  calc blockKron (fun _ : Fin 7 => G.gate) * (gateOf q M * ρ * (gateOf q M)ᴴ)
        * (blockKron (fun _ : Fin 7 => G.gate))ᴴ
      = (blockKron (fun _ : Fin 7 => G.gate) * gateOf q M) * ρ
        * (blockKron (fun _ : Fin 7 => G.gate) * gateOf q M)ᴴ := by
        rw [conjTranspose_mul]; noncomm_ring
    _ = (gateOf q (G.gate * M * G.gateᴴ) * blockKron (fun _ : Fin 7 => G.gate)) * ρ
        * (gateOf q (G.gate * M * G.gateᴴ) * blockKron (fun _ : Fin 7 => G.gate))ᴴ := by rw [h]
    _ = _ := by rw [conjTranspose_mul]; noncomm_ring

/-- ★★ **The one-fault bound, discharged**: a gadget whose pattern has at most one faulty location,
each fault unitary, is the ideal gadget followed by a weight-one error — #96's `DeviatesBy`. -/
theorem deviatesBy_faulty (G : Gadget) {U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : ∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) {b : Fin 7 → Bool}
    (hb : (Finset.univ.filter fun q : Fin 7 => b q = true).card ≤ 1) :
    DeviatesBy steaneProj weightOne G.ideal (G.faulty U b) := by
  intro ρ _
  obtain ⟨i, E, hE, hfun⟩ := exists_single_of_card_le_one G.gate U hU hb
  refine ⟨fun σ => gateOf i E * σ * (gateOf i E)ᴴ, ⟨i, E, hE, rfl⟩, ?_⟩
  show blockKron (fun q => if b q then U q * G.gate else G.gate) * ρ
      * (blockKron (fun q => if b q then U q * G.gate else G.gate))ᴴ
    = gateOf i E * (blockKron (fun _ : Fin 7 => G.gate) * ρ
      * (blockKron (fun _ : Fin 7 => G.gate))ᴴ) * (gateOf i E)ᴴ
  rw [hfun, faultyTransversal_eq (fun _ : Fin 7 => G.gate) i E, conjTranspose_mul]
  noncomm_ring

end Gadget

/-! ### The gadget set discharges the premise -/

/-- ★★★ **The Steane gadget set is a set of corrected steps.** One recovery channel `R` serves every
gadget: for each of the transversal `H̄`, `X̄`, `Z̄`, every assignment of unitary faults to its seven
locations, and every fault pattern that is **not bad** (at most one faulty location — `isBad 7 1`,
the pattern predicate the threshold theorem counts), the faulty gadget followed by `R` is an
`IsCorrectedStep` for the ideal gadget. It is #96's `isCorrectedStep_rect` with its three
hypotheses discharged: `isRecovery_weightOne`, `Gadget.deviatesBy_faulty`,
`Gadget.isCodeState_ideal`. This is the hypothesis the composition theorem and the level reduction
consume, at a concrete code. -/
theorem steane_gadgetSet_corrected :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      IsRecovery steaneProj R.apply weightOne
      ∧ ∀ (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ b : ConcatPat 7 1, isBad 7 1 b = false →
          IsCorrectedStep steaneProj G.ideal (G.step R U (locPat b)) := by
  obtain ⟨R, hR⟩ := steane_recovery_unitary_qubit
  have hrec := isRecovery_weightOne hR
  exact ⟨R, hrec, fun G U hU b hb => isCorrectedStep_rect hrec
    (G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hb)) fun _ hρ => G.isCodeState_ideal hρ⟩

/-- **The level reduction's level-`0` premise**: each good step of the gadget set is a corrected
gadget at level `0`, in the sense of `IsCorrectedAtLevel`. -/
theorem steane_gadgetSet_correctedAtLevel_zero :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ b : ConcatPat 7 1, isBad 7 1 b = false →
          IsCorrectedAtLevel steaneProj 0 G.ideal (G.step R U (locPat b)) := by
  obtain ⟨R, -, h⟩ := steane_gadgetSet_corrected
  exact ⟨R, h⟩

/-- ★★★ **#96's extended rectangle at the Steane code.** With the same recovery `R`:

* **a faulty leading recovery** — any map that leaves a weight-one deviation of a code state — then
  the ideal gadget, then `R`, is a corrected step (`isCorrectedStep_exRec_leading`, transversality
  being `Gadget.propagatesD`);
* **a faulty gadget** with a good pattern between two copies of `R` is a corrected step
  (`isCorrectedStep_exRec_gadget`);
* **a faulty trailing recovery** hands on a weight-one deviation of the ideal output
  (`deviatesBy_exRec_trailing`), in the form the next rectangle's `IsRecovery` consumes. -/
theorem steane_exRec :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      (∀ (G : Gadget) (R₁ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
            → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
          DeviatesBy steaneProj weightOne id R₁ →
          IsCorrectedStep steaneProj G.ideal (exRec R₁ G.ideal R.apply))
      ∧ (∀ (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
          (∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
          ∀ b : ConcatPat 7 1, isBad 7 1 b = false →
            IsCorrectedStep steaneProj G.ideal (exRec R.apply (G.faulty U (locPat b)) R.apply))
      ∧ (∀ (G : Gadget) (R₂ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
            → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
          DeviatesBy steaneProj weightOne id R₂ →
          DeviatesBy steaneProj weightOne G.ideal (exRec R.apply G.ideal R₂)) := by
  obtain ⟨R, hR⟩ := steane_recovery_unitary_qubit
  have hrec := isRecovery_weightOne hR
  refine ⟨R, fun G R₁ hR₁ => ?_, fun G U hU b hb => ?_, fun G R₂ hR₂ => ?_⟩
  · exact isCorrectedStep_exRec_leading hR₁ G.propagatesD hrec fun _ hρ => G.isCodeState_ideal hρ
  · exact isCorrectedStep_exRec_gadget id_mem_weightOne hrec
      (G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hb)) hrec
      fun _ hρ => G.isCodeState_ideal hρ
  · exact deviatesBy_exRec_trailing id_mem_weightOne hrec hR₂ fun _ hρ => G.isCodeState_ideal hρ

/-! ### The machine -/

/-- **The machine's circuit**: gadget `j` is `gs j`, its fault unitaries are `U j`, and its fault
pattern is `ω j`; each gadget is run and then recovered. -/
def machineCircuit (R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)) {N : ℕ}
    (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 1) :
    Circuit (Fin 7 → Fin 2) :=
  List.ofFn fun j => ((gs j).ideal, (gs j).step R (U j) (locPat (ω j)))

/-- The ideal output of the machine: the ideal gadgets, in order. -/
def machineIdeal {N : ℕ} (gs : Fin N → Gadget) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  runMaps (List.ofFn fun j => (gs j).ideal) ρ

theorem idealRun_machineCircuit (R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr))
    {N : ℕ} (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : CircuitPat N 7 1) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    idealRun (machineCircuit R gs U ω) ρ = machineIdeal gs ρ := by
  rw [idealRun, machineCircuit, machineIdeal, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine at level one.** One recovery channel `R` such that, for every circuit
of `N` gadgets from the set, every assignment of unitary faults to their locations and every encoded
input:

* **the deterministic premise holds**: a fault pattern that makes no gadget bad gives exactly the
  ideal output — via the level reduction's `correctedRun_eq_idealRun_of_level` at level `0`, fed by
  `steane_gadgetSet_correctedAtLevel_zero`; this is `hgood` of `one_sub_le_measure_output_eq_concat`,
  discharged;
* **the threshold statement follows**: under independent location faults of rate at most `p`, the
  output is exactly the ideal one with probability at least
  `1 − N · codeCapacityBound 21 p 1 = 1 − 21 N p²`. -/
theorem steane_machine :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (N : ℕ) (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ, IsCodeState steaneProj ρ →
          (∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
              correctedRun (machineCircuit R gs U ω) ρ = machineIdeal gs ρ)
          ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
              ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
                ≤ QuantumInfo.circuitMeasure N 7 ν 1
                    {ω | correctedRun (machineCircuit R gs U ω) ρ = machineIdeal gs ρ} := by
  obtain ⟨R, hR⟩ := steane_gadgetSet_correctedAtLevel_zero
  refine ⟨R, fun N gs U hU ρ hρ => ?_⟩
  have hgood : ∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
      correctedRun (machineCircuit R gs U ω) ρ = machineIdeal gs ρ := by
    intro ω hω
    rw [← idealRun_machineCircuit R gs U ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hR (gs j) (U j) (hU j) (ω j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := 1) ν hp hν
    (out := fun ω => correctedRun (machineCircuit R gs U ω) ρ) (ideal := machineIdeal gs ρ) hgood
  rwa [h21] at h

/-- The level-one bound in closed form: `codeCapacityBound 21 p 1 = 21 p²`. -/
theorem codeCapacityBound_twentyOne_one (p : ℝ) : codeCapacityBound 21 p 1 = 21 * p ^ 2 := rfl

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
