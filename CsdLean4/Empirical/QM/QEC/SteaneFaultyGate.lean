/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneArbitrary
public import CsdLean4.Empirical.QM.QEC.SteaneThreshold
public import CsdLean4.Mathlib.Probability.CircuitThreshold
public import CsdLean4.Mathlib.QuantumInfo.BlockKron

/-!
# Faulty gates: a transversal gadget on the Steane code, with one bad location

**Category:** 3-Local (Empirical, QM twin). BACKLOG #62, its first rung: the noise sits on the
**gates** now, not on resting qubits.

Code capacity (#51, #86) puts the errors on the seven qubits of a block and keeps every gate
perfect. The circuit-level model of Aharonov–Ben-Or puts a fault at every *location* of the circuit
— each gate of each gadget. This module does the first case of that: a **transversal gadget**, one
single-qubit gate per qubit of the block, with one of its seven locations faulty.

* ★★ `faultyTransversal_eq` — **error propagation**: a fault at location `i`, acting after the ideal
  single-qubit gate there, makes the gadget `gateOf i E * blockKron A` — the ideal gadget followed by
  a **weight-one** error (`blockKron_replace_eq_gateOf_mul`). This is why transversal gadgets are
  fault-tolerant: a single fault cannot spread inside a block;
* ★★★ `steane_faultyTransversal_recovery` — one channel returns the **ideal** output of the faulty
  gadget, up to the scalar of #61, whenever the ideal output is a code state; ★★★
  `steane_faultyTransversal_recovery_unitary` — exactly, for a unitary fault;
* `blockKron_pX_eq_pauliMat` — the transversal `X` **is** the all-ones Pauli, the code's logical `X̄`
  (an entrywise computation: a product of `X`s is `1` exactly on `w = z + 1⃗`), with
  ★ `logicalX_density` — it flips the encoded qubit `a|0̄⟩ + b|1̄⟩ ↦ b|0̄⟩ + a|1̄⟩;
* ★★★ `steane_faultyLogicalX_recovery` — **the concrete statement**: a faulty transversal logical
  `X̄` on an encoded qubit, one location bad and the fault an arbitrary unitary, is corrected — the
  recovery returns the ideally flipped encoded qubit;
* ★★ `steane_circuit_threshold` — the accounting: a circuit of `N` such gadgets, faults independent
  at rate `p < 1/21`, reaches every accuracy at some concatenation level
  (`exists_level_circuitMeasure_lt` with `C(7, 2) = 21`).

## Honest scope

⚠️ **Faulty gates, ideal recovery.** The recovery channel here is the perfect one of #14(b): faults
inside the *recovery* gadget — hence extended rectangles, and with them the simulation theorem that
makes the levels compose — are not treated. That is what BACKLOG #62 still holds, and the two rows
it was split into name the pieces.

⚠️ **One fault per gadget, level one.** The quantum statement is for a single faulty location of a
single transversal gadget on one block. The recursion over levels is the probabilistic one
(`circuitMeasure_circuitBad_le`): what a level-`k` gadget *does* when its pattern is good is #86's
theorem at code capacity, not a statement about faulty gates.

⚠️ A transversal gadget is not a universal gate set: `blockKron A` for arbitrary `A` need not
preserve the code space, which is why the general theorem carries that as a hypothesis, discharged
here for the logical `X̄`. Which transversal gates the Steane code admits (the Clifford group, by
CSS self-duality) is not proved here.

References: D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008); P. Aliferis, D. Gottesman,
J. Preskill, Quantum Inf. Comput. 6 (2006); A. Steane, PRL 77 (1996);
`Empirical/QM/QEC/SteaneArbitrary.lean` (#61), `Mathlib/Probability/CircuitThreshold.lean` (#62);
`specs/BACKLOG.md` #62; `specs/steane-plan.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open scoped ENNReal

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

open Controlled QuantumInfo.Controlled

/-! ### Error propagation through a transversal gadget -/

/-- ★★ **A fault at one location of a transversal gadget is a weight-one error.** The gadget whose
factor at `i` is `E * A i` — the ideal gate there, followed by the fault — is the ideal gadget
followed by the single-qubit error `E`. -/
theorem faultyTransversal_eq (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 7)
    (E : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron (fun b => if b = i then E * A i else A b) = gateOf i E * blockKron A :=
  blockKron_replace_eq_gateOf_mul A i E

/-- Conjugating a rank-one density operator by a matrix acts on the vector. -/
theorem conj_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    M * vecMulVec v (star v) * Mᴴ = vecMulVec (M *ᵥ v) (star (M *ᵥ v)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-! ### One faulty location is corrected -/

/-- ★★★ **A transversal gadget with one faulty location is corrected.** For every transversal gadget
whose ideal output on `ρ` is a code state, and every fault `E` at one of the seven locations, one
channel returns that ideal output — up to the scalar `tr(EᴴE)/2` of #61, since a non-unitary fault is
trace-decreasing. -/
theorem steane_faultyTransversal_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
        blockKron A * ρ * (blockKron A)ᴴ
            = steaneProj * (blockKron A * ρ * (blockKron A)ᴴ) * steaneProj →
        ∀ (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ),
          R.apply (blockKron (fun b => if b = i then E * A i else A b) * ρ
              * (blockKron (fun b => if b = i then E * A i else A b))ᴴ)
            = ((star (E 0 0) * E 0 0 + star (E 0 1) * E 0 1 + star (E 1 0) * E 1 0
                + star (E 1 1) * E 1 1) / 2) • (blockKron A * ρ * (blockKron A)ᴴ) := by
  obtain ⟨R, hR⟩ := steane_recovery_arbitrary
  refine ⟨R, fun A ρ hcode i E => ?_⟩
  have hrewrite : blockKron (fun b => if b = i then E * A i else A b) * ρ
      * (blockKron (fun b => if b = i then E * A i else A b))ᴴ
      = gateOf i E * (blockKron A * ρ * (blockKron A)ᴴ) * (gateOf i E)ᴴ := by
    rw [faultyTransversal_eq, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [hrewrite]
  exact hR _ hcode i E

/-- ★★★ **A unitary fault at one location is undone exactly**: the scalar is `1`. -/
theorem steane_faultyTransversal_recovery_unitary :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
        blockKron A * ρ * (blockKron A)ᴴ
            = steaneProj * (blockKron A * ρ * (blockKron A)ᴴ) * steaneProj →
        ∀ (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ), E ∈ Matrix.unitaryGroup (Fin 2) ℂ →
          R.apply (blockKron (fun b => if b = i then E * A i else A b) * ρ
              * (blockKron (fun b => if b = i then E * A i else A b))ᴴ)
            = blockKron A * ρ * (blockKron A)ᴴ := by
  obtain ⟨R, hR⟩ := steane_recovery_unitary_qubit
  refine ⟨R, fun A ρ hcode i E hE => ?_⟩
  have hrewrite : blockKron (fun b => if b = i then E * A i else A b) * ρ
      * (blockKron (fun b => if b = i then E * A i else A b))ᴴ
      = gateOf i E * (blockKron A * ρ * (blockKron A)ᴴ) * (gateOf i E)ᴴ := by
    rw [faultyTransversal_eq, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [hrewrite]
  exact hR _ hcode i E hE

/-! ### The transversal `X` is the logical `X̄` -/

/-- The transversal `X` on the seven qubits **is** the all-ones Pauli: a product of `X`s is `1`
exactly when every coordinate flips, `w = z + 1⃗`. -/
theorem blockKron_pX_eq_pauliMat :
    blockKron (fun _ : Fin 7 => pX) = pauliMat allOnes 0 := by
  have hpX : ∀ x y : Fin 2, pX x y = if y = x + 1 then 1 else 0 := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [pX]
  ext z w
  rw [blockKron_apply, pauliMat, pauliSign_zero_left,
    Finset.prod_congr rfl fun i _ => hpX (z i) (w i)]
  by_cases h : w = z + allOnes
  · rw [if_pos h]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [if_pos (show w i = z i + 1 by rw [h]; rfl)]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ z i + 1 := by
      by_contra hc
      have hall : ∀ i, w i = z i + 1 := fun i => by
        by_contra hci
        exact hc ⟨i, hci⟩
      exact h (funext fun i => by rw [hall i]; rfl)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The all-ones Pauli flips the encoded qubit: `a|0̄⟩ + b|1̄⟩ ↦ b|0̄⟩ + a|1̄⟩`. -/
theorem pauliMat_allOnes_mulVec_logicalVec (a b : ℂ) :
    pauliMat allOnes 0 *ᵥ logicalVec a b = logicalVec b a := by
  rw [logicalVec, pauliMat_mulVec, WithLp.toLp_ofLp, pauliOp_add, pauliOp_smul, pauliOp_smul,
    logicalX_steaneZero, logicalX_steaneOne, logicalVec, add_comm (b • steaneZero) (a • steaneOne)]

/-- ★ The transversal `X` flips the encoded qubit's density operator. -/
theorem logicalX_density (a b : ℂ) :
    blockKron (fun _ : Fin 7 => pX) * vecMulVec (logicalVec a b) (star (logicalVec a b))
        * (blockKron (fun _ : Fin 7 => pX))ᴴ
      = vecMulVec (logicalVec b a) (star (logicalVec b a)) := by
  rw [blockKron_pX_eq_pauliMat, conj_vecMulVec, pauliMat_allOnes_mulVec_logicalVec]

/-- ★★★ **A faulty transversal logical `X̄` is corrected.** The gadget is the transversal `X` on the
seven qubits — the code's logical `X̄` — with an arbitrary unitary fault at one of its seven
locations. One channel returns the *ideal* output: the encoded qubit with its amplitudes
exchanged. -/
theorem steane_faultyLogicalX_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (a b : ℂ) (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ),
        E ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        R.apply (blockKron (fun q => if q = i then E * pX else pX)
              * vecMulVec (logicalVec a b) (star (logicalVec a b))
              * (blockKron (fun q => if q = i then E * pX else pX))ᴴ)
          = vecMulVec (logicalVec b a) (star (logicalVec b a)) := by
  obtain ⟨R, hR⟩ := steane_faultyTransversal_recovery_unitary
  refine ⟨R, fun a b i E hE => ?_⟩
  have hcode : blockKron (fun _ : Fin 7 => pX) * vecMulVec (logicalVec a b)
        (star (logicalVec a b)) * (blockKron (fun _ : Fin 7 => pX))ᴴ
      = steaneProj * (blockKron (fun _ : Fin 7 => pX) * vecMulVec (logicalVec a b)
        (star (logicalVec a b)) * (blockKron (fun _ : Fin 7 => pX))ᴴ) * steaneProj := by
    rw [logicalX_density]
    exact logical_density_eq b a
  have h := hR (fun _ => pX) (vecMulVec (logicalVec a b) (star (logicalVec a b))) hcode i E hE
  rw [h, logicalX_density]

/-! ### The circuit-level accounting -/

/-- ★★ **The threshold for a circuit of transversal gadgets.** Each of the `N` gadgets of the
circuit has seven locations, faults are independent with rate at most `p`, and a gadget is bad when
two or more of its locations are (which is the case `steane_faultyTransversal_recovery` excludes).
Below `p < 1/21` every accuracy is reached at some concatenation level. -/
theorem steane_circuit_threshold (N : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] {p ε : ℝ}
    (hp : 0 ≤ p) (hν : ν {c | c = true} ≤ ENNReal.ofReal p) (hthr : p < 1 / 21) (hε : 0 < ε) :
    ∃ k, circuitMeasure N 7 ν k (circuitBad N 7 k) < ENNReal.ofReal ε := by
  have h21 : Nat.choose 7 2 = 21 := by decide
  refine exists_level_circuitMeasure_lt N 7 ν hp hν (by rw [h21]; norm_num) ?_ hε
  rw [h21]
  push_cast
  linarith [hthr]

end Steane
end QEC
end QM
end Empirical
end CSD

end
