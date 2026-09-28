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
public import CsdLean4.Mathlib.QuantumInfo.TransversalClifford

/-!
# Faulty gates: a transversal gadget on the Steane code, with one bad location

**Category:** 3-Local (Empirical, QM twin). BACKLOG #62 (a) and (b): the noise sits on the
**gates** now, not on resting qubits, and the transversal gadgets are the code's logical gates.

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
* `blockKron_pX_eq_pauliMat`, `blockKron_pZ_eq_pauliMat` — the transversal `X` and `Z` **are** the
  all-ones Paulis, the code's logical `X̄` and `Z̄` (a Pauli string factorises over the qubits,
  `pauliMat_eq_blockKron`, and `X = onePauli 1 0`, `Z = onePauli 0 1`), with ★ `logicalX_density`
  and ★ `logicalZ_density` — they flip and sign the encoded qubit;
* ★★★ `steane_faultyLogicalX_recovery` and ★★★ `steane_faultyLogicalZ_recovery` — **the
  concrete statements**: a faulty transversal logical `X̄` (or `Z̄`) on an encoded qubit, one location
  bad and the fault an arbitrary unitary, is corrected — the recovery returns the ideal output;
* **the transversal Hadamard, #62 (b)**: `swapHalves` exchanges the halves of a stabiliser label, so
  `steaneA_swapHalves`/`steaneB_swapHalves` turn the label swap of `hadTransversal_conj_pauliMat`
  into a bijection of the family; with the CSS condition `bdot_steaneA_steaneB` killing the sign
  that gives ★★ `hadTransversal_conj_steaneProj` — **the transversal Hadamard preserves the code
  projector** — hence ★ `hadTransversal_code_state`, and ★★ `hadTransversal_conj_logicalX` /
  `_logicalZ`: **it exchanges `X̄` and `Z̄`**, the logical Hadamard in the Heisenberg picture.
  ★★★ `steane_faultyHadamard_recovery` is then (a)'s theorem for the Hadamard gadget;
* ★★ `steane_circuit_threshold` — the accounting: a circuit of `N` such gadgets, faults independent
  at rate `p < 1/21`, reaches every accuracy at some concatenation level
  (`exists_level_circuitMeasure_lt` with `C(7, 2) = 21`).

## Honest scope

⚠️ **Faulty gates, ideal recovery.** The recovery channel here is the perfect one of #14(b): faults
inside the *recovery* gadget — hence extended rectangles, and with them the simulation theorem that
makes the levels compose — are not treated. That is what BACKLOG #62 (c) and (d) hold.

⚠️ **One fault per gadget, level one.** The quantum statement is for a single faulty location of a
single transversal gadget on one block. The recursion over levels is the probabilistic one
(`circuitMeasure_circuitBad_le`): what a level-`k` gadget *does* when its pattern is good is #86's
theorem at code capacity, not a statement about faulty gates.

⚠️ A transversal gadget is not a universal gate set: `blockKron A` for arbitrary `A` need not
preserve the code space, which is why the general theorem carries that as a hypothesis — discharged
here for `X̄`, `Z̄` and the Hadamard. The two-block transversal `CNOT` is not here because it needs
a faulty-gadget theorem across *two* blocks, a different statement from (a)'s; that is
[`SteaneTransversalCNOT.lean`](SteaneTransversalCNOT.lean) (#62 (f), landed 2026-09-28).

⚠️ The Hadamard's logical action is proved in the **Heisenberg** picture (where `X̄` and `Z̄` go) and
through the projector, which is what fault tolerance needs. That `H^{⊗ 7}|0̄⟩ = (|0̄⟩ + |1̄⟩)/√2` in
the Schrödinger picture — the MacWilliams/coset computation — is not proved here.

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

open Controlled QuantumInfo.Controlled QuantumInfo.CliffordT QuantumInfo.SU2

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

/-! ### The transversal `X` and `Z` are the logical `X̄` and `Z̄` -/

theorem onePauli_one_zero : onePauli 1 0 = pX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onePauli, pX, signChar]

theorem onePauli_zero_one : onePauli 0 1 = pZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onePauli, pZ, signChar]

/-- The transversal `X` on the seven qubits **is** the all-ones Pauli, the code's logical `X̄`: a
Pauli string factorises over the qubits (`pauliMat_eq_blockKron`) and `X = onePauli 1 0`. -/
theorem blockKron_pX_eq_pauliMat :
    blockKron (fun _ : Fin 7 => pX) = pauliMat allOnes 0 := by
  rw [pauliMat_eq_blockKron]
  congr 1
  funext i
  rw [show allOnes i = 1 from rfl, show (0 : Fin 7 → Fin 2) i = 0 from rfl, onePauli_one_zero]

/-- The transversal `Z` **is** the other all-ones Pauli, the code's logical `Z̄`. -/
theorem blockKron_pZ_eq_pauliMat :
    blockKron (fun _ : Fin 7 => pZ) = pauliMat 0 allOnes := by
  rw [pauliMat_eq_blockKron]
  congr 1
  funext i
  rw [show allOnes i = 1 from rfl, show (0 : Fin 7 → Fin 2) i = 0 from rfl, onePauli_zero_one]

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

/-- The all-ones `Z` Pauli signs the encoded qubit's second amplitude: `Z̄` on `a|0̄⟩ + b|1̄⟩`. -/
theorem pauliMat_zero_allOnes_mulVec_logicalVec (a b : ℂ) :
    pauliMat 0 allOnes *ᵥ logicalVec a b = logicalVec a (-b) := by
  rw [logicalVec, pauliMat_mulVec, WithLp.toLp_ofLp, pauliOp_add, pauliOp_smul, pauliOp_smul,
    logicalZ_steaneZero, logicalZ_steaneOne, logicalVec, smul_neg, ← neg_smul]

/-- ★ The transversal `Z` signs the encoded qubit's density operator. -/
theorem logicalZ_density (a b : ℂ) :
    blockKron (fun _ : Fin 7 => pZ) * vecMulVec (logicalVec a b) (star (logicalVec a b))
        * (blockKron (fun _ : Fin 7 => pZ))ᴴ
      = vecMulVec (logicalVec a (-b)) (star (logicalVec a (-b))) := by
  rw [blockKron_pZ_eq_pauliMat, conj_vecMulVec, pauliMat_zero_allOnes_mulVec_logicalVec]

/-- ★★★ **A faulty transversal logical `Z̄` is corrected**, with the ideal output the signed encoded
qubit. -/
theorem steane_faultyLogicalZ_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (a b : ℂ) (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ),
        E ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        R.apply (blockKron (fun q => if q = i then E * pZ else pZ)
              * vecMulVec (logicalVec a b) (star (logicalVec a b))
              * (blockKron (fun q => if q = i then E * pZ else pZ))ᴴ)
          = vecMulVec (logicalVec a (-b)) (star (logicalVec a (-b))) := by
  obtain ⟨R, hR⟩ := steane_faultyTransversal_recovery_unitary
  refine ⟨R, fun a b i E hE => ?_⟩
  have hcode : blockKron (fun _ : Fin 7 => pZ) * vecMulVec (logicalVec a b)
        (star (logicalVec a b)) * (blockKron (fun _ : Fin 7 => pZ))ᴴ
      = steaneProj * (blockKron (fun _ : Fin 7 => pZ) * vecMulVec (logicalVec a b)
        (star (logicalVec a b)) * (blockKron (fun _ : Fin 7 => pZ))ᴴ) * steaneProj := by
    rw [logicalZ_density]
    exact logical_density_eq a (-b)
  have h := hR (fun _ => pZ) (vecMulVec (logicalVec a b) (star (logicalVec a b))) hcode i E hE
  rw [h, logicalZ_density]

/-! ### The transversal Hadamard preserves the code space -/

/-- Swapping the two halves of a stabiliser label: in `Fin 6` that is `k ↦ k + 3`. -/
def swapHalves (x : Fin 6 → Fin 2) : Fin 6 → Fin 2 := fun k => x (k + 3)

theorem swapHalves_involutive : Function.Involutive swapHalves := by
  intro x
  funext k
  show x (k + 3 + 3) = x k
  congr 1
  revert k
  decide

/-- The swap exchanges the `X`-labels for the `Z`-labels of the stabiliser family. -/
theorem steaneA_swapHalves (x : Fin 6 → Fin 2) : steaneA (swapHalves x) = steaneB x := by
  rw [steaneA, steaneB]
  congr 1
  funext i
  show x (Fin.castAdd 3 i + 3) = x (Fin.natAdd 3 i)
  congr 1
  revert i
  decide

theorem steaneB_swapHalves (x : Fin 6 → Fin 2) : steaneB (swapHalves x) = steaneA x := by
  rw [steaneA, steaneB]
  congr 1
  funext i
  show x (Fin.natAdd 3 i + 3) = x (Fin.castAdd 3 i)
  congr 1
  revert i
  decide

/-- **The CSS condition on the family's labels**: every `X`-label is orthogonal to every `Z`-label,
so the transversal Hadamard's sign is `1`. -/
theorem bdot_steaneA_steaneB (x : Fin 6 → Fin 2) : bdot (steaneA x) (steaneB x) = 0 := by
  rw [steaneA, steaneB]
  exact bdot_rowComb_rowComb _ _

/-- ★★ **The transversal Hadamard preserves the Steane code projector.** The Hadamard exchanges the
`X`- and `Z`-labels of every group element (`hadTransversal_conj_pauliMat`), the CSS condition kills
the sign, and swapping the halves of the label is a bijection of the family — so the group average
comes back to itself. -/
theorem hadTransversal_conj_steaneProj :
    hadTransversal 7 * steaneProj * hadTransversal 7 = steaneProj := by
  have hterm : ∀ x : Fin 6 → Fin 2,
      hadTransversal 7 * genMat steaneA steaneB (fun _ => 0) x * hadTransversal 7
        = genMat steaneA steaneB (fun _ => 0) (swapHalves x) := by
    intro x
    rw [genMat, genMat, signChar_zero, one_smul, one_smul, hadTransversal_conj_pauliMat,
      bdot_steaneA_steaneB x, signChar_zero, one_smul, steaneA_swapHalves, steaneB_swapHalves]
  rw [steaneProj, stabMat, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl fun x _ => hterm x]
  congr 1
  exact Fintype.sum_bijective swapHalves swapHalves_involutive.bijective _ _ fun _ => rfl

theorem steaneProj_mul_hadTransversal :
    steaneProj * hadTransversal 7 = hadTransversal 7 * steaneProj := by
  calc steaneProj * hadTransversal 7
      = (hadTransversal 7 * steaneProj * hadTransversal 7) * hadTransversal 7 := by
        rw [hadTransversal_conj_steaneProj]
    _ = hadTransversal 7 * steaneProj * (hadTransversal 7 * hadTransversal 7) := by noncomm_ring
    _ = hadTransversal 7 * steaneProj := by rw [hadTransversal_mul_self, mul_one]

/-- ★ **The transversal Hadamard maps code states to code states**, which is what the faulty-gadget
theorem needs of the ideal gadget. -/
theorem hadTransversal_code_state {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : ρ = steaneProj * ρ * steaneProj) :
    hadTransversal 7 * ρ * (hadTransversal 7)ᴴ
      = steaneProj * (hadTransversal 7 * ρ * (hadTransversal 7)ᴴ) * steaneProj := by
  rw [hadTransversal_conjTranspose]
  calc hadTransversal 7 * ρ * hadTransversal 7
      = hadTransversal 7 * (steaneProj * ρ * steaneProj) * hadTransversal 7 := by rw [← hρ]
    _ = (hadTransversal 7 * steaneProj) * ρ * (steaneProj * hadTransversal 7) := by noncomm_ring
    _ = (steaneProj * hadTransversal 7) * ρ * (hadTransversal 7 * steaneProj) := by
        rw [← steaneProj_mul_hadTransversal, steaneProj_mul_hadTransversal]
    _ = steaneProj * (hadTransversal 7 * ρ * hadTransversal 7) * steaneProj := by noncomm_ring

/-- ★★ **The transversal Hadamard exchanges the logical `X̄` and `Z̄`** — the logical Hadamard in the
Heisenberg picture. -/
theorem hadTransversal_conj_logicalX :
    hadTransversal 7 * pauliMat allOnes 0 * hadTransversal 7 = pauliMat 0 allOnes := by
  rw [hadTransversal_conj_pauliMat, bdot_zero_right, signChar_zero, one_smul]

theorem hadTransversal_conj_logicalZ :
    hadTransversal 7 * pauliMat 0 allOnes * hadTransversal 7 = pauliMat allOnes 0 := by
  rw [hadTransversal_conj_pauliMat, bdot_zero_left, signChar_zero, one_smul]

/-- ★★★ **A faulty transversal Hadamard is corrected.** The gadget is the Hadamard on all seven
qubits — a logical Hadamard, by `hadTransversal_conj_logicalX`/`_logicalZ` — with an arbitrary
unitary fault at one of its seven locations; one channel returns the ideal output. -/
theorem steane_faultyHadamard_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), ρ = steaneProj * ρ * steaneProj →
        ∀ (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ), E ∈ Matrix.unitaryGroup (Fin 2) ℂ →
          R.apply (blockKron (fun q => if q = i then E * hGateM else hGateM) * ρ
              * (blockKron (fun q => if q = i then E * hGateM else hGateM))ᴴ)
            = hadTransversal 7 * ρ * (hadTransversal 7)ᴴ := by
  obtain ⟨R, hR⟩ := steane_faultyTransversal_recovery_unitary
  refine ⟨R, fun ρ hρ i E hE => ?_⟩
  have hblock : blockKron (fun _ : Fin 7 => hGateM) = hadTransversal 7 := rfl
  have hcode : blockKron (fun _ : Fin 7 => hGateM) * ρ * (blockKron (fun _ : Fin 7 => hGateM))ᴴ
      = steaneProj * (blockKron (fun _ : Fin 7 => hGateM) * ρ
          * (blockKron (fun _ : Fin 7 => hGateM))ᴴ) * steaneProj := by
    rw [hblock]
    exact hadTransversal_code_state hρ
  have h := hR (fun _ => hGateM) ρ hcode i E hE
  rw [h, hblock]

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
