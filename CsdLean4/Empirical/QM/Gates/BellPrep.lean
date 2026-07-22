/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/QM: Bell-state preparation circuit

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

The canonical two-gate Bell-state preparation circuit:
`(CNOT) ∘ (H ⊗ I)` applied to `|00⟩` yields `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.

This is the building block for entanglement generation in essentially
every quantum-circuit construction. Pairs with `Empirical/CSD/Gates/BellPrep.lean`.

## Contents

- `qmH_tensor_I`: the 4×4 matrix `H ⊗ I` (Hadamard on qubit 0, identity
  on qubit 1).
- `qmBellPrepCircuit`: the composition `qmCNOT * qmH_tensor_I`.
- `qmKet00`, `qmKetPhiPlus`: the `|00⟩` and `|Φ⁺⟩` state vectors as
  `EuclideanSpace ℂ (Fin 4)`.
- `qmBellPrep_yields_phiplus`: the headline identity
  `qmBellPrepCircuit · |00⟩ = |Φ⁺⟩` (matrix-vector form, up to
  the `Matrix.toEuclideanLin` coercion).

## Notation

`|Φ⁺⟩` is one of the four Bell states. The LF3 `singlet` is `|Ψ⁻⟩`,
a *different* Bell state related to `|Φ⁺⟩` by `(I ⊗ σ_y)` up to
phase. No direct algebraic identity between this file's circuit
output and the LF3 singlet — the circuit produces a different Bell
state, mentioned in the docstring for context.
-/

open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace Gates

/-- The 4×4 matrix `H ⊗ I`. Hadamard on qubit 0 (the high bit),
identity on qubit 1.

Explicit entries with basis order `|00⟩, |01⟩, |10⟩, |11⟩`:
`(1/√2) · ((H[0,0]·I, H[0,1]·I), (H[1,0]·I, H[1,1]·I))`. -/
noncomputable def qmH_tensor_I : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    Matrix.of (fun i j : Fin 4 =>
      (match i, j with
        | 0, 0 => 1 | 0, 2 => 1
        | 1, 1 => 1 | 1, 3 => 1
        | 2, 0 => 1 | 2, 2 => -1
        | 3, 1 => 1 | 3, 3 => -1
        | _, _ => 0 : ℂ))

/-- The Bell-state preparation circuit: `CNOT ∘ (H ⊗ I)`. -/
noncomputable def qmBellPrepCircuit : Matrix (Fin 4) (Fin 4) ℂ :=
  qmCNOT * qmH_tensor_I

/-- The two-qubit basis state `|00⟩` as a vector in
`EuclideanSpace ℂ (Fin 4)`. -/
noncomputable def qmKet00 : EuclideanSpace ℂ (Fin 4) :=
  EuclideanSpace.single 0 (1 : ℂ)

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩) / √2`. -/
noncomputable def qmKetPhiPlus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single 3 (1 : ℂ))

/-- **Definitional unfold of the Bell-prep circuit's factorisation.**
A `rfl`-closed labelled handle on `qmBellPrepCircuit = qmCNOT * qmH_tensor_I`;
exists for downstream consumers that prefer the factorised form. The
genuine empirical identity is `qmBellPrep_yields_phiplus` below. -/
theorem qmBellPrep_factorisation :
    qmBellPrepCircuit = qmCNOT * qmH_tensor_I := rfl

/-! ### Column-0 entries of the composite circuit

The 4×4 matrix `qmBellPrepCircuit = qmCNOT * qmH_tensor_I` has, in
column 0 (the only column probed by `|00⟩ = e_0`):
- entry 0: `(1/√2)` (from `CNOT[0,0] · (H⊗I)[0,0] = 1 · (1/√2)`),
- entry 1: `0`,
- entry 2: `0` (`CNOT[2,3] · (H⊗I)[3,0] = 1 · 0`),
- entry 3: `(1/√2)` (`CNOT[3,2] · (H⊗I)[2,0] = 1 · (1/√2)`).

These four entries are the matrix-element computations underlying
`qmBellPrep_yields_phiplus`. -/

lemma qmBellPrepCircuit_col0_zero :
    qmBellPrepCircuit 0 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmBellPrepCircuit, qmCNOT, qmH_tensor_I, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.of_apply]

lemma qmBellPrepCircuit_col0_one :
    qmBellPrepCircuit 1 0 = 0 := by
  simp [qmBellPrepCircuit, qmCNOT, qmH_tensor_I, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.of_apply]

lemma qmBellPrepCircuit_col0_two :
    qmBellPrepCircuit 2 0 = 0 := by
  simp [qmBellPrepCircuit, qmCNOT, qmH_tensor_I, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.of_apply]

lemma qmBellPrepCircuit_col0_three :
    qmBellPrepCircuit 3 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmBellPrepCircuit, qmCNOT, qmH_tensor_I, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.of_apply]

/-! ### Component-form expressions for `qmKet00` and `qmKetPhiPlus`

Both vectors live in `EuclideanSpace ℂ (Fin 4)` and have explicit
component expressions; we expose those for the headline proof.

`qmKet00.ofLp` is `1` at index `0` and `0` elsewhere. `qmKetPhiPlus.ofLp`
is `(1/√2)` at indices `0` and `3` and `0` elsewhere. -/

private lemma qmKet00_ofLp_zero : qmKet00.ofLp 0 = (1 : ℂ) := by
  simp [qmKet00, EuclideanSpace.single]

private lemma qmKet00_ofLp_one : qmKet00.ofLp 1 = (0 : ℂ) := by
  simp [qmKet00, EuclideanSpace.single]

private lemma qmKet00_ofLp_two : qmKet00.ofLp 2 = (0 : ℂ) := by
  simp [qmKet00, EuclideanSpace.single]

private lemma qmKet00_ofLp_three : qmKet00.ofLp 3 = (0 : ℂ) := by
  simp [qmKet00, EuclideanSpace.single]

private lemma qmKetPhiPlus_ofLp_zero :
    qmKetPhiPlus.ofLp 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma qmKetPhiPlus_ofLp_one : qmKetPhiPlus.ofLp 1 = (0 : ℂ) := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma qmKetPhiPlus_ofLp_two : qmKetPhiPlus.ofLp 2 = (0 : ℂ) := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

private lemma qmKetPhiPlus_ofLp_three :
    qmKetPhiPlus.ofLp 3 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [qmKetPhiPlus, EuclideanSpace.single]

/-- For any row index `k`, `(qmBellPrepCircuit *ᵥ qmKet00.ofLp) k`
    collapses to the column-0 entry `qmBellPrepCircuit k 0`, because
    `qmKet00.ofLp` is `1` at index `0` and `0` elsewhere. -/
private lemma qmBellPrepCircuit_mulVec_qmKet00 (k : Fin 4) :
    (qmBellPrepCircuit *ᵥ qmKet00.ofLp) k = qmBellPrepCircuit k 0 := by
  show qmBellPrepCircuit k ⬝ᵥ qmKet00.ofLp = qmBellPrepCircuit k 0
  show ∑ j, qmBellPrepCircuit k j * qmKet00.ofLp j = qmBellPrepCircuit k 0
  rw [Fin.sum_univ_four, qmKet00_ofLp_zero, qmKet00_ofLp_one,
      qmKet00_ofLp_two, qmKet00_ofLp_three]
  ring

/-- **Bell-prep headline identity: `(CNOT ∘ (H ⊗ I)) |00⟩ = |Φ⁺⟩`.**

The matrix `qmBellPrepCircuit` applied to the `|00⟩` standard basis
vector produces the Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. This is the
genuine empirical identity the Bell-state-preparation circuit
encodes; the factorisation `qmBellPrep_factorisation` above is the
defining decomposition.

**Proof.** Componentwise via `ext`: expose the matrix-mulVec form
via `Matrix.toLpLin_apply`, then collapse the mulVec to column 0 via
`qmBellPrepCircuit_mulVec_qmKet00`, and compare to `qmKetPhiPlus.ofLp i`
via the four column-0 and `qmKetPhiPlus_ofLp_*` lemmas. -/
theorem qmBellPrep_yields_phiplus :
    (Matrix.toEuclideanLin qmBellPrepCircuit) qmKet00 = qmKetPhiPlus := by
  ext i
  show (Matrix.toLpLin 2 2 qmBellPrepCircuit) qmKet00 i = qmKetPhiPlus i
  rw [Matrix.toLpLin_apply]
  show (qmBellPrepCircuit *ᵥ qmKet00.ofLp) i = qmKetPhiPlus.ofLp i
  rw [qmBellPrepCircuit_mulVec_qmKet00]
  -- Goal: qmBellPrepCircuit i 0 = qmKetPhiPlus.ofLp i.
  fin_cases i
  · change qmBellPrepCircuit 0 0 = qmKetPhiPlus.ofLp 0
    rw [qmBellPrepCircuit_col0_zero, qmKetPhiPlus_ofLp_zero]
  · change qmBellPrepCircuit 1 0 = qmKetPhiPlus.ofLp 1
    rw [qmBellPrepCircuit_col0_one, qmKetPhiPlus_ofLp_one]
  · change qmBellPrepCircuit 2 0 = qmKetPhiPlus.ofLp 2
    rw [qmBellPrepCircuit_col0_two, qmKetPhiPlus_ofLp_two]
  · change qmBellPrepCircuit 3 0 = qmKetPhiPlus.ofLp 3
    rw [qmBellPrepCircuit_col0_three, qmKetPhiPlus_ofLp_three]

end Gates
end QM
end Empirical
end CSD
