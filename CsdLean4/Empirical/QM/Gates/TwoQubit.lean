import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

/-!
# Empirical/QM: Two-qubit gates (CNOT, SWAP, CZ)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Pure linear-algebra definitions for the canonical two-qubit gates on
`Matrix (Fin 4) (Fin 4) ℂ`, with their **involutivity** properties
(`G * G = 1`). These gates are real Hermitian permutation/diagonal matrices, so
involutivity coincides with unitarity: each `qmG*_hermitian` (`Gᴴ = G`) combines
with the involutive `qmG*_mul_self` to give `qmG*_unitary` (`Gᴴ * G = 1`), now
proved for every gate. No CSD ontology; the CSD-side reading lives in the
companion `Empirical/CSD/Gates/TwoQubit.lean`.

## Contents

- `qmCNOT`: controlled-NOT, involutive, Hermitian, unitary.
- `qmSWAP`: swap, involutive, Hermitian, unitary.
- `qmCZ`: controlled-Z, involutive, Hermitian, unitary.

Basis order `|00⟩, |01⟩, |10⟩, |11⟩` (qubit-0 = high bit, qubit-1
= low bit). Function-based matrix definitions; the `!!` notation
fails to propagate ℂ elaboration cleanly for 4×4.
-/

open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace Gates

/-- Controlled-NOT gate on `Fin 4`. -/
noncomputable def qmCNOT : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    match i, j with
    | 0, 0 => 1
    | 1, 1 => 1
    | 2, 3 => 1
    | 3, 2 => 1
    | _, _ => 0)

/-- CNOT is involutive: `CNOT * CNOT = 1`. -/
theorem qmCNOT_mul_self : qmCNOT * qmCNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmCNOT, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

/-- CNOT is Hermitian (real symmetric `{0,1}` permutation matrix): `CNOTᴴ = CNOT`. -/
theorem qmCNOT_hermitian : qmCNOTᴴ = qmCNOT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmCNOT, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- CNOT is unitary: `CNOTᴴ * CNOT = 1` (Hermitian + involutive). -/
theorem qmCNOT_unitary : qmCNOTᴴ * qmCNOT = 1 := by
  rw [qmCNOT_hermitian, qmCNOT_mul_self]

/-- SWAP gate on `Fin 4`. -/
noncomputable def qmSWAP : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    match i, j with
    | 0, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 3, 3 => 1
    | _, _ => 0)

/-- SWAP is involutive. -/
theorem qmSWAP_mul_self : qmSWAP * qmSWAP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmSWAP, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

/-- SWAP is Hermitian: `SWAPᴴ = SWAP`. -/
theorem qmSWAP_hermitian : qmSWAPᴴ = qmSWAP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmSWAP, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- SWAP is unitary: `SWAPᴴ * SWAP = 1`. -/
theorem qmSWAP_unitary : qmSWAPᴴ * qmSWAP = 1 := by
  rw [qmSWAP_hermitian, qmSWAP_mul_self]

/-- Controlled-Z gate: phase-flip on `|11⟩`. -/
noncomputable def qmCZ : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (fun i j : Fin 4 =>
    match i, j with
    | 0, 0 => 1
    | 1, 1 => 1
    | 2, 2 => 1
    | 3, 3 => -1
    | _, _ => 0)

/-- CZ is involutive. -/
theorem qmCZ_mul_self : qmCZ * qmCZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmCZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

/-- CZ is Hermitian (real diagonal `{1,-1}` matrix): `CZᴴ = CZ`. -/
theorem qmCZ_hermitian : qmCZᴴ = qmCZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmCZ, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- CZ is unitary: `CZᴴ * CZ = 1`. -/
theorem qmCZ_unitary : qmCZᴴ * qmCZ = 1 := by
  rw [qmCZ_hermitian, qmCZ_mul_self]

end Gates
end QM
end Empirical
end CSD
