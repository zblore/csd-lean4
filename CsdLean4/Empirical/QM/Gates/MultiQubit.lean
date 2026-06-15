import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

/-!
# Empirical/QM: Multi-qubit gates (Toffoli, Fredkin)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Universal classical reversible logic via Toffoli (CCNOT) and Fredkin
(CSWAP) gates on three qubits. Both are 8×8 real symmetric permutation
matrices — Hermitian and involutive, hence unitary. Each `qmG_hermitian`
(`Gᴴ = G`) combines with the involutive `qmG_mul_self` to give the unitarity
`qmG_unitary` (`Gᴴ * G = 1`), now proved for both gates.

## Contents

- `qmToffoli` (CCNOT): flips qubit 2 iff qubits 0 and 1 are both 1; Hermitian, unitary.
- `qmFredkin` (CSWAP): swaps qubits 1 and 2 iff qubit 0 is 1; Hermitian, unitary.

Basis order: `|000⟩, |001⟩, ..., |111⟩` = `Fin 8`.

Function-based matrix definitions (the `!!` notation fails to
propagate ℂ elaboration cleanly for 8×8 sparse permutations).
-/

open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace Gates

/-- Toffoli (CCNOT) gate on `Fin 8`. Permutes `|110⟩` ↔ `|111⟩`,
acts as identity elsewhere. Basis order: bit 0 high, bit 2 low, so
`|110⟩` = Fin 6 and `|111⟩` = Fin 7. -/
noncomputable def qmToffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of (fun i j : Fin 8 =>
    match i, j with
    | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1
    | 4, 4 => 1 | 5, 5 => 1
    | 6, 7 => 1 | 7, 6 => 1
    | _, _ => 0)

set_option maxHeartbeats 1000000 in
/-- Toffoli is involutive. -/
theorem qmToffoli_mul_self : qmToffoli * qmToffoli = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmToffoli, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

set_option maxHeartbeats 1000000 in
/-- Toffoli is Hermitian (real symmetric `{0,1}` permutation matrix): `Toffoliᴴ = Toffoli`. -/
theorem qmToffoli_hermitian : qmToffoliᴴ = qmToffoli := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmToffoli, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- Toffoli is unitary: `Toffoliᴴ * Toffoli = 1` (Hermitian + involutive). -/
theorem qmToffoli_unitary : qmToffoliᴴ * qmToffoli = 1 := by
  rw [qmToffoli_hermitian, qmToffoli_mul_self]

/-- Fredkin (CSWAP) gate on `Fin 8`. Permutes `|101⟩` ↔ `|110⟩`,
acts as identity elsewhere. -/
noncomputable def qmFredkin : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of (fun i j : Fin 8 =>
    match i, j with
    | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1
    | 4, 4 => 1
    | 5, 6 => 1 | 6, 5 => 1
    | 7, 7 => 1
    | _, _ => 0)

set_option maxHeartbeats 1000000 in
/-- Fredkin is involutive. -/
theorem qmFredkin_mul_self : qmFredkin * qmFredkin = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmFredkin, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

set_option maxHeartbeats 1000000 in
/-- Fredkin is Hermitian (real symmetric `{0,1}` permutation matrix): `Fredkinᴴ = Fredkin`. -/
theorem qmFredkin_hermitian : qmFredkinᴴ = qmFredkin := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmFredkin, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- Fredkin is unitary: `Fredkinᴴ * Fredkin = 1` (Hermitian + involutive). -/
theorem qmFredkin_unitary : qmFredkinᴴ * qmFredkin = 1 := by
  rw [qmFredkin_hermitian, qmFredkin_mul_self]

end Gates
end QM
end Empirical
end CSD
