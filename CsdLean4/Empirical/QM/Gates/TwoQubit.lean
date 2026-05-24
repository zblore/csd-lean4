import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

/-!
# Empirical/QM: Two-qubit gates (CNOT, SWAP, CZ)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Pure linear-algebra definitions + unitarity properties for the
canonical two-qubit gates on `Matrix (Fin 4) (Fin 4) ℂ`. No CSD
ontology; the CSD-side reading lives in the companion
`Empirical/CSD/Gates/TwoQubit.lean`.

## Contents

- `qmCNOT`: controlled-NOT, involutive.
- `qmSWAP`: swap, involutive.
- `qmCZ`: controlled-Z, involutive.

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

end Gates
end QM
end Empirical
end CSD
