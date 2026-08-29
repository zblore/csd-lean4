/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Empirical/QM: Single-qubit gates (Hadamard, Phase S, Phase T)

**Category:** 3-Local (promotion-ready to 2-Framework on demand;
content is QM-generic and Cat-2 candidate parallel to NoCloning).

Pure linear-algebra definitions + unitarity properties for the
canonical single-qubit gates. No CSD ontology; the CSD-side reading
lives in the companion `Empirical/CSD/Gates/SingleQubit.lean`.

## Contents

- `qmH`: Hadamard `(1/√2) !![1, 1; 1, -1]`. Involutive (`qmH * qmH = 1`),
  Hermitian (`qmH_hermitian`), unitary (`qmH_unitary`).
- `qmS`: Phase `!![1, 0; 0, I]`. Diagonal; `qmS² = qmZ` (Pauli Z);
  unitary (`qmS_unitary`).
- `qmT`: π/4-phase `!![1, 0; 0, exp(iπ/4)]`. Diagonal; `qmT² = qmS`;
  unitary (`qmT_unitary`).

`qmZ` is included as an auxiliary (also re-exportable; conventional
Pauli `σ_z`). (The unitarity lemmas were added 2026-08-29: an audit found
the header promising them while only the squaring identities were proved —
the sibling `MultiQubit.lean` standard, `Gᴴ * G = 1`, now holds here too.)

## Naming

`qm`-prefixed matrix-level gates, serving the density-matrix / CSD-gates
ecosystem (`Empirical/CSD/Gates/`, `Einselection.lean`). The
**coordinate-operator** siblings on the register live in the Cat-1 tree
(`Mathlib/QuantumInfo/Clifford.lean`'s `sGate`/`hGate`, `Magic.lean`'s
`tGate` — where `T² = S` is `tGate_tGate`); the two layers serve different
consumer bases and neither derives from the other. The CSD-side companion
uses `csd`-prefixed names.

## Experimental provenance

These are standard textbook gates; specific experimental verification
is unit-test-level (gate fidelity measurements in any QC platform).
No single named experiment. -/

@[expose] public section

open Matrix Complex
open scoped Matrix

namespace CSD
namespace Empirical
namespace QM
namespace Gates

/-! ## Auxiliary: Pauli Z -/

/-- Pauli `σ_z = !![1, 0; 0, -1]`. Auxiliary for `qmS² = qmZ`. -/
noncomputable def qmZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-! ## Hadamard -/

/-- Hadamard gate `H = (1/√2) !![1, 1; 1, -1]`. -/
noncomputable def qmH : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; 1, -1]

/-- `H * H = I`. Hadamard is involutive. -/
theorem qmH_mul_self : qmH * qmH = 1 := by
  unfold qmH
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) from by
    rw [← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-- `Hᴴ = H`: the Hadamard is Hermitian (real symmetric). -/
theorem qmH_hermitian : qmHᴴ = qmH := by
  unfold qmH
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- `Hᴴ * H = 1`: the Hadamard is unitary (Hermitian + involutive). -/
theorem qmH_unitary : qmHᴴ * qmH = 1 := by
  rw [qmH_hermitian]
  exact qmH_mul_self

/-! ## Phase S -/

/-- Phase gate `S = !![1, 0; 0, I]`. -/
noncomputable def qmS : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- `S² = Z`. -/
theorem qmS_sq : qmS * qmS = qmZ := by
  unfold qmS qmZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `Sᴴ * S = 1`: the phase gate is unitary (`conj i · i = 1`). -/
theorem qmS_unitary : qmSᴴ * qmS = 1 := by
  unfold qmS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.conj_I]

/-! ## Phase T -/

/-- Phase gate `T = !![1, 0; 0, exp(iπ/4)]`. Diagonal eighth-root-of-unity
factor on the second basis state. -/
noncomputable def qmT : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * (Real.pi / 4))]

/-- `T² = S`. Follows from `exp(iπ/4)² = exp(iπ/2) = i`. -/
theorem qmT_sq : qmT * qmT = qmS := by
  unfold qmT qmS
  have h : Complex.exp (Complex.I * (Real.pi / 4)) *
           Complex.exp (Complex.I * (Real.pi / 4)) = Complex.I := by
    rw [← Complex.exp_add]
    have h_add : Complex.I * (↑Real.pi / 4) + Complex.I * (↑Real.pi / 4)
              = (↑Real.pi / 2) * Complex.I := by ring
    rw [h_add, Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h]

/-- `Tᴴ * T = 1`: the T gate is unitary (`e^{−iπ/4} · e^{iπ/4} = 1`). -/
theorem qmT_unitary : qmTᴴ * qmT = 1 := by
  have h : (starRingEnd ℂ) (Complex.exp (Complex.I * (Real.pi / 4)))
      * Complex.exp (Complex.I * (Real.pi / 4)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add,
      show (starRingEnd ℂ) (Complex.I * ((Real.pi : ℂ) / 4))
            + Complex.I * ((Real.pi : ℂ) / 4) = 0 from by
        simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
        ring,
      Complex.exp_zero]
  unfold qmT
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h]

end Gates
end QM
end Empirical
end CSD
