/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF3.Singlet.JointProjector
import Mathlib.Analysis.Matrix.Hermitian

/-!
# LF3 Singlet / JointEig: genuine joint spin eigenstates of the singlet (LF4 §3)

**Category:** 3-Local (LF4 §3 discharge — genuine joint spin eigenvectors).

Constructs the **actual** joint spin eigenstate at sector `(s, t)` as the
normalised projection of the singlet onto that sector,
`singletJointEig s t := (√P_st)⁻¹ • (Πˢ(a)⊗Πᵗ(b)) ψ⁻`, and proves the facts a
`MeasurementJointEig` bundle needs **as theorems** rather than carried
hypotheses:

- `singletJointEig_norm` — unit norm (uses `jointSpinProj` Hermitian +
  idempotent + the Born expectation identity);
- `singletJointEig_born` — `‖⟨ψ⁻, singletJointEig s t⟩‖² = P_st a b s t`
  (the LF4-todo §3 target);
- `singletJointEig_orthogonal` — distinct sectors give orthogonal eigenstates.

All over `EuclideanSpace ℂ (Fin 2 × Fin 2)`; the LF4 bundle re-indexes to
`Fin N` via a `LinearIsometryEquiv` (inner products / norms transport).

**Generic-context restriction.** The `(√P_st)⁻¹` normalisation requires
`P_st a b s t ≠ 0`, i.e. `s·t·(a·b) ≠ 1`. For a *generic* context
(`|a·b| < 1`, e.g. all Bell-test settings) every sector has `P_st > 0`, so the
construction covers all four sectors. Collinear settings (`a = ±b`) have one
vanishing sector and are excluded; they carry no Born information anyway.
-/

open scoped BigOperators ComplexConjugate
open Matrix

namespace CSD
namespace LF3

variable (s t : Sign) (a b : DetectorSetting)

/-- The genuine joint spin eigenstate at sector `(s, t)`: the normalised
    projection of the singlet onto the range of `Πˢ(a)⊗Πᵗ(b)`. -/
noncomputable def singletJointEig : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt (P_st a b s t) : ℂ))⁻¹ •
    (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)

/-- `toEuclideanLin` turns matrix multiplication into composition. -/
lemma toEuclideanLin_mul_apply
    (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (v : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    Matrix.toEuclideanLin (M * N) v
      = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- The joint projector acts idempotently on vectors. -/
lemma toEuclideanLin_jointSpinProj_idem
    (v : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    Matrix.toEuclideanLin (jointSpinProj s t a b)
        (Matrix.toEuclideanLin (jointSpinProj s t a b) v)
      = Matrix.toEuclideanLin (jointSpinProj s t a b) v := by
  rw [← toEuclideanLin_mul_apply, jointSpinProj_idem]

/-- `T_P` is symmetric (self-adjoint), from `jointSpinProj` Hermitian. -/
lemma toEuclideanLin_jointSpinProj_isSymmetric :
    (Matrix.toEuclideanLin (jointSpinProj s t a b)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.symm.mp (jointSpinProj_isHermitian s t a b)

/-- The squared norm of the singlet's projection onto the sector is `P_st`. -/
lemma norm_sq_jointSpinProj_singlet :
    ‖Matrix.toEuclideanLin (jointSpinProj s t a b) singlet‖ ^ 2 = P_st a b s t := by
  have hsymm := toEuclideanLin_jointSpinProj_isSymmetric s t a b
  have key : inner ℂ (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)
        (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet) = (P_st a b s t : ℂ) := by
    rw [hsymm singlet (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet),
        toEuclideanLin_jointSpinProj_idem]
    exact singlet_jointSpinProj_expectation s t a b
  have h2 : ‖Matrix.toEuclideanLin (jointSpinProj s t a b) singlet‖ ^ 2
      = RCLike.re (inner ℂ (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)
          (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)) :=
    (inner_self_eq_norm_sq _).symm
  rw [h2, key]
  simp

/-- **Unit norm of the joint spin eigenstate** (generic context). -/
theorem singletJointEig_norm (hP : 0 < P_st a b s t) :
    ‖singletJointEig s t a b‖ = 1 := by
  unfold singletJointEig
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnn : ‖Matrix.toEuclideanLin (jointSpinProj s t a b) singlet‖
      = Real.sqrt (P_st a b s t) := by
    rw [← norm_sq_jointSpinProj_singlet s t a b, Real.sqrt_sq (norm_nonneg _)]
  rw [hnn, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hP)]

/-- **The Born identity for the genuine joint spin eigenstate** (LF4-todo §3):
    `‖⟨ψ⁻, singletJointEig s t⟩‖² = P_st a b s t`. -/
theorem singletJointEig_born (hP : 0 < P_st a b s t) :
    ‖inner ℂ singlet (singletJointEig s t a b)‖ ^ 2 = P_st a b s t := by
  have hexp : inner ℂ singlet (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)
      = (P_st a b s t : ℂ) := singlet_jointSpinProj_expectation s t a b
  have hinner : inner ℂ singlet (singletJointEig s t a b)
      = (Real.sqrt (P_st a b s t) : ℂ) := by
    unfold singletJointEig
    rw [inner_smul_right, hexp,
        show (P_st a b s t : ℂ)
            = (Real.sqrt (P_st a b s t) : ℂ) * (Real.sqrt (P_st a b s t) : ℂ) by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hP.le],
        ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast Real.sqrt_ne_zero'.mpr hP), one_mul]
  rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hP.le]

/-- **Distinct sectors give orthogonal joint spin eigenstates.** -/
theorem singletJointEig_orthogonal {s t s' t' : Sign} (a b : DetectorSetting)
    (h : (s, t) ≠ (s', t')) :
    inner ℂ (singletJointEig s t a b) (singletJointEig s' t' a b) = 0 := by
  have hsymm := toEuclideanLin_jointSpinProj_isSymmetric s t a b
  have hzero : inner ℂ (Matrix.toEuclideanLin (jointSpinProj s t a b) singlet)
        (Matrix.toEuclideanLin (jointSpinProj s' t' a b) singlet) = 0 := by
    rw [hsymm singlet (Matrix.toEuclideanLin (jointSpinProj s' t' a b) singlet),
        ← toEuclideanLin_mul_apply, jointSpinProj_mul_orthogonal a b h]
    simp
  unfold singletJointEig
  rw [inner_smul_left, inner_smul_right, hzero, mul_zero, mul_zero]

end LF3
end CSD
