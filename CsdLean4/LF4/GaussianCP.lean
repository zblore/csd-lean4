import CsdLean4.LF4.GaussianFS
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# LF4 plan B, Part 1 (Option 2): `gaussianCP = fubiniStudyMeasure` via `ℝ⁴`

Identifies the Fubini–Study measure on `ℂℙ¹` with the projectivized standard
Gaussian, working through a hand-built real coordinate isometry
`coords : ℝ⁴ ≃ₗᵢ[ℝ] ℂ²` to keep `stdGaussian` on the clean real space (avoiding
the ℝ/ℂ typeclass diamond on `EuclideanSpace ℂ (Fin 2)`). See
`specs/plan-b-detail.md` Part 1 (Option 2).
-/

open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **C1.** The real coordinate isometry `ℝ⁴ ≃ₗᵢ[ℝ] ℂ²`:
`y ↦ (y₀ + y₁·i, y₂ + y₃·i)`. -/
noncomputable def coords :
    EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun y := (WithLp.equiv 2 (Fin 2 → ℂ)).symm
    ![(y 0 : ℂ) + (y 1 : ℂ) * Complex.I, (y 2 : ℂ) + (y 3 : ℂ) * Complex.I]
  invFun z := (WithLp.equiv 2 (Fin 4 → ℝ)).symm
    ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  map_add' x y := by
    ext i
    fin_cases i <;>
      simp [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.ext_iff, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;> push_cast <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;>
      (simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, PiLp.smul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, RingHom.id_apply,
        smul_eq_mul, Complex.real_smul]
       push_cast
       ring)
  left_inv y := by
    ext i
    fin_cases i <;>
      simp [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
  right_inv z := by
    ext i
    fin_cases i <;>
      simp [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.ext_iff, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  norm_map' y := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_four]
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Real.norm_eq_abs, sq_abs]
    ring

/-- **C2.** The standard Gaussian transported to `ℂ²` via the coordinate
isometry. A probability measure on `ℂ²` (kept off the diamond-prone direct
`stdGaussian (EuclideanSpace ℂ (Fin 2))`). -/
noncomputable def gaussianH : Measure (EuclideanSpace ℂ (Fin 2)) :=
  Measure.map coords (stdGaussian (EuclideanSpace ℝ (Fin 4)))

instance instProbGaussianH : IsProbabilityMeasure gaussianH := by
  unfold gaussianH
  exact isProbabilityMeasure_map coords.continuous.measurable.aemeasurable

/-- The projectivization map `ℂ² → ℂℙ¹`, with junk value `p₀` at `0` (which is
`gaussianH`-null). -/
noncomputable def gaussianProj (p₀ : CPN 2) (v : EuclideanSpace ℂ (Fin 2)) : CPN 2 :=
  if h : v = 0 then p₀ else Projectivization.mk ℂ v h

lemma measurable_gaussianProj (p₀ : CPN 2) : Measurable (gaussianProj p₀) := by
  borelize (EuclideanSpace ℂ (Fin 2))
  exact Measurable.dite measurable_const Projectivization.measurable_mk'
    (measurableSet_singleton 0)

/-- **C3.** The projectivized Gaussian on `ℂℙ¹`. -/
noncomputable def gaussianCP (p₀ : CPN 2) : Measure (CPN 2) :=
  Measure.map (gaussianProj p₀) gaussianH

instance instProbGaussianCP (p₀ : CPN 2) : IsProbabilityMeasure (gaussianCP p₀) := by
  unfold gaussianCP
  exact isProbabilityMeasure_map (measurable_gaussianProj p₀).aemeasurable

end LF4
end CSD
