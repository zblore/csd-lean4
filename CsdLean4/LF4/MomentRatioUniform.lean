import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Basis.Fin
import CsdLean4.LF4.MomentMarginalUniform

/-!
# LF4 plan B, Part 2, Slice 3 (L5.3): the ratio map sends `expHalf × expHalf` to uniform

`ratioSqNorm_map_expHalf_prod : R∗ (expHalf.prod expHalf) = volume.restrict (Ioo 0 1)`,
where `R q = q.1 / (q.1 + q.2)`.

This is the crux of the moment-marginal route discharging
`CSD.LF4.fs_moment_pushforward_uniform`. The proof is a 2-D change of variables
through the diffeomorphism `Ψ(T,S) = (T·S, (1−T)·S)` from `Ioo 0 1 ×ˢ Ioi 0` onto
the open quadrant `Q = Ioi 0 ×ˢ Ioi 0`, with Jacobian determinant `S`. After the
substitution the `S`-integral factors out as the radial constant
`∫_{S>0} (1/4)·S·e^{−S/2} dS = 1` (a `Gamma 2 = 1` computation), leaving the bare
`g(T)` integral over `Ioo 0 1`.

This file builds the four independent ingredients (radial constant, the `fderiv`
and its determinant, injectivity, image) and assembles them. See
`specs/plan-b-detail.md` Part 2, Slice 3.
-/

open MeasureTheory Real Set Module
open scoped ENNReal

namespace CSD
namespace LF4

/-- **L5.3 radial constant.** `∫⁻_{S>0} (1/4)·S·e^{−S/2} dS = 1`. This is the
normalisation that makes the substituted `S`-integral collapse to `1`; it is the
chi-squared(2) total mass, a `Gamma 2 = 1!` computation. -/
theorem lintegral_radial_const :
    ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal ((1 / 4) * S * Real.exp (-S / 2)) = 1 := by
  -- Reduce to the Bochner integral via `ofReal_integral_eq_lintegral_ofReal`.
  have hnonneg : ∀ S ∈ Ioi (0 : ℝ), 0 ≤ (1 / 4) * S * Real.exp (-S / 2) := by
    intro S hS; simp only [mem_Ioi] at hS; positivity
  -- The base radial integral `∫_{S>0} S·e^{−S/2} = 4` (first moment of Exp(1/2)).
  have hbase : ∫ t in Ioi (0 : ℝ), t * Real.exp (-t / 2) = 4 := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / 2)
      (by norm_num) (by norm_num)
    -- Simplify the RHS `(1/(1/2))^2 · Gamma 2 = 4` in isolation.
    have hRHS : ((1 : ℝ) / (1 / 2)) ^ (2 : ℝ) * Real.Gamma 2 = 4 := by
      rw [Real.Gamma_two, mul_one, show ((1 : ℝ) / (1 / 2)) = 2 by norm_num, Real.rpow_two]
      norm_num
    rw [hRHS] at h
    rw [← h]
    -- Match the integrands: `t^(2-1) = t`, `exp(-(1/2 · t)) = exp(-t/2)` on `Ioi 0`.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi, Real.rpow_one, show ((2 : ℝ) - 1) = 1 by norm_num] at *
    congr 2
    ring
  -- Integrability of `t·e^{−t/2}` on `Ioi 0` (needed for the ofReal↔lintegral bridge).
  have hint : IntegrableOn (fun t : ℝ => t * Real.exp (-t / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1 / 2)
      (by norm_num) (le_refl 1) (by norm_num)
    apply h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi, Real.rpow_one] at *
    congr 2
    ring
  have hint' : IntegrableOn (fun t : ℝ => (1 / 4) * t * Real.exp (-t / 2)) (Ioi 0) := by
    have : (fun t : ℝ => (1 / 4) * t * Real.exp (-t / 2))
        = (fun t : ℝ => (1 / 4 : ℝ) * (t * Real.exp (-t / 2))) := by ext t; ring
    rw [this]
    exact hint.const_mul _
  -- The Bochner value `∫_{S>0} (1/4)·S·e^{−S/2} = 1`.
  have hval : ∫ S in Ioi (0 : ℝ), (1 / 4) * S * Real.exp (-S / 2) = 1 := by
    rw [show (∫ S in Ioi (0 : ℝ), (1 / 4) * S * Real.exp (-S / 2))
          = ∫ S in Ioi (0 : ℝ), (1 / 4) * (S * Real.exp (-S / 2)) from by
        apply setIntegral_congr_fun measurableSet_Ioi; intro S _; ring,
      integral_const_mul, hbase]
    norm_num
  -- Bridge `ofReal ∘ Bochner = lintegral ∘ ofReal` over `volume.restrict (Ioi 0)`.
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnonneg)),
    hval, ENNReal.ofReal_one]

/-! ## The substitution diffeomorphism `Ψ(T,S) = (T·S, (1−T)·S)` -/

/-- The inverse substitution `Ψ(T,S) = (T·S, (1−T)·S)`. It carries
`Ioo 0 1 ×ˢ Ioi 0` bijectively onto the open quadrant `Ioi 0 ×ˢ Ioi 0`, with
constant-sign Jacobian determinant `S`. -/
noncomputable def Psi (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * p.2, (1 - p.1) * p.2)

/-- The Fréchet derivative of `Ψ` at `(T,S)`, as the explicit continuous linear
map `v ↦ (S·v.1 + T·v.2, (−S)·v.1 + (1−T)·v.2)` (matrix `[[S,T],[−S,1−T]]`). -/
noncomputable def psiFDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      p.2 • (0 - ContinuousLinearMap.fst ℝ ℝ ℝ))

/-- `Ψ` is Fréchet differentiable everywhere with derivative `psiFDeriv`. The
derivative is taken in the exact shape produced by `HasFDerivAt.mul`/`.prodMk`,
so the construction is a single `exact`. -/
theorem hasFDerivAt_Psi (p : ℝ × ℝ) : HasFDerivAt Psi (psiFDeriv p) p :=
  ((hasFDerivAt_fst.mul hasFDerivAt_snd).prodMk
    (((hasFDerivAt_const (1 : ℝ) p).sub hasFDerivAt_fst).mul hasFDerivAt_snd))

/-- **Jacobian determinant.** `det (psiFDeriv (T,S)) = S`. -/
theorem psiFDeriv_det (p : ℝ × ℝ) : (psiFDeriv p).det = p.2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, psiFDeriv,
    Basis.finTwoProd_zero, Basis.finTwoProd_one, Basis.coe_finTwoProd_repr,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Pi.smul_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `Ψ` is injective on `Ioo 0 1 ×ˢ Ioi 0`: from `Ψ(T,S) = (TS,(1−T)S)`, the sum
of components recovers `S`, and then `T` (since `S > 0`). -/
theorem injOn_Psi : InjOn Psi (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
  rintro ⟨T₁, S₁⟩ h₁ ⟨T₂, S₂⟩ h₂ heq
  simp only [Set.mem_prod, mem_Ioo, mem_Ioi] at h₁ h₂
  simp only [Psi, Prod.mk.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  have hS : S₁ = S₂ := by linear_combination e1 + e2
  rw [hS] at e1
  exact Prod.ext (mul_right_cancel₀ (ne_of_gt h₂.2) e1) hS

/-- The image of `Ψ` over `Ioo 0 1 ×ˢ Ioi 0` is the open quadrant `Ioi 0 ×ˢ Ioi 0`;
the preimage of `(A,B)` is `(A/(A+B), A+B)`. -/
theorem image_Psi :
    Psi '' (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
  ext ⟨A, B⟩
  simp only [mem_image, Set.mem_prod, mem_Ioo, mem_Ioi, Psi, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨T, S, ⟨⟨hT0, hT1⟩, hS⟩, rfl, rfl⟩
    exact ⟨mul_pos hT0 hS, mul_pos (by linarith) hS⟩
  · rintro ⟨hA, hB⟩
    refine ⟨A / (A + B), A + B, ⟨⟨by positivity, ?_⟩, by positivity⟩, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · field_simp
    · field_simp; ring

end LF4
end CSD
