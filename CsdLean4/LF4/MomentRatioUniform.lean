/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Basis.Fin
public import CsdLean4.LF4.MomentMarginalUniform

/-!
# LF4 plan B, Part 2, Slice 3 (L5.3): the ratio map sends `expHalf × expHalf` to uniform

**Category:** 3-Local (the ratio map sends `expHalf × expHalf` to uniform).

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
and its determinant, injectivity, image) and assembles them into
`ratioSqNorm_map_expHalf_prod`. Foundational-triple-only. See
`specs/plan-b-detail.md` Part 2, Slice 3.
-/

@[expose] public section

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
    add_apply, FunLike.coe_smul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Pi.smul_apply,
    ContinuousLinearMap.prod_apply, sub_apply,
    zero_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
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

/-! ## L5.3: the ratio map sends `expHalf × expHalf` to uniform on `(0,1)` -/

/-- **L5.3 (the crux).** The ratio `R q = q.1/(q.1+q.2)` pushes `expHalf × expHalf`
to the uniform measure on `(0,1)`. The change of variables through `Ψ` turns the
density into `(1/4)·S·e^{−S/2}` and the radial `S`-integral collapses to `1`
(`lintegral_radial_const`), leaving the bare `g(T)` integral over `(0,1)`. -/
theorem ratioSqNorm_map_expHalf_prod :
    Measure.map (fun q : ℝ × ℝ => q.1 / (q.1 + q.2)) (expHalf.prod expHalf)
      = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hR_meas : Measurable (fun q : ℝ × ℝ => q.1 / (q.1 + q.2)) :=
    measurable_fst.div (measurable_fst.add measurable_snd)
  refine Measure.ext_of_lintegral _ (fun g hg => ?_)
  rw [lintegral_map hg hR_meas, expHalf,
    prod_withDensity measurable_expHalf_density measurable_expHalf_density,
    ← Measure.volume_eq_prod,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : ℝ × ℝ =>
          ENNReal.ofReal (if 0 < z.1 then (1 / 2) * Real.exp (-z.1 / 2) else 0)
            * ENNReal.ofReal (if 0 < z.2 then (1 / 2) * Real.exp (-z.2 / 2) else 0)) from
        (measurable_expHalf_density.comp measurable_fst).mul
          (measurable_expHalf_density.comp measurable_snd))
      (by fun_prop : Measurable fun a : ℝ × ℝ => g (a.1 / (a.1 + a.2)))]
  simp only [Pi.mul_apply]
  -- The post-density integrand `F q = d q.1 · d q.2 · g(R q)` (folded by defeq).
  set d : ℝ → ℝ≥0∞ :=
    fun s => ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0) with hd
  have hd0 : ∀ s : ℝ, ¬ 0 < s → d s = 0 := fun s hs => by rw [hd]; simp [if_neg hs]
  have hdpos : ∀ s : ℝ, 0 < s → d s = ENNReal.ofReal ((1 / 2) * Real.exp (-s / 2)) :=
    fun s hs => by rw [hd]; simp [if_pos hs]
  -- Step B: the integrand is supported on the open quadrant; restrict to it.
  have hFeqInd :
      (fun q : ℝ × ℝ => d q.1 * d q.2 * g (q.1 / (q.1 + q.2)))
        = (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
            (fun q => d q.1 * d q.2 * g (q.1 / (q.1 + q.2))) := by
    ext q
    rw [Set.indicator_apply]
    by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
    · rw [if_pos hq]
    · rw [if_neg hq]
      rw [Set.mem_prod, mem_Ioi, mem_Ioi, not_and_or] at hq
      rcases hq with h | h
      · rw [hd0 q.1 h]; simp
      · rw [hd0 q.2 h]; simp
  -- The pointwise integrand identity on `D = Ioo 0 1 ×ˢ Ioi 0` after the substitution.
  have hcongr :
      ∀ x ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal |(psiFDeriv x).det|
            * (d (Psi x).1 * d (Psi x).2
                * g ((Psi x).1 / ((Psi x).1 + (Psi x).2)))
          = ENNReal.ofReal ((1 / 4) * x.2 * Real.exp (-x.2 / 2)) * g x.1 := by
    intro x hx
    rw [Set.mem_prod, mem_Ioo, mem_Ioi] at hx
    obtain ⟨⟨hT0, hT1⟩, hS⟩ := hx
    have hPsi1 : (Psi x).1 = x.1 * x.2 := rfl
    have hPsi2 : (Psi x).2 = (1 - x.1) * x.2 := rfl
    have hpos1 : 0 < x.1 * x.2 := mul_pos hT0 hS
    have hpos2 : 0 < (1 - x.1) * x.2 := mul_pos (by linarith) hS
    rw [psiFDeriv_det, abs_of_pos hS, hPsi1, hPsi2, hdpos _ hpos1, hdpos _ hpos2,
      show x.1 * x.2 / (x.1 * x.2 + (1 - x.1) * x.2) = x.1 from by
        rw [show x.1 * x.2 + (1 - x.1) * x.2 = x.2 from by ring, mul_div_assoc,
          div_self (ne_of_gt hS), mul_one],
      ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul hS.le]
    congr 2
    rw [show (1 / 2 * Real.exp (-(x.1 * x.2) / 2)) * (1 / 2 * Real.exp (-((1 - x.1) * x.2) / 2))
          = (1 / 4) * (Real.exp (-(x.1 * x.2) / 2) * Real.exp (-((1 - x.1) * x.2) / 2)) from by
        ring,
      ← Real.exp_add,
      show -(x.1 * x.2) / 2 + -((1 - x.1) * x.2) / 2 = -x.2 / 2 from by ring]
    ring
  show ∫⁻ (a : ℝ × ℝ), d a.1 * d a.2 * g (a.1 / (a.1 + a.2)) ∂volume = _
  rw [hFeqInd, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),
    ← image_Psi,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (measurableSet_Ioo.prod measurableSet_Ioi)
      (fun x _ => (hasFDerivAt_Psi x).hasFDerivWithinAt) injOn_Psi
      (fun q => d q.1 * d q.2 * g (q.1 / (q.1 + q.2))),
    setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi) hcongr,
    Measure.volume_eq_prod,
    setLIntegral_prod _ (by apply Measurable.aemeasurable; fun_prop)]
  -- Step E: collapse the inner radial integral to `1`, leaving `∫ g over (0,1)`.
  refine setLIntegral_congr_fun measurableSet_Ioo (fun T _ => ?_)
  show ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (1 / 4 * y * Real.exp (-y / 2)) * g T = g T
  rw [lintegral_mul_const _ (by fun_prop), lintegral_radial_const, one_mul]

end LF4
end CSD
