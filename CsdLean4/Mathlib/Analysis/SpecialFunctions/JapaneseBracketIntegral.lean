/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The integral of the Japanese bracket power `(1 + ‖w‖²)^{-(n+1)}` over `ℂⁿ`

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.SpecialFunctions.JapaneseBracket`, which at the pin proves only the
*integrability* of `(1 + ‖x‖²)^{-r/2}` for `r > dim`, never a value).

The analytic half of the Fubini–Study mass computation: the total mass of the
Fubini–Study volume is `4ⁿ n!` times this integral, and its value is `πⁿ / n!`.

* `bracketAnti a k` — the antiderivative `-(a + r²)^{-(k+1)} / (2(k+1))` of `r (a + r²)^{-(k+2)}`,
  with `hasDerivAt_bracketAnti`, `continuous_bracketAnti`, `tendsto_bracketAnti` (to `0` at `∞`);
* ★ `integral_Ioi_mul_pow_inv_add_sq` — the radial integral
  `∫₀^∞ r (a + r²)^{-(k+2)} dr = a^{-(k+1)} / (2(k+1))`, by the fundamental theorem of calculus on
  `[0, ∞)` (`integral_Ioi_of_hasDerivAt_of_tendsto`), with `integrableOn_Ioi_mul_pow_inv_add_sq`;
* ★ `lintegral_complex_pow_inv_add_norm_sq` — the planar integral
  `∫_ℂ (a + |z|²)^{-(k+2)} dz = π a^{-(k+1)} / (k+1)`, by polar coordinates
  (`Complex.lintegral_comp_polarCoord_symm`) and Tonelli;
* ★★ `lintegral_pi_pow_inv_one_add_sum_norm_sq` — **`∫_{ℂⁿ} (1 + ∑ⱼ |wⱼ|²)^{-(n+1)} dw = πⁿ / n!`**,
  by induction on `n`: split off one coordinate (`measurePreserving_piFinSuccAbove`), integrate
  it out with the planar integral at `a = 1 + ‖w'‖²`, and recognise `π/(n+1)` times the case `n`.

## Honest scope

⚠️ Lebesgue integrals (`lintegral`) of `ENNReal.ofReal`, against `volume` on `Fin n → ℂ`
(the product of the Lebesgue measures on `ℂ = ℝ²`); the norm is written as the coordinate sum
`∑ⱼ ‖wⱼ‖²`, so no `EuclideanSpace` appears. Only the exponent `n + 1` on `ℂⁿ` is computed — the
one the top power needs — not the general `(1 + ‖x‖²)^{-r/2}`.

**Provenance and references.** The top-power plan (M7); `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`;
`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`; `Mathlib/MeasureTheory/Constructions/Pi.lean`
(`measurePreserving_piFinSuccAbove`); the completed-work ledger.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

noncomputable section

namespace MeasureTheory

/-! ### The radial integral -/

/-- The antiderivative `-(a + r²)^{-(k+1)} / (2(k+1))` of `r (a + r²)^{-(k+2)}`. -/
def bracketAnti (a : ℝ) (k : ℕ) (r : ℝ) : ℝ := -(((a + r ^ 2)⁻¹) ^ (k + 1) / (2 * (k + 1)))

theorem hasDerivAt_bracketAnti (a : ℝ) (ha : 0 < a) (k : ℕ) (r : ℝ) :
    HasDerivAt (bracketAnti a k) (r * ((a + r ^ 2)⁻¹) ^ (k + 1 + 1)) r := by
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add a
  have ht : a + r ^ 2 ≠ 0 := by positivity
  have h2 := h1.inv ht
  have h3 := ((h2.pow (k + 1)).div_const (2 * (k + 1))).neg
  refine h3.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Pi.inv_apply]
  rw [show -(2 * r) / (a + r ^ 2) ^ 2 = -(2 * r) * ((a + r ^ 2)⁻¹) ^ 2 by
    rw [div_eq_mul_inv, inv_pow]]
  generalize (a + r ^ 2)⁻¹ = u
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem continuous_bracketAnti (a : ℝ) (ha : 0 < a) (k : ℕ) : Continuous (bracketAnti a k) := by
  refine (Continuous.div_const (Continuous.pow ?_ _) _).neg
  exact (continuous_const.add (continuous_pow 2)).inv₀ fun r => by
    show a + r ^ 2 ≠ 0
    positivity

theorem tendsto_bracketAnti (a : ℝ) (k : ℕ) : Tendsto (bracketAnti a k) atTop (𝓝 0) := by
  have h0 : Tendsto (fun r : ℝ => (a + r ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left _ a (tendsto_pow_atTop two_ne_zero))
  have := ((h0.pow (k + 1)).div_const (2 * (k + 1))).neg
  show Tendsto (fun r : ℝ => -(((a + r ^ 2)⁻¹) ^ (k + 1) / (2 * (k + 1)))) atTop (𝓝 0)
  simpa using this

theorem integrableOn_Ioi_mul_pow_inv_add_sq (a : ℝ) (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun r : ℝ => r * ((a + r ^ 2)⁻¹) ^ (k + 1 + 1)) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (continuous_bracketAnti a ha k).continuousWithinAt
    (fun r _ => hasDerivAt_bracketAnti a ha k r)
    (fun r hr => by
      have : (0 : ℝ) < r := hr
      positivity)
    (tendsto_bracketAnti a k)

/-- ★ The radial integral `∫₀^∞ r (a + r²)^{-(k+2)} dr = a^{-(k+1)} / (2 (k+1))`. -/
theorem integral_Ioi_mul_pow_inv_add_sq (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), r * ((a + r ^ 2)⁻¹) ^ (k + 1 + 1) = (a⁻¹) ^ (k + 1) / (2 * (k + 1)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (continuous_bracketAnti a ha k).continuousWithinAt
    (fun r _ => hasDerivAt_bracketAnti a ha k r) (integrableOn_Ioi_mul_pow_inv_add_sq a ha k)
    (tendsto_bracketAnti a k)]
  simp [bracketAnti]

/-! ### The planar integral -/

/-- ★ The planar integral `∫_ℂ (a + |z|²)^{-(k+2)} dz = π a^{-(k+1)} / (k+1)`, by polar
coordinates. -/
theorem lintegral_complex_pow_inv_add_norm_sq (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2)⁻¹) ^ (k + 1 + 1))
      = ENNReal.ofReal (π * (a⁻¹) ^ (k + 1) / (k + 1)) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul, sq_abs]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * ENNReal.ofReal (((a + p.1 ^ 2)⁻¹) ^ (k + 1 + 1)) :=
    measurable_fst.ennreal_ofReal.mul
      ((((measurable_fst.pow_const 2).const_add a).inv.pow_const _).ennreal_ofReal)
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp_rw [setLIntegral_const, Real.volume_Ioo]
  have hmeas' : Measurable fun r : ℝ =>
      ENNReal.ofReal r * ENNReal.ofReal (((a + r ^ 2)⁻¹) ^ (k + 1 + 1)) :=
    measurable_id.ennreal_ofReal.mul
      ((((measurable_id.pow_const 2).const_add a).inv.pow_const _).ennreal_ofReal)
  rw [lintegral_mul_const _ hmeas']
  have hin : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ENNReal.ofReal (((a + r ^ 2)⁻¹) ^ (k + 1 + 1))
      = ENNReal.ofReal ((a⁻¹) ^ (k + 1) / (2 * (k + 1))) := by
    rw [← integral_Ioi_mul_pow_inv_add_sq a ha k,
      ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_mul_pow_inv_add_sq a ha k)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => by
          have : (0 : ℝ) < r := hr
          positivity))]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [ENNReal.ofReal_mul (le_of_lt hr)]
  rw [hin, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-! ### The integral over `ℂⁿ` -/

/-- ★★ **`∫_{ℂⁿ} (1 + ‖w‖²)^{-(n+1)} dw = πⁿ / n!`**, with `‖w‖² = ∑ⱼ ‖wⱼ‖²`: by induction on
`n`, splitting off one coordinate (`measurePreserving_piFinSuccAbove`) and integrating it out. -/
theorem lintegral_pi_pow_inv_one_add_sum_norm_sq :
    ∀ n : ℕ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ j, ‖w j‖ ^ 2)⁻¹) ^ (n + 1))
      = ENNReal.ofReal (π ^ n / n.factorial)
  | 0 => by
    simp [volume_pi]
  | n + 1 => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0
    rw [volume_pi, MeasurePreserving.lintegral_map_equiv _ _ (MeasurePreserving.symm _ hmp)]
    have hsymm : ∀ p : ℂ × (Fin n → ℂ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm p = Fin.cons p.1 p.2 :=
      fun p => Fin.insertNth_zero' p.1 p.2
    simp_rw [hsymm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hre : ∀ (z : ℂ) (S : ℝ), (1 + (‖z‖ ^ 2 + S)) = (1 + S) + ‖z‖ ^ 2 := fun z S => by ring
    simp_rw [hre]
    have hmeas : Measurable fun p : ℂ × (Fin n → ℂ) =>
        ENNReal.ofReal ((((1 + ∑ j, ‖p.2 j‖ ^ 2) + ‖p.1‖ ^ 2)⁻¹) ^ (n + 1 + 1)) :=
      ((((Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp measurable_snd).norm.pow_const 2).const_add 1).add
        (measurable_fst.norm.pow_const 2)).inv.pow_const _).ennreal_ofReal
    rw [lintegral_prod_symm _ hmeas.aemeasurable]
    have hinner : ∀ w' : Fin n → ℂ,
        ∫⁻ z : ℂ, ENNReal.ofReal ((((1 + ∑ j, ‖w' j‖ ^ 2) + ‖z‖ ^ 2)⁻¹) ^ (n + 1 + 1))
          = ENNReal.ofReal (π / (n + 1))
            * ENNReal.ofReal (((1 + ∑ j, ‖w' j‖ ^ 2)⁻¹) ^ (n + 1)) := fun w' => by
      rw [lintegral_complex_pow_inv_add_norm_sq _ (by positivity) n,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    simp_rw [hinner]
    have hmeas' : Measurable fun w' : Fin n → ℂ =>
        ENNReal.ofReal (((1 + ∑ j, ‖w' j‖ ^ 2)⁻¹) ^ (n + 1)) :=
      (((Finset.measurable_sum _ fun j _ =>
        (measurable_pi_apply j).norm.pow_const 2).const_add 1).inv.pow_const _).ennreal_ofReal
    rw [lintegral_const_mul _ hmeas', ← volume_pi, lintegral_pi_pow_inv_one_add_sum_norm_sq n,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end MeasureTheory
