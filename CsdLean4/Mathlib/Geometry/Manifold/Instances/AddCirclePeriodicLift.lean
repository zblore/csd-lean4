/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.AddCircleTranslation
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Periodic lifts on the circle: derivative and smoothness in the translation atlas

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #195.

A function `f : ℝ → ℝ` of period `T` descends to `hf.lift : AddCircle T → ℝ`
(`Function.Periodic.lift`). In the translation atlas of `AddCircleTranslation.lean` every chart
inverse is the quotient map, so the lift read in any chart **is** `f`: its manifold derivative is
`f'` and it is as smooth as `f`.

* `Function.Periodic.deriv_periodic` — the derivative of a periodic function is periodic;
* `Function.Periodic.continuous_lift`;
* ★ `Function.Periodic.hasMFDerivAt_lift` — **the manifold derivative of the lift is `f'`**, read
  back on the circle through the lift of `f'`; `mfderiv_lift`;
* ★ `Function.Periodic.contMDiff_lift` — **the lift is `C^n` when `f` is**.

References: `Instances/AddCircleTranslation.lean` (`translationChart`, `chartAt_eq`,
`coe_translationChart`); `Mathlib/Algebra/Ring/Periodic.lean` (`Function.Periodic.lift`).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace Function.Periodic

variable {f : ℝ → ℝ} {T : ℝ}

/-- The derivative of a periodic function is periodic. -/
theorem deriv_periodic (hf : Periodic f T) : Periodic (deriv f) T := fun x => by
  rw [← deriv_comp_add_const (f := f) (a := T)]
  congr 1
  funext y
  exact hf y

/-- The lift is continuous when `f` is: the quotient map is a quotient map. -/
theorem continuous_lift (hf : Periodic f T) (hc : Continuous f) :
    Continuous (hf.lift : AddCircle T → ℝ) :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples T)).continuous_iff.mpr
    (hc.congr fun x => (hf.lift_coe x).symm)

variable [Fact (0 < T)]

/-- Read through any translation chart, the lift is `f`. -/
theorem lift_comp_chart_symm (hf : Periodic f T) (x : AddCircle T) (y : ℝ) :
    hf.lift ((chartAt ℝ x).symm y) = f y := by
  rw [AddCircle.chartAt_eq, AddCircle.translationChart_symm_apply]
  exact hf.lift_coe y

/-- The lift of `f'` at `x` is `f'` at the chart coordinate of `x`. -/
theorem deriv_periodic_lift_eq (hf : Periodic f T) (x : AddCircle T) :
    hf.deriv_periodic.lift x = deriv f (chartAt ℝ x x) := by
  conv_lhs => rw [← AddCircle.coe_translationChart (AddCircle.cutPoint x) x]
  exact hf.deriv_periodic.lift_coe _

/-- ★ **The manifold derivative of the lift is `f'`**, for the translation atlas. -/
theorem hasMFDerivAt_lift (hf : Periodic f T) (hd : Differentiable ℝ f) (x : AddCircle T) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) hf.lift x
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift x)) := by
  refine ⟨(hf.continuous_lift hd.continuous).continuousAt, ?_⟩
  have hw : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) x hf.lift = f := by
    funext y
    simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id, extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    exact hf.lift_comp_chart_symm x y
  rw [hw, hf.deriv_periodic_lift_eq x]
  simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ, extChartAt_coe,
    Function.comp_apply, id]
  exact hasDerivAt_iff_hasFDerivAt.1 (hd _).hasDerivAt

theorem mfderiv_lift (hf : Periodic f T) (hd : Differentiable ℝ f) (x : AddCircle T) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) hf.lift x
      = (1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift x) :=
  (hf.hasMFDerivAt_lift hd x).mfderiv

/-- ★ **The lift is `C^n` when `f` is**, for the translation atlas. -/
theorem contMDiff_lift (hf : Periodic f T) {n : WithTop ℕ∞} (hc : ContDiff ℝ n f) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n hf.lift := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(hf.continuous_lift hc.continuous).continuousAt, ?_⟩
  have hw : (extChartAt 𝓘(ℝ, ℝ) (hf.lift x) ∘ hf.lift ∘ (extChartAt 𝓘(ℝ, ℝ) x).symm) = f := by
    funext y
    simp only [Function.comp, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id,
      extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    exact hf.lift_comp_chart_symm x y
  rw [hw, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  exact hc.contDiffAt

end Function.Periodic

end
