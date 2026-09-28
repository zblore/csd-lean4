/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The quotient rule for the Fréchet derivative

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Analysis.Calculus.FDeriv.Mul`, beside
`HasFDerivAt.mul`). BACKLOG #89.

Mathlib has the quotient rule for the *one-dimensional* derivative (`HasDerivAt.div`) and, for the
Fréchet derivative, multiplication (`HasFDerivAt.mul`) and inversion in a normed division algebra
(`hasFDerivAt_inv'`), but not the quotient of two maps into a normed field — a gap one meets as soon
as a chart is a ratio of coordinates. MATHLIB-ABSENT(HasFDerivAt.div)

* ★ `HasFDerivAt.div` — `f / g` is differentiable where `g` does not vanish, with derivative
  `(g x)⁻¹ • f' − (f x / g x ^ 2) • g'`.

The target field `K` may be larger than the base field `𝕜` (the case this is written for: `ℝ`-Fréchet
derivatives of `ℂ`-valued coordinate ratios), which is exactly what `HasDerivAt.div` cannot express
and what `ContDiffAt.div` — stated for `f g : E → 𝕜`, the base field itself — does not cover either.
The corresponding `ContDiff` statement needs no new lemma: `ContDiffAt.inv` is already general in the
target field, so `hf.mul (hg.inv hx)` does it.

References: `Mathlib/Analysis/Calculus/FDeriv/Mul.lean` (`HasFDerivAt.mul`, `hasFDerivAt_inv'`);
`Mathlib/Analysis/Calculus/Deriv/Inv.lean` (`HasDerivAt.div`); `specs/BACKLOG.md` #89;
`specs/future-work.md`.
-/

@[expose] public section

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {K : Type*} [NormedField K] [NormedAlgebra 𝕜 K]

/-- ★ **The quotient rule for the Fréchet derivative**, for maps into a normed field over the base
field: where the denominator does not vanish,
`d(f / g) = (g x)⁻¹ • df − (f x / g x ^ 2) • dg`. -/
theorem HasFDerivAt.div {f g : E → K} {f' g' : E →L[𝕜] K} {x : E} (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' x) (hx : g x ≠ 0) :
    HasFDerivAt (fun y => f y / g y) ((g x)⁻¹ • f' - (f x / g x ^ 2) • g') x := by
  have hinv : HasFDerivAt (fun y => (g y)⁻¹)
      ((-mulLeftRight 𝕜 K (g x)⁻¹ (g x)⁻¹ : K →L[𝕜] K).comp g') x :=
    (hasFDerivAt_inv' hx).comp x hg
  have hmul : HasFDerivAt (fun y => f y * (g y)⁻¹)
      (f x • ((-mulLeftRight 𝕜 K (g x)⁻¹ (g x)⁻¹ : K →L[𝕜] K).comp g') + (g x)⁻¹ • f') x :=
    hf.mul hinv
  have heq : f x • ((-mulLeftRight 𝕜 K (g x)⁻¹ (g x)⁻¹ : K →L[𝕜] K).comp g') + (g x)⁻¹ • f'
      = (g x)⁻¹ • f' - (f x / g x ^ 2) • g' := by
    ext y
    simp only [FunLike.coe_add, FunLike.coe_sub, FunLike.coe_smul, ContinuousLinearMap.coe_comp,
      FunLike.coe_neg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      Function.comp_apply, smul_eq_mul, mulLeftRight_apply]
    field_simp
    ring
  have hfun : (fun y => f y / g y) = fun y => f y * (g y)⁻¹ := by
    funext y
    rw [div_eq_mul_inv]
  rw [hfun]
  exact hmul.congr_fderiv heq

end
