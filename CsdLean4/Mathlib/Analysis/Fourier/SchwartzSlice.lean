/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WeylSymbolClass

/-!
# Slicing a Schwartz function on a product

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #121(i), out of #92's split.

A Schwartz function on a product restricts to a Schwartz function on each slice. Mathlib has the
machinery — `SchwartzMap.compCLM` composes on the right with any map of temperate growth that does
not shrink the norm too much — but not the instance, because the slice map `w ↦ (e, w)` is **affine**
rather than linear and `fun_prop` has no `Prod.mk` rule for `HasTemperateGrowth`.

* ★ `Function.hasTemperateGrowth_prodMk_left` — the slice map has temperate growth, through
  `HasTemperateGrowth.of_fderiv`: its derivative is the *constant* `inr`, and `‖(e, w)‖` grows
  linearly;
* `SchwartzMap.sliceCLM` and `SchwartzMap.slice` — **the slice, as a continuous linear map in the
  kernel**, with ★ `SchwartzMap.slice_apply` its defining equation `slice K e w = K (e, w)`;
* ★★★ `WignerFunction.integral_conj_mul_weylOpK` — **the payoff**: the Weyl expectation formula holds
  on the Schwartz kernel class with **no hypotheses**. `WignerWeyl.lean` states it for a slice family
  under three assumptions (joint continuity, and a bound integrable in the first slot); #92(a1)
  discharged the last two for a jointly Schwartz kernel, and the slice supplies the family itself, so
  nothing is left to assume.

## Honest scope

⚠️ **Continuity in the slice parameter is not proved**, and that is the other half of #121(i). What is
continuous here is slicing *in the kernel* (`sliceCLM` is a continuous linear map `𝓢(E × F, G) →L
𝓢(F, G)` for each fixed `e`), which is what transfers theorems. That `e ↦ slice K e` is continuous
into `𝓢(F, G)` for the Schwartz topology is a different statement, it needs one more order of decay
and a mean-value estimate in the sliced variable, and Mathlib has no curry
`𝓢(E × F, G) ≃ 𝓢(E, 𝓢(F, G))` to get it from. It is **#123**, and nothing in the corpus needs it.

⚠️ **No partial Fourier transform**, which is #121(ii) and the half a pseudodifferential calculus
would need.

References: [`WeylSymbolClass.lean`](WeylSymbolClass.lean) (#92(a1), `weylOpK`, `weylOpK_eq_weylOp`,
`exists_integrable_bound`), [`WignerWeyl.lean`](WignerWeyl.lean) (`weylOp`, `weylSymbol`,
`integral_conj_mul_weylOp`); `specs/BACKLOG.md` #121, #92, #123.
-/

@[expose] public section

open MeasureTheory SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The slice map has temperate growth -/

/-- ★ **The slice map `w ↦ (e, w)` has temperate growth.** It is affine, so `fun_prop` cannot see it:
the derivative is the constant `inr` and the value grows linearly. -/
theorem Function.hasTemperateGrowth_prodMk_left (e : E) :
    Function.HasTemperateGrowth (fun w : F => (e, w)) := by
  refine Function.HasTemperateGrowth.of_fderiv ?_ ?_ (k := 1) (C := ‖e‖ + 1) ?_
  · have h : fderiv ℝ (fun w : F => (e, w)) = fun _ => ContinuousLinearMap.inr ℝ E F := by
      funext w
      exact (hasFDerivAt_prodMk_right e w).fderiv
    rw [h]
    exact Function.HasTemperateGrowth.const _
  · exact fun w => (hasFDerivAt_prodMk_right e w).differentiableAt
  · intro w
    have h1 : ‖((e, w) : E × F)‖ = max ‖e‖ ‖w‖ := Prod.norm_def _
    have h2 : max ‖e‖ ‖w‖ ≤ ‖e‖ + ‖w‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg w)) (le_add_of_nonneg_left (norm_nonneg e))
    rw [h1]
    nlinarith [norm_nonneg e, norm_nonneg w, h2]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The slice map does not shrink the norm, which is `compCLM`'s other hypothesis. -/
theorem exists_norm_le_prodMk_left (e : E) :
    ∃ (k : ℕ) (C : ℝ), ∀ w : F, ‖w‖ ≤ C * (1 + ‖((e, w) : E × F)‖) ^ k := by
  refine ⟨1, 1, fun w => ?_⟩
  have h : ‖w‖ ≤ ‖((e, w) : E × F)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  nlinarith [norm_nonneg ((e, w) : E × F), h]

/-! ### The slice -/

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 G]

/-- **Slicing a Schwartz function on a product, as a continuous linear map in the kernel.** -/
noncomputable def sliceCLM (e : E) : 𝓢(E × F, G) →L[𝕜] 𝓢(F, G) :=
  compCLM 𝕜 (Function.hasTemperateGrowth_prodMk_left e) (exists_norm_le_prodMk_left e)

variable {𝕜}

/-- The slice of a Schwartz function on a product: a Schwartz function on the second factor. -/
noncomputable def slice (K : 𝓢(E × F, G)) (e : E) : 𝓢(F, G) := sliceCLM ℝ e K

/-- ★ **The defining equation of the slice.** -/
@[simp] theorem slice_apply (K : 𝓢(E × F, G)) (e : E) (w : F) : slice K e w = K (e, w) := by
  rw [slice, sliceCLM, compCLM_apply]
  rfl

end SchwartzMap

/-! ### The payoff: the Weyl expectation formula, hypothesis-free -/

namespace WignerFunction

open scoped FourierTransform ComplexConjugate

/-- ★ **The kernel-class Weyl operator *is* `weylOp` of the kernel's slice family** — no longer a
hypothesis, since `SchwartzMap.slice` supplies the family. -/
theorem weylOpK_eq_weylOp_slice (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK K ψ x = weylOp (SchwartzMap.slice K) ψ x :=
  weylOpK_eq_weylOp K (SchwartzMap.slice K) (fun u w => SchwartzMap.slice_apply K u w) ψ x

/-- ★★★ **The Weyl expectation formula on the Schwartz kernel class, with no hypotheses.** The
expectation of the Weyl operator in a state is the phase-space average of the symbol against the
state's Wigner function.

`WignerWeyl.lean` proves this for a slice family under three assumptions, because its datum could not
supply them: joint continuity of the kernel, and a bound integrable in the first slot. #92(a1)
discharged the latter two for a jointly Schwartz kernel (`continuous_weylKernel`,
`exists_integrable_bound`) and `SchwartzMap.slice` supplies the family, so on this class the formula
is unconditional. -/
theorem integral_conj_mul_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x, conj (ψ x) * weylOpK K ψ x)
      = ∫ u, ∫ ξ, weylSymbol (SchwartzMap.slice K) u ξ * wigner ψ u ξ := by
  obtain ⟨M, hM, hbM⟩ := exists_integrable_bound K
  have hbc : Continuous fun p : ℝ × ℝ => SchwartzMap.slice K p.1 p.2 := by
    simpa using continuous_weylKernel K
  have hbM' : ∀ u w : ℝ, ‖SchwartzMap.slice K u w‖ ≤ M u := by
    intro u w
    rw [SchwartzMap.slice_apply]
    exact hbM u w
  have heq : ∀ x, weylOpK K ψ x = weylOp (SchwartzMap.slice K) ψ x :=
    fun x => weylOpK_eq_weylOp_slice K ψ x
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [heq])]
  exact integral_conj_mul_weylOp (SchwartzMap.slice K) ψ hbc hM hbM'

end WignerFunction

end
