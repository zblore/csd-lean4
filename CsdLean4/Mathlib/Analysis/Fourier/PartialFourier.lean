/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzSlice
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The symbol of a Schwartz kernel, at each midpoint

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #121(ii), partially — see the scope note, which is the point of this file.

#121(ii) asked for the **partial Fourier transform** on `𝓢(ℝ × ℝ, ℂ)`: the transform in the second
slot alone, landing in Schwartz functions *on the plane*. That is what turns a kernel into a symbol
and what #92(c) recorded as the reason `W` could not be shown Schwartz on the plane.

What is delivered here is the **slice-wise** transform, which is the object `weylSymbol` actually is:

* `SchwartzMap.sliceFourierCLM` — the composite of #121(i)'s `sliceCLM` with Mathlib's
  `fourierTransformCLM`, so **the symbol at a fixed midpoint is a Schwartz function of the frequency,
  continuously and linearly in the kernel**;
* ★ `WignerFunction.weylSymbol_slice_apply` — it *is* `weylSymbol` of the kernel's slice family;
* ★ `WignerFunction.integrable_weylSymbol_slice` and ★ `WignerFunction.exists_bound_weylSymbol_slice`
  — the two consequences a consumer wants, both free once the symbol slice is Schwartz.

## Honest scope — and a dependency the row did not know about

⚠️ **This does not close #121(ii), and the joint statement is not a corollary of it.** That
`(u, ξ) ↦ weylSymbol (slice K) u ξ` is Schwartz **on the plane** needs decay and smoothness *jointly*,
and slice-wise Schwartzness gives neither: every constant here may depend on the midpoint `u`.

⚠️ **The reason is structural, and it is new information.** The natural proof of the joint statement
factors through the curry `𝓢(E × F, G) ≃ 𝓢(E, 𝓢(F, G))`, after which a partial transform is just
Mathlib's `fourierTransformCLM` applied in the inner factor. **Mathlib has no such curry**, and its
first half is #123. The alternative is bespoke: differentiate under the integral in *both* variables
to all orders, which needs the finite-dimensional-parameter version of #120 (that row's own scope note
records the one-dimensional restriction), and then the seminorm estimates
`(2πiξ)^c 𝓕₂K = 𝓕₂[∂_w^c K]` and `∂_ξ^b 𝓕₂K = 𝓕₂[(−2πiw)^b K]` assembled against `K`'s decay. Either
way it is not a one-sitting build, which the row's `L` did not reflect.

References: [`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i)), [`WignerWeyl.lean`](WignerWeyl.lean)
(`weylSymbol`), `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`;
`specs/BACKLOG.md` #121, #123, #120, #92.
-/

@[expose] public section

open MeasureTheory SchwartzMap

open scoped FourierTransform

namespace SchwartzMap

/-- **The slice-wise Fourier transform**: slice the kernel at a midpoint, then transform. A
continuous linear map in the kernel, being a composite of two. -/
noncomputable def sliceFourierCLM (u : ℝ) : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (fourierTransformCLM ℂ).comp (sliceCLM ℂ u)

@[simp] theorem sliceFourierCLM_apply (u : ℝ) (K : 𝓢(ℝ × ℝ, ℂ)) :
    (sliceFourierCLM u K : ℝ → ℂ) = 𝓕 (slice K u) := by
  rw [sliceFourierCLM, ContinuousLinearMap.comp_apply, fourierTransformCLM_apply]
  rfl

end SchwartzMap

namespace WignerFunction

/-- ★ **The symbol at a midpoint is a Schwartz function of the frequency.** The left side is the
corpus's `weylSymbol`; the right is a term of `𝓢(ℝ, ℂ)`. -/
theorem weylSymbol_slice_apply (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    weylSymbol (SchwartzMap.slice K) u ξ = SchwartzMap.sliceFourierCLM u K ξ := by
  rw [weylSymbol, SchwartzMap.sliceFourierCLM_apply]

/-- ★ The symbol slice is integrable, which is what the Weyl expectation formula's inner integral
needs. -/
theorem integrable_weylSymbol_slice (K : 𝓢(ℝ × ℝ, ℂ)) (u : ℝ) :
    Integrable (weylSymbol (SchwartzMap.slice K) u) := by
  have h : weylSymbol (SchwartzMap.slice K) u
      = (SchwartzMap.sliceFourierCLM u K : ℝ → ℂ) :=
    funext fun ξ => weylSymbol_slice_apply K u ξ
  rw [h]
  exact (SchwartzMap.sliceFourierCLM u K).integrable

/-- ★ And bounded, uniformly in the frequency. -/
theorem exists_bound_weylSymbol_slice (K : 𝓢(ℝ × ℝ, ℂ)) (u : ℝ) :
    ∃ C : ℝ, ∀ ξ : ℝ, ‖weylSymbol (SchwartzMap.slice K) u ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_le (SchwartzMap.sliceFourierCLM u K)
  refine ⟨C, fun ξ => ?_⟩
  rw [weylSymbol_slice_apply]
  exact hC ξ

end WignerFunction

end
