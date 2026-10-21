/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourierDeriv

/-!
# Polynomial weights on the partial Fourier transform are partial Fourier transforms

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #172 (out of #121(ii), brick 3 of 5: the partial Fourier transform on `𝓢(ℝ × ℝ, ℂ)`).

For a Schwartz kernel `K` on the plane,

  `u · 𝓕₂K(u, ξ) = 𝓕₂(u · K)(u, ξ)`,  `2πi ξ · 𝓕₂K(u, ξ) = 𝓕₂(∂_w K)(u, ξ)`,

so every polynomial weight on `𝓕₂K` is `𝓕₂` of a continuous linear image of `K`:
`‖(u, ξ)‖ᵏ ‖𝓕₂K(u, ξ)‖ ≤ ‖𝓕₂(uᵏ K)(u, ξ)‖ + (2π)⁻ᵏ ‖𝓕₂(∂_wᵏ K)(u, ξ)‖`. With #171 (derivatives are
`𝓕₂`'s) and #170 (`𝓕₂` of a Schwartz function is bounded by one of its seminorms), this is what makes
`𝓕₂K` decay on the plane, which is #173.

The `ξ` identity is **slice-wise and Mathlib's**: `𝓕₂K(u, ·) = 𝓕 (slice K u)` (`PartialFourier.lean`)
and `SchwartzMap.fourier_lineDerivOp_eq` is `𝓕(∂f) = 2πi ξ · 𝓕f` on `𝓢(ℝ, ℂ)`; what needs saying is
that the `w`-derivative of a slice is the slice of the `w`-derivative (`slice_derivW`, the chain rule
through `w ↦ (u, w)`). The `u` identity is that `u` is a parameter of the integral.

* `SchwartzMap.uMul`, `mulU`, `mulU_apply` — multiplication by `u`, a continuous linear map of
  Schwartz space; `derivW`, `derivW_apply` — the `w`-derivative;
* `SchwartzMap.slice_derivW` — the slice of `∂_w K` is the derivative of the slice;
* ★ `SchwartzMap.partialFourier_mulU` — **`𝓕₂(u K) = u · 𝓕₂K`**;
* ★★ `SchwartzMap.partialFourier_derivW` — **`𝓕₂(∂_w K) = 2πi ξ · 𝓕₂K`**;
* `SchwartzMap.mulUPow`, `derivWPow`, `partialFourier_mulUPow`, `partialFourier_derivWPow` — the
  iterates, `𝓕₂(uᵏ K) = uᵏ 𝓕₂K` and `𝓕₂(∂_wᵏ K) = (2πi ξ)ᵏ 𝓕₂K`;
* ★★ `SchwartzMap.norm_pow_mul_norm_partialFourier_le` — **the weight moves inside**:
  `‖p‖ᵏ ‖𝓕₂K(p)‖ ≤ ‖𝓕₂(mulUPow k K)(p)‖ + (2π)⁻ᵏ ‖𝓕₂(derivWPow k K)(p)‖` for every `p`.

## Honest scope

* Identities and one inequality, no estimate on `K`'s seminorms: the seminorm bound on
  `mulUPow k K` and `derivWPow k K`, and its combination with #171's derivative operators, is #173.
* The iterates are written as explicit recursions `mulUPow`, `derivWPow` rather than powers in the
  endomorphism monoid of `𝓢(ℝ × ℝ, ℂ)`, so that their `_apply` lemmas are `rfl`.

References: [`PartialFourierSmooth.lean`](PartialFourierSmooth.lean) (#170,
`partialFourier_eq_sliceFourier`), [`PartialFourierDeriv.lean`](PartialFourierDeriv.lean) (#171),
[`PartialFourier.lean`](PartialFourier.lean) (`sliceFourierCLM`), [`SchwartzSlice.lean`](SchwartzSlice.lean)
(#121(i), `slice`); Mathlib `Analysis/Distribution/SchwartzSpace/Fourier.lean`
(`fourier_lineDerivOp_eq`); `specs/BACKLOG.md` #172, #121.
-/

@[expose] public section

open MeasureTheory Set Real LineDeriv
open scoped FourierTransform

namespace SchwartzMap

/-! ### The two operators -/

/-- The multiplier `(u, w) ↦ u`. -/
noncomputable def uMul (q : ℝ × ℝ) : ℂ := (q.1 : ℂ)

theorem uMul_eq_clm : uMul = ⇑(Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) := by
  funext q
  simp [uMul]

theorem hasTemperateGrowth_uMul : Function.HasTemperateGrowth uMul := by
  rw [uMul_eq_clm]
  exact ContinuousLinearMap.hasTemperateGrowth _

/-- **Multiplication by `u`** on Schwartz kernels. -/
noncomputable def mulU : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) := smulLeftCLM ℂ uMul

theorem mulU_apply (K : 𝓢(ℝ × ℝ, ℂ)) (q : ℝ × ℝ) : mulU K q = (q.1 : ℂ) * K q := by
  rw [mulU, smulLeftCLM_apply_apply hasTemperateGrowth_uMul, smul_eq_mul]
  rfl

/-- **The `w`-derivative** on Schwartz kernels. -/
noncomputable def derivW : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((0 : ℝ), (1 : ℝ))

theorem derivW_apply (K : 𝓢(ℝ × ℝ, ℂ)) (q : ℝ × ℝ) :
    derivW K q = fderiv ℝ K q ((0 : ℝ), (1 : ℝ)) := rfl

/-! ### The `u` identity -/

/-- ★ **`𝓕₂(u K) = u · 𝓕₂K`**: `u` is a parameter of the integral. -/
theorem partialFourier_mulU (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourier (mulU K) (u, ξ) = (u : ℂ) * partialFourier K (u, ξ) := by
  rw [partialFourier, partialFourier, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mulU_apply]
  ring

/-! ### The `ξ` identity -/

/-- The slice of the `w`-derivative is the derivative of the slice. -/
theorem slice_derivW (K : 𝓢(ℝ × ℝ, ℂ)) (u : ℝ) :
    slice (derivW K) u = ∂_{(1 : ℝ)} (slice K u) := by
  ext w
  rw [slice_apply, derivW_apply, lineDerivOp_apply_eq_fderiv]
  have hinr : HasFDerivAt (fun w : ℝ => (u, w)) (ContinuousLinearMap.inr ℝ ℝ ℝ) w := by
    simpa using ((ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt (x := w)).const_add ((u, (0 : ℝ)))
  have hs : HasFDerivAt (slice K u)
      ((fderiv ℝ K (u, w)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) w := by
    have h := (K.differentiable (u, w)).hasFDerivAt.comp w hinr
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    simp [slice_apply]
  rw [hs.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- ★★ **`𝓕₂(∂_w K) = 2πi ξ · 𝓕₂K`**: Mathlib's Fourier–derivative rule on the slice. -/
theorem partialFourier_derivW (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourier (derivW K) (u, ξ) = (2 * π * Complex.I) * ((ξ : ℂ) * partialFourier K (u, ξ)) := by
  rw [partialFourier_eq_sliceFourier, partialFourier_eq_sliceFourier, sliceFourierCLM_apply,
    sliceFourierCLM_apply, slice_derivW, fourier_lineDerivOp_eq]
  have hg : Function.HasTemperateGrowth fun x : ℝ => (inner ℝ x (1 : ℝ) : ℝ) :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  rw [_root_.smul_apply, smulLeftCLM_apply_apply hg]
  have hinner : (inner ℝ ξ (1 : ℝ) : ℝ) = ξ := by simp
  rw [hinner, Complex.real_smul, smul_eq_mul]

/-! ### The iterates -/

/-- `uᵏ ·`, as an explicit recursion. -/
noncomputable def mulUPow : ℕ → (𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | k + 1 => mulU.comp (mulUPow k)

/-- `∂_wᵏ`, as an explicit recursion. -/
noncomputable def derivWPow : ℕ → (𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | k + 1 => derivW.comp (derivWPow k)

@[simp] theorem mulUPow_zero (K : 𝓢(ℝ × ℝ, ℂ)) : mulUPow 0 K = K := rfl

theorem mulUPow_succ (k : ℕ) (K : 𝓢(ℝ × ℝ, ℂ)) : mulUPow (k + 1) K = mulU (mulUPow k K) := rfl

@[simp] theorem derivWPow_zero (K : 𝓢(ℝ × ℝ, ℂ)) : derivWPow 0 K = K := rfl

theorem derivWPow_succ (k : ℕ) (K : 𝓢(ℝ × ℝ, ℂ)) :
    derivWPow (k + 1) K = derivW (derivWPow k K) := rfl

/-- `𝓕₂(uᵏ K) = uᵏ · 𝓕₂K`. -/
theorem partialFourier_mulUPow (k : ℕ) (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourier (mulUPow k K) (u, ξ) = (u : ℂ) ^ k * partialFourier K (u, ξ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [mulUPow_succ, partialFourier_mulU, ih]
      ring

/-- `𝓕₂(∂_wᵏ K) = (2πi ξ)ᵏ · 𝓕₂K`. -/
theorem partialFourier_derivWPow (k : ℕ) (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourier (derivWPow k K) (u, ξ)
      = (2 * π * Complex.I * (ξ : ℂ)) ^ k * partialFourier K (u, ξ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [derivWPow_succ, partialFourier_derivW, ih]
      ring

/-! ### The weight moves inside -/

theorem norm_two_pi_I : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `max(a, b)ᵏ ≤ aᵏ + bᵏ` for nonnegative `a, b`. -/
theorem max_pow_le_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    max a b ^ k ≤ a ^ k + b ^ k := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (by positivity)

/-- ★★ **The weight moves inside**: a polynomial weight on `𝓕₂K` is bounded by `𝓕₂` of two
continuous linear images of `K`, with no `p` left outside. -/
theorem norm_pow_mul_norm_partialFourier_le (K : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (p : ℝ × ℝ) :
    ‖p‖ ^ k * ‖partialFourier K p‖
      ≤ ‖partialFourier (mulUPow k K) p‖
        + (2 * π)⁻¹ ^ k * ‖partialFourier (derivWPow k K) p‖ := by
  obtain ⟨u, ξ⟩ := p
  rw [partialFourier_mulUPow, partialFourier_derivWPow, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_mul, norm_two_pi_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hN : 0 ≤ ‖partialFourier K (u, ξ)‖ := norm_nonneg _
  have hmax := max_pow_le_add_pow (abs_nonneg u) (abs_nonneg ξ) k
  have h2π : (2 * π)⁻¹ ^ k * (2 * π * |ξ|) ^ k = |ξ| ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc max |u| |ξ| ^ k * ‖partialFourier K (u, ξ)‖
      ≤ (|u| ^ k + |ξ| ^ k) * ‖partialFourier K (u, ξ)‖ := by gcongr
    _ = |u| ^ k * ‖partialFourier K (u, ξ)‖
        + (2 * π)⁻¹ ^ k * ((2 * π * |ξ|) ^ k * ‖partialFourier K (u, ξ)‖) := by
        rw [← mul_assoc, h2π]
        ring

end SchwartzMap

end
