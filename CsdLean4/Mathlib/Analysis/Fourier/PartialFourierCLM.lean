/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourierBound

/-!
# The partial Fourier transform on `𝓢(ℝ × ℝ, ℂ)`, and the Wigner function on the plane

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #174 (out of #121(ii), brick 5 of 5 — closes #121).

The partial Fourier transform in the second slot is a **continuous linear map of Schwartz space on
the plane to itself**, ★★★ `partialFourierCLM : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ)`, by
`SchwartzMap.mkCLM` with #170 (smoothness), #171 (linearity in the kernel) and #173 (the joint
seminorm bounds). Its value at `(u, ξ)` is the corpus's `weylSymbol` of the sliced kernel
(★★ `partialFourierCLM_apply_eq_weylSymbol`): **the symbol of a Schwartz kernel is a Schwartz function
on the plane**, which is what #92(c) recorded as the missing step.

**The payoff.** The Wigner kernel `(x, y) ↦ ψ(x + y/2) · conj ψ(x − y/2)` is a Schwartz function on the
plane — the tensor product `ψ ⊗ conj ψ` of #126(i) composed with the linear automorphism
`(x, y) ↦ (x + y/2, x − y/2)` — and `W_ψ = 𝓕₂` of it, so ★★★ `wignerSchwartz ψ : 𝓢(ℝ × ℝ, ℂ)` with
`wignerSchwartz_apply : wignerSchwartz ψ (x, ξ) = wigner ψ x ξ`: **the Wigner function of a Schwartz
state is a Schwartz function of `(x, ξ)`**, resolving the caveat in `WignerCalculus.lean`.

* ★★★ `SchwartzMap.partialFourierCLM`, `partialFourierCLM_apply`, `slice_partialFourierCLM` — the
  transform as a CLM; its slices are the slice-wise transforms of `PartialFourier.lean`;
* ★★ `SchwartzMap.partialFourierCLM_apply_eq_weylSymbol` — it is `weylSymbol` of the slice family;
* `SchwartzMap.conjS`, `wignerL`, `norm_le_wignerL`, ★ `wignerKernelS`, `wignerKernelS_apply` — the
  Wigner kernel as a Schwartz function on the plane;
* ★★★ `SchwartzMap.wignerSchwartz`, `wignerSchwartz_apply` — the Wigner function on the plane.

## Honest scope

* One dimension in each slot, scalar kernels; the transform is in the second slot only (the first
  slot is the parameter), which is the one a symbol calculus uses.
* `wignerSchwartz` is the Wigner function of one Schwartz state; the cross Wigner function `wigner₂`
  of `MoyalBracket.lean` is the same construction with `φ ⊗ conj ψ` and is not packaged here.
* Nothing about the Moyal product of symbols, adjoints, or a wider symbol class: `partialFourierCLM`
  is the tool those would be stated with, not any of them.

References: [`PartialFourierSmooth.lean`](PartialFourierSmooth.lean) (#170),
[`PartialFourierDeriv.lean`](PartialFourierDeriv.lean) (#171), [`PartialFourierMul.lean`](PartialFourierMul.lean)
(#172), [`PartialFourierBound.lean`](PartialFourierBound.lean) (#173), [`PartialFourier.lean`](PartialFourier.lean)
(`sliceFourierCLM`, `weylSymbol_slice_apply`), [`SchwartzTensor.lean`](SchwartzTensor.lean) (#126(i),
`tensorProd`), [`Wigner.lean`](Wigner.lean) (`wigner`), [`WignerCalculus.lean`](WignerCalculus.lean)
(#92(c)); `specs/BACKLOG.md` #174, #121, #92.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped FourierTransform ComplexConjugate

namespace SchwartzMap

/-! ### The partial Fourier transform as a continuous linear map -/

/-- ★★★ **The partial Fourier transform on Schwartz space of the plane**, `𝓕₂ : 𝓢(ℝ × ℝ, ℂ) →L[ℂ]
𝓢(ℝ × ℝ, ℂ)`, `𝓕₂K(u, ξ) = ∫ e(−wξ) K(u, w) dw`. -/
noncomputable def partialFourierCLM : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  mkCLM (fun K p => partialFourier K p)
    (fun K₁ K₂ p => by rw [partialFourier_add, Pi.add_apply])
    (fun c K p => by rw [partialFourier_smul, Pi.smul_apply, RingHom.id_apply])
    (fun K => contDiff_partialFourier K)
    (fun n => exists_bound_partialFourier n.1 n.2)

@[simp] theorem partialFourierCLM_apply (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    partialFourierCLM K p = partialFourier K p := rfl

/-- The slices of `𝓕₂K` are the slice-wise transforms of `PartialFourier.lean`. -/
theorem slice_partialFourierCLM (K : 𝓢(ℝ × ℝ, ℂ)) (u : ℝ) :
    slice (partialFourierCLM K) u = sliceFourierCLM u K := by
  ext ξ
  rw [slice_apply, partialFourierCLM_apply, partialFourier_eq_sliceFourier]

/-- ★★ **The symbol of a Schwartz kernel is a Schwartz function on the plane**: `𝓕₂K` is the corpus's
`weylSymbol` of the slice family of `K`. -/
theorem partialFourierCLM_apply_eq_weylSymbol (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourierCLM K (u, ξ) = WignerFunction.weylSymbol (slice K) u ξ := by
  rw [partialFourierCLM_apply, partialFourier_eq_sliceFourier, WignerFunction.weylSymbol_slice_apply]

/-! ### The Wigner kernel as a Schwartz function on the plane -/

/-- The complex conjugate of a Schwartz function, as a Schwartz function. -/
noncomputable def conjS (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  bilinLeftCLM ((ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap)
    (g := fun _ : ℝ => (1 : ℂ)) (by fun_prop) ψ

@[simp] theorem conjS_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : conjS ψ x = conj (ψ x) := by
  rw [conjS, bilinLeftCLM_apply]
  simp

/-- The linear automorphism `(x, y) ↦ (x + y/2, x − y/2)` of the plane. -/
noncomputable def wignerL : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + (2⁻¹ : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ - (2⁻¹ : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem wignerL_apply (q : ℝ × ℝ) : wignerL q = (q.1 + q.2 / 2, q.1 - q.2 / 2) := by
  simp [wignerL, div_eq_inv_mul]

/-- `wignerL` does not shrink the norm by more than a factor `2`, which is what `compCLM` needs. -/
theorem norm_le_wignerL (q : ℝ × ℝ) : ‖q‖ ≤ 2 * (1 + ‖wignerL q‖) ^ 1 := by
  obtain ⟨x, y⟩ := q
  rw [wignerL_apply, pow_one, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs]
  simp only
  have h1 := abs_add_le (x + y / 2) (x - y / 2)
  have h2 := abs_add_le (x + y / 2) (-(x - y / 2))
  rw [show x + y / 2 + (x - y / 2) = 2 * x by ring, abs_mul, abs_two] at h1
  rw [show x + y / 2 + -(x - y / 2) = y by ring, abs_neg] at h2
  have ha := le_max_left |x + y / 2| |x - y / 2|
  have hb := le_max_right |x + y / 2| |x - y / 2|
  have h0 := abs_nonneg (x + y / 2)
  apply max_le <;> linarith

/-- ★ **The Wigner kernel is a Schwartz function on the plane**: `ψ ⊗ conj ψ` composed with
`wignerL`. -/
noncomputable def wignerKernelS (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  compCLM ℂ wignerL.hasTemperateGrowth ⟨1, 2, norm_le_wignerL⟩ (tensorProd ψ (conjS ψ))

theorem wignerKernelS_apply (ψ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    wignerKernelS ψ (x, y) = ψ (x + y / 2) * conj (ψ (x - y / 2)) := by
  show (tensorProd ψ (conjS ψ)) (wignerL (x, y)) = _
  rw [wignerL_apply, tensorProd_apply, conjS_apply]

/-! ### The Wigner function on the plane -/

/-- ★★★ **The Wigner function of a Schwartz state, as a Schwartz function on the plane.** -/
noncomputable def wignerSchwartz (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  partialFourierCLM (wignerKernelS ψ)

/-- It is `Wigner.lean`'s `wigner` at every point. -/
theorem wignerSchwartz_apply (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wignerSchwartz ψ (x, ξ) = WignerFunction.wigner ψ x ξ := by
  rw [wignerSchwartz, partialFourierCLM_apply, WignerFunction.wigner_eq_integral]
  show (∫ w : ℝ, (𝐞 (-(w * ξ)) : ℂ) * wignerKernelS ψ (x, w)) = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [wignerKernelS_apply]

end SchwartzMap

end
