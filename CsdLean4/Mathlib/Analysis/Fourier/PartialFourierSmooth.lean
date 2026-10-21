/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourier
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzPartialIntegral
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzTensor

/-!
# The partial Fourier transform is smooth on the plane, with uniformly bounded derivatives

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #170 (out of #121(ii), brick 1 of 5: the partial Fourier transform on `𝓢(ℝ × ℝ, ℂ)`).

For a Schwartz kernel `K` on the plane, the **partial Fourier transform** in the second slot,

  `𝓕₂K(u, ξ) = ∫ e(−wξ) K(u, w) dw`,

is `C^∞` as a function of `(u, ξ) ∈ ℝ × ℝ`, and every iterated derivative is bounded **uniformly
on the plane** by a constant times a single `Finset.sup` of `K`'s seminorms:

  `‖∂ⁿ 𝓕₂K(u, ξ)‖ ≤ (Σᵢ C(n, i) (2π)ⁱ 2ⁱ⁺²) · π · 𝒮ₙ(K)`.

The integrand `F p w = e(−w p.2) · K(p.1, w)` has parameter `p = (u, ξ)` in a finite-dimensional
space and is **jointly** smooth in `(p, w)`, which is exactly the shape of #124's
★★★ `contDiffOn_integral_of_iteratedFDeriv_bound` and ★★★ `norm_iteratedFDeriv_integral_le`
(`ContDiffParametricIntegralFDeriv.lean`); #126(ii)'s `prodDirDeriv` lemmas discharge the
measurability hypotheses for any jointly smooth integrand. **The content of this file is the bound
family**, a Leibniz expansion across the oscillating factor: `∂ᵏ_p [e(−wξ) K(u, w)]` is a sum over
`i ≤ k` of a derivative of the phase of order `i` — of norm exactly `(2π|w|)ⁱ`, the phase being
`exp(c · ξ)` with `|c| = 2π|w|` — times a derivative of `u ↦ K(u, w)` of order `k − i`, and `K`'s
decay two orders apart turns `(1 + |w|)ⁱ ‖∂ᵏ⁻ⁱK(u, w)‖` into `2ⁱ⁺² 𝒮(K) (1 + w²)⁻¹`, integrable in
`w` and independent of `u`.

* `SchwartzMap.partialFourier` — `𝓕₂K` as a plain function on the plane, with
  `partialFourier_eq_sliceFourier`: at `(u, ξ)` it is the slice-wise transform of
  `PartialFourier.lean`, so the slice-wise object and this one are the same;
* `SchwartzMap.iteratedDeriv_cexp_const_mul_ofReal`, ★ `norm_iteratedFDeriv_phase_le` — the
  phase's derivatives in the parameter have norm `(2π|w|)ⁱ`;
* ★ `SchwartzMap.one_add_abs_pow_mul_norm_iteratedFDeriv_le` — the weight transfer onto the
  integration variable: `(1 + |w|)ⁱ ‖∂ʲK(u, w)‖ ≤ 2ⁱ⁺² 𝒮(K) (1 + w²)⁻¹`, uniformly in `u`;
* ★★ `SchwartzMap.norm_iteratedFDeriv_partialFourierIntegrand_le` — **the Leibniz bound family**,
  `‖∂ᵏ_p F(·, w)(p)‖ ≤ leibnizConst k · kSup K k · (1 + w²)⁻¹`;
* ★★ `SchwartzMap.contDiff_partialFourier` — **`𝓕₂K` is `C^∞` on the plane**;
* ★★ `SchwartzMap.norm_iteratedFDeriv_partialFourier_le`, `norm_partialFourier_le` — **every
  derivative is bounded uniformly on the plane**, linearly in one `Finset.sup` of `K`'s seminorms.

## Honest scope

* No decay in `(u, ξ)` is proved here: that is #172 (the multiplication identities) and #173 (the
  joint seminorm bounds). The uniform derivative bound is what #173 combines with them.
* The constants are not sharp; `leibnizConst k = Σᵢ C(k, i) (2π)ⁱ 2ⁱ⁺²` and `kSup K k`, the sup of
  `K`'s seminorms over `Iic (k + 2, k)`, fall out of the route.
* One dimension in each slot, scalar-valued kernels.

References: [`ContDiffParametricIntegralFDeriv.lean`](../Calculus/ContDiffParametricIntegralFDeriv.lean)
(#124), [`SchwartzPartialIntegral.lean`](SchwartzPartialIntegral.lean) (#126(ii), the measurability
lemmas and the weight transfer this file mirrors), [`SchwartzTensor.lean`](SchwartzTensor.lean)
(`norm_iteratedFDeriv_comp_clm_le`), [`PartialFourier.lean`](PartialFourier.lean) (`sliceFourierCLM`);
Mathlib `Analysis/Calculus/ContDiff/Bounds.lean` (`norm_iteratedFDeriv_mul_le`);
`specs/BACKLOG.md` #170, #121.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped FourierTransform

namespace SchwartzMap

/-! ### The partial Fourier transform as a function -/

/-- **The partial Fourier transform** of a Schwartz kernel on the plane, in the second slot:
`𝓕₂K(u, ξ) = ∫ e(−wξ) K(u, w) dw`. -/
noncomputable def partialFourier (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) : ℂ :=
  ∫ w : ℝ, (𝐞 (-(w * p.2)) : ℂ) * K (p.1, w)

/-- At `(u, ξ)` the partial Fourier transform is the slice-wise transform of `PartialFourier.lean`. -/
theorem partialFourier_eq_sliceFourier (K : 𝓢(ℝ × ℝ, ℂ)) (u ξ : ℝ) :
    partialFourier K (u, ξ) = sliceFourierCLM u K ξ := by
  rw [sliceFourierCLM_apply, SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp only [partialFourier, slice_apply, Circle.smul_def, smul_eq_mul]

/-- The integrand, as a jointly smooth function of `(p, w)`. -/
noncomputable def partialFourierIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  (𝐞 (-(q.2 * q.1.2)) : ℂ) * K (q.1.1, q.2)

theorem partialFourierIntegrand_apply (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) (w : ℝ) :
    partialFourierIntegrand K (p, w) = (𝐞 (-(w * p.2)) : ℂ) * K (p.1, w) := rfl

theorem partialFourier_eq_integral_integrand (K : 𝓢(ℝ × ℝ, ℂ)) :
    partialFourier K = fun p => ∫ w : ℝ, partialFourierIntegrand K (p, w) := rfl

/-- The integrand is jointly smooth. -/
theorem contDiff_partialFourierIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (partialFourierIntegrand K) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun q : (ℝ × ℝ) × ℝ => (𝐞 (-(q.2 * q.1.2)) : ℂ) := by
    have : (fun q : (ℝ × ℝ) × ℝ => (𝐞 (-(q.2 * q.1.2)) : ℂ))
        = fun q => Complex.exp (((2 * π * -(q.2 * q.1.2) : ℝ) : ℂ) * Complex.I) := by
      funext q
      rw [Real.fourierChar_apply]
    rw [this]
    have hpoly : ContDiff ℝ (⊤ : ℕ∞) fun q : (ℝ × ℝ) × ℝ => 2 * π * -(q.2 * q.1.2) :=
      contDiff_const.mul (contDiff_snd.mul (contDiff_snd.comp contDiff_fst)).neg
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hpoly).mul contDiff_const)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) :=
    (K.smooth ⊤).comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h1.mul h2

theorem contDiff_partialFourierIntegrand_left (K : 𝓢(ℝ × ℝ, ℂ)) (w : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => partialFourierIntegrand K (p, w) :=
  (contDiff_partialFourierIntegrand K).comp (contDiff_id.prodMk contDiff_const)

/-! ### The phase -/

/-- The iterated derivative of `x ↦ exp(c x)` on the real line. -/
theorem iteratedDeriv_cexp_const_mul_ofReal (n : ℕ) (c : ℂ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (c * x))
      = fun x : ℝ => c ^ n * Complex.exp (c * x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have h := ((h1.const_mul c).cexp).const_mul (c ^ n)
      rw [h.deriv]
      ring

theorem contDiff_cexp_const_mul_ofReal (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => Complex.exp (c * x) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The phase in the parameter is `exp(c · ξ)` with `c = −2πw · i`, read through the second
projection. -/
theorem phase_eq (w : ℝ) :
    (fun p : ℝ × ℝ => (𝐞 (-(w * p.2)) : ℂ))
      = fun p => Complex.exp ((((-(2 * π * w) : ℝ) : ℂ) * Complex.I)
          * (ContinuousLinearMap.snd ℝ ℝ ℝ p : ℂ)) := by
  funext p
  rw [Real.fourierChar_apply, ContinuousLinearMap.coe_snd']
  congr 1
  push_cast
  ring

/-- ★ **The phase's derivatives in the parameter have norm `(2π|w|)ⁱ`.** -/
theorem norm_iteratedFDeriv_phase_le (w : ℝ) (i : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => (𝐞 (-(w * p.2)) : ℂ)) p‖ ≤ (2 * π * |w|) ^ i := by
  rw [phase_eq w]
  set c : ℂ := ((-(2 * π * w) : ℝ) : ℂ) * Complex.I with hc
  have hnc : ‖c‖ = 2 * π * |w| := by
    rw [hc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_mul, abs_of_pos Real.two_pi_pos]
  refine (norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.snd ℝ ℝ ℝ) norm_snd_clm_le_one
    (contDiff_cexp_const_mul_ofReal c) i p).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_const_mul_ofReal]
  simp only
  rw [norm_mul, norm_pow, hnc]
  have hexp : ‖Complex.exp (c * ((ContinuousLinearMap.snd ℝ ℝ ℝ) p : ℂ))‖ = 1 := by
    rw [show c * ((ContinuousLinearMap.snd ℝ ℝ ℝ) p : ℂ)
        = ((-(2 * π * w) * (ContinuousLinearMap.snd ℝ ℝ ℝ) p : ℝ) : ℂ) * Complex.I by
          rw [hc]; push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [hexp, mul_one]

/-! ### The kernel factor -/

/-- A derivative in `u` of `u ↦ K(u, w)` is no bigger than the full derivative of `K`. -/
theorem norm_iteratedFDeriv_slice_fst_le (K : 𝓢(ℝ × ℝ, ℂ)) (w : ℝ) (j : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => K (p.1, w)) p‖
      ≤ ‖iteratedFDeriv ℝ j (K : ℝ × ℝ → ℂ) (p.1, w)‖ := by
  have h1 := norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.fst ℝ ℝ ℝ) norm_fst_clm_le_one
    (f := fun u : ℝ => K (u, w)) (contDiff_slice_left K w) j p
  exact h1.trans (norm_iteratedFDeriv_comp_inl_le (K.smooth ⊤) w j p.1)

/-- ★ **The weight transfer onto the integration variable**: two orders of `K`'s decay give
`(1 + |w|)ⁱ ‖∂ʲK(u, w)‖ ≤ 2ⁱ⁺² 𝒮(K) (1 + w²)⁻¹`, uniformly in `u`. The mirror of #126(ii)'s
`one_add_norm_pow_mul_norm_iteratedFDeriv_le`, with the weight on the other slot. -/
theorem one_add_abs_pow_mul_norm_iteratedFDeriv_le (K : 𝓢(ℝ × ℝ, ℂ)) (i j : ℕ) (u w : ℝ) :
    (1 + |w|) ^ i * ‖iteratedFDeriv ℝ j (K : ℝ × ℝ → ℂ) (u, w)‖
      ≤ 2 ^ (i + 2) * (Finset.Iic (i + 2, j)).sup (schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) K
          * (1 + w ^ 2)⁻¹ := by
  have hw : |w| ≤ ‖((u, w) : ℝ × ℝ)‖ := by simp
  have h1 : (1 + |w|) ^ i ≤ (1 + ‖((u, w) : ℝ × ℝ)‖) ^ i := by gcongr
  have h2 : 1 + w ^ 2 ≤ (1 + ‖((u, w) : ℝ × ℝ)‖) ^ 2 := by
    nlinarith [abs_nonneg w, sq_abs w]
  have h3 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (i + 2, j))
    (le_refl (i + 2)) (le_refl j) K (u, w)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + w ^ 2)]
  calc (1 + |w|) ^ i * ‖iteratedFDeriv ℝ j (K : ℝ × ℝ → ℂ) (u, w)‖ * (1 + w ^ 2)
      ≤ (1 + ‖((u, w) : ℝ × ℝ)‖) ^ i * ‖iteratedFDeriv ℝ j (K : ℝ × ℝ → ℂ) (u, w)‖
          * (1 + ‖((u, w) : ℝ × ℝ)‖) ^ 2 := by gcongr
    _ = (1 + ‖((u, w) : ℝ × ℝ)‖) ^ (i + 2)
          * ‖iteratedFDeriv ℝ j (K : ℝ × ℝ → ℂ) (u, w)‖ := by rw [pow_add]; ring
    _ ≤ 2 ^ (i + 2) * (Finset.Iic (i + 2, j)).sup (schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) K := h3

/-! ### The bound family -/

/-- The sup of `K`'s seminorms over the square `Iic (k + 2, k)`, which dominates every
`Iic (i + 2, k − i)` with `i ≤ k`. -/
noncomputable def kSup (K : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) : ℝ :=
  (Finset.Iic (k + 2, k)).sup (schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) K

theorem kSup_nonneg (K : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) : 0 ≤ kSup K k := apply_nonneg _ _

theorem sup_le_kSup (K : 𝓢(ℝ × ℝ, ℂ)) (k i : ℕ) (hi : i ≤ k) :
    (Finset.Iic (i + 2, k - i)).sup (schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) K ≤ kSup K k := by
  have hsub : Finset.Iic (i + 2, k - i) ⊆ Finset.Iic (k + 2, k) := by
    intro m hm
    rw [Finset.mem_Iic] at hm ⊢
    exact hm.trans ⟨by simpa using hi, by simp⟩
  exact (Seminorm.le_def.1 (Finset.sup_mono hsub)) K

/-- The Leibniz constant `Σᵢ C(k, i) (2π)ⁱ 2ⁱ⁺²`. -/
noncomputable def leibnizConst (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * π) ^ i * 2 ^ (i + 2)

theorem leibnizConst_nonneg (k : ℕ) : 0 ≤ leibnizConst k :=
  Finset.sum_nonneg fun i _ => by positivity

theorem leibnizConst_zero : leibnizConst 0 = 4 := by
  simp [leibnizConst]
  norm_num

/-- ★★ **The Leibniz bound family**: every `p`-derivative of the integrand is bounded, uniformly in
`p`, by `leibnizConst k · kSup K k · (1 + w²)⁻¹`, which is integrable in `w`. -/
theorem norm_iteratedFDeriv_partialFourierIntegrand_le (K : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (p : ℝ × ℝ)
    (w : ℝ) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × ℝ => partialFourierIntegrand K (p, w)) p‖
      ≤ leibnizConst k * kSup K k * (1 + w ^ 2)⁻¹ := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => (𝐞 (-(w * p.2)) : ℂ) := by
    rw [phase_eq w]
    exact (contDiff_cexp_const_mul_ofReal _).comp (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff
  have hg : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × ℝ => K (p.1, w) :=
    (K.smooth ⊤).comp (contDiff_fst.prodMk contDiff_const)
  show ‖iteratedFDeriv ℝ k (fun p : ℝ × ℝ => (𝐞 (-(w * p.2)) : ℂ) * K (p.1, w)) p‖ ≤ _
  refine (norm_iteratedFDeriv_mul_le hf hg p (by exact_mod_cast le_top)).trans ?_
  rw [leibnizConst, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hA := norm_iteratedFDeriv_phase_le w i p
  have hB := norm_iteratedFDeriv_slice_fst_le K w (k - i) p
  have hC := one_add_abs_pow_mul_norm_iteratedFDeriv_le K i (k - i) p.1 w
  have hS := sup_le_kSup K k i hi'
  have hw1 : |w| ≤ 1 + |w| := le_add_of_nonneg_left zero_le_one
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => (𝐞 (-(w * p.2)) : ℂ)) p‖
        * ‖iteratedFDeriv ℝ (k - i) (fun p : ℝ × ℝ => K (p.1, w)) p‖
      ≤ (k.choose i : ℝ) * (2 * π * |w|) ^ i
        * ‖iteratedFDeriv ℝ (k - i) (K : ℝ × ℝ → ℂ) (p.1, w)‖ := by gcongr
    _ = (k.choose i : ℝ) * (2 * π) ^ i
        * (|w| ^ i * ‖iteratedFDeriv ℝ (k - i) (K : ℝ × ℝ → ℂ) (p.1, w)‖) := by
        rw [mul_pow]; ring
    _ ≤ (k.choose i : ℝ) * (2 * π) ^ i
        * ((1 + |w|) ^ i * ‖iteratedFDeriv ℝ (k - i) (K : ℝ × ℝ → ℂ) (p.1, w)‖) := by gcongr
    _ ≤ (k.choose i : ℝ) * (2 * π) ^ i
        * (2 ^ (i + 2) * (Finset.Iic (i + 2, k - i)).sup (schwartzSeminormFamily ℂ (ℝ × ℝ) ℂ) K
          * (1 + w ^ 2)⁻¹) := by gcongr
    _ ≤ (k.choose i : ℝ) * (2 * π) ^ i * (2 ^ (i + 2) * kSup K k * (1 + w ^ 2)⁻¹) := by gcongr
    _ = (k.choose i : ℝ) * (2 * π) ^ i * 2 ^ (i + 2) * kSup K k * (1 + w ^ 2)⁻¹ := by ring

/-! ### Smoothness and the uniform derivative bound -/

/-- The bound family in the form #124's theorems take it. -/
theorem norm_dirDeriv_partialFourierIntegrand_le (K : 𝓢(ℝ × ℝ, ℂ)) (hs : List (ℝ × ℝ))
    (p : ℝ × ℝ) (w : ℝ) :
    ‖dirDeriv (fun (p : ℝ × ℝ) (w : ℝ) => partialFourierIntegrand K (p, w)) hs p w‖
      ≤ dirWeight hs * (leibnizConst hs.length * kSup K hs.length * (1 + w ^ 2)⁻¹) := by
  have h := norm_dirDeriv_le hs (fun (p : ℝ × ℝ) (w : ℝ) => partialFourierIntegrand K (p, w))
    (fun w => contDiff_partialFourierIntegrand_left K w) p w
  refine h.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_partialFourierIntegrand_le K _ p w)
    (dirWeight_nonneg hs)

/-- ★★ **The partial Fourier transform is `C^∞` on the plane.** -/
theorem contDiff_partialFourier (K : 𝓢(ℝ × ℝ, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (partialFourier K) := by
  rw [partialFourier_eq_integral_integrand]
  refine contDiff_infty.2 fun m => ?_
  rw [← contDiffOn_univ]
  refine contDiffOn_integral_of_iteratedFDeriv_bound (μ := volume)
    (F := fun (p : ℝ × ℝ) (w : ℝ) => partialFourierIntegrand K (p, w))
    (bound := fun k w => leibnizConst k * kSup K k * (1 + w ^ 2)⁻¹) isOpen_univ
    (fun w => contDiff_partialFourierIntegrand_left K w)
    (fun hs x => aestronglyMeasurable_dirDeriv_prodMk (contDiff_partialFourierIntegrand K) hs x)
    (fun hs x => aestronglyMeasurable_fderiv_dirDeriv_prodMk
      (contDiff_partialFourierIntegrand K) hs x)
    (fun k => integrable_inv_one_add_sq.const_mul _)
    (fun k w => mul_nonneg (mul_nonneg (leibnizConst_nonneg k) (kSup_nonneg K k)) (by positivity))
    (fun k x _ w => norm_iteratedFDeriv_partialFourierIntegrand_le K k x w) m

/-- ★★ **Every derivative of the partial Fourier transform is bounded uniformly on the plane**,
linearly in one `Finset.sup` of `K`'s seminorms:
`‖∂ⁿ 𝓕₂K(p)‖ ≤ leibnizConst n · kSup K n · π`. -/
theorem norm_iteratedFDeriv_partialFourier_le (K : 𝓢(ℝ × ℝ, ℂ)) (n : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (partialFourier K) p‖ ≤ leibnizConst n * kSup K n * π := by
  rw [partialFourier_eq_integral_integrand]
  have h := norm_iteratedFDeriv_integral_le (μ := volume) n
    (fun (p : ℝ × ℝ) (w : ℝ) => partialFourierIntegrand K (p, w)) univ
    (fun k w => leibnizConst k * kSup K k * (1 + w ^ 2)⁻¹) isOpen_univ
    (fun m w => (contDiff_partialFourierIntegrand_left K w).of_le (by exact_mod_cast le_top))
    (fun hs x => aestronglyMeasurable_dirDeriv_prodMk (contDiff_partialFourierIntegrand K) hs x)
    (fun hs x => aestronglyMeasurable_fderiv_dirDeriv_prodMk
      (contDiff_partialFourierIntegrand K) hs x)
    (fun k => integrable_inv_one_add_sq.const_mul _)
    (fun k w => mul_nonneg (mul_nonneg (leibnizConst_nonneg k) (kSup_nonneg K k)) (by positivity))
    (fun hs x _ w => norm_dirDeriv_partialFourierIntegrand_le K hs x w) p (mem_univ p)
  refine h.trans ?_
  rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- The zero-order case: `‖𝓕₂K(p)‖ ≤ 4π · kSup K 0`. -/
theorem norm_partialFourier_le (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    ‖partialFourier K p‖ ≤ 4 * π * kSup K 0 := by
  have h := norm_iteratedFDeriv_partialFourier_le K 0 p
  rw [norm_iteratedFDeriv_zero, leibnizConst_zero] at h
  linarith

end SchwartzMap

end
