/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourierSmooth

/-!
# The derivatives of the partial Fourier transform are partial Fourier transforms

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #171 (out of #121(ii), brick 2 of 5: the partial Fourier transform on `𝓢(ℝ × ℝ, ℂ)`).

For a Schwartz kernel `K` on the plane and a direction `h = (h₁, h₂)`,

  `∂_h 𝓕₂K = 𝓕₂(Dop h K)`,  `Dop h K = h₁ · ∂_u K + h₂ · (−2πi w) · K`,

and `Dop h` is a **continuous linear map of `𝓢(ℝ × ℝ, ℂ)` to itself** (Mathlib's `lineDerivOpCLM` along
`(1, 0)` and `smulLeftCLM` of the temperate-growth function `w ↦ −2πi w`). So the identity iterates:
the `n`-th derivative of `𝓕₂K` evaluated on directions `v₁, …, vₙ` is `𝓕₂` of `K` with the `n`
operators `Dop vᵢ` applied — a partial Fourier transform of a Schwartz function, never a derivative
of one. This is what lets #173 bound a derivative of `𝓕₂K` by an integral.

First order is #124's ★★ `fderiv_integral_apply_of_bound` on #170's integrand, with #170's bound
family at orders `0` and `1`; the pointwise derivative of the integrand is the product rule, the
phase contributing `−2πi w h₂` and the kernel its `u`-derivative. The iteration is
`iteratedFDeriv_apply_succ_last` (#124), which peels the last direction as the innermost derivative.

* `SchwartzMap.wMul`, `hasTemperateGrowth_wMul` — the multiplier `w ↦ −2πi w` on the plane;
* `SchwartzMap.Dop`, `Dop_apply`, `Dop_add`, `Dop_smul`, `Dop_fst`, `Dop_snd` — **the first-order
  operator**, linear in the direction;
* ★ `SchwartzMap.fderiv_partialFourierIntegrand_apply` — the pointwise derivative of the integrand
  is the integrand of `Dop h K`;
* `SchwartzMap.integrable_partialFourierIntegrand`, `partialFourier_add`, `partialFourier_smul` —
  integrability and linearity in the kernel;
* ★★ `SchwartzMap.fderiv_partialFourier_apply` — **`∂_h 𝓕₂K(p) = 𝓕₂(Dop h K)(p)`**;
  `fderiv_partialFourier_fst`, `fderiv_partialFourier_snd` the two named partials;
  ★ `hasFDerivAt_partialFourier` the derivative as a continuous linear map;
* `SchwartzMap.dopFin` — the composite of `Dop` along a tuple of directions, last first;
* ★★ `SchwartzMap.iteratedFDeriv_partialFourier_apply` — **`∂ⁿ 𝓕₂K(p)(v) = 𝓕₂(dopFin v K)(p)`**
  for every `n`, every `p` and every tuple `v` of directions.

## Honest scope

* Nothing here is an estimate; the seminorm bound on `dopFin v K` in terms of `K` and `∏‖vᵢ‖` is
  #173's, where it is combined with #172's multiplication identities.
* `Dop` is stated with the complex scalars `(h₁ : ℂ)`, `(h₂ : ℂ)` so that it is a `ℂ`-linear map of
  Schwartz space; `Dop_smul` records the real homogeneity.

References: [`PartialFourierSmooth.lean`](PartialFourierSmooth.lean) (#170),
[`ContDiffParametricIntegralFDeriv.lean`](../Calculus/ContDiffParametricIntegralFDeriv.lean) (#124,
`fderiv_integral_apply_of_bound`, `iteratedFDeriv_apply_succ_last`),
[`SchwartzPartialIntegral.lean`](SchwartzPartialIntegral.lean) (#126(ii), the measurability lemmas);
Mathlib `Analysis/Distribution/SchwartzSpace/Basic.lean` (`smulLeftCLM`) and
`Deriv.lean` (`lineDerivOpCLM`);
`specs/BACKLOG.md` #171, #121.
-/

@[expose] public section

open MeasureTheory Set Real LineDeriv
open scoped FourierTransform

namespace SchwartzMap

/-! ### The first-order operator -/

/-- The multiplier `(u, w) ↦ −2πi w`. -/
noncomputable def wMul (q : ℝ × ℝ) : ℂ := -(2 * π * Complex.I) * (q.2 : ℂ)

theorem wMul_eq_clm :
    wMul = ⇑((-(2 * π * Complex.I)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) := by
  funext q
  simp [wMul]

theorem hasTemperateGrowth_wMul : Function.HasTemperateGrowth wMul := by
  rw [wMul_eq_clm]
  exact ContinuousLinearMap.hasTemperateGrowth _

/-- The directional derivative CLM of Schwartz space, evaluated. -/
theorem lineDerivOpCLM_apply_eq_fderiv (m : ℝ × ℝ) (K : 𝓢(ℝ × ℝ, ℂ)) (q : ℝ × ℝ) :
    lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) m K q = fderiv ℝ K q m := rfl

/-- **The first-order operator** `Dop h K = h₁ · ∂_u K + h₂ · (−2πi w) · K`, a continuous linear
map of Schwartz space to itself. -/
noncomputable def Dop (h : ℝ × ℝ) : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  (h.1 : ℂ) • lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) + (h.2 : ℂ) • smulLeftCLM ℂ wMul

theorem Dop_apply (h : ℝ × ℝ) (K : 𝓢(ℝ × ℝ, ℂ)) (q : ℝ × ℝ) :
    Dop h K q = (h.1 : ℂ) * fderiv ℝ K q ((1 : ℝ), (0 : ℝ)) + (h.2 : ℂ) * (wMul q * K q) := by
  simp only [Dop, _root_.add_apply, _root_.smul_apply, lineDerivOpCLM_apply_eq_fderiv,
    smulLeftCLM_apply_apply hasTemperateGrowth_wMul, smul_eq_mul]

theorem Dop_add (h₁ h₂ : ℝ × ℝ) : Dop (h₁ + h₂) = Dop h₁ + Dop h₂ := by
  refine ContinuousLinearMap.ext fun K => SchwartzMap.ext fun q => ?_
  rw [_root_.add_apply, _root_.add_apply, Dop_apply, Dop_apply, Dop_apply]
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem Dop_smul (c : ℝ) (h : ℝ × ℝ) : Dop (c • h) = (c : ℂ) • Dop h := by
  refine ContinuousLinearMap.ext fun K => SchwartzMap.ext fun q => ?_
  rw [_root_.smul_apply, _root_.smul_apply, Dop_apply, Dop_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

theorem Dop_fst : Dop ((1 : ℝ), (0 : ℝ)) = lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) := by
  refine ContinuousLinearMap.ext fun K => SchwartzMap.ext fun q => ?_
  rw [Dop_apply, lineDerivOpCLM_apply_eq_fderiv]
  push_cast
  ring

theorem Dop_snd : Dop ((0 : ℝ), (1 : ℝ)) = smulLeftCLM ℂ wMul := by
  refine ContinuousLinearMap.ext fun K => SchwartzMap.ext fun q => ?_
  rw [Dop_apply, smulLeftCLM_apply_apply hasTemperateGrowth_wMul, smul_eq_mul]
  push_cast
  ring

/-! ### The pointwise derivative of the integrand -/

/-- ★ **The derivative of the integrand in the parameter is the integrand of `Dop h K`.** -/
theorem fderiv_partialFourierIntegrand_apply (K : 𝓢(ℝ × ℝ, ℂ)) (w : ℝ) (p h : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => partialFourierIntegrand K (y, w)) p h
      = partialFourierIntegrand (Dop h K) (p, w) := by
  set c : ℂ := ((-(2 * π * w) : ℝ) : ℂ) * Complex.I with hc
  have hphase : ∀ y : ℝ × ℝ, (𝐞 (-(w * y.2)) : ℂ) = Complex.exp (c * ((y.2 : ℝ) : ℂ)) := by
    intro y
    rw [Real.fourierChar_apply, hc]
    congr 1
    push_cast
    ring
  -- the phase
  have hφ : HasFDerivAt (fun y : ℝ × ℝ => Complex.exp (c * ((y.2 : ℝ) : ℂ)))
      (Complex.exp (c * ((p.2 : ℝ) : ℂ))
        • (c • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)))) p :=
    ((Complex.ofRealCLM.hasFDerivAt.comp p hasFDerivAt_snd).const_mul c).cexp
  -- the kernel factor
  have hinl : HasFDerivAt (fun u : ℝ => (u, w)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 := by
    simpa using ((ContinuousLinearMap.inl ℝ ℝ ℝ).hasFDerivAt (x := p.1)).add_const ((0 : ℝ), w)
  have hK : HasFDerivAt (fun y : ℝ × ℝ => K (y.1, w))
      ((fderiv ℝ K (p.1, w)).comp
        ((ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ))) p :=
    (K.differentiable (p.1, w)).hasFDerivAt.comp p (hinl.comp p hasFDerivAt_fst)
  have hfun : (fun y : ℝ × ℝ => partialFourierIntegrand K (y, w))
      = fun y => Complex.exp (c * ((y.2 : ℝ) : ℂ)) * K (y.1, w) := by
    funext y
    rw [partialFourierIntegrand_apply, hphase y]
  have hd : HasFDerivAt (fun y : ℝ × ℝ => partialFourierIntegrand K (y, w))
      (Complex.exp (c * ((p.2 : ℝ) : ℂ)) • ((fderiv ℝ K (p.1, w)).comp
          ((ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)))
        + K (p.1, w) • (Complex.exp (c * ((p.2 : ℝ) : ℂ))
          • (c • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))))) p := by
    rw [hfun]
    exact hφ.mul hK
  rw [hd.fderiv, partialFourierIntegrand_apply, Dop_apply, hphase p]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, smul_eq_mul]
  have hlin : fderiv ℝ (K : ℝ × ℝ → ℂ) (p.1, w) (h.1, (0 : ℝ))
      = (h.1 : ℂ) * fderiv ℝ (K : ℝ × ℝ → ℂ) (p.1, w) ((1 : ℝ), (0 : ℝ)) := by
    rw [show ((h.1, (0 : ℝ)) : ℝ × ℝ) = h.1 • ((1 : ℝ), (0 : ℝ)) by simp, map_smul,
      Complex.real_smul]
  rw [hlin, wMul, hc]
  push_cast
  ring

/-! ### Integrability and linearity in the kernel -/

theorem integrable_partialFourierIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    Integrable (fun w : ℝ => partialFourierIntegrand K (p, w)) volume := by
  refine (integrable_inv_one_add_sq.const_mul (leibnizConst 0 * kSup K 0)).mono'
    (aestronglyMeasurable_dirDeriv_prodMk (contDiff_partialFourierIntegrand K) [] p)
    (Filter.Eventually.of_forall fun w => ?_)
  have h := norm_iteratedFDeriv_partialFourierIntegrand_le K 0 p w
  rwa [norm_iteratedFDeriv_zero] at h

theorem partialFourier_add (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) :
    partialFourier (K₁ + K₂) = partialFourier K₁ + partialFourier K₂ := by
  funext p
  rw [Pi.add_apply, partialFourier_eq_integral_integrand, partialFourier_eq_integral_integrand,
    partialFourier_eq_integral_integrand]
  simp only
  rw [← integral_add (integrable_partialFourierIntegrand K₁ p)
    (integrable_partialFourierIntegrand K₂ p)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [partialFourierIntegrand_apply, _root_.add_apply, mul_add]

theorem partialFourier_smul (c : ℂ) (K : 𝓢(ℝ × ℝ, ℂ)) :
    partialFourier (c • K) = c • partialFourier K := by
  funext p
  rw [Pi.smul_apply, partialFourier_eq_integral_integrand, partialFourier_eq_integral_integrand]
  simp only
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [partialFourierIntegrand_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-! ### The first derivative -/

/-- The bound family of #170 at order `0`, in the form #124's first-order identity takes. -/
theorem norm_partialFourierIntegrand_le (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) (w : ℝ) :
    ‖partialFourierIntegrand K (p, w)‖ ≤ leibnizConst 0 * kSup K 0 * (1 + w ^ 2)⁻¹ := by
  have h := norm_iteratedFDeriv_partialFourierIntegrand_le K 0 p w
  rwa [norm_iteratedFDeriv_zero] at h

/-- And at order `1`. -/
theorem norm_fderiv_partialFourierIntegrand_le (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) (w : ℝ) :
    ‖fderiv ℝ (fun y : ℝ × ℝ => partialFourierIntegrand K (y, w)) p‖
      ≤ leibnizConst 1 * kSup K 1 * (1 + w ^ 2)⁻¹ := by
  have h := norm_iteratedFDeriv_partialFourierIntegrand_le K 1 p w
  rwa [norm_iteratedFDeriv_one] at h

/-- ★★ **The derivative of the partial Fourier transform in a direction is the partial Fourier
transform of `Dop h K`**: `∂_h 𝓕₂K(p) = 𝓕₂(Dop h K)(p)`. -/
theorem fderiv_partialFourier_apply (K : 𝓢(ℝ × ℝ, ℂ)) (p h : ℝ × ℝ) :
    fderiv ℝ (partialFourier K) p h = partialFourier (Dop h K) p := by
  rw [partialFourier_eq_integral_integrand,
    fderiv_integral_apply_of_bound (μ := volume) (U := univ)
      (F := fun (p : ℝ × ℝ) (w : ℝ) => partialFourierIntegrand K (p, w))
      (b₀ := fun w => leibnizConst 0 * kSup K 0 * (1 + w ^ 2)⁻¹)
      (b₁ := fun w => leibnizConst 1 * kSup K 1 * (1 + w ^ 2)⁻¹) isOpen_univ
      (fun w => (contDiff_partialFourierIntegrand_left K w).differentiable (by simp))
      (fun x => aestronglyMeasurable_dirDeriv_prodMk (contDiff_partialFourierIntegrand K) [] x)
      (fun x => aestronglyMeasurable_fderiv_dirDeriv_prodMk
        (contDiff_partialFourierIntegrand K) [] x)
      (integrable_inv_one_add_sq.const_mul _) (integrable_inv_one_add_sq.const_mul _)
      (fun x _ w => norm_partialFourierIntegrand_le K x w)
      (fun x _ w => norm_fderiv_partialFourierIntegrand_le K x w) (mem_univ p) h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show fderiv ℝ (fun y : ℝ × ℝ => partialFourierIntegrand K (y, w)) p h = _
  exact fderiv_partialFourierIntegrand_apply K w p h

/-- `∂_u 𝓕₂K = 𝓕₂(∂_u K)`. -/
theorem fderiv_partialFourier_fst (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    fderiv ℝ (partialFourier K) p ((1 : ℝ), (0 : ℝ))
      = partialFourier (lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) K) p := by
  rw [fderiv_partialFourier_apply, Dop_fst]

/-- `∂_ξ 𝓕₂K = 𝓕₂((−2πi w) K)`. -/
theorem fderiv_partialFourier_snd (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    fderiv ℝ (partialFourier K) p ((0 : ℝ), (1 : ℝ))
      = partialFourier (smulLeftCLM ℂ wMul K) p := by
  rw [fderiv_partialFourier_apply, Dop_snd]

/-- ★ The derivative as a continuous linear map in the direction. -/
theorem hasFDerivAt_partialFourier (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    HasFDerivAt (partialFourier K)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (partialFourier (lineDerivOpCLM ℂ 𝓢(ℝ × ℝ, ℂ) ((1 : ℝ), (0 : ℝ)) K) p)
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (partialFourier (smulLeftCLM ℂ wMul K) p)) p := by
  have hd := ((contDiff_partialFourier K).differentiable (by simp) p).hasFDerivAt
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [fderiv_partialFourier_apply, Dop, _root_.add_apply, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply, partialFourier_add,
    partialFourier_smul, partialFourier_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.real_smul,
    Complex.real_smul, smul_eq_mul, smul_eq_mul]

/-! ### All orders -/

/-- The composite of `Dop` along a tuple of directions, the **last** direction applied first — the
order `iteratedFDeriv_apply_succ_last` peels them in. -/
noncomputable def dopFin : (n : ℕ) → (Fin n → ℝ × ℝ) → (𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ))
  | 0, _ => ContinuousLinearMap.id ℂ _
  | n + 1, v => (dopFin n (Fin.init v)).comp (Dop (v (Fin.last n)))

@[simp] theorem dopFin_zero (v : Fin 0 → ℝ × ℝ) : dopFin 0 v = ContinuousLinearMap.id ℂ _ := rfl

theorem dopFin_succ (n : ℕ) (v : Fin (n + 1) → ℝ × ℝ) :
    dopFin (n + 1) v = (dopFin n (Fin.init v)).comp (Dop (v (Fin.last n))) := rfl

/-- ★★ **Every iterated derivative of the partial Fourier transform is a partial Fourier
transform**: `∂ⁿ 𝓕₂K(p)(v₁, …, vₙ) = 𝓕₂(dopFin v K)(p)`. -/
theorem iteratedFDeriv_partialFourier_apply :
    ∀ (n : ℕ) (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) (v : Fin n → ℝ × ℝ),
      (iteratedFDeriv ℝ n (partialFourier K) p : (Fin n → ℝ × ℝ) → ℂ) v
        = partialFourier (dopFin n v K) p
  | 0, K, p, v => by
      rw [iteratedFDeriv_zero_apply]
      rfl
  | n + 1, K, p, v => by
      rw [iteratedFDeriv_apply_succ_last
        ((contDiff_partialFourier K).contDiffAt.of_le (by exact_mod_cast le_top)) v]
      have hfun : (fun y => fderiv ℝ (partialFourier K) y (v (Fin.last n)))
          = partialFourier (Dop (v (Fin.last n)) K) :=
        funext fun y => fderiv_partialFourier_apply K y _
      rw [hfun, iteratedFDeriv_partialFourier_apply n _ p (Fin.init v)]
      rfl

end SchwartzMap

end
