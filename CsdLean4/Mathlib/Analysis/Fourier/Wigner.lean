/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.GaussianPacket

/-!
# The Wigner function on Schwartz space

**Category:** 1-Mathlib (staged for upstream). BACKLOG #45 — the Wigner–Moyal phase-space
formulation, the part that is Fourier analysis.

For `ψ ∈ 𝓢(ℝ, ℂ)` the **Wigner function** is the Fourier transform in `y` of the kernel
`y ↦ ψ(x + y/2) · conj ψ(x − y/2)`, in Mathlib's convention `𝓕 f (ξ) = ∫ e^{−2πiyξ} f(y) dy`:

`W_ψ(x, ξ) = ∫ e^{−2πiyξ} ψ(x + y/2) conj ψ(x − y/2) dy`.

The variable `ξ` is the frequency; the momentum is `p = 2πξ` (`ℏ = m = 1`, the convention of
`SchrodingerGroup.lean`, where the free Hamiltonian is the multiplier `2π²ξ²`).

* `affineCLM x hs`, `modCLM a` — the reparametrisation `ψ ↦ ψ(x + s ·)` (`s ≠ 0`) and the
  modulation `ψ ↦ e^{2πia·} ψ` as continuous linear maps of Schwartz space;
* `wignerKernel ψ x : 𝓢(ℝ, ℂ)` — the kernel is Schwartz in `y`; `wigner ψ x ξ` — its Fourier
  transform at `ξ`;
* ★ `conj_wigner`, `im_wigner` — **the Wigner function is real**;
* ★ `integral_wigner_right` — **the `ξ`-marginal is the position density**: `∫ W_ψ(x, ξ) dξ = |ψ(x)|²`
  (Fourier inversion at the origin);
* ★★ `wigner_fourier` — **the momentum representation**: `W_{𝓕ψ}(ξ, −x) = W_ψ(x, ξ)`, by Parseval
  for Schwartz functions (`SchwartzMap.integral_inner_fourier_fourier`) applied to the modulated
  reparametrisations, together with the Fourier transform of an affine reparametrisation
  (`fourier_comp_affine`) and of a modulation (`fourier_char_mul`);
* ★ `integral_wigner_left` — **the `x`-marginal is the momentum density**: `∫ W_ψ(x, ξ) dx = |𝓕ψ(ξ)|²`;
  `integral_integral_wigner` — total mass `∫|ψ|²`; `integral_integral_mul_wigner_left/right` —
  the position and momentum expectations are the phase-space moments;
* ★ `wigner_gaussianS` — **the Gaussian is positive**: `W_{g_σ}(x, ξ) = √(2/σ) e^{−2πσx²} e^{−2πξ²/σ}`
  for the Schwartz Gaussian `g_σ = e^{−πσx²}`, `σ > 0` (`wigner_gaussianS_pos`);
* ★ `wigner_zero_zero_of_odd`, `re_wigner_zero_zero_neg` — **negativity is a witness of
  non-classicality**: an odd `ψ ≠ 0` has `W_ψ(0, 0) = −2∫|ψ|² < 0`;
* ★★ `wigner_freeSchrodingerS` — **the free evolution is the classical free flow**:
  `W_{U₀(t)ψ}(x, ξ) = W_ψ(x − 2πtξ, ξ)`, i.e. `W_t(x, p) = W_0(x − pt, p)` in the momentum
  `p = 2πξ` — Liouville transport, exact for the free Hamiltonian (the phase
  `e^{−2π²it[(ξ+η/2)² − (ξ−η/2)²]} = e^{−4π²itξη}` is the character of the shift).

## Honest scope

⚠️ One dimension, Schwartz data. The expectation of a **general** Weyl-quantised observable as the
phase-space integral against `W` (only the position and momentum moments are stated here), the
joint integrability of `(x, ξ) ↦ W_ψ(x, ξ)` on `ℝ²`, and the Moyal bracket with its `ℏ²`
expansion (only the free, quadratic case is stated, where the Moyal and Poisson flows agree)
are BACKLOG #63 and #64.

References: E. Wigner, Phys. Rev. 40 (1932) 749; J. E. Moyal, Proc. Cambridge Philos. Soc. 45
(1949) 99; G. B. Folland, *Harmonic Analysis in Phase Space* (1989) §1.8;
`Mathlib/Analysis/Semigroup/SchrodingerSchwartz.lean`, `GaussianPacket.lean`; `specs/BACKLOG.md`
#45; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate

namespace WignerFunction

/-! ### Two continuous linear maps of Schwartz space -/

/-- `y ↦ x + s y` has temperate growth. -/
theorem hasTemperateGrowth_affine (x s : ℝ) :
    Function.HasTemperateGrowth (fun y : ℝ => x + s * y) := by
  have h := (Function.HasTemperateGrowth.const (E := ℝ) x).add
    (s • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
  exact h

/-- `y ↦ x + s y` is antilipschitz for `s ≠ 0`. -/
theorem antilipschitzWith_affine (x : ℝ) {s : ℝ} (hs : s ≠ 0) :
    AntilipschitzWith ⟨|s|⁻¹, inv_nonneg.mpr (abs_nonneg s)⟩ (fun y : ℝ => x + s * y) := by
  refine AntilipschitzWith.of_le_mul_dist fun y z => ?_
  show dist y z ≤ |s|⁻¹ * dist (x + s * y) (x + s * z)
  rw [Real.dist_eq, Real.dist_eq, show x + s * y - (x + s * z) = s * (y - z) by ring, abs_mul,
    ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hs), one_mul]

/-- The reparametrisation `ψ ↦ (y ↦ ψ(x + s y))`, `s ≠ 0`, on Schwartz space. -/
noncomputable def affineCLM (x : ℝ) {s : ℝ} (hs : s ≠ 0) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_affine x s)
    (antilipschitzWith_affine x hs)

@[simp]
theorem affineCLM_apply (x : ℝ) {s : ℝ} (hs : s ≠ 0) (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    affineCLM x hs ψ y = ψ (x + s * y) :=
  rfl

/-- The character `y ↦ e^{2πiay}` has temperate growth. -/
theorem hasTemperateGrowth_char (a : ℝ) :
    Function.HasTemperateGrowth (fun y : ℝ => (𝐞 (a * y) : ℂ)) := by
  have h : (fun y : ℝ => (𝐞 (a * y) : ℂ))
      = (fun s : ℝ => Complex.exp (↑s * Complex.I)) ∘ fun y => 2 * π * (a * y) := by
    funext y
    rw [Function.comp_apply, Real.fourierChar_apply]
  rw [h]
  exact SchrodingerGroup.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- The modulation `ψ ↦ (y ↦ e^{2πiay} ψ(y))` on Schwartz space. -/
noncomputable def modCLM (a : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (𝐞 (a * y) : ℂ))

@[simp]
theorem modCLM_apply (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    modCLM a ψ y = (𝐞 (a * y) : ℂ) * ψ y := by
  rw [modCLM, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char a), smul_eq_mul]

/-! ### Two Fourier identities on `ℝ` -/

theorem conj_fourierChar (t : ℝ) : conj (𝐞 t : ℂ) = 𝐞 (-t) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- Modulation shifts the Fourier transform: `𝓕 (e^{2πia·} φ) (w) = 𝓕 φ (w − a)`. -/
theorem fourier_char_mul (φ : ℝ → ℂ) (a w : ℝ) :
    𝓕 (fun y => (𝐞 (a * y) : ℂ) * φ y) w = 𝓕 φ (w - a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  congr 1
  funext y
  rw [show -(y * (w - a)) = -(y * w) + a * y by ring, AddChar.map_add_eq_mul, Circle.smul_def,
    Circle.smul_def, Circle.coe_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- The Fourier transform of an affine reparametrisation:
`𝓕 (φ(x + s ·)) (w) = |s|⁻¹ e^{2πixw/s} 𝓕 φ (w/s)`, `s ≠ 0`. -/
theorem fourier_comp_affine (φ : ℝ → ℂ) (x : ℝ) {s : ℝ} (hs : s ≠ 0) (w : ℝ) :
    𝓕 (fun y => φ (x + s * y)) w = |s⁻¹| • ((𝐞 (x * (w / s)) : ℂ) * 𝓕 φ (w / s)) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  set G : ℝ → ℂ := fun z => (𝐞 (-((z - x) / s * w)) : ℂ) * φ z with hG
  have h1 : ∀ y, 𝐞 (-(y * w)) • φ (x + s * y) = G (x + s * y) := by
    intro y
    simp only [hG, Circle.smul_def, smul_eq_mul, add_sub_cancel_left, mul_div_cancel_left₀ y hs]
  have h2 : ∀ z, G z = (𝐞 (x * (w / s)) : ℂ) * (𝐞 (-(z * (w / s))) • φ z) := by
    intro z
    have harg : -((z - x) / s * w) = x * (w / s) + -(z * (w / s)) := by
      field_simp
      ring
    simp only [hG, Circle.smul_def, smul_eq_mul]
    rw [harg, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
  simp_rw [h1]
  calc ∫ y, G (x + s * y) = ∫ y, (fun u => G (x + u)) (s * y) := rfl
    _ = |s⁻¹| • ∫ u, G (x + u) := Measure.integral_comp_mul_left (fun u => G (x + u)) s
    _ = |s⁻¹| • ∫ z, G z := by rw [integral_add_left_eq_self]
    _ = _ := by
      simp_rw [h2]
      rw [integral_const_mul]

/-! ### The Wigner function -/

theorem half_ne_zero' : (1 / 2 : ℝ) ≠ 0 := by norm_num

theorem neg_half_ne_zero' : (-1 / 2 : ℝ) ≠ 0 := by norm_num

/-- **The Wigner kernel** `y ↦ ψ(x + y/2) · conj ψ(x − y/2)` as a Schwartz function of `y`. -/
noncomputable def wignerKernel (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth.comp
      (affineCLM x neg_half_ne_zero' ψ).hasTemperateGrowth) (affineCLM x half_ne_zero' ψ)

theorem wignerKernel_apply (ψ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    wignerKernel ψ x y = ψ (x + y / 2) * conj (ψ (x - y / 2)) := by
  show ψ (x + 1 / 2 * y) * conj (ψ (x + -1 / 2 * y)) = _
  rw [show x + 1 / 2 * y = x + y / 2 by ring, show x + -1 / 2 * y = x - y / 2 by ring]

/-- **The Wigner function** `W_ψ(x, ξ) = ∫ e^{−2πiyξ} ψ(x + y/2) conj ψ(x − y/2) dy`. -/
noncomputable def wigner (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : ℂ :=
  𝓕 (wignerKernel ψ x) ξ

theorem wigner_eq_integral (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wigner ψ x ξ = ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (ψ (x + y / 2) * conj (ψ (x - y / 2))) := by
  rw [wigner, SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp only [wignerKernel_apply, Circle.smul_def, smul_eq_mul]

/-- ★ **The Wigner function is real.** -/
theorem conj_wigner (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : conj (wigner ψ x ξ) = wigner ψ x ξ := by
  rw [wigner_eq_integral, ← integral_conj]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext y
  simp only [map_mul, conj_fourierChar, Complex.conj_conj, neg_neg, neg_mul, neg_div,
    ← sub_eq_add_neg, sub_neg_eq_add]
  ring

theorem im_wigner (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : (wigner ψ x ξ).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_wigner ψ x ξ)

/-- ★ **The `ξ`-marginal is the position density**: `∫ W_ψ(x, ξ) dξ = |ψ(x)|²`. -/
theorem integral_wigner_right (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∫ ξ, wigner ψ x ξ = (‖ψ x‖ : ℂ) ^ 2 := by
  have h1 : Integrable (⇑(wignerKernel ψ x)) := (wignerKernel ψ x).integrable
  have h2 : Integrable (𝓕 ⇑(wignerKernel ψ x)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 (wignerKernel ψ x)).integrable
  have hinv := (wignerKernel ψ x).continuous.fourierInv_fourier_eq h1 h2
  have h0 : 𝓕⁻ (𝓕 ⇑(wignerKernel ψ x)) 0 = ∫ ξ, 𝓕 ⇑(wignerKernel ψ x) ξ := by
    rw [Real.fourierInv_eq]
    simp
  calc ∫ ξ, wigner ψ x ξ = 𝓕⁻ (𝓕 ⇑(wignerKernel ψ x)) 0 := by rw [h0]; rfl
    _ = wignerKernel ψ x 0 := by rw [hinv]
    _ = _ := by
      rw [wignerKernel_apply]
      simp [Complex.mul_conj']

/-! ### The momentum representation -/

/-- ★★ **The momentum representation**: `W_{𝓕ψ}(ξ, −x) = W_ψ(x, ξ)` — the Wigner function of the
Fourier transform is the Wigner function with the roles of position and frequency exchanged
(Parseval on the modulated reparametrisations). -/
theorem wigner_fourier (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wigner (𝓕 ψ) ξ (-x) = wigner ψ x ξ := by
  set f : 𝓢(ℝ, ℂ) := modCLM (-(ξ / 2)) (affineCLM x half_ne_zero' ψ) with hf
  set g : 𝓢(ℝ, ℂ) := modCLM (ξ / 2) (affineCLM x neg_half_ne_zero' ψ) with hg
  have hP := SchwartzMap.integral_inner_fourier_fourier g f
  simp only [RCLike.inner_apply] at hP
  -- `hP : ∫ η, 𝓕 f η * conj (𝓕 g η) = ∫ y, f y * conj (g y)`
  have hR : ∫ y, f y * conj (g y) = wigner ψ x ξ := by
    rw [wigner_eq_integral]
    congr 1
    funext y
    simp only [hf, hg, modCLM_apply, affineCLM_apply, map_mul, conj_fourierChar]
    rw [show x + 1 / 2 * y = x + y / 2 by ring, show x + -1 / 2 * y = x - y / 2 by ring]
    have hc : (𝐞 (-(ξ / 2) * y) : ℂ) * 𝐞 (-(ξ / 2 * y)) = 𝐞 (-(y * ξ)) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    linear_combination (ψ (x + y / 2) * conj (ψ (x - y / 2))) * hc
  have hfF : ∀ η, 𝓕 f η
      = |(1 / 2 : ℝ)⁻¹| • ((𝐞 (x * ((η + ξ / 2) / (1 / 2))) : ℂ)
          * 𝓕 (⇑ψ) ((η + ξ / 2) / (1 / 2))) := by
    intro η
    have hf' : ⇑f = fun y => (𝐞 (-(ξ / 2) * y) : ℂ) * (fun y' => ψ (x + 1 / 2 * y')) y := by
      funext y
      simp [hf]
    rw [SchwartzMap.fourier_coe, hf', fourier_char_mul, fourier_comp_affine _ _ half_ne_zero',
      sub_neg_eq_add]
  have hgF : ∀ η, 𝓕 g η
      = |(-1 / 2 : ℝ)⁻¹| • ((𝐞 (x * ((η - ξ / 2) / (-1 / 2))) : ℂ)
          * 𝓕 (⇑ψ) ((η - ξ / 2) / (-1 / 2))) := by
    intro η
    have hg' : ⇑g = fun y => (𝐞 (ξ / 2 * y) : ℂ) * (fun y' => ψ (x + -1 / 2 * y')) y := by
      funext y
      simp [hg]
    rw [SchwartzMap.fourier_coe, hg', fourier_char_mul, fourier_comp_affine _ _ neg_half_ne_zero']
  set G : ℝ → ℂ := fun η => (𝐞 (-(η * -x)) : ℂ)
    * (𝓕 (⇑ψ) (ξ + η / 2) * conj (𝓕 (⇑ψ) (ξ - η / 2))) with hG
  have hpt : ∀ η, 𝓕 f η * conj (𝓕 g η) = 4 * G (4 * η) := by
    intro η
    rw [hfF, hgF, hG]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_fourierChar]
    rw [show (η + ξ / 2) / (1 / 2) = ξ + 4 * η / 2 by ring,
      show (η - ξ / 2) / (-1 / 2) = ξ - 4 * η / 2 by ring,
      show |(1 / 2 : ℝ)⁻¹| = 2 by norm_num, show |(-1 / 2 : ℝ)⁻¹| = 2 by norm_num]
    have hc : (𝐞 (x * (ξ + 4 * η / 2)) : ℂ) * 𝐞 (-(x * (ξ - 4 * η / 2)))
        = 𝐞 (-(4 * η * -x)) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    push_cast
    linear_combination (4 * (𝓕 (⇑ψ) (ξ + 4 * η / 2) * conj (𝓕 (⇑ψ) (ξ - 4 * η / 2)))) * hc
  have hsub := Measure.integral_comp_mul_left G 4
  have hL : ∫ η, 𝓕 f η * conj (𝓕 g η) = wigner (𝓕 ψ) ξ (-x) := by
    rw [wigner_eq_integral]
    calc ∫ η, 𝓕 f η * conj (𝓕 g η) = ∫ η, 4 * G (4 * η) := by
          congr 1
          funext η
          exact hpt η
      _ = 4 * ∫ η, G (4 * η) := integral_const_mul 4 _
      _ = ∫ η, G η := by
          rw [hsub, Complex.real_smul, show |(4 : ℝ)⁻¹| = 4⁻¹ by norm_num]
          push_cast
          ring
      _ = _ := rfl
  rw [← hR, ← hP, hL]

/-- ★ **The `x`-marginal is the momentum density**: `∫ W_ψ(x, ξ) dx = |𝓕ψ(ξ)|²`. -/
theorem integral_wigner_left (ψ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ∫ x, wigner ψ x ξ = (‖𝓕 ψ ξ‖ : ℂ) ^ 2 := by
  have h : ∀ x, wigner ψ x ξ = wigner (𝓕 ψ) ξ (-x) := fun x => (wigner_fourier ψ x ξ).symm
  simp_rw [h]
  rw [integral_neg_eq_self (fun x => wigner (𝓕 ψ) ξ x) volume, integral_wigner_right]

/-- **Total mass**: `∫∫ W_ψ = ∫ |ψ|²`. -/
theorem integral_integral_wigner (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x, ∫ ξ, wigner ψ x ξ = ∫ x, (‖ψ x‖ : ℂ) ^ 2 := by
  simp_rw [integral_wigner_right]

/-- **The position expectation is the first `x`-moment of `W_ψ`**: `∫∫ x W_ψ = ∫ x |ψ(x)|²`. -/
theorem integral_integral_mul_wigner_left (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ∫ ξ : ℝ, (x : ℂ) * wigner ψ x ξ = ∫ x : ℝ, (x : ℂ) * (‖ψ x‖ : ℂ) ^ 2 := by
  simp_rw [integral_const_mul, integral_wigner_right]

/-- **The momentum expectation is the first `ξ`-moment of `W_ψ`**: `∫∫ ξ W_ψ = ∫ ξ |𝓕ψ(ξ)|²`
(the momentum is `p = 2πξ`). -/
theorem integral_integral_mul_wigner_right (ψ : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ∫ x : ℝ, (ξ : ℂ) * wigner ψ x ξ = ∫ ξ : ℝ, (ξ : ℂ) * (‖𝓕 ψ ξ‖ : ℂ) ^ 2 := by
  simp_rw [integral_const_mul, integral_wigner_left]

/-! ### Positivity of the Gaussian, negativity of odd states -/

theorem re_ofReal_pos {σ : ℝ} (hσ : 0 < σ) : 0 < (σ : ℂ).re := by simpa using hσ

/-- The Wigner kernel of the Gaussian `e^{−πσx²}` is `e^{−2πσx²} · e^{−π(σ/2)y²}`. -/
theorem wignerKernel_gaussianS {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    wignerKernel (SchrodingerGroup.gaussianS σ (re_ofReal_pos hσ)) x
      = (Complex.exp (-(2 * π * σ * x ^ 2) : ℝ)) •
          SchrodingerGroup.gaussianS (σ / 2 : ℝ) (re_ofReal_pos (half_pos hσ)) := by
  ext y
  rw [wignerKernel_apply, smul_apply, smul_eq_mul, SchrodingerGroup.gaussianS_apply,
    SchrodingerGroup.gaussianS_apply, SchrodingerGroup.gaussianS_apply, ← Complex.exp_conj,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal]
  push_cast
  ring

/-- ★ **The Wigner function of the Gaussian** `g_σ = e^{−πσx²}` (`σ > 0`) is the positive Gaussian
`√(2/σ) e^{−2πσx²} e^{−2πξ²/σ}`. -/
theorem wigner_gaussianS {σ : ℝ} (hσ : 0 < σ) (x ξ : ℝ) :
    wigner (SchrodingerGroup.gaussianS σ (re_ofReal_pos hσ)) x ξ
      = ((Real.sqrt (2 / σ) * Real.exp (-(2 * π * σ * x ^ 2))
          * Real.exp (-(2 * π * ξ ^ 2 / σ)) : ℝ) : ℂ) := by
  rw [wigner, wignerKernel_gaussianS hσ, FourierSMul.fourier_smul, smul_apply, smul_eq_mul]
  have hF := congrFun (SchrodingerGroup.fourier_gaussianS (σ / 2 : ℝ)
    (re_ofReal_pos (half_pos hσ))) ξ
  rw [hF]
  have hpow : ((σ / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (σ / 2) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (half_pos hσ).le]
    push_cast
    rfl
  rw [hpow]
  have hsqrt : (1 : ℂ) / (Real.sqrt (σ / 2) : ℂ) = (Real.sqrt (2 / σ) : ℂ) := by
    rw [show (2 / σ : ℝ) = (σ / 2)⁻¹ by rw [inv_div], Real.sqrt_inv]
    push_cast
    ring
  rw [hsqrt]
  push_cast
  have hexp : Complex.exp (-(π : ℂ) / ((σ : ℂ) / 2) * (ξ : ℂ) ^ 2)
      = Complex.exp (-(2 * (π : ℂ) * (ξ : ℂ) ^ 2 / (σ : ℂ))) := by
    congr 1
    rw [div_div_eq_mul_div]
    ring
  rw [hexp]
  ring

/-- ★ The Wigner function of the Gaussian is positive everywhere. -/
theorem wigner_gaussianS_pos {σ : ℝ} (hσ : 0 < σ) (x ξ : ℝ) :
    0 < (wigner (SchrodingerGroup.gaussianS σ (re_ofReal_pos hσ)) x ξ).re := by
  rw [wigner_gaussianS hσ, Complex.ofReal_re]
  have h2 : 0 < Real.sqrt (2 / σ) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- ★ **Negativity at the origin for odd states**: if `ψ(−y) = −ψ(y)` then
`W_ψ(0, 0) = −2 ∫ |ψ|²`. -/
theorem wigner_zero_zero_of_odd (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ y, ψ (-y) = -ψ y) :
    wigner ψ 0 0 = -(2 * ∫ y, ((‖ψ y‖ ^ 2 : ℝ) : ℂ)) := by
  rw [wigner_eq_integral]
  have h1 : ∀ y : ℝ, (𝐞 (-(y * 0)) : ℂ) * (ψ (0 + y / 2) * conj (ψ (0 - y / 2)))
      = -((fun u : ℝ => ((‖ψ u‖ ^ 2 : ℝ) : ℂ)) (2⁻¹ * y)) := by
    intro y
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, zero_add,
      zero_sub, hψ, map_neg, mul_neg, Complex.mul_conj', div_eq_inv_mul]
    push_cast
    ring
  simp_rw [h1]
  rw [integral_neg, Measure.integral_comp_mul_left (fun u : ℝ => ((‖ψ u‖ ^ 2 : ℝ) : ℂ)) 2⁻¹,
    inv_inv, abs_two, Complex.real_smul]
  push_cast
  ring

/-- A nonzero Schwartz function has positive `L²` mass. -/
theorem integral_norm_sq_pos (ψ : 𝓢(ℝ, ℂ)) (hψ : ψ ≠ 0) : 0 < ∫ y, ‖ψ y‖ ^ 2 := by
  have hint : Integrable (fun y => ‖ψ y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm ψ.continuous.aestronglyMeasurable).mp (ψ.memLp 2 volume)
  rw [integral_pos_iff_support_of_nonneg (fun y => by positivity) hint]
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (SchwartzMap.ext h)
  have hopen : IsOpen (Function.support fun y => ‖ψ y‖ ^ 2) := by
    rw [Function.support_eq_preimage]
    exact isOpen_compl_singleton.preimage (ψ.continuous.norm.pow 2)
  exact hopen.measure_pos volume ⟨y₀, pow_ne_zero 2 (norm_ne_zero_iff.mpr hy₀)⟩

/-- ★ **Negativity is a witness of non-classicality**: an odd nonzero `ψ` has `W_ψ(0, 0) < 0`. -/
theorem re_wigner_zero_zero_neg (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ y, ψ (-y) = -ψ y) (h0 : ψ ≠ 0) :
    (wigner ψ 0 0).re < 0 := by
  have hI : ∫ y, ((‖ψ y‖ ^ 2 : ℝ) : ℂ) = ((∫ y, ‖ψ y‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [wigner_zero_zero_of_odd ψ hψ, hI]
  have := integral_norm_sq_pos ψ h0
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
  linarith

/-! ### The free evolution is the classical free flow -/

/-- ★★ **Liouville transport for the free Schrödinger group**:
`W_{U₀(t)ψ}(x, ξ) = W_ψ(x − 2πtξ, ξ)` — in the momentum `p = 2πξ`, `W_t(x, p) = W_0(x − pt, p)`,
the classical free flow, exact (the quadratic Hamiltonian has no `ℏ²` Moyal correction). -/
theorem wigner_freeSchrodingerS (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wigner (SchrodingerGroup.freeSchrodingerS t ψ) x ξ = wigner ψ (x - 2 * π * t * ξ) ξ := by
  rw [← wigner_fourier, ← wigner_fourier ψ]
  have hF : 𝓕 (SchrodingerGroup.freeSchrodingerS t ψ)
      = SchwartzMap.smulLeftCLM ℂ (SchrodingerGroup.phaseFun SchrodingerGroup.freeSymbol t)
          (𝓕 ψ) := by
    rw [SchrodingerGroup.freeSchrodingerS, SchrodingerGroup.fourierGroupS,
      SchwartzMap.fourierMultiplierCLM_apply, FourierInvPair.fourier_fourierInv_eq]
  have hT := SchrodingerGroup.hasTemperateGrowth_phaseFun
    (SchrodingerGroup.hasTemperateGrowth_freeSymbol (E := ℝ)) t
  rw [hF, wigner_eq_integral, wigner_eq_integral]
  congr 1
  funext η
  rw [SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul,
    smul_eq_mul, map_mul]
  have hph : (𝐞 (-(η * -x)) : ℂ)
      * (SchrodingerGroup.phaseFun SchrodingerGroup.freeSymbol t (ξ + η / 2)
        * conj (SchrodingerGroup.phaseFun SchrodingerGroup.freeSymbol t (ξ - η / 2)))
      = 𝐞 (-(η * -(x - 2 * π * t * ξ))) := by
    simp only [Real.fourierChar_apply, SchrodingerGroup.phaseFun, SchrodingerGroup.freeSymbol,
      Real.norm_eq_abs, sq_abs, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (𝓕 ψ (ξ + η / 2) * conj (𝓕 ψ (ξ - η / 2))) * hph

end WignerFunction

end
