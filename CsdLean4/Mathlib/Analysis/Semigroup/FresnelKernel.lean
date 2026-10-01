/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.GaussianPacket
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Feynman's kernel for the free propagator

**Category:** 1-Mathlib (CSD-free; staged for upstream).

`Analysis/Semigroup/SchrodingerSchwartz.lean` builds the free propagator `U₀(t) = e^{−itH₀}`,
`H₀ = −½ d²/dx²`, as a Fourier multiplier: `U₀(t) = 𝓕⁻¹ e^{−2π²itξ²} 𝓕`. This module (BACKLOG #44,
FC-5′) writes the **kernel** of that operator — the one the path integral is built from — by
analytic continuation of the heat kernel in the time variable:

* **the kernel at complex time** `w`, `fresnelKernel w x = (4πw)^{−1/2} e^{−x²/(4w)}`, is a
  Schwartz function for `Re w > 0` (`fresnelS`, on top of `GaussianPacket.lean`'s complex-parameter
  Gaussian) and its Fourier transform is the multiplier `e^{−4π²wξ²}` (★ `fourier_fresnelS`): the
  amplitude `(4πw)^{−1/2}` is exactly what cancels the `a^{−1/2}` of the Gaussian transform;
* **the operator** `fresnelOp w` is convolution with that kernel, so it has both the kernel form
  `∫ K_w(x − y) ψ(y) dy` (★ `fresnelOp_apply`) and the multiplier form (★ `fourier_fresnelOp`);
  it is a semigroup in the complex time (★★ `fresnelOp_fresnelOp`), and therefore **every
  time-slicing is exact**: `n+1` slices of `w/(n+1)` compose to `w` (★★ `fresnelOp_iterate_div`),
  each slice one kernel integral (★ `fresnelOp_iterate_succ_apply`);
* ★★★ `tendsto_fresnelOp` — **the Gaussian-regularised Fresnel integral is the propagator**:
  `(U₀(t)ψ)(x) = lim_{ε ↓ 0} ∫ K_{ε + it/2}(x − y) ψ(y) dy`, by dominated convergence on the
  Fourier side (`|e^{−4π²(ε+it/2)ξ²}| ≤ 1`, `𝓕ψ` integrable). This is the continuation `t ↦ it` of
  the heat kernel, taken where it converges absolutely and carried to the imaginary axis;
* ★ `fresnelKernel_I_mul` — at `w = it/2` the kernel **is** Feynman's
  `(2πit)^{−1/2} e^{ix²/(2t)}`, of constant modulus (`norm_fresnelKernel_I_mul`): it does not
  decay, which is why the integral is improper for general `L²` data — and absolutely convergent
  against the `L¹` Schwartz functions used here (★ `integrable_fresnelKernel_mul`);
* ★★★ `freeSchrodingerS_eq_integral_fresnel` — **Feynman's kernel formula, exactly**:
  `(U₀(t)ψ)(x) = (2πit)^{−1/2} ∫ e^{i(x−y)²/(2t)} ψ(y) dy` for `t ≠ 0` and Schwartz `ψ`, with no
  regularisation left in the statement. The regularised integrals converge both to the propagator
  and to this integral, and limits are unique;
* ★★ `freeSchrodingerS_iterate` — `U₀(t) = (U₀(t/(n+1)))^{n+1}`, so the `n`-slice iterated Feynman
  integral is exact for every `n`; and ★★★ `prod_fresnelKernel_eq_exp_discreteAction` — the product
  of the `n` kernels in that iterated integral is `((2πit/n)^{−1/2})^n e^{iS_n}` with `S_n` the
  **discrete action** `∑ (q_{k+1} − q_k)²/(2Δt)` of the sampled path (`discreteAction`). The phase
  of the path integral is a theorem here, not a notation.

## Honest scope

⚠️ One dimension, Schwartz data. The scoping note's `ψ ∈ L¹ ∩ L²` is **not** claimed: Fourier
inversion at this pin is the Schwartz theorem, and for `ψ ∈ L² \ L¹` the Feynman integral is
genuinely improper — it needs oscillatory-integral technology the pin does not have
(MATHLIB-ABSENT(fresnelIntegral)). Nothing here evaluates an oscillatory integral as a limit of
truncations `∫_{−R}^{R}`; the `ε ↓ 0` regularisation is the whole method.

⚠️ The `n`-slice identity is **exact for every `n`**, so no limit over paths is taken and none is
claimed: there is no measure on path space here, and no statement that `S_n` converges to the
classical action. The imaginary-time counterpart, where the path measure does exist, is the
corpus's Feynman–Kac chain.

⚠️ `fresnelS` is defined by a `dite` on `Re w > 0`, following Mathlib's own
`SchwartzMap.smulLeftCLM`: off the half-plane the kernel is not Schwartz, and every lemma carries
the hypothesis.

References: M. Reed, B. Simon, *Methods of Modern Mathematical Physics* II §IX.7;
R. P. Feynman, A. R. Hibbs, *Quantum Mechanics and Path Integrals* (1965) §2-2, §3-1;
`Analysis/Semigroup/SchrodingerSchwartz.lean` (FC-5″), `GaussianPacket.lean` (FC-5‴);
`specs/feynman-continuum-scoping.md` §5 and §8 D4; `specs/BACKLOG.md` #44;
`specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped Nat SchwartzMap FourierTransform ContDiff RealInnerProductSpace Topology
open MeasureTheory Filter Convolution
open ContinuousLinearMap (mul)

namespace SchrodingerGroup

variable {t : ℝ} {w w₁ w₂ : ℂ}

/-! ### The kernel at complex time -/

/-- The amplitude `(4πw)^{−1/2}` of the heat kernel at complex time `w`. -/
noncomputable def fresnelAmp (w : ℂ) : ℂ := (4 * (Real.pi : ℂ) * w) ^ (-(1 : ℂ) / 2)

/-- The heat kernel at complex time `w`: `(4πw)^{−1/2} e^{−x²/(4w)}`. At `w = it/2` this is
Feynman's kernel `(2πit)^{−1/2} e^{ix²/(2t)}` (`fresnelKernel_I_mul`). -/
noncomputable def fresnelKernel (w : ℂ) (x : ℝ) : ℂ :=
  fresnelAmp w * Complex.exp (-(x : ℂ) ^ 2 / (4 * w))

/-- The Fourier multiplier of the complex-time kernel: `e^{−4π²wξ²}`. At `w = it/2` this is the
free Schrödinger phase `e^{−2π²itξ²}` (`fresnelSymbol_I_mul`). -/
noncomputable def fresnelSymbol (w : ℂ) (ξ : ℝ) : ℂ :=
  Complex.exp (-(4 * (Real.pi : ℂ) ^ 2 * w) * (ξ : ℂ) ^ 2)

theorem re_four_pi_mul (w : ℂ) : (4 * (Real.pi : ℂ) * w).re = 4 * Real.pi * w.re := by
  have h : 4 * (Real.pi : ℂ) * w = ((4 * Real.pi : ℝ) : ℂ) * w := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]

theorem four_pi_mul_ne_zero (hw : w ≠ 0) : 4 * (Real.pi : ℂ) * w ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) hw
  exact Complex.ofReal_ne_zero.2 Real.pi_ne_zero

theorem ne_zero_of_re_pos (hw : 0 < w.re) : w ≠ 0 := fun h => by simp [h] at hw

/-- The Gaussian parameter of the kernel, `a = (4πw)⁻¹`, has positive real part. -/
theorem re_fresnelParam_pos (hw : 0 < w.re) : 0 < ((4 * (Real.pi : ℂ) * w)⁻¹).re :=
  re_inv_pos (by rw [re_four_pi_mul]; positivity)

theorem arg_four_pi_mul_ne_pi (hw : 0 < w.re) : (4 * (Real.pi : ℂ) * w).arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.1 h).1
  rw [re_four_pi_mul] at this
  nlinarith [Real.pi_pos]

/-- The modulus of the multiplier: `|e^{−4π²wξ²}| = e^{−4π²(Re w)ξ²}`, which is `≤ 1` for
`Re w ≥ 0` — the bound that drives every dominated convergence below. -/
theorem norm_fresnelSymbol (w : ℂ) (ξ : ℝ) :
    ‖fresnelSymbol w ξ‖ = Real.exp (-(4 * Real.pi ^ 2 * w.re * ξ ^ 2)) := by
  rw [fresnelSymbol, Complex.norm_exp]
  congr 1
  have h : -(4 * (Real.pi : ℂ) ^ 2 * w) * (ξ : ℂ) ^ 2
      = ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) * w := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]
  ring

theorem norm_fresnelSymbol_le_one (hw : 0 ≤ w.re) (ξ : ℝ) : ‖fresnelSymbol w ξ‖ ≤ 1 := by
  have h : 0 ≤ 4 * Real.pi ^ 2 * w.re * ξ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hw) (sq_nonneg ξ)
  rw [norm_fresnelSymbol]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The modulus of the Gaussian factor of the kernel is `≤ 1` when `Re w ≥ 0`: the exponent's real
part is `−x²(Re w)/(4|w|²)`. -/
theorem norm_exp_fresnel_le_one (hw : 0 ≤ w.re) (hw0 : w ≠ 0) (x : ℝ) :
    ‖Complex.exp (-(x : ℂ) ^ 2 / (4 * w))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.2 ?_
  have h : -(x : ℂ) ^ 2 / (4 * w) = ((-(x ^ 2) / 4 : ℝ) : ℂ) * w⁻¹ := by
    push_cast
    field_simp
  rw [h, Complex.re_ofReal_mul, Complex.inv_re]
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  have : 0 ≤ w.re / Complex.normSq w := div_nonneg hw hns.le
  nlinarith [sq_nonneg x]

/-- The kernel at complex time `w`, `Re w > 0`, as a Schwartz function: the Gaussian `e^{−πax²}` of
parameter `a = (4πw)⁻¹`, scaled by `(4πw)^{−1/2}`. The `dite` follows Mathlib's own
`SchwartzMap.smulLeftCLM`: outside the half-plane the Gaussian is not Schwartz, and every lemma
below carries `0 < w.re`. -/
noncomputable def fresnelS (w : ℂ) : 𝓢(ℝ, ℂ) :=
  if hw : 0 < w.re then
    fresnelAmp w • gaussianS ((4 * (Real.pi : ℂ) * w)⁻¹) (re_fresnelParam_pos hw)
  else 0

theorem fresnelS_eq (hw : 0 < w.re) :
    fresnelS w = fresnelAmp w • gaussianS ((4 * (Real.pi : ℂ) * w)⁻¹) (re_fresnelParam_pos hw) :=
  dif_pos hw

/-- The Schwartz function is the kernel. -/
theorem coe_fresnelS (hw : 0 < w.re) : ⇑(fresnelS w) = fresnelKernel w := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hexp : ∀ x : ℝ, -(Real.pi : ℂ) * (4 * (Real.pi : ℂ) * w)⁻¹ * (x : ℂ) ^ 2
      = -(x : ℂ) ^ 2 / (4 * w) := fun x => by field_simp
  funext x
  rw [fresnelS_eq hw]
  simp only [smul_apply, gaussianS_apply, fresnelKernel, smul_eq_mul, hexp]

/-- ★ **The Fourier transform of the complex-time kernel is the multiplier** `e^{−4π²wξ²}`:
the amplitude `(4πw)^{−1/2}` is exactly what cancels the `a^{−1/2}` of the Gaussian transform. -/
theorem fourier_fresnelS (hw : 0 < w.re) :
    ⇑(𝓕 (fresnelS w) : 𝓢(ℝ, ℂ)) = fresnelSymbol w := by
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have hbase : 4 * (Real.pi : ℂ) * w ≠ 0 := four_pi_mul_ne_zero hw0
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hinv : ((4 * (Real.pi : ℂ) * w)⁻¹) ^ (1 / 2 : ℂ)
      = ((4 * (Real.pi : ℂ) * w) ^ (1 / 2 : ℂ))⁻¹ :=
    Complex.inv_cpow _ _ (arg_four_pi_mul_ne_pi hw)
  have hcancel : fresnelAmp w * (1 / ((4 * (Real.pi : ℂ) * w)⁻¹) ^ (1 / 2 : ℂ)) = 1 := by
    rw [hinv, fresnelAmp, one_div, inv_inv, ← Complex.cpow_add _ _ hbase]
    norm_num
  funext ξ
  rw [fresnelS_eq hw, FourierSMul.fourier_smul, smul_apply, smul_eq_mul,
    congrFun (fourier_gaussianS _ (re_fresnelParam_pos hw)) ξ, fresnelSymbol, ← mul_assoc,
    hcancel, one_mul]
  congr 1
  field_simp

/-! ### The operator -/

/-- Convolution with the complex-time kernel, on Schwartz functions: `e^{−wH₀}` for
`H₀ = −½ d²/dx²`, read through `Re w > 0` (heat) and continued to `w = it/2` (Schrödinger). -/
noncomputable def fresnelOp (w : ℂ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (mul ℂ ℂ) (fresnelS w)

/-- ★ **The kernel form of the operator**: `(fresnelOp w ψ) x = ∫ K_w(x − y) ψ(y) dy`, an
absolutely convergent integral (Mathlib's Schwartz convolution). -/
theorem fresnelOp_apply (hw : 0 < w.re) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    fresnelOp w ψ x = ∫ y : ℝ, fresnelKernel w (x - y) * ψ y := by
  rw [fresnelOp, SchwartzMap.convolution_apply, MeasureTheory.convolution_mul_swap,
    coe_fresnelS hw]

/-- ★ **The multiplier form**: the Fourier transform of the operator is multiplication by
`e^{−4π²wξ²}`. -/
theorem fourier_fresnelOp (hw : 0 < w.re) (ψ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (fresnelOp w ψ) ξ = fresnelSymbol w ξ * 𝓕 ψ ξ := by
  rw [fresnelOp, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', congrFun (fourier_fresnelS hw) ξ]

/-- Fourier inversion, pointwise: a Schwartz function is the inverse transform of its transform. -/
theorem apply_eq_integral_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    f x = ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • 𝓕 f ξ := by
  have h : (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f :=
    FourierTransform.fourierInv_fourier_eq f
  conv_lhs => rw [← h]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]

theorem fresnelOp_apply_eq_integral_symbol (hw : 0 < w.re) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    fresnelOp w ψ x = ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (fresnelSymbol w ξ * 𝓕 ψ ξ) := by
  rw [apply_eq_integral_fourier]
  exact integral_congr_ae (.of_forall fun ξ => by simp only [fourier_fresnelOp hw])

/-- The multiplier is a one-parameter semigroup in the complex time. -/
theorem fresnelSymbol_add (w₁ w₂ : ℂ) (ξ : ℝ) :
    fresnelSymbol (w₁ + w₂) ξ = fresnelSymbol w₁ ξ * fresnelSymbol w₂ ξ := by
  rw [fresnelSymbol, fresnelSymbol, fresnelSymbol, ← Complex.exp_add]
  congr 1
  ring

/-- ★★ **The complex-time semigroup**: two slices compose into one,
`fresnelOp w₁ ∘ fresnelOp w₂ = fresnelOp (w₁ + w₂)`. On the Fourier side it is
`e^{−4π²w₁ξ²} e^{−4π²w₂ξ²} = e^{−4π²(w₁+w₂)ξ²}`; on the kernel side it is the Gaussian convolution
identity, continued in the time. -/
theorem fresnelOp_fresnelOp (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re) (ψ : 𝓢(ℝ, ℂ)) :
    fresnelOp w₁ (fresnelOp w₂ ψ) = fresnelOp (w₁ + w₂) ψ := by
  have hadd : 0 < (w₁ + w₂).re := by rw [Complex.add_re]; linarith
  have h : 𝓕 (fresnelOp w₁ (fresnelOp w₂ ψ)) = 𝓕 (fresnelOp (w₁ + w₂) ψ) := by
    ext ξ
    rw [fourier_fresnelOp h₁, fourier_fresnelOp h₂, fourier_fresnelOp hadd, fresnelSymbol_add,
      mul_assoc]
  calc fresnelOp w₁ (fresnelOp w₂ ψ)
      = 𝓕⁻ (𝓕 (fresnelOp w₁ (fresnelOp w₂ ψ))) := by
        rw [FourierTransform.fourierInv_fourier_eq]
    _ = 𝓕⁻ (𝓕 (fresnelOp (w₁ + w₂) ψ)) := by rw [h]
    _ = fresnelOp (w₁ + w₂) ψ := by rw [FourierTransform.fourierInv_fourier_eq]

theorem re_natCast_add_one_mul (n : ℕ) (w : ℂ) : (((n : ℂ) + 1) * w).re = (n + 1) * w.re := by
  have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]

/-- ★ **`n` equal slices compose**: iterating the complex-time operator `n+1` times is the operator
at `(n+1)w`. -/
theorem fresnelOp_iterate (hw : 0 < w.re) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    (fresnelOp w)^[n + 1] ψ = fresnelOp (((n : ℂ) + 1) * w) ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 < (((n : ℂ) + 1) * w).re := by
      rw [re_natCast_add_one_mul]
      positivity
    rw [Function.iterate_succ_apply', ih, fresnelOp_fresnelOp hw hn]
    congr 1
    push_cast
    ring_nf

theorem re_div_natCast_add_one (w : ℂ) (n : ℕ) :
    (w / ((n : ℂ) + 1)).re = w.re / (n + 1) := by
  have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.div_ofReal_re]

/-- ★★ **Every time-slicing is exact**: `n+1` slices of complex time `w/(n+1)` compose to the single
slice `w`. -/
theorem fresnelOp_iterate_div (hw : 0 < w.re) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    (fresnelOp (w / ((n : ℂ) + 1)))^[n + 1] ψ = fresnelOp w ψ := by
  have hre : 0 < (w / ((n : ℂ) + 1)).re := by
    rw [re_div_natCast_add_one]
    positivity
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  rw [fresnelOp_iterate hre n]
  congr 1
  field_simp

/-- ★ **The time-slicing recursion**: each slice is one kernel integral, so the `n+1`-slice operator
is an `n+1`-fold iterated kernel integral. -/
theorem fresnelOp_iterate_succ_apply (hw : 0 < w.re) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ((fresnelOp w)^[n + 1] ψ) x
      = ∫ y : ℝ, fresnelKernel w (x - y) * ((fresnelOp w)^[n] ψ) y := by
  rw [Function.iterate_succ_apply', fresnelOp_apply hw]

/-! ### The free propagator is the `ε ↓ 0` limit -/

/-- The real part of the regularised time `ε + it/2` is the regulariser (`simp` knows this; the
name is here because the positivity hypothesis is rewritten with it everywhere below). -/
theorem re_ofReal_add_I_mul (ε t : ℝ) : ((ε : ℂ) + Complex.I * t / 2).re = ε := by simp

theorem ofReal_add_I_mul_ne_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (ε : ℂ) + Complex.I * t / 2 ≠ 0 := by
  intro h
  have h0 : ((ε : ℂ) + Complex.I * t / 2).re = 0 := by rw [h]; simp
  rw [re_ofReal_add_I_mul] at h0
  exact absurd h0 (ne_of_gt hε)

/-- At purely imaginary time the multiplier **is** the free Schrödinger phase `e^{−2π²itξ²}`. -/
theorem fresnelSymbol_I_mul (t : ℝ) (ξ : ℝ) :
    fresnelSymbol (Complex.I * t / 2) ξ = phaseFun (freeSymbol (E := ℝ)) t ξ := by
  rw [fresnelSymbol, phaseFun, freeSymbol]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- The Fourier transform of the free propagator applied to a Schwartz function. -/
theorem fourier_freeSchrodingerS (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (freeSchrodingerS t ψ) ξ = fresnelSymbol (Complex.I * t / 2) ξ * 𝓕 ψ ξ := by
  rw [freeSchrodingerS, fourierGroupS, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_phaseFun hasTemperateGrowth_freeSymbol t), smul_eq_mul,
    fresnelSymbol_I_mul]

theorem freeSchrodingerS_apply_eq_integral (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    freeSchrodingerS t ψ x
      = ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (fresnelSymbol (Complex.I * t / 2) ξ * 𝓕 ψ ξ) := by
  rw [apply_eq_integral_fourier]
  exact integral_congr_ae (.of_forall fun ξ => by simp only [fourier_freeSchrodingerS])

theorem continuous_fourierChar_inner (x : ℝ) : Continuous fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ :=
  Real.continuous_fourierChar.comp (by fun_prop)

theorem continuous_ofReal_add_I_mul (t : ℝ) :
    Continuous fun ε : ℝ => ((ε : ℂ) + Complex.I * t / 2) := by fun_prop

theorem tendsto_ofReal_add_I_mul (t : ℝ) :
    Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I * t / 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.I * t / 2)) := by
  simpa using ((continuous_ofReal_add_I_mul t).tendsto 0).mono_left nhdsWithin_le_nhds

/-- ★★★ **The Gaussian-regularised Fresnel integral is the free propagator**: for Schwartz data,
`(U₀(t)ψ)(x) = lim_{ε ↓ 0} (e^{−(ε + it/2)H₀} ψ)(x)`, every term on the left an absolutely
convergent kernel integral. The proof is dominated convergence on the Fourier side: the multiplier
`e^{−4π²(ε + it/2)ξ²}` has modulus `≤ 1` and tends pointwise to the free phase, and `𝓕ψ` is
integrable. -/
theorem tendsto_fresnelOp (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => fresnelOp ((ε : ℂ) + Complex.I * t / 2) ψ x) (𝓝[>] 0)
      (𝓝 (freeSchrodingerS t ψ x)) := by
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (fresnelSymbol ((ε : ℂ) + Complex.I * t / 2) ξ * 𝓕 ψ ξ))
      volume := by
    intro ε
    refine Continuous.aestronglyMeasurable ?_
    refine (continuous_fourierChar_inner x).smul ?_
    exact (Complex.continuous_exp.comp (by fun_prop)).mul (𝓕 ψ).continuous
  have hlim : Tendsto (fun ε : ℝ =>
      ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (fresnelSymbol ((ε : ℂ) + Complex.I * t / 2) ξ * 𝓕 ψ ξ))
      (𝓝[>] (0 : ℝ)) (𝓝 (freeSchrodingerS t ψ x)) := by
    rw [freeSchrodingerS_apply_eq_integral t ψ x]
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖𝓕 ψ ξ‖)
      (Eventually.of_forall hmeas) ?_ (𝓕 ψ).integrable.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with ξ
      rw [Circle.norm_smul, norm_mul]
      calc ‖fresnelSymbol ((ε : ℂ) + Complex.I * t / 2) ξ‖ * ‖𝓕 ψ ξ‖
          ≤ 1 * ‖𝓕 ψ ξ‖ := by
            gcongr
            exact norm_fresnelSymbol_le_one (by simpa using (Set.mem_Ioi.1 hε).le) ξ
        _ = ‖𝓕 ψ ξ‖ := one_mul _
    · filter_upwards with ξ
      have hc : Continuous fun ε : ℝ =>
          𝐞 ⟪ξ, x⟫ • (fresnelSymbol ((ε : ℂ) + Complex.I * t / 2) ξ * 𝓕 ψ ξ) := by
        refine continuous_const.smul (Continuous.mul ?_ continuous_const)
        exact Complex.continuous_exp.comp (by fun_prop)
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (fresnelOp_apply_eq_integral_symbol (by simpa using Set.mem_Ioi.1 hε) ψ x).symm

/-- ★★★ The same limit as the kernel integral the physics writes:
`(U₀(t)ψ)(x) = lim_{ε ↓ 0} ∫ (4π(ε + it/2))^{−1/2} e^{−(x−y)²/(4(ε + it/2))} ψ(y) dy`. -/
theorem tendsto_integral_fresnelKernel_freeSchrodingerS (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y : ℝ, fresnelKernel ((ε : ℂ) + Complex.I * t / 2) (x - y) * ψ y)
      (𝓝[>] 0) (𝓝 (freeSchrodingerS t ψ x)) := by
  refine (tendsto_fresnelOp t ψ x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact fresnelOp_apply (by simpa using Set.mem_Ioi.1 hε) ψ x

/-- ★★ **Feynman's time-slicing, regularised**: for every number of slices the `n+1`-fold iterated
kernel integral has the same `ε ↓ 0` limit, the propagator. -/
theorem tendsto_fresnelOp_iterate (t : ℝ) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ =>
        ((fresnelOp (((ε : ℂ) + Complex.I * t / 2) / ((n : ℂ) + 1)))^[n + 1] ψ) x)
      (𝓝[>] 0) (𝓝 (freeSchrodingerS t ψ x)) := by
  refine (tendsto_fresnelOp t ψ x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [fresnelOp_iterate_div (by simpa using Set.mem_Ioi.1 hε)]

/-! ### Feynman's kernel -/

/-- ★ **Feynman's kernel**: at purely imaginary time `w = it/2` the complex-time kernel is
`(2πit)^{−1/2} e^{ix²/(2t)}`, the kernel of the path integral. -/
theorem fresnelKernel_I_mul (ht : t ≠ 0) (x : ℝ) :
    fresnelKernel (Complex.I * t / 2) x
      = (2 * (Real.pi : ℂ) * Complex.I * t) ^ (-(1 : ℂ) / 2)
        * Complex.exp (Complex.I * (x : ℂ) ^ 2 / (2 * t)) := by
  have ht' : ((t : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 ht
  rw [fresnelKernel, fresnelAmp]
  congr 2
  · ring
  · field_simp
    rw [Complex.I_sq]
    ring

/-- The Feynman kernel has constant modulus: it does not decay, which is why the Fresnel integral is
improper for general `L²` data — and why it is nevertheless absolutely convergent against the `L¹`
Schwartz functions used here. -/
theorem norm_fresnelKernel_I_mul (ht : t ≠ 0) (x : ℝ) :
    ‖fresnelKernel (Complex.I * t / 2) x‖ = ‖fresnelAmp (Complex.I * t / 2)‖ := by
  rw [fresnelKernel, norm_mul, Complex.norm_exp]
  have h : (-(x : ℂ) ^ 2 / (4 * (Complex.I * t / 2))).re = 0 := by
    have ht' : ((t : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 ht
    have hrw : -(x : ℂ) ^ 2 / (4 * (Complex.I * t / 2))
        = Complex.I * ((x ^ 2 / (2 * t) : ℝ) : ℂ) := by
      push_cast
      field_simp
      rw [Complex.I_sq]
      ring
    rw [hrw, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h]
  simp

/-- ★ **The Feynman integral converges absolutely** for Schwartz data: the kernel is bounded and `ψ`
is integrable. -/
theorem integrable_fresnelKernel_mul (ht : t ≠ 0) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun y : ℝ => fresnelKernel (Complex.I * t / 2) (x - y) * ψ y) := by
  have hb : ∀ y : ℝ, ‖fresnelKernel (Complex.I * t / 2) (x - y)‖
      ≤ ‖fresnelAmp (Complex.I * t / 2)‖ := fun y =>
    le_of_eq (norm_fresnelKernel_I_mul ht (x - y))
  have hmeas : AEStronglyMeasurable (fun y : ℝ => fresnelKernel (Complex.I * t / 2) (x - y))
      volume := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [fresnelKernel]
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  exact ψ.integrable.bdd_mul hmeas (Eventually.of_forall hb)

/-- The `ε ↓ 0` limit of the regularised kernel integrals is the Feynman integral: the amplitude
converges by continuity of the principal square root off the cut, and the Gaussian factor by
dominated convergence (its modulus is `≤ 1` for `Re w ≥ 0`). -/
theorem tendsto_integral_fresnelKernel (ht : t ≠ 0) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y : ℝ, fresnelKernel ((ε : ℂ) + Complex.I * t / 2) (x - y) * ψ y)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, fresnelKernel (Complex.I * t / 2) (x - y) * ψ y)) := by
  have hw0 : Complex.I * t / 2 ≠ 0 := by simp [Complex.ext_iff, ht]
  have hslit : 4 * (Real.pi : ℂ) * (Complex.I * t / 2) ∈ Complex.slitPlane := by
    refine Or.inr ?_
    have h : 4 * (Real.pi : ℂ) * (Complex.I * t / 2)
        = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    simpa using mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ht
  have hamp : Tendsto (fun ε : ℝ => fresnelAmp ((ε : ℂ) + Complex.I * t / 2)) (𝓝[>] 0)
      (𝓝 (fresnelAmp (Complex.I * t / 2))) := by
    simp only [fresnelAmp]
    exact Filter.Tendsto.cpow (tendsto_const_nhds.mul (tendsto_ofReal_add_I_mul t))
      tendsto_const_nhds hslit
  have hgauss : Tendsto
      (fun ε : ℝ => ∫ y : ℝ, Complex.exp (-((x - y : ℝ) : ℂ) ^ 2
          / (4 * ((ε : ℂ) + Complex.I * t / 2))) * ψ y) (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Complex.exp (-((x - y : ℝ) : ℂ) ^ 2 / (4 * (Complex.I * t / 2))) * ψ y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖ψ y‖) ?_ ?_
      ψ.integrable.norm ?_
    · filter_upwards with ε
      refine Continuous.aestronglyMeasurable ?_
      exact (Complex.continuous_exp.comp (by fun_prop)).mul ψ.continuous
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with y
      rw [norm_mul]
      calc ‖Complex.exp (-((x - y : ℝ) : ℂ) ^ 2 / (4 * ((ε : ℂ) + Complex.I * t / 2)))‖ * ‖ψ y‖
          ≤ 1 * ‖ψ y‖ := by
            gcongr
            exact norm_exp_fresnel_le_one (by simpa using (Set.mem_Ioi.1 hε).le)
              (ofReal_add_I_mul_ne_zero (Set.mem_Ioi.1 hε) t) _
        _ = ‖ψ y‖ := one_mul _
    · filter_upwards with y
      have hd : ContinuousAt (fun v : ℂ => Complex.exp (-((x - y : ℝ) : ℂ) ^ 2 / (4 * v)) * ψ y)
          (Complex.I * t / 2) := by
        refine ContinuousAt.mul ?_ continuousAt_const
        refine Complex.continuous_exp.continuousAt.comp ?_
        exact continuousAt_const.div (by fun_prop) (by simpa using hw0)
      exact hd.tendsto.comp (tendsto_ofReal_add_I_mul t)
  have hsplit : ∀ v : ℂ, (∫ y : ℝ, fresnelKernel v (x - y) * ψ y)
      = fresnelAmp v * ∫ y : ℝ, Complex.exp (-((x - y : ℝ) : ℂ) ^ 2 / (4 * v)) * ψ y := by
    intro v
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [fresnelKernel]
    ring
  simp only [hsplit]
  exact hamp.mul hgauss

/-- ★★★ **Feynman's kernel formula, exactly**: for Schwartz data and `t ≠ 0`,
`(U₀(t)ψ)(x) = (2πit)^{−1/2} ∫ e^{i(x−y)²/(2t)} ψ(y) dy`, an absolutely convergent integral — no
regularisation is left in the statement. The Gaussian regularisation proves it: the regularised
integrals converge to the propagator (`tendsto_fresnelOp`) and to this integral
(`tendsto_integral_fresnelKernel`), and limits in `ℂ` are unique. -/
theorem freeSchrodingerS_eq_integral_fresnel (ht : t ≠ 0) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    freeSchrodingerS t ψ x
      = (2 * (Real.pi : ℂ) * Complex.I * t) ^ (-(1 : ℂ) / 2)
        * ∫ y : ℝ, Complex.exp (Complex.I * ((x - y : ℝ) : ℂ) ^ 2 / (2 * t)) * ψ y := by
  have h := tendsto_nhds_unique (tendsto_integral_fresnelKernel_freeSchrodingerS t ψ x)
    (tendsto_integral_fresnelKernel ht ψ x)
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [fresnelKernel_I_mul ht]
  ring

/-- The free propagator is a one-parameter group on Schwartz functions. -/
theorem freeSchrodingerS_add (t₁ t₂ : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    freeSchrodingerS t₁ (freeSchrodingerS t₂ ψ) = freeSchrodingerS (t₁ + t₂) ψ := by
  have hmul : phaseFun (freeSymbol (E := ℝ)) t₁ * phaseFun (freeSymbol (E := ℝ)) t₂
      = phaseFun (freeSymbol (E := ℝ)) (t₁ + t₂) := by
    funext ξ
    rw [Pi.mul_apply, phaseFun, phaseFun, phaseFun, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [freeSchrodingerS, freeSchrodingerS, freeSchrodingerS, fourierGroupS, fourierGroupS,
    fourierGroupS, SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (hasTemperateGrowth_phaseFun hasTemperateGrowth_freeSymbol t₁)
      (hasTemperateGrowth_phaseFun hasTemperateGrowth_freeSymbol t₂), hmul]

theorem freeSchrodingerS_iterate_eq (s : ℝ) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    (freeSchrodingerS s)^[n + 1] ψ = freeSchrodingerS (((n : ℝ) + 1) * s) ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, freeSchrodingerS_add]
    congr 1
    push_cast
    ring_nf

/-- ★★ **The propagator is its own `n`-slice product**: `U₀(t) = (U₀(t/(n+1)))^{n+1}`, so the
`n`-slice iterated Feynman integral is exact for every `n`, not only in a limit. -/
theorem freeSchrodingerS_iterate (t : ℝ) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    (freeSchrodingerS (t / ((n : ℝ) + 1)))^[n + 1] ψ = freeSchrodingerS t ψ := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [freeSchrodingerS_iterate_eq]
  congr 1
  field_simp

/-! ### The discrete action -/

/-- The discrete action of a path `q : ℕ → ℝ` sampled at `n` steps of duration `t/n`:
`S_n = ∑_{k<n} (q_{k+1} − q_k)²/(2Δt)`, the Riemann sum of `∫ ½ q̇² ds` for the free Lagrangian. -/
noncomputable def discreteAction (t : ℝ) (n : ℕ) (q : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (q (k + 1) - q k) ^ 2 / (2 * (t / n))

/-- ★★★ **`e^{iS_n}` is the integrand**: the product of the `n` Feynman kernels that make up the
`n`-slice iterated integral is `((2πit/n)^{−1/2})^n e^{iS_n}`, with `S_n` the discrete action of the
sampled path. The phase of the path integral is a theorem, not a notation. -/
theorem prod_fresnelKernel_eq_exp_discreteAction (ht : t ≠ 0) (n : ℕ) (hn : n ≠ 0) (q : ℕ → ℝ) :
    ∏ k ∈ Finset.range n, fresnelKernel (Complex.I * ((t : ℂ) / n) / 2) (q (k + 1) - q k)
      = fresnelAmp (Complex.I * ((t : ℂ) / n) / 2) ^ n
        * Complex.exp (Complex.I * ((discreteAction t n q : ℝ) : ℂ)) := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have ht' : ((t : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 ht
  have hterm : ∀ k : ℕ, -((q (k + 1) - q k : ℝ) : ℂ) ^ 2 / (4 * (Complex.I * ((t : ℂ) / n) / 2))
      = Complex.I * (((q (k + 1) - q k) ^ 2 / (2 * (t / n)) : ℝ) : ℂ) := by
    intro k
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hsum : ∑ k ∈ Finset.range n,
      Complex.I * (((q (k + 1) - q k) ^ 2 / (2 * (t / n)) : ℝ) : ℂ)
      = Complex.I * ((discreteAction t n q : ℝ) : ℂ) := by
    rw [discreteAction, Complex.ofReal_sum, Finset.mul_sum]
  simp only [fresnelKernel, hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Complex.exp_sum, hsum]

end SchrodingerGroup
