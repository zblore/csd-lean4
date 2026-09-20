/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.SchrodingerSchwartz
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The free Gaussian packet

**Category:** 1-Mathlib (CSD-free; staged for upstream).

`Analysis/Semigroup/SchrodingerSchwartz.lean` puts the free Schrödinger group `U₀(t) = e^{−itH₀}`,
`H₀ = −½ d²/dx²`, on Schwartz space. This module (BACKLOG #48, FC-5‴) lets the reader see it act,
on the one initial state whose evolution is explicit — the Gaussian:

* **the Gaussian is a Schwartz function**: `gaussianS a ha : 𝓢(ℝ, ℂ)` is `x ↦ e^{−π a x²}` for
  `Re a > 0` (the pin has no Gaussian bundled as a `SchwartzMap`). Its `n`-th derivative is
  `P_n(x) e^{−π a x²}` with `P_{n+1} = P_n' − 2πa X P_n` (`iteratedDeriv_gaussFun`, `gaussPoly`),
  and `|x|^m e^{−c x²} ≤ 1 + m!/cᵐ` (`pow_mul_exp_neg_le`, from `x^m/m! ≤ eˣ`) gives the decay;
* **its Fourier transform** is the Gaussian `a^{−1/2} e^{−πξ²/a}` (`fourier_gaussianS`, Mathlib's
  `fourier_gaussian_pi` read as a Schwartz identity), and the free phase `e^{−2π²itξ²}` turns it
  into the Gaussian of the complex parameter `a⁻¹ + 2πit` (`smulLeft_phase_fourier_gaussianS`);
  the inverse transform of an even function is its transform (`fourierInv_gaussianS`);
* ★★ `freeSchrodingerS_gaussianS` — **the packet spreads**:
  `U₀(t) g_a = packetAmp a t • g_{a(t)}` with `a(t) = (a⁻¹ + 2πit)⁻¹ = a / (1 + 2πiat)`
  (`packetParam_eq`) and amplitude `(1 + 2πiat)^{−1/2}` (`packetAmp_eq`, after ★
  `mul_cpow_of_re_pos`: the principal square root is multiplicative on the right half-plane);
  ★ `freeSchrodinger_gaussianS_toLp` is the same in `L²`, through `freeSchrodinger_toLp`;
* ★ `re_packetParam_ofReal` — for a real width parameter `σ > 0` the density is
  `|U₀(t) g_σ|² = |amp|² e^{−2π σ(t) x²}` with `σ(t) = σ / (1 + (2πσt)²)` decreasing in `|t|`
  (`norm_freeSchrodingerS_gaussianS`): the Gaussian widens as `√(1 + (2πσt)²)`, the textbook
  spreading of a free wave packet (units `ℏ = m = 1`, Mathlib's Fourier convention).

## Honest scope

⚠️ One dimension only (`E = ℝ`); the `d`-dimensional Gaussian `e^{−πa‖x‖²}` follows the same
route through Mathlib's `fourier_gaussian_innerProductSpace` and is not done. The packet is centred
at the origin with zero mean momentum; the moving packet `e^{2πipx} g_a(x − q)` (Mathlib's
`fourier_gaussian_pi'` carries the shift) is not stated. No uncertainty product is computed.

References: M. Reed, B. Simon, *Methods of Modern Mathematical Physics* II §IX.7; A. Messiah,
*Quantum Mechanics* I ch. II §3 (the spreading of a free Gaussian packet);
`Analysis/Semigroup/SchrodingerSchwartz.lean` (FC-5″); `specs/feynman-continuum-scoping.md` §5;
`specs/BACKLOG.md` #48; `specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped Nat SchwartzMap FourierTransform ContDiff
open MeasureTheory Polynomial SchrodingerGroup

namespace SchrodingerGroup

/-! ### The Gaussian and its derivatives -/

/-- The Gaussian `x ↦ e^{−π a x²}` on `ℝ`, as a plain function. -/
noncomputable def gaussFun (a : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2)

/-- The polynomial factor of the `n`-th derivative of the Gaussian:
`P_0 = 1`, `P_{n+1} = P_n' − 2πa X P_n`. -/
noncomputable def gaussPoly (a : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => derivative (gaussPoly a n) - (2 * (Real.pi : ℂ) * a) • (X * gaussPoly a n)

theorem norm_gaussFun (a : ℂ) (x : ℝ) :
    ‖gaussFun a x‖ = Real.exp (-(Real.pi * a.re * x ^ 2)) := by
  rw [gaussFun, Complex.norm_exp]
  congr 1
  have h : (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2) = ((-(Real.pi * x ^ 2) : ℝ) : ℂ) * a := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

theorem contDiff_gaussFun (a : ℂ) : ContDiff ℝ ∞ (gaussFun a) :=
  Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.pow 2))

/-- The derivative of `P(x) e^{−π a x²}` is `(P' − 2πa X P)(x) e^{−π a x²}`. -/
theorem hasDerivAt_eval_mul_gaussFun (a : ℂ) (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (fun x : ℝ => p.eval (x : ℂ) * gaussFun a x)
      ((derivative p - (2 * (Real.pi : ℂ) * a) • (X * p)).eval (x : ℂ) * gaussFun a x) x := by
  have h2 : HasDerivAt (fun z : ℂ => -(Real.pi : ℂ) * a * z ^ 2)
      (-(Real.pi : ℂ) * a * (2 * (x : ℂ))) (x : ℂ) := by
    simpa using (hasDerivAt_pow 2 (x : ℂ)).const_mul (-(Real.pi : ℂ) * a)
  have h1 : HasDerivAt (fun z : ℂ => p.eval z * Complex.exp (-(Real.pi : ℂ) * a * z ^ 2))
      (p.derivative.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2)
        + p.eval (x : ℂ) * (Complex.exp (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2)
          * (-(Real.pi : ℂ) * a * (2 * (x : ℂ))))) (x : ℂ) :=
    (Polynomial.hasDerivAt p (x : ℂ)).mul ((Complex.hasDerivAt_exp _).comp (x : ℂ) h2)
  show HasDerivAt
    (fun x : ℝ => p.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2)) _ x
  refine h1.comp_ofReal.congr_deriv ?_
  simp only [gaussFun, eval_sub, eval_smul, eval_mul, eval_X, smul_eq_mul]
  ring

/-- The `n`-th derivative of the Gaussian is `P_n(x) e^{−π a x²}`. -/
theorem iteratedDeriv_gaussFun (a : ℂ) (n : ℕ) :
    iteratedDeriv n (gaussFun a) = fun x : ℝ => (gaussPoly a n).eval (x : ℂ) * gaussFun a x := by
  induction n with
  | zero =>
    funext x
    simp [gaussPoly]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [(hasDerivAt_eval_mul_gaussFun a (gaussPoly a n) x).deriv]
    rfl

/-- A polynomial is bounded by the sum of its coefficients' norms times the powers. -/
theorem norm_eval_le_sum (p : ℂ[X]) (z : ℂ) :
    ‖p.eval z‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ i := by
  rw [eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow]

/-- `|x|^m e^{−c x²} ≤ 1 + m!/cᵐ` for `c > 0`: from `y^m/m! ≤ e^y` at `y = c x²`. -/
theorem pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (m : ℕ) (x : ℝ) :
    |x| ^ m * Real.exp (-(c * x ^ 2)) ≤ 1 + m ! / c ^ m := by
  have hx2 : 0 ≤ c * x ^ 2 := by positivity
  have h1 : (c * x ^ 2) ^ m / m ! ≤ Real.exp (c * x ^ 2) := Real.pow_div_factorial_le_exp _ hx2 m
  have hexp : 0 < Real.exp (c * x ^ 2) := Real.exp_pos _
  rw [Real.exp_neg]
  have h2 : |x| ^ m ≤ 1 + (x ^ 2) ^ m := by
    rcases le_or_gt |x| 1 with h | h
    · calc |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
        _ ≤ 1 + (x ^ 2) ^ m := le_add_of_nonneg_right (by positivity)
    · calc |x| ^ m ≤ (|x| ^ 2) ^ m := by
            rw [← pow_mul]
            exact pow_le_pow_right₀ h.le (by omega)
        _ = (x ^ 2) ^ m := by rw [sq_abs]
        _ ≤ 1 + (x ^ 2) ^ m := le_add_of_nonneg_left zero_le_one
  have h3 : (x ^ 2) ^ m * (Real.exp (c * x ^ 2))⁻¹ ≤ m ! / c ^ m := by
    rw [mul_inv_le_iff₀ hexp, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc m)]
    calc (x ^ 2) ^ m * c ^ m = (c * x ^ 2) ^ m := by rw [mul_pow, mul_comm]
      _ ≤ m ! * Real.exp (c * x ^ 2) := by
          rw [div_le_iff₀ (by positivity)] at h1
          linarith
  calc |x| ^ m * (Real.exp (c * x ^ 2))⁻¹
      ≤ (1 + (x ^ 2) ^ m) * (Real.exp (c * x ^ 2))⁻¹ := by gcongr
    _ = (Real.exp (c * x ^ 2))⁻¹ + (x ^ 2) ^ m * (Real.exp (c * x ^ 2))⁻¹ := by ring
    _ ≤ 1 + m ! / c ^ m := by
        gcongr
        exact inv_le_one_of_one_le₀ (Real.one_le_exp hx2)

/-- The Schwartz decay of the Gaussian: every `|x|^k |∂ⁿ g|` is bounded. -/
theorem decay_gaussFun {a : ℂ} (ha : 0 < a.re) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussFun a) x‖ ≤ C := by
  have hc : 0 < Real.pi * a.re := mul_pos Real.pi_pos ha
  refine ⟨∑ i ∈ Finset.range ((gaussPoly a n).natDegree + 1),
    ‖(gaussPoly a n).coeff i‖ * (1 + (k + i)! / (Real.pi * a.re) ^ (k + i)), fun x => ?_⟩
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gaussFun, norm_mul,
    norm_gaussFun, Real.norm_eq_abs]
  calc |x| ^ k * (‖(gaussPoly a n).eval (x : ℂ)‖ * Real.exp (-(Real.pi * a.re * x ^ 2)))
      ≤ |x| ^ k * ((∑ i ∈ Finset.range ((gaussPoly a n).natDegree + 1),
          ‖(gaussPoly a n).coeff i‖ * ‖(x : ℂ)‖ ^ i) * Real.exp (-(Real.pi * a.re * x ^ 2))) := by
        gcongr
        exact norm_eval_le_sum _ _
    _ = ∑ i ∈ Finset.range ((gaussPoly a n).natDegree + 1),
          ‖(gaussPoly a n).coeff i‖ * (|x| ^ (k + i) * Real.exp (-(Real.pi * a.re * x ^ 2))) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, pow_add]
        ring
    _ ≤ ∑ i ∈ Finset.range ((gaussPoly a n).natDegree + 1),
          ‖(gaussPoly a n).coeff i‖ * (1 + (k + i)! / (Real.pi * a.re) ^ (k + i)) := by
        gcongr with i _
        exact pow_mul_exp_neg_le hc (k + i) x

/-- **The Gaussian `x ↦ e^{−π a x²}`, `Re a > 0`, as a Schwartz function on `ℝ`.** -/
noncomputable def gaussianS (a : ℂ) (ha : 0 < a.re) : 𝓢(ℝ, ℂ) where
  toFun := gaussFun a
  smooth' := contDiff_gaussFun a
  decay' := decay_gaussFun ha

theorem coe_gaussianS (a : ℂ) (ha : 0 < a.re) : ⇑(gaussianS a ha) = gaussFun a :=
  rfl

@[simp]
theorem gaussianS_apply (a : ℂ) (ha : 0 < a.re) (x : ℝ) :
    gaussianS a ha x = Complex.exp (-(Real.pi : ℂ) * a * (x : ℂ) ^ 2) :=
  rfl

theorem norm_gaussianS_apply (a : ℂ) (ha : 0 < a.re) (x : ℝ) :
    ‖gaussianS a ha x‖ = Real.exp (-(Real.pi * a.re * x ^ 2)) :=
  norm_gaussFun a x

/-! ### The Fourier transform and the free phase -/

/-- The Fourier transform of the Gaussian is the Gaussian `a^{−1/2} e^{−πξ²/a}`. -/
theorem fourier_gaussianS (a : ℂ) (ha : 0 < a.re) :
    ⇑(𝓕 (gaussianS a ha) : 𝓢(ℝ, ℂ))
      = fun ξ : ℝ => 1 / a ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / a * (ξ : ℂ) ^ 2) := by
  rw [SchwartzMap.fourier_coe, coe_gaussianS]
  exact fourier_gaussian_pi ha

theorem re_inv_pos {b : ℂ} (hb : 0 < b.re) : 0 < (b⁻¹).re := by
  rw [Complex.inv_re]
  exact div_pos hb (Complex.normSq_pos.2 fun h => by simp [h] at hb)

/-- The inverse Fourier transform of the (even) Gaussian is its Fourier transform. -/
theorem fourierInv_gaussianS (b : ℂ) (hb : 0 < b.re) :
    𝓕⁻ (gaussianS b hb) = (1 / b ^ (1 / 2 : ℂ)) • gaussianS b⁻¹ (re_inv_pos hb) := by
  ext ξ
  have h : 𝓕 (gaussFun b)
      = fun ξ : ℝ => 1 / b ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / b * (ξ : ℂ) ^ 2) :=
    fourier_gaussian_pi hb
  rw [SchwartzMap.fourierInv_coe, coe_gaussianS, Real.fourierInv_eq_fourier_neg, h, smul_apply,
    smul_eq_mul, gaussianS_apply]
  simp only [Complex.ofReal_neg, neg_sq, div_eq_mul_inv]

/-- The inverse width parameter `a⁻¹ + 2πit` of the packet at time `t` has positive real part. -/
theorem re_inv_add_pos {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    0 < (a⁻¹ + 2 * Real.pi * Complex.I * t).re := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I * t).re = 0 := by simp
  rw [Complex.add_re, h0, add_zero]
  exact re_inv_pos ha

/-- The free phase `e^{−2π²itξ²}` times the transform of `g_a` is the transform of the Gaussian of
parameter `a⁻¹ + 2πit`, up to the constant `a^{−1/2}`. -/
theorem smulLeft_phase_fourier_gaussianS (a : ℂ) (ha : 0 < a.re) (t : ℝ) :
    SchwartzMap.smulLeftCLM ℂ (phaseFun (freeSymbol (E := ℝ)) t) (𝓕 (gaussianS a ha))
      = (1 / a ^ (1 / 2 : ℂ)) •
          gaussianS (a⁻¹ + 2 * Real.pi * Complex.I * t) (re_inv_add_pos ha t) := by
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_phaseFun hasTemperateGrowth_freeSymbol t),
    smul_eq_mul, fourier_gaussianS, smul_apply, smul_eq_mul, gaussianS_apply, phaseFun,
    freeSymbol, Real.norm_eq_abs, sq_abs, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### The spreading packet -/

/-- The width parameter of the packet at time `t`: `a(t) = (a⁻¹ + 2πit)⁻¹ = a / (1 + 2πiat)`. -/
noncomputable def packetParam (a : ℂ) (t : ℝ) : ℂ :=
  (a⁻¹ + 2 * Real.pi * Complex.I * t)⁻¹

/-- The amplitude of the packet at time `t`: `a^{−1/2} (a⁻¹ + 2πit)^{−1/2} = (1 + 2πiat)^{−1/2}`. -/
noncomputable def packetAmp (a : ℂ) (t : ℝ) : ℂ :=
  1 / a ^ (1 / 2 : ℂ) * (1 / (a⁻¹ + 2 * Real.pi * Complex.I * t) ^ (1 / 2 : ℂ))

theorem re_packetParam_pos {a : ℂ} (ha : 0 < a.re) (t : ℝ) : 0 < (packetParam a t).re :=
  re_inv_pos (re_inv_add_pos ha t)

theorem one_add_mul_eq {a : ℂ} (ha : a ≠ 0) (t : ℝ) :
    1 + 2 * Real.pi * Complex.I * a * t = a * (a⁻¹ + 2 * Real.pi * Complex.I * t) := by
  rw [mul_add, mul_inv_cancel₀ ha]
  ring

theorem packetParam_eq {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    packetParam a t = a / (1 + 2 * Real.pi * Complex.I * a * t) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [packetParam, one_add_mul_eq ha0, div_mul_cancel_left₀ ha0]

/-- ★ The principal power is multiplicative on the right half-plane. -/
theorem mul_cpow_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (r : ℂ) :
    (x * y) ^ r = x ^ r * y ^ r := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hlog : Complex.log (x * y) = Complex.log x + Complex.log y := by
    apply Complex.ext
    · simp only [Complex.log_re, Complex.add_re, norm_mul]
      exact Real.log_mul (norm_ne_zero_iff.2 hx0) (norm_ne_zero_iff.2 hy0)
    · simp only [Complex.log_im, Complex.add_im]
      refine Complex.arg_mul hx0 hy0 ?_
      have h1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)
      have h2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hy)
      rw [abs_lt] at h1 h2
      exact Set.mem_Ioc.2 ⟨by linarith, by linarith⟩
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx0 hy0), Complex.cpow_def_of_ne_zero hx0,
    Complex.cpow_def_of_ne_zero hy0, hlog, add_mul, Complex.exp_add]

/-- The amplitude in closed form: `(1 + 2πiat)^{−1/2}`. -/
theorem packetAmp_eq {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    packetAmp a t = 1 / (1 + 2 * Real.pi * Complex.I * a * t) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [packetAmp, one_add_mul_eq ha0, mul_cpow_of_re_pos ha (re_inv_add_pos ha t),
    one_div_mul_one_div]

/-- ★★ **The free Gaussian packet spreads**: `U₀(t) g_a = packetAmp a t • g_{a(t)}` with
`a(t) = (a⁻¹ + 2πit)⁻¹`. The Fourier transform of `g_a` is a Gaussian, the free phase multiplies
its exponent by `2πit`, and the inverse transform is a Gaussian again. -/
theorem freeSchrodingerS_gaussianS (a : ℂ) (ha : 0 < a.re) (t : ℝ) :
    freeSchrodingerS (E := ℝ) t (gaussianS a ha)
      = packetAmp a t • gaussianS (packetParam a t) (re_packetParam_pos ha t) := by
  rw [freeSchrodingerS, fourierGroupS, SchwartzMap.fourierMultiplierCLM_apply,
    smulLeft_phase_fourier_gaussianS a ha t, FourierTransform.fourierInv_smul,
    fourierInv_gaussianS, smul_smul]
  rfl

/-- ★ The same in `L²`: the free Schrödinger group of `SchrodingerGroup.lean` sends the Gaussian
to the spread Gaussian. -/
theorem freeSchrodinger_gaussianS_toLp (a : ℂ) (ha : 0 < a.re) (t : ℝ) :
    freeSchrodinger (E := ℝ) t ((gaussianS a ha).toLp 2)
      = (packetAmp a t • gaussianS (packetParam a t) (re_packetParam_pos ha t)).toLp 2 := by
  rw [freeSchrodinger_toLp, freeSchrodingerS_gaussianS]

/-- The modulus of the spread packet is a real Gaussian of parameter `Re a(t)`. -/
theorem norm_freeSchrodingerS_gaussianS (a : ℂ) (ha : 0 < a.re) (t x : ℝ) :
    ‖freeSchrodingerS (E := ℝ) t (gaussianS a ha) x‖
      = ‖packetAmp a t‖ * Real.exp (-(Real.pi * (packetParam a t).re * x ^ 2)) := by
  rw [freeSchrodingerS_gaussianS, smul_apply, norm_smul, norm_gaussianS_apply]

/-- ★ For a real width parameter `σ > 0`, `Re a(t) = σ / (1 + (2πσt)²)`: the density
`e^{−2π Re a(t) x²}` widens with `|t|`. -/
theorem re_packetParam_ofReal {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (packetParam σ t).re = σ / (1 + (2 * Real.pi * σ * t) ^ 2) := by
  have hre : ((σ : ℂ)⁻¹ + 2 * Real.pi * Complex.I * t).re = σ⁻¹ := by
    rw [← Complex.ofReal_inv]
    simp
  have him : ((σ : ℂ)⁻¹ + 2 * Real.pi * Complex.I * t).im = 2 * Real.pi * t := by
    rw [← Complex.ofReal_inv]
    simp
  rw [packetParam, Complex.inv_re, Complex.normSq_apply, hre, him]
  field_simp

end SchrodingerGroup
