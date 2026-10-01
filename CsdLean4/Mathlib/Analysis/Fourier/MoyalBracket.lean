/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WignerCalculus

/-!
# The Moyal bracket of a potential, and the classical limit

**Category:** 1-Mathlib (staged for upstream). BACKLOG #64.

For `H(x, ξ) = 2π²ξ² + V(x)` the Wigner function obeys
`∂_t W = −2πξ ∂_x W + (the potential term)`. The kinetic half is **exactly** classical and is already
proved, as a flow rather than as a PDE: ★★ `wigner_freeSchrodingerS` of
[`Wigner.lean`](Wigner.lean) says the free evolution moves `W` along `x ↦ x − 2πtξ`, with no quantum
correction at all. This file does the potential half, where the correction lives.

* `wignerKernel₂`, `wigner₂` — the **cross** Wigner function, of which `wigner` is the diagonal
  case (`wignerKernel₂_self`);
* `moyalPot V ψ` — **the potential term**, the Wigner transform of `−i[V, ·]` on the kernel, with
  ★★★ `moyalPot_eq_comm` identifying it with `−i` times a difference of cross Wigner functions — so
  the integral against the *symmetric difference* `V(x + y/2) − V(x − y/2)` really is the commutator;
* ★★ `deriv_wigner_right` — the `ξ`-derivative of `W` brings the factor `−2πiy` into the integral,
  which is what turns the leading Taylor term of the symmetric difference into a Poisson bracket;
* ★★ `norm_symmDiff_sub_le` — **`|V(x+h) − V(x−h) − 2hV'(x)| ≤ Ch³/3` when `|V'''| ≤ C`**, by
  three integrations by parts of the symmetric differences; `norm_symmDiff_sub_le'` is the
  either-sign form;
* ★★★ `norm_moyalPot_sub_poisson_le` — **the classical limit with its remainder**:
  `‖moyalPot V ψ (x, ξ) − (1/2π) V'(x) ∂_ξ W‖ ≤ (sup|V'''|/24) ∫ |y|³ |K_ψ(x, y)| dy`. The constant
  `1/24` is the textbook one, and in the scaling `ξ = p/2πℏ` the third moment carries the `ℏ²`: this
  is `{H, W}_M = {H, W} + O(ℏ²)` for the potential term;
* ★★★ `moyalPot_eq_poisson_of_third_deriv_zero` — **and when `V''' = 0` the two brackets are equal.**
  Linear and quadratic potentials — the uniform force and the harmonic oscillator — evolve their
  Wigner functions exactly classically, which with the free case covers the whole exactly-classical
  family.

## Honest scope

⚠️ **This is the generator, not the evolution.** `moyalPot` is the potential term of the Wigner
equation, and the theorems compare it with the Poisson bracket pointwise in `(x, ξ)`. What is **not**
proved is the time-dependent statement `∂_t W_{U_V(t)ψ} = − 2πξ ∂_x W + moyalPot V ψ`: the corpus's
propagator for `H₀ + V` is a Trotter limit on `L²`
([`Semigroup/BoundedPerturbation.lean`](../Semigroup/BoundedPerturbation.lean)), with no
differentiability in `t` on Schwartz functions, and differentiating `W` in `x` would need
differentiation under the Fourier integral in the *parameter*, which the pin does not have in usable
form. `specs/BACKLOG.md` #64 carries that part with this measurement.

⚠️ **`ℏ` is not a variable here.** The convention is the one of `Wigner.lean`
(`𝓕 f ξ = ∫ e^{−2πiyξ} f y dy`, momentum `p = 2πξ`, so `ℏ = 1`). The `ℏ²` of the row is the third
moment `∫ |y|³ |K|` under `ξ = p/2πℏ`; no `ℏ`-indexed family of transforms is defined, so the
`ℏ → 0` statement is the remainder bound read in that scaling, not a limit theorem about a family.

⚠️ One dimension; `V` real, three times differentiable with bounded third derivative. The commutator
form `moyalPot_eq_comm` additionally needs `V` of temperate growth, so that `Vψ` is Schwartz; the
remainder bound does not.

References: J. E. Moyal, *Quantum mechanics as a statistical theory*, Proc. Cambridge Philos. Soc. 45
(1949) 99 §7 (the bracket and its `ℏ²` term); M. Hillery, R. F. O'Connell, M. O. Scully,
E. P. Wigner, *Distribution functions in physics: fundamentals*, Phys. Rep. 106 (1984) 121 §3.2;
`specs/BACKLOG.md` #64; #45; #63.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate LineDeriv

noncomputable section

namespace WignerFunction

/-! ### The symmetric difference of a potential is cubic in the step -/

section Taylor

variable {V V' V'' V''' : ℝ → ℝ} {C : ℝ}
  (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
  (hV'' : ∀ x, HasDerivAt V'' (V''' x) x) (hV''' : Continuous V''')
  (hC : ∀ x, ‖V''' x‖ ≤ C)

include hV'' hV''' hC in
/-- The symmetric difference of `V''` is linear in the step. -/
theorem norm_symmDiff_V''_le (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖V'' (x + u) - V'' (x - u)‖ ≤ 2 * C * u := by
  have hle : x - u ≤ x + u := by linarith
  have heq : V'' (x + u) - V'' (x - u) = ∫ v in (x - u)..(x + u), V''' v :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hV'' v)
      (hV'''.intervalIntegrable _ _)).symm
  rw [heq]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun v _ => hC v)).trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + u - (x - u))]
  ring_nf
  linarith

include hV' hV'' hV''' hC in
/-- The symmetric second difference of `V'` is quadratic in the step. -/
theorem norm_symmDiff_V'_le (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ‖V' (x + s) + V' (x - s) - 2 * V' x‖ ≤ C * s ^ 2 := by
  have hV''c : Continuous V'' := continuous_iff_continuousAt.2 fun y => (hV'' y).continuousAt
  have hd : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun t : ℝ => V' (x + t) + V' (x - t) - 2 * V' x)
        (V'' (x + u) - V'' (x - u)) u := by
    intro u _
    have ha : HasDerivAt (fun t : ℝ => V' (x + t)) (V'' (x + u)) u :=
      (hV' (x + u)).comp_const_add x u
    have hb : HasDerivAt (fun t : ℝ => V' (x - t)) (-V'' (x - u)) u :=
      (hV' (x - u)).comp_const_sub x u
    exact ((ha.add hb).sub_const (2 * V' x)).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun u => V'' (x + u) - V'' (x - u)) volume 0 s :=
    ((hV''c.comp (continuous_const.add continuous_id)).sub
      (hV''c.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have heq : V' (x + s) + V' (x - s) - 2 * V' x
      = ∫ u in (0 : ℝ)..s, (V'' (x + u) - V'' (x - u)) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simp only [add_zero, sub_zero] at h
    rw [h]
    ring
  rw [heq]
  have hbd : ∀ u ∈ Set.Ioc (0 : ℝ) s, ‖V'' (x + u) - V'' (x - u)‖ ≤ 2 * C * u := fun u hu =>
    norm_symmDiff_V''_le hV'' hV''' hC x hu.1.le
  refine (intervalIntegral.norm_integral_le_of_norm_le hs
    (Filter.Eventually.of_forall hbd) ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    ).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num
  exact le_of_eq (by ring)

include hV hV' hV'' hV''' hC in
/-- ★★ **The odd symmetric difference of a potential is cubic in the step**:
`|V(x+h) − V(x−h) − 2hV'(x)| ≤ C h³/3` when `|V'''| ≤ C`. This is the Taylor estimate the Moyal
remainder is made of. It is proved by hand because the pin's `taylor_mean_remainder_lagrange`
expands about one endpoint of an interval, while the cancellation here is between the two sides of a
point — the zeroth, first and second order terms cancel pairwise — so a one-sided expansion does not
exhibit it. -/
theorem norm_symmDiff_sub_le (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖V (x + h) - V (x - h) - 2 * h * V' x‖ ≤ C * h ^ 3 / 3 := by
  have hV'c : Continuous V' := continuous_iff_continuousAt.2 fun y => (hV' y).continuousAt
  have hd : ∀ u ∈ Set.uIcc (0 : ℝ) h,
      HasDerivAt (fun t : ℝ => V (x + t) - V (x - t) - 2 * t * V' x)
        (V' (x + u) + V' (x - u) - 2 * V' x) u := by
    intro u _
    have ha : HasDerivAt (fun t : ℝ => V (x + t)) (V' (x + u)) u :=
      (hV (x + u)).comp_const_add x u
    have hb : HasDerivAt (fun t : ℝ => V (x - t)) (-V' (x - u)) u :=
      (hV (x - u)).comp_const_sub x u
    have hc : HasDerivAt (fun t : ℝ => 2 * t * V' x) (2 * V' x) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 : ℝ)).mul_const (V' x)
    exact ((ha.sub hb).sub hc).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun u => V' (x + u) + V' (x - u) - 2 * V' x) volume 0 h :=
    (((hV'c.comp (continuous_const.add continuous_id)).add
      (hV'c.comp (continuous_const.sub continuous_id))).sub
        continuous_const).intervalIntegrable _ _
  have heq : V (x + h) - V (x - h) - 2 * h * V' x
      = ∫ u in (0 : ℝ)..h, (V' (x + u) + V' (x - u) - 2 * V' x) := by
    have hh' := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simp only [add_zero, sub_zero] at hh'
    rw [hh']
    ring
  rw [heq]
  have hbd : ∀ u ∈ Set.Ioc (0 : ℝ) h, ‖V' (x + u) + V' (x - u) - 2 * V' x‖ ≤ C * u ^ 2 :=
    fun u hu => norm_symmDiff_V'_le hV' hV'' hV''' hC x hu.1.le
  refine (intervalIntegral.norm_integral_le_of_norm_le hh
    (Filter.Eventually.of_forall hbd)
    ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num [mul_div_assoc]

end Taylor

/-! ### The cross Wigner function -/

/-- The Fourier transform of a Schwartz function, written as the integral this file uses. -/
theorem fourier_eq_integral (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 g ξ = ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * g y := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp only [Circle.smul_def, smul_eq_mul]

/-- The **cross** Wigner kernel `φ(x + y/2) conj (ψ(x − y/2))`, of which `wignerKernel` is the
diagonal case. -/
noncomputable def wignerKernel₂ (φ ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  mulConj (affineCLM x half_ne_zero' φ) (affineCLM x neg_half_ne_zero' ψ)

@[simp]
theorem wignerKernel₂_apply (φ ψ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    wignerKernel₂ φ ψ x y = φ (x + y / 2) * conj (ψ (x - y / 2)) := by
  rw [wignerKernel₂, mulConj_apply, affineCLM_apply, affineCLM_apply,
    show x + 1 / 2 * y = x + y / 2 by ring, show x + -1 / 2 * y = x - y / 2 by ring]

theorem wignerKernel₂_self (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : wignerKernel₂ ψ ψ x = wignerKernel ψ x := by
  ext y
  rw [wignerKernel₂_apply, wignerKernel_apply]

/-- The cross Wigner function. -/
noncomputable def wigner₂ (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : ℂ := 𝓕 (wignerKernel₂ φ ψ x) ξ

theorem wigner₂_eq_integral (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wigner₂ φ ψ x ξ = ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (φ (x + y / 2) * conj (ψ (x - y / 2))) := by
  rw [wigner₂, fourier_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [wignerKernel₂_apply]

/-! ### The potential term of the Wigner evolution equation -/

/-- Multiplication by a real potential, on Schwartz space. -/
noncomputable def mulPot (V : ℝ → ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ fun x => (V x : ℂ)

theorem mulPot_apply {V : ℝ → ℝ} (hV : Function.HasTemperateGrowth fun x => (V x : ℂ))
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : mulPot V ψ x = (V x : ℂ) * ψ x := by
  rw [mulPot, SchwartzMap.smulLeftCLM_apply_apply hV, smul_eq_mul]

/-- **The potential term of the Wigner (Moyal) evolution equation**: the Wigner transform of
`−i[V, ·]` applied to the kernel. For `H = 2π²ξ² + V` the Wigner function obeys
`∂_t W = −2πξ ∂_x W + moyalPot V ψ`, the first term being the free transport of
`wigner_freeSchrodingerS`. -/
noncomputable def moyalPot (V : ℝ → ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : ℂ :=
  ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ)
    * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y)

theorem integrable_char_mul (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    Integrable fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ) * g y := by
  refine (g.integrable (μ := volume)).norm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).mul
      g.continuous |>.aestronglyMeasurable
  · rw [norm_mul, Circle.norm_coe, one_mul]

/-- ★★★ **The potential term is the Wigner transform of the commutator.** `moyalPot` is defined as
an integral against the symmetric difference of `V`; this identifies it with `−i` times the
difference of two cross Wigner functions, which is the Wigner transform of `−i[V, ρ]`. -/
theorem moyalPot_eq_comm {V : ℝ → ℝ} (hV : Function.HasTemperateGrowth fun x => (V x : ℂ))
    (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    moyalPot V ψ x ξ
      = -Complex.I * (wigner₂ (mulPot V ψ) ψ x ξ - wigner₂ ψ (mulPot V ψ) x ξ) := by
  have h1 := integrable_char_mul (wignerKernel₂ (mulPot V ψ) ψ x) ξ
  have h2 := integrable_char_mul (wignerKernel₂ ψ (mulPot V ψ) x) ξ
  rw [wigner₂, wigner₂, fourier_eq_integral, fourier_eq_integral, ← integral_sub h1 h2,
    ← integral_const_mul, moyalPot]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hpt : mulPot V ψ (x + y / 2) * conj (ψ (x - y / 2))
      - ψ (x + y / 2) * conj (mulPot V ψ (x - y / 2))
      = ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y := by
    rw [mulPot_apply hV, mulPot_apply hV, wignerKernel_apply, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  show (𝐞 (-(y * ξ)) : ℂ)
        * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y)
      = -Complex.I * ((𝐞 (-(y * ξ)) : ℂ) * wignerKernel₂ (mulPot V ψ) ψ x y
          - (𝐞 (-(y * ξ)) : ℂ) * wignerKernel₂ ψ (mulPot V ψ) x y)
  rw [wignerKernel₂_apply, wignerKernel₂_apply]
  linear_combination (Complex.I * ((𝐞 (-(y * ξ)) : ℂ))) * hpt

/-! ### The `ξ`-derivative, and the classical limit -/

/-- ★★ The `ξ`-derivative of the Wigner function brings the factor `−2πiy` into the integral. -/
theorem deriv_wigner_right (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    deriv (fun ξ : ℝ => wigner ψ x ξ) ξ
      = ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (-(2 * π * Complex.I) * y * wignerKernel ψ x y) := by
  have hg : Function.HasTemperateGrowth fun y : ℝ => (inner ℝ y (1 : ℝ) : ℝ) :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  have h1 : deriv (fun ξ : ℝ => wigner ψ x ξ) ξ = (∂_{(1 : ℝ)} (𝓕 (wignerKernel ψ x))) ξ := by
    rw [lineDerivOp_one, SchwartzMap.derivCLM_apply]
    rfl
  rw [h1, SchwartzMap.lineDerivOp_fourier_eq, fourier_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, Complex.real_smul, smul_eq_mul]
  have hinner : (inner ℝ y (1 : ℝ) : ℝ) = y := by simp
  rw [hinner]
  ring

/-- The bound on the symmetric difference, for either sign of the step. -/
theorem norm_symmDiff_sub_le' {V V' V'' V''' : ℝ → ℝ} {C : ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV'' : ∀ x, HasDerivAt V'' (V''' x) x) (hV''' : Continuous V''')
    (hC : ∀ x, ‖V''' x‖ ≤ C) (x y : ℝ) :
    ‖V (x + y / 2) - V (x - y / 2) - y * V' x‖ ≤ C / 24 * |y| ^ 3 := by
  rcases le_total 0 y with hy | hy
  · have h := norm_symmDiff_sub_le hV hV' hV'' hV''' hC x (h := y / 2) (by linarith)
    rw [abs_of_nonneg hy]
    calc ‖V (x + y / 2) - V (x - y / 2) - y * V' x‖
        = ‖V (x + y / 2) - V (x - y / 2) - 2 * (y / 2) * V' x‖ := by ring_nf
      _ ≤ C * (y / 2) ^ 3 / 3 := h
      _ = C / 24 * y ^ 3 := by ring
  · have h := norm_symmDiff_sub_le hV hV' hV'' hV''' hC x (h := -(y / 2)) (by linarith)
    rw [abs_of_nonpos hy]
    calc ‖V (x + y / 2) - V (x - y / 2) - y * V' x‖
        = ‖V (x + -(y / 2)) - V (x - -(y / 2)) - 2 * -(y / 2) * V' x‖ := by
          rw [← norm_neg]
          ring_nf
      _ ≤ C * (-(y / 2)) ^ 3 / 3 := h
      _ = C / 24 * (-y) ^ 3 := by ring

/-! ### The classical limit -/

section Classical

variable {V V' V'' V''' : ℝ → ℝ} {C : ℝ}
  (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
  (hV'' : ∀ x, HasDerivAt V'' (V''' x) x) (hV''' : Continuous V''')
  (hC : ∀ x, ‖V''' x‖ ≤ C)

include hV in
theorem continuous_potential : Continuous V :=
  continuous_iff_continuousAt.2 fun y => (hV y).continuousAt

include hV hV' hV'' hV''' hC in
/-- The Moyal integrand is integrable: the symmetric difference of `V` grows at most like `|y|³`
against a Schwartz kernel. -/
theorem integrable_moyalPot_integrand (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    Integrable fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)
      * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y) := by
  have hVc : Continuous V := continuous_potential hV
  have hm1 : Integrable fun y : ℝ => |y| ^ 1 * ‖wignerKernel ψ x y‖ := by
    simpa [Real.norm_eq_abs] using (wignerKernel ψ x).integrable_pow_mul (μ := volume) 1
  have hm3 : Integrable fun y : ℝ => |y| ^ 3 * ‖wignerKernel ψ x y‖ := by
    simpa [Real.norm_eq_abs] using (wignerKernel ψ x).integrable_pow_mul (μ := volume) 3
  have hmaj : Integrable fun y : ℝ =>
      |V' x| * (|y| ^ 1 * ‖wignerKernel ψ x y‖) + C / 24 * (|y| ^ 3 * ‖wignerKernel ψ x y‖) :=
    (hm1.const_mul _).add (hm3.const_mul _)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp
        ((hVc.comp (by fun_prop)).sub (hVc.comp (by fun_prop))))).mul
        (wignerKernel ψ x).continuous)).aestronglyMeasurable
  · have hbound := norm_symmDiff_sub_le' hV hV' hV'' hV''' hC x y
    have hsplit : ‖((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ)‖
        ≤ |V' x| * |y| + C / 24 * |y| ^ 3 := by
      have h1 : ‖((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ)‖
          ≤ ‖((V (x + y / 2) - V (x - y / 2) - y * V' x : ℝ) : ℂ)‖
            + ‖((y * V' x : ℝ) : ℂ)‖ := by
        have := norm_add_le (((V (x + y / 2) - V (x - y / 2) - y * V' x : ℝ) : ℂ))
          (((y * V' x : ℝ) : ℂ))
        refine le_trans (le_of_eq ?_) this
        push_cast
        ring_nf
      refine h1.trans ?_
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have h2 : |V (x + y / 2) - V (x - y / 2) - y * V' x| ≤ C / 24 * |y| ^ 3 := by
        simpa [Real.norm_eq_abs] using hbound
      nlinarith [abs_nonneg y, abs_nonneg (V' x)]
    rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hKnn : (0 : ℝ) ≤ ‖wignerKernel ψ x y‖ := norm_nonneg _
    calc ‖((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ)‖ * ‖wignerKernel ψ x y‖
        ≤ (|V' x| * |y| + C / 24 * |y| ^ 3) * ‖wignerKernel ψ x y‖ :=
          mul_le_mul_of_nonneg_right hsplit hKnn
      _ = |V' x| * (|y| ^ 1 * ‖wignerKernel ψ x y‖)
            + C / 24 * (|y| ^ 3 * ‖wignerKernel ψ x y‖) := by ring

/-- The Poisson-bracket term, written as the same kind of integral. -/
theorem poisson_eq_integral (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    (1 / (2 * π) : ℂ) * (V' x : ℂ) * deriv (fun ξ : ℝ => wigner ψ x ξ) ξ
      = ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ)
          * (-Complex.I * ((y * V' x : ℝ) : ℂ) * wignerKernel ψ x y) := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [deriv_wigner_right, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  field_simp

theorem integrable_poisson_integrand (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    Integrable fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)
      * (-Complex.I * ((y * V' x : ℝ) : ℂ) * wignerKernel ψ x y) := by
  have hm1 : Integrable fun y : ℝ => |V' x| * (|y| ^ 1 * ‖wignerKernel ψ x y‖) := by
    refine Integrable.const_mul ?_ _
    simpa [Real.norm_eq_abs] using (wignerKernel ψ x).integrable_pow_mul (μ := volume) 1
  refine hm1.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const))).mul
        (wignerKernel ψ x).continuous)).aestronglyMeasurable
  · rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hKnn : (0 : ℝ) ≤ ‖wignerKernel ψ x y‖ := norm_nonneg _
    calc |y| * |V' x| * ‖wignerKernel ψ x y‖
        = |V' x| * (|y| ^ 1 * ‖wignerKernel ψ x y‖) := by ring
      _ ≤ |V' x| * (|y| ^ 1 * ‖wignerKernel ψ x y‖) := le_refl _

include hV hV' hV'' hV''' hC in
/-- ★★★ **The classical limit of the Moyal bracket, with its remainder.** The potential term of the
Wigner evolution differs from the Poisson-bracket term `(1/2π) V'(x) ∂_ξ W` by at most
`(sup |V'''| / 24) · ∫ |y|³ |K_ψ(x, y)| dy`. In the scaling `ξ = p/2πℏ` the third moment carries
`ℏ²`, so this is the `ℏ²` remainder of the Moyal series: **the Moyal bracket is the Poisson bracket
up to the third derivative of the potential.** -/
theorem norm_moyalPot_sub_poisson_le (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    ‖moyalPot V ψ x ξ - (1 / (2 * π) : ℂ) * (V' x : ℂ)
        * deriv (fun ξ : ℝ => wigner ψ x ξ) ξ‖
      ≤ C / 24 * ∫ y : ℝ, |y| ^ 3 * ‖wignerKernel ψ x y‖ := by
  have hm3 : Integrable fun y : ℝ => |y| ^ 3 * ‖wignerKernel ψ x y‖ := by
    simpa [Real.norm_eq_abs] using (wignerKernel ψ x).integrable_pow_mul (μ := volume) 3
  rw [moyalPot, poisson_eq_integral (V' := V') ψ x ξ,
    ← integral_sub (integrable_moyalPot_integrand hV hV' hV'' hV''' hC ψ x ξ)
      (integrable_poisson_integrand (V' := V') ψ x ξ)]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (hm3.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  have hpt : (𝐞 (-(y * ξ)) : ℂ)
        * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y)
      - (𝐞 (-(y * ξ)) : ℂ) * (-Complex.I * ((y * V' x : ℝ) : ℂ) * wignerKernel ψ x y)
      = (𝐞 (-(y * ξ)) : ℂ) * (-Complex.I
          * ((V (x + y / 2) - V (x - y / 2) - y * V' x : ℝ) : ℂ) * wignerKernel ψ x y) := by
    push_cast
    ring
  simp only [hpt]
  rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hbound : |V (x + y / 2) - V (x - y / 2) - y * V' x| ≤ C / 24 * |y| ^ 3 := by
    simpa [Real.norm_eq_abs] using norm_symmDiff_sub_le' hV hV' hV'' hV''' hC x y
  calc |V (x + y / 2) - V (x - y / 2) - y * V' x| * ‖wignerKernel ψ x y‖
      ≤ (C / 24 * |y| ^ 3) * ‖wignerKernel ψ x y‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = C / 24 * (|y| ^ 3 * ‖wignerKernel ψ x y‖) := by ring

include hV hV' hV'' hV''' in
/-- ★★★ **For a potential with vanishing third derivative the Moyal bracket *is* the Poisson
bracket.** Linear and quadratic potentials — the free particle, the uniform force, the harmonic
oscillator — have exactly classical phase-space evolution, which is the companion of
`wigner_freeSchrodingerS` for the potential term. -/
theorem moyalPot_eq_poisson_of_third_deriv_zero (hV0 : ∀ x, V''' x = 0) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    moyalPot V ψ x ξ
      = (1 / (2 * π) : ℂ) * (V' x : ℂ) * deriv (fun ξ : ℝ => wigner ψ x ξ) ξ := by
  have hC : ∀ x, ‖V''' x‖ ≤ 0 := fun x => by rw [hV0 x]; simp
  have h := norm_moyalPot_sub_poisson_le hV hV' hV'' hV''' hC ψ x ξ
  rw [zero_div, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

end Classical

end WignerFunction

end

end
