/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WignerWeyl

/-!
# The Weyl calculus: phase space as a measure space, and the temperate symbols

**Category:** 1-Mathlib (staged for upstream). BACKLOG #92, the residue of #63.

[`WignerWeyl.lean`](WignerWeyl.lean) proves the overlap identity and the Weyl expectation formula as
**iterated** integrals, for symbols with Schwartz slices. This file supplies the two things that were
missing from that picture: the Wigner function as a function **on the plane** rather than a family of
slices, and the three symbols of **temperate growth** whose quantisations are the position, momentum
and symmetrised-product operators.

## Phase space as a measure space

* ★ `stronglyMeasurable_wigner` — `(x, ξ) ↦ W_ψ(x, ξ)` is jointly measurable;
* `wignerEnergy ψ x = ∫ |W_ψ(x, ξ)|² dξ`, with ★★ `integrable_wignerEnergy` — the energy is
  integrable in the position, because slicewise Plancherel turns it into a convolution of two `L¹`
  functions read at `2x`;
* ★★ `integrable_normSq_wigner_prod` — **`W_ψ` is square-integrable on the plane**;
* ★★★ `integrable_wigner_mul_conj` — **the overlap integrand is integrable on the plane**, by
  `|ab| ≤ (|a|² + |b|²)/2`, and hence
* ★★★ `integral_prod_wigner_mul_conj` — **the overlap identity against the product measure**:
  `∫_{ℝ²} W_φ conj W_ψ = |⟨φ, ψ⟩|²`, with ★★ `integral_prod_wigner_sq` the purity form. This is what
  makes phase space a measure space for the state rather than a family of one-dimensional slices.

## The three temperate symbols

`weylOp` of `WignerWeyl.lean` needs symbol slices dominated by an integrable function, which excludes
`a(x, ξ) = x`, `ξ` and `xξ`. Their content is nevertheless available as moment identities, and in
operator form:

* `posCLM` and `momCLM` — the position operator `Xψ = xψ` and, in the conventions of `Wigner.lean`
  (momentum `p = 2πξ`), the momentum operator `P = (2πi)⁻¹ d/dx`, both as continuous operators on
  `𝓢(ℝ, ℂ)`;
* ★★ `integral_integral_wigner_pos` and ★★ `integral_integral_wigner_mom` — the symbols `x` and `ξ`
  average against `W_ψ` to `⟨ψ, Xψ⟩` and `⟨ψ, Pψ⟩`;
* ★★★ `integral_integral_wigner_posMom` — **the symbol `xξ` averages to `⟨ψ, ½(XP + PX)ψ⟩`**, the
  symmetrised product. This is the one that is not a marginal: the `½ψ` term is produced by the
  integration by parts that the weight `x` forces, and it is exactly the ordering correction that
  makes the Weyl quantisation of `xξ` symmetric.

Along the way, three lemmas that are about the Fourier transform rather than about `W`:
★ `integral_fourier` (`∫ 𝓕f = f 0`, by inversion), ★ `integral_deriv` (`∫ f' = 0`, because
`𝓕 f'` carries a factor `ξ`), and ★ `integral_mul_fourier` (the first moment of `𝓕f` is
`(2πi)⁻¹ f'(0)`), from which ★ `integral_mul_deriv` (`∫ x f'(x) dx = −∫ f`) and
★★ `integral_mul_wigner_right` (the `ξ`-moment of `W_ψ` at fixed `x` is the probability current).

## Honest scope

⚠️ **`W_ψ` is not proved to be Schwartz on `ℝ²`.** BACKLOG #92(c) asked for that, and what is proved
here is what it was wanted for — joint measurability, square-integrability, and the product-measure
form of the overlap identity — by a cheaper route: slicewise Plancherel plus a convolution, rather
than seminorm estimates on the plane. The Schwartz property itself would need the partial Fourier
transform to act on `𝓢(ℝ², ℂ)`, which the pin has in no form.

⚠️ **`Op(a)` is still not an operator on `𝓢(ℝ, ℂ)`** (#92(a)). Nothing here maps Schwartz functions
to Schwartz functions, composes symbols, or takes adjoints. With `weylOp`'s datum — a family
`b : ℝ → 𝓢(ℝ, ℂ)` with no regularity in its first slot — `weylOp b ψ` need not even be continuous,
so this is not a gap in the proofs but a statement that needs a different symbol class (a jointly
Schwartz kernel), and then differentiation under the integral sign **to all orders with bounds**,
which neither Mathlib nor this corpus has
(MATHLIB-ABSENT(file:Mathlib/Analysis/Calculus/ParametricIntegralContDiff)):
[`ContDiffParametricIntervalIntegral.lean`](../Calculus/ContDiffParametricIntervalIntegral.lean)
covers `C^n` dependence for *interval* integrals only.

⚠️ The three temperate symbols appear as **moment identities**, not as operators `Op(x)`, `Op(ξ)`,
`Op(xξ)`; the identification of the symmetrised product with a Weyl quantisation is the physics
reading of `integral_integral_wigner_posMom`, not a theorem about `weylOp`.

⚠️ One dimension, Schwartz states, the conventions of `Wigner.lean`
(`𝓕 f ξ = ∫ e^{−2πiyξ} f y dy`, momentum `p = 2πξ`).

References: J. E. Moyal, *Quantum mechanics as a statistical theory*, Proc. Cambridge Philos. Soc. 45
(1949) 99 §3 (the moments of `W`); G. B. Folland, *Harmonic Analysis in Phase Space* (1989) §1.8
(the symmetrised product as the Weyl quantisation of `xξ`); `specs/BACKLOG.md` #92;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate Convolution LineDeriv

noncomputable section

namespace WignerFunction

/-! ### The mass and the first moment of a Fourier transform -/

/-- The line derivative at `1` is the ordinary derivative. -/
theorem lineDerivOp_one (f : 𝓢(ℝ, ℂ)) : ∂_{(1 : ℝ)} f = SchwartzMap.derivCLM ℂ ℂ f := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply]
  rfl

/-- The Fourier transform at the origin is the mass. -/
theorem fourier_apply_zero (f : 𝓢(ℝ, ℂ)) : 𝓕 f (0 : ℝ) = ∫ y : ℝ, f y := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

/-- ★ **The mass of a Fourier transform is the value at the origin**, by inversion. -/
theorem integral_fourier (f : 𝓢(ℝ, ℂ)) : ∫ ξ : ℝ, 𝓕 f ξ = f 0 := by
  have h1 : Integrable (⇑f) := f.integrable
  have h2 : Integrable (𝓕 ⇑f) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 f).integrable
  have hinv := f.continuous.fourierInv_fourier_eq h1 h2
  have h0 : 𝓕⁻ (𝓕 ⇑f) 0 = ∫ ξ : ℝ, 𝓕 ⇑f ξ := by
    rw [Real.fourierInv_eq]
    simp
  calc ∫ ξ : ℝ, 𝓕 f ξ = 𝓕⁻ (𝓕 ⇑f) 0 := by rw [h0]; rfl
    _ = f 0 := by rw [hinv]

/-- The Fourier transform of a derivative, pointwise: the factor `2πiξ`. -/
theorem fourier_deriv_apply (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (∂_{(1 : ℝ)} f) ξ = (2 * π * Complex.I) * ((ξ : ℂ) * 𝓕 f ξ) := by
  have hg : Function.HasTemperateGrowth fun x : ℝ => (inner ℝ x (1 : ℝ) : ℝ) :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq f (1 : ℝ), smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  have hinner : (inner ℝ ξ (1 : ℝ) : ℝ) = ξ := by simp
  rw [hinner, Complex.real_smul, smul_eq_mul]

/-- ★ **The integral of a derivative vanishes**: the Fourier transform of `f'` carries a factor `ξ`,
which kills it at the origin. -/
theorem integral_deriv (f : 𝓢(ℝ, ℂ)) : ∫ x : ℝ, deriv f x = 0 := by
  have h0 : 𝓕 (∂_{(1 : ℝ)} f) (0 : ℝ) = 0 := by
    rw [fourier_deriv_apply]
    simp
  rw [fourier_apply_zero] at h0
  calc ∫ x : ℝ, deriv f x = ∫ x : ℝ, (∂_{(1 : ℝ)} f) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [lineDerivOp_one, SchwartzMap.derivCLM_apply]
    _ = 0 := h0

/-- ★ **The first `ξ`-moment of a Fourier transform is the derivative at the origin.** -/
theorem integral_mul_fourier (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, (ξ : ℂ) * 𝓕 f ξ = (2 * π * Complex.I)⁻¹ * deriv f 0 := by
  have hI : (2 * (π : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hmass : ∫ ξ : ℝ, 𝓕 (∂_{(1 : ℝ)} f) ξ = deriv f 0 := by
    rw [integral_fourier, lineDerivOp_one, SchwartzMap.derivCLM_apply]
  have hconst : ∫ ξ : ℝ, 𝓕 (∂_{(1 : ℝ)} f) ξ
      = (2 * π * Complex.I) * ∫ ξ : ℝ, (ξ : ℂ) * 𝓕 f ξ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fourier_deriv_apply f))
  rw [hmass] at hconst
  rw [hconst, ← mul_assoc, inv_mul_cancel₀ hI, one_mul]

/-! ### The position and momentum operators -/

theorem hasTemperateGrowth_ofReal : Function.HasTemperateGrowth fun x : ℝ => (x : ℂ) :=
  Complex.ofRealCLM.hasTemperateGrowth

/-- **The position operator** on Schwartz space: multiplication by the coordinate. -/
def posCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.smulLeftCLM ℂ fun x : ℝ => (x : ℂ)

@[simp]
theorem posCLM_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : posCLM ψ x = (x : ℂ) * ψ x := by
  rw [posCLM, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_ofReal, smul_eq_mul]

/-- **The momentum operator** in the conventions of `Wigner.lean`, where the momentum is `p = 2πξ`:
`P = (2πi)⁻¹ d/dx`. -/
def momCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (2 * π * Complex.I)⁻¹ • SchwartzMap.derivCLM ℂ ℂ

@[simp]
theorem momCLM_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momCLM ψ x = (2 * π * Complex.I)⁻¹ * deriv ψ x := by
  simp [momCLM, SchwartzMap.derivCLM_apply, smul_eq_mul]

/-- The derivative of `x ψ(x)`. -/
theorem deriv_posCLM (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (posCLM ψ) x = ψ x + (x : ℂ) * deriv ψ x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ψ t) (deriv ψ x) x := ψ.differentiableAt.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => (t : ℂ) * ψ t) (1 * ψ x + (x : ℂ) * deriv ψ x) x := h1.mul h2
  have heq : (⇑(posCLM ψ) : ℝ → ℂ) = fun t : ℝ => (t : ℂ) * ψ t := funext (posCLM_apply ψ)
  rw [heq, h.deriv, one_mul]

/-- ★ **Integration by parts against the coordinate**: `∫ x ψ'(x) dx = −∫ ψ`. -/
theorem integral_mul_deriv (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, (x : ℂ) * deriv ψ x = -∫ x : ℝ, ψ x := by
  have hd : Integrable fun x : ℝ => deriv (posCLM ψ) x := by
    have h : (fun x : ℝ => deriv (posCLM ψ) x)
        = fun x : ℝ => SchwartzMap.derivCLM ℂ ℂ (posCLM ψ) x :=
      funext fun x => (SchwartzMap.derivCLM_apply (𝕜 := ℂ) (posCLM ψ) x).symm
    rw [h]
    exact (SchwartzMap.derivCLM ℂ ℂ (posCLM ψ)).integrable
  have hpt : ∀ x : ℝ, (x : ℂ) * deriv ψ x = deriv (posCLM ψ) x - ψ x := by
    intro x
    rw [deriv_posCLM]
    ring
  calc ∫ x : ℝ, (x : ℂ) * deriv ψ x = ∫ x : ℝ, (deriv (posCLM ψ) x - ψ x) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x : ℝ, deriv (posCLM ψ) x) - ∫ x : ℝ, ψ x := integral_sub hd ψ.integrable
    _ = -∫ x : ℝ, ψ x := by rw [integral_deriv]; ring

/-! ### The `ξ`-moment of the Wigner function at a fixed position -/

/-- The derivative of the pointwise product `φ · conj ψ`. -/
theorem hasDerivAt_mulConj (φ ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => mulConj φ ψ y)
      (deriv φ x * conj (ψ x) + φ x * conj (deriv ψ x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => φ y) (deriv φ x) x := φ.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => conj (ψ y)) (conj (deriv ψ x)) x :=
    (ψ.differentiableAt.hasDerivAt).star
  have h : HasDerivAt (fun y : ℝ => φ y * conj (ψ y))
      (deriv φ x * conj (ψ x) + φ x * conj (deriv ψ x)) x := h1.mul h2
  have heq : (fun y : ℝ => mulConj φ ψ y) = fun y : ℝ => φ y * conj (ψ y) :=
    funext (mulConj_apply φ ψ)
  rw [heq]
  exact h

/-- The chain rule for the affine reparametrisations of `Wigner.lean`. -/
theorem hasDerivAt_affine (ψ : 𝓢(ℝ, ℂ)) (x s y : ℝ) :
    HasDerivAt (fun t : ℝ => ψ (x + s * t)) ((s : ℂ) * deriv ψ (x + s * y)) y := by
  have hu : HasDerivAt (fun t : ℝ => x + s * t) s y := by
    simpa using ((hasDerivAt_id y).const_mul s).const_add x
  have hψ : HasDerivAt (fun t : ℝ => ψ t) (deriv ψ (x + s * y)) ((fun t : ℝ => x + s * t) y) :=
    ψ.differentiableAt.hasDerivAt
  have h := hψ.scomp y hu
  simpa [Function.comp_def, Complex.real_smul, mul_comm] using h

/-- The `y`-derivative of the Wigner kernel at the origin is the probability current, up to the
factor `2πi`. -/
theorem hasDerivAt_wignerKernel_zero (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => wignerKernel ψ x y)
      (2⁻¹ * (deriv ψ x * conj (ψ x) - ψ x * conj (deriv ψ x))) 0 := by
  have h1 : HasDerivAt (fun y : ℝ => ψ (x + 2⁻¹ * y)) (((2⁻¹ : ℝ) : ℂ) * deriv ψ x) 0 := by
    simpa using hasDerivAt_affine ψ x 2⁻¹ 0
  have h2 : HasDerivAt (fun y : ℝ => ψ (x + (-2⁻¹) * y))
      (((-2⁻¹ : ℝ) : ℂ) * deriv ψ x) 0 := by
    simpa using hasDerivAt_affine ψ x (-2⁻¹) 0
  have h2' : HasDerivAt (fun y : ℝ => conj (ψ (x + (-2⁻¹) * y)))
      (conj (((-2⁻¹ : ℝ) : ℂ) * deriv ψ x)) 0 := h2.star
  have h := h1.mul h2'
  have heq : (fun y : ℝ => wignerKernel ψ x y)
      = fun y : ℝ => ψ (x + 2⁻¹ * y) * conj (ψ (x + (-2⁻¹) * y)) := by
    funext y
    rw [wignerKernel_apply, show x + 2⁻¹ * y = x + y / 2 by ring,
      show x + (-2⁻¹) * y = x - y / 2 by ring]
  rw [heq]
  refine h.congr_deriv ?_
  simp only [mul_zero, add_zero, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- ★★ **The first `ξ`-moment of the Wigner function at a fixed position is the probability
current** — the local momentum density, whose integral is the momentum expectation. -/
theorem integral_mul_wigner_right (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∫ ξ : ℝ, (ξ : ℂ) * wigner ψ x ξ
      = (2 * π * Complex.I)⁻¹ * (2⁻¹ * (deriv ψ x * conj (ψ x) - ψ x * conj (deriv ψ x))) := by
  have h : ∫ ξ : ℝ, (ξ : ℂ) * wigner ψ x ξ
      = (2 * π * Complex.I)⁻¹ * deriv (wignerKernel ψ x) 0 := integral_mul_fourier _
  rw [h, (hasDerivAt_wignerKernel_zero ψ x).deriv]

/-! ### Integrability of the products that appear -/

theorem integrable_mulConj (φ ψ : 𝓢(ℝ, ℂ)) : Integrable fun x : ℝ => φ x * conj (ψ x) := by
  have h : (fun x : ℝ => φ x * conj (ψ x)) = fun x : ℝ => mulConj φ ψ x :=
    funext fun x => (mulConj_apply φ ψ x).symm
  rw [h]
  exact (mulConj φ ψ).integrable

theorem integrable_mul_mulConj (φ ψ : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => (x : ℂ) * (φ x * conj (ψ x)) := by
  have h : (fun x : ℝ => (x : ℂ) * (φ x * conj (ψ x)))
      = fun x : ℝ => posCLM (mulConj φ ψ) x := by
    funext x
    simp only [posCLM_apply, mulConj_apply]
  rw [h]
  exact (posCLM (mulConj φ ψ)).integrable

theorem integrable_deriv_mul_conj (ψ : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => deriv ψ x * conj (ψ x) := by
  have h : (fun x : ℝ => deriv ψ x * conj (ψ x))
      = fun x : ℝ => (SchwartzMap.derivCLM ℂ ℂ ψ) x * conj (ψ x) :=
    funext fun x => by rw [SchwartzMap.derivCLM_apply]
  rw [h]
  exact integrable_mulConj _ _

theorem integrable_mul_conj_deriv (ψ : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => ψ x * conj (deriv ψ x) := by
  have h : (fun x : ℝ => ψ x * conj (deriv ψ x))
      = fun x : ℝ => ψ x * conj ((SchwartzMap.derivCLM ℂ ℂ ψ) x) :=
    funext fun x => by rw [SchwartzMap.derivCLM_apply]
  rw [h]
  exact integrable_mulConj _ _

theorem integrable_mul_deriv_mul_conj (ψ : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => (x : ℂ) * (deriv ψ x * conj (ψ x)) := by
  have h : (fun x : ℝ => (x : ℂ) * (deriv ψ x * conj (ψ x)))
      = fun x : ℝ => (x : ℂ) * ((SchwartzMap.derivCLM ℂ ℂ ψ) x * conj (ψ x)) :=
    funext fun x => by rw [SchwartzMap.derivCLM_apply]
  rw [h]
  exact integrable_mul_mulConj _ _

theorem integrable_mul_mul_conj_deriv (ψ : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => (x : ℂ) * (ψ x * conj (deriv ψ x)) := by
  have h : (fun x : ℝ => (x : ℂ) * (ψ x * conj (deriv ψ x)))
      = fun x : ℝ => (x : ℂ) * (ψ x * conj ((SchwartzMap.derivCLM ℂ ℂ ψ) x)) :=
    funext fun x => by rw [SchwartzMap.derivCLM_apply]
  rw [h]
  exact integrable_mul_mulConj _ _

/-! ### The two current identities -/

/-- The derivative of `|ψ|²`. -/
theorem deriv_mulConj_self (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (mulConj ψ ψ) x = deriv ψ x * conj (ψ x) + ψ x * conj (deriv ψ x) :=
  (hasDerivAt_mulConj ψ ψ x).deriv

/-- ★ **The current integrates to zero**: `∫ (ψ' conj ψ + ψ conj ψ') = 0`, since it is the integral
of the derivative of `|ψ|²`. -/
theorem integral_deriv_mul_conj_add (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, deriv ψ x * conj (ψ x)) + ∫ x : ℝ, ψ x * conj (deriv ψ x) = 0 := by
  have h := integral_deriv (mulConj ψ ψ)
  calc (∫ x : ℝ, deriv ψ x * conj (ψ x)) + ∫ x : ℝ, ψ x * conj (deriv ψ x)
      = ∫ x : ℝ, (deriv ψ x * conj (ψ x) + ψ x * conj (deriv ψ x)) :=
        (integral_add (integrable_deriv_mul_conj ψ) (integrable_mul_conj_deriv ψ)).symm
    _ = ∫ x : ℝ, deriv (mulConj ψ ψ) x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (deriv_mulConj_self ψ x).symm)
    _ = 0 := h

/-- ★★ **The weighted current identity**: `∫ x (ψ' conj ψ + ψ conj ψ') = −∫ |ψ|²`, which is
integration by parts against the coordinate. -/
theorem integral_mul_deriv_mul_conj_add (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
        + ∫ x : ℝ, (x : ℂ) * (ψ x * conj (deriv ψ x))
      = -∫ x : ℝ, ψ x * conj (ψ x) := by
  have h := integral_mul_deriv (mulConj ψ ψ)
  have hmass : (∫ x : ℝ, mulConj ψ ψ x) = ∫ x : ℝ, ψ x * conj (ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall (mulConj_apply ψ ψ))
  calc (∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
          + ∫ x : ℝ, (x : ℂ) * (ψ x * conj (deriv ψ x))
      = ∫ x : ℝ, ((x : ℂ) * (deriv ψ x * conj (ψ x)) + (x : ℂ) * (ψ x * conj (deriv ψ x))) :=
        (integral_add (integrable_mul_deriv_mul_conj ψ)
          (integrable_mul_mul_conj_deriv ψ)).symm
    _ = ∫ x : ℝ, (x : ℂ) * deriv (mulConj ψ ψ) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [deriv_mulConj_self]
        ring
    _ = -∫ x : ℝ, mulConj ψ ψ x := h
    _ = -∫ x : ℝ, ψ x * conj (ψ x) := by rw [hmass]

/-! ### The three temperate symbols -/

/-- ★★ **The symbol `a(x, ξ) = x` quantises to the position operator.** -/
theorem integral_integral_wigner_pos (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ∫ ξ : ℝ, (x : ℂ) * wigner ψ x ξ) = ∫ x : ℝ, conj (ψ x) * posCLM ψ x := by
  rw [integral_integral_mul_wigner_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [posCLM_apply]
  rw [← Complex.mul_conj']
  ring

/-- ★★ **The symbol `a(x, ξ) = ξ` quantises to the momentum operator** `P = (2πi)⁻¹ d/dx`. -/
theorem integral_integral_wigner_mom (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ∫ ξ : ℝ, (ξ : ℂ) * wigner ψ x ξ) = ∫ x : ℝ, conj (ψ x) * momCLM ψ x := by
  have hcur := integral_deriv_mul_conj_add ψ
  have hL : (∫ x : ℝ, ∫ ξ : ℝ, (ξ : ℂ) * wigner ψ x ξ)
      = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((∫ x : ℝ, deriv ψ x * conj (ψ x))
          - ∫ x : ℝ, ψ x * conj (deriv ψ x))) := by
    calc (∫ x : ℝ, ∫ ξ : ℝ, (ξ : ℂ) * wigner ψ x ξ)
        = ∫ x : ℝ, (2 * π * Complex.I)⁻¹
            * (2⁻¹ * (deriv ψ x * conj (ψ x) - ψ x * conj (deriv ψ x))) :=
          integral_congr_ae (Filter.Eventually.of_forall (integral_mul_wigner_right ψ))
      _ = (2 * π * Complex.I)⁻¹
            * ∫ x : ℝ, 2⁻¹ * (deriv ψ x * conj (ψ x) - ψ x * conj (deriv ψ x)) :=
          integral_const_mul _ _
      _ = (2 * π * Complex.I)⁻¹
            * (2⁻¹ * ∫ x : ℝ, (deriv ψ x * conj (ψ x) - ψ x * conj (deriv ψ x))) := by
          rw [integral_const_mul]
      _ = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((∫ x : ℝ, deriv ψ x * conj (ψ x))
            - ∫ x : ℝ, ψ x * conj (deriv ψ x))) := by
          rw [integral_sub (integrable_deriv_mul_conj ψ) (integrable_mul_conj_deriv ψ)]
  have hR : (∫ x : ℝ, conj (ψ x) * momCLM ψ x)
      = (2 * π * Complex.I)⁻¹ * ∫ x : ℝ, deriv ψ x * conj (ψ x) := by
    calc (∫ x : ℝ, conj (ψ x) * momCLM ψ x)
        = ∫ x : ℝ, (2 * π * Complex.I)⁻¹ * (deriv ψ x * conj (ψ x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [momCLM_apply]
          ring
      _ = (2 * π * Complex.I)⁻¹ * ∫ x : ℝ, deriv ψ x * conj (ψ x) := integral_const_mul _ _
  rw [hL, hR]
  have h2 : (∫ x : ℝ, ψ x * conj (deriv ψ x)) = -∫ x : ℝ, deriv ψ x * conj (ψ x) := by
    linear_combination hcur
  rw [h2]
  ring

/-- ★★★ **The symbol `a(x, ξ) = xξ` quantises to the symmetrised product `½(XP + PX)`.** This is
the third temperate symbol and the only one that is not a marginal: the phase-space average of `xξ`
against `W_ψ` is the expectation of the symmetrised product, the extra `½ψ` coming from the
integration by parts that the weight `x` forces. -/
theorem integral_integral_wigner_posMom (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ∫ ξ : ℝ, (x : ℂ) * (ξ : ℂ) * wigner ψ x ξ)
      = ∫ x : ℝ, conj (ψ x) * (2⁻¹ * (posCLM (momCLM ψ) x + momCLM (posCLM ψ) x)) := by
  have hweight := integral_mul_deriv_mul_conj_add ψ
  have hinner : ∀ x : ℝ, (∫ ξ : ℝ, (x : ℂ) * (ξ : ℂ) * wigner ψ x ξ)
      = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((x : ℂ) * (deriv ψ x * conj (ψ x))
          - (x : ℂ) * (ψ x * conj (deriv ψ x)))) := by
    intro x
    rw [show (fun ξ : ℝ => (x : ℂ) * (ξ : ℂ) * wigner ψ x ξ)
        = fun ξ : ℝ => (x : ℂ) * ((ξ : ℂ) * wigner ψ x ξ) from funext fun ξ => by ring,
      integral_const_mul, integral_mul_wigner_right]
    ring
  have hL : (∫ x : ℝ, ∫ ξ : ℝ, (x : ℂ) * (ξ : ℂ) * wigner ψ x ξ)
      = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
          - ∫ x : ℝ, (x : ℂ) * (ψ x * conj (deriv ψ x)))) := by
    calc (∫ x : ℝ, ∫ ξ : ℝ, (x : ℂ) * (ξ : ℂ) * wigner ψ x ξ)
        = ∫ x : ℝ, (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((x : ℂ) * (deriv ψ x * conj (ψ x))
            - (x : ℂ) * (ψ x * conj (deriv ψ x)))) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = (2 * π * Complex.I)⁻¹ * ∫ x : ℝ, 2⁻¹ * ((x : ℂ) * (deriv ψ x * conj (ψ x))
            - (x : ℂ) * (ψ x * conj (deriv ψ x))) := integral_const_mul _ _
      _ = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ∫ x : ℝ, ((x : ℂ) * (deriv ψ x * conj (ψ x))
            - (x : ℂ) * (ψ x * conj (deriv ψ x)))) := by rw [integral_const_mul]
      _ = (2 * π * Complex.I)⁻¹ * (2⁻¹ * ((∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
            - ∫ x : ℝ, (x : ℂ) * (ψ x * conj (deriv ψ x)))) := by
          rw [integral_sub (integrable_mul_deriv_mul_conj ψ) (integrable_mul_mul_conj_deriv ψ)]
  have hR : (∫ x : ℝ, conj (ψ x) * (2⁻¹ * (posCLM (momCLM ψ) x + momCLM (posCLM ψ) x)))
      = (2 * π * Complex.I)⁻¹ * ((∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
          + 2⁻¹ * ∫ x : ℝ, ψ x * conj (ψ x)) := by
    calc (∫ x : ℝ, conj (ψ x) * (2⁻¹ * (posCLM (momCLM ψ) x + momCLM (posCLM ψ) x)))
        = ∫ x : ℝ, (2 * π * Complex.I)⁻¹ * ((x : ℂ) * (deriv ψ x * conj (ψ x))
            + 2⁻¹ * (ψ x * conj (ψ x))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [posCLM_apply, momCLM_apply, deriv_posCLM]
          ring
      _ = (2 * π * Complex.I)⁻¹ * ∫ x : ℝ, ((x : ℂ) * (deriv ψ x * conj (ψ x))
            + 2⁻¹ * (ψ x * conj (ψ x))) := integral_const_mul _ _
      _ = (2 * π * Complex.I)⁻¹ * ((∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
            + ∫ x : ℝ, 2⁻¹ * (ψ x * conj (ψ x))) := by
          rw [integral_add (integrable_mul_deriv_mul_conj ψ)
            ((integrable_mulConj ψ ψ).const_mul (2⁻¹ : ℂ))]
      _ = (2 * π * Complex.I)⁻¹ * ((∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)))
            + 2⁻¹ * ∫ x : ℝ, ψ x * conj (ψ x)) := by rw [integral_const_mul]
  rw [hL, hR]
  have h2 : (∫ x : ℝ, (x : ℂ) * (ψ x * conj (deriv ψ x)))
      = -(∫ x : ℝ, ψ x * conj (ψ x)) - ∫ x : ℝ, (x : ℂ) * (deriv ψ x * conj (ψ x)) := by
    linear_combination hweight
  rw [h2]
  ring

/-! ### The Wigner function as a function on the plane -/

/-- The square of the modulus of a Schwartz function is integrable. -/
theorem integrable_normSq (g : 𝓢(ℝ, ℂ)) : Integrable fun y : ℝ => ‖g y‖ ^ 2 := by
  have h : (fun y : ℝ => ‖g y‖ ^ 2) = fun y : ℝ => ‖mulConj g g y‖ := by
    funext y
    rw [mulConj_apply, norm_mul, RCLike.norm_conj]
    ring
  rw [h]
  exact (mulConj g g).integrable.norm

/-- ★ **The Wigner function is jointly measurable on the plane.** -/
theorem stronglyMeasurable_wigner (ψ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable fun p : ℝ × ℝ => wigner ψ p.1 p.2 := by
  have hcont : Continuous fun q : (ℝ × ℝ) × ℝ =>
      (𝐞 (-(q.2 * q.1.2)) : ℂ) * (ψ (q.1.1 + q.2 / 2) * conj (ψ (q.1.1 - q.2 / 2))) := by
    have h2 : Continuous fun q : (ℝ × ℝ) × ℝ => ψ (q.1.1 + q.2 / 2) := by
      refine ψ.continuous.comp ?_
      exact (continuous_fst.comp continuous_fst).add (continuous_snd.div_const 2)
    have h3 : Continuous fun q : (ℝ × ℝ) × ℝ => conj (ψ (q.1.1 - q.2 / 2)) := by
      refine Complex.continuous_conj.comp (ψ.continuous.comp ?_)
      exact (continuous_fst.comp continuous_fst).sub (continuous_snd.div_const 2)
    exact (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ =>
      (𝐞 (-(q.2 * q.1.2)) : ℂ)).mul (h2.mul h3)
  have heq : (fun p : ℝ × ℝ => wigner ψ p.1 p.2)
      = fun p : ℝ × ℝ => ∫ y : ℝ,
        (𝐞 (-(y * p.2)) : ℂ) * (ψ (p.1 + y / 2) * conj (ψ (p.1 - y / 2))) :=
    funext fun p => wigner_eq_integral ψ p.1 p.2
  rw [heq]
  exact hcont.stronglyMeasurable.integral_prod_right'

/-- The `ξ`-energy of the Wigner function at a fixed position: `∫ |W_ψ(x, ξ)|² dξ`. -/
def wignerEnergy (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ := ∫ ξ : ℝ, ‖wigner ψ x ξ‖ ^ 2

theorem integrable_normSq_wigner (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable fun ξ : ℝ => ‖wigner ψ x ξ‖ ^ 2 := by
  have h : (fun ξ : ℝ => ‖wigner ψ x ξ‖ ^ 2) = fun ξ : ℝ => ‖𝓕 (wignerKernel ψ x) ξ‖ ^ 2 := rfl
  rw [h]
  exact integrable_normSq _

/-- The energy is the slicewise overlap of the Wigner function with itself. -/
theorem wignerEnergy_eq (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ((wignerEnergy ψ x : ℝ) : ℂ) = ∫ ξ : ℝ, wigner ψ x ξ * conj (wigner ψ x ξ) := by
  have hcomm : (∫ ξ : ℝ, ((‖wigner ψ x ξ‖ ^ 2 : ℝ) : ℂ))
      = ((∫ ξ : ℝ, ‖wigner ψ x ξ‖ ^ 2 : ℝ) : ℂ) := by
    simpa using
      ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (integrable_normSq_wigner ψ x)
  rw [wignerEnergy, ← hcomm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Complex.mul_conj']
  push_cast
  ring

/-- ★★ **The energy is an integrable function of the position**: it is a convolution of two
integrable functions, read at `2x`. -/
theorem integrable_wignerEnergy (ψ : 𝓢(ℝ, ℂ)) : Integrable (wignerEnergy ψ) := by
  have hGint : Integrable (fun v => mulConj ψ ψ v) := (mulConj ψ ψ).integrable
  have hGconj : Integrable (fun v => conj (mulConj ψ ψ v)) := by
    refine hGint.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (Complex.continuous_conj.comp (mulConj ψ ψ).continuous).aestronglyMeasurable
    · simp
  have hconv : Integrable ((fun v => mulConj ψ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
      (fun v => conj (mulConj ψ ψ v))) := hGint.integrable_convolution _ hGconj
  have hscale : Integrable fun x : ℝ => ((fun v => mulConj ψ ψ v)
      ⋆[ContinuousLinearMap.mul ℝ ℂ] (fun v => conj (mulConj ψ ψ v))) (2 * x) :=
    hconv.comp_mul_left' (by norm_num)
  have hstep : ∀ x : ℝ, ((wignerEnergy ψ x : ℝ) : ℂ)
      = 2 * ((fun v => mulConj ψ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj ψ ψ v))) (2 * x) := by
    intro x
    rw [wignerEnergy_eq, integral_wigner_mul_conj ψ ψ x,
      show (∫ y : ℝ, wignerKernel ψ x y * conj (wignerKernel ψ x y))
          = ∫ y : ℝ, mulConj ψ ψ (x + y / 2) * conj (mulConj ψ ψ (x - y / 2)) from
        integral_congr_ae (Filter.Eventually.of_forall fun y => wignerKernel_mul_conj ψ ψ x y),
      integral_mulConj_shift (mulConj ψ ψ) x]
  have hC : Integrable fun x : ℝ => ((wignerEnergy ψ x : ℝ) : ℂ) := by
    refine (hscale.const_mul 2).congr (Filter.Eventually.of_forall fun x => ?_)
    exact (hstep x).symm
  have hre := hC.re
  refine hre.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- ★★ **The Wigner function is square-integrable on the plane.** -/
theorem integrable_normSq_wigner_prod (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun p : ℝ × ℝ => ‖wigner ψ p.1 p.2‖ ^ 2) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖wigner ψ p.1 p.2‖ ^ 2)
      (volume.prod volume) :=
    ((stronglyMeasurable_wigner ψ).norm.pow 2).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact integrable_normSq_wigner ψ x
  · refine (integrable_wignerEnergy ψ).congr (Filter.Eventually.of_forall fun x => ?_)
    rw [wignerEnergy]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    exact (Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖wigner ψ x ξ‖ ^ 2)).symm

/-- ★★★ **The overlap integrand is integrable on the plane**, so the overlap identity is an integral
against the product measure and not only an iterated integral. The bound is the elementary
`|ab| ≤ (|a|² + |b|²)/2`, which is what square-integrability buys. -/
theorem integrable_wigner_mul_conj (φ ψ : 𝓢(ℝ, ℂ)) :
    Integrable (Function.uncurry fun x ξ : ℝ => wigner φ x ξ * conj (wigner ψ x ξ))
      (volume.prod volume) := by
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      2⁻¹ * (‖wigner φ p.1 p.2‖ ^ 2 + ‖wigner ψ p.1 p.2‖ ^ 2)) (volume.prod volume) :=
    ((integrable_normSq_wigner_prod φ).add (integrable_normSq_wigner_prod ψ)).const_mul _
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x ξ : ℝ => wigner φ x ξ * conj (wigner ψ x ξ))
      (volume.prod volume) := by
    have h : (Function.uncurry fun x ξ : ℝ => wigner φ x ξ * conj (wigner ψ x ξ))
        = fun p : ℝ × ℝ => wigner φ p.1 p.2 * conj (wigner ψ p.1 p.2) := rfl
    rw [h]
    exact ((stronglyMeasurable_wigner φ).mul
      (Complex.continuous_conj.comp_stronglyMeasurable
        (stronglyMeasurable_wigner ψ))).aestronglyMeasurable
  refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
  show ‖wigner φ p.1 p.2 * conj (wigner ψ p.1 p.2)‖
      ≤ 2⁻¹ * (‖wigner φ p.1 p.2‖ ^ 2 + ‖wigner ψ p.1 p.2‖ ^ 2)
  rw [norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖wigner φ p.1 p.2‖ - ‖wigner ψ p.1 p.2‖), norm_nonneg (wigner φ p.1 p.2),
    norm_nonneg (wigner ψ p.1 p.2)]

/-- ★★★ **The overlap identity against the product measure on the plane.** This is
`integral_integral_wigner_mul_conj` with the iterated integral replaced by a single integral over
phase space, which is what makes `W_ψ` a function *on* the plane rather than a family of slices. -/
theorem integral_prod_wigner_mul_conj (φ ψ : 𝓢(ℝ, ℂ)) :
    (∫ p : ℝ × ℝ, wigner φ p.1 p.2 * conj (wigner ψ p.1 p.2))
      = (∫ v : ℝ, φ v * conj (ψ v)) * conj (∫ v : ℝ, φ v * conj (ψ v)) := by
  have h := MeasureTheory.integral_integral (μ := volume) (ν := volume)
    (f := fun x ξ : ℝ => wigner φ x ξ * conj (wigner ψ x ξ)) (integrable_wigner_mul_conj φ ψ)
  rw [MeasureTheory.Measure.volume_eq_prod, ← h]
  exact integral_integral_wigner_mul_conj φ ψ

/-- ★★ **The purity form on the plane.** -/
theorem integral_prod_wigner_sq (ψ : 𝓢(ℝ, ℂ)) :
    (∫ p : ℝ × ℝ, wigner ψ p.1 p.2 * wigner ψ p.1 p.2)
      = (∫ v : ℝ, (‖ψ v‖ : ℂ) ^ 2) * ∫ v : ℝ, (‖ψ v‖ : ℂ) ^ 2 := by
  have h : (∫ p : ℝ × ℝ, wigner ψ p.1 p.2 * wigner ψ p.1 p.2)
      = ∫ p : ℝ × ℝ, wigner ψ p.1 p.2 * conj (wigner ψ p.1 p.2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [conj_wigner]
  rw [h, integral_prod_wigner_mul_conj]
  have hmass : (∫ v : ℝ, ψ v * conj (ψ v)) = ∫ v : ℝ, (‖ψ v‖ : ℂ) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun v => Complex.mul_conj' (ψ v))
  rw [hmass]
  congr 1
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

end WignerFunction

end

end
