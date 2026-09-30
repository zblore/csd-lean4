/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.Wigner
public import Mathlib.Analysis.Convolution

/-!
# The Wigner function as the state in phase space: overlaps and Weyl expectations

**Category:** 1-Mathlib (staged for upstream). BACKLOG #63, the residue of #45.

[`Wigner.lean`](Wigner.lean) gives the Wigner function its marginals and its free transport. That
makes `W_ψ` a phase-space picture of the *position and momentum distributions*; this file makes it
the picture of the **state**:

* ★★★ `integral_integral_wigner_mul_conj` — **the overlap (Moyal) identity**
  `∫∫ W_φ(x, ξ) conj (W_ψ(x, ξ)) dξ dx = |∫ φ conj ψ|²`. Phase space recovers the inner product, so
  the Wigner map loses nothing: two states with the same Wigner function agree up to a phase. With
  `φ = ψ` it reads `∫∫ W_ψ² = (∫ |ψ|²)²` (★★ `integral_integral_wigner_sq`);
* ★★★ `integral_conj_mul_weylOp` — **the Weyl expectation formula**
  `⟨ψ, Op(a) ψ⟩ = ∫∫ a(u, ξ) W_ψ(u, ξ) dξ du`: the expectation of a Weyl-quantised observable is
  the phase-space average of its symbol against `W_ψ`, which is what "the state in phase space"
  means operationally.

## How the symbol is presented, and why

A Weyl operator is `(Op(a) ψ)(x) = ∫∫ a((x + y)/2, ξ) e^{2πi(x − y)ξ} ψ(y) dξ dy`. The inner
`ξ`-integral is the Fourier transform of the symbol in its second slot, so the operator only ever
sees that transform, and this file takes **that** as the datum: a symbol is a family
`b : ℝ → 𝓢(ℝ, ℂ)` of Schwartz slices, the operator is
`weylOp b ψ x = ∫ y, b ((x + y)/2) (x − y) ψ y`, and the symbol itself is
`weylSymbol b u ξ = 𝓕 (b u) ξ`. Presenting it this way buys two things: the `ξ`-integral converges by
fiat rather than by an oscillatory-integral argument, and the Parseval step of the proof is Mathlib's
Plancherel theorem for Schwartz functions, applied slicewise.

The substitutions `x = u + w/2`, `y = u − w/2` turn the operator's `(x, y)` kernel into the Wigner
kernel in `(u, w)`, and Plancherel in `w` turns that into the symbol against `W_ψ`. The step needs
the `(x, u)` integrand to be integrable on the plane, which is what the hypotheses `hM`, `hbM` (an
integrable function dominating the slices) supply.

## Honest scope

⚠️ **No pseudodifferential calculus.** `weylOp` is a function of `x`, not a continuous operator on
`𝓢(ℝ, ℂ)`; nothing here says `Op(a)` maps Schwartz functions to Schwartz functions, composes, or has
an adjoint. BACKLOG #92.

⚠️ **Schwartz slices with an integrable dominating function**, which excludes the symbols of
temperate growth — `a(x, ξ) = x`, `ξ`, `xξ` — whose quantisations are the position, momentum and
symmetrised product operators. Their **moment identities** are now proved in
[`WignerCalculus.lean`](WignerCalculus.lean) (★★ `integral_integral_wigner_pos`,
★★ `integral_integral_wigner_mom`, ★★★ `integral_integral_wigner_posMom` — the last being the
symmetrised product `½(XP + PX)`), so what is still missing for those symbols is `Op(a)` as an
operator, not the physics: BACKLOG #92(a).

⚠️ **The overlap identity here is an iterated integral**, in the order `∫ x, ∫ ξ`. The
product-measure form on `ℝ²` is [`WignerCalculus.lean`](WignerCalculus.lean)
(★★★ `integral_prod_wigner_mul_conj`, on ★★★ `integrable_wigner_mul_conj`), which also gives joint
measurability and square-integrability on the plane. The Schwartz property of
`(x, ξ) ↦ W_ψ(x, ξ)` on `ℝ²` is still not proved, and is not needed for either.

⚠️ One dimension, Schwartz data, the conventions of `Wigner.lean` (`𝓕 f ξ = ∫ e^{−2πiyξ} f y dy`,
momentum `p = 2πξ`).

References: J. E. Moyal, *Quantum mechanics as a statistical theory*, Proc. Cambridge Philos. Soc. 45
(1949) 99 §§3–4 (the overlap identity and the expectation formula); G. B. Folland, *Harmonic
Analysis in Phase Space* (1989) §1.8; `specs/BACKLOG.md` #63; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate Convolution

namespace WignerFunction

/-! ### Two substitutions on the line -/

/-- Substitution `y ↦ x + s y` in an integral over the line. -/
theorem integral_comp_affine_shift (f : ℝ → ℂ) (x s : ℝ) :
    ∫ y, f (x + s * y) = |s⁻¹| • ∫ z, f z := by
  calc ∫ y, f (x + s * y) = ∫ y, (fun u => f (x + u)) (s * y) := rfl
    _ = |s⁻¹| • ∫ u, f (x + u) := Measure.integral_comp_mul_left (fun u => f (x + u)) s
    _ = |s⁻¹| • ∫ z, f z := by rw [integral_add_left_eq_self]

/-! ### The pointwise product `φ · conj ψ` as a Schwartz function -/

/-- The Schwartz function `v ↦ φ v * conj (ψ v)`, whose integral is the `L²` pairing. -/
noncomputable def mulConj (φ ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth.comp ψ.hasTemperateGrowth) φ

theorem mulConj_apply (φ ψ : 𝓢(ℝ, ℂ)) (v : ℝ) : mulConj φ ψ v = φ v * conj (ψ v) := rfl

/-- The Wigner kernels of two states multiply into the product `φ · conj ψ` at the two shifted
points. -/
theorem wignerKernel_mul_conj (φ ψ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    wignerKernel φ x y * conj (wignerKernel ψ x y)
      = mulConj φ ψ (x + y / 2) * conj (mulConj φ ψ (x - y / 2)) := by
  simp only [wignerKernel_apply, mulConj_apply, map_mul, Complex.conj_conj]
  ring

/-! ### The overlap identity -/

/-- Plancherel slicewise: at a fixed `x` the `ξ`-integral of `W_φ · conj (W_ψ)` is the `y`-integral
of `K_φ · conj (K_ψ)`. -/
theorem integral_wigner_mul_conj (φ ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∫ ξ, wigner φ x ξ * conj (wigner ψ x ξ)
      = ∫ y, wignerKernel φ x y * conj (wignerKernel ψ x y) := by
  simpa only [RCLike.inner_apply, wigner] using
    SchwartzMap.integral_inner_fourier_fourier (wignerKernel ψ x) (wignerKernel φ x)

/-- The `y`-integral of `G(x + y/2) conj (G(x − y/2))` is twice the convolution of `G` with
`conj ∘ G` at `2x`. -/
theorem integral_mulConj_shift (G : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∫ y, G (x + y / 2) * conj (G (x - y / 2))
      = 2 * ((fun v => G v) ⋆[ContinuousLinearMap.mul ℝ ℂ] (fun v => conj (G v))) (2 * x) := by
  have h1 : (∫ y, G (x + y / 2) * conj (G (x - y / 2)))
      = ∫ y, (fun u => G u * conj (G (2 * x - u))) (x + 1 / 2 * y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show G (x + y / 2) * conj (G (x - y / 2))
        = G (x + 1 / 2 * y) * conj (G (2 * x - (x + 1 / 2 * y)))
    rw [show x + 1 / 2 * y = x + y / 2 by ring, show 2 * x - (x + y / 2) = x - y / 2 by ring]
  have h2 : ((fun v => G v) ⋆[ContinuousLinearMap.mul ℝ ℂ] (fun v => conj (G v))) (2 * x)
      = ∫ u, G u * conj (G (2 * x - u)) := by
    rw [convolution]
    simp [ContinuousLinearMap.mul_apply']
  rw [h1, integral_comp_affine_shift (fun u => G u * conj (G (2 * x - u))) x (1 / 2), h2,
    show |(1 / 2 : ℝ)⁻¹| = (2 : ℝ) by norm_num]
  simp [Complex.real_smul]

/-- ★★★ **The overlap identity** (Moyal 1949): the phase-space overlap of two Wigner functions is
the squared modulus of the states' inner product, so nothing is lost in passing from the state to
its Wigner function. -/
theorem integral_integral_wigner_mul_conj (φ ψ : 𝓢(ℝ, ℂ)) :
    (∫ x, ∫ ξ, wigner φ x ξ * conj (wigner ψ x ξ))
      = (∫ v, φ v * conj (ψ v)) * conj (∫ v, φ v * conj (ψ v)) := by
  have hGint : Integrable (fun v => mulConj φ ψ v) := (mulConj φ ψ).integrable
  have hGconj : Integrable (fun v => conj (mulConj φ ψ v)) := by
    refine hGint.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (Complex.continuous_conj.comp (mulConj φ ψ).continuous).aestronglyMeasurable
    · simp
  have hstep : ∀ x : ℝ, (∫ ξ, wigner φ x ξ * conj (wigner ψ x ξ))
      = 2 * ((fun v => mulConj φ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj φ ψ v))) (2 * x) := by
    intro x
    rw [integral_wigner_mul_conj φ ψ x,
      show (∫ y, wignerKernel φ x y * conj (wignerKernel ψ x y))
          = ∫ y, mulConj φ ψ (x + y / 2) * conj (mulConj φ ψ (x - y / 2)) from
        integral_congr_ae (Filter.Eventually.of_forall fun y => wignerKernel_mul_conj φ ψ x y),
      integral_mulConj_shift (mulConj φ ψ) x]
  calc (∫ x, ∫ ξ, wigner φ x ξ * conj (wigner ψ x ξ))
      = ∫ x, 2 * ((fun v => mulConj φ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj φ ψ v))) (2 * x) :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = 2 * ∫ x, ((fun v => mulConj φ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj φ ψ v))) (2 * x) := integral_const_mul 2 _
    _ = 2 * (|(2 : ℝ)⁻¹| • ∫ t, ((fun v => mulConj φ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj φ ψ v))) t) := by
        rw [Measure.integral_comp_mul_left]
    _ = ∫ t, ((fun v => mulConj φ ψ v) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun v => conj (mulConj φ ψ v))) t := by
        rw [show |(2 : ℝ)⁻¹| = (2⁻¹ : ℝ) by norm_num]
        simp [Complex.real_smul]
    _ = (∫ v, mulConj φ ψ v) * ∫ v, conj (mulConj φ ψ v) := by
        rw [MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℂ) hGint hGconj]
        simp [ContinuousLinearMap.mul_apply']
    _ = (∫ v, φ v * conj (ψ v)) * conj (∫ v, φ v * conj (ψ v)) := by
        rw [integral_conj]
        simp only [mulConj_apply]

/-- ★★ **The purity form**: the phase-space square of a Wigner function is the square of the
state's mass. -/
theorem integral_integral_wigner_sq (ψ : 𝓢(ℝ, ℂ)) :
    (∫ x, ∫ ξ, wigner ψ x ξ * wigner ψ x ξ)
      = (∫ v, (‖ψ v‖ : ℂ) ^ 2) * ∫ v, (‖ψ v‖ : ℂ) ^ 2 := by
  have h := integral_integral_wigner_mul_conj ψ ψ
  simp only [conj_wigner] at h
  rw [h]
  have hmass : (∫ v, ψ v * conj (ψ v)) = ∫ v, (‖ψ v‖ : ℂ) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show ψ v * conj (ψ v) = (‖ψ v‖ : ℂ) ^ 2
    rw [Complex.mul_conj']
  rw [hmass]
  congr 1
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

/-! ### Weyl quantisation and the expectation formula -/

/-- A uniform bound for a Schwartz function. -/
theorem exists_norm_le (ψ : 𝓢(ℝ, ℂ)) : ∃ C, ∀ v, ‖ψ v‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := ψ.decay 0 0
  refine ⟨C, fun v => ?_⟩
  have h := hC v
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h
  exact h

/-- Plancherel in product form: `∫ 𝓕 f conj (𝓕 g) = ∫ f conj g`. -/
theorem integral_fourier_mul_conj (f g : 𝓢(ℝ, ℂ)) :
    ∫ ξ, 𝓕 f ξ * conj (𝓕 g ξ) = ∫ y, f y * conj (g y) := by
  simpa only [RCLike.inner_apply] using SchwartzMap.integral_inner_fourier_fourier g f

/-- **The Weyl operator of a symbol given in kernel form**: `b u` is the Fourier transform, in the
frequency slot, of the symbol's slice at the midpoint `u`, and the operator is the integral against
the kernel `b ((x + y)/2) (x − y)`. -/
noncomputable def weylOp (b : ℝ → 𝓢(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∫ y, b ((x + y) / 2) (x - y) * ψ y

/-- **The symbol** of a Weyl operator presented in kernel form. -/
noncomputable def weylSymbol (b : ℝ → 𝓢(ℝ, ℂ)) (u ξ : ℝ) : ℂ := 𝓕 (b u) ξ

/-- After the substitution `y = 2u − x` the Weyl expectation's integrand is dominated by a product
of integrable functions of the two variables separately, hence is integrable on the plane. -/
theorem integrable_weylPair (b : ℝ → 𝓢(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ))
    (hbc : Continuous fun p : ℝ × ℝ => b p.1 p.2)
    {M : ℝ → ℝ} (hM : Integrable M) (hbM : ∀ u w, ‖b u w‖ ≤ M u) :
    Integrable
      (Function.uncurry fun x u : ℝ => conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := exists_norm_le ψ
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hmaj : Integrable (fun p : ℝ × ℝ => ‖ψ p.1‖ * (M p.2 * C)) (volume.prod volume) :=
    (ψ.integrable.norm).mul_prod (hM.mul_const C)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have h1 : Continuous fun p : ℝ × ℝ => conj (ψ p.1) :=
      Complex.continuous_conj.comp (ψ.continuous.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × ℝ => b p.2 (2 * p.1 - 2 * p.2) := by
      refine hbc.comp (continuous_snd.prodMk ?_)
      exact (continuous_const.mul continuous_fst).sub (continuous_const.mul continuous_snd)
    have h3 : Continuous fun p : ℝ × ℝ => ψ (2 * p.2 - p.1) := by
      refine ψ.continuous.comp ?_
      exact (continuous_const.mul continuous_snd).sub continuous_fst
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable
  · have hb := hbM p.2 (2 * p.1 - 2 * p.2)
    have hψ := hC (2 * p.2 - p.1)
    have hMnn : 0 ≤ M p.2 := le_trans (norm_nonneg _) hb
    show ‖conj (ψ p.1) * (b p.2 (2 * p.1 - 2 * p.2) * ψ (2 * p.2 - p.1))‖
        ≤ ‖ψ p.1‖ * (M p.2 * C)
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul hb hψ (norm_nonneg _) hMnn

/-- The Weyl expectation's inner integral after the substitution `y = 2u − x`. -/
theorem conj_mul_weylOp_eq (b : ℝ → 𝓢(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    conj (ψ x) * weylOp b ψ x
      = 2 * ∫ u, conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)) := by
  have hsub := integral_comp_affine_shift
    (fun y => conj (ψ x) * (b ((x + y) / 2) (x - y) * ψ y)) (-x) 2
  have hpt : ∀ u : ℝ, (fun y => conj (ψ x) * (b ((x + y) / 2) (x - y) * ψ y)) (-x + 2 * u)
      = conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)) := by
    intro u
    show conj (ψ x) * (b ((x + (-x + 2 * u)) / 2) (x - (-x + 2 * u)) * ψ (-x + 2 * u)) = _
    rw [show (x + (-x + 2 * u)) / 2 = u by ring, show x - (-x + 2 * u) = 2 * x - 2 * u by ring,
      show -x + 2 * u = 2 * u - x by ring]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    show |(2 : ℝ)⁻¹| = (2⁻¹ : ℝ) by norm_num, Complex.real_smul] at hsub
  rw [weylOp, hsub, integral_const_mul]
  push_cast
  ring

/-- The inner `x`-integral, after the substitution `x = u + w/2`, is the Wigner kernel against the
symbol's slice. -/
theorem integral_weylPair_x (b : ℝ → 𝓢(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (∫ x, conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)))
      = 2⁻¹ * ∫ w, b u w * conj (wignerKernel ψ u w) := by
  have hsub := integral_comp_affine_shift
    (fun x => conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x))) u (1 / 2)
  have hpt : ∀ w : ℝ,
      (fun x => conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x))) (u + 1 / 2 * w)
        = b u w * conj (wignerKernel ψ u w) := by
    intro w
    show conj (ψ (u + 1 / 2 * w))
        * (b u (2 * (u + 1 / 2 * w) - 2 * u) * ψ (2 * u - (u + 1 / 2 * w))) = _
    rw [show 2 * (u + 1 / 2 * w) - 2 * u = w by ring,
      show 2 * u - (u + 1 / 2 * w) = u - w / 2 by ring,
      show u + 1 / 2 * w = u + w / 2 by ring, wignerKernel_apply]
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    show |(1 / 2 : ℝ)⁻¹| = (2 : ℝ) by norm_num, Complex.real_smul] at hsub
  rw [hsub]
  push_cast
  ring

/-- ★★★ **The Weyl expectation formula.** For a symbol presented in kernel form, with slices
dominated by an integrable function, the expectation of the Weyl operator in a state is the
phase-space average of the symbol against the state's Wigner function. So `W_ψ` carries every Weyl
expectation, not only the position and momentum ones. -/
theorem integral_conj_mul_weylOp (b : ℝ → 𝓢(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ))
    (hbc : Continuous fun p : ℝ × ℝ => b p.1 p.2)
    {M : ℝ → ℝ} (hM : Integrable M) (hbM : ∀ u w, ‖b u w‖ ≤ M u) :
    (∫ x, conj (ψ x) * weylOp b ψ x) = ∫ u, ∫ ξ, weylSymbol b u ξ * wigner ψ u ξ := by
  have hswap := MeasureTheory.integral_integral_swap (integrable_weylPair b ψ hbc hM hbM)
  calc (∫ x, conj (ψ x) * weylOp b ψ x)
      = ∫ x, 2 * ∫ u, conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => conj_mul_weylOp_eq b ψ x)
    _ = 2 * ∫ x, ∫ u, conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)) :=
        integral_const_mul 2 _
    _ = 2 * ∫ u, ∫ x, conj (ψ x) * (b u (2 * x - 2 * u) * ψ (2 * u - x)) := by rw [hswap]
    _ = 2 * ∫ u, 2⁻¹ * ∫ w, b u w * conj (wignerKernel ψ u w) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall fun u => integral_weylPair_x b ψ u)]
    _ = ∫ u, ∫ w, b u w * conj (wignerKernel ψ u w) := by
        rw [integral_const_mul]
        ring
    _ = ∫ u, ∫ ξ, weylSymbol b u ξ * wigner ψ u ξ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show (∫ w, b u w * conj (wignerKernel ψ u w))
            = ∫ ξ, weylSymbol b u ξ * wigner ψ u ξ
        rw [← integral_fourier_mul_conj (b u) (wignerKernel ψ u)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        show 𝓕 (b u) ξ * conj (𝓕 (wignerKernel ψ u) ξ) = weylSymbol b u ξ * wigner ψ u ξ
        rw [weylSymbol, show 𝓕 (wignerKernel ψ u) ξ = wigner ψ u ξ from rfl, conj_wigner]

end WignerFunction

end
