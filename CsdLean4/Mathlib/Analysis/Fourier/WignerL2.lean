/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.Wigner
public import CsdLean4.Mathlib.Analysis.Semigroup.PhaseGeneratorDomain

/-!
# The Wigner function on `L²`, and its time derivative along the interacting orbit

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #167 (out of ~~#64~~: the interacting Wigner equation, first brick).

The corpus's Wigner function (`Wigner.lean`) is defined on Schwartz functions, where the kernel
`y ↦ ψ(x + y/2) conj ψ(x − y/2)` is itself Schwartz. The interacting Schrödinger orbit `U(t)ψ`
of #129/#154 lives in `L²` (in `dom H₀`, operator-theoretically), not in Schwartz space, so to
differentiate `W_{U(t)ψ}` in `t` the Wigner function has to exist on `L²` first. It does, in the
**momentum form**: for `φ, ψ ∈ L²(ℝ)`,

  `W(φ, ψ)(x, ξ) = 2 ∫ e(2xu) · ψ̂(ξ + u) · conj φ̂(ξ − u) du = 2 ⟪ L_ξ φ, R_{x,ξ} ψ ⟫_{L²}`,

where `L_ξ φ = φ̂(ξ − ·)` and `R_{x,ξ} ψ = e(2x·) ψ̂(ξ + ·)` are **isometries of `L²`** (Plancherel,
a reflection/translation of Lebesgue measure, and a unimodular multiplier). Writing `W` as an inner
product of two continuous linear images of the states is what makes everything else one line:
the integrand is integrable, `|W| ≤ 2‖φ‖‖ψ‖`, and `t ↦ W(ψ_t, ψ_t)` is differentiable whenever
`t ↦ ψ_t` is differentiable in `L²`, with `∂_t W = W(ψ̇, ψ) + W(ψ, ψ̇)`.

* `WignerFunction.reflectAt`, `shiftAt`, `phaseLinf`, `wignerLeft`, `wignerRight` — the two
  continuous linear maps, with their almost-everywhere values;
* ★ `WignerFunction.wignerL2`, `wignerL2_eq_integral` — **the Wigner function of two `L²` states**,
  and its integral formula;
* ★ `WignerFunction.norm_wignerL2_le` — `‖W(φ, ψ)(x, ξ)‖ ≤ 2 ‖φ‖ ‖ψ‖`;
* ★★ `WignerFunction.wignerL2_toLp` — **on a Schwartz state it is the Wigner function of
  `Wigner.lean`** (through `wigner_fourier`, Mathlib's `SchwartzMap.toLp_fourier_eq`, and the
  substitution `y = 2u`);
* ★★ `WignerFunction.hasDerivAt_wignerL2` — **the chain rule**: along any `L²`-differentiable
  path, `∂_t W(ψ_t, ψ_t) = W(ψ̇_t, ψ_t) + W(ψ_t, ψ̇_t)` pointwise in `(x, ξ)`;
* ★★★ `WignerFunction.hasDerivAt_wignerL2_schrodinger` — **along the interacting orbit**
  `ψ_t = U(t)ψ₀` (bounded real potential, `ψ₀ ∈ dom H₀`), for every `t > 0`,
  `∂_t W_{ψ_t}(x, ξ) = W(−i(H₀ + V)ψ_t, ψ_t) + W(ψ_t, −i(H₀ + V)ψ_t)`, with `H₀` acting on the
  orbit point — the interacting Wigner equation in its first, operator form.

## Honest scope

* The two halves of the right-hand side are not yet identified: `W(−iH₀ψ, ψ) + W(ψ, −iH₀ψ)
  = −2πξ ∂_x W_ψ` for `ψ ∈ dom H₀` is #168, and `W(−iVψ, ψ) + W(ψ, −iVψ) = moyalPot V ψ` (the
  `Moyal` term of `MoyalBracket.lean`) is #169; together they give
  `∂_t W = −2πξ ∂_x W + moyalPot`, the equation ~~#64~~ named.
* `V` enters as an `L^∞` class (`potential VL`), as in #129/#154; the orbit is the Dyson/Trotter
  propagator `schrodinger` of `BoundedPerturbation.lean`.
* One space dimension.

References: E. Wigner, Phys. Rev. 40 (1932) 749; `Wigner.lean` (`wigner`, `wigner_fourier`),
`PhaseGeneratorDomain.lean` (#154, `hasDerivAt_schrodinger_orbit`), `MoyalBracket.lean`,
`WignerEvolution.lean`; Mathlib `Analysis/Fourier/LpSpace.lean` (`Lp.fourierTransformₗᵢ`,
`SchwartzMap.toLp_fourier_eq`); `specs/BACKLOG.md` #167, ~~#64~~.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real Filter
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal Topology

namespace WignerFunction

local notation "L2" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The two continuous linear maps -/

/-- `u ↦ f(ξ − u)`, an isometry of `L²`. -/
noncomputable def reflectAt (ξ : ℝ) : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => ξ - u) (Measure.measurePreserving_sub_left volume ξ)

/-- `u ↦ f(ξ + u)`, an isometry of `L²`. -/
noncomputable def shiftAt (ξ : ℝ) : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => ξ + u) (measurePreserving_add_left volume ξ)

theorem coeFn_reflectAt (ξ : ℝ) (f : L2) : reflectAt ξ f =ᵐ[volume] fun u => f (ξ - u) :=
  Lp.coeFn_compMeasurePreserving f _

theorem coeFn_shiftAt (ξ : ℝ) (f : L2) : shiftAt ξ f =ᵐ[volume] fun u => f (ξ + u) :=
  Lp.coeFn_compMeasurePreserving f _

theorem continuous_phase (x : ℝ) : Continuous fun u : ℝ => (𝐞 (2 * x * u) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))

theorem memLp_top_phase (x : ℝ) :
    MemLp (fun u : ℝ => (𝐞 (2 * x * u) : ℂ)) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_phase x).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun u => by simp)

/-- The unimodular phase `u ↦ e(2xu)` as an `L^∞` class. -/
noncomputable def phaseLinf (x : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) := (memLp_top_phase x).toLp _

theorem coeFn_phaseLinf (x : ℝ) : phaseLinf x =ᵐ[volume] fun u => (𝐞 (2 * x * u) : ℂ) :=
  MemLp.coeFn_toLp _

theorem norm_phaseLinf_le (x : ℝ) : ‖phaseLinf x‖ ≤ 1 := by
  rw [phaseLinf, Lp.norm_toLp, eLpNorm_exponent_top]
  have h : eLpNormEssSup (fun u : ℝ => (𝐞 (2 * x * u) : ℂ)) volume ≤ ENNReal.ofReal 1 :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun u => by simp)
  calc (eLpNormEssSup (fun u : ℝ => (𝐞 (2 * x * u) : ℂ)) volume).toReal
      ≤ (ENNReal.ofReal 1).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 1 := by simp
  exact (continuous_phase x).aestronglyMeasurable

/-- `L_ξ φ = φ̂(ξ − ·)`. -/
noncomputable def wignerLeft (ξ : ℝ) : L2 →L[ℂ] L2 :=
  (reflectAt ξ).toContinuousLinearMap.comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- `R_{x,ξ} ψ = e(2x·) ψ̂(ξ + ·)`. -/
noncomputable def wignerRight (x ξ : ℝ) : L2 →L[ℂ] L2 :=
  (HeatSemigroup.potential (phaseLinf x)).comp ((shiftAt ξ).toContinuousLinearMap.comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem coeFn_wignerLeft (ξ : ℝ) (φ : L2) :
    wignerLeft ξ φ =ᵐ[volume] fun u => (Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u) :=
  coeFn_reflectAt ξ _

theorem coeFn_wignerRight (x ξ : ℝ) (ψ : L2) :
    wignerRight x ξ ψ =ᵐ[volume]
      fun u => (𝐞 (2 * x * u) : ℂ) * (Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) := by
  filter_upwards [HeatSemigroup.coeFn_potential (phaseLinf x)
    ((shiftAt ξ) (Lp.fourierTransformₗᵢ ℝ ℂ ψ)), coeFn_shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ),
    coeFn_phaseLinf x] with u h1 h2 h3
  show HeatSemigroup.potential (phaseLinf x) ((shiftAt ξ) (Lp.fourierTransformₗᵢ ℝ ℂ ψ)) u = _
  rw [h1, h2, h3]

theorem norm_wignerLeft_apply (ξ : ℝ) (φ : L2) : ‖wignerLeft ξ φ‖ = ‖φ‖ := by
  show ‖reflectAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ φ)‖ = ‖φ‖
  rw [(reflectAt ξ).norm_map, (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map]

theorem norm_wignerRight_apply_le (x ξ : ℝ) (ψ : L2) : ‖wignerRight x ξ ψ‖ ≤ ‖ψ‖ := by
  show ‖HeatSemigroup.potential (phaseLinf x) (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ))‖ ≤ ‖ψ‖
  calc ‖HeatSemigroup.potential (phaseLinf x) (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ))‖
      ≤ ‖HeatSemigroup.potential (phaseLinf x)‖ * ‖shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := by
        rw [(shiftAt ξ).norm_map, (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map]
        gcongr
        exact (HeatSemigroup.norm_potential_le _).trans (norm_phaseLinf_le x)
    _ = ‖ψ‖ := one_mul _

/-! ### The Wigner function of two `L²` states -/

/-- ★ **The Wigner function of two `L²` states**, in the momentum form
`W(φ, ψ)(x, ξ) = 2 ⟪ φ̂(ξ − ·), e(2x·) ψ̂(ξ + ·) ⟫_{L²}`. -/
noncomputable def wignerL2 (φ ψ : L2) (x ξ : ℝ) : ℂ :=
  2 * ⟪wignerLeft ξ φ, wignerRight x ξ ψ⟫_ℂ

/-- The integral formula: `W(φ, ψ)(x, ξ) = 2 ∫ e(2xu) ψ̂(ξ + u) conj φ̂(ξ − u) du`. -/
theorem wignerL2_eq_integral (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 φ ψ x ξ
      = 2 * ∫ u : ℝ, (𝐞 (2 * x * u) : ℂ)
          * ((Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) * conj ((Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u))) := by
  rw [wignerL2, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_wignerLeft ξ φ, coeFn_wignerRight x ξ ψ] with u h1 h2
  rw [RCLike.inner_apply', h1, h2]
  ring

/-- ★ `‖W(φ, ψ)(x, ξ)‖ ≤ 2 ‖φ‖ ‖ψ‖`. -/
theorem norm_wignerL2_le (φ ψ : L2) (x ξ : ℝ) : ‖wignerL2 φ ψ x ξ‖ ≤ 2 * ‖φ‖ * ‖ψ‖ := by
  rw [wignerL2, norm_mul, Complex.norm_two, mul_assoc]
  gcongr
  calc ‖⟪wignerLeft ξ φ, wignerRight x ξ ψ⟫_ℂ‖
      ≤ ‖wignerLeft ξ φ‖ * ‖wignerRight x ξ ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖φ‖ * ‖ψ‖ := by
        rw [norm_wignerLeft_apply]
        gcongr
        exact norm_wignerRight_apply_le x ξ ψ

/-! ### On Schwartz states it is the Wigner function -/

/-- ★★ **On a Schwartz state the `L²` Wigner function is the Wigner function of `Wigner.lean`.** -/
theorem wignerL2_toLp (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wignerL2 (ψ.toLp 2) (ψ.toLp 2) x ξ = wigner ψ x ξ := by
  have hF : Lp.fourierTransformₗᵢ ℝ ℂ (ψ.toLp 2 volume) = (𝓕 ψ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq ψ
  rw [wignerL2_eq_integral, ← wigner_fourier, wigner_eq_integral, hF]
  -- the integrand of the `L²` side, with the class replaced by the function
  have hae : (fun u : ℝ => (𝐞 (2 * x * u) : ℂ)
        * (((𝓕 ψ).toLp 2 : L2) (ξ + u) * conj (((𝓕 ψ).toLp 2 : L2) (ξ - u))))
      =ᵐ[volume] fun u => (𝐞 (2 * x * u) : ℂ) * ((𝓕 ψ) (ξ + u) * conj ((𝓕 ψ) (ξ - u))) := by
    have h1 := (measurePreserving_add_left (volume : Measure ℝ) ξ).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 ψ).coeFn_toLp 2 (volume : Measure ℝ))
    have h2 := (Measure.measurePreserving_sub_left (volume : Measure ℝ) ξ).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 ψ).coeFn_toLp 2 (volume : Measure ℝ))
    filter_upwards [h1, h2] with u hu1 hu2
    simp only [Function.comp] at hu1 hu2
    rw [hu1, hu2]
  rw [integral_congr_ae hae]
  -- the substitution `y = 2u`
  have hsub := Measure.integral_comp_mul_left
    (fun y : ℝ => (𝐞 (-(y * -x)) : ℂ) * ((𝓕 ψ) (ξ + y / 2) * conj ((𝓕 ψ) (ξ - y / 2)))) 2
  have h2 : (∫ y : ℝ, (𝐞 (-(y * -x)) : ℂ) * ((𝓕 ψ) (ξ + y / 2) * conj ((𝓕 ψ) (ξ - y / 2))))
      = 2 * ∫ u : ℝ, (𝐞 (-(2 * u * -x)) : ℂ)
          * ((𝓕 ψ) (ξ + 2 * u / 2) * conj ((𝓕 ψ) (ξ - 2 * u / 2))) := by
    rw [hsub, Complex.real_smul, show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num]
    push_cast
    ring
  rw [h2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [show -(2 * u * -x) = 2 * x * u by ring, show ξ + 2 * u / 2 = ξ + u by ring,
    show ξ - 2 * u / 2 = ξ - u by ring]

/-! ### The chain rule -/

/-- ★★ **The chain rule for the Wigner function**: along an `L²`-differentiable path,
`∂_t W(ψ_t, ψ_t)(x, ξ) = W(ψ̇_t, ψ_t)(x, ξ) + W(ψ_t, ψ̇_t)(x, ξ)`. -/
theorem hasDerivAt_wignerL2 {ψ : ℝ → L2} {ψ' : L2} {t : ℝ} (hψ : HasDerivAt ψ ψ' t) (x ξ : ℝ) :
    HasDerivAt (fun s => wignerL2 (ψ s) (ψ s) x ξ)
      (wignerL2 ψ' (ψ t) x ξ + wignerL2 (ψ t) ψ' x ξ) t := by
  have h1 : HasDerivAt (fun s => wignerLeft ξ (ψ s)) (wignerLeft ξ ψ') t :=
    ((wignerLeft ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hψ
  have h2 : HasDerivAt (fun s => wignerRight x ξ (ψ s)) (wignerRight x ξ ψ') t :=
    ((wignerRight x ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hψ
  have h := (h1.inner ℂ h2).const_mul (2 : ℂ)
  refine h.congr_deriv ?_
  simp only [wignerL2]
  ring

/-! ### Along the interacting orbit -/

open SchrodingerGroup in
/-- ★★★ **The interacting Wigner equation, operator form.** Along the Schrödinger orbit
`ψ_t = U(t)ψ₀` of a bounded real potential, started in `dom H₀`, for every `t > 0` and every
phase-space point,

  `∂_t W_{ψ_t}(x, ξ) = W(−i(H₀ + V)ψ_t, ψ_t)(x, ξ) + W(ψ_t, −i(H₀ + V)ψ_t)(x, ξ)`,

with `H₀ = freePositionOp` acting on the orbit point. -/
theorem hasDerivAt_wignerL2_schrodinger (VL : Lp ℂ ∞ (volume : Measure ℝ))
    (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : L2) ∈ freePositionOp.domain) {t : ℝ} (ht : 0 < t) (x ξ : ℝ) :
    HasDerivAt
      (fun s => wignerL2 (schrodinger (measurable_freeSymbol (E := ℝ)) VL s (fourierL2.symm (f : L2)))
        (schrodinger (measurable_freeSymbol (E := ℝ)) VL s (fourierL2.symm (f : L2))) x ξ)
      (wignerL2
          ((-Complex.I) • ((freePositionOp.addCLM (HeatSemigroup.potential VL))
            ⟨schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)),
              schrodinger_mem_freePositionOp_domain VL f h ht.le⟩))
          (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))) x ξ
        + wignerL2 (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)))
          ((-Complex.I) • ((freePositionOp.addCLM (HeatSemigroup.potential VL))
            ⟨schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)),
              schrodinger_mem_freePositionOp_domain VL f h ht.le⟩)) x ξ) t :=
  hasDerivAt_wignerL2 (hasDerivAt_schrodinger_orbit VL f h ht) x ξ

end WignerFunction

end
