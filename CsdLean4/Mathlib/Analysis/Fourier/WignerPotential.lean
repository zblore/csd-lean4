/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WignerFree
public import CsdLean4.Mathlib.Analysis.Fourier.MoyalBracket

/-!
# The potential half, and the interacting Wigner equation

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #169 (out of ~~#64~~, last brick of the interacting Wigner equation).

Along the Schrödinger orbit `ψ_t = U(t)ψ₀` of a bounded real potential `V`, started in `dom H₀`,
for every `t > 0` and every phase-space point,

  `∂_t W_{ψ_t}(x, ξ) = −2πξ · ∂_x W_{ψ_t}(x, ξ) + moyalPotL2 V ψ_t ψ_t (x, ξ)`,

the Wigner (Moyal) evolution equation for `H = 2π²ξ² + V(x)` on `L²`. #167 gave
`∂_t W = W(−i(H₀+V)ψ, ψ) + W(ψ, −i(H₀+V)ψ)` and #168 the `H₀` half; this file does the `V` half.

**The one real step is Plancherel on `L²`.** The `L²` Wigner function of #167 is defined in the
momentum form, `W(φ, ψ)(x, ξ) = 2 ⟪ φ̂(ξ − ·), e(2x·) ψ̂(ξ + ·) ⟫`, because `H₀` is a multiplier
there; a potential is a multiplier in the position form,
`W_pos(φ, ψ)(x, ξ) = 2 ⟪ φ(x − ·), e(−2ξ·) ψ(x + ·) ⟫`. The two forms are the same function
(★★★ `wignerPos_eq_wignerL2`): both are continuous sesquilinear forms on `L² × L²`, and they agree
on Schwartz states — where both are the cross Wigner function `wigner₂` of `MoyalBracket.lean`, by
the Plancherel symmetry ★★ `wigner₂_fourier`, the cross form of `Wigner.lean`'s `wigner_fourier` —
and Schwartz states are dense (`SchwartzMap.denseRange_toLpCLM`). No Fourier transform of a
translate or a modulation is computed on `L²`.

* `WignerFunction.posRight`, ★ `wignerPos`, `wignerPos_eq_integral`,
  `integrable_wignerPos_integrand` — the position form, an inner product of continuous linear
  images of the states, like the momentum form;
* `WignerFunction.wignerL2_eq_wignerPos_fourier` — the momentum form **is** the position form of
  the transforms at `(ξ, −x)`;
* `WignerFunction.wignerPos_toLp`, ★★ `wigner₂_fourier`, `wignerL2_toLp₂` — on Schwartz states
  both forms are `wigner₂` (first slot conjugated);
* ★★★ `WignerFunction.wignerPos_eq_wignerL2` — **the `L²` Plancherel identity for the Wigner
  function**;
* ★ `WignerFunction.moyalPotL2`, ★★ `moyalPotL2_toLp` — the potential term on `L²`, equal to
  `moyalPot` on Schwartz states;
* ★★★ `WignerFunction.wignerPos_potential_add`, ★★★ `wignerL2_potential_add`,
  `wignerL2_potential_add_toLp` — **the potential half**:
  `W(−iVφ, ψ) + W(φ, −iVψ) = moyalPotL2 V φ ψ`;
* ★★★ `WignerFunction.hasDerivAt_wignerL2_schrodinger_eq` — **the interacting Wigner equation**
  along the orbit, assembled from #167, #168 and the potential half.

## Honest scope

* `V` enters as a bounded class `VL ∈ L^∞` almost everywhere equal to the real function `V`
  (the hypothesis form of `SchrodingerGroup.norm_schrodinger_apply`); `moyalPotL2` is stated with
  the real `V`, as `moyalPot` is. No regularity of `V` beyond boundedness is used — the classical
  limit of `moyalPot` (`MoyalBracket.lean`) is where `V'''` enters, and it is unchanged.
* The equation is for `W_{ψ_t} = wignerL2 ψ_t ψ_t` with `ψ_t ∈ L²` (the orbit leaves Schwartz
  space); for a Schwartz initial state the `t = 0` value is `wigner ψ₀` (`wignerL2_toLp`, #167).
* `∂_x W` is the derivative of #168, which exists because `ψ_t ∈ dom H₀`
  (`schrodinger_mem_freePositionOp_domain`).
* One dimension, as the whole Wigner line.

References: E. Wigner, Phys. Rev. 40 (1932) 749; J. E. Moyal, Proc. Cambridge Philos. Soc. 45
(1949) 99 §7; `WignerL2.lean` (#167), `WignerFree.lean` (#168), `MoyalBracket.lean` (`moyalPot`,
`wigner₂`), `Wigner.lean` (`wigner_fourier`), `PhaseGeneratorDomain.lean`
(`hasDerivAt_schrodinger_orbit`); `specs/BACKLOG.md` #169, ~~#64~~.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real Filter SchrodingerGroup
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal Topology

namespace WignerFunction

local notation "L2" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The position form -/

/-- `P_{x,ξ} ψ = e(−2ξ·) ψ(x + ·)`. -/
noncomputable def posRight (x ξ : ℝ) : L2 →L[ℂ] L2 :=
  (HeatSemigroup.potential (phaseLinf (-ξ))).comp (shiftAt x).toContinuousLinearMap

theorem coeFn_posRight (x ξ : ℝ) (ψ : L2) :
    posRight x ξ ψ =ᵐ[volume] fun v => (𝐞 (-(2 * v * ξ)) : ℂ) * ψ (x + v) := by
  filter_upwards [HeatSemigroup.coeFn_potential (phaseLinf (-ξ)) (shiftAt x ψ), coeFn_shiftAt x ψ,
    coeFn_phaseLinf (-ξ)] with v h1 h2 h3
  show HeatSemigroup.potential (phaseLinf (-ξ)) (shiftAt x ψ) v = _
  rw [h1, h2, h3, show 2 * -ξ * v = -(2 * v * ξ) by ring]

/-- ★ **The position form of the Wigner function of two `L²` states**:
`W_pos(φ, ψ)(x, ξ) = 2 ⟪ φ(x − ·), e(−2ξ·) ψ(x + ·) ⟫_{L²}`. -/
noncomputable def wignerPos (φ ψ : L2) (x ξ : ℝ) : ℂ :=
  2 * ⟪reflectAt x φ, posRight x ξ ψ⟫_ℂ

/-- The integral formula: `W_pos(φ, ψ)(x, ξ) = 2 ∫ e(−2vξ) ψ(x + v) conj φ(x − v) dv`. -/
theorem wignerPos_eq_integral (φ ψ : L2) (x ξ : ℝ) :
    wignerPos φ ψ x ξ
      = 2 * ∫ v : ℝ, (𝐞 (-(2 * v * ξ)) : ℂ) * (ψ (x + v) * conj (φ (x - v))) := by
  rw [wignerPos, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_reflectAt x φ, coeFn_posRight x ξ ψ] with v h1 h2
  rw [RCLike.inner_apply', h1, h2]
  ring

theorem integrable_wignerPos_integrand (φ ψ : L2) (x ξ : ℝ) :
    Integrable (fun v : ℝ => (𝐞 (-(2 * v * ξ)) : ℂ) * (ψ (x + v) * conj (φ (x - v)))) volume := by
  refine (L2.integrable_inner (reflectAt x φ) (posRight x ξ ψ)).congr ?_
  filter_upwards [coeFn_reflectAt x φ, coeFn_posRight x ξ ψ] with v h1 h2
  rw [RCLike.inner_apply', h1, h2]
  ring

/-- The momentum form is the position form of the transforms, with `(x, ξ) ↦ (ξ, −x)`:
`W(φ, ψ)(x, ξ) = W_pos(φ̂, ψ̂)(ξ, −x)`. -/
theorem wignerL2_eq_wignerPos_fourier (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 φ ψ x ξ
      = wignerPos (Lp.fourierTransformₗᵢ ℝ ℂ φ) (Lp.fourierTransformₗᵢ ℝ ℂ ψ) ξ (-x) := by
  show 2 * ⟪reflectAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ φ),
      HeatSemigroup.potential (phaseLinf x) (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ))⟫_ℂ
    = 2 * ⟪reflectAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ φ),
      HeatSemigroup.potential (phaseLinf (-(-x))) (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ))⟫_ℂ
  rw [neg_neg]

/-! ### On Schwartz states both forms are the cross Wigner function -/

/-- On Schwartz states the position form is the cross Wigner function of `MoyalBracket.lean`, with
the slots in inner-product order (the first slot conjugated). -/
theorem wignerPos_toLp (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wignerPos (φ.toLp 2) (ψ.toLp 2) x ξ = wigner₂ ψ φ x ξ := by
  rw [wignerPos_eq_integral, wigner₂_eq_integral]
  have hae : (fun v : ℝ => (𝐞 (-(2 * v * ξ)) : ℂ)
        * ((ψ.toLp 2 : L2) (x + v) * conj ((φ.toLp 2 : L2) (x - v))))
      =ᵐ[volume] fun v => (𝐞 (-(2 * v * ξ)) : ℂ) * (ψ (x + v) * conj (φ (x - v))) := by
    have h1 := (measurePreserving_add_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
      (ψ.coeFn_toLp 2 (volume : Measure ℝ))
    have h2 := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
      (φ.coeFn_toLp 2 (volume : Measure ℝ))
    filter_upwards [h1, h2] with v hv1 hv2
    simp only [Function.comp] at hv1 hv2
    rw [hv1, hv2]
  rw [integral_congr_ae hae]
  -- the substitution `y = 2v`
  have hsub := Measure.integral_comp_mul_left
    (fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ) * (ψ (x + y / 2) * conj (φ (x - y / 2)))) 2
  have h2 : (∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (ψ (x + y / 2) * conj (φ (x - y / 2))))
      = 2 * ∫ v : ℝ, (𝐞 (-(2 * v * ξ)) : ℂ)
          * (ψ (x + 2 * v / 2) * conj (φ (x - 2 * v / 2))) := by
    rw [hsub, Complex.real_smul, show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num]
    push_cast
    ring
  rw [h2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [show x + 2 * v / 2 = x + v by ring, show x - 2 * v / 2 = x - v by ring]

/-- ★★ **The Plancherel symmetry of the cross Wigner function**: `W(𝓕φ, 𝓕ψ)(ξ, −x) = W(φ, ψ)(x, ξ)`
on Schwartz states — the cross form of `wigner_fourier`. -/
theorem wigner₂_fourier (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wigner₂ (𝓕 φ) (𝓕 ψ) ξ (-x) = wigner₂ φ ψ x ξ := by
  set f : 𝓢(ℝ, ℂ) := modCLM (-(ξ / 2)) (affineCLM x half_ne_zero' φ) with hf
  set g : 𝓢(ℝ, ℂ) := modCLM (ξ / 2) (affineCLM x neg_half_ne_zero' ψ) with hg
  have hP := SchwartzMap.integral_inner_fourier_fourier g f
  simp only [RCLike.inner_apply] at hP
  -- `hP : ∫ η, 𝓕 f η * conj (𝓕 g η) = ∫ y, f y * conj (g y)`
  have hR : ∫ y, f y * conj (g y) = wigner₂ φ ψ x ξ := by
    rw [wigner₂_eq_integral]
    congr 1
    funext y
    simp only [hf, hg, modCLM_apply, affineCLM_apply, map_mul, conj_fourierChar]
    rw [show x + 1 / 2 * y = x + y / 2 by ring, show x + -1 / 2 * y = x - y / 2 by ring]
    have hc : (𝐞 (-(ξ / 2) * y) : ℂ) * 𝐞 (-(ξ / 2 * y)) = 𝐞 (-(y * ξ)) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    linear_combination (φ (x + y / 2) * conj (ψ (x - y / 2))) * hc
  have hfF : ∀ η, 𝓕 f η
      = |(1 / 2 : ℝ)⁻¹| • ((𝐞 (x * ((η + ξ / 2) / (1 / 2))) : ℂ)
          * 𝓕 (⇑φ) ((η + ξ / 2) / (1 / 2))) := by
    intro η
    have hf' : ⇑f = fun y => (𝐞 (-(ξ / 2) * y) : ℂ) * (fun y' => φ (x + 1 / 2 * y')) y := by
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
    * (𝓕 (⇑φ) (ξ + η / 2) * conj (𝓕 (⇑ψ) (ξ - η / 2))) with hG
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
    linear_combination (4 * (𝓕 (⇑φ) (ξ + 4 * η / 2) * conj (𝓕 (⇑ψ) (ξ - 4 * η / 2)))) * hc
  have hsub := Measure.integral_comp_mul_left G 4
  have hL : ∫ η, 𝓕 f η * conj (𝓕 g η) = wigner₂ (𝓕 φ) (𝓕 ψ) ξ (-x) := by
    rw [wigner₂_eq_integral]
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

/-- On Schwartz states the momentum form is the cross Wigner function too (first slot
conjugated). -/
theorem wignerL2_toLp₂ (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wignerL2 (φ.toLp 2) (ψ.toLp 2) x ξ = wigner₂ ψ φ x ξ := by
  have hFφ : Lp.fourierTransformₗᵢ ℝ ℂ (φ.toLp 2 volume) = (𝓕 φ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq φ
  have hFψ : Lp.fourierTransformₗᵢ ℝ ℂ (ψ.toLp 2 volume) = (𝓕 ψ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq ψ
  rw [wignerL2_eq_wignerPos_fourier, hFφ, hFψ, wignerPos_toLp, wigner₂_fourier]

/-! ### The `L²` Plancherel identity -/

theorem continuous_wignerPos (x ξ : ℝ) :
    Continuous fun q : L2 × L2 => wignerPos q.1 q.2 x ξ :=
  continuous_const.mul (((reflectAt x).continuous.comp continuous_fst).inner
    ((posRight x ξ).continuous.comp continuous_snd))

theorem continuous_wignerL2 (x ξ : ℝ) :
    Continuous fun q : L2 × L2 => wignerL2 q.1 q.2 x ξ :=
  continuous_const.mul (((wignerLeft ξ).continuous.comp continuous_fst).inner
    ((wignerRight x ξ).continuous.comp continuous_snd))

/-- ★★★ **The `L²` Plancherel identity for the Wigner function**: the position form and the
momentum form agree on all of `L² × L²`. Both are continuous sesquilinear forms; they agree on
Schwartz states (`wignerPos_toLp`, `wignerL2_toLp₂`), which are dense. -/
theorem wignerPos_eq_wignerL2 (φ ψ : L2) (x ξ : ℝ) : wignerPos φ ψ x ξ = wignerL2 φ ψ x ξ := by
  refine DenseRange.induction_on₂
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure ℝ))
      ENNReal.ofNat_ne_top) ?_ ?_ φ ψ
  · exact isClosed_eq (continuous_wignerPos x ξ) (continuous_wignerL2 x ξ)
  · intro φ ψ
    simp only [SchwartzMap.toLpCLM_apply]
    rw [wignerPos_toLp, wignerL2_toLp₂]

/-- The integral formula of the momentum form, in position variables. -/
theorem wignerL2_eq_integral_pos (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 φ ψ x ξ
      = 2 * ∫ v : ℝ, (𝐞 (-(2 * v * ξ)) : ℂ) * (ψ (x + v) * conj (φ (x - v))) := by
  rw [← wignerPos_eq_wignerL2, wignerPos_eq_integral]

/-! ### The potential term on `L²` -/

/-- ★ **The potential term of the Wigner equation on `L²`**, for a real potential `V`: the position
integral against the symmetric difference `V(x + v) − V(x − v)`. It is `MoyalBracket.lean`'s
`moyalPot` in the variable `y = 2v` (`moyalPotL2_toLp`), extended to `L²` states and to two slots
(the first conjugated). -/
noncomputable def moyalPotL2 (V : ℝ → ℝ) (φ ψ : L2) (x ξ : ℝ) : ℂ :=
  2 * ∫ v : ℝ, (𝐞 (-(2 * v * ξ)) : ℂ)
    * (-Complex.I * ((V (x + v) - V (x - v) : ℝ) : ℂ) * (ψ (x + v) * conj (φ (x - v))))

/-- ★★ **On a Schwartz state, `moyalPotL2` is `moyalPot`.** -/
theorem moyalPotL2_toLp (V : ℝ → ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    moyalPotL2 V (ψ.toLp 2) (ψ.toLp 2) x ξ = moyalPot V ψ x ξ := by
  rw [moyalPotL2, moyalPot]
  have hae : (fun v : ℝ => (𝐞 (-(2 * v * ξ)) : ℂ)
        * (-Complex.I * ((V (x + v) - V (x - v) : ℝ) : ℂ)
          * ((ψ.toLp 2 : L2) (x + v) * conj ((ψ.toLp 2 : L2) (x - v)))))
      =ᵐ[volume] fun v => (𝐞 (-(2 * v * ξ)) : ℂ)
        * (-Complex.I * ((V (x + v) - V (x - v) : ℝ) : ℂ) * (ψ (x + v) * conj (ψ (x - v)))) := by
    have h1 := (measurePreserving_add_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
      (ψ.coeFn_toLp 2 (volume : Measure ℝ))
    have h2 := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
      (ψ.coeFn_toLp 2 (volume : Measure ℝ))
    filter_upwards [h1, h2] with v hv1 hv2
    simp only [Function.comp] at hv1 hv2
    rw [hv1, hv2]
  rw [integral_congr_ae hae]
  -- the substitution `y = 2v`
  have hsub := Measure.integral_comp_mul_left
    (fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)
      * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y)) 2
  have h2 : (∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ)
        * (-Complex.I * ((V (x + y / 2) - V (x - y / 2) : ℝ) : ℂ) * wignerKernel ψ x y))
      = 2 * ∫ v : ℝ, (𝐞 (-(2 * v * ξ)) : ℂ)
        * (-Complex.I * ((V (x + 2 * v / 2) - V (x - 2 * v / 2) : ℝ) : ℂ)
          * wignerKernel ψ x (2 * v)) := by
    rw [hsub, Complex.real_smul, show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num]
    push_cast
    ring
  rw [h2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [wignerKernel_apply, show x + 2 * v / 2 = x + v by ring, show x - 2 * v / 2 = x - v by ring]

/-- `(−i V φ)(y) = −i V(y) φ(y)` almost everywhere, for `VL` almost everywhere the real `V`. -/
theorem coeFn_neg_I_smul_potential {VL : Lp ℂ ∞ (volume : Measure ℝ)} {V : ℝ → ℝ}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun y => (V y : ℂ)) (φ : L2) :
    ((-Complex.I) • HeatSemigroup.potential VL φ : L2)
      =ᵐ[volume] fun y => -Complex.I * ((V y : ℂ) * φ y) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I) (HeatSemigroup.potential VL φ),
    HeatSemigroup.coeFn_potential VL φ, hVL] with y h1 h2 h3
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3]

/-! ### The potential half -/

/-- ★★★ **The potential half of the interacting Wigner equation**, position form: for a bounded
potential `VL` almost everywhere equal to the real `V`,
`W_pos(−iVφ, ψ) + W_pos(φ, −iVψ) = moyalPotL2 V φ ψ`. Pointwise under the position integral:
`conj(−i V(x−v)) + (−i V(x+v)) = −i (V(x+v) − V(x−v))` because `V` is real. -/
theorem wignerPos_potential_add {VL : Lp ℂ ∞ (volume : Measure ℝ)} {V : ℝ → ℝ}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun y => (V y : ℂ)) (φ ψ : L2) (x ξ : ℝ) :
    wignerPos ((-Complex.I) • HeatSemigroup.potential VL φ) ψ x ξ
        + wignerPos φ ((-Complex.I) • HeatSemigroup.potential VL ψ) x ξ
      = moyalPotL2 V φ ψ x ξ := by
  rw [wignerPos_eq_integral, wignerPos_eq_integral, moyalPotL2, ← mul_add,
    ← integral_add (integrable_wignerPos_integrand _ _ x ξ) (integrable_wignerPos_integrand _ _ x ξ)]
  congr 1
  have hA := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
    (coeFn_neg_I_smul_potential hVL φ)
  have hB := (measurePreserving_add_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae_eq_comp
    (coeFn_neg_I_smul_potential hVL ψ)
  refine integral_congr_ae ?_
  filter_upwards [hA, hB] with v h1 h2
  simp only [Function.comp] at h1 h2
  rw [h1, h2]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- ★★★ **The potential half**, momentum form — the form the orbit theorem of #167 produces — via
the `L²` Plancherel identity: `W(−iVφ, ψ) + W(φ, −iVψ) = moyalPotL2 V φ ψ`. -/
theorem wignerL2_potential_add {VL : Lp ℂ ∞ (volume : Measure ℝ)} {V : ℝ → ℝ}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun y => (V y : ℂ)) (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 ((-Complex.I) • HeatSemigroup.potential VL φ) ψ x ξ
        + wignerL2 φ ((-Complex.I) • HeatSemigroup.potential VL ψ) x ξ
      = moyalPotL2 V φ ψ x ξ := by
  rw [← wignerPos_eq_wignerL2, ← wignerPos_eq_wignerL2]
  exact wignerPos_potential_add hVL φ ψ x ξ

/-- The potential half on a Schwartz state, with `MoyalBracket.lean`'s `moyalPot` on the right:
`W(−iVψ, ψ) + W(ψ, −iVψ) = moyalPot V ψ`. -/
theorem wignerL2_potential_add_toLp {VL : Lp ℂ ∞ (volume : Measure ℝ)} {V : ℝ → ℝ}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun y => (V y : ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    wignerL2 ((-Complex.I) • HeatSemigroup.potential VL (ψ.toLp 2)) (ψ.toLp 2) x ξ
        + wignerL2 (ψ.toLp 2) ((-Complex.I) • HeatSemigroup.potential VL (ψ.toLp 2)) x ξ
      = moyalPot V ψ x ξ := by
  rw [wignerL2_potential_add hVL, moyalPotL2_toLp]

/-! ### The interacting Wigner equation -/

/-- ★★★ **The interacting Wigner equation.** Along the Schrödinger orbit `ψ_t = U(t)ψ₀` of a
bounded potential `VL` almost everywhere equal to the real `V`, started in `dom H₀`, for every
`t > 0` and every phase-space point `(x, ξ)`,

  `∂_t W_{ψ_t}(x, ξ) = −2πξ · ∂_x W_{ψ_t}(x, ξ) + moyalPotL2 V ψ_t ψ_t (x, ξ)`.

The free transport is #168's half, the potential term is `wignerL2_potential_add`, and the
left-hand side is #167's `∂_t W = W(−i(H₀+V)ψ, ψ) + W(ψ, −i(H₀+V)ψ)` split by sesquilinearity. -/
theorem hasDerivAt_wignerL2_schrodinger_eq (VL : Lp ℂ ∞ (volume : Measure ℝ)) {V : ℝ → ℝ}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun y => (V y : ℂ)) (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : L2) ∈ freePositionOp.domain) {t : ℝ} (ht : 0 < t) (x ξ : ℝ) :
    HasDerivAt
      (fun s => wignerL2 (schrodinger (measurable_freeSymbol (E := ℝ)) VL s (fourierL2.symm (f : L2)))
        (schrodinger (measurable_freeSymbol (E := ℝ)) VL s (fourierL2.symm (f : L2))) x ξ)
      (-(2 * π * ξ) * deriv (fun x => wignerL2
          (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)))
          (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))) x ξ) x
        + moyalPotL2 V (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)))
          (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))) x ξ) t := by
  have hmem := schrodinger_mem_freePositionOp_domain VL f h ht.le
  refine (hasDerivAt_wignerL2_schrodinger VL f h ht x ξ).congr_deriv ?_
  change wignerL2 ((-Complex.I) • (freePositionOp ⟨_, hmem⟩ + HeatSemigroup.potential VL
        (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))))) _ x ξ
      + wignerL2 _ ((-Complex.I) • (freePositionOp ⟨_, hmem⟩ + HeatSemigroup.potential VL
        (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))))) x ξ
    = _
  rw [smul_add, wignerL2_add_left, wignerL2_add_right]
  have hF := wignerL2_freePositionOp_add hmem hmem x ξ
  have hP := wignerL2_potential_add hVL
    (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2)))
    (schrodinger (measurable_freeSymbol (E := ℝ)) VL t (fourierL2.symm (f : L2))) x ξ
  linear_combination hF + hP

end WignerFunction

end
