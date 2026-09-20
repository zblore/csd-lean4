/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.SchrodingerGroup
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The free Schrödinger group on Schwartz functions, and the Schrödinger equation

**Category:** 1-Mathlib (CSD-free; staged for upstream).

`Analysis/Semigroup/SchrodingerGroup.lean` defines the unitary group `U_κ(t) = 𝓕⁻¹ e^{−itκ} 𝓕` on
`L²(E)` and never writes a generator. This module (BACKLOG #43, FC-5″) writes it, on Schwartz
functions, where Mathlib's Fourier calculus is available:

* **the phase `e^{−itκ}` of a symbol of temperate growth has temperate growth**
  (`hasTemperateGrowth_phaseFun`; `s ↦ e^{is}` has all its derivatives unimodular), so the
  multiplier is Mathlib's `SchwartzMap.fourierMultiplierCLM` and `U_κ(t)` **preserves Schwartz
  space**: ★ `fourierGroup_toLp`, `U_κ(t) (f.toLp 2) = (𝓕⁻¹ (e^{−itκ} · 𝓕 f)).toLp 2`;
* **the kinetic energy operator** `kineticOp = fourierMultiplierCLM (2π²ξ²)` **is** `−½ Δ`
  (★ `kineticOp_eq_laplacian`, from Mathlib's `laplacian_eq_fourierMultiplierCLM`) — the
  identification of `freeSchrodinger` with the differential operator `−½ d²/dx²`;
* ★★ `hasDerivAt_freeSchrodinger` — **the free Schrödinger equation** `i ∂_t ψ = −½ Δ ψ` holds in
  `L²` for `ψ(t) = e^{−itH₀} f`, `f` Schwartz: `∂_t (U₀(t) f) = −i H₀ (U₀(t) f)` at every `t`. The
  derivative at `0` is a dominated convergence for the difference quotient of the phase
  (`|(e^{−itκ} − 1)/t| ≤ |κ|`), lifted through the Fourier isometry; the group law moves it to
  every `t`. `hasDerivAt_fourierGroup_toLp` is the same for any dispersion relation `κ` of
  temperate growth: `∂_t U_κ(t) f = −i κ(D) (U_κ(t) f)`.

## Honest scope

⚠️ The derivative is taken in `L²` (the strong derivative of the orbit), for Schwartz initial data;
the statement in the Schwartz topology is not made. The action on a Gaussian packet — the packet
spreading into a Gaussian of complex variance — is `Analysis/Semigroup/GaussianPacket.lean` (FC-5‴,
BACKLOG #48). The space `E` is any finite-dimensional real inner product space (`H₀ = −½ Δ` on
`ℝᵈ`).

References: M. Reed, B. Simon, *Methods of Modern Mathematical Physics* II §IX.7;
`Analysis/Semigroup/SchrodingerGroup.lean` (FC-5); `specs/feynman-continuum-scoping.md` §5;
`specs/BACKLOG.md` #43; `specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped ENNReal NNReal Topology Nat SchwartzMap FourierTransform Laplacian
open MeasureTheory Filter SchrodingerGroup

namespace SchrodingerGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L²(E, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-! ### Temperate growth of a real phase -/

theorem hasDerivAt_exp_mul_I (s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (↑s * Complex.I)) (Complex.exp (↑s * Complex.I) * Complex.I)
      s := by
  have h := (Complex.hasDerivAt_exp (↑s * Complex.I)).comp (↑s : ℂ)
    ((hasDerivAt_id (↑s : ℂ)).mul_const Complex.I)
  simpa using h.comp_ofReal

theorem iteratedDeriv_exp_mul_I (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => Complex.exp (↑s * Complex.I))
      = fun s : ℝ => Complex.I ^ n * Complex.exp (↑s * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [((hasDerivAt_exp_mul_I s).const_mul (Complex.I ^ n)).deriv]
    ring

/-- `s ↦ e^{is}` has temperate growth: all its derivatives are unimodular. -/
theorem hasTemperateGrowth_exp_mul_I :
    Function.HasTemperateGrowth (fun s : ℝ => Complex.exp (↑s * Complex.I)) := by
  refine ⟨?_, fun n => ⟨0, 1, fun s => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_mul_I]
    simp [Complex.norm_exp_ofReal_mul_I]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- ★ **The phase `e^{−itκ}` of a symbol of temperate growth has temperate growth.** -/
theorem hasTemperateGrowth_phaseFun {κ : E → ℝ} (hκ : Function.HasTemperateGrowth κ) (t : ℝ) :
    Function.HasTemperateGrowth (phaseFun κ t) := by
  have h : phaseFun κ t = (fun s : ℝ => Complex.exp (↑s * Complex.I)) ∘ fun ξ => -(t * κ ξ) := by
    funext ξ
    rfl
  rw [h]
  refine hasTemperateGrowth_exp_mul_I.comp ?_
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasTemperateGrowth_freeSymbol : Function.HasTemperateGrowth (freeSymbol (E := E)) :=
  (Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)

/-! ### The group on Schwartz space -/

/-- The unitary group `U_κ` on Schwartz space: Mathlib's Fourier multiplier with symbol
`e^{−itκ}`. -/
noncomputable def fourierGroupS (κ : E → ℝ) (t : ℝ) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (phaseFun κ t)

/-- The free Schrödinger group on Schwartz space. -/
noncomputable def freeSchrodingerS (t : ℝ) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  fourierGroupS (freeSymbol (E := E)) t

variable {κ : E → ℝ} (hκm : Measurable κ) (hκ : Function.HasTemperateGrowth κ)
include hκm hκ

/-- On Schwartz functions the `L²` phase group is multiplication by the phase. -/
theorem phaseGroup_toLp (t : ℝ) (ψ : 𝓢(E, ℂ)) :
    phaseGroup hκm t (ψ.toLp 2) = (SchwartzMap.smulLeftCLM ℂ (phaseFun κ t) ψ).toLp 2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_phaseGroup hκm t (ψ.toLp 2), ψ.coeFn_toLp 2,
    (SchwartzMap.smulLeftCLM ℂ (phaseFun κ t) ψ).coeFn_toLp 2] with x h1 h2 h3
  rw [h1, h2, h3, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phaseFun hκ t),
    smul_eq_mul]

/-- ★ **The unitary group preserves Schwartz space**:
`U_κ(t) (f.toLp 2) = (𝓕⁻¹ (e^{−itκ} · 𝓕 f)).toLp 2`. -/
theorem fourierGroup_toLp (t : ℝ) (f : 𝓢(E, ℂ)) :
    fourierGroup hκm t (f.toLp 2) = (fourierGroupS κ t f).toLp 2 := by
  rw [fourierGroup_apply, fourierGroupS, SchwartzMap.fourierMultiplierCLM_apply]
  have h1 : fourierL2 (f.toLp 2) = (𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq f
  have h2 : ∀ ψ : 𝓢(E, ℂ), fourierL2.symm (ψ.toLp 2) = (𝓕⁻ ψ).toLp 2 := fun ψ =>
    SchwartzMap.toLp_fourierInv_eq ψ
  rw [h1, phaseGroup_toLp hκm hκ t, h2]

omit hκm hκ in
theorem freeSchrodinger_toLp (t : ℝ) (f : 𝓢(E, ℂ)) :
    freeSchrodinger t (f.toLp 2) = (freeSchrodingerS t f).toLp 2 :=
  fourierGroup_toLp (measurable_freeSymbol (E := E)) hasTemperateGrowth_freeSymbol t f

/-! ### The generator -/

omit hκm hκ in
/-- The kinetic energy operator `H₀ = −½ d²/dx²` on Schwartz functions, as the Fourier multiplier
of the free symbol `2π²ξ²`. -/
noncomputable def kineticOp : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
  SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ (freeSymbol (E := E))

omit hκm hκ in
/-- ★ **`H₀ = −½ Δ`** on Schwartz functions, from Mathlib's `laplacian_eq_fourierMultiplierCLM`. -/
theorem kineticOp_eq_laplacian (f : 𝓢(E, ℂ)) : kineticOp f = (-(1 / 2 : ℝ)) • Δ f := by
  have hsym : freeSymbol (E := E) = (2 * Real.pi ^ 2) • fun ξ : E => ‖ξ‖ ^ 2 := by
    funext ξ
    simp [freeSymbol]
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM, smul_smul, kineticOp, hsym,
    SchwartzMap.fourierMultiplierCLM_smul (Function.hasTemperateGrowth_norm_sq E), smul_apply]
  congr 1
  ring

/-! ### The Schrödinger equation -/

omit hκm hκ [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The difference quotient of the phase is bounded by `2|κ|`. -/
theorem norm_phaseQuot_le (t : ℝ) (x : E) :
    ‖((t⁻¹ : ℝ) : ℂ) * (phaseFun κ t x - 1) + Complex.I * (κ x : ℂ)‖ ≤ 2 * |κ x| := by
  refine le_trans (norm_add_le _ _) ?_
  have h2 : ‖Complex.I * (κ x : ℂ)‖ = |κ x| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
    linarith [abs_nonneg (κ x)]
  · have h1 : ‖((t⁻¹ : ℝ) : ℂ) * (phaseFun κ t x - 1)‖ ≤ |κ x| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
      have hexp : ‖phaseFun κ t x - 1‖ ≤ |t * κ x| := by
        rw [phaseFun, mul_comm]
        refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
        rw [Real.norm_eq_abs, abs_neg]
      calc |t|⁻¹ * ‖phaseFun κ t x - 1‖ ≤ |t|⁻¹ * |t * κ x| := by gcongr
        _ = |κ x| := by
            rw [abs_mul, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr ht), one_mul]
    linarith

omit hκm hκ [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The difference quotient of the phase tends to `−iκ`. -/
theorem tendsto_phaseQuot (x : E) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) * (phaseFun κ t x - 1) + Complex.I * (κ x : ℂ))
      (𝓝[≠] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun t : ℝ => phaseFun κ t x) (-(Complex.I * (κ x : ℂ))) 0 := by
    have he : HasDerivAt (fun z : ℂ => Complex.exp (-(z * (κ x : ℂ)) * Complex.I))
        (Complex.exp (-(((0 : ℝ) : ℂ) * (κ x : ℂ)) * Complex.I) * (-(1 * (κ x : ℂ)) * Complex.I))
        ((0 : ℝ) : ℂ) :=
      (Complex.hasDerivAt_exp _).comp _
        ((((hasDerivAt_id _).mul_const (κ x : ℂ)).neg).mul_const Complex.I)
    have h := he.comp_ofReal
    refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
    · simp only [phaseFun]
      push_cast
      ring_nf
    · simp
      ring
  have h := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simp only [zero_add, phaseFun, zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero,
    Complex.real_smul] at h
  have := h.add_const (Complex.I * (κ x : ℂ))
  rw [neg_add_cancel] at this
  exact this.congr fun t => by simp [phaseFun]

/-- ★ **The strong derivative of the phase group at `t = 0`**, on Schwartz functions:
`∂_t (e^{−itκ} ψ)|₀ = −iκψ` in `L²`, by dominated convergence with dominator `4κ²|ψ|²`. -/
theorem hasDerivAt_phaseGroup_toLp (ψ : 𝓢(E, ℂ)) :
    HasDerivAt (fun t => phaseGroup hκm t (ψ.toLp 2))
      ((-Complex.I) • (SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ κ ψ).toLp 2) 0 := by
  set D : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ κ ψ with hD
  have hDx : ∀ x, D x = (κ x : ℂ) * ψ x := fun x => by
    rw [hD, SchwartzMap.smulLeftCLM_apply_apply hκ, Complex.real_smul]
  set F : ℝ → E → ℂ := fun t x =>
    (((t⁻¹ : ℝ) : ℂ) * (phaseFun κ t x - 1) + Complex.I * (κ x : ℂ)) * ψ x with hF
  set X : ℝ → L2 := fun t =>
    t⁻¹ • (phaseGroup hκm t (ψ.toLp 2 volume) - ψ.toLp 2 volume) - (-Complex.I) • D.toLp 2 volume
    with hX
  -- the norm of the remainder, as an integral
  have hXF : ∀ t, ‖X t‖ ^ 2 = ∫ x, ‖F t x‖ ^ 2 := by
    intro t
    have hae : (X t : E → ℂ) =ᵐ[volume] F t := by
      filter_upwards [Lp.coeFn_sub (t⁻¹ • (phaseGroup hκm t (ψ.toLp 2 volume) - ψ.toLp 2 volume))
          ((-Complex.I) • D.toLp 2 volume),
        Lp.coeFn_smul (t⁻¹ : ℝ) (phaseGroup hκm t (ψ.toLp 2 volume) - ψ.toLp 2 volume),
        Lp.coeFn_sub (phaseGroup hκm t (ψ.toLp 2 volume)) (ψ.toLp 2 volume),
        Lp.coeFn_smul (-Complex.I) (D.toLp 2 volume), coeFn_phaseGroup hκm t (ψ.toLp 2 volume),
        ψ.coeFn_toLp 2 volume, D.coeFn_toLp 2 volume] with x h1 h2 h3 h4 h5 h6 h7
      simp only [hX, hF]
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, Pi.smul_apply, h5, h6, h7,
        hDx, Complex.real_smul, smul_eq_mul]
      ring
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def]
    have h1 : ∫ a, inner ℂ ((X t) a) ((X t) a) = ((∫ a, ‖(X t) a‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      show inner ℂ ((X t) a) ((X t) a) = ((‖(X t) a‖ ^ 2 : ℝ) : ℂ)
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h1, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_congr_ae (hae.mono fun x hx => by
      show ‖(X t) x‖ ^ 2 = ‖F t x‖ ^ 2
      rw [hx])
  -- dominated convergence for the integrals
  have hκc : Continuous κ := hκ.1.continuous
  have hbound : Integrable (fun x => 4 * ‖D x‖ ^ 2) (volume : Measure E) :=
    ((D.memLp 2).integrable_norm_pow (p := 2) two_ne_zero).const_mul 4
  have hlim : Tendsto (fun t => ∫ x, ‖F t x‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : (∫ x : E, ‖(0 : ℂ)‖ ^ 2) = 0 := by simp
    rw [← h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 4 * ‖D x‖ ^ 2)
      (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => Eventually.of_forall fun x => ?_)
      hbound (Eventually.of_forall fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF, phaseFun]
      fun_prop
    · simp only [hF]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow, hDx, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow]
      have := norm_phaseQuot_le (κ := κ) t x
      calc ‖((t⁻¹ : ℝ) : ℂ) * (phaseFun κ t x - 1) + Complex.I * (κ x : ℂ)‖ ^ 2 * ‖ψ x‖ ^ 2
          ≤ (2 * |κ x|) ^ 2 * ‖ψ x‖ ^ 2 := by gcongr
        _ = 4 * (|κ x| ^ 2 * ‖ψ x‖ ^ 2) := by ring
    · have := ((tendsto_phaseQuot (κ := κ) x).mul_const (ψ x)).norm.pow 2
      simpa [hF] using this
  -- back to the norm
  have hnorm : Tendsto (fun t => ‖X t‖) (𝓝[≠] 0) (𝓝 0) := by
    have h := hlim.sqrt
    rw [Real.sqrt_zero] at h
    refine h.congr fun t => ?_
    rw [← hXF t, Real.sqrt_sq (norm_nonneg _)]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, phaseGroup_zero, one_apply_eq_self]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- ★ **The strong derivative of `U_κ` at `t = 0`** on Schwartz functions:
`∂_t (U_κ(t) f)|₀ = −i κ(D) f` in `L²`. -/
theorem hasDerivAt_fourierGroup_toLp_zero (f : 𝓢(E, ℂ)) :
    HasDerivAt (fun t => fourierGroup hκm t (f.toLp 2))
      ((-Complex.I) • (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ κ f).toLp 2) 0 := by
  have hfun : (fun t => fourierGroup hκm t (f.toLp 2))
      = fun t => (((fourierL2 (E := E)).symm.toContinuousLinearEquiv : L2 →L[ℂ] L2).restrictScalars ℝ)
          (phaseGroup hκm t ((𝓕 f).toLp 2)) := by
    funext t
    rw [fourierGroup_apply, ← SchwartzMap.toLp_fourier_eq]
    rfl
  rw [hfun]
  have h := (((fourierL2 (E := E)).symm.toContinuousLinearEquiv : L2 →L[ℂ] L2).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt (0 : ℝ) (hasDerivAt_phaseGroup_toLp hκm hκ (𝓕 f))
  refine HasDerivAt.congr_deriv h ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul]
  have h2 : ∀ ψ : 𝓢(E, ℂ), fourierL2.symm (ψ.toLp 2 volume) = (𝓕⁻ ψ).toLp 2 volume := fun ψ =>
    SchwartzMap.toLp_fourierInv_eq ψ
  rw [h2]
  rfl

/-- ★★ **The Schrödinger equation for `U_κ`**, in `L²`, for Schwartz initial data: at every `t`,
`∂_t (U_κ(t) f) = −i κ(D) (U_κ(t) f)`. -/
theorem hasDerivAt_fourierGroup_toLp (f : 𝓢(E, ℂ)) (t₀ : ℝ) :
    HasDerivAt (fun t => fourierGroup hκm t (f.toLp 2))
      ((-Complex.I) • (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ κ
        (fourierGroupS κ t₀ f)).toLp 2) t₀ := by
  have hfun : (fun t => fourierGroup hκm t (f.toLp 2))
      = fun t => fourierGroup hκm (t - t₀) ((fourierGroupS κ t₀ f).toLp 2) := by
    funext t
    rw [← fourierGroup_toLp hκm hκ, ← mul_apply_eq_comp, ← fourierGroup_add, sub_add_cancel]
  rw [hfun]
  have h := hasDerivAt_fourierGroup_toLp_zero hκm hκ (fourierGroupS κ t₀ f)
  rw [← sub_self t₀] at h
  exact HasDerivAt.comp_sub_const t₀ t₀ h

omit hκm hκ in
/-- ★★ **The free Schrödinger equation** `i ∂_t ψ = H₀ ψ`, `H₀ = −½ d²/dx²`, in `L²` for Schwartz
initial data: `ψ(t) = e^{−itH₀} f` satisfies `∂_t ψ(t) = −i H₀ ψ(t)` at every `t`. -/
theorem hasDerivAt_freeSchrodinger (f : 𝓢(E, ℂ)) (t₀ : ℝ) :
    HasDerivAt (fun t => freeSchrodinger t (f.toLp 2))
      ((-Complex.I) • (kineticOp (freeSchrodingerS t₀ f)).toLp 2) t₀ :=
  hasDerivAt_fourierGroup_toLp (measurable_freeSymbol (E := E)) hasTemperateGrowth_freeSymbol f t₀

end SchrodingerGroup
