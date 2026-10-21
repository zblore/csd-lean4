/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WignerL2

/-!
# The free half of the interacting Wigner equation on `dom H₀`

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #168 (out of ~~#64~~, second brick of the interacting Wigner equation).

For `φ, ψ ∈ dom H₀` (the free Hamiltonian's domain in the position representation),

  `W(−iH₀φ, ψ) + W(φ, −iH₀ψ) = −2πξ · ∂_x W(φ, ψ)`.

In the momentum form of #167, `W(φ, ψ)(x, ξ) = 2 ∫ e(2xu) ψ̂(ξ + u) conj φ̂(ξ − u) du`, and
`H₀` multiplies the transform by `2π²η²` (`freeSymbolOp`). Two facts make the identity algebra:

* **the `x`-dependence is a phase group.** `e(2xu) = e^{−ix·κ(u)}` with `κ(u) = −4πu`, so
  `x ↦ e(2x·) ψ̂(ξ + ·)` is `phaseGroup κ x` applied to a fixed `L²` function, and
  `PhaseGenerator.lean`'s ★★★ `hasDerivAt_phaseGroup_apply` differentiates it in `L²` as soon as
  `κ · ψ̂(ξ + ·) ∈ L²`, which is exactly what `ψ ∈ dom H₀` gives (`η ψ̂ ∈ L²` because
  `|η| ≤ 1 + 2π²η²`). Hence `∂_x W = 2 ∫ 4πiu · e(2xu) ψ̂(ξ + u) conj φ̂(ξ − u) du`;
* **`(ξ − u)² − (ξ + u)² = −4ξu`**, so the two `H₀` terms combine to `−2πξ` times that integrand.

* `WignerFunction.wignerKappa`, `phaseFun_wignerKappa`, ★ `wignerRight_eq_phaseGroup` — the
  right slot is the phase group of `κ(u) = −4πu`;
* `WignerFunction.memLp_id_mul_of_mem`, `memLp_shift_mul`, `memLp_kappa_shift` — the domain
  condition `η ψ̂ ∈ L²` and its translates;
* ★★ `WignerFunction.hasDerivAt_wignerRight`, ★★ `hasDerivAt_wignerL2_x`, `deriv_wignerL2_x_eq` —
  **the `x`-derivative of the `L²` Wigner function** exists for `ψ ∈ dom H₀`, with its integral
  formula;
* `WignerFunction.mem_freeSymbolOp_domain_of_mem`, `fourier_freePositionOp` — `H₀` on `dom H₀` is
  the symbol multiplier on the transform;
* `WignerFunction.integrable_wignerL2_integrand`, `wignerL2_add_left`, `wignerL2_add_right`,
  `wignerL2_smul_left`, `wignerL2_smul_right` — the integrand is integrable; `W` is
  sesquilinear;
* ★★★ `WignerFunction.wignerL2_freePositionOp_add` — **the free half**:
  `W(−iH₀φ, ψ) + W(φ, −iH₀ψ) = −2πξ ∂_x W(φ, ψ)` on `dom H₀`.

## Honest scope

* `dom H₀` is `freePositionOp.domain`, the operator-theoretic domain (`{ψ : (1 + ξ²) ψ̂ ∈ L²}`);
  no identification with `H²(ℝ)` is used or needed.
* The potential half `W(−iVψ, ψ) + W(ψ, −iVψ) = moyalPot V ψ` and the assembled equation are #169,
  [`WignerPotential.lean`](WignerPotential.lean).

References: E. Wigner, Phys. Rev. 40 (1932) 749; `WignerL2.lean` (#167), `PhaseGenerator.lean`
(`hasDerivAt_phaseGroup_apply`), `FreeHamiltonian.lean` (`freeSymbolOp`, `freePositionOp`),
`LinearPMapConj.lean` (`conjIsometry_apply_of_eq`); `specs/BACKLOG.md` #168, ~~#64~~.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real Filter SchrodingerGroup
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal Topology

namespace WignerFunction

local notation "L2" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### Sesquilinearity and integrability -/

theorem wignerL2_add_left (φ₁ φ₂ ψ : L2) (x ξ : ℝ) :
    wignerL2 (φ₁ + φ₂) ψ x ξ = wignerL2 φ₁ ψ x ξ + wignerL2 φ₂ ψ x ξ := by
  simp only [wignerL2, map_add, inner_add_left, mul_add]

theorem wignerL2_add_right (φ ψ₁ ψ₂ : L2) (x ξ : ℝ) :
    wignerL2 φ (ψ₁ + ψ₂) x ξ = wignerL2 φ ψ₁ x ξ + wignerL2 φ ψ₂ x ξ := by
  simp only [wignerL2, map_add, inner_add_right, mul_add]

theorem wignerL2_smul_left (c : ℂ) (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 (c • φ) ψ x ξ = conj c * wignerL2 φ ψ x ξ := by
  simp only [wignerL2, map_smul, inner_smul_left]
  ring

theorem wignerL2_smul_right (c : ℂ) (φ ψ : L2) (x ξ : ℝ) :
    wignerL2 φ (c • ψ) x ξ = c * wignerL2 φ ψ x ξ := by
  simp only [wignerL2, map_smul, inner_smul_right]
  ring

/-- The integrand of the momentum form is integrable (it is the integrand of an `L²` inner
product). -/
theorem integrable_wignerL2_integrand (φ ψ : L2) (x ξ : ℝ) :
    Integrable (fun u : ℝ => (𝐞 (2 * x * u) : ℂ)
      * ((Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) * conj ((Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u))))
      volume := by
  refine (L2.integrable_inner (wignerLeft ξ φ) (wignerRight x ξ ψ)).congr ?_
  filter_upwards [coeFn_wignerLeft ξ φ, coeFn_wignerRight x ξ ψ] with u h1 h2
  rw [RCLike.inner_apply', h1, h2]
  ring

/-! ### The right slot is a phase group -/

/-- The multiplier `κ(u) = −4πu`, whose phase group `e^{−ixκ}` is `e(2x·)`. -/
noncomputable def wignerKappa (u : ℝ) : ℝ := -(4 * π * u)

theorem measurable_wignerKappa : Measurable wignerKappa := by
  unfold wignerKappa
  fun_prop

theorem phaseFun_wignerKappa (x u : ℝ) : phaseFun wignerKappa x u = (𝐞 (2 * x * u) : ℂ) := by
  rw [phaseFun, Real.fourierChar_apply, wignerKappa]
  congr 1
  push_cast
  ring

/-- ★ **The right slot is the phase group of `κ` applied to the shifted transform.** -/
theorem wignerRight_eq_phaseGroup (x ξ : ℝ) (ψ : L2) :
    wignerRight x ξ ψ
      = phaseGroup (E := ℝ) measurable_wignerKappa x (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wignerRight x ξ ψ,
    coeFn_phaseGroup (E := ℝ) measurable_wignerKappa x (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)),
    coeFn_shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)] with u h1 h2 h3
  rw [h1, h2, h3, phaseFun_wignerKappa]

/-! ### The domain condition `η ψ̂ ∈ L²` -/

/-- `(1 + 2π²η²) f ∈ L²` gives `η f ∈ L²`. -/
theorem memLp_id_mul_of_mem (f : L2) (hf : f ∈ freeSymbolOp.domain) :
    MemLp (fun η : ℝ => (η : ℂ) * f η) 2 (volume : Measure ℝ) := by
  have hsym : MemLp (fun η : ℝ => ((freeSymbol (E := ℝ) η : ℝ) : ℂ) * f η) 2 (volume : Measure ℝ) := by
    rw [freeSymbolOp, L2.mulOp_domain, L2.mem_mulDomain_iff] at hf
    exact hf
  have hf2 : MemLp (fun η : ℝ => f η) 2 (volume : Measure ℝ) := Lp.memLp f
  have hg : MemLp (fun η : ℝ => ‖f η‖ + ‖((freeSymbol (E := ℝ) η : ℝ) : ℂ) * f η‖) 2
      (volume : Measure ℝ) :=
    (hf2.norm.add hsym.norm).ae_eq (Filter.Eventually.of_forall fun η => by simp only [Pi.add_apply])
  refine MemLp.mono' hg (Complex.measurable_ofReal.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun η => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hπ : (1 : ℝ) ≤ 2 * π ^ 2 := by nlinarith [Real.two_le_pi]
  have h0 : freeSymbol (E := ℝ) η = 2 * π ^ 2 * η ^ 2 := by
    rw [freeSymbol, Real.norm_eq_abs, sq_abs]
  have h1 : |η| ≤ 1 + |freeSymbol (E := ℝ) η| := by
    rw [h0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π ^ 2 * η ^ 2)]
    nlinarith [sq_nonneg (|η| - 1), sq_abs η, abs_nonneg η,
      mul_nonneg (sq_nonneg η) (sub_nonneg.2 hπ)]
  calc |η| * ‖f η‖ ≤ (1 + |freeSymbol (E := ℝ) η|) * ‖f η‖ := by gcongr
    _ = ‖f η‖ + |freeSymbol (E := ℝ) η| * ‖f η‖ := by ring

/-- The translate `u ↦ u · f(ξ + u)` is in `L²` for `f` in the free symbol domain. -/
theorem memLp_shift_mul (f : L2) (hf : f ∈ freeSymbolOp.domain) (ξ : ℝ) :
    MemLp (fun u : ℝ => (u : ℂ) * f (ξ + u)) 2 (volume : Measure ℝ) := by
  have h1 : MemLp (fun u : ℝ => ((ξ + u : ℝ) : ℂ) * f (ξ + u)) 2 (volume : Measure ℝ) := by
    have := (memLp_id_mul_of_mem f hf).comp_measurePreserving (measurePreserving_add_left volume ξ)
    simpa only [Function.comp_def] using this
  have h2 : MemLp (fun u : ℝ => (ξ : ℂ) * f (ξ + u)) 2 (volume : Measure ℝ) := by
    have := ((Lp.memLp f).comp_measurePreserving (measurePreserving_add_left volume ξ)).const_mul
      (ξ : ℂ)
    simpa only [Function.comp_def] using this
  refine (h1.sub h2).ae_eq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- `κ · ψ̂(ξ + ·) ∈ L²` for `ψ̂` in the free symbol domain. -/
theorem memLp_kappa_shift (ψ : L2) (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain)
    (ξ : ℝ) :
    MemLp (fun u : ℝ => ((wignerKappa u : ℝ) : ℂ) * (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)) u) 2
      (volume : Measure ℝ) := by
  have h := (memLp_shift_mul _ hψ ξ).const_mul ((-(4 * π) : ℝ) : ℂ)
  refine h.ae_eq ?_
  filter_upwards [coeFn_shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)] with u hu
  rw [hu, wignerKappa]
  push_cast
  ring

/-! ### The `x`-derivative -/

/-- The `L²` class of `u ↦ κ(u) ψ̂(ξ + u)`. -/
noncomputable def kappaShift (ψ : L2) (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain)
    (ξ : ℝ) : L2 :=
  (memLp_kappa_shift ψ hψ ξ).toLp _

theorem coeFn_kappaShift (ψ : L2) (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain)
    (ξ : ℝ) :
    (kappaShift ψ hψ ξ : ℝ → ℂ) =ᵐ[volume]
      fun u => ((wignerKappa u : ℝ) : ℂ) * (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)) u :=
  MemLp.coeFn_toLp _

/-- ★★ **The right slot is differentiable in `x`** for `ψ̂` in the free symbol domain, with
derivative `−i · e(2x·) · κ ψ̂(ξ + ·)`. -/
theorem hasDerivAt_wignerRight (ξ : ℝ) (ψ : L2)
    (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain) (x : ℝ) :
    HasDerivAt (fun x => wignerRight x ξ ψ)
      ((-Complex.I) • phaseGroup (E := ℝ) measurable_wignerKappa x (kappaShift ψ hψ ξ)) x := by
  have h := hasDerivAt_phaseGroup_apply (E := ℝ) measurable_wignerKappa
    (shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)) (kappaShift ψ hψ ξ) (MemLp.coeFn_toLp _) x
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => wignerRight_eq_phaseGroup s ξ ψ)

/-- ★★ **The `L²` Wigner function is differentiable in `x`** for `ψ ∈ dom H₀`. -/
theorem hasDerivAt_wignerL2_x (φ ψ : L2) (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain)
    (x ξ : ℝ) :
    HasDerivAt (fun x => wignerL2 φ ψ x ξ)
      (2 * ⟪wignerLeft ξ φ,
        (-Complex.I) • phaseGroup (E := ℝ) measurable_wignerKappa x (kappaShift ψ hψ ξ)⟫_ℂ) x := by
  have h := ((hasDerivAt_const x (wignerLeft ξ φ)).inner ℂ (hasDerivAt_wignerRight ξ ψ hψ x)).const_mul
    (2 : ℂ)
  refine h.congr_deriv ?_
  rw [inner_zero_left, add_zero]

/-- The integral formula for `∂_x W`: `2 ∫ 4πiu · e(2xu) ψ̂(ξ + u) conj φ̂(ξ − u) du`. -/
theorem deriv_wignerL2_x_eq (φ ψ : L2) (hψ : Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain)
    (x ξ : ℝ) :
    deriv (fun x => wignerL2 φ ψ x ξ) x
      = 2 * ∫ u : ℝ, ((4 * π * u : ℝ) : ℂ) * Complex.I * (𝐞 (2 * x * u) : ℂ)
          * ((Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) * conj ((Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u))) := by
  rw [(hasDerivAt_wignerL2_x φ ψ hψ x ξ).deriv, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_wignerLeft ξ φ,
    Lp.coeFn_smul (-Complex.I) (phaseGroup (E := ℝ) measurable_wignerKappa x (kappaShift ψ hψ ξ)),
    coeFn_phaseGroup (E := ℝ) measurable_wignerKappa x (kappaShift ψ hψ ξ),
    coeFn_kappaShift ψ hψ ξ,
    coeFn_shiftAt ξ (Lp.fourierTransformₗᵢ ℝ ℂ ψ)] with u h1 h2 h3 h4 h5
  rw [RCLike.inner_apply', h1, h2, Pi.smul_apply, smul_eq_mul, h3, h4, h5, phaseFun_wignerKappa,
    wignerKappa]
  push_cast
  ring

/-! ### `H₀` on the transform -/

theorem mem_freeSymbolOp_domain_of_mem {ψ : L2} (hψ : ψ ∈ freePositionOp.domain) :
    Lp.fourierTransformₗᵢ ℝ ℂ ψ ∈ freeSymbolOp.domain := by
  rw [freePositionOp_domain] at hψ
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hψ
  show Lp.fourierTransformₗᵢ ℝ ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ).symm y) ∈ freeSymbolOp.domain
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact hy

/-- `𝓕 (H₀ ψ) = (2π²η²) ψ̂` on `dom H₀`. -/
theorem fourier_freePositionOp {ψ : L2} (hψ : ψ ∈ freePositionOp.domain) :
    Lp.fourierTransformₗᵢ ℝ ℂ (freePositionOp ⟨ψ, hψ⟩)
      = freeSymbolOp ⟨Lp.fourierTransformₗᵢ ℝ ℂ ψ, mem_freeSymbolOp_domain_of_mem hψ⟩ := by
  have h := LinearPMap.conjIsometry_apply_of_eq (Lp.fourierTransformₗᵢ ℝ ℂ).symm freeSymbolOp
    ⟨Lp.fourierTransformₗᵢ ℝ ℂ ψ, mem_freeSymbolOp_domain_of_mem hψ⟩ ⟨ψ, hψ⟩ (by simp)
  rw [show freePositionOp ⟨ψ, hψ⟩ = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (freeSymbolOp ⟨Lp.fourierTransformₗᵢ ℝ ℂ ψ, mem_freeSymbolOp_domain_of_mem hψ⟩) from h,
    LinearIsometryEquiv.apply_symm_apply]

/-- The transform of `−iH₀ψ`, almost everywhere: `−i · 2π²η² · ψ̂(η)`. -/
theorem coeFn_fourier_neg_I_smul_freePositionOp {ψ : L2} (hψ : ψ ∈ freePositionOp.domain) :
    (Lp.fourierTransformₗᵢ ℝ ℂ ((-Complex.I) • freePositionOp ⟨ψ, hψ⟩) : ℝ → ℂ)
      =ᵐ[volume] fun η => (-Complex.I) * (((freeSymbol (E := ℝ) η : ℝ) : ℂ)
        * (Lp.fourierTransformₗᵢ ℝ ℂ ψ) η) := by
  rw [map_smul, fourier_freePositionOp hψ]
  filter_upwards [Lp.coeFn_smul (-Complex.I)
    (freeSymbolOp ⟨Lp.fourierTransformₗᵢ ℝ ℂ ψ, mem_freeSymbolOp_domain_of_mem hψ⟩),
    L2.coeFn_mulOp (m := freeSymbol (E := ℝ)) (μ := (volume : Measure ℝ))
      ⟨Lp.fourierTransformₗᵢ ℝ ℂ ψ, mem_freeSymbolOp_domain_of_mem hψ⟩] with η h1 h2
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact congrArg _ h2

/-! ### The free half -/

/-- ★★★ **The free half of the interacting Wigner equation**: for `φ, ψ ∈ dom H₀`,
`W(−iH₀φ, ψ) + W(φ, −iH₀ψ) = −2πξ · ∂_x W(φ, ψ)`. -/
theorem wignerL2_freePositionOp_add {φ ψ : L2} (hφ : φ ∈ freePositionOp.domain)
    (hψ : ψ ∈ freePositionOp.domain) (x ξ : ℝ) :
    wignerL2 ((-Complex.I) • freePositionOp ⟨φ, hφ⟩) ψ x ξ
        + wignerL2 φ ((-Complex.I) • freePositionOp ⟨ψ, hψ⟩) x ξ
      = -(2 * π * ξ) * deriv (fun x => wignerL2 φ ψ x ξ) x := by
  rw [deriv_wignerL2_x_eq φ ψ (mem_freeSymbolOp_domain_of_mem hψ) x ξ, wignerL2_eq_integral,
    wignerL2_eq_integral, ← mul_add,
    ← integral_add (integrable_wignerL2_integrand _ _ x ξ) (integrable_wignerL2_integrand _ _ x ξ)]
  have hR : -(2 * (π : ℂ) * (ξ : ℂ)) * (2 * ∫ u : ℝ, ((4 * π * u : ℝ) : ℂ) * Complex.I
        * (𝐞 (2 * x * u) : ℂ)
        * ((Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) * conj ((Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u))))
      = 2 * ∫ u : ℝ, -(2 * (π : ℂ) * (ξ : ℂ)) * (((4 * π * u : ℝ) : ℂ) * Complex.I
        * (𝐞 (2 * x * u) : ℂ)
        * ((Lp.fourierTransformₗᵢ ℝ ℂ ψ) (ξ + u) * conj ((Lp.fourierTransformₗᵢ ℝ ℂ φ) (ξ - u)))) := by
    rw [integral_const_mul (-(2 * (π : ℂ) * (ξ : ℂ)))]
    ring
  rw [hR]
  congr 1
  have hA := (Measure.measurePreserving_sub_left (volume : Measure ℝ) ξ).quasiMeasurePreserving.ae_eq_comp
    (coeFn_fourier_neg_I_smul_freePositionOp hφ)
  have hB := (measurePreserving_add_left (volume : Measure ℝ) ξ).quasiMeasurePreserving.ae_eq_comp
    (coeFn_fourier_neg_I_smul_freePositionOp hψ)
  refine integral_congr_ae ?_
  filter_upwards [hA, hB] with u h1 h2
  simp only [Function.comp] at h1 h2
  rw [h1, h2]
  simp only [freeSymbol, Real.norm_eq_abs, sq_abs, map_mul, map_neg, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  ring

end WignerFunction

end
