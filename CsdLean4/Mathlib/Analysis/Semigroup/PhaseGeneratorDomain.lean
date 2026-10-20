/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.SchrodingerGenerator

/-!
# The generator domain of the phase group is the multiplication domain

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #154 (out of ~~#129~~).

`PhaseGenerator.lean` proved the forward half: if `κ·f ∈ L²` then the orbit `t ↦ e^{−itκ} f` is
differentiable with derivative `−i κ f` (`hasDerivAt_phaseGroup_apply`), and the phase group
preserves that domain (`phaseGroup_mem_mulDomain`). This file proves the **converse**: if the orbit
has a right derivative at `0` in `L²` — `HasGeneratorAt (phaseGroup hκ) f w` — then `κ·f ∈ L²`.
The generator domain of the phase group *is* the multiplication domain.

* ★★ `mem_mulDomain_of_hasGeneratorAt` — **the Fatou argument.** Along `hₙ = 1/(n+1)` the
  quotients `qₙ = hₙ⁻¹(e^{−ihₙκ} − 1) f` converge to `w` in `L²`, so `‖qₙ‖² → ‖w‖²`; pointwise their
  squared moduli converge to `|κ f|²` (`tendsto_phaseDefect`); Fatou's lemma
  (`lintegral_liminf_le'`) gives `∫ |κ f|² ≤ liminf ∫ |qₙ|² = ‖w‖² < ∞`.
* ★ `hasGeneratorAt_phaseGroup_iff`: the two readings of the domain agree, with the generator value
  `−i κ f` (`L2.mulOp`), uniqueness of the right derivative identifying `w`.
* The free Hamiltonian: ★★ `mem_freePositionOp_domain_of_hasGeneratorAt` carries the statement
  across the Fourier transform — a vector whose free orbit has a right derivative at `0` lies in
  `freePositionOp.domain`.
* ★★★ `schrodinger_mem_freePositionOp_domain`: **the interacting orbit stays in `dom H₀`**, now in
  the operator sense; and ★★★ `hasDerivAt_schrodinger_orbit`: **`i ∂ₜ U(t)ψ = (H₀ + V)(U(t)ψ)`**
  with `H₀` the self-adjoint operator `freePositionOp` acting on the orbit point. This closes the
  gap ~~#129~~ left: the mild solution is classical in the operator-theoretic sense.

## Honest scope

* The potential remains the bounded multiplier `potential VL`; the identification with
  `schrodingerOp`'s `mulCLM` for a real `V` is a `coeFn` statement not made here.
* One dimension and `κ = freeSymbol` for the Schrödinger part, as throughout; the Fatou lemma is
  for any measurable `κ` on any `E`.

References: Reed–Simon I §VIII.4 (the generator of a multiplication group); `PhaseGenerator.lean`
(`phaseDefect`, `tendsto_phaseDefect`, `coeFn_slope_phaseGroup`, `norm_sq_eq_integral`),
`PerturbedGenerator.lean` (`HasGeneratorAt`), `SchrodingerGenerator.lean`
(`hasGeneratorAt_freeGroup_schrodinger`, `schrodinger_classical`); Mathlib
`MeasureTheory.lintegral_liminf_le'`; `specs/BACKLOG.md` #154, ~~#129~~.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set ContractionSemigroup HeatSemigroup

noncomputable section

namespace SchrodingerGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "L2" => Lp ℂ 2 (volume : Measure E)

variable {κ : E → ℝ} (hκ : Measurable κ)
include hκ

/-! ### The quotients, pointwise -/

/-- The right quotient of the phase group at `0`, pointwise: `f · h⁻¹(e^{−ihκ} − 1)`. -/
theorem coeFn_quotient_phaseGroup (f : L2) (h : ℝ) :
    ((h⁻¹ • (phaseGroup hκ h f - f) : L2) : E → ℂ)
      =ᵐ[volume] fun x => f x * (h⁻¹ • (phaseFun κ h x - 1)) := by
  have hs : slope (fun r => phaseGroup hκ r f) 0 h = h⁻¹ • (phaseGroup hκ h f - f) := by
    rw [slope_def_module, sub_zero, phaseGroup_zero, one_apply_eq_self]
  have := coeFn_slope_phaseGroup hκ f 0 h
  rw [hs] at this
  filter_upwards [this] with x hx
  rw [hx, phaseFun_zero, one_mul, sub_zero]

/-! ### ★★ The Fatou argument -/

/-- ★★ **A vector whose phase-group orbit has a right derivative at `0` lies in the multiplication
domain**: `κ·f ∈ L²`. Fatou along `hₙ = 1/(n+1)`. -/
theorem mem_mulDomain_of_hasGeneratorAt (f w : L2) (hw : HasGeneratorAt (phaseGroup hκ) f w) :
    f ∈ (MeasureTheory.L2.mulOp (μ := (volume : Measure E)) κ).domain := by
  rw [MeasureTheory.L2.mulOp_domain, MeasureTheory.L2.mem_mulDomain_iff]
  -- the sequence of steps
  set h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hh
  have hpos : ∀ n, 0 < h n := fun n => by positivity
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hpos)
  -- the quotients
  set q : ℕ → L2 := fun n => (h n)⁻¹ • (phaseGroup hκ (h n) f - f) with hq
  have hqw : Tendsto q atTop (𝓝 w) := hw.comp hlim
  have hnorm : Tendsto (fun n => ‖q n‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := hqw.norm.pow 2
  have hptw : ∀ n, (q n : E → ℂ) =ᵐ[volume] fun x => f x * ((h n)⁻¹ • (phaseFun κ (h n) x - 1)) :=
    fun n => coeFn_quotient_phaseGroup hκ f (h n)
  -- Fatou
  have hmeasG : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (‖q n x‖ ^ 2)) volume := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Lp.aestronglyMeasurable (q n)).norm.aemeasurable.pow_const 2)
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure E)) (u := atTop) hmeasG
  -- the right-hand side is `‖w‖²`
  have hint : ∀ n, ∫⁻ x, ENNReal.ofReal (‖q n x‖ ^ 2) = ENNReal.ofReal (‖q n‖ ^ 2) := by
    intro n
    rw [norm_sq_eq_integral, ofReal_integral_eq_lintegral_ofReal]
    · exact_mod_cast (Lp.memLp (q n)).integrable_norm_pow (p := 2) two_ne_zero
    · exact Eventually.of_forall fun x => by positivity
  have hR : liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖q n x‖ ^ 2)) atTop
      = ENNReal.ofReal (‖w‖ ^ 2) := by
    simp_rw [hint]
    exact (ENNReal.tendsto_ofReal hnorm).liminf_eq
  -- the left-hand side is `∫ |κ f|²`
  have hL : (fun x => liminf (fun n => ENNReal.ofReal (‖q n x‖ ^ 2)) atTop)
      =ᵐ[volume] fun x => ENNReal.ofReal (‖(κ x : ℂ) * f x‖ ^ 2) := by
    have hall : ∀ᵐ x ∂(volume : Measure E), ∀ n,
        q n x = f x * ((h n)⁻¹ • (phaseFun κ (h n) x - 1)) := ae_all_iff.2 hptw
    filter_upwards [hall] with x hx
    have hne : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
      hlim.mono_right (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
    have hdef : Tendsto (fun n => phaseDefect κ (h n) x) atTop (𝓝 0) :=
      (tendsto_phaseDefect κ x).comp hne
    have hlim' : Tendsto (fun n => (h n)⁻¹ • (phaseFun κ (h n) x - 1)) atTop
        (𝓝 (-(Complex.I * (κ x : ℂ)))) := by
      have := hdef.sub_const (Complex.I * (κ x : ℂ))
      simp only [phaseDefect, add_sub_cancel_right, zero_sub] at this
      exact this
    have h1 : Tendsto (fun n => f x * ((h n)⁻¹ • (phaseFun κ (h n) x - 1))) atTop
        (𝓝 (f x * -(Complex.I * (κ x : ℂ)))) := tendsto_const_nhds.mul hlim'
    have h2 := ENNReal.tendsto_ofReal (h1.norm.pow 2)
    have h3 : ‖f x * -(Complex.I * (κ x : ℂ))‖ ^ 2 = ‖(κ x : ℂ) * f x‖ ^ 2 := by
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, norm_mul, mul_comm]
    rw [h3] at h2
    refine (h2.congr fun n => ?_).liminf_eq
    rw [hx n]
  rw [lintegral_congr_ae hL, hR] at hfatou
  -- conclude
  have hmeas : AEStronglyMeasurable (fun x => (κ x : ℂ) * f x) (volume : Measure E) :=
    ((Complex.measurable_ofReal.comp hκ).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨(hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
  exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top

/-- ★ **The two readings of the domain agree.** A vector is in the generator domain of the phase
group with value `w` iff it is in the multiplication domain and `w = −i κ f`. -/
theorem hasGeneratorAt_phaseGroup_iff (f w : L2) :
    HasGeneratorAt (phaseGroup hκ) f w
      ↔ ∃ hf : f ∈ (MeasureTheory.L2.mulOp (μ := (volume : Measure E)) κ).domain,
          w = (-Complex.I) • MeasureTheory.L2.mulOp κ ⟨f, hf⟩ := by
  constructor
  · intro hw
    have hf := mem_mulDomain_of_hasGeneratorAt hκ f w hw
    refine ⟨hf, ?_⟩
    have hd := hasDerivAt_phaseGroup_apply hκ f (MeasureTheory.L2.mulOp κ ⟨f, hf⟩)
      (MeasureTheory.L2.coeFn_mulOp ⟨f, hf⟩) 0
    rw [phaseGroup_zero, one_apply_eq_self] at hd
    have hw' : HasGeneratorAt (phaseGroup hκ) f
        ((-Complex.I) • MeasureTheory.L2.mulOp κ ⟨f, hf⟩) :=
      (hasGeneratorAt_iff_hasDerivWithinAt (phaseGroup_zero hκ) _ _).2 hd.hasDerivWithinAt
    exact hw.unique hw'
  · rintro ⟨hf, rfl⟩
    have hd := hasDerivAt_phaseGroup_apply hκ f (MeasureTheory.L2.mulOp κ ⟨f, hf⟩)
      (MeasureTheory.L2.coeFn_mulOp ⟨f, hf⟩) 0
    rw [phaseGroup_zero, one_apply_eq_self] at hd
    exact (hasGeneratorAt_iff_hasDerivWithinAt (phaseGroup_zero hκ) _ _).2 hd.hasDerivWithinAt

end SchrodingerGroup

/-! ### The free Hamiltonian in position space -/

namespace SchrodingerGroup

/-- The free generator statement transports across the Fourier transform to the phase group. -/
theorem hasGeneratorAt_phaseGroup_fourierL2 (χ w : Lp ℂ 2 (volume : Measure ℝ))
    (hw : HasGeneratorAt (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1) χ w) :
    HasGeneratorAt (phaseGroup (measurable_freeSymbol (E := ℝ))) (fourierL2 χ) (fourierL2 w) := by
  unfold HasGeneratorAt at hw ⊢
  have hc := ((fourierL2 (E := ℝ)).continuous.tendsto w).comp hw
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  -- ⚠️ the scalar action in `HasGeneratorAt` is the one `NormedSpace ℂ E` induces; restating the
  -- goal re-elaborates it with `Lp`'s own instance, so the rewrites below match syntactically.
  have hm : ∀ x : Lp ℂ 2 (volume : Measure ℝ), fourierL2 (h⁻¹ • x) = h⁻¹ • fourierL2 x :=
    fun x => ((fourierL2 (E := ℝ)).toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ)).map_smul_of_tower h⁻¹ x
  show fourierL2 (h⁻¹ • ((if 0 ≤ h then fourierGroup (measurable_freeSymbol (E := ℝ)) h else 1) χ
      - χ))
    = h⁻¹ • (phaseGroup (measurable_freeSymbol (E := ℝ)) h (fourierL2 χ) - fourierL2 χ)
  rw [hm, map_sub]
  simp only [hh', ↓reduceIte, fourierGroup_apply, LinearIsometryEquiv.apply_symm_apply]

/-- ★★ **A vector whose free orbit has a right derivative at `0` lies in `dom H₀`.** -/
theorem mem_freePositionOp_domain_of_hasGeneratorAt (χ w : Lp ℂ 2 (volume : Measure ℝ))
    (hw : HasGeneratorAt (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1) χ w) : χ ∈ freePositionOp.domain := by
  have hmem : fourierL2 χ ∈ freeSymbolOp.domain :=
    mem_mulDomain_of_hasGeneratorAt (measurable_freeSymbol (E := ℝ)) _ _
      (hasGeneratorAt_phaseGroup_fourierL2 χ w hw)
  have h := LinearPMap.mem_conjIsometry_domain (Lp.fourierTransformₗᵢ ℝ ℂ).symm freeSymbolOp hmem
  rwa [show (Lp.fourierTransformₗᵢ ℝ ℂ).symm (fourierL2 χ) = χ from
    LinearIsometryEquiv.symm_apply_apply _ _] at h

/-- ★★★ **The interacting orbit stays in `dom H₀`**, in the operator sense. -/
theorem schrodinger_mem_freePositionOp_domain (VL : Lp ℂ ∞ (volume : Measure ℝ))
    (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    schrodinger (measurable_freeSymbol (E := ℝ)) VL t
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))) ∈ freePositionOp.domain :=
  mem_freePositionOp_domain_of_hasGeneratorAt _ _ (hasGeneratorAt_freeGroup_schrodinger VL f h ht)

/-- The free generator value at a point of `dom H₀` is `−i H₀` of it. -/
theorem hasGeneratorAt_freeGroup_of_mem (χ : Lp ℂ 2 (volume : Measure ℝ))
    (hχ : χ ∈ freePositionOp.domain) :
    HasGeneratorAt (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1) χ ((-Complex.I) • freePositionOp ⟨χ, hχ⟩) := by
  have hmem := LinearPMap.symm_mem_of_mem_map (Lp.fourierTransformₗᵢ ℝ ℂ).symm _ hχ
  rw [LinearIsometryEquiv.symm_symm] at hmem
  have e : fourierL2.symm (fourierL2 χ) = χ := LinearIsometryEquiv.symm_apply_apply _ _
  have h' : fourierL2.symm (fourierL2 χ) ∈ freePositionOp.domain := by rw [e]; exact hχ
  have h := hasGeneratorAt_freeGroup ⟨fourierL2 χ, hmem⟩ h'
  have hsub : (⟨fourierL2.symm (fourierL2 χ), h'⟩ : freePositionOp.domain) = ⟨χ, hχ⟩ :=
    Subtype.ext e
  rw [hsub, e] at h
  exact h

/-- ★★★ **The interacting Schrödinger equation with `H₀` acting on the orbit**:
`d/dt U(t)ψ = −i (H₀ + V)(U(t)ψ)` at every `t > 0`, where `H₀ = freePositionOp` is applied to the
orbit point, which lies in its domain. The mild solution is classical in the operator sense. -/
theorem hasDerivAt_schrodinger_orbit (VL : Lp ℂ ∞ (volume : Measure ℝ)) (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt
      (fun s => schrodinger (measurable_freeSymbol (E := ℝ)) VL s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      ((-Complex.I) • ((freePositionOp.addCLM (potential VL))
        ⟨schrodinger (measurable_freeSymbol (E := ℝ)) VL t
            (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))),
          schrodinger_mem_freePositionOp_domain VL f h ht.le⟩)) t := by
  obtain ⟨w, hw, hd⟩ := schrodinger_classical VL f h ht
  have hw' := hasGeneratorAt_freeGroup_of_mem _ (schrodinger_mem_freePositionOp_domain VL f h ht.le)
  have hwe := hw.unique hw'
  refine hd.congr_deriv ?_
  rw [hwe]
  change _ = (-Complex.I) • (freePositionOp ⟨_, _⟩ + potential VL _)
  simp only [smul_add, neg_smul, sub_eq_add_neg]
  rfl

end SchrodingerGroup

end

end
