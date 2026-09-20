/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.FeynmanKac

/-!
# The Feynman–Kac formula on all of `L²`

**Category:** 1-Mathlib (CSD-free; staged for upstream).

`Probability/FeynmanKac.lean` proves Kac's formula for bounded measurable `f ∈ L²`. This module
removes the boundedness (BACKLOG #42, FC-4′): for every `g ∈ L²(ℝ)`,

  `(e^{−t(H₀+V)} g)(x) = E[ exp (−∫₀ᵗ V (x + B_s) ds) · g (x + B_t) ]`  for a.e. `x`

(★★ `feynmanKac_Lp`), the right side being the Feynman–Kac functional `fkFunctional`, which is
well defined for a.e. `x` because `ω ↦ g (x + B_t ω)` is `P`-integrable for a.e. `x`
(`ae_integrable_shift`: the joint integrability of `(x, y) ↦ g (x + y)` on finite-measure sets
against the Gaussian, from `HeatSemigroup.lean`, sliced by Fubini and pushed through the law of
`B_t`).

## Design

Both sides are continuous in `g` and agree on the simple functions, which are dense in `L²`
(`Lp.simpleFunc.denseRange`); the identification is made on every finite-measure set `A`:

* the operator side is bounded, `‖∫_A e^{−t(H₀+V)} h‖ ≤ ‖1_A‖ ‖e^{−t(H₀+V)}‖ ‖h‖`;
* ★ the Wiener side is bounded by the heat semigroup of `|h|`:
  `‖∫_A fk h‖ ≤ e^{t‖V‖} ∫_A E‖h (x + B_t)‖ dx`, and `x ↦ E‖h (x + B_t)‖` **is** `P_t |h|`
  almost everywhere (`absConv_ae_eq`, through the pointwise formula of `HeatSemigroup.lean` and
  the law of `B_t`), so the integral is at most `‖1_A‖ ‖h‖` by Cauchy–Schwarz and contraction
  (`setIntegral_absConv_le`, `norm_setIntegral_fkFunctional_le`);
* so `‖∫_A (e^{−t(H₀+V)} g − fk g)‖ ≤ K_A ‖g − s‖` for every simple `s`, hence `= 0`.

The measurability of `fkFunctional g` comes for free from `FeynmanKac.tendsto_slicedWiener`,
generalised there to any `f` integrable along the endpoint: `fk g` is an a.e. pointwise limit of
the measurable sliced functionals.

* `fkFunctional V P B t f x` — the functional; `fkFunctional_congr_ae` — it depends only on the
  a.e.-class of `f` (the endpoint has a Gaussian law);
* `aestronglyMeasurable_weight` — the path integral of the potential is a.e.-measurable in `ω`
  (a limit of Riemann sums along the a.s. continuous paths), `integrable_weight_mul`;
* ★ `absConv_ae_eq` — `E‖g (x + B_t)‖ = (P_t |g|)(x)` for a.e. `x`;
* ★★ `feynmanKac_Lp` — **Feynman–Kac for every `g ∈ L²`**.

## Honest scope

⚠️ Conditional on a Brownian motion (`hB : IsBrownianReal B P`), one dimension, bounded continuous
`V`, `t > 0`; as in `FeynmanKac.lean`.

References: M. Kac, Trans. AMS 65, 1 (1949); B. Simon, *Functional Integration and Quantum Physics*,
Thm 6.2; `Probability/FeynmanKac.lean` (FC-4); `specs/feynman-continuum-scoping.md` §4;
`specs/BACKLOG.md` #42; `specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped ENNReal NNReal Topology Nat
open MeasureTheory ProbabilityTheory Filter HeatSemigroup TimeSlicedWiener

namespace FeynmanKac

/-- `L²(ℝ, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The functional -/

/-- The Feynman–Kac weight `exp (−∫₀ᵗ V (x + B_s) ds)`. -/
noncomputable def weight (V : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (x : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (-(((∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) : ℝ) : ℂ))

/-- The Feynman–Kac functional `E[exp (−∫₀ᵗ V (x + B_s) ds) · f (x + B_t)]`. -/
noncomputable def fkFunctional (V : ℝ → ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ω, weight V B t x ω * f (x + B t ω) ∂P

variable {V : ℝ → ℝ} {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV)

omit [MeasurableSpace Ω] in
include hCV in
theorem norm_weight_le (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (x : ℝ) (ω : Ω) :
    ‖weight V B t x ω‖ ≤ Real.exp ((t : ℝ) * CV) := by
  rw [weight, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (le_trans (neg_le_abs _) ?_)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ)) (C := CV)
    (f := fun s => V (x + B (Real.toNNReal s) ω)) fun s _ => by
      rw [Real.norm_eq_abs]; exact hCV _
  rw [Real.norm_eq_abs, sub_zero, NNReal.abs_eq, mul_comm] at h
  exact h

/-- The path integral of the potential is a.e.-strongly measurable in `ω`: a limit of Riemann
sums along the almost surely continuous paths. -/
theorem aestronglyMeasurable_pathIntegral (hVc : Continuous V) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : 0 < t) (x : ℝ) :
    AEStronglyMeasurable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) P := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (n : ℕ) ω =>
    ((t : ℝ) / n) * ∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω))
    (fun n => ?_) ?_
  · exact (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      hVc.measurable.comp (measurable_const.add (hBm _)))).aestronglyMeasurable
  · filter_upwards [hB.cont] with ω hω
    exact tendsto_riemann_path hVc ht x hω

theorem aestronglyMeasurable_weight (hVc : Continuous V) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : 0 < t) (x : ℝ) :
    AEStronglyMeasurable (weight V B t x) P :=
  Complex.continuous_exp.comp_aestronglyMeasurable
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_pathIntegral hVc hB hBm ht x)).neg

include hCV in
theorem integrable_weight_mul (hVc : Continuous V) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : 0 < t) {f : ℝ → ℂ} {x : ℝ}
    (hfi : Integrable (fun ω => f (x + B t ω)) P) :
    Integrable (fun ω => weight V B t x ω * f (x + B t ω)) P :=
  hfi.bdd_mul (aestronglyMeasurable_weight hVc hB hBm ht x)
    (Eventually.of_forall fun ω => norm_weight_le hCV B t x ω)

/-- The functional depends only on the a.e.-class of `f`: for `t > 0` the endpoint `x + B_t` has
a Gaussian law. -/
theorem fkFunctional_congr_ae {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : 0 < t) {f₁ f₂ : ℝ → ℂ}
    (h : f₁ =ᵐ[volume] f₂) (x : ℝ) : fkFunctional V P B t f₁ x = fkFunctional V P B t f₂ x := by
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ y ∂(volume : Measure ℝ), f₁ (x + y) = f₂ (x + y) :=
    (measurePreserving_add_left volume x).quasiMeasurePreserving.ae_eq h
  have h2 : ∀ᵐ y ∂(gaussianReal 0 t), f₁ (x + y) = f₂ (x + y) :=
    (gaussianReal_absolutelyContinuous 0 ht.ne').ae_eq h1
  rw [← (hB.toIsPreBrownianReal.hasLaw_eval t).map_eq] at h2
  filter_upwards [ae_of_ae_map (hBm t).aemeasurable h2] with ω hω
  rw [hω]

/-! ### Integrability along the endpoint, and the averaged modulus -/

/-- For `g ∈ L²`, `ω ↦ g (x + B_t ω)` is integrable for almost every `x`. -/
theorem ae_integrable_shift {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (g : L2) :
    ∀ᵐ x ∂(volume : Measure ℝ), Integrable (fun ω => g (x + B t ω)) P := by
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hμs => ?_
  filter_upwards [(integrable_shift_prod g (t : ℝ) hμs).prod_right_ae] with x hx
  rw [gaussian, Real.toNNReal_coe, ← (hB.toIsPreBrownianReal.hasLaw_eval t).map_eq] at hx
  exact (integrable_map_measure hx.aestronglyMeasurable (hBm t).aemeasurable).mp hx

/-- `|g|` as an element of `L²`. -/
noncomputable def absL (g : L2) : L2 := ((Lp.memLp g).norm.ofReal).toLp _

theorem coeFn_absL (g : L2) : (absL g : ℝ → ℂ) =ᵐ[volume] fun x => ((‖g x‖ : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem norm_absL (g : L2) : ‖absL g‖ = ‖g‖ := by
  rw [absL, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)

/-- The heat convolution depends only on the a.e.-class of the function (`t > 0`). -/
theorem heatConv_congr_ae {t : ℝ} (ht : 0 < t) {f₁ f₂ : ℝ → ℂ} (h : f₁ =ᵐ[volume] f₂) (x : ℝ) :
    heatConv t f₁ x = heatConv t f₂ x := by
  simp only [heatConv, gaussian]
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ y ∂(volume : Measure ℝ), f₁ (x + y) = f₂ (x + y) :=
    (measurePreserving_add_left volume x).quasiMeasurePreserving.ae_eq h
  exact (gaussianReal_absolutelyContinuous 0 (Real.toNNReal_pos.mpr ht).ne').ae_eq h1

/-- ★ **The averaged modulus is the heat semigroup of `|g|`**: `E‖g (x + B_t)‖ = (P_t |g|)(x)` for
almost every `x`. -/
theorem absConv_ae_eq {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ≥0} (ht : 0 < t)
    (g : L2) :
    (fun x => ((∫ ω, ‖g (x + B t ω)‖ ∂P : ℝ) : ℂ)) =ᵐ[volume] heatSemigroup (t : ℝ) (absL g) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : ∀ x, ((∫ ω, ‖g (x + B t ω)‖ ∂P : ℝ) : ℂ)
      = heatConv (t : ℝ) (fun y => ((‖g y‖ : ℝ) : ℂ)) x := by
    intro x
    rw [heatConv_eq_integral_brownian hB.toIsPreBrownianReal htR
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g).norm) x,
      Real.toNNReal_coe, integral_complex_ofReal]
  have h2 : ∀ x, heatConv (t : ℝ) (fun y => ((‖g y‖ : ℝ) : ℂ)) x = heatConv (t : ℝ) (absL g) x :=
    fun x => heatConv_congr_ae htR (coeFn_absL g).symm x
  filter_upwards [heatSemigroup_apply_ae_eq (t : ℝ) (absL g)] with x hx
  rw [h1, h2, hx]

theorem integrableOn_absConv {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ≥0} (ht : 0 < t)
    (g : L2) {A : Set ℝ} (hμA : volume A < ∞) :
    IntegrableOn (fun x => ∫ ω, ‖g (x + B t ω)‖ ∂P) A volume := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict A) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hμA⟩
  refine ((((Lp.memLp (heatSemigroup (t : ℝ) (absL g))).restrict A).integrable one_le_two).norm).congr ?_
  filter_upwards [ae_restrict_of_ae (absConv_ae_eq hB ht g)] with x hx
  rw [← hx, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]

/-- ★ `∫_A E‖g (x + B_t)‖ dx ≤ ‖1_A‖ ‖g‖`: Cauchy–Schwarz against the indicator and the contraction
property of the heat semigroup. -/
theorem setIntegral_absConv_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ≥0}
    (ht : 0 < t) (g : L2) {A : Set ℝ} (hA : MeasurableSet A) (hμA : volume A < ∞) :
    ∫ x in A, ∫ ω, ‖g (x + B t ω)‖ ∂P ≤ ‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * ‖g‖ := by
  have hre : ∫ x in A, ∫ ω, ‖g (x + B t ω)‖ ∂P
      = (∫ x in A, heatSemigroup (t : ℝ) (absL g) x).re := by
    rw [← setIntegral_congr_ae hA ((absConv_ae_eq hB ht g).mono fun x hx _ => hx),
      integral_complex_ofReal, Complex.ofReal_re]
  rw [hre, ← L2.inner_indicatorConstLp_one hA hμA.ne]
  refine le_trans (Complex.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
  rw [← norm_absL g]
  exact mul_le_mul_of_nonneg_left (norm_heatSemigroup_apply_le _ _) (norm_nonneg _)

/-! ### Bounds and measurability of the functional -/

include hCV in
theorem norm_fkFunctional_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (g : L2) :
    ∀ᵐ x ∂(volume : Measure ℝ), ‖fkFunctional V P B t g x‖
      ≤ Real.exp ((t : ℝ) * CV) * ∫ ω, ‖g (x + B t ω)‖ ∂P := by
  filter_upwards [ae_integrable_shift hB hBm t g] with x hx
  rw [fkFunctional, ← integral_const_mul]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
    (hx.norm.const_mul _) (Eventually.of_forall fun ω => ?_)
  show ‖weight V B t x ω * g (x + B t ω)‖ ≤ Real.exp ((t : ℝ) * CV) * ‖g (x + B t ω)‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_weight_le hCV B t x ω) (norm_nonneg _)

include hCV in
/-- ★ **The Wiener side is bounded on finite-measure sets**:
`‖∫_A fk g‖ ≤ e^{t‖V‖} ‖1_A‖ ‖g‖`. -/
theorem norm_setIntegral_fkFunctional_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0} (ht : 0 < t) (g : L2)
    {A : Set ℝ} (hA : MeasurableSet A) (hμA : volume A < ∞) :
    ‖∫ x in A, fkFunctional V P B t g x‖
      ≤ Real.exp ((t : ℝ) * CV) * (‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * ‖g‖) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  calc ∫ x in A, ‖fkFunctional V P B t g x‖
      ≤ ∫ x in A, Real.exp ((t : ℝ) * CV) * ∫ ω, ‖g (x + B t ω)‖ ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          ((integrableOn_absConv hB ht g hμA).const_mul _)
          (ae_restrict_of_ae (norm_fkFunctional_le hCV hB hBm t g))
    _ = Real.exp ((t : ℝ) * CV) * ∫ x in A, ∫ ω, ‖g (x + B t ω)‖ ∂P := integral_const_mul _ _
    _ ≤ Real.exp ((t : ℝ) * CV) * (‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * ‖g‖) := by
        gcongr
        exact setIntegral_absConv_le hB ht g hA hμA

include hCV in
/-- The functional is a.e.-strongly measurable: an a.e. pointwise limit of the sliced
functionals. -/
theorem aestronglyMeasurable_fkFunctional [IsProbabilityMeasure P] (hVc : Continuous V)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0}
    (ht : 0 < t) (g : L2) :
    AEStronglyMeasurable (fkFunctional V P B t g) (volume : Measure ℝ) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n : ℕ => slicedWiener P B (t / n)
      (fun z => Complex.exp (-((((t : ℝ) / n : ℝ) : ℂ) * (V z : ℂ)))) g n)
    (fun n => (measurable_slicedWiener hBm _ (measurable_expFun hVc.measurable _)
      (Lp.stronglyMeasurable g).measurable n).aestronglyMeasurable) ?_
  filter_upwards [ae_integrable_shift hB hBm t g] with x hx
  exact tendsto_slicedWiener hCV hB hBm hVc (Lp.stronglyMeasurable g).measurable ht x hx

include hCV in
theorem integrableOn_fkFunctional [IsProbabilityMeasure P] (hVc : Continuous V)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ≥0}
    (ht : 0 < t) (g : L2) {A : Set ℝ} (hμA : volume A < ∞) :
    IntegrableOn (fkFunctional V P B t g) A volume :=
  ((integrableOn_absConv hB ht g hμA).const_mul _).mono'
    (aestronglyMeasurable_fkFunctional hCV hVc hB hBm ht g).restrict
    (ae_restrict_of_ae (norm_fkFunctional_le hCV hB hBm t g))

/-! ### Feynman–Kac on `L²` -/

include hCV in
/-- Feynman–Kac for a simple function, from `FeynmanKac.feynmanKac`. -/
theorem feynmanKac_simpleFunc [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hVc : Continuous V) {VL : Lp ℂ ∞ (volume : Measure ℝ)}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ≥0} (ht : 0 < t)
    (s : Lp.simpleFunc ℂ 2 (volume : Measure ℝ)) :
    (perturbedHeat VL (t : ℝ) (s : L2) : ℝ → ℂ) =ᵐ[volume] fkFunctional V P B t (s : L2) := by
  obtain ⟨C, hC⟩ := (Lp.simpleFunc.toSimpleFunc s).exists_forall_norm_le
  have h := feynmanKac hCV hB hBm hVc hVL (Lp.simpleFunc.toSimpleFunc s).measurable hC
    (Lp.simpleFunc.memLp s) ht
  have hs : (Lp.simpleFunc.memLp s).toLp _ = (s : L2) := by
    rw [← Lp.simpleFunc.toLp_eq_toLp, Lp.simpleFunc.toLp_toSimpleFunc]
  rw [hs] at h
  refine h.trans (Eventually.of_forall fun x => ?_)
  exact fkFunctional_congr_ae hB hBm ht (Lp.simpleFunc.toSimpleFunc_eq_toFun s) x

include hCV in
/-- ★★ **The Feynman–Kac formula on all of `L²`.** For a Brownian motion `B` with almost surely
continuous paths, a bounded continuous potential `V` (with `VL` its `L^∞` class) and **every**
`g ∈ L²`,

  `(e^{−t(H₀+V)} g)(x) = E[ exp (−∫₀ᵗ V (x + B_s) ds) · g (x + B_t) ]`  for a.e. `x`.

Both sides are continuous in `g` on every finite-measure set and agree on the dense set of simple
functions (`FeynmanKac.feynmanKac`). -/
theorem feynmanKac_Lp [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hVc : Continuous V) {VL : Lp ℂ ∞ (volume : Measure ℝ)}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) (g : L2) {t : ℝ≥0} (ht : 0 < t) :
    (perturbedHeat VL (t : ℝ) g : ℝ → ℂ) =ᵐ[volume] fun x =>
      ∫ ω, Complex.exp (-(((∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) : ℝ) : ℂ))
        * g (x + B t ω) ∂P := by
  show (perturbedHeat VL (t : ℝ) g : ℝ → ℂ) =ᵐ[volume] fkFunctional V P B t g
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A _ hμA => ?_)
    (fun A _ hμA => integrableOn_fkFunctional hCV hVc hB hBm ht g hμA) (fun A hA hμA => ?_)
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict A) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμA⟩
    exact ((Lp.memLp (perturbedHeat VL (t : ℝ) g)).restrict A).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict A) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμA⟩
    set K := ‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖
      * (‖perturbedHeat VL (t : ℝ)‖ + Real.exp ((t : ℝ) * CV)) with hK
    have hK0 : 0 ≤ K := by positivity
    -- the operator side on `A`, for any `h ∈ L²`
    have hPHint : ∀ h : L2, IntegrableOn (perturbedHeat VL (t : ℝ) h) A volume := fun h =>
      ((Lp.memLp (perturbedHeat VL (t : ℝ) h)).restrict A).integrable one_le_two
    have hPHle : ∀ h : L2, ‖∫ x in A, perturbedHeat VL (t : ℝ) h x‖
        ≤ ‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * (‖perturbedHeat VL (t : ℝ)‖ * ‖h‖) := by
      intro h
      rw [← L2.inner_indicatorConstLp_one hA hμA.ne]
      exact le_trans (norm_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    -- the difference of the two set integrals is at most `K ε` for every `ε > 0`
    have key : ∀ ε > 0, ‖(∫ x in A, perturbedHeat VL (t : ℝ) g x)
        - ∫ x in A, fkFunctional V P B t g x‖ ≤ K * ε := by
      intro ε hε
      obtain ⟨s, hs⟩ := (Lp.simpleFunc.denseRange (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
        ENNReal.ofNat_ne_top).exists_dist_lt g hε
      rw [dist_eq_norm] at hs
      have hPH : (∫ x in A, perturbedHeat VL (t : ℝ) g x) - ∫ x in A, perturbedHeat VL (t : ℝ) (s : L2) x
          = ∫ x in A, perturbedHeat VL (t : ℝ) (g - s) x := by
        rw [← integral_sub (hPHint g) (hPHint s)]
        refine setIntegral_congr_ae hA ?_
        filter_upwards [Lp.coeFn_sub (perturbedHeat VL (t : ℝ) g) (perturbedHeat VL (t : ℝ) s)]
          with x hx _
        rw [map_sub, hx, Pi.sub_apply]
      have hFK : (∫ x in A, fkFunctional V P B t g x) - ∫ x in A, fkFunctional V P B t (s : L2) x
          = ∫ x in A, fkFunctional V P B t (g - s : L2) x := by
        rw [← integral_sub (integrableOn_fkFunctional hCV hVc hB hBm ht g hμA)
          (integrableOn_fkFunctional hCV hVc hB hBm ht s hμA)]
        refine setIntegral_congr_ae hA ?_
        filter_upwards [ae_integrable_shift hB hBm t g, ae_integrable_shift hB hBm t s]
          with x hxg hxs _
        rw [fkFunctional_congr_ae hB hBm ht (Lp.coeFn_sub g s) x, fkFunctional, fkFunctional,
          fkFunctional, ← integral_sub (integrable_weight_mul hCV hVc hB hBm ht hxg)
            (integrable_weight_mul hCV hVc hB hBm ht hxs)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.sub_apply]
        ring
      have hs0 : ∫ x in A, perturbedHeat VL (t : ℝ) (s : L2) x
          = ∫ x in A, fkFunctional V P B t (s : L2) x :=
        setIntegral_congr_ae hA ((feynmanKac_simpleFunc hCV hB hBm hVc hVL ht s).mono
          fun x hx _ => hx)
      calc ‖(∫ x in A, perturbedHeat VL (t : ℝ) g x) - ∫ x in A, fkFunctional V P B t g x‖
          = ‖((∫ x in A, perturbedHeat VL (t : ℝ) g x)
                - ∫ x in A, perturbedHeat VL (t : ℝ) (s : L2) x)
              - ((∫ x in A, fkFunctional V P B t g x)
                - ∫ x in A, fkFunctional V P B t (s : L2) x)‖ := by
            rw [hs0]
            congr 1
            abel
        _ = ‖(∫ x in A, perturbedHeat VL (t : ℝ) (g - s) x)
              - ∫ x in A, fkFunctional V P B t (g - s : L2) x‖ := by rw [hPH, hFK]
        _ ≤ ‖∫ x in A, perturbedHeat VL (t : ℝ) (g - s) x‖
              + ‖∫ x in A, fkFunctional V P B t (g - s : L2) x‖ := norm_sub_le _ _
        _ ≤ ‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * (‖perturbedHeat VL (t : ℝ)‖ * ‖g - s‖)
              + Real.exp ((t : ℝ) * CV) * (‖indicatorConstLp 2 hA hμA.ne (1 : ℂ)‖ * ‖g - s‖) :=
            add_le_add (hPHle _)
              (norm_setIntegral_fkFunctional_le hCV hB hBm ht (g - s) hA hμA)
        _ = K * ‖g - s‖ := by rw [hK]; ring
        _ ≤ K * ε := mul_le_mul_of_nonneg_left hs.le hK0
    have hzero : ‖(∫ x in A, perturbedHeat VL (t : ℝ) g x)
        - ∫ x in A, fkFunctional V P B t g x‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      rw [zero_add]
      rcases eq_or_lt_of_le hK0 with h0 | hKpos
      · have := key 1 one_pos
        rw [← h0, zero_mul] at this
        exact this.trans hδ.le
      · have := key (δ / K) (div_pos hδ hKpos)
        rwa [mul_div_cancel₀ _ hKpos.ne'] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

end FeynmanKac
