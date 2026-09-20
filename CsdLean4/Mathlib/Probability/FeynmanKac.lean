/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.TimeSlicedWiener

/-!
# The Feynman–Kac formula

**Category:** 1-Mathlib (CSD-free; staged for upstream).

For a Brownian motion `B` with almost surely continuous paths, a bounded continuous potential `V`
and a bounded `f ∈ L²(ℝ)`,

  `(e^{−t(H₀ + V)} f)(x) = E[ f (x + B_t) · exp (−∫₀ᵗ V (x + B_s) ds) ]`  for a.e. `x`,

where `e^{−t(H₀+V)}` is the perturbed heat semigroup of `HeatSemigroup.lean` (the Dyson series
around `P_t` with interaction `−V`; no generator is written). The Euclidean path integral is a
Wiener integral, as Kac stated it in 1949.

The proof joins the two limits of the same time-sliced expression:
* the **operator side** converges by the Trotter product formula (`tendsto_trotter_perturbedHeat`),
  once `exp (−h M_V) = M_{e^{−hV}}` (★ `exp_smul_neg_potential`, the exponential of a multiplication
  operator is multiplication by the exponential);
* the **Wiener side** is the time-sliced functional of `TimeSlicedWiener.lean`, whose Riemann sums
  along the continuous path converge (`tendsto_riemannSum`) and are dominated;
* the two limits agree because their integrals over every finite-measure set agree
  (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`).

* `expPot hV h` — the `L^∞` class of `e^{−hV}`; ★ `exp_smul_neg_potential`;
* `tendsto_riemannSum` — Riemann sums of a continuous function on `[0, t]`;
* ★★ `feynmanKac` — **the Feynman–Kac formula**.

## Honest scope

⚠️ **Conditional on a Brownian motion.** `hB : IsBrownianReal B P` (almost surely continuous
paths) is a hypothesis; the Mathlib pin does not yet construct one. Bounded continuous `V`, bounded
measurable `f ∈ L²`; one dimension. The extension to `f ∈ L²` alone is by continuity of both sides
and is not stated here.

References: M. Kac, *On distributions of certain Wiener functionals*, Trans. AMS 65, 1 (1949);
B. Simon, *Functional Integration and Quantum Physics*, Thm 6.2; `Probability/TimeSlicedWiener.lean`
(FC-3); `Analysis/Semigroup/HeatSemigroup.lean` (FC-2); `Analysis/Semigroup/BoundedPerturbation.lean`
(FC-1); `specs/feynman-continuum-scoping.md` (FC-4); `specs/BACKLOG.md` #36(c).
-/

@[expose] public section

open scoped ENNReal NNReal Topology Nat
open MeasureTheory ProbabilityTheory Filter HeatSemigroup TimeSlicedWiener NormedSpace

namespace FeynmanKac

/-- `L²(ℝ, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The exponential of a multiplication operator -/

/-- The coercion of a finite sum of `Lp` elements is the sum of the coercions, almost everywhere. -/
theorem coeFn_sum_range {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (u : ℕ → Lp F p μ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, u n : Lp F p μ) : α → F) =ᵐ[μ] fun x => ∑ n ∈ Finset.range N, u n x := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
  | succ N ih =>
    rw [Finset.sum_range_succ]
    filter_upwards [Lp.coeFn_add (∑ n ∈ Finset.range N, u n) (u N), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_range_succ]

variable {V : ℝ → ℝ} (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV)
include hVm hCV

omit hCV in
theorem measurable_expFun (h : ℝ) :
    Measurable fun x : ℝ => Complex.exp (-((h : ℂ) * (V x : ℂ))) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hVm)).neg

omit hVm in
theorem norm_expFun_le (h : ℝ) (x : ℝ) :
    ‖Complex.exp (-((h : ℂ) * (V x : ℂ)))‖ ≤ Real.exp (|h| * CV) := by
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  refine Real.exp_le_exp.mpr ?_
  calc -(h * V x) ≤ |h * V x| := neg_le_abs _
    _ = |h| * |V x| := abs_mul _ _
    _ ≤ |h| * CV := by gcongr; exact hCV x

theorem memLp_expFun (h : ℝ) :
    MemLp (fun x : ℝ => Complex.exp (-((h : ℂ) * (V x : ℂ)))) ∞ volume :=
  memLp_top_of_bound (measurable_expFun hVm h).aestronglyMeasurable (Real.exp (|h| * CV))
    (Eventually.of_forall (norm_expFun_le hCV h))

/-- The `L^∞` class of `e^{−h V}`. -/
noncomputable def expPot (h : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_expFun hVm hCV h).toLp _

theorem coeFn_expPot (h : ℝ) :
    (expPot hVm hCV h : ℝ → ℂ) =ᵐ[volume] fun x => Complex.exp (-((h : ℂ) * (V x : ℂ))) :=
  MemLp.coeFn_toLp _

omit hVm hCV in
/-- The powers of the multiplication operator by `−V`, pointwise. -/
theorem neg_potential_pow_apply_ae_eq {VL : Lp ℂ ∞ (volume : Measure ℝ)}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) (f : L2) :
    ∀ n : ℕ, (((-potential VL) ^ n) f : ℝ → ℂ) =ᵐ[volume] fun x => (-(V x : ℂ)) ^ n * f x := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, one_apply_eq_self]
    exact Eventually.of_forall fun x => by simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, neg_apply]
    filter_upwards [Lp.coeFn_neg (potential VL (((-potential VL) ^ n) f)),
      coeFn_potential VL (((-potential VL) ^ n) f), hVL, ih] with x h1 h2 h3 h4
    rw [h1, Pi.neg_apply, h2, h3, h4]
    ring

omit hVm hCV in
/-- The partial sums of the exponential series are bounded by `e^{|c|}`. -/
theorem norm_sum_pow_div_factorial_le (c : ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, c ^ n / (n ! : ℂ)‖ ≤ Real.exp ‖c‖ := by
  calc ‖∑ n ∈ Finset.range N, c ^ n / (n ! : ℂ)‖
      ≤ ∑ n ∈ Finset.range N, ‖c ^ n / (n ! : ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖c‖ ^ n / (n ! : ℝ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖c‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) N

set_option maxHeartbeats 800000 in
/-- ★ **The exponential of a multiplication operator is multiplication by the exponential**:
`exp (h • (−M_V)) = M_{e^{−hV}}` on `L²`. -/
theorem exp_smul_neg_potential {VL : Lp ℂ ∞ (volume : Measure ℝ)}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) (h : ℝ) :
    exp (h • (-potential VL)) = potential (expPot hVm hCV h) := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  set A : L2 →L[ℂ] L2 := -potential VL
  -- the series in the operator algebra, applied to `f`
  have hsum := (ContinuousLinearMap.apply ℂ L2 f).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) (h • A))
  have hlim := hsum.tendsto_sum_nat
  simp only [ContinuousLinearMap.apply_apply] at hlim
  -- the partial sums, pointwise
  have hpartial : ∀ N : ℕ,
      ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • (h • A) ^ n) f : L2) : ℝ → ℂ)
        =ᵐ[volume] fun x => (∑ n ∈ Finset.range N, (-((h : ℂ) * V x)) ^ n / n !) * f x := by
    intro N
    have hterm : ∀ n : ℕ, ((((n ! : ℝ)⁻¹ • (h • A) ^ n) f : L2) : ℝ → ℂ)
        =ᵐ[volume] fun x => (-((h : ℂ) * V x)) ^ n / n ! * f x := by
      intro n
      rw [smul_apply, smul_pow, smul_apply]
      filter_upwards [Lp.coeFn_smul ((n ! : ℝ)⁻¹) (h ^ n • (A ^ n) f),
        Lp.coeFn_smul (h ^ n) ((A ^ n) f), neg_potential_pow_apply_ae_eq hVL f n] with x h1 h2 h3
      rw [h1, Pi.smul_apply, h2, Pi.smul_apply, h3]
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_pow]
      rw [neg_mul_eq_mul_neg, mul_pow]
      field_simp
    have hsumN := coeFn_sum_range (fun n => ((n ! : ℝ)⁻¹ • (h • A) ^ n) f) N
    filter_upwards [hsumN, ae_all_iff.mpr hterm] with x hx hx'
    rw [hx, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => hx' n
  -- identification on every finite-measure set
  have hbound : ∀ N x, ‖(∑ n ∈ Finset.range N, (-((h : ℂ) * V x)) ^ n / n !) * f x‖
      ≤ Real.exp (|h| * CV) * ‖f x‖ := by
    intro N x
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sum_pow_div_factorial_le _ N) (Real.exp_le_exp.mpr ?_)
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    gcongr
    exact hCV x
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hμs => ?_) (fun s _ hμs => ?_)
    (fun s hs hμs => ?_)
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (exp (h • A) f)).restrict s).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (potential (expPot hVm hCV h) f)).restrict s).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    have hfint : Integrable (fun x => Real.exp (|h| * CV) * ‖f x‖) ((volume : Measure ℝ).restrict s) :=
      (((Lp.memLp f).restrict s).integrable one_le_two).norm.const_mul _
    -- the set integrals of the partial sums converge to both sides
    have h1 : Tendsto (fun N => ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • (h • A) ^ n) f : L2) x))
        atTop (𝓝 (∫ x in s, exp (h • A) f x)) := by
      have hcont : Continuous fun g : L2 => ∫ x in s, g x := by
        have : (fun g : L2 => ∫ x in s, g x)
            = fun g => inner ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) g := by
          funext g
          rw [L2.inner_indicatorConstLp_one hs hμs.ne]
        rw [this]
        exact continuous_const.inner continuous_id
      exact (hcont.tendsto _).comp hlim
    have h2 : Tendsto (fun N => ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • (h • A) ^ n) f : L2) x))
        atTop (𝓝 (∫ x in s, Complex.exp (-((h : ℂ) * V x)) * f x)) := by
      have hrw : ∀ N, ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • (h • A) ^ n) f : L2) x)
          = ∫ x in s, (∑ n ∈ Finset.range N, (-((h : ℂ) * V x)) ^ n / n !) * f x :=
        fun N => integral_congr_ae (ae_restrict_of_ae (hpartial N))
      simp_rw [hrw]
      refine tendsto_integral_filter_of_dominated_convergence (fun x => Real.exp (|h| * CV) * ‖f x‖)
        (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => Eventually.of_forall fun x => hbound N x)
        hfint (Eventually.of_forall fun x => ?_)
      · have hVc : Measurable fun x : ℝ => (V x : ℂ) := Complex.measurable_ofReal.comp hVm
        have hsm : Measurable fun x : ℝ => ∑ n ∈ Finset.range N, (-((h : ℂ) * V x)) ^ n / (n ! : ℂ) :=
          Finset.measurable_sum _ fun n _ => ((measurable_const.mul hVc).neg.pow_const n).div_const _
        exact hsm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).restrict
      · refine Tendsto.mul_const _ ?_
        rw [Complex.exp_eq_exp_ℂ]
        exact (expSeries_div_hasSum_exp (-((h : ℂ) * V x))).tendsto_sum_nat
    rw [tendsto_nhds_unique h1 h2]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [coeFn_potential (expPot hVm hCV h) f, coeFn_expPot hVm hCV h] with x hx hx'
    rw [hx, hx']

/-! ### Riemann sums along a continuous path -/

omit hVm hCV in
/-- Riemann sums of a continuous function on `[0, t]` converge to its integral. -/
theorem tendsto_riemannSum (g : ℝ → ℝ) (hg : Continuous g) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => (t / n) * ∑ k ∈ Finset.range n, g (((k : ℝ) + 1) * t / n)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, g s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := (isCompact_Icc (a := (0 : ℝ)) (b := t)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (ε / (2 * t)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hstep : t / n ≤ δ := by
    rw [div_le_iff₀ hn0]
    have : t / δ < n := lt_of_lt_of_le hN (by exact_mod_cast (show N ≤ n by omega))
    rw [div_lt_iff₀ hδ] at this
    linarith
  set a : ℕ → ℝ := fun k => k * t / n with ha
  have ha_mem : ∀ k, k ≤ n → a k ∈ Set.Icc (0 : ℝ) t := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [ha]
    show (k : ℝ) * t / n ≤ t
    rw [div_le_iff₀ hn0]
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  have ha_succ : ∀ k, a (k + 1) - a k = t / n := by
    intro k
    simp only [ha, Nat.cast_succ]
    ring
  have hpart : ∫ s in (0 : ℝ)..t, g s = ∑ k ∈ Finset.range n, ∫ s in a k..a (k + 1), g s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg.intervalIntegrable _ _)]
    simp only [ha, Nat.cast_zero, zero_mul, zero_div]
    rw [show (n : ℝ) * t / n = t from by field_simp]
  have hconst : ∀ k : ℕ, (t / n) * g (((k : ℝ) + 1) * t / n)
      = ∫ _ in a k..a (k + 1), g (((k : ℝ) + 1) * t / n) := by
    intro k
    rw [intervalIntegral.integral_const, smul_eq_mul, ha_succ]
  rw [Real.dist_eq, Finset.mul_sum, hpart, ← Finset.sum_sub_distrib]
  simp_rw [hconst]
  have hsub : ∀ k ∈ Finset.range n,
      (∫ _ in a k..a (k + 1), g (((k : ℝ) + 1) * t / n)) - ∫ s in a k..a (k + 1), g s
        = ∫ s in a k..a (k + 1), (g (((k : ℝ) + 1) * t / n) - g s) := fun k _ =>
    (intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)).symm
  rw [Finset.sum_congr rfl hsub]
  have hpiece : ∀ k ∈ Finset.range n,
      |∫ s in a k..a (k + 1), (g (((k : ℝ) + 1) * t / n) - g s)| ≤ ε / (2 * t) * (t / n) := by
    intro k hk
    have hk' : k + 1 ≤ n := Finset.mem_range.mp hk
    have hle : a k ≤ a (k + 1) := by
      have := ha_succ k
      have : 0 ≤ t / n := by positivity
      linarith
    rw [← Real.norm_eq_abs]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / (2 * t))
      fun s hs => ?_) ?_
    · rw [Set.uIoc_of_le hle] at hs
      have hs0 : s ∈ Set.Icc (0 : ℝ) t :=
        ⟨le_trans (ha_mem k (by omega)).1 hs.1.le, le_trans hs.2 (ha_mem (k + 1) hk').2⟩
      have hx : ((k : ℝ) + 1) * t / n = a (k + 1) := by simp [ha]
      rw [Real.norm_eq_abs, ← Real.dist_eq, hx]
      refine hδ' _ (ha_mem (k + 1) hk') _ hs0 ?_
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.2])]
      have := ha_succ k
      linarith [hs.1, hstep]
    · rw [ha_succ, abs_of_pos (by positivity)]
  calc |∑ k ∈ Finset.range n, ∫ s in a k..a (k + 1), (g (((k : ℝ) + 1) * t / n) - g s)|
      ≤ ∑ k ∈ Finset.range n, |∫ s in a k..a (k + 1), (g (((k : ℝ) + 1) * t / n) - g s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ε / (2 * t) * (t / n) := Finset.sum_le_sum hpiece
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ < ε := by linarith

/-! ### The Wiener side -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit hVm hCV [MeasurableSpace Ω] in
/-- The sliced weight is the exponential of a Riemann sum. -/
theorem prod_exp_eq (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) (ω : Ω) :
    (∏ k ∈ Finset.range n, Complex.exp (-(((h : ℝ) : ℂ) * (V (x + B (((k + 1 : ℕ) : ℝ≥0) * h) ω) : ℂ))))
        * f (x + B ((n : ℝ≥0) * h) ω)
      = Complex.exp (-(((h : ℝ) * ∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * h) ω) : ℝ) : ℂ))
        * f (x + B ((n : ℝ≥0) * h) ω) := by
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

omit hVm [MeasurableSpace Ω] in
/-- The Riemann sums of the potential along the path are bounded by `t · CV`. -/
theorem abs_riemann_le (B : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} {n : ℕ} (hn : 0 < n) (x : ℝ) (ω : Ω) :
    |((t : ℝ) / n) * ∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω)|
      ≤ (t : ℝ) * CV := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCV0 : 0 ≤ CV := le_trans (abs_nonneg _) (hCV 0)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) / n)]
  calc (t : ℝ) / n * |∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω)|
      ≤ (t : ℝ) / n * ∑ k ∈ Finset.range n, |V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (t : ℝ) / n * ∑ _k ∈ Finset.range n, CV := by
        gcongr with k _
        exact hCV _
    _ = (t : ℝ) * CV := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

omit hVm hCV in
/-- The time-sliced functional is bounded by `Cg ^ n · Cf`. -/
theorem norm_slicedWiener_le [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) {g f : ℝ → ℂ}
    {Cg Cf : ℝ} (hCg : ∀ x, ‖g x‖ ≤ Cg) (hCf : ∀ x, ‖f x‖ ≤ Cf) (n : ℕ) (x : ℝ) :
    ‖slicedWiener P B h g f n x‖ ≤ Cg ^ n * Cf := by
  rw [slicedWiener]
  refine le_trans (norm_integral_le_of_norm_le (integrable_const _)
    (Eventually.of_forall fun ω => norm_pathFunctional_le hCg hCf h n (x, fun t => B t ω))) ?_
  simp

omit hVm hCV in
/-- The index of the `k`-th slice end, as a nonnegative real. -/
theorem toNNReal_slice (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Real.toNNReal (((k : ℝ) + 1) * (t : ℝ) / n) = ((k + 1 : ℕ) : ℝ≥0) * (t / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine NNReal.coe_injective ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast
  ring

omit hVm hCV [MeasurableSpace Ω] in
/-- Along a continuous path, the Riemann sums of the potential converge to its time integral. -/
theorem tendsto_riemann_path (hVc : Continuous V) {B : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (ht : 0 < t) (x : ℝ)
    {ω : Ω} (hω : Continuous fun s => B s ω) :
    Tendsto (fun n : ℕ =>
        ((t : ℝ) / n) * ∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω)) atTop
      (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω))) := by
  have hG : Continuous fun s : ℝ => V (x + B (Real.toNNReal s) ω) :=
    hVc.comp (continuous_const.add (hω.comp continuous_real_toNNReal))
  have := tendsto_riemannSum _ hG (by exact_mod_cast ht : (0 : ℝ) < t)
  refine this.congr' (Eventually.of_forall fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toNNReal_slice t hn k]

omit hVm in
/-- **The Wiener-side limit**: along a Brownian motion with continuous paths, the time-sliced
functional with weight `e^{−(t/n) V}` converges to the Feynman–Kac functional, for any measurable
`f` integrable along the endpoint `x + B_t` (bounded `f` in particular). -/
theorem tendsto_slicedWiener {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hVc : Continuous V) {f : ℝ → ℂ} (hf : Measurable f) {t : ℝ≥0}
    (ht : 0 < t) (x : ℝ) (hfi : Integrable (fun ω => f (x + B t ω)) P) :
    Tendsto (fun n : ℕ => slicedWiener P B (t / n)
        (fun z => Complex.exp (-((((t : ℝ) / n : ℝ) : ℂ) * (V z : ℂ)))) f n x) atTop
      (𝓝 (∫ ω, Complex.exp (-(((∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) : ℝ) : ℂ))
        * f (x + B t ω) ∂P)) := by
  set R : ℕ → Ω → ℝ := fun n ω =>
    ((t : ℝ) / n) * ∑ k ∈ Finset.range n, V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω) with hR
  set I : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω) with hI
  simp only [slicedWiener]
  -- the integrands, rewritten for `n ≥ 1`
  have hrw : ∀ n : ℕ, 0 < n → ∀ ω,
      (∏ k ∈ Finset.range n, Complex.exp (-((((t : ℝ) / n : ℝ) : ℂ)
          * (V (x + B (((k + 1 : ℕ) : ℝ≥0) * (t / n)) ω) : ℂ))))
        * f (x + B ((n : ℝ≥0) * (t / n)) ω)
      = Complex.exp (-((R n ω : ℝ) : ℂ)) * f (x + B t ω) := by
    intro n hn ω
    have hnt : (n : ℝ≥0) * (t / n) = t := by
      rw [mul_div_cancel₀]
      exact_mod_cast hn.ne'
    have := prod_exp_eq (V := V) B (t / n) f n x ω
    rw [NNReal.coe_div, NNReal.coe_natCast] at this
    rw [this, hnt]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => Real.exp ((t : ℝ) * CV) * ‖f (x + B t ω)‖)
    (Eventually.of_forall fun n => ?_) ?_ (hfi.norm.const_mul _) ?_
  · -- measurability of the sliced integrand
    refine Measurable.aestronglyMeasurable (Measurable.mul (Finset.measurable_prod _ fun k _ => ?_) ?_)
    · exact (measurable_expFun hVc.measurable _).comp (measurable_const.add (hBm _))
    · exact hf.comp (measurable_const.add (hBm _))
  · -- the domination, for `n ≥ 1`
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Eventually.of_forall fun ω => ?_
    rw [hrw n hn ω, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact le_trans (neg_le_abs _) (abs_riemann_le hCV B hn x ω)
  · -- the pointwise limit, along continuous paths
    filter_upwards [hB.cont] with ω hω
    have hRlim : Tendsto (fun n => R n ω) atTop (𝓝 (I ω)) := tendsto_riemann_path hVc ht x hω
    have hexp : Tendsto (fun n => Complex.exp (-((R n ω : ℝ) : ℂ)) * f (x + B t ω)) atTop
        (𝓝 (Complex.exp (-((I ω : ℝ) : ℂ)) * f (x + B t ω))) := by
      refine Tendsto.mul_const _ ?_
      exact (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hRlim).neg)
    refine hexp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hrw n hn ω).symm

/-! ### Feynman–Kac -/

omit hVm in
set_option maxHeartbeats 800000 in
/-- ★★ **The Feynman–Kac formula.** For a Brownian motion `B` with almost surely continuous paths,
a bounded continuous potential `V` (with `VL` its `L^∞` class) and a bounded measurable `f ∈ L²`,

  `(e^{−t(H₀+V)} f)(x) = E[ exp (−∫₀ᵗ V (x + B_s) ds) · f (x + B_t) ]`  for a.e. `x`,

where `e^{−t(H₀+V)}` is the perturbed heat semigroup (the Dyson series around `P_t`). The Euclidean
path integral is a Wiener integral: the operator side is the Trotter limit of the time-sliced
products, the Wiener side the limit of the time-sliced functionals, and the two agree on every
finite-measure set. -/
theorem feynmanKac [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hVc : Continuous V) {VL : Lp ℂ ∞ (volume : Measure ℝ)}
    (hVL : (VL : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {f : ℝ → ℂ} (hf : Measurable f) {Cf : ℝ}
    (hCf : ∀ x, ‖f x‖ ≤ Cf) (hf2 : MemLp f 2 volume) {t : ℝ≥0} (ht : 0 < t) :
    (perturbedHeat VL (t : ℝ) (hf2.toLp f) : ℝ → ℂ) =ᵐ[volume] fun x =>
      ∫ ω, Complex.exp (-(((∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) : ℝ) : ℂ))
        * f (x + B t ω) ∂P := by
  have hVm := hVc.measurable
  have hCV0 : 0 ≤ CV := le_trans (abs_nonneg _) (hCV 0)
  set fL : L2 := hf2.toLp f with hfL
  set FK : ℝ → ℂ := fun x =>
    ∫ ω, Complex.exp (-(((∫ s in (0 : ℝ)..(t : ℝ), V (x + B (Real.toNNReal s) ω)) : ℝ) : ℂ))
      * f (x + B t ω) ∂P with hFK
  set gn : ℕ → ℝ → ℂ := fun n z => Complex.exp (-((((t : ℝ) / n : ℝ) : ℂ) * (V z : ℂ))) with hgn
  set Wn : ℕ → ℝ → ℂ := fun n => slicedWiener P B (t / n) (gn n) f n with hWn
  -- the operator side, for `n ≥ 1`: the Trotter step is the heat–potential step
  have hop : ∀ n : ℕ, 0 < n →
      ContractionSemigroup.trotterStep heatSemigroup (-potential VL) ((t : ℝ) / n)
        = stepOp (t / n) (expPot hVm hCV ((t : ℝ) / n)) := by
    intro n _
    rw [ContractionSemigroup.trotterStep, stepOp, NNReal.coe_div, NNReal.coe_natCast]
    congr 1
    exact exp_smul_neg_potential hVm hCV hVL _
  have hslice : ∀ n : ℕ, 0 < n →
      ((stepOp (t / n) (expPot hVm hCV ((t : ℝ) / n)) ^ n) fL : ℝ → ℂ) =ᵐ[volume] Wn n := by
    intro n hn
    have hh : (0 : ℝ≥0) < t / n := div_pos ht (by exact_mod_cast hn)
    exact pow_stepOp_apply_ae_eq_slicedWiener hh (measurable_expFun hVm _) hf (norm_expFun_le hCV _)
      hCf hf2 (coeFn_expPot hVm hCV _) n B hB.toIsPreBrownianReal hBm
  -- the Wiener side
  have hlim : ∀ x, Tendsto (fun n => Wn n x) atTop (𝓝 (FK x)) := fun x =>
    tendsto_slicedWiener hCV hB hBm hVc hf ht x
      (Integrable.of_bound (hf.comp (measurable_const.add (hBm t))).aestronglyMeasurable Cf
        (Eventually.of_forall fun ω => hCf _))
  have hWb : ∀ n : ℕ, 0 < n → ∀ x, ‖Wn n x‖ ≤ Real.exp ((t : ℝ) * CV) * Cf := by
    intro n hn x
    refine le_trans (norm_slicedWiener_le B (t / n) (norm_expFun_le hCV _) hCf n x) ?_
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.exp_nat_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (le_trans (norm_nonneg _) (hCf 0))
    congr 1
    field_simp
  have hFKm : Measurable FK :=
    measurable_of_tendsto_metrizable
      (fun n => measurable_slicedWiener hBm _ (measurable_expFun hVm _) hf n) (tendsto_pi_nhds.mpr hlim)
  have hFKb : ∀ x, ‖FK x‖ ≤ Real.exp ((t : ℝ) * CV) * Cf := fun x =>
    le_of_tendsto (hlim x).norm (by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact hWb n hn x)
  -- the Trotter limit on the operator side
  have htrot := tendsto_trotter_perturbedHeat VL (t := (t : ℝ)) (by positivity) fL
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hμs => ?_) (fun s _ hμs => ?_)
    (fun s hs hμs => ?_)
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (perturbedHeat VL (t : ℝ) fL)).restrict s).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact Integrable.of_bound hFKm.aestronglyMeasurable _ (Eventually.of_forall hFKb)
  · have : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    have hcont : Continuous fun g : L2 => ∫ x in s, g x := by
      have : (fun g : L2 => ∫ x in s, g x)
          = fun g => inner ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) g := by
        funext g
        rw [L2.inner_indicatorConstLp_one hs hμs.ne]
      rw [this]
      exact continuous_const.inner continuous_id
    have h1 : Tendsto (fun n : ℕ => ∫ x in s,
        ((ContractionSemigroup.trotterStep heatSemigroup (-potential VL) ((t : ℝ) / n) ^ n) fL) x)
        atTop (𝓝 (∫ x in s, perturbedHeat VL (t : ℝ) fL x)) :=
      (hcont.tendsto _).comp htrot
    have h2 : Tendsto (fun n : ℕ => ∫ x in s,
        ((ContractionSemigroup.trotterStep heatSemigroup (-potential VL) ((t : ℝ) / n) ^ n) fL) x)
        atTop (𝓝 (∫ x in s, FK x)) := by
      have hrw : (fun n : ℕ => ∫ x in s, Wn n x) =ᶠ[atTop] fun n : ℕ => ∫ x in s,
          ((ContractionSemigroup.trotterStep heatSemigroup (-potential VL) ((t : ℝ) / n) ^ n) fL) x := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hop n hn]
        exact (integral_congr_ae (ae_restrict_of_ae (hslice n hn))).symm
      refine Tendsto.congr' hrw ?_
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp ((t : ℝ) * CV) * Cf)
        (Eventually.of_forall fun n =>
          (measurable_slicedWiener hBm _ (measurable_expFun hVm _) hf n).aestronglyMeasurable) ?_
        (integrable_const _) (Eventually.of_forall fun x => hlim x)
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact Eventually.of_forall fun x => hWb n hn x
    rw [tendsto_nhds_unique h1 h2]

end FeynmanKac
