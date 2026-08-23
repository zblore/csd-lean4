/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Data.Nat.Dist

/-!
# Quantitative correlation decay forces time averages to the space average

**Category:** 1-Mathlib. Nothing here mentions CSD; this is elementary ergodic-theory-flavoured
measure theory, and it is the engine the equilibration arc's E4 needs
(`specs/equilibration-arc-plan.md`).

## The statement, and why it is shaped this way

E4 wants: *if the flow has decaying correlations, then time-averaged observables converge to the
space average, at a rate controlled by that decay* — **explicitly conditional; mixing is never
proved here or anywhere in the corpus.**

The antecedent is deliberately **quantitative correlation decay** (`HasCorrelationDecay`), an
explicit bound `|⟨(f∘Φ^s)(f∘Φ^t)⟩ − ⟨f⟩²| ≤ ε (dist s t)`, rather than abstract mixing. That
choice is the difference between a feasible brick and a blocked one:

* Mathlib has **no mixing definition** and **no pointwise Birkhoff theorem** (the standing row in
  `MATHLIB-GAPS.md`), so routing through abstract ergodic theory stops immediately.
* Mathlib *does* have the **von Neumann mean ergodic theorem**
  (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`) — the arc plan's wall note
  claiming otherwise was stale and is corrected at source. But it is not what E4 needs: it gives
  **no rate**, and its limit is the orthogonal projection onto the invariant subspace, which
  equals the space average only under an *ergodicity* hypothesis. Correlation decay delivers both
  the rate and the identification of the limit, and needs no upstream ergodic theorem at all.

From the quantitative antecedent the Cesàro estimate is elementary: expand the square of the
Birkhoff average, and the double sum is controlled by counting how often each distance occurs.

## What is proved

* `sum_sum_nat_dist_le` — the counting bound: a nonnegative weight depending only on `Nat.dist`
  is counted at most twice per value across a `T × T` block;
* `HasCorrelationDecay` — the antecedent, and `HasCorrelationDecay.nonneg`;
* ★ `integral_birkhoffAverage_sub_sq_le` — the sharp `L²` estimate, in double-sum form;
* ★★ `integral_birkhoffAverage_sub_sq_le_cesaro` — the usable form,
  `E[(A_T f − ⟨f⟩)²] ≤ (2/T) Σ_{u<T} ε u`;
* ★★ `tendsto_integral_birkhoffAverage_sub_sq` — if `ε` is summable then the time averages
  converge to the space average **in `L²`**, which is E4's consequent;
* `integral_iterate_of_measurePreserving` and `HasCorrelationDecay.of_measurePreserving` — the
  bridge supplying both hypotheses from a measure-preserving map plus a **one-lag** bound.

## ⚠️ Honest scope

* **Mixing is not proved, and no dynamics is exhibited.** Everything is conditional on
  `HasCorrelationDecay`, which is a hypothesis about a particular `Φ`, `f` and `ε`. Whether any
  Σ-flow satisfies it is the separate question E5 asks; a non-vacuity witness is required before
  any of this may be described as equilibration of anything in particular.
* **Discrete time.** `Φ^[t]` iterates a single map. A continuous one-parameter flow enters by
  sampling at a fixed timestep; the continuous-time statement is not proved.
* The mean-stationarity hypothesis `hmean` is stated *directly* (`⟨f∘Φ^t⟩ = ⟨f⟩`) rather than
  derived from `MeasurePreserving`, so that the analytic core has no dynamics in it at all.
  `HasCorrelationDecay.of_measurePreserving` is the bridge for the measure-preserving case.
* Convergence is proved in **`L²`**. On a probability space that implies convergence in measure by
  Chebyshev, but **the in-measure form is not stated here** — no theorem below mentions
  `μ {x | δ ≤ |A_T f x − ⟨f⟩|}`. Almost-everywhere convergence is a different matter: it is what
  pointwise Birkhoff would buy and is *not* available.
* The observable must be **bounded** (`hfb`), which is what keeps every integrability side
  condition trivial. Unbounded `L²` observables would need a genuine `L²` argument.

Reference: `specs/equilibration-arc-plan.md` (E4); `MATHLIB-GAPS.md` (the Birkhoff row);
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-! ### The pair-distance counting bound -/

/-- **Each distance is counted at most twice per row.** For a nonnegative weight `ε` depending
only on `Nat.dist`, the total over a `T × T` block is at most `2T Σ_{u<T} ε u`.

This is the whole combinatorial content of the Cesàro estimate below: within a row `s`, the map
`t ↦ Nat.dist s t` is injective on each side of the diagonal separately (not globally — the
truncated subtraction `t - s` collapses the whole left half to `0`), so the row splits into two
injective pieces, each of which reindexes into `range T`. -/
lemma sum_sum_nat_dist_le {ε : ℕ → ℝ} (hε : ∀ u, 0 ≤ ε u) (T : ℕ) :
    ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T, ε (Nat.dist s t)
      ≤ 2 * T * ∑ u ∈ Finset.range T, ε u := by
  classical
  have key : ∀ (A : Finset ℕ) (g : ℕ → ℕ), Set.InjOn g A → (∀ a ∈ A, g a < T) →
      ∑ a ∈ A, ε (g a) ≤ ∑ u ∈ Finset.range T, ε u := by
    intro A g hinj hlt
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hε i)
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (hlt a ha)
  have hrow : ∀ s ∈ Finset.range T,
      ∑ t ∈ Finset.range T, ε (Nat.dist s t) ≤ 2 * ∑ u ∈ Finset.range T, ε u := by
    intro s hs
    have hsT : s < T := Finset.mem_range.mp hs
    have hleft : ∑ t ∈ (Finset.range T).filter (fun t => t ≤ s), ε (Nat.dist s t)
        ≤ ∑ u ∈ Finset.range T, ε u := by
      rw [Finset.sum_congr rfl (fun t ht => by
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp ht).2])]
      refine key _ (fun t => s - t) (fun a ha b hb hab => ?_) (fun a _ => ?_)
      · have ha' : a ≤ s := (Finset.mem_filter.mp ha).2
        have hb' : b ≤ s := (Finset.mem_filter.mp hb).2
        simp only at hab
        omega
      · omega
    have hright : ∑ t ∈ (Finset.range T).filter (fun t => ¬ t ≤ s), ε (Nat.dist s t)
        ≤ ∑ u ∈ Finset.range T, ε u := by
      rw [Finset.sum_congr rfl (fun t ht => by
        rw [Nat.dist_eq_sub_of_le (le_of_not_ge (Finset.mem_filter.mp ht).2)])]
      refine key _ (fun t => t - s) (fun a ha b hb hab => ?_) (fun a ha => ?_)
      · have ha' : ¬ a ≤ s := (Finset.mem_filter.mp ha).2
        have hb' : ¬ b ≤ s := (Finset.mem_filter.mp hb).2
        simp only at hab
        omega
      · have : a < T := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        omega
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t => t ≤ s)
      (fun t => ε (Nat.dist s t))]
    linarith
  calc ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T, ε (Nat.dist s t)
      ≤ ∑ _s ∈ Finset.range T, (2 * ∑ u ∈ Finset.range T, ε u) := Finset.sum_le_sum hrow
    _ = 2 * T * ∑ u ∈ Finset.range T, ε u := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ### The antecedent -/

variable {X : Type*} [MeasurableSpace X]

/-- **Quantitative correlation decay** — E4's antecedent, and the only hypothesis about the
dynamics anywhere in this file. The pair correlation of `f` along the iterates of `Φ` sits within
`ε (Nat.dist s t)` of the product of means.

Stated as an explicit bound rather than as abstract mixing, deliberately: see the module header.
Any prose derived from the theorems below must carry this hypothesis with it — nothing here says
that any particular dynamics satisfies it. -/
def HasCorrelationDecay (μ : Measure X) (Φ : X → X) (f : X → ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ s t : ℕ, |(∫ x, f (Φ^[s] x) * f (Φ^[t] x) ∂μ) - (∫ y, f y ∂μ) ^ 2| ≤ ε (Nat.dist s t)

/-- A decay envelope is automatically nonnegative — it dominates an absolute value. -/
lemma HasCorrelationDecay.nonneg {μ : Measure X} {Φ : X → X} {f : X → ℝ} {ε : ℕ → ℝ}
    (h : HasCorrelationDecay μ Φ f ε) (u : ℕ) : 0 ≤ ε u := by
  have hu := h 0 u
  rw [show Nat.dist 0 u = u by simp [Nat.dist]] at hu
  exact le_trans (abs_nonneg _) hu

/-! ### ★ The Cesàro estimate -/

/-- ★ **The sharp `L²` Cesàro estimate.** The mean square deviation of the Birkhoff average from
the space average is controlled by the correlation envelope over the `T × T` block of time pairs.

Note what is *not* assumed: no ergodicity, no mixing, no measure-preservation. The only inputs
are that `f` is bounded and measurable, that its mean is stationary (`hmean`), and the
quantitative decay. -/
theorem integral_birkhoffAverage_sub_sq_le {μ : Measure X} [IsProbabilityMeasure μ]
    {Φ : X → X} {f : X → ℝ} {ε : ℕ → ℝ} {C : ℝ}
    (hΦ : Measurable Φ) (hf : Measurable f) (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C)
    (hmean : ∀ t : ℕ, ∫ x, f (Φ^[t] x) ∂μ = ∫ y, f y ∂μ)
    (hdec : HasCorrelationDecay μ Φ f ε) {T : ℕ} (hT : 0 < T) :
    ∫ x, (birkhoffAverage ℝ Φ f T x - ∫ y, f y ∂μ) ^ 2 ∂μ
      ≤ ((T : ℝ) ^ 2)⁻¹ * ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T, ε (Nat.dist s t) := by
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  set m : ℝ := ∫ y, f y ∂μ with hm
  have hmi : ∀ t : ℕ, Measurable (fun x => f (Φ^[t] x)) := fun t => hf.comp (hΦ.iterate t)
  have hbi : ∀ (t : ℕ) (x : X), |f (Φ^[t] x)| ≤ C := fun t x => hfb _
  have hDnn : (0 : ℝ) ≤ C + |m| := add_nonneg hC (abs_nonneg m)
  have hbd : ∀ (t : ℕ) (x : X), |f (Φ^[t] x) - m| ≤ C + |m| := by
    intro t x
    have h1 := abs_le.mp (hbi t x)
    have h2 : -|m| ≤ m := neg_abs_le m
    have h3 : m ≤ |m| := le_abs_self m
    rw [abs_le]
    constructor <;> linarith
  have hint1 : ∀ t : ℕ, Integrable (fun x => f (Φ^[t] x)) μ := fun t =>
    Integrable.of_bound (hmi t).aestronglyMeasurable C
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hbi t x))
  have hint2 : ∀ s t : ℕ, Integrable (fun x => f (Φ^[s] x) * f (Φ^[t] x)) μ := fun s t =>
    Integrable.of_bound ((hmi s).mul (hmi t)).aestronglyMeasurable (C * C)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbi s x) (hbi t x) (abs_nonneg _) hC))
  have hintd : ∀ s t : ℕ, Integrable (fun x => (f (Φ^[s] x) - m) * (f (Φ^[t] x) - m)) μ :=
    fun s t => Integrable.of_bound
      (((hmi s).sub measurable_const).mul ((hmi t).sub measurable_const)).aestronglyMeasurable
      ((C + |m|) * (C + |m|))
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbd s x) (hbd t x) (abs_nonneg _) hDnn))
  have hexp : ∀ x, (birkhoffAverage ℝ Φ f T x - m) ^ 2
      = ((T : ℝ) ^ 2)⁻¹ * ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T,
          ((f (Φ^[s] x) - m) * (f (Φ^[t] x) - m)) := by
    intro x
    have hbs : birkhoffAverage ℝ Φ f T x = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (Φ^[t] x) := by
      rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
    have hsum : birkhoffAverage ℝ Φ f T x - m
        = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (Φ^[t] x) - m) := by
      rw [hbs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_sub]
      field_simp
    rw [hsum, mul_pow, inv_pow, pow_two (∑ t ∈ Finset.range T, (f (Φ^[t] x) - m)),
      Finset.sum_mul_sum]
  rw [integral_congr_ae (ae_of_all _ hexp), integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hintd s t))]
  refine Finset.sum_le_sum (fun s _ => ?_)
  rw [integral_finsetSum _ (fun t _ => hintd s t)]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hcov : ∫ x, (f (Φ^[s] x) - m) * (f (Φ^[t] x) - m) ∂μ
      = (∫ x, f (Φ^[s] x) * f (Φ^[t] x) ∂μ) - m ^ 2 := by
    have hpt : ∀ x, (f (Φ^[s] x) - m) * (f (Φ^[t] x) - m)
        = f (Φ^[s] x) * f (Φ^[t] x) - m * f (Φ^[s] x) - m * f (Φ^[t] x) + m ^ 2 :=
      fun x => by ring
    have i1 := hint2 s t
    have i2 : Integrable (fun x => m * f (Φ^[s] x)) μ := (hint1 s).const_mul m
    have i3 : Integrable (fun x => m * f (Φ^[t] x)) μ := (hint1 t).const_mul m
    -- state each combination with an explicit lambda: `Integrable.sub` otherwise produces the
    -- Pi-level `f - g`, which `integral_sub`/`integral_add` cannot match under `rw`.
    have j1 : Integrable (fun x => f (Φ^[s] x) * f (Φ^[t] x) - m * f (Φ^[s] x)) μ := i1.sub i2
    have j2 : Integrable
        (fun x => f (Φ^[s] x) * f (Φ^[t] x) - m * f (Φ^[s] x) - m * f (Φ^[t] x)) μ := j1.sub i3
    have hc : ∫ _x : X, m ^ 2 ∂μ = m ^ 2 := by simp
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_add j2 (integrable_const (m ^ 2)), hc, integral_sub j1 i3,
      integral_sub i1 i2, integral_const_mul, integral_const_mul, hmean s, hmean t]
    ring
  rw [hcov]
  exact le_of_abs_le (hdec s t)

/-- ★★ **The Cesàro estimate in usable form**: the mean square deviation of the time average
from the space average is at most `(2/T) Σ_{u<T} ε u`.

The factor two is the counting bound `sum_sum_nat_dist_le`: across the `T × T` block of time
pairs each distance occurs at most twice per row. -/
theorem integral_birkhoffAverage_sub_sq_le_cesaro {μ : Measure X} [IsProbabilityMeasure μ]
    {Φ : X → X} {f : X → ℝ} {ε : ℕ → ℝ} {C : ℝ}
    (hΦ : Measurable Φ) (hf : Measurable f) (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C)
    (hmean : ∀ t : ℕ, ∫ x, f (Φ^[t] x) ∂μ = ∫ y, f y ∂μ)
    (hdec : HasCorrelationDecay μ Φ f ε) {T : ℕ} (hT : 0 < T) :
    ∫ x, (birkhoffAverage ℝ Φ f T x - ∫ y, f y ∂μ) ^ 2 ∂μ
      ≤ 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  refine (integral_birkhoffAverage_sub_sq_le hΦ hf hC hfb hmean hdec hT).trans ?_
  calc ((T : ℝ) ^ 2)⁻¹ * ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T, ε (Nat.dist s t)
      ≤ ((T : ℝ) ^ 2)⁻¹ * (2 * T * ∑ u ∈ Finset.range T, ε u) :=
        mul_le_mul_of_nonneg_left (sum_sum_nat_dist_le hdec.nonneg T) (by positivity)
    _ = 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u := by
        field_simp

/-- ★★ **E4's consequent.** If the correlation envelope is summable, the time averages converge
to the space average in `L²`.

This is equilibration *conditional on decay* — the hypothesis `hdec` is doing all the work and
must travel with any statement derived from this theorem. Nothing here exhibits a dynamics with
decaying correlations. -/
theorem tendsto_integral_birkhoffAverage_sub_sq {μ : Measure X} [IsProbabilityMeasure μ]
    {Φ : X → X} {f : X → ℝ} {ε : ℕ → ℝ} {C : ℝ}
    (hΦ : Measurable Φ) (hf : Measurable f) (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C)
    (hmean : ∀ t : ℕ, ∫ x, f (Φ^[t] x) ∂μ = ∫ y, f y ∂μ)
    (hdec : HasCorrelationDecay μ Φ f ε) (hsum : Summable ε) :
    Filter.Tendsto
      (fun T : ℕ => ∫ x, (birkhoffAverage ℝ Φ f T x - ∫ y, f y ∂μ) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  have hnn : ∀ T : ℕ, 0 ≤ ∫ x, (birkhoffAverage ℝ Φ f T x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
    fun _ => integral_nonneg (fun _ => sq_nonneg _)
  have hg : Filter.Tendsto (fun T : ℕ => 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℕ => 2 * (T : ℝ)⁻¹) Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
    have h2 : Filter.Tendsto (fun T : ℕ => ∑ u ∈ Finset.range T, ε u) Filter.atTop
        (nhds (∑' u, ε u)) := hsum.hasSum.tendsto_sum_nat
    simpa using h1.mul h2
  refine squeeze_zero' (Filter.Eventually.of_forall hnn) ?_ hg
  filter_upwards [Filter.eventually_gt_atTop 0] with T hT
  exact integral_birkhoffAverage_sub_sq_le_cesaro hΦ hf hC hfb hmean hdec hT

/-! ### ★ The antecedent has teeth: periodic dynamics cannot satisfy it -/

/-- ★ **A periodic map forces zero variance.** If `Φ^[k] = id` for some `k ≥ 1`, then the only
observables with summably-decaying correlations are the ones with `⟨f²⟩ = ⟨f⟩²`, i.e. the a.e.
constant ones.

The proof is one line of dynamics and one of analysis: `Φ^[k*m] = id` for every `m`, so the
correlation at lag `k*m` is *exactly* `⟨f²⟩`; a summable envelope tends to zero along that
subsequence, and a constant bounded by a null sequence is zero.

This is the sharpness statement for `HasCorrelationDecay` — it rules out the cheap witnesses.
Every measure-preserving map of a finite or countable probability space is periodic on its
support, so **no such space carries a non-trivial witness**: a genuine one needs a non-atomic
space, which is why `CorrelationDecayWitness` builds on the circle. -/
theorem HasCorrelationDecay.integral_mul_self_eq_of_periodic {μ : Measure X}
    {Φ : X → X} {f : X → ℝ} {ε : ℕ → ℝ} {k : ℕ} (hk : 0 < k) (hper : Φ^[k] = id)
    (hdec : HasCorrelationDecay μ Φ f ε) (hsum : Summable ε) :
    ∫ x, f x * f x ∂μ = (∫ y, f y ∂μ) ^ 2 := by
  have hiter : ∀ m : ℕ, Φ^[k * m] = id := by
    intro m
    rw [Function.iterate_mul, hper, Function.iterate_id]
  have hbound : ∀ m : ℕ,
      |(∫ x, f x * f x ∂μ) - (∫ y, f y ∂μ) ^ 2| ≤ ε (k * m) := by
    intro m
    have h := hdec 0 (k * m)
    rw [show Nat.dist 0 (k * m) = k * m by simp [Nat.dist], hiter m] at h
    simpa using h
  have hzero : Filter.Tendsto (fun m : ℕ => ε (k * m)) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero.comp
      (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => le_trans hn
        (Nat.le_mul_of_pos_left n hk)⟩))
  have := ge_of_tendsto' hzero hbound
  have habs : |(∫ x, f x * f x ∂μ) - (∫ y, f y ∂μ) ^ 2| = 0 :=
    le_antisymm this (abs_nonneg _)
  linarith [sub_eq_zero.mp (abs_eq_zero.mp habs)]

/-! ### The measure-preserving bridge

The analytic core above deliberately takes `hmean` and the two-index decay as bare hypotheses, so
that it contains no dynamics at all. These two lemmas supply both from the natural inputs: a
measure-preserving map and a **one-lag** decay bound, which is what a physical estimate actually
provides. -/

/-- Precomposing with a measure-preserving self-map does not change an integral. -/
lemma integral_comp_of_measurePreserving {μ : Measure X} {Ψ : X → X}
    (hΨ : MeasurePreserving Ψ μ μ) {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ x, f (Ψ x) ∂μ = ∫ y, f y ∂μ := by
  have hmap : Measure.map Ψ μ = μ := hΨ.map_eq
  calc ∫ x, f (Ψ x) ∂μ = ∫ y, f y ∂(Measure.map Ψ μ) :=
        (integral_map hΨ.measurable.aemeasurable (by rw [hmap]; exact hf)).symm
    _ = ∫ y, f y ∂μ := by rw [hmap]

/-- Along a measure-preserving map, the mean of an observable is stationary — this is `hmean`. -/
lemma integral_iterate_of_measurePreserving {μ : Measure X} {Φ : X → X}
    (hΦ : MeasurePreserving Φ μ μ) {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (t : ℕ) :
    ∫ x, f (Φ^[t] x) ∂μ = ∫ y, f y ∂μ :=
  integral_comp_of_measurePreserving (hΦ.iterate t) hf

/-- **An odd symmetry kills an integral.** If some measure-preserving involution-like translation
negates the integrand, the integral vanishes — the sign-flip argument of `Q24`, in the form the
circle witness uses. -/
lemma integral_eq_zero_of_measurePreserving_neg {μ : Measure X} {Ψ : X → X}
    (hΨ : MeasurePreserving Ψ μ μ) {g : X → ℝ} (hg : Integrable g μ)
    (hflip : ∀ x, g (Ψ x) = - g x) : ∫ x, g x ∂μ = 0 := by
  have h := integral_comp_of_measurePreserving hΨ hg.aestronglyMeasurable
  rw [integral_congr_ae (ae_of_all _ hflip), integral_neg] at h
  linarith

/-- **From a one-lag bound to the two-index antecedent.** For a measure-preserving map the pair
correlation depends only on the lag, so a decay estimate at each lag `u` — the form a physical
argument produces — gives `HasCorrelationDecay`. -/
lemma HasCorrelationDecay.of_measurePreserving {μ : Measure X} {Φ : X → X} {f : X → ℝ}
    {ε : ℕ → ℝ} (hΦ : MeasurePreserving Φ μ μ) (hf : Measurable f)
    (hlag : ∀ u : ℕ, |(∫ x, f x * f (Φ^[u] x) ∂μ) - (∫ y, f y ∂μ) ^ 2| ≤ ε u) :
    HasCorrelationDecay μ Φ f ε := by
  have hpair : ∀ s t : ℕ, s ≤ t →
      ∫ x, f (Φ^[s] x) * f (Φ^[t] x) ∂μ = ∫ x, f x * f (Φ^[t - s] x) ∂μ := by
    intro s t hst
    have hcomp : ∀ x, f (Φ^[s] x) * f (Φ^[t] x)
        = (fun y => f y * f (Φ^[t - s] y)) (Φ^[s] x) := by
      intro x
      have hit : Φ^[t] x = Φ^[t - s] (Φ^[s] x) := by
        rw [← Function.iterate_add_apply Φ (t - s) s x]
        congr 1
        omega
      rw [hit]
    rw [integral_congr_ae (ae_of_all _ hcomp)]
    exact integral_iterate_of_measurePreserving hΦ
      (hf.mul (hf.comp (hΦ.measurable.iterate (t - s)))).aestronglyMeasurable s
  intro s t
  rcases le_total s t with h | h
  · rw [hpair s t h, Nat.dist_eq_sub_of_le h]
    exact hlag _
  · rw [integral_congr_ae (ae_of_all _ (fun x => mul_comm (f (Φ^[s] x)) (f (Φ^[t] x)))),
      hpair t s h, Nat.dist_eq_sub_of_le_right h]
    exact hlag _

end MeasureTheory
