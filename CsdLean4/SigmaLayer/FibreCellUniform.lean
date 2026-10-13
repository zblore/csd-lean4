/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreHorizonDivergence
public import CsdLean4.RecordLayer.CircleFibre

/-!
# The Haar cell law of the fibre grid is uniform

**Category:** 7-SigmaLayer.
BACKLOG #144, out of #130.

[`FibreCoarseArrow.lean`](FibreCoarseArrow.lean) cuts the `T²` fibre into `(m+1)²` cells of equal
width, [`FibreFiniteHorizon.lean`](FibreFiniteHorizon.lean) measures a cell's time-averaged
occupation against its Haar weight, and [`FibreHorizonDivergence.lean`](FibreHorizonDivergence.lean)
compares the occupation law with the **uniform** cell law. All three *say* the weights are equal,
because the construction makes them so, and none of them **proved** it. This file does.

* ★★★ `volume_circCell_preimage` — one circle cell has Haar measure `1/(m+1)`;
* ★★★ `volume_torusCell_preimage` — one fibre cell has `1/(m+1)²`, by the product measure;
* ★★★ `coarseLaw_fibreCell_apply` — so the Haar cell law of `Σ` gives every cell `1/(m+1)²`, and
  ★★ `coarseLaw_fibreCell_toReal` is the real-valued form the rate arguments consume.

## How it goes, and why it is one argument rather than three

`circCell m x` is `min m ⌊(m+1)·circRep x⌋₊`, and `circRep` carries Haar measure on `AddCircle 1` to
Lebesgue measure on `(0, 1]`, so a cell's weight is the Lebesgue measure of
`{t ∈ (0, 1] | min m ⌊(m+1)t⌋₊ = k}`. The obvious plan is three cases — `k = 0` loses its left
endpoint to `(0, 1]`, `0 < k < m` is a clean half-open interval, and `k = m` absorbs `t = 1` through
the `min` clamp — and each case is a different interval, which is what made this look like `M` of
endpoint bookkeeping.

It is one case instead. The set is **sandwiched** between `Ioo (k/(m+1)) ((k+1)/(m+1))` and the
corresponding `Icc`, uniformly in `k`, and those two have the same Lebesgue measure, so
`measure_mono` in both directions pins the cell without ever naming which interval it is. The
endpoints never have to be decided, only bounded. `cellSet_inter_subset_Icc` still splits on
`k < m` against `k = m`, because the clamp genuinely behaves differently there, but each half is
three lines and the `k = 0` case has vanished entirely.

The general machinery this needs is ★★ `RecordLayer.volume_rep_preimage` — the `rep`-preimage of
**any** measurable set weighs what the set weighs inside one turn — extracted here from the `Ioc`
form that already existed, because a floor cell is half-open the other way round and the `Ioc` form
cannot see it.

## Honest scope

⚠️ **This is the Haar cell law, not the occupation law.** It says the *reference* measure spreads
evenly over the cells. It says nothing about where a trajectory spends its time, which is #118's
question and still carries #118(i)'s unproved decorrelation hypothesis.

⚠️ **It unblocks a rate, and the rate is still time-averaged.** With this, #130's divergence bound
and #118(ii)'s `L²` bound are about the same reference and can be combined; the result is still a
statement about time averages over `[0, T)`, not about the law at step `n`, so `R-019` is no closer
than #118 left it.

⚠️ **The grid only.** `circCell` is the equal-width grid of `FibreCoarseArrow.lean`. Nothing here is
stated for the Born cells of `RecordLayer/CircleFibre.lean`, whose widths are the Born weights and
are deliberately *not* equal.

References: [`FibreCoarseArrow.lean`](FibreCoarseArrow.lean) (`circRep`, `circIdx`, `circCell`,
`torusCell`, `fibreCell`), [`CircleFibre.lean`](../RecordLayer/CircleFibre.lean)
(`rep`, `volume_rep_preimage`), [`FibreHorizonDivergence.lean`](FibreHorizonDivergence.lean) (#130),
[`FibreFiniteHorizon.lean`](FibreFiniteHorizon.lean) (#118(ii));
`specs/BACKLOG.md` #144, #130, #118; `specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set InformationTheory

open scoped ENNReal

namespace CSD.SigmaLayer

open LF4

/-! ### The representatives of one cell, as a set of reals -/

/-- The representatives that land in cell `k`: the grid condition, read on `ℝ`. -/
def cellSet (m k : ℕ) : Set ℝ := {t : ℝ | min m ⌊((m : ℝ) + 1) * t⌋₊ = k}

theorem measurableSet_cellSet (m k : ℕ) : MeasurableSet (cellSet m k) := by
  have h : Measurable fun t : ℝ => min m ⌊((m : ℝ) + 1) * t⌋₊ :=
    (Measurable.of_discrete (f := fun j : ℕ => min m j)).comp
      ((Nat.measurable_floor : Measurable (Nat.floor : ℝ → ℕ)).comp
        (measurable_const.mul measurable_id))
  exact h (measurableSet_singleton k)

/-- `circRep` is `RecordLayer.rep`: the two files took the measurable equivalence and the plain
one, and the measurable one's `toEquiv` is the plain one. -/
theorem circRep_eq_rep : circRep = RecordLayer.rep := rfl

/-- A cell of the circle is the `rep`-preimage of its grid condition. -/
theorem circCell_preimage (m : ℕ) (k : Fin (m + 1)) :
    circCell m ⁻¹' {k} = RecordLayer.rep ⁻¹' cellSet m (k : ℕ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, cellSet, Set.mem_ofPred_eq,
    circCell, circIdx, ← circRep_eq_rep]
  exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩

/-! ### The sandwich -/

/-- The open interval of width `1/(m+1)` sits inside the cell. -/
theorem Ioo_subset_cellSet_inter (m : ℕ) (k : Fin (m + 1)) :
    Ioo ((k : ℕ) / ((m : ℝ) + 1)) (((k : ℕ) + 1) / ((m : ℝ) + 1))
      ⊆ cellSet m (k : ℕ) ∩ Ioc (0 : ℝ) 1 := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hkm : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    have : ((k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
    linarith
  intro t ht
  obtain ⟨hlo, hhi⟩ := ht
  have hklt : ((k : ℕ) : ℝ) < ((m : ℝ) + 1) * t := by
    rw [div_lt_iff₀ hM] at hlo
    linarith [hlo]
  have hhit : ((m : ℝ) + 1) * t < ((k : ℕ) : ℝ) + 1 := by
    rw [lt_div_iff₀ hM] at hhi
    linarith [hhi]
  have ht0 : 0 < t := by
    by_contra h
    have : ((m : ℝ) + 1) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le (not_lt.mp h)
    have hneg : ((k : ℕ) : ℝ) < 0 := lt_of_lt_of_le hklt this
    exact absurd hneg (not_lt.mpr (by positivity))
  have ht1 : t ≤ 1 := by
    nlinarith [hhit, hkm]
  refine ⟨?_, ht0, ht1⟩
  have hfloor : ⌊((m : ℝ) + 1) * t⌋₊ = (k : ℕ) := by
    rw [Nat.floor_eq_iff (by positivity)]
    exact ⟨hklt.le, by exact_mod_cast hhit⟩
  show min m ⌊((m : ℝ) + 1) * t⌋₊ = (k : ℕ)
  rw [hfloor]
  exact min_eq_right (Nat.lt_succ_iff.mp k.isLt)

/-- And the cell sits inside the closed interval of the same width. This is the half where the
`min` clamp matters: at `k = m` the cell absorbs everything above `m/(m+1)`, which is still inside
the closed interval because the representatives stop at `1`. -/
theorem cellSet_inter_subset_Icc (m : ℕ) (k : Fin (m + 1)) :
    cellSet m (k : ℕ) ∩ Ioc (0 : ℝ) 1
      ⊆ Icc ((k : ℕ) / ((m : ℝ) + 1)) (((k : ℕ) + 1) / ((m : ℝ) + 1)) := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  intro t ht
  obtain ⟨hcell, ht0, ht1⟩ := ht
  have hmin : min m ⌊((m : ℝ) + 1) * t⌋₊ = (k : ℕ) := hcell
  have hnn : (0 : ℝ) ≤ ((m : ℝ) + 1) * t := by positivity
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hk | hk
  · -- `k < m`, so the clamp is inactive and the floor is exactly `k`
    have hfloor : ⌊((m : ℝ) + 1) * t⌋₊ = (k : ℕ) := by
      rcases Nat.le_total ⌊((m : ℝ) + 1) * t⌋₊ m with h | h
      · rwa [min_eq_right h] at hmin
      · rw [min_eq_left h] at hmin
        omega
    rw [Nat.floor_eq_iff hnn] at hfloor
    exact ⟨by rw [div_le_iff₀ hM]; linarith [hfloor.1],
      by rw [le_div_iff₀ hM]; linarith [hfloor.2]⟩
  · -- `k = m`: the cell is everything from `m/(m+1)` up, and `t ≤ 1 = (m+1)/(m+1)`
    have hkR : ((k : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hk
    have hge : (m : ℕ) ≤ ⌊((m : ℝ) + 1) * t⌋₊ := by
      rcases Nat.le_total ⌊((m : ℝ) + 1) * t⌋₊ m with h | h
      · rw [min_eq_right h] at hmin
        omega
      · exact h
    have hmt : (m : ℝ) ≤ ((m : ℝ) + 1) * t := by
      have h := (Nat.le_floor_iff hnn).mp hge
      exact_mod_cast h
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hM, hkR]
      nlinarith [hmt]
    · rw [le_div_iff₀ hM, hkR]
      nlinarith [ht1]

/-! ### The weights -/

/-- ★★★ **A circle cell has Haar measure `1/(m+1)`.** Pinned by `measure_mono` between the open
and closed intervals of that width, so no endpoint has to be decided. -/
theorem volume_circCell_preimage (m : ℕ) (k : Fin (m + 1)) :
    (volume : Measure (AddCircle (1 : ℝ))) (circCell m ⁻¹' {k})
      = ENNReal.ofReal (((m : ℝ) + 1)⁻¹) := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hw : ((((k : ℕ) : ℝ) + 1) / ((m : ℝ) + 1)) - (((k : ℕ) : ℝ) / ((m : ℝ) + 1))
      = ((m : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  rw [circCell_preimage, RecordLayer.volume_rep_preimage (measurableSet_cellSet m (k : ℕ))]
  have hlo := measure_mono (μ := (volume : Measure ℝ))
    (Ioo_subset_cellSet_inter m k)
  have hhi := measure_mono (μ := (volume : Measure ℝ))
    (cellSet_inter_subset_Icc m k)
  rw [Real.volume_Ioo, hw] at hlo
  rw [Real.volume_Icc, hw] at hhi
  exact le_antisymm hhi hlo

/-- ★★★ **A fibre cell has Haar measure `1/(m+1)²`**: the fibre is a product of two circles and so
is its grid. -/
theorem volume_torusCell_preimage (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    (volume : Measure KTorus) (torusCell m ⁻¹' {c})
      = ENNReal.ofReal ((((m : ℝ) + 1) ^ 2)⁻¹) := by
  have hprod : torusCell m ⁻¹' {c}
      = (circCell m ⁻¹' {c.1}) ×ˢ (circCell m ⁻¹' {c.2}) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, torusCell, Prod.ext_iff]
  rw [hprod, Measure.volume_eq_prod, Measure.prod_prod, volume_circCell_preimage,
    volume_circCell_preimage, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← inv_pow, pow_two]

/-- ★★★ **The Haar cell law of `Σ` is uniform**: every one of the `(m+1)²` cells carries
`1/(m+1)²`. This is the statement #130's bound and #118(ii)'s both assumed. -/
theorem coarseLaw_fibreCell_apply {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) :
    coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}
      = ENNReal.ofReal ((((m : ℝ) + 1) ^ 2)⁻¹) := by
  have hpre : fibreCell (N := N) m ⁻¹' {c} = (univ : Set (CPN N)) ×ˢ (torusCell m ⁻¹' {c}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ, true_and,
      fibreCell]
  rw [coarseLaw_apply _ (measurable_fibreCell m) (measurableSet_singleton c), hpre, kMuL,
    Measure.prod_prod, measure_univ, one_mul, volume_torusCell_preimage]

/-- ★★ **The real-valued form**, which is what the rate arguments consume. -/
theorem coarseLaw_fibreCell_toReal {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) :
    (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal
      = (((m : ℝ) + 1) ^ 2)⁻¹ := by
  rw [coarseLaw_fibreCell_apply, ENNReal.toReal_ofReal (by positivity)]


/-! ### The rate `R-019`'s second clause asks for

With the reference identified, #130's pointwise divergence bound and #118(ii)'s `L²` bound are
about the same quantity and compose. The two ingredients the composition needs beyond them are the
measurability and boundedness of a cell's time-averaged occupation, which is what makes the
integrand integrable. -/

/-- A cell's time-averaged occupation is measurable in the base point. -/
theorem measurable_birkhoffAverage_fibreCellInd {N : ℕ} (m T : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) :
    Measurable fun p : LF4.KSigma N =>
      birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  exact Measurable.const_mul
    (Finset.measurable_sum _ fun u _ =>
      (measurable_fibreCellInd m c).comp (measurable_fibreStroke.iterate u)) _

/-- And it lies in `[0, 1]`, being an average of indicators. -/
theorem birkhoffAverage_fibreCellInd_mem_Icc {N : ℕ} (m T : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) (p : LF4.KSigma N) :
    birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p ∈ Icc (0 : ℝ) 1 := by
  have hterm : ∀ u : ℕ, fibreCellInd (N := N) m c (fibreStroke^[u] p) ∈ Icc (0 : ℝ) 1 := by
    intro u
    rw [fibreCellInd_eq_ite]
    split <;> norm_num
  have hlo : (0 : ℝ) ≤ ∑ u ∈ Finset.range T, fibreCellInd (N := N) m c (fibreStroke^[u] p) :=
    Finset.sum_nonneg fun u _ => (hterm u).1
  have hhi : (∑ u ∈ Finset.range T, fibreCellInd (N := N) m c (fibreStroke^[u] p)) ≤ (T : ℝ) := by
    calc (∑ u ∈ Finset.range T, fibreCellInd (N := N) m c (fibreStroke^[u] p))
        ≤ ∑ _u ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun u _ => (hterm u).2
      _ = (T : ℝ) := by simp
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp [birkhoffAverage, birkhoffSum]
  · have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
    refine ⟨by positivity, ?_⟩
    rw [inv_mul_le_one₀ hTR]
    exact hhi

/-- The squared deviation of an occupation from a weight in `[0, 1]` is integrable: it is
measurable and bounded by `1`. -/
theorem integrable_birkhoffAverage_sub_sq {N : ℕ} (p₀ : LF4.CPN N) (m T : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => (birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p - q) ^ 2)
      (kMuL p₀) := by
  refine Integrable.of_bound
    (((measurable_birkhoffAverage_fibreCellInd m T c).sub measurable_const).pow_const 2
      |>.aestronglyMeasurable) 1 (ae_of_all _ fun p => ?_)
  obtain ⟨h0, h1⟩ := birkhoffAverage_fibreCellInd_mem_Icc (N := N) m T c p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [hq.1, hq.2]

/-- ★★★ **`R-019`'s second clause at a finite horizon, with its rate.**

The divergence of the time-averaged occupation law from the cell law is, in expectation over the
epistemic measure, at most `(m+1)⁴·(2/T)·∑_{u<T} ε u`. One factor `(m+1)²` is #118(ii)'s cell count
and the other is the chi-squared conversion of #130, and the reference is the same on both sides
because of `coarseLaw_fibreCell_apply` above — which is the whole reason this row existed.

⚠️ Still **time-averaged**: what equilibrates is a cell's occupation over `[0, T)`, not the law
at step `n`. And `hdec` is #118(i), unproved. -/
theorem lintegral_klDiv_horizonLaw_le {N : ℕ} (p₀ : LF4.CPN N) (m : ℕ)
    {ε : ℕ → ℝ} {T : ℕ}
    (hdec : ∀ c : Fin (m + 1) × Fin (m + 1),
      HasCorrelationDecayUpTo (kMuL p₀) fibreStroke (fibreCellInd (N := N) m c) ε T)
    (hT : 0 < T) :
    ∫⁻ p, klDiv (horizonLaw (N := N) m T p)
        (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1)))) ∂(kMuL p₀)
      ≤ ENNReal.ofReal (((m : ℝ) + 1) ^ 2 *
          (((m : ℝ) + 1) ^ 2 * (2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u))) := by
  classical
  set dev : (Fin (m + 1) × Fin (m + 1)) → LF4.KSigma N → ℝ := fun c p =>
    (birkhoffAverage ℝ fibreStroke (fibreCellInd (N := N) m c) T p
      - (((m : ℝ) + 1) ^ 2)⁻¹) ^ 2 with hdev
  have hq : (((m : ℝ) + 1) ^ 2)⁻¹ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [inv_le_one₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hint : ∀ c, Integrable (dev c) (kMuL p₀) := fun c =>
    integrable_birkhoffAverage_sub_sq p₀ m T c hq
  have hg_int : Integrable (fun p => ((m : ℝ) + 1) ^ 2 * ∑ c, dev c p) (kMuL p₀) :=
    ((integrable_finsetSum _ fun c _ => hint c).const_mul _)
  have hg_nn : ∀ p, 0 ≤ ((m : ℝ) + 1) ^ 2 * ∑ c, dev c p := by
    intro p
    have : (0 : ℝ) ≤ ∑ c, dev c p :=
      Finset.sum_nonneg fun c _ => by rw [hdev]; positivity
    positivity
  -- the deviation is measured from the Haar cell law, which is what #118(ii) bounds
  have hcentre : ∀ c : Fin (m + 1) × Fin (m + 1),
      (((m : ℝ) + 1) ^ 2)⁻¹
        = (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal := fun c =>
    (coarseLaw_fibreCell_toReal p₀ m c).symm
  have hsum : ∑ c, ∫ p, dev c p ∂(kMuL p₀)
      ≤ ((m : ℝ) + 1) ^ 2 * (2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u) := by
    have h := integral_sum_birkhoffAverage_fibreCellInd_sub_sq_le p₀ m hdec hT
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) h
    rw [hdev]
    simp only [hcentre c]
  calc ∫⁻ p, klDiv (horizonLaw (N := N) m T p)
          (uniformOn (univ : Set (Fin (m + 1) × Fin (m + 1)))) ∂(kMuL p₀)
      ≤ ∫⁻ p, ENNReal.ofReal (((m : ℝ) + 1) ^ 2 * ∑ c, dev c p) ∂(kMuL p₀) :=
        lintegral_mono fun p => klDiv_horizonLaw_le_chiSq m T p hT
    _ = ENNReal.ofReal (∫ p, ((m : ℝ) + 1) ^ 2 * ∑ c, dev c p ∂(kMuL p₀)) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nn)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_finsetSum _ fun c _ => hint c]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)

end CSD.SigmaLayer

end
