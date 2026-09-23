/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.AmplitudeAmplification
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# QSearch: amplitude amplification with unknown amplitude, the expected cost (BHMT Theorem 3)

**Category:** 1-Mathlib (CSD-free).

BHMT's `QSearch` runs amplitude amplification in stages `l = 0, 1, 2, …` with the guesses
`M_l = ⌈(6/5)^l⌉`: at each stage it measures a fresh copy of `ψ` directly, and failing that
draws a round count `j` uniformly below `M_l`, amplifies a fresh copy `j` rounds and measures.
Their Theorem 3: the expected number of applications of `A` and `A⁻¹` before a good element
is found is `O(1/√a)`, with `a = goodProb G ψ` the unknown success probability.

* **The stage law.** `stageProbAt G ψ j = a + (1 − a) · goodProb (Q^j ψ)` is the success
  probability of a stage at round count `j` (the direct measurement, then the amplified one on
  a fresh copy); `stageProb G ψ M` averages it over `j < M`. Once `M · sin 2θ ≥ 1` the average
  is at least `1/4` (`quarter_le_stageProb`, from the engine `qsearch_average`), and it is
  always at least `a` (`le_stageProb`).
* **The run as a random process** (`QSearchRun`): on a probability space, stage `l` draws its
  round count `J l` and records its success `W l`; the stages are independent (`iIndepFun`),
  `J l` is uniform below `M_l`, and given `J l = j` the stage succeeds with the Born
  probability `stageProbAt G ψ j`. The applications charged to a reached stage are
  `2 + 2 J l` — the direct run, the fresh preparation, and two per round — and `cost` sums
  them over the reached stages.
* **The bookkeeping.** Stage `l` is reached with probability `∏_{k<l} (1 − p_k)`
  (`meas_reach`, from independence), a reached stage costs `M_l + 1` in expectation
  (`lintegral_stageCost`, independence of the fresh draw from the past), so the expected cost
  is `∑_l (M_l + 1) ∏_{k<l} (1 − p_k)` (`lintegral_cost`). Past the critical stage every
  `p_k ≥ 1/4`, so the reach probabilities decay like `(3/4)^{l − l₀}` (`meas_reach_le`), and
  the series is bounded by the explicit geometric weights `qsearchWeight`
  (`qsearch_partial_sum_le`: `45 · (6/5)^{l₀}`).
* ★★ **BHMT Theorem 3** (`qsearch_expected_cost`): for `0 < a < 1`, the expected cost of a run
  is at most `54/√a`. Below `a ≤ 3/4` the critical stage is the first with
  `(6/5)^{l₀} > 1/sin 2θ`, so `(6/5)^{l₀} ≤ (6/5)/sin 2θ` and `sin 2θ ≥ √a`; above it every
  stage already succeeds with probability `≥ a > 3/4`.

## Honest scope

The theorem is the upper bound of BHMT's `Θ(1/√a)`; the matching lower bound is the optimality
of Grover search (Bennett–Bernstein–Brassard–Vazirani), not treated here. The cost charged to a
stage, `2 + 2j`, is an upper bound on the applications actually used when the direct
measurement already succeeds. The process model is an abstract probability space carrying the
stage variables with the stated laws — the standard reading of "independent stages with fresh
randomness"; its consistency is witnessed by `exists_qsearchRun` on the infinite product of
the stage laws. Query counting is by applications of the abstract step, as in
`AmplitudeAmplification.lean`; no gate decomposition is claimed. The constant `54` is not
optimised (BHMT's own accounting gives a smaller one).

## Source

Brassard, Høyer, Mosca, Tapp 2002, *Quantum amplitude amplification and estimation*, Contemp.
Math. **305**, Theorem 3 and the algorithm `QSearch` (§2, with `c = 6/5`), Lemma 2 (the engine,
`qsearch_average`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QuantumInfo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The schedule -/

/-- BHMT's growth constant, `c = 6/5`. -/
noncomputable def qsearchRatio : ℝ := 6 / 5

/-- The stage-`l` guess `M_l = ⌈(6/5)^l⌉`. -/
noncomputable def qsearchGuess (l : ℕ) : ℕ := ⌈qsearchRatio ^ l⌉₊

omit [Fintype ι] [DecidableEq ι] in
lemma one_lt_qsearchRatio : 1 < qsearchRatio := by norm_num [qsearchRatio]

omit [Fintype ι] [DecidableEq ι] in
lemma one_le_qsearchRatio_pow (l : ℕ) : 1 ≤ qsearchRatio ^ l :=
  one_le_pow₀ one_lt_qsearchRatio.le

omit [Fintype ι] [DecidableEq ι] in
lemma le_qsearchGuess (l : ℕ) : qsearchRatio ^ l ≤ qsearchGuess l := Nat.le_ceil _

omit [Fintype ι] [DecidableEq ι] in
lemma qsearchGuess_pos (l : ℕ) : 0 < qsearchGuess l :=
  Nat.cast_pos.mp (lt_of_lt_of_le one_pos ((one_le_qsearchRatio_pow l).trans (le_qsearchGuess l)))

omit [Fintype ι] [DecidableEq ι] in
lemma qsearchGuess_lt (l : ℕ) : (qsearchGuess l : ℝ) < qsearchRatio ^ l + 1 :=
  Nat.ceil_lt_add_one (by linarith [one_le_qsearchRatio_pow l])

/-! ## The stage success probability -/

variable (G : Finset ι) (ψ : EuclideanSpace ℂ ι)

/-- The success probability of one stage at round count `j`: the direct measurement of `ψ`
succeeds with probability `a = goodProb G ψ`; failing that, a fresh copy is amplified `j`
rounds and measured. -/
noncomputable def stageProbAt (j : ℕ) : ℝ :=
  goodProb G ψ + (1 - goodProb G ψ) * goodProb G ((ampStep ψ G)^[j] ψ)

/-- The success probability of a stage with guess `M`: the round count is uniform below `M`. -/
noncomputable def stageProb (M : ℕ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, stageProbAt G ψ j

variable {G ψ}

lemma goodProb_iterate_le_one (hψ : ‖ψ‖ = 1) (ha0 : 0 < goodProb G ψ)
    (ha1 : goodProb G ψ < 1) (j : ℕ) : goodProb G ((ampStep ψ G)^[j] ψ) ≤ 1 := by
  rw [amplitude_amplification G ψ hψ ha0 ha1 j]
  exact Real.sin_sq_le_one _

lemma stageProbAt_nonneg (ha1 : goodProb G ψ < 1) (j : ℕ) : 0 ≤ stageProbAt G ψ j := by
  unfold stageProbAt
  have := goodProb_nonneg G ψ
  have := goodProb_nonneg G ((ampStep ψ G)^[j] ψ)
  nlinarith

lemma stageProbAt_le_one (hψ : ‖ψ‖ = 1) (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1)
    (j : ℕ) : stageProbAt G ψ j ≤ 1 := by
  unfold stageProbAt
  have := goodProb_iterate_le_one hψ ha0 ha1 j
  nlinarith

/-- The direct measurement alone: a stage succeeds with probability at least `a`. -/
lemma le_stageProbAt (ha1 : goodProb G ψ < 1) (j : ℕ) : goodProb G ψ ≤ stageProbAt G ψ j := by
  unfold stageProbAt
  have := goodProb_nonneg G ((ampStep ψ G)^[j] ψ)
  nlinarith

/-- The amplified measurement alone: a stage succeeds at least as often as `Q^j ψ` does. -/
lemma goodProb_iterate_le_stageProbAt (hψ : ‖ψ‖ = 1) (ha0 : 0 < goodProb G ψ)
    (ha1 : goodProb G ψ < 1) (j : ℕ) :
    goodProb G ((ampStep ψ G)^[j] ψ) ≤ stageProbAt G ψ j := by
  unfold stageProbAt
  have := goodProb_iterate_le_one hψ ha0 ha1 j
  nlinarith

lemma stageProb_nonneg (ha1 : goodProb G ψ < 1) (M : ℕ) : 0 ≤ stageProb G ψ M :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun j _ => stageProbAt_nonneg ha1 j)

/-- A stage succeeds with probability at least `a`. -/
lemma le_stageProb (ha1 : goodProb G ψ < 1) {M : ℕ} (hM : 0 < M) :
    goodProb G ψ ≤ stageProb G ψ M := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  unfold stageProb
  rw [le_inv_mul_iff₀ hMpos]
  calc (M : ℝ) * goodProb G ψ = ∑ _j ∈ Finset.range M, goodProb G ψ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range M, stageProbAt G ψ j :=
        Finset.sum_le_sum fun j _ => le_stageProbAt ha1 j

/-- ★ **The engine, in stage form (BHMT Lemma 2):** once `M · sin 2θ ≥ 1`, a stage succeeds
with probability at least `1/4`. -/
lemma quarter_le_stageProb (hψ : ‖ψ‖ = 1) (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1)
    (M : ℕ) (hM : 1 ≤ M * (2 * Real.sqrt (goodProb G ψ * (1 - goodProb G ψ)))) :
    1 / 4 ≤ stageProb G ψ M := by
  have hMpos : (0 : ℝ) < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      norm_num at hM
    · exact Nat.cast_pos.mpr h
  have h1 := qsearch_average G ψ hψ ha0 ha1 M hM
  have h2 : ∑ j ∈ Finset.range M, goodProb G ((ampStep ψ G)^[j] ψ)
      ≤ ∑ j ∈ Finset.range M, stageProbAt G ψ j :=
    Finset.sum_le_sum fun j _ => goodProb_iterate_le_stageProbAt hψ ha0 ha1 j
  unfold stageProb
  rw [le_inv_mul_iff₀ hMpos]
  linarith

/-! ## The run as a random process -/

variable (G ψ) in
/-- **A run of QSearch as a random process.** On a probability space `(Ω, μ)`, stage `l` draws
its round count `J l` and records its success `W l`. The stages are independent, `J l` is
uniform below the guess `M l`, and given `J l = j` the stage succeeds with the Born probability
`stageProbAt G ψ j` (the direct measurement, then the amplified one on a fresh copy). -/
structure QSearchRun (M : ℕ → ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The round count drawn at stage `l`. -/
  J : ℕ → Ω → ℕ
  /-- Whether stage `l` found a good element. -/
  W : ℕ → Ω → Bool
  /-- The round counts are measurable. -/
  measurable_J : ∀ l, Measurable (J l)
  /-- The outcomes are measurable. -/
  measurable_W : ∀ l, Measurable (W l)
  /-- The stages use fresh randomness. -/
  indep : iIndepFun (fun l ω => (J l ω, W l ω)) μ
  /-- The round count is uniform below the guess. -/
  uniform : ∀ l j, μ (J l ⁻¹' {j}) = if j < M l then ((M l : ℝ≥0∞))⁻¹ else 0
  /-- Given the round count, the stage succeeds with the Born probability. -/
  law : ∀ l j, μ (J l ⁻¹' {j} ∩ W l ⁻¹' {true})
    = μ (J l ⁻¹' {j}) * ENNReal.ofReal (stageProbAt G ψ j)

namespace QSearchRun

variable {M : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (R : QSearchRun G ψ M μ)

/-- Stage `l` is reached: every earlier stage failed. -/
def reach (l : ℕ) : Set Ω := ⋂ k ∈ Finset.range l, R.W k ⁻¹' {false}

lemma measurableSet_W_false (l : ℕ) : MeasurableSet (R.W l ⁻¹' {false}) :=
  R.measurable_W l (measurableSet_singleton false)

lemma measurableSet_W_true (l : ℕ) : MeasurableSet (R.W l ⁻¹' {true}) :=
  R.measurable_W l (measurableSet_singleton true)

lemma measurableSet_J (l j : ℕ) : MeasurableSet (R.J l ⁻¹' {j}) :=
  R.measurable_J l (measurableSet_singleton j)

lemma measurableSet_reach (l : ℕ) : MeasurableSet (R.reach l) :=
  Finset.measurableSet_biInter _ fun k _ => R.measurableSet_W_false k

/-- The failure event of stage `k`, seen through stage `k`'s own variables. -/
lemma comap_W_false (k : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω => (R.J k ω, R.W k ω)) inferInstance]
      (R.W k ⁻¹' {false}) :=
  MeasurableSpace.measurableSet_comap.mpr
    ⟨Set.univ ×ˢ {false}, MeasurableSet.univ.prod (measurableSet_singleton false),
      by ext ω; simp⟩

/-- The round-count event of stage `k`, seen through stage `k`'s own variables. -/
lemma comap_J (k j : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω => (R.J k ω, R.W k ω)) inferInstance]
      (R.J k ⁻¹' {j}) :=
  MeasurableSpace.measurableSet_comap.mpr
    ⟨{j} ×ˢ Set.univ, (measurableSet_singleton j).prod MeasurableSet.univ, by ext ω; simp⟩

/-- **Reaching stage `l`:** every earlier stage fails, independently. -/
lemma meas_reach (l : ℕ) : μ (R.reach l) = ∏ k ∈ Finset.range l, μ (R.W k ⁻¹' {false}) := by
  unfold reach
  exact R.indep.meas_biInter fun k _ => R.comap_W_false k

/-- The round count of stage `l` is independent of reaching stage `l`. -/
lemma meas_J_inter_reach (l j : ℕ) :
    μ (R.J l ⁻¹' {j} ∩ R.reach l) = μ (R.J l ⁻¹' {j}) * μ (R.reach l) := by
  have h := R.indep.meas_biInter (S := Finset.range (l + 1))
    (s := fun k => if k < l then R.W k ⁻¹' {false} else R.J k ⁻¹' {j}) (fun k _ => by
      by_cases hk : k < l
      · rw [if_pos hk]; exact R.comap_W_false k
      · rw [if_neg hk]; exact R.comap_J k j)
  rw [Finset.range_add_one, Finset.set_biInter_insert,
    Finset.prod_insert Finset.notMem_range_self, if_neg (lt_irrefl l),
    Set.iInter₂_congr fun k (hk : k ∈ Finset.range l) => if_pos (Finset.mem_range.mp hk),
    Finset.prod_congr rfl fun k hk => congrArg μ (if_pos (Finset.mem_range.mp hk))] at h
  calc μ (R.J l ⁻¹' {j} ∩ R.reach l)
      = μ (R.J l ⁻¹' {j} ∩ ⋂ k ∈ Finset.range l, R.W k ⁻¹' {false}) := rfl
    _ = μ (R.J l ⁻¹' {j}) * ∏ k ∈ Finset.range l, μ (R.W k ⁻¹' {false}) := h
    _ = μ (R.J l ⁻¹' {j}) * μ (R.reach l) := by rw [R.meas_reach]

/-! ### The cost -/

/-- The applications of `A` and `A⁻¹` charged to stage `l` if it is reached: one for the direct
run, one for the fresh preparation and two per amplification round. -/
noncomputable def stageCost (l : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (R.reach l).indicator (fun ω => 2 + 2 * (R.J l ω : ℝ≥0∞)) ω

/-- The total cost of the run: the charges of every reached stage. -/
noncomputable def cost (ω : Ω) : ℝ≥0∞ := ∑' l, R.stageCost l ω

lemma measurable_stageCost (l : ℕ) : Measurable (R.stageCost l) :=
  (((measurable_from_nat.comp (R.measurable_J l)).const_mul 2).const_add 2).indicator
    (R.measurableSet_reach l)

/-- The expected cost is the sum of the expected stage costs. -/
lemma lintegral_cost : ∫⁻ ω, R.cost ω ∂μ = ∑' l, ∫⁻ ω, R.stageCost l ω ∂μ := by
  unfold cost
  exact lintegral_tsum fun l => (R.measurable_stageCost l).aemeasurable

/-- `∑_{j<M} (2 + 2j) = M (M + 1)`. -/
lemma sum_two_add_two_mul (M : ℕ) : ∑ j ∈ Finset.range M, (2 + 2 * j) = M * (M + 1) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  have := Finset.sum_range_id_mul_two M
  rcases M with _ | k
  · simp
  · rw [show (k + 1) * 2 + 2 * ∑ i ∈ Finset.range (k + 1), i
        = (k + 1) * 2 + (∑ i ∈ Finset.range (k + 1), i) * 2 by ring, this]
    simp only [Nat.add_sub_cancel]
    ring

/-- **A reached stage costs `M_l + 1` in expectation:** the fresh draw is independent of the
past, and a uniform round count below `M` has mean `(M − 1)/2`. -/
lemma lintegral_stageCost (l : ℕ) (hM : 0 < M l) :
    ∫⁻ ω, R.stageCost l ω ∂μ = ((M l : ℝ≥0∞) + 1) * μ (R.reach l) := by
  have hpt : ∀ ω, R.stageCost l ω = ∑' j,
      (R.J l ⁻¹' {j} ∩ R.reach l).indicator (fun _ => (2 + 2 * j : ℝ≥0∞)) ω := by
    intro ω
    have hz : ∀ j, j ≠ R.J l ω →
        (R.J l ⁻¹' {j} ∩ R.reach l).indicator (fun _ => (2 + 2 * j : ℝ≥0∞)) ω = 0 :=
      fun j hj => Set.indicator_of_notMem (fun h => hj (Set.mem_singleton_iff.mp h.1).symm) _
    rw [tsum_eq_single (R.J l ω) hz]
    unfold stageCost
    by_cases h : ω ∈ R.reach l
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem
        (show ω ∈ R.J l ⁻¹' {R.J l ω} ∩ R.reach l from ⟨rfl, h⟩)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
        (show ω ∉ R.J l ⁻¹' {R.J l ω} ∩ R.reach l from fun h' => h h'.2)]
  simp_rw [hpt]
  rw [lintegral_tsum fun j => (measurable_const.indicator
    ((R.measurableSet_J l j).inter (R.measurableSet_reach l))).aemeasurable]
  have hind : ∀ j : ℕ, ∫⁻ ω, (R.J l ⁻¹' {j} ∩ R.reach l).indicator
      (fun _ => (2 + 2 * j : ℝ≥0∞)) ω ∂μ = (2 + 2 * j) * μ (R.J l ⁻¹' {j} ∩ R.reach l) :=
    fun j => lintegral_indicator_const ((R.measurableSet_J l j).inter (R.measurableSet_reach l)) _
  simp_rw [hind, R.meas_J_inter_reach l, ← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [tsum_eq_sum (s := Finset.range (M l)) fun j hj => by
      rw [R.uniform, if_neg (by simpa using hj), mul_zero]]
  rw [Finset.sum_congr rfl fun j hj => by rw [R.uniform, if_pos (Finset.mem_range.mp hj)],
    ← Finset.sum_mul]
  have hsum : ∑ j ∈ Finset.range (M l), ((2 : ℝ≥0∞) + 2 * (j : ℝ≥0∞))
      = ((M l * (M l + 1) : ℕ) : ℝ≥0∞) := by
    rw [← sum_two_add_two_mul]
    push_cast
    rfl
  rw [hsum, Nat.cast_mul, mul_comm, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hM.ne') (ENNReal.natCast_ne_top _), one_mul]
  push_cast
  rfl

variable [IsProbabilityMeasure μ]

lemma meas_W_false (l : ℕ) : μ (R.W l ⁻¹' {false}) = 1 - μ (R.W l ⁻¹' {true}) := by
  rw [show R.W l ⁻¹' {false} = (R.W l ⁻¹' {true})ᶜ by ext ω; simp,
    prob_compl_eq_one_sub (R.measurableSet_W_true l)]

omit [IsProbabilityMeasure μ] in
/-- **The stage law, averaged:** stage `l` succeeds with probability `stageProb G ψ (M l)`. -/
lemma meas_W_true (ha1 : goodProb G ψ < 1) (l : ℕ) (hM : 0 < M l) :
    μ (R.W l ⁻¹' {true}) = ENNReal.ofReal (stageProb G ψ (M l)) := by
  have hU : R.W l ⁻¹' {true} = ⋃ j, (R.J l ⁻¹' {j} ∩ R.W l ⁻¹' {true}) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun j => R.J l ⁻¹' {j} ∩ R.W l ⁻¹' {true}) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨hi, -⟩ ⟨hj, -⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hj
    exact hij (hi.symm.trans hj)
  rw [hU, measure_iUnion hdisj fun j => (R.measurableSet_J l j).inter (R.measurableSet_W_true l)]
  simp_rw [R.law]
  rw [tsum_eq_sum (s := Finset.range (M l)) fun j hj => by
      rw [R.uniform, if_neg (by simpa using hj), zero_mul]]
  rw [Finset.sum_congr rfl fun j hj => by rw [R.uniform, if_pos (Finset.mem_range.mp hj)]]
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun j _ => stageProbAt_nonneg ha1 j,
    stageProb, ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _)),
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 hM), ENNReal.ofReal_natCast]

/-! ### Past the critical stage -/

/-- Once every stage from `l₀` on succeeds with probability at least `1/4`, the probability of
reaching stage `l` is at most `(3/4)^{l − l₀}`. -/
lemma meas_reach_le (l₀ : ℕ)
    (hq : ∀ k, l₀ ≤ k → ENNReal.ofReal (1 / 4) ≤ μ (R.W k ⁻¹' {true})) (l : ℕ) :
    μ (R.reach l) ≤ ENNReal.ofReal (3 / 4) ^ (l - l₀) := by
  induction l with
  | zero => simp [reach]
  | succ l ih =>
    rw [R.meas_reach] at ih ⊢
    rw [Finset.prod_range_succ]
    by_cases hl : l₀ ≤ l
    · have h34 : μ (R.W l ⁻¹' {false}) ≤ ENNReal.ofReal (3 / 4) := by
        rw [R.meas_W_false, tsub_le_iff_right]
        calc (1 : ℝ≥0∞) = ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) := by
              rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
          _ ≤ ENNReal.ofReal (3 / 4) + μ (R.W l ⁻¹' {true}) := add_le_add_right (hq l hl) _
      rw [show l + 1 - l₀ = (l - l₀) + 1 by omega, pow_succ]
      exact mul_le_mul' ih h34
    · rw [show l + 1 - l₀ = l - l₀ by omega]
      calc (∏ k ∈ Finset.range l, μ (R.W k ⁻¹' {false})) * μ (R.W l ⁻¹' {false})
          ≤ (∏ k ∈ Finset.range l, μ (R.W k ⁻¹' {false})) * 1 := mul_le_mul' le_rfl prob_le_one
        _ ≤ ENNReal.ofReal (3 / 4) ^ (l - l₀) := by rw [mul_one]; exact ih

end QSearchRun

/-! ## The series -/

/-- The geometric weights of the schedule: `(5/6)^{l₀−l}` up to the critical stage `l₀`,
`(9/10)^{l−l₀}` after it. -/
noncomputable def qsearchWeight (l₀ l : ℕ) : ℝ :=
  if l ≤ l₀ then (5 / 6) ^ (l₀ - l) else (9 / 10) ^ (l - l₀)

omit [Fintype ι] [DecidableEq ι] in
lemma sum_qsearchWeight_le (l₀ N : ℕ) : ∑ l ∈ Finset.range N, qsearchWeight l₀ l ≤ 15 := by
  have hA : ∀ N, ∑ l ∈ Finset.range N, (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0) ≤ 6 := by
    intro N
    have hnn : ∀ l, 0 ≤ (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0) := fun l => by
      split_ifs <;> positivity
    calc ∑ l ∈ Finset.range N, (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0)
        ≤ ∑ l ∈ Finset.range (max N (l₀ + 1)), (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (le_max_left N (l₀ + 1))) fun l _ _ => hnn l
      _ = ∑ l ∈ Finset.range (l₀ + 1), (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0) := by
          rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N (l₀ + 1)),
            Finset.sum_eq_zero (s := Finset.Ico (l₀ + 1) (max N (l₀ + 1))) fun l hl => if_neg (by
              have := (Finset.mem_Ico.mp hl).1; omega), add_zero]
      _ = ∑ l ∈ Finset.range (l₀ + 1), (5 / 6 : ℝ) ^ (l₀ - l) :=
          Finset.sum_congr rfl fun l hl => if_pos (by
            have := Finset.mem_range.mp hl; omega)
      _ = ∑ i ∈ Finset.range (l₀ + 1), (5 / 6 : ℝ) ^ i := by
          rw [← Finset.sum_range_reflect (fun i => (5 / 6 : ℝ) ^ i) (l₀ + 1)]
          exact Finset.sum_congr rfl fun l _ => by
            rw [show l₀ + 1 - 1 - l = l₀ - l by omega]
      _ ≤ ∑' i : ℕ, (5 / 6 : ℝ) ^ i :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
            fun i _ => by positivity
      _ = 6 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hB : ∀ N, ∑ l ∈ Finset.range N, (if l ≤ l₀ then 0 else (9 / 10 : ℝ) ^ (l - l₀)) ≤ 9 := by
    intro N
    rcases le_or_gt N (l₀ + 1) with hN | hN
    · rw [Finset.sum_eq_zero fun l hl => if_pos (by have := Finset.mem_range.mp hl; omega)]
      norm_num
    · rw [← Finset.sum_range_add_sum_Ico _ hN.le,
        Finset.sum_eq_zero fun l hl => if_pos (by have := Finset.mem_range.mp hl; omega),
        zero_add,
        Finset.sum_congr rfl fun l hl => if_neg (by have := (Finset.mem_Ico.mp hl).1; omega),
        Finset.sum_Ico_eq_sum_range]
      calc ∑ k ∈ Finset.range (N - (l₀ + 1)), (9 / 10 : ℝ) ^ (l₀ + 1 + k - l₀)
          = ∑ k ∈ Finset.range (N - (l₀ + 1)), (9 / 10 : ℝ) * (9 / 10) ^ k :=
            Finset.sum_congr rfl fun k _ => by
              rw [show l₀ + 1 + k - l₀ = k + 1 by omega, pow_succ, mul_comm]
        _ = (9 / 10 : ℝ) * ∑ k ∈ Finset.range (N - (l₀ + 1)), (9 / 10 : ℝ) ^ k := by
            rw [Finset.mul_sum]
        _ ≤ (9 / 10 : ℝ) * ∑' k : ℕ, (9 / 10 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left ((summable_geometric_of_lt_one (by norm_num)
              (by norm_num)).sum_le_tsum _ fun i _ => by positivity) (by norm_num)
        _ = 9 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hsplit : ∀ l, qsearchWeight l₀ l = (if l ≤ l₀ then (5 / 6 : ℝ) ^ (l₀ - l) else 0)
      + (if l ≤ l₀ then 0 else (9 / 10 : ℝ) ^ (l - l₀)) := by
    intro l
    unfold qsearchWeight
    split_ifs <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  linarith [hA N, hB N]

omit [Fintype ι] [DecidableEq ι] in
/-- **The schedule series, bounded:** every partial sum of `(M_l + 1)(3/4)^{l − l₀}` is at most
`45 · (6/5)^{l₀}`. Before the critical stage the terms are `≤ 3 c^l = 3 c^{l₀} (5/6)^{l₀−l}`,
after it `≤ 3 c^{l₀} (9/10)^{l−l₀}`. -/
lemma qsearch_partial_sum_le (l₀ N : ℕ) :
    ∑ l ∈ Finset.range N, ((qsearchGuess l : ℝ) + 1) * (3 / 4) ^ (l - l₀)
      ≤ 45 * qsearchRatio ^ l₀ := by
  have hterm : ∀ l, ((qsearchGuess l : ℝ) + 1) * (3 / 4) ^ (l - l₀)
      ≤ 3 * qsearchRatio ^ l₀ * qsearchWeight l₀ l := by
    intro l
    have hM : (qsearchGuess l : ℝ) + 1 ≤ 3 * qsearchRatio ^ l := by
      linarith [qsearchGuess_lt l, one_le_qsearchRatio_pow l]
    unfold qsearchWeight
    split_ifs with hl
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [Nat.sub_eq_zero_of_le (Nat.le_add_right l d), pow_zero, mul_one, Nat.add_sub_cancel_left,
        pow_add, mul_assoc, mul_assoc, ← mul_pow,
        show qsearchRatio * (5 / 6) = 1 by norm_num [qsearchRatio], one_pow, mul_one]
      exact hM
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hl)
      rw [show l₀ + d + 1 - l₀ = d + 1 by omega]
      calc ((qsearchGuess (l₀ + d + 1) : ℝ) + 1) * (3 / 4) ^ (d + 1)
          ≤ 3 * qsearchRatio ^ (l₀ + d + 1) * (3 / 4) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right hM (by positivity)
        _ = 3 * qsearchRatio ^ l₀ * (qsearchRatio ^ (d + 1) * (3 / 4) ^ (d + 1)) := by
            rw [show l₀ + d + 1 = l₀ + (d + 1) by ring, pow_add qsearchRatio l₀ (d + 1)]; ring
        _ = 3 * qsearchRatio ^ l₀ * (9 / 10) ^ (d + 1) := by
            rw [← mul_pow, show qsearchRatio * (3 / 4) = 9 / 10 by norm_num [qsearchRatio]]
  calc ∑ l ∈ Finset.range N, ((qsearchGuess l : ℝ) + 1) * (3 / 4) ^ (l - l₀)
      ≤ ∑ l ∈ Finset.range N, 3 * qsearchRatio ^ l₀ * qsearchWeight l₀ l :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = 3 * qsearchRatio ^ l₀ * ∑ l ∈ Finset.range N, qsearchWeight l₀ l := by
        rw [Finset.mul_sum]
    _ ≤ 3 * qsearchRatio ^ l₀ * 15 :=
        mul_le_mul_of_nonneg_left (sum_qsearchWeight_le l₀ N)
          (by have := one_le_qsearchRatio_pow l₀; linarith)
    _ = 45 * qsearchRatio ^ l₀ := by ring

/-! ## The expected cost -/

namespace QSearchRun

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The expected cost past a critical stage:** if every stage from `l₀` on succeeds with
probability at least `1/4`, the expected cost is at most `45 · (6/5)^{l₀}`. -/
theorem lintegral_cost_le (R : QSearchRun G ψ qsearchGuess μ) (l₀ : ℕ)
    (hq : ∀ k, l₀ ≤ k → ENNReal.ofReal (1 / 4) ≤ μ (R.W k ⁻¹' {true})) :
    ∫⁻ ω, R.cost ω ∂μ ≤ ENNReal.ofReal (45 * qsearchRatio ^ l₀) := by
  rw [R.lintegral_cost]
  have h1 : ∀ l, ∫⁻ ω, R.stageCost l ω ∂μ = ((qsearchGuess l : ℝ≥0∞) + 1) * μ (R.reach l) :=
    fun l => R.lintegral_stageCost l (qsearchGuess_pos l)
  simp_rw [h1]
  have hcast : ∀ l, ((qsearchGuess l : ℝ≥0∞) + 1) * ENNReal.ofReal (3 / 4) ^ (l - l₀)
      = ENNReal.ofReal (((qsearchGuess l : ℝ) + 1) * (3 / 4) ^ (l - l₀)) := by
    intro l
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  calc ∑' l, ((qsearchGuess l : ℝ≥0∞) + 1) * μ (R.reach l)
      ≤ ∑' l, ((qsearchGuess l : ℝ≥0∞) + 1) * ENNReal.ofReal (3 / 4) ^ (l - l₀) :=
        ENNReal.tsum_le_tsum fun l => mul_le_mul' le_rfl (R.meas_reach_le l₀ hq l)
    _ ≤ ENNReal.ofReal (45 * qsearchRatio ^ l₀) := by
        refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
        simp_rw [hcast]
        rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => by positivity]
        exact ENNReal.ofReal_le_ofReal (qsearch_partial_sum_le l₀ N)

/-- ★★ **BHMT Theorem 3, the upper bound.** For a unit state with unknown success probability
`0 < a < 1`, a run of QSearch uses at most `54/√a` applications of `A` and `A⁻¹` in
expectation. Below `a ≤ 3/4` the critical stage `l₀` is the first with `(6/5)^{l₀} > 1/sin 2θ`,
past which every stage succeeds with probability `≥ 1/4`; above it the direct measurement
already succeeds with probability `> 3/4` at every stage. -/
theorem qsearch_expected_cost (R : QSearchRun G ψ qsearchGuess μ) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    ∫⁻ ω, R.cost ω ∂μ ≤ ENNReal.ofReal (54 / Real.sqrt (goodProb G ψ)) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = goodProb G ψ := ⟨_, rfl⟩
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (ha ▸ ha0)
  have hsa1 : Real.sqrt a ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by rw [ha]; exact ha1.le)
  -- the stage law
  have hstage : ∀ l, μ (R.W l ⁻¹' {true}) = ENNReal.ofReal (stageProb G ψ (qsearchGuess l)) :=
    fun l => R.meas_W_true ha1 l (qsearchGuess_pos l)
  rcases le_or_gt a (3 / 4) with h34 | h34
  · -- `sin 2θ = 2√(a(1−a)) ≥ √a`
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 * Real.sqrt (goodProb G ψ * (1 - goodProb G ψ)) := ⟨_, rfl⟩
    have hspos : 0 < s := by
      rw [hs]
      have : 0 < goodProb G ψ * (1 - goodProb G ψ) := mul_pos ha0 (by linarith)
      have := Real.sqrt_pos.mpr this
      linarith
    have hs1 : s ≤ 1 := by
      rw [hs, ← ha]
      have h1 : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
      have h2 : Real.sqrt (a * (1 - a)) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hsqa : Real.sqrt a ≤ s := by
      rw [hs, ← ha, Real.sqrt_mul (ha ▸ ha0.le)]
      have h1 : (1 / 2 : ℝ) ≤ Real.sqrt (1 - a) := by
        rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg a]
    -- the critical stage
    have hex : ∃ n : ℕ, 1 / s < qsearchRatio ^ n := pow_unbounded_of_one_lt _ one_lt_qsearchRatio
    obtain ⟨l₀, hl₀, hmin⟩ : ∃ l₀ : ℕ, 1 / s < qsearchRatio ^ l₀ ∧
        ∀ m < l₀, ¬ 1 / s < qsearchRatio ^ m :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hq : ∀ k, l₀ ≤ k → ENNReal.ofReal (1 / 4) ≤ μ (R.W k ⁻¹' {true}) := by
      intro k hk
      rw [hstage]
      refine ENNReal.ofReal_le_ofReal (quarter_le_stageProb hψ ha0 ha1 _ ?_)
      rw [← hs]
      have h1 : qsearchRatio ^ l₀ ≤ qsearchRatio ^ k :=
        pow_le_pow_right₀ one_lt_qsearchRatio.le hk
      have h2 := le_qsearchGuess k
      have h3 : 1 / s < qsearchGuess k := by linarith
      rw [div_lt_iff₀ hspos] at h3
      linarith
    have hbound : 45 * qsearchRatio ^ l₀ ≤ 54 / Real.sqrt a := by
      have hcl : qsearchRatio ^ l₀ ≤ qsearchRatio / s := by
        rcases l₀ with _ | m
        · rw [pow_zero, le_div_iff₀ hspos, one_mul]
          exact hs1.trans one_lt_qsearchRatio.le
        · have h := not_lt.mp (hmin m (Nat.lt_succ_self m))
          rw [pow_succ, mul_comm, div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left h (by linarith [one_lt_qsearchRatio])
      calc 45 * qsearchRatio ^ l₀ ≤ 45 * (qsearchRatio / s) :=
            mul_le_mul_of_nonneg_left hcl (by norm_num)
        _ = 54 / s := by rw [qsearchRatio]; ring
        _ ≤ 54 / Real.sqrt a := div_le_div_of_nonneg_left (by norm_num) hsa hsqa
    calc ∫⁻ ω, R.cost ω ∂μ ≤ ENNReal.ofReal (45 * qsearchRatio ^ l₀) := R.lintegral_cost_le l₀ hq
      _ ≤ ENNReal.ofReal (54 / Real.sqrt (goodProb G ψ)) := by
          rw [← ha]; exact ENNReal.ofReal_le_ofReal hbound
  · -- `a > 3/4`: every stage succeeds with probability at least `a`
    have hq : ∀ k, 0 ≤ k → ENNReal.ofReal (1 / 4) ≤ μ (R.W k ⁻¹' {true}) := by
      intro k _
      rw [hstage]
      refine ENNReal.ofReal_le_ofReal ?_
      have := le_stageProb ha1 (qsearchGuess_pos k)
      rw [← ha] at this
      linarith
    have hbound : 45 * qsearchRatio ^ 0 ≤ 54 / Real.sqrt a := by
      rw [pow_zero, mul_one, le_div_iff₀ hsa]
      nlinarith
    calc ∫⁻ ω, R.cost ω ∂μ ≤ ENNReal.ofReal (45 * qsearchRatio ^ 0) := R.lintegral_cost_le 0 hq
      _ ≤ ENNReal.ofReal (54 / Real.sqrt (goodProb G ψ)) := by
          rw [← ha]; exact ENNReal.ofReal_le_ofReal hbound

end QSearchRun

/-! ## The model is consistent: a run on the product of the stage laws -/

/-- The law of one stage with guess `M` and conditional success probabilities `q`: the round
count `j` uniform below `M`, then success with probability `q j`. -/
noncomputable def stageMeasure (q : ℕ → ℝ) (M : ℕ) : Measure (ℕ × Bool) :=
  (M : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range M,
    (ENNReal.ofReal (q j) • Measure.dirac (j, true)
      + ENNReal.ofReal (1 - q j) • Measure.dirac (j, false))

omit [Fintype ι] [DecidableEq ι] in
lemma stageMeasure_apply (q : ℕ → ℝ) (M : ℕ) {S : Set (ℕ × Bool)} (hS : MeasurableSet S) :
    stageMeasure q M S = (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M,
      (ENNReal.ofReal (q j) * S.indicator 1 (j, true)
        + ENNReal.ofReal (1 - q j) * S.indicator 1 (j, false)) := by
  simp only [stageMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.add_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma stageMeasure_univ (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) {M : ℕ}
    (hM : 0 < M) : stageMeasure q M Set.univ = 1 := by
  rw [stageMeasure_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  have h1 : ∀ j, ENNReal.ofReal (q j) + ENNReal.ofReal (1 - q j) = 1 := fun j => by
    rw [← ENNReal.ofReal_add (hq0 j) (by linarith [hq1 j])]
    norm_num
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hM.ne') (ENNReal.natCast_ne_top _)

omit [Fintype ι] [DecidableEq ι] in
/-- The marginal of the round count: uniform below `M`. -/
lemma stageMeasure_fst (q : ℕ → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (M j : ℕ) :
    stageMeasure q M (Prod.fst ⁻¹' {j}) = if j < M then (M : ℝ≥0∞)⁻¹ else 0 := by
  rw [stageMeasure_apply _ _ (measurable_fst (measurableSet_singleton j))]
  have h1 : ∀ j, ENNReal.ofReal (q j) + ENNReal.ofReal (1 - q j) = 1 := fun j => by
    rw [← ENNReal.ofReal_add (hq0 j) (by linarith [hq1 j])]
    norm_num
  have hterm : ∀ i, ENNReal.ofReal (q i) * (Prod.fst ⁻¹' {j}).indicator 1 (i, true)
      + ENNReal.ofReal (1 - q i) * (Prod.fst ⁻¹' {j}).indicator 1 (i, false)
      = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [h1]
    · simp [hij]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
/-- The joint law: round count `j` and success, with probability `M⁻¹ q j`. -/
lemma stageMeasure_singleton_true (q : ℕ → ℝ) (M j : ℕ) :
    stageMeasure q M {(j, true)} = if j < M then (M : ℝ≥0∞)⁻¹ * ENNReal.ofReal (q j) else 0 := by
  rw [stageMeasure_apply _ _ (measurableSet_singleton _)]
  have hterm : ∀ i, ENNReal.ofReal (q i) * ({(j, true)} : Set (ℕ × Bool)).indicator 1 (i, true)
      + ENNReal.ofReal (1 - q i) * ({(j, true)} : Set (ℕ × Bool)).indicator 1 (i, false)
      = if i = j then ENNReal.ofReal (q j) else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> simp

/-- ★ **The model is consistent.** For every unit state with `0 < a < 1` and every schedule of
positive guesses, the product of the stage laws over the stages carries a `QSearchRun`: the
coordinates are independent (`iIndepFun_infinitePi`) and each has the stage law. -/
theorem exists_qsearchRun (hψ : ‖ψ‖ = 1) (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1)
    (M : ℕ → ℕ) (hM : ∀ l, 0 < M l) :
    ∃ μ : Measure (ℕ → ℕ × Bool), IsProbabilityMeasure μ ∧ Nonempty (QSearchRun G ψ M μ) := by
  have hq0 := stageProbAt_nonneg (G := G) (ψ := ψ) ha1
  have hq1 := stageProbAt_le_one hψ ha0 ha1
  let P : ℕ → Measure (ℕ × Bool) := fun l => stageMeasure (stageProbAt G ψ) (M l)
  have : ∀ l, IsProbabilityMeasure (P l) := fun l =>
    ⟨stageMeasure_univ _ hq0 hq1 (hM l)⟩
  refine ⟨Measure.infinitePi P, inferInstance, ⟨?_⟩⟩
  have hmarg : ∀ (l : ℕ) (S : Set (ℕ × Bool)), MeasurableSet S →
      Measure.infinitePi P ((fun ω => ω l) ⁻¹' S) = P l S := fun l S hS => by
    rw [← Measure.map_apply (measurable_pi_apply l) hS, Measure.infinitePi_map_eval]
  refine
    { J := fun l ω => (ω l).1
      W := fun l ω => (ω l).2
      measurable_J := fun l => measurable_fst.comp (measurable_pi_apply l)
      measurable_W := fun l => measurable_snd.comp (measurable_pi_apply l)
      indep := ?_
      uniform := fun l j => ?_
      law := fun l j => ?_ }
  · exact iIndepFun_infinitePi (X := fun _ => (id : ℕ × Bool → ℕ × Bool)) fun _ => measurable_id
  · rw [show (fun ω : ℕ → ℕ × Bool => (ω l).1) ⁻¹' {j}
        = (fun ω => ω l) ⁻¹' (Prod.fst ⁻¹' {j}) from rfl,
      hmarg l _ (measurable_fst (measurableSet_singleton j))]
    exact stageMeasure_fst _ hq0 hq1 (M l) j
  · rw [show (fun ω : ℕ → ℕ × Bool => (ω l).1) ⁻¹' {j}
        ∩ (fun ω : ℕ → ℕ × Bool => (ω l).2) ⁻¹' {true}
        = (fun ω => ω l) ⁻¹' {(j, true)} from by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff],
      show (fun ω : ℕ → ℕ × Bool => (ω l).1) ⁻¹' {j}
        = (fun ω => ω l) ⁻¹' (Prod.fst ⁻¹' {j}) from rfl,
      hmarg l _ (measurableSet_singleton _),
      hmarg l _ (measurable_fst (measurableSet_singleton j)),
      stageMeasure_singleton_true, stageMeasure_fst _ hq0 hq1]
    split_ifs <;> simp

end QuantumInfo

end
