import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.Trials
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

/--
A repeated-trial model for LF1.

`Ω` is the external sample space indexing repeated experimental runs.
`P` is the probability law on that sample space.
`X n` is the ontic initial microstate used on the `n`-th trial.

At this stage we require only that each `X n` is measurable and has law equal to
the preparation probability measure `S.prepMeasure`.

Independence is intentionally deferred to the next stage, once the exact law of
large numbers route in `Convergence.lean` is fixed.
-/
structure TrialModel (Ω : Type*) [MeasurableSpace Ω] where
  P : ProbabilityMeasure Ω
  X : ℕ → Ω → Σ
  hX_measurable : ∀ n, Measurable (X n)
  hLaw : ∀ n,
    Measure.map (X n) ((P : ProbabilityMeasure Ω) : Measure Ω) =
      ((S.prepMeasure : ProbabilityMeasure Σ) : Measure Σ)

namespace TrialModel

variable {S}

/-- The law of the `n`-th trial random variable. -/
noncomputable def law
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (n : ℕ) : Measure Σ :=
  Measure.map (T.X n) ((T.P : ProbabilityMeasure Ω) : Measure Ω)

@[simp]
lemma law_eq_prepMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (n : ℕ) :
    T.law n = ((S.prepMeasure : ProbabilityMeasure Σ) : Measure Σ) :=
  T.hLaw n

@[simp]
lemma measurable_X
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (n : ℕ) :
    Measurable (T.X n) :=
  T.hX_measurable n

/--
The event on the external sample space that the `n`-th trial lands in the pulled-back
outcome region associated with `O`.
-/
def trialEvent
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (O : S.OutcomeRegion) (n : ℕ) : Set Ω :=
  T.X n ⁻¹' (O.preEvent (S := S))

lemma measurable_trialEvent
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (O : S.OutcomeRegion) (n : ℕ) :
    MeasurableSet (T.trialEvent O n) := by
  exact (O.measurable_preEvent (S := S)).preimage (T.measurable_X n)

/--
The probability of the `n`-th trial landing in outcome region `O`, computed on the
external sample space.
-/
noncomputable def trialProb
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (O : S.OutcomeRegion) (n : ℕ) : ℝ≥0∞ :=
  ((T.P : ProbabilityMeasure Ω) : Measure Ω) (T.trialEvent O n)

/--
The probability of the `n`-th trial landing in `O` agrees with the preparation weight
of `O`.
-/
lemma trialProb_eq_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = O.weight (S := S) := by
  dsimp [trialProb, TrialModel.trialEvent, OutcomeRegion.weight, OutcomeRegion.preEvent]
  rw [← T.hLaw n]
  rw [Measure.map_apply (T.hX_measurable n) (O.measurable_preEvent (S := S))]

/--
All trial probabilities agree, because each trial has the same law.
-/
lemma trialProb_eq_trialProb_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω) (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = T.trialProb O 0 := by
  rw [T.trialProb_eq_weight (S := S) O n, T.trialProb_eq_weight (S := S) O 0]

/--
The indicator random variable for outcome region `O` on trial `n`.

It takes value `1` exactly when the `n`-th sampled initial condition lies in the
pullback event associated with `O`, and `0` otherwise.
-/
noncomputable def indicatorRV (O : S.OutcomeRegion) (n : ℕ) : Ω → ℝ :=
  Set.indicator (T.trialEvent (S := S) O n) (fun _ => (1 : ℝ))

/-- Measurability of the indicator random variable. -/
lemma measurable_indicatorRV (O : S.OutcomeRegion) (n : ℕ) :
    Measurable (T.indicatorRV (S := S) O n) := by
  classical
  unfold indicatorRV
  exact Measurable.indicator (T.measurable_trialEvent (S := S) O n) measurable_const

/-- The indicator random variable takes value `1` on the event. -/
lemma indicatorRV_of_mem (O : S.OutcomeRegion) (n : ℕ) {ω : Ω}
    (hω : ω ∈ T.trialEvent (S := S) O n) :
    T.indicatorRV (S := S) O n ω = 1 := by
  classical
  unfold indicatorRV
  simp [Set.indicator_of_mem, hω]

/-- The indicator random variable takes value `0` off the event. -/
lemma indicatorRV_of_not_mem (O : S.OutcomeRegion) (n : ℕ) {ω : Ω}
    (hω : ω ∉ T.trialEvent (S := S) O n) :
    T.indicatorRV (S := S) O n ω = 0 := by
  classical
  unfold indicatorRV
  simp [Set.indicator_of_not_mem, hω]

/-- Pointwise nonnegativity of the indicator random variable. -/
lemma indicatorRV_nonneg (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    0 ≤ T.indicatorRV (S := S) O n ω := by
  classical
  by_cases hω : ω ∈ T.trialEvent (S := S) O n
  · rw [T.indicatorRV_of_mem (S := S) O n hω]; norm_num
  · rw [T.indicatorRV_of_not_mem (S := S) O n hω]; norm_num

/-- Pointwise upper bound by `1`. -/
lemma indicatorRV_le_one (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    T.indicatorRV (S := S) O n ω ≤ 1 := by
  classical
  by_cases hω : ω ∈ T.trialEvent (S := S) O n
  · rw [T.indicatorRV_of_mem (S := S) O n hω]; norm_num
  · rw [T.indicatorRV_of_not_mem (S := S) O n hω]; norm_num

/--
The indicator random variable is bounded in absolute value by `1`.
This is convenient later for integrability and law-of-large-numbers hypotheses.
-/
lemma norm_indicatorRV_le_one (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    ‖T.indicatorRV (S := S) O n ω‖ ≤ 1 := by
  have h0 := T.indicatorRV_nonneg (S := S) O n ω
  have h1 := T.indicatorRV_le_one (S := S) O n ω
  rw [Real.norm_of_nonneg h0]
  exact h1

/--
The indicator random variable is almost everywhere strongly measurable with respect
to the trial probability measure.
-/
lemma aestronglyMeasurable_indicatorRV (O : S.OutcomeRegion) (n : ℕ) :
    AEStronglyMeasurable (T.indicatorRV (S := S) O n)
      (((T.P : ProbabilityMeasure Ω) : Measure Ω)) :=
  (T.measurable_indicatorRV (S := S) O n).aestronglyMeasurable

/--
A convenient alias for the empirical average of the first `N` indicator variables
for outcome `O`.

This is the object whose convergence will be studied in `Convergence.lean`.
-/
noncomputable def empiricalFreq (O : S.OutcomeRegion) (N : ℕ) : Ω → ℝ :=
  fun ω =>
    (∑ j in Finset.range N, T.indicatorRV (S := S) O j ω) / N

end TrialModel

end OnticSetup

end LF1
end CSD
