import CsdLean4.LF1.Trials
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

namespace TrialModel

variable {S}
variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/--
The indicator random variable for outcome region `O` on trial `n`.

Takes value `1` when the `n`-th sampled initial condition lies in the pullback
event associated with `O`, and `0` otherwise.
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
  classical; unfold indicatorRV; simp [Set.indicator_of_mem, hω]

/-- The indicator random variable takes value `0` off the event. -/
lemma indicatorRV_of_not_mem (O : S.OutcomeRegion) (n : ℕ) {ω : Ω}
    (hω : ω ∉ T.trialEvent (S := S) O n) :
    T.indicatorRV (S := S) O n ω = 0 := by
  classical; unfold indicatorRV; simp [Set.indicator_of_not_mem, hω]

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

/-- The indicator random variable is bounded in absolute value by `1`. -/
lemma norm_indicatorRV_le_one (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    ‖T.indicatorRV (S := S) O n ω‖ ≤ 1 :=
  Real.norm_of_nonneg (T.indicatorRV_nonneg (S := S) O n ω) ▸
    T.indicatorRV_le_one (S := S) O n ω

/-- The indicator random variable is a.e. strongly measurable w.r.t. the trial measure. -/
lemma aestronglyMeasurable_indicatorRV (O : S.OutcomeRegion) (n : ℕ) :
    AEStronglyMeasurable (T.indicatorRV (S := S) O n)
      ((T.P : ProbabilityMeasure Ω) : Measure Ω) :=
  (T.measurable_indicatorRV (S := S) O n).aestronglyMeasurable

/--
The empirical average of the first `N` indicator variables for outcome `O`.
This is the object whose almost sure convergence is studied in `Convergence.lean`.
-/
noncomputable def empiricalFreq (O : S.OutcomeRegion) (N : ℕ) : Ω → ℝ :=
  fun ω => (∑ j in Finset.range N, T.indicatorRV (S := S) O j ω) / N

end TrialModel

end OnticSetup

end LF1
end CSD
