import CsdLean4.LF1.Indicators
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory Set ENNReal

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

namespace TrialModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/-- The probability measure on the external repeated-trial sample space. -/
abbrev trialMeasure : Measure Ω :=
  ((T.P : ProbabilityMeasure Ω) : Measure Ω)

/--
Real-valued version of the ontic outcome weight.

This is the quantity that should appear as the expectation of the real-valued
indicator random variable.
-/
noncomputable def weightReal (O : S.OutcomeRegion) : ℝ :=
  ENNReal.toReal (O.weight (S := S))

/-- The same weight computed from the `n`-th trial event. -/
noncomputable def trialProbReal (O : S.OutcomeRegion) (n : ℕ) : ℝ :=
  ENNReal.toReal (T.trialProb (S := S) O n)

@[simp]
lemma trialProbReal_eq_weightReal (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProbReal (S := S) O n = T.weightReal (S := S) O := by
  unfold trialProbReal weightReal
  rw [T.trialProb_eq_weight (S := S) O n]

/--
The expectation of the indicator random variable is the real-valued probability of
the corresponding trial event.

This is the key bridge lemma for LF1.
-/
lemma integral_indicatorRV_eq_trialProbReal
    (O : S.OutcomeRegion) (n : ℕ)
    (hint : Integrable (T.indicatorRV (S := S) O n) (T.trialMeasure)) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      = T.trialProbReal (S := S) O n := by
  classical
  unfold TrialModel.indicatorRV TrialModel.trialProbReal TrialModel.trialProb
  -- Expected route:
  -- 1. rewrite the integral of the indicator as an integral over the restricted measure
  -- 2. evaluate the integral of the constant function `1`
  -- 3. identify the resulting measure with the trial-event probability
  --
  -- In current Mathlib, this should be discharged by the standard indicator-integral
  -- lemmas from `Mathlib.MeasureTheory.Integral.Bochner.Set`. The exact simp-normal
  -- form can vary slightly with the pinned version.
  rw [integral_indicator (T.measurable_trialEvent (S := S) O n)]
  simp [T.measurable_trialEvent (S := S) O n]

/--
The expectation of the indicator random variable is the real-valued ontic weight.
-/
lemma integral_indicatorRV_eq_weightReal
    (O : S.OutcomeRegion) (n : ℕ)
    (hint : Integrable (T.indicatorRV (S := S) O n) (T.trialMeasure)) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      = T.weightReal (S := S) O := by
  rw [T.integral_indicatorRV_eq_trialProbReal (S := S) O n hint]
  exact T.trialProbReal_eq_weightReal (S := S) O n

/--
All indicator expectations agree across trials, because each trial has the same law.
-/
lemma integral_indicatorRV_eq_weightReal_zero
    (O : S.OutcomeRegion) (n : ℕ)
    (hint : Integrable (T.indicatorRV (S := S) O n) (T.trialMeasure))
    (hint0 : Integrable (T.indicatorRV (S := S) O 0) (T.trialMeasure)) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      =
    ∫ ω, T.indicatorRV (S := S) O 0 ω ∂ T.trialMeasure := by
  rw [T.integral_indicatorRV_eq_weightReal (S := S) O n hint]
  rw [T.integral_indicatorRV_eq_weightReal (S := S) O 0 hint0]

end TrialModel

end OnticSetup

end LF1
end CSD
