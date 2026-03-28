import CsdLean4.LF1.Indicators
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory Set ENNReal

namespace CSD
namespace LF1

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

namespace TrialModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/-- The probability measure on the external repeated-trial sample space. -/
abbrev trialMeasure : Measure Ω :=
  ((T.P : ProbabilityMeasure Ω) : Measure Ω)

/-- The same weight computed from the `n`-th trial event. -/
noncomputable def trialProbReal (O : S.OutcomeRegion) (n : ℕ) : ℝ :=
  ENNReal.toReal (T.trialProb (S := S) O n)

@[simp]
lemma trialProbReal_eq_weightReal (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProbReal (S := S) O n = O.weightReal := by
  unfold trialProbReal OutcomeRegion.weightReal
  rw [T.trialProb_eq_weight (S := S) O n]

/--
The expectation of the indicator random variable is the real-valued probability of
the corresponding trial event.

This is the key bridge lemma for LF1.
-/
lemma integral_indicatorRV_eq_trialProbReal
    (O : S.OutcomeRegion) (n : ℕ) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      = T.trialProbReal (S := S) O n := by
  unfold indicatorRV trialProbReal trialProb
  rw [integral_indicator (T.measurable_trialEvent (S := S) O n),
      setIntegral_const, smul_eq_mul, mul_one]
  simp [Measure.real]

/--
The expectation of the indicator random variable is the real-valued ontic weight.
-/
lemma integral_indicatorRV_eq_weightReal
    (O : S.OutcomeRegion) (n : ℕ) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      = O.weightReal := by
  rw [T.integral_indicatorRV_eq_trialProbReal (S := S) O n]
  exact T.trialProbReal_eq_weightReal (S := S) O n

/--
All indicator expectations agree across trials, because each trial has the same law.
-/
lemma integral_indicatorRV_eq_weightReal_zero
    (O : S.OutcomeRegion) (n : ℕ) :
    ∫ ω, T.indicatorRV (S := S) O n ω ∂ T.trialMeasure
      =
    ∫ ω, T.indicatorRV (S := S) O 0 ω ∂ T.trialMeasure := by
  rw [T.integral_indicatorRV_eq_weightReal (S := S) O n]
  rw [T.integral_indicatorRV_eq_weightReal (S := S) O 0]

end TrialModel

end OnticSetup

end LF1
end CSD
