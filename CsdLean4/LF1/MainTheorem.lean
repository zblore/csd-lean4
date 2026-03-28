import CsdLean4.LF1.Setup
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.Trials
import CsdLean4.LF1.Indicators
import CsdLean4.LF1.Expectation
import CsdLean4.LF1.Convergence

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

namespace TrialModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/--
LF1 main theorem, real-valued version.

For a fixed measurable outcome region `O`, if the indicator random variables attached to
the repeated-trial model are integrable, pairwise independent, and identically distributed,
then the empirical frequencies converge almost surely to the corresponding real-valued
ontic weight.
-/
theorem main_theorem_ae
    (O : S.OutcomeRegion)
    (hint :
      Integrable (T.indicatorRV (S := S) O 0) (T.trialMeasure))
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n)))
    (hident :
      ∀ n,
        IdentDistrib
          (T.indicatorRV (S := S) O n)
          (T.indicatorRV (S := S) O 0)
          (T.trialMeasure) (T.trialMeasure)) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (T.weightReal (S := S) O)) := by
  apply T.strongLaw_empiricalFreq_to_weight_ae (S := S) O hint hindep hident
  exact T.integral_indicatorRV_eq_weightReal (S := S) O 0 hint

/--
Equivalent statement written with the expectation of the indicator random variable as
the limit. This is useful when citing the theorem in a probability-theoretic form.
-/
theorem main_theorem_ae_mean_form
    (O : S.OutcomeRegion)
    (hint :
      Integrable (T.indicatorRV (S := S) O 0) (T.trialMeasure))
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n)))
    (hident :
      ∀ n,
        IdentDistrib
          (T.indicatorRV (S := S) O n)
          (T.indicatorRV (S := S) O 0)
          (T.trialMeasure) (T.trialMeasure)) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure)) := by
  apply T.strongLaw_indicator_to_mean_ae (S := S) O hint hindep hident

/--
The expectation of the indicator random variable equals the real-valued ontic weight.
This is the expectation-to-weight bridge isolated for separate citation.
-/
theorem expectation_eq_weight
    (O : S.OutcomeRegion)
    (n : ℕ)
    (hint :
      Integrable (T.indicatorRV (S := S) O n) (T.trialMeasure)) :
    (∫ x, T.indicatorRV (S := S) O n x ∂ T.trialMeasure)
      =
    T.weightReal (S := S) O := by
  exact T.integral_indicatorRV_eq_weightReal (S := S) O n hint

/--
All trial expectations agree, because every trial has the same preparation law.
-/
theorem expectation_constant_across_trials
    (O : S.OutcomeRegion)
    (n : ℕ)
    (hint :
      Integrable (T.indicatorRV (S := S) O n) (T.trialMeasure))
    (hint0 :
      Integrable (T.indicatorRV (S := S) O 0) (T.trialMeasure)) :
    (∫ x, T.indicatorRV (S := S) O n x ∂ T.trialMeasure)
      =
    (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) := by
  exact T.integral_indicatorRV_eq_weightReal_zero (S := S) O n hint hint0

end TrialModel

/--
A convenient top-level alias for the LF1 theorem.

This is the statement most closely matching the manuscript:
empirical frequencies converge almost surely to the real-valued normalised ontic weight.
-/
theorem LF1_main_theorem_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hint :
      Integrable (T.indicatorRV (S := S) O 0) (T.trialMeasure))
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n)))
    (hident :
      ∀ n,
        IdentDistrib
          (T.indicatorRV (S := S) O n)
          (T.indicatorRV (S := S) O 0)
          (T.trialMeasure) (T.trialMeasure)) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (T.weightReal (S := S) O)) :=
  T.main_theorem_ae (S := S) O hint hindep hident

end OnticSetup

end LF1
end CSD
