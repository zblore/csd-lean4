/-
Main theorem of LF1.

The theorem proved here is a deterministic repeated-trial typicality theorem.
The ontic flow and outcome assignment are deterministic. Probability enters only
through the repeated-preparation model on initial conditions. The convergence
step then follows from a law of large numbers applied to the induced indicator
observables.
-/
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

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

namespace TrialModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/--
LF1 main theorem, real-valued version.

For a fixed measurable outcome region `O`, if the indicator random variables attached to
the repeated-trial model are pairwise independent, then the empirical frequencies converge
almost surely to the corresponding real-valued ontic weight.

Integrability and identical distribution are automatic consequences of the model
structure and need not be supplied by the caller.
-/
theorem main_theorem_ae
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (O.weightReal)) :=
  T.strongLaw_empiricalFreq_to_weight_ae (S := S) O hindep

/--
Equivalent statement written with the expectation of the indicator random variable as
the limit. This is useful when citing the theorem in a probability-theoretic form.
-/
theorem main_theorem_ae_mean_form
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure)) := by
  filter_upwards [T.strongLaw_indicator_to_mean_ae (S := S) O hindep] with ω hω
  simpa [TrialModel.empiricalFreq] using hω

/--
The expectation of the indicator random variable equals the real-valued ontic weight.
This is the expectation-to-weight bridge isolated for separate citation.
-/
theorem expectation_eq_weight
    (O : S.OutcomeRegion)
    (n : ℕ) :
    (∫ x, T.indicatorRV (S := S) O n x ∂ T.trialMeasure)
      =
    O.weightReal :=
  T.integral_indicatorRV_eq_weightReal (S := S) O n

/--
All trial expectations agree, because every trial has the same preparation law.
-/
theorem expectation_constant_across_trials
    (O : S.OutcomeRegion)
    (n : ℕ) :
    (∫ x, T.indicatorRV (S := S) O n x ∂ T.trialMeasure)
      =
    (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) :=
  T.integral_indicatorRV_eq_weightReal_zero (S := S) O n

end TrialModel

/--
A convenient top-level alias for the LF1 theorem.

This is the statement most closely matching the manuscript:
empirical frequencies converge almost surely to the real-valued normalised ontic weight.

The only non-trivial hypothesis is pairwise independence of the trial random variables.
Integrability and identical distribution follow automatically from the model.
-/
theorem LF1_main_theorem_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (O.weightReal)) :=
  T.main_theorem_ae (S := S) O hindep

end OnticSetup

end LF1
end CSD
