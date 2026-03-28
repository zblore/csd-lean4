import CsdLean4.LF1.Expectation
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace LF1

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

namespace TrialModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/--
Strong law for the indicator random variables attached to a fixed outcome region.

It shows that the empirical frequency converges almost surely to the expectation of
the indicator random variable.  The separate identification of that expectation with
the ontic weight is handled below through `integral_indicatorRV_eq_weightReal`.

Integrability and identical distribution are derived automatically from the model;
only pairwise independence must be supplied by the caller.
-/
theorem strongLaw_indicator_to_mean_ae
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ =>
          (∑ i ∈ Finset.range n, T.indicatorRV (S := S) O i ω) / (n : ℝ))
        atTop
        (nhds (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure)) :=
  strong_law_ae_real
    (fun n => T.indicatorRV (S := S) O n)
    (T.indicatorRV_integrable (S := S) O 0)
    hindep
    (fun n => T.indicatorRV_identDistrib (S := S) O n)

/--
If the expectation of the indicator random variable has been identified with the
ontic preparation weight, then the empirical frequency converges almost surely to
that weight.
-/
theorem strongLaw_indicator_to_weight_ae
    (O : S.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := S) O n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ =>
          (∑ i ∈ Finset.range n, T.indicatorRV (S := S) O i ω) / (n : ℝ))
        atTop
        (nhds (O.weightReal)) := by
  filter_upwards
    [T.strongLaw_indicator_to_mean_ae (S := S) O hindep] with ω hω
  simpa [T.integral_indicatorRV_eq_weightReal (S := S) O 0] using hω

/--
Version of the previous theorem written using the `empiricalFreq` abbreviation from
`Indicators.lean`.
-/
theorem strongLaw_empiricalFreq_to_weight_ae
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
        (nhds (O.weightReal)) := by
  filter_upwards
    [T.strongLaw_indicator_to_weight_ae (S := S) O hindep] with ω hω
  simpa [TrialModel.empiricalFreq] using hω

end TrialModel

end OnticSetup

end LF1
end CSD
