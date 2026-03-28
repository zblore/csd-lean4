import CsdLean4.LF1.Indicators
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Set Filter

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
Strong law for the indicator random variables attached to a fixed outcome region.

This is the clean first theorem for `Convergence.lean`. It shows that the empirical
frequency converges almost surely to the expectation of the indicator random variable.
The separate identification of that expectation with the ontic weight is handled below
through an explicit hypothesis `hmean`, which can later be replaced by a proved lemma.
-/
theorem strongLaw_indicator_to_mean_ae
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
        (fun n : ℕ =>
          (∑ i in Finset.range n, T.indicatorRV (S := S) O i ω) / (n : ℝ))
        atTop
        (nhds (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure)) := by
  simpa [trialMeasure] using
    (ProbabilityTheory.strong_law_ae_real
      (X := fun n => T.indicatorRV (S := S) O n)
      hint hindep hident)

/--
If the expectation of the indicator random variable has been identified with the
ontic preparation weight, then the empirical frequency converges almost surely to
that weight.
-/
theorem strongLaw_indicator_to_weight_ae
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
          (T.trialMeasure) (T.trialMeasure))
    (hmean :
      (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) = O.weightReal (S := S)) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ =>
          (∑ i in Finset.range n, T.indicatorRV (S := S) O i ω) / (n : ℝ))
        atTop
        (nhds (O.weightReal (S := S))) := by
  filter_upwards
    [T.strongLaw_indicator_to_mean_ae (S := S) O hint hindep hident] with ω hω
  simpa [hmean] using hω

/--
Version of the previous theorem written using the `empiricalFreq` abbreviation from
`Indicators.lean`.
-/
theorem strongLaw_empiricalFreq_to_weight_ae
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
          (T.trialMeasure) (T.trialMeasure))
    (hmean :
      (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) = O.weightReal (S := S)) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (O.weightReal (S := S))) := by
  filter_upwards
    [T.strongLaw_indicator_to_weight_ae (S := S) O hint hindep hident hmean] with ω hω
  simpa [TrialModel.empiricalFreq] using hω

end TrialModel

end OnticSetup

end LF1
end CSD
