import CsdLean4.LF1.Indicators
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory Set Filter ENNReal

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
      (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) = T.weightReal (S := S) O) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ =>
          (∑ i in Finset.range n, T.indicatorRV (S := S) O i ω) / (n : ℝ))
        atTop
        (nhds (T.weightReal (S := S) O)) := by
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
      (∫ x, T.indicatorRV (S := S) O 0 x ∂ T.trialMeasure) = T.weightReal (S := S) O) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := S) O n ω)
        atTop
        (nhds (T.weightReal (S := S) O)) := by
  filter_upwards
    [T.strongLaw_indicator_to_weight_ae (S := S) O hint hindep hident hmean] with ω hω
  simpa [TrialModel.empiricalFreq] using hω

end TrialModel

end OnticSetup

end LF1
end CSD
