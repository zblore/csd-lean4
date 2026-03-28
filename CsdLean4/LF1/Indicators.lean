import CsdLean4.LF1.Outcomes
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure

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

end TrialModel

end OnticSetup

end LF1
end CSD
