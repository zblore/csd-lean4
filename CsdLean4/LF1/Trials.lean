/-
LF1 repeated-trial probability space.

This file introduces the repeated-preparation model used in LF1.
Each trial begins from a fresh initial microstate sampled from the conditional
preparation measure on the preparation region. The resulting product measure
models repetition of preparation, not stochastic dynamics of a single trial.

Single-trial evolution remains deterministic at the ontic level.
-/
import CsdLean4.LF1.Outcomes
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

/--
A repeated-trial model for LF1.

`Ω` is the external sample space indexing repeated experimental runs.
`P` is the probability law on that sample space.
`X n` is the ontic initial microstate used on the `n`-th trial.

Each `X n` is measurable and has law equal to the preparation probability measure
`S.prepMeasure`. Independence and identical distribution are declared as explicit
hypotheses in `Convergence.lean`, where the law of large numbers is applied.
-/
structure TrialModel (Ω : Type*) [MeasurableSpace Ω] where
  P : ProbabilityMeasure Ω
  X : ℕ → Ω → Sigma
  hX_measurable : ∀ n, Measurable (X n)
  hLaw : ∀ n,
    Measure.map (X n) ((P : ProbabilityMeasure Ω) : Measure Ω) =
      ((S.prepMeasure : ProbabilityMeasure Sigma) : Measure Sigma)

namespace TrialModel

variable {S}
variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/-- The law of the `n`-th trial random variable. -/
noncomputable def law (n : ℕ) : Measure Sigma :=
  Measure.map (T.X n) ((T.P : ProbabilityMeasure Ω) : Measure Ω)

@[simp]
lemma law_eq_prepMeasure (n : ℕ) :
    T.law n = ((S.prepMeasure : ProbabilityMeasure Sigma) : Measure Sigma) :=
  T.hLaw n

@[simp]
lemma measurable_X (n : ℕ) : Measurable (T.X n) :=
  T.hX_measurable n

/--
The event on the external sample space that the `n`-th trial lands in the
pulled-back outcome region associated with `O`.
-/
def trialEvent (O : S.OutcomeRegion) (n : ℕ) : Set Ω :=
  T.X n ⁻¹' (O.preEvent (S := S))

lemma measurable_trialEvent (O : S.OutcomeRegion) (n : ℕ) :
    MeasurableSet (T.trialEvent O n) :=
  (O.measurable_preEvent (S := S)).preimage (T.measurable_X n)

/--
The probability of the `n`-th trial landing in outcome region `O`, computed on
the external sample space.
-/
noncomputable def trialProb (O : S.OutcomeRegion) (n : ℕ) : ENNReal :=
  ((T.P : ProbabilityMeasure Ω) : Measure Ω) (T.trialEvent O n)

/-- The trial probability agrees with the preparation weight of `O`. -/
lemma trialProb_eq_weight (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = O.weight (S := S) := by
  unfold trialProb trialEvent OutcomeRegion.weight
  -- P(X n ⁻¹' preEvent) = (map Xn P)(preEvent)   [← Measure.map_apply, backward direction]
  -- then (map Xn P) = prepMeasure                  [T.hLaw n]
  rw [← Measure.map_apply (T.measurable_X n) (O.measurable_preEvent (S := S)), T.hLaw n]

/-- All trial probabilities agree, because each trial has the same law. -/
lemma trialProb_eq_trialProb_zero (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = T.trialProb O 0 := by
  rw [T.trialProb_eq_weight (S := S) O n, T.trialProb_eq_weight (S := S) O 0]

end TrialModel

end OnticSetup

end LF1
end CSD
