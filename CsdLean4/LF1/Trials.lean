import CsdLean4.LF1.Outcomes
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] [Nonempty Σ] (S : OnticSetup Σ)

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
  X : ℕ → Ω → Σ
  hX_measurable : ∀ n, Measurable (X n)
  hLaw : ∀ n,
    Measure.map (X n) ((P : ProbabilityMeasure Ω) : Measure Ω) =
      ((S.prepMeasure : ProbabilityMeasure Σ) : Measure Σ)

namespace TrialModel

variable {S}
variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/-- The law of the `n`-th trial random variable. -/
noncomputable def law (n : ℕ) : Measure Σ :=
  Measure.map (T.X n) ((T.P : ProbabilityMeasure Ω) : Measure Ω)

@[simp]
lemma law_eq_prepMeasure (n : ℕ) :
    T.law n = ((S.prepMeasure : ProbabilityMeasure Σ) : Measure Σ) :=
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
noncomputable def trialProb (O : S.OutcomeRegion) (n : ℕ) : ℝ≥0∞ :=
  ((T.P : ProbabilityMeasure Ω) : Measure Ω) (T.trialEvent O n)

/-- The trial probability agrees with the preparation weight of `O`. -/
lemma trialProb_eq_weight (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = O.weight (S := S) := by
  sorry

/-- All trial probabilities agree, because each trial has the same law. -/
lemma trialProb_eq_trialProb_zero (O : S.OutcomeRegion) (n : ℕ) :
    T.trialProb O n = T.trialProb O 0 := by
  rw [T.trialProb_eq_weight (S := S) O n, T.trialProb_eq_weight (S := S) O 0]

end TrialModel

end OnticSetup

end LF1
end CSD
