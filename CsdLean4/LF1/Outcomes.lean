/-
LF1 outcome regions.

Outcome regions are measurable ontic regions associated with a fixed
experimental context. In LF1 they are treated abstractly as measurable sets.
The realised outcome of a single trial is determined by whether the deterministic
evolution of the sampled microstate lands in the corresponding outcome region.

No stochastic outcome law is postulated at this stage.
-/
import CsdLean4.LF1.Preparation

open MeasureTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

/-- A single measurable outcome region in the ontic state space.
    Parameterized by `S` so that `S.OutcomeRegion` works as dot notation. -/
structure OutcomeRegion {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma]
    (_S : OnticSetup Sigma) where
  Ω : Set Sigma
  hΩ_meas : MeasurableSet Ω

namespace OutcomeRegion

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma]
         {S : OnticSetup Sigma} (O : OutcomeRegion S)

/-- The pullback event of an outcome region under the deterministic flow `Φ`. -/
noncomputable def preEvent : Set Sigma :=
  S.Φ ⁻¹' O.Ω

lemma measurable_preEvent : MeasurableSet O.preEvent :=
  O.hΩ_meas.preimage S.measurable_Φ

/-- The preparation-side version of the event. -/
noncomputable def prepEvent : Set Sigma :=
  S.Ω0 ∩ O.preEvent

lemma measurable_prepEvent : MeasurableSet O.prepEvent :=
  S.hΩ0_meas.inter O.measurable_preEvent

/-- The outcome weight under the preparation probability measure. -/
noncomputable def weight : ENNReal :=
  ((S.prepMeasure : ProbabilityMeasure Sigma) : Measure Sigma) O.preEvent

/-- The outcome weight as a real number, for use in convergence statements. -/
noncomputable def weightReal : ℝ :=
  ENNReal.toReal O.weight

end OutcomeRegion

end OnticSetup

end LF1
end CSD
