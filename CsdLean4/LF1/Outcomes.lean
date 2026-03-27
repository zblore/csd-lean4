import CsdLean4.LF1.Preparation

open MeasureTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

/-- A single measurable outcome region in the ontic state space. -/
structure OutcomeRegion where
  Ω : Set Σ
  hΩ_meas : MeasurableSet Ω

namespace OutcomeRegion

/-- The pullback event of an outcome region under the deterministic flow `Φ`. -/
def preEvent (O : S.OutcomeRegion) : Set Σ :=
  S.Φ ⁻¹' O.Ω

lemma measurable_preEvent (O : S.OutcomeRegion) :
    MeasurableSet (O.preEvent (S := S)) := by
  exact O.hΩ_meas.preimage S.measurable_Φ

/-- The preparation-side version of the event. -/
def prepEvent (O : S.OutcomeRegion) : Set Σ :=
  S.Ω0 ∩ O.preEvent (S := S)

lemma measurable_prepEvent (O : S.OutcomeRegion) :
    MeasurableSet (O.prepEvent (S := S)) := by
  exact S.hΩ0_meas.inter (O.measurable_preEvent (S := S))

/-- The outcome weight under the preparation probability measure. -/
noncomputable def weight (O : S.OutcomeRegion) : ℝ≥0∞ :=
  ((S.prepMeasure : ProbabilityMeasure Σ) : Measure Σ) (O.preEvent (S := S))

end OutcomeRegion

end OnticSetup

end LF1
end CSD
