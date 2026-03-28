import CsdLean4.LF1.Setup
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open MeasureTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] [Nonempty Σ] (S : OnticSetup Σ)

/-- The finite measure obtained by restricting `μL` to the preparation region `Ω0`. -/
def prepFiniteMeasure : MeasureTheory.FiniteMeasure Σ :=
  ⟨((S.μL : Measure Σ).restrict S.Ω0), by
    -- finiteness follows from finiteness of μL
    haveI := S.μL.isFiniteMeasure
    infer_instance
  ⟩

/-- The preparation probability measure, obtained by normalizing the restricted measure. -/
noncomputable def prepMeasure : MeasureTheory.ProbabilityMeasure Σ :=
  (S.prepFiniteMeasure).normalize

@[simp]
lemma prepFiniteMeasure_toMeasure :
    ((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Σ) : Measure Σ) =
      (S.μL : Measure Σ).restrict S.Ω0 := rfl

/-- The restricted preparation measure is nonzero because `μL Ω0 ≠ 0`. -/
lemma prepFiniteMeasure_ne_zero :
    ((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Σ) : Measure Σ) ≠ 0 := by
  intro hzero
  have hΩ0zero :
      ((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Σ) : Measure Σ) S.Ω0 = 0 := by
    simpa [hzero]
  have hrestrict :
      ((S.μL : Measure Σ).restrict S.Ω0) S.Ω0 = (S.μL : Measure Σ) S.Ω0 := by
    simpa [Measure.restrict_apply, S.hΩ0_meas, inter_eq_left]
  have : (S.μL : Measure Σ) S.Ω0 = 0 := by
    simpa [S.prepFiniteMeasure_toMeasure, hrestrict] using hΩ0zero
  exact S.hΩ0_nonzero this

/-- Since the restricted measure is nonzero, normalization gives back the usual
conditional preparation law on `Ω0`. -/
lemma prepMeasure_toMeasure_eq :
    ((S.prepMeasure : MeasureTheory.ProbabilityMeasure Σ) : Measure Σ) =
      (((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Σ).normalize :
        MeasureTheory.ProbabilityMeasure Σ) : Measure Σ) := rfl

end OnticSetup

end LF1
end CSD
