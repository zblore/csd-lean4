import CsdLean4.LF1.Setup
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open MeasureTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

/-- The finite measure obtained by restricting `μL` to the preparation region `Ω0`. -/
noncomputable def prepFiniteMeasure : MeasureTheory.FiniteMeasure Sigma :=
  ⟨((S.μL : Measure Sigma).restrict S.Ω0), by
    -- finiteness follows from finiteness of μL
    haveI := S.μL.isFiniteMeasure
    infer_instance
  ⟩

/-- The preparation probability measure, obtained by normalizing the restricted measure. -/
noncomputable def prepMeasure : MeasureTheory.ProbabilityMeasure Sigma :=
  (S.prepFiniteMeasure).normalize

@[simp]
lemma prepFiniteMeasure_toMeasure :
    ((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Sigma) : Measure Sigma) =
      (S.μL : Measure Sigma).restrict S.Ω0 := rfl

/-- The restricted preparation measure is nonzero because `μL Ω0 ≠ 0`. -/
lemma prepFiniteMeasure_ne_zero :
    ((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Sigma) : Measure Sigma) ≠ 0 := by
  rw [prepFiniteMeasure_toMeasure, Ne, Measure.restrict_eq_zero]
  exact S.hΩ0_nonzero

/-- Since the restricted measure is nonzero, normalization gives back the usual
conditional preparation law on `Ω0`. -/
lemma prepMeasure_toMeasure_eq :
    ((S.prepMeasure : MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) =
      (((S.prepFiniteMeasure : MeasureTheory.FiniteMeasure Sigma).normalize :
        MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) := rfl

/--
The preparation probability measure applied to a measurable set equals the
Liouville measure of the intersection with `Ω0`, divided by `µL(Ω0)`.

This is the explicit rewriting formula `µprep(A) = µL(A ∩ Ω0) / µL(Ω0)` that
Section 4.2 of the LF1 paper identifies as infrastructure for the wider Lean branch.
-/
lemma prepMeasure_apply (A : Set Sigma) (hA : MeasurableSet A) :
    ((S.prepMeasure : MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) A =
      (S.μL : Measure Sigma) (A ∩ S.Ω0) / (S.μL : Measure Sigma) S.Ω0 := by
  have hne_fm : S.prepFiniteMeasure ≠ 0 := fun h =>
    S.prepFiniteMeasure_ne_zero (congrArg FiniteMeasure.toMeasure h)
  have hmass_ne : S.prepFiniteMeasure.mass ≠ 0 :=
    S.prepFiniteMeasure.mass_nonzero_iff.mpr hne_fm
  have hmass_eq : (S.prepFiniteMeasure.mass : ENNReal) = (S.μL : Measure Sigma) S.Ω0 := by
    rw [FiniteMeasure.ennreal_mass, prepFiniteMeasure_toMeasure,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [prepMeasure_toMeasure_eq,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero S.prepFiniteMeasure hne_fm,
      Measure.smul_apply, prepFiniteMeasure_toMeasure, Measure.restrict_apply hA,
      ENNReal.smul_def, smul_eq_mul,
      ENNReal.div_eq_inv_mul, ENNReal.coe_inv hmass_ne, hmass_eq]

end OnticSetup

end LF1
end CSD
