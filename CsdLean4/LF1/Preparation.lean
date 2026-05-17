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

/-- The mass of `prepFiniteMeasure`, coerced to `ENNReal`, equals `µL(Ω0)`.
Isolated so a Mathlib refactor of `FiniteMeasure.ennreal_mass` or
`Measure.restrict_apply` lands in one place. -/
lemma prepFiniteMeasure_mass_eq :
    (S.prepFiniteMeasure.mass : ENNReal) = (S.μL : Measure Sigma) S.Ω0 := by
  rw [FiniteMeasure.ennreal_mass, prepFiniteMeasure_toMeasure,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- `prepFiniteMeasure` is nonzero as a finite measure, and its mass is nonzero
as an `ℝ≥0`. Both facts are needed by `prepMeasure_apply`; bundling them isolates
the dependency on `FiniteMeasure.mass_nonzero_iff`. -/
lemma prepFiniteMeasure_ne_zero_pair :
    S.prepFiniteMeasure ≠ 0 ∧ S.prepFiniteMeasure.mass ≠ 0 := by
  refine ⟨?_, ?_⟩
  · exact fun h => S.prepFiniteMeasure_ne_zero (congrArg FiniteMeasure.toMeasure h)
  · exact S.prepFiniteMeasure.mass_nonzero_iff.mpr
      (fun h => S.prepFiniteMeasure_ne_zero (congrArg FiniteMeasure.toMeasure h))

/--
The preparation probability measure applied to a measurable set equals the
Liouville measure of the intersection with `Ω0`, divided by `µL(Ω0)`.

This is the explicit rewriting formula `µprep(A) = µL(A ∩ Ω0) / µL(Ω0)` that
Section 4.2 of the LF1 paper identifies as infrastructure for the wider Lean branch.

The proof routes through three named intermediate facts
(`prepMeasure_toMeasure_eq`, `prepFiniteMeasure_toMeasure`,
`prepFiniteMeasure_mass_eq`) and three Mathlib lemmas
(`toMeasure_normalize_eq_of_nonzero`, `Measure.smul_apply`,
`Measure.restrict_apply`). A future Mathlib rename of any of the latter is
localised to this one proof.
-/
lemma prepMeasure_apply (A : Set Sigma) (hA : MeasurableSet A) :
    ((S.prepMeasure : MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) A =
      (S.μL : Measure Sigma) (A ∩ S.Ω0) / (S.μL : Measure Sigma) S.Ω0 := by
  obtain ⟨hne_fm, hmass_ne⟩ := S.prepFiniteMeasure_ne_zero_pair
  rw [prepMeasure_toMeasure_eq,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero S.prepFiniteMeasure hne_fm,
      Measure.smul_apply, prepFiniteMeasure_toMeasure, Measure.restrict_apply hA,
      ENNReal.smul_def, smul_eq_mul,
      ENNReal.div_eq_inv_mul, ENNReal.coe_inv hmass_ne, S.prepFiniteMeasure_mass_eq]

end OnticSetup

end LF1
end CSD
