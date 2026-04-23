import CsdLean4.LF2.Weights
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes

/-!
# LF2 ↔ LF1 interface

Spec §6. The measure-theoretic identity linking the LF1 ontic weight
`μprep(π⁻¹(O))` to the LF2 projective weight `(π*μprep)(O)`.

This is the cleanest theorem in the LF2 stack: a single application of
`Measure.map_apply`. Its role is structural — it is the formal connection
point for `LF1_main_theorem_ae` to speak about projective outcome weights,
and the hinge by which LF2's measure bridge feeds back into the LF1 frequency
theorem.
-/

open MeasureTheory Set

namespace CSD
namespace LF2

variable {Sigma P G : Type*}
  [MeasurableSpace Sigma] [Nonempty Sigma]
  [MeasurableSpace P]
  [Group G]

/-- **Spec §6.2 — the LF1 ↔ LF2 weight identity.** The ontic mass of the
    pulled-back outcome region under a preparation measure equals the
    projective weight of that region under the pushforward preparation. -/
theorem lf1_weight_eq_projective_weight
    (D : SectorData Sigma P G)
    (μprep : Measure Sigma)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    μprep (D.π ⁻¹' Oep) = projectiveWeight D μprep Oep := by
  rw [projectiveWeight, Measure.map_apply D.measurable_π hOep]

/-- Specialisation of `lf1_weight_eq_projective_weight` to the LF1 conditional
    preparation measure `S.prepMeasure`. This is the exact form consumed by a
    caller who has invoked `LF1_main_theorem_ae` for some
    `T : S.TrialModel Ω` and wants to reinterpret the limiting ontic weight
    as a projective weight. -/
theorem lf1_prepMeasure_weight_eq_projective_weight
    (D : SectorData Sigma P G)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    ((D.toOntic.prepMeasure :
        MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) (D.π ⁻¹' Oep)
      = projectiveWeight D
          ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) Oep :=
  lf1_weight_eq_projective_weight D _ hOep

end LF2
end CSD
