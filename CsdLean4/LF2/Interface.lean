import CsdLean4.LF2.Weights
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.MainTheorem

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

open MeasureTheory Set Filter

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

/-- **Combined LF1 + LF2 main theorem.**  Under the LF1 repeated-trial model
    and an LF2 sector structure with projection `π`, if an LF1 outcome
    region's pre-event coincides with the `π`-preimage of a projective
    outcome region `Oep`, then the empirical frequency converges almost
    surely to the (real-valued) **projective weight** of `Oep` under the
    pushforward of the preparation measure.

    This is the theorem-level consumption of LF1 by LF2: it shows that the
    LF1 limit is not merely an ontic volume fraction but can be reinterpreted
    natively in the projective measurable space that LF2 introduces.  No new
    mathematical content beyond LF1 + the LF2 interface identity — the point
    is the combined statement.

    A full Born-form conclusion (`‖⟨ψ, φ⟩‖²`) would require an additional
    spec-layer correspondence between measure-theoretic projective
    preparations and Hilbert-space unit vectors, which LF2 does not
    formalise.  See spec §6.4 and §8.5. -/
theorem LF1_main_theorem_projective
    (D : SectorData Sigma P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (O : D.toOntic.OutcomeRegion)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g (T.trialMeasure))
          (fun n => T.indicatorRV (S := D.toOntic) O n)))
    {Oep : Set P} (hOep : MeasurableSet Oep)
    (hCorresp : O.preEvent = D.π ⁻¹' Oep) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := D.toOntic) O n ω)
        atTop
        (nhds
          (ENNReal.toReal
            (projectiveWeight D
              ((D.toOntic.prepMeasure :
                  MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma)
              Oep))) := by
  have hW :
      O.weightReal =
        ENNReal.toReal
          (projectiveWeight D
            ((D.toOntic.prepMeasure :
                MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma)
            Oep) := by
    unfold CSD.LF1.OnticSetup.OutcomeRegion.weightReal
    congr 1
    show ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma) O.preEvent
      = projectiveWeight D
          ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure Sigma) : Measure Sigma)
          Oep
    rw [hCorresp]
    exact lf1_weight_eq_projective_weight D _ hOep
  rw [← hW]
  exact D.toOntic.LF1_main_theorem_ae T O hindep

end LF2
end CSD
