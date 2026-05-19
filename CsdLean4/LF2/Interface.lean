import CsdLean4.LF2.Weights
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.MainTheorem

/-!
# LF2 ↔ LF1 interface

**Category:** 3-Local (LF1 ↔ LF2 weight identity plus combined `LF1_main_theorem_projective` headline theorem).

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

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **Spec §6.2 — the LF1 ↔ LF2 weight identity.** The ontic mass of the
    pulled-back outcome region under a preparation measure equals the
    projective weight of that region under the pushforward preparation. -/
theorem lf1_weight_eq_projective_weight
    (D : SectorData SigmaSpace P G)
    (μprep : Measure SigmaSpace)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    μprep (D.π ⁻¹' Oep) = projectiveWeight D μprep Oep := by
  rw [projectiveWeight, Measure.map_apply D.measurable_π hOep]

/-- Specialisation of `lf1_weight_eq_projective_weight` to the LF1 conditional
    preparation measure `S.prepMeasure`. This is the exact form consumed by a
    caller who has invoked `LF1_main_theorem_ae` for some
    `T : S.TrialModel Ω` and wants to reinterpret the limiting ontic weight
    as a projective weight. -/
theorem lf1_prepMeasure_weight_eq_projective_weight
    (D : SectorData SigmaSpace P G)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    ((D.toOntic.prepMeasure :
        MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) (D.π ⁻¹' Oep)
      = projectiveWeight D
          ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) Oep :=
  lf1_weight_eq_projective_weight D _ hOep

/-! ### Projective-first outcome constructor

`SectorData.outcomeOfProjective` builds an LF1 ontic `OutcomeRegion`
from a measurable projective region `Oep ⊆ P` by taking the `π`-preimage:
`Ω := D.π ⁻¹' Oep`. The constructor itself requires only measurability
of `Oep`.

The **flow-projection compatibility** hypothesis
`∀ x, D.π (D.toOntic.Φ x) = D.π x` (CSD's constraint-surface
preservation reading — the ontic flow preserves projective rays) is
**not** consumed by the constructor itself. It is consumed by the
companion lemma `outcomeOfProjective_preEvent` to identify
`preEvent = Ω` (i.e. to fold the LF1 one-step-ahead pullback into the
plain preimage), which is what `LF1_main_theorem_projective` and the
LF3 chain capstones need.

Architectural rationale: the Φ-π compatibility hypothesis is supplied
as a *lemma* argument rather than as a field on `SectorData` —
adding a field would commit all `SectorData` instances to the
constraint-surface reading, which is LF4 instantiation work. Keeping
it on the per-lemma side lets the projective-first outcome family be
built at the LF3 chain capstone with a single CSD-foundational
hypothesis. -/

/-- **Projective-first outcome constructor.** Given a measurable
    projective region `Oep ⊆ P`, returns the ontic `OutcomeRegion`
    with `Ω := D.π ⁻¹' Oep`. The constructor requires only `hOep`;
    flow-projection compatibility is consumed by the companion lemma
    `outcomeOfProjective_preEvent`, which identifies `preEvent = Ω`.
    The companion lemma `outcomeOfProjective_weight_eq_projectiveWeight`
    gives the projective-side reformulation of the LF1 outcome weight. -/
noncomputable def SectorData.outcomeOfProjective
    (D : SectorData SigmaSpace P G)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    D.toOntic.OutcomeRegion where
  Ω := D.π ⁻¹' Oep
  hΩ_meas := D.measurable_π hOep

/-- Unfolding lemma: the ontic outcome region's underlying set is the
    projection preimage. -/
@[simp] lemma SectorData.outcomeOfProjective_Ω
    (D : SectorData SigmaSpace P G)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    (D.outcomeOfProjective hOep).Ω = D.π ⁻¹' Oep := rfl

/-- **Pre-event of `outcomeOfProjective` equals `π⁻¹(Oep)`** under the
    flow-projection compatibility hypothesis. This is the lemma that
    discharges the `hCorresp` argument of `LF1_main_theorem_projective`
    for the constructor-built outcome region. -/
lemma SectorData.outcomeOfProjective_preEvent
    (D : SectorData SigmaSpace P G)
    (h_flow_π : ∀ x, D.π (D.toOntic.Φ x) = D.π x)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    (D.outcomeOfProjective hOep).preEvent = D.π ⁻¹' Oep := by
  ext x
  show D.toOntic.Φ x ∈ D.π ⁻¹' Oep ↔ x ∈ D.π ⁻¹' Oep
  rw [Set.mem_preimage, Set.mem_preimage, h_flow_π]

/-- **Weight of `outcomeOfProjective` equals the projective weight of
    `Oep`** under the flow-projection compatibility hypothesis. Direct
    consequence of `outcomeOfProjective_preEvent` and
    `lf1_weight_eq_projective_weight`. -/
lemma SectorData.outcomeOfProjective_weight_eq_projectiveWeight
    (D : SectorData SigmaSpace P G)
    (h_flow_π : ∀ x, D.π (D.toOntic.Φ x) = D.π x)
    (μprep : Measure SigmaSpace)
    {Oep : Set P} (hOep : MeasurableSet Oep) :
    μprep ((D.outcomeOfProjective hOep).preEvent)
      = projectiveWeight D μprep Oep := by
  rw [D.outcomeOfProjective_preEvent h_flow_π hOep]
  exact lf1_weight_eq_projective_weight D μprep hOep

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
    (D : SectorData SigmaSpace P G)
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
                  MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
              Oep))) := by
  have hW :
      O.weightReal =
        ENNReal.toReal
          (projectiveWeight D
            ((D.toOntic.prepMeasure :
                MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
            Oep) := by
    unfold CSD.LF1.OnticSetup.OutcomeRegion.weightReal
    congr 1
    show ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) O.preEvent
      = projectiveWeight D
          ((D.toOntic.prepMeasure :
              MeasureTheory.ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
          Oep
    rw [hCorresp]
    exact lf1_weight_eq_projective_weight D _ hOep
  rw [← hW]
  exact D.toOntic.LF1_main_theorem_ae T O hindep

end LF2
end CSD
