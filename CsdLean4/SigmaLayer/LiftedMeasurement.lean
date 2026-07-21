import CsdLean4.SigmaLayer.MeasurementRecord
import CsdLean4.LF5.PointerOutcome

/-!
# FND/LiftedMeasurement: the concrete de-isolation model from the LF5 pointer machinery

**Category:** 7-SigmaLayer (the Choice A ontological layer).

The concrete `DeisolationModel` for Tranche 2b, on the dilated projective sector `CP^{M}`
(`M + 1 = N * N`). The physical interaction is the LF5 von Neumann de-isolation flow
`measurementFlow` (a genuine measure-preserving unitary map), and the contextual readout is the LF5
per-microstate pointer outcome `vnPointerOutcome`. The outcome regions are the pointer fibres, so the
readout is a genuine function (hence the outcome is unique), the fibres are pairwise disjoint, and the
readout equals `some i` exactly on the `i`-th region. Almost-everywhere totality (the outcome is defined
off an FS-null set, transferred through the measure-preserving interaction) is
`vnDeisolationModel_ae_total`.

Crucially, the model reproduces the Born STATISTICS, not merely a defined outcome: for the dilated
system state `ψ'` and i.i.d. FS-typical trials, the frequency of trials whose de-isolation readout is
pointer `i` converges almost surely to `‖⟨eᵢ, ψ⟩‖²` (`vnDeisolationModel_born_frequency`). This is the
LF5 outcome-frequency capstone `measurement_flow_outcome_frequency` transferred through the
measure-preserving interaction, so the frequency is about the model's OWN outcome (readout after the
interaction), not the raw microstate. `lifted_choiceA_measurement_born_capstone` bundles the full
measurement: measure preservation, unique outcome a.e., record establishment, and Born frequencies.

This is a theorem-backed construction, not an assumed instance: every field is discharged by an LF5
lemma. The isolated dynamics is trivial here (`trivialDynamics`); the physical content is the
de-isolation interaction.
-/

open MeasureTheory Matrix.UnitaryGroup Filter
open scoped LinearAlgebra.Projectivization

namespace CSD.SigmaLayer

open CSD.LF4 CSD.LF5

variable {N M : ℕ} [NeZero N]

/-- The record signature of the von Neumann pointer measurement: a single fixed context, outcome type
`Fin N` (the pointer index). -/
def vnRecordSignature (N : ℕ) : RecordSignature where
  Context := Unit
  Outcome := fun _ => Fin N

/-- The record semantics: the event of pointer outcome `i` is the pointer fibre
`vnPointerOutcome ⁻¹' {some i}` on `CP^{M}`. -/
noncomputable def vnRecordSemantics (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0) :
    RecordSemantics (CPN (M + 1)) (vnRecordSignature N) where
  event := fun r => vnPointerOutcome ψ' hψ'0 e ⁻¹' {some r.outcome}
  measurable_event := fun r =>
    (vnPointerOutcome_preimage_some ψ' hψ'0 e r.outcome).symm ▸
      MeasurableSet.iUnion (fun n => bornRegion_measurable_uncond ψ' hψ'0 (e (n, r.outcome)))
  exclusive := fun _ a b _ x ha hb => by
    simp only [Set.mem_preimage] at ha hb
    exact Option.some.inj (ha ▸ hb)

/-- **The concrete de-isolation model.** Interaction = the LF5 measurement flow (measure-preserving
unitary); readout = the LF5 pointer outcome; outcome regions = the pointer fibres. Every field is
discharged by an LF5 lemma. Preparation type is `Unit` (the reference state `ψ'` is fixed). -/
noncomputable def vnDeisolationModel (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0) :
    DeisolationModel (trivialDynamics ⟨fubiniStudyMeasure p₀, inferInstance⟩)
      (vnRecordSignature N) (vnRecordSemantics e ψ' hψ'0) Unit where
  interaction := fun _ _ => measurementFlow N e
  measurable_interaction := fun _ _ => measurementFlow_measurable e
  interaction_preserves := fun _ _ => measurementFlow_measurePreserving e p₀
  outcomeRegion := fun _ _ i => vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}
  measurable_outcomeRegion := fun _ _ i =>
    (vnPointerOutcome_preimage_some ψ' hψ'0 e i).symm ▸
      MeasurableSet.iUnion (fun n => bornRegion_measurable_uncond ψ' hψ'0 (e (n, i)))
  pairwise_disjoint := fun _ _ i _ j _ hij => by
    simp only [Function.onFun, Set.disjoint_left, Set.mem_preimage]
    exact fun x hi hj => hij (Option.some.inj (hi ▸ hj))
  readout := fun _ _ x => vnPointerOutcome ψ' hψ'0 e x
  readout_eq_some_iff := fun _ _ _ _ => Iff.rfl

/-- **The readout records the established outcome (B5 proved for the model).** If the pointer readout
after the interaction is `some i`, the post-interaction state lies in the record event for `i`. -/
theorem vnDeisolationModel_records (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0) :
    DeisolationModel.RecordsEstablishedOutcome (vnDeisolationModel p₀ e ψ' hψ'0) :=
  fun _ _ _ _ _ h => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr h)

/-- **Almost-everywhere unique outcome (T6 for the model).** For almost every initial ontic state
(Fubini-Study measure), the pointer readout after the de-isolation interaction is defined: the outcome
is established a.e. Uniqueness is automatic (the readout is a function; its fibres are pairwise
disjoint). Transfers `bornOutcome_ae_isSome` through the measure-preserving interaction. -/
theorem vnDeisolationModel_ae_total (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0) (hψ' : ‖ψ'‖ = 1) :
    (vnDeisolationModel p₀ e ψ' hψ'0).AETotalReadout () () 0 (fubiniStudyMeasure p₀) := by
  have hmp := measurementFlow_measurePreserving (N := N) e p₀
  have hQ : MeasurableSet {p : CPN (M + 1) | (bornOutcome ψ' hψ'0 p).isSome} := by
    have : {p : CPN (M + 1) | (bornOutcome ψ' hψ'0 p).isSome}
        = ⋃ i, bornRegion ψ' hψ'0 i := by
      ext p
      simp only [Set.mem_ofPred_eq, Option.isSome_iff_exists, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i, (bornOutcome_eq_some_iff ψ' hψ'0 p i).mp hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i, (bornOutcome_eq_some_iff ψ' hψ'0 p i).mpr hi⟩
    rw [this]; exact MeasurableSet.iUnion (bornRegion_measurable_uncond ψ' hψ'0)
  have hbase : ∀ᵐ p ∂ fubiniStudyMeasure p₀, (bornOutcome ψ' hψ'0 p).isSome :=
    bornOutcome_ae_isSome p₀ ψ' hψ'0 hψ'
  have htrans : ∀ᵐ x ∂ fubiniStudyMeasure p₀,
      (bornOutcome ψ' hψ'0 (measurementFlow N e x)).isSome := by
    rw [← hmp.map_eq] at hbase
    exact (ae_map_iff hmp.measurable.aemeasurable hQ).mp hbase
  filter_upwards [htrans] with x hx
  show (vnPointerOutcome ψ' hψ'0 e (measurementFlow N e x)).isSome
  rcases hb : bornOutcome ψ' hψ'0 (measurementFlow N e x) with _ | c
  · rw [hb] at hx; simp only [Option.isSome_none, Bool.false_eq_true] at hx
  · simp only [vnPointerOutcome, hb, Option.map_some, Option.isSome_some]

/-- **The lifted Choice A measurement capstone.** For the concrete de-isolation model on `CP^{M}`
(`M + 1 = N * N`), with the LF5 measurement flow as the physical interaction and the LF5 pointer outcome
as the contextual readout, the following hold with no open hypotheses beyond a unit reference state:

* the interaction is measure-preserving (`DeisolationModel.interaction_preserves`);
* the outcome regions (pointer fibres) are pairwise disjoint, so the recorded outcome is unique;
* the readout records the established outcome (bridge B5);
* the outcome is established for almost every initial ontic state (target T6).

This is the contextual pointer readout and almost-everywhere unique outcome that the product forward
capstone `product_choiceA_forward_capstone` explicitly did not claim: the measurement content, delivered
from a genuine de-isolation interaction rather than an assumed instance. -/
theorem lifted_choiceA_measurement_capstone (p₀ : CPN (M + 1))
    (e : Fin N × Fin N ≃ Fin (M + 1)) (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'0 : ψ' ≠ 0) (hψ' : ‖ψ'‖ = 1) :
    (∀ t, MeasurePreserving ((vnDeisolationModel p₀ e ψ' hψ'0).interaction t ())
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    ∧ Set.PairwiseDisjoint Set.univ ((vnDeisolationModel p₀ e ψ' hψ'0).outcomeRegion () ())
    ∧ DeisolationModel.RecordsEstablishedOutcome (vnDeisolationModel p₀ e ψ' hψ'0)
    ∧ (vnDeisolationModel p₀ e ψ' hψ'0).AETotalReadout () () 0 (fubiniStudyMeasure p₀) :=
  ⟨fun t => (vnDeisolationModel p₀ e ψ' hψ'0).interaction_preserves t (),
    (vnDeisolationModel p₀ e ψ' hψ'0).pairwise_disjoint () (),
    vnDeisolationModel_records p₀ e ψ' hψ'0,
    vnDeisolationModel_ae_total p₀ e ψ' hψ'0 hψ'⟩

/-- **The model reproduces the Born statistics (the measurement content).** For the dilated system state
`ψ'` (the von Neumann dilation of a unit system state `ψ`) and i.i.d. FS-typical trials, the frequency
of trials whose de-isolation readout is pointer `i` converges almost surely to the Born weight
`‖⟨eᵢ, ψ⟩‖²`. The event `(interaction ∘ trial)⁻¹' (readout⁻¹' {some i})` is exactly "the model reads
pointer `i` on this trial", the readout applied AFTER the model's interaction.

This is the LF5 outcome-frequency capstone `measurement_flow_outcome_frequency` transferred through the
measure-preserving interaction: the composed trial process `measurementFlow ∘ fsTrial` still samples the
Fubini-Study law (measure preservation), and its per-trial indicators are still independent (a fixed
deterministic map of independent trials), so the Born weights are unchanged. Hence the frequency is a
genuine statistic of the model's own outcome, not of the raw microstate. -/
theorem vnDeisolationModel_born_frequency (hN : 1 < N) (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0) (p₀ : CPN (M + 1)) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((measurementFlow N e ∘ fsTrial (M + 1) k) ⁻¹'
                  (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  have hlaw : ∀ k, Measure.map (measurementFlow N e ∘ fsTrial (M + 1) k) (fsTrialMeasure p₀)
      = fubiniStudyMeasure p₀ := fun k => by
    rw [← Measure.map_map (measurementFlow_measurable e) (fsTrial_measurable k),
      fsTrial_law p₀ k, (measurementFlow_measurePreserving e p₀).map_eq]
  exact measurement_flow_outcome_frequency hN e ψ hψ ψ' hψ'eq hψ'0 p₀
    (fun k => measurementFlow N e ∘ fsTrial (M + 1) k)
    (fun k => (measurementFlow_measurable e).comp (fsTrial_measurable k)) hlaw
    (fsTrial_pairwise_indepFun_indicator p₀
      (fun j => measurementFlow N e ⁻¹' bornRegion ψ' hψ'0 j)
      (fun j => measurementFlow_measurable e (bornRegion_measurable_uncond ψ' hψ'0 j)))

/-- **The full lifted Choice A measurement capstone (with Born statistics).** For the concrete
de-isolation model on the dilated sector, with the system state `ψ'` the von Neumann dilation of a unit
state `ψ`, the following hold with no open hypotheses beyond the dilation data:

* the interaction is measure-preserving;
* the outcome regions (pointer fibres) are pairwise disjoint, so the recorded outcome is unique;
* the readout records the established outcome (bridge B5);
* the outcome is established for almost every initial ontic state (target T6);
* the frequency of pointer-`i` readouts converges almost surely to the Born weight `‖⟨eᵢ, ψ⟩‖²`.

This is the genuine measurement: a defined, unique outcome a.e. AND the Born statistics, delivered from a
de-isolation interaction rather than an assumed instance. -/
theorem lifted_choiceA_measurement_born_capstone (hN : 1 < N)
    (e : Fin N × Fin N ≃ Fin (M + 1)) (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0) (hψ' : ‖ψ'‖ = 1) (p₀ : CPN (M + 1)) :
    (∀ t, MeasurePreserving ((vnDeisolationModel p₀ e ψ' hψ'0).interaction t ())
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    ∧ Set.PairwiseDisjoint Set.univ ((vnDeisolationModel p₀ e ψ' hψ'0).outcomeRegion () ())
    ∧ DeisolationModel.RecordsEstablishedOutcome (vnDeisolationModel p₀ e ψ' hψ'0)
    ∧ (vnDeisolationModel p₀ e ψ' hψ'0).AETotalReadout () () 0 (fubiniStudyMeasure p₀)
    ∧ (∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin N,
        Tendsto
          (fun m : ℕ =>
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((measurementFlow N e ∘ fsTrial (M + 1) k) ⁻¹'
                    (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
          atTop
          (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2))) :=
  ⟨(lifted_choiceA_measurement_capstone p₀ e ψ' hψ'0 hψ').1,
    (lifted_choiceA_measurement_capstone p₀ e ψ' hψ'0 hψ').2.1,
    (lifted_choiceA_measurement_capstone p₀ e ψ' hψ'0 hψ').2.2.1,
    (lifted_choiceA_measurement_capstone p₀ e ψ' hψ'0 hψ').2.2.2,
    vnDeisolationModel_born_frequency hN e ψ hψ ψ' hψ'eq hψ'0 p₀⟩

end CSD.SigmaLayer
