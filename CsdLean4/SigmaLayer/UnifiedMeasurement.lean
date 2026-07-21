import CsdLean4.SigmaLayer.MeasureBridge
import CsdLean4.SigmaLayer.DynamicsBridge
import CsdLean4.SigmaLayer.LiftedMeasurement

/-!
# FND/UnifiedMeasurement: dynamics and measurement on ONE many-to-one ontic model (FND-T5)

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

The primary structural closure item. The forward capstone (`product_projectiveSector_forward_capstone`) lives on
`Σ = ℂℙ^{M} × T²` with the `exp(-itH)` Hamiltonian flow; the measurement capstone
(`lifted_projectiveSector_measurement_born_capstone`) lived on the dilated `ℂℙ^{M}` with `trivialDynamics`. They
used DIFFERENT ontic models. This module puts BOTH on the SAME `(Σ, μL, Φ, π)`:

* `Σ = KSigma (M+1) = ℂℙ^{M} × T²`, `μL = kMuL = μFS ⊗ vol`, `π = Prod.fst` (`productSector`);
* the ISOLATED dynamics is the genuine Hamiltonian flow `productDynamics H hH p₀`
  (`Φ_t(p,θ) = (exp(-itH)•p, θ)`), NOT `trivialDynamics`;
* the DE-ISOLATION measurement is a `DeisolationModel` over that same `productDynamics` whose interaction
  is the LF5 von Neumann flow lifted to the fibre, `Φ_meas(p,θ) = (measurementFlow p, θ)`, with the
  pointer readout `vnPointerOutcome ∘ π`.

`unified_projectiveSector_capstone` then delivers, on the ONE model `productDynamics H hH p₀`:

1. the isolated flow is measure-preserving (`flow_preserves`);
2. it projects through `π = Prod.fst` to `exp(-itH) • ·` — the Schrödinger pillar (`productDynamicsBridge`);
3. `π_* μL = μFS` — the Fubini-Study bridge (B1);
4. the de-isolation interaction (on the SAME Σ, μL) is measure-preserving;
5. the contextual pointer readout is defined almost everywhere (target T6, lifted through the fibre);
6. the readout records the established outcome (bridge B5).

So one `(Σ, μL, Φ, π)` carries isolated Hamiltonian evolution AND de-isolating measurement AND records
AND the Fubini-Study/Born content — removing the forward-vs-measurement model split. The Born outcome
FREQUENCIES are the base-space statement `vnDeisolationModel_born_frequency` (the readout factors through
`π`, so its i.i.d. law lives on the base `ℂℙ^{M}`). Follow-on residue (see `specs/future-work.md`
FND-T5): physical record persistence, nonzero post-outcome preparation, the conditional→Lüders link.
-/

open MeasureTheory Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD.SigmaLayer

open CSD.LF4 CSD.LF5

variable {N M : ℕ} [NeZero N] (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
  (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)

/-- The record semantics on the product ontic space: the event of pointer outcome `i` is the fibred
pointer preimage `{(p,θ) | vnPointerOutcome p = some i}` (the base pointer fibre pulled back through
`π = Prod.fst`). -/
noncomputable def vnRecordSemanticsProd :
    RecordSemantics (KSigma (M + 1)) (vnRecordSignature N) where
  event := fun r => (fun x : KSigma (M + 1) => vnPointerOutcome ψ' hψ'0 e x.1) ⁻¹' {some r.outcome}
  measurable_event := fun r =>
    measurable_fst ((vnPointerOutcome_preimage_some ψ' hψ'0 e r.outcome).symm ▸
      MeasurableSet.iUnion (fun n => bornRegion_measurable_uncond ψ' hψ'0 (e (n, r.outcome))))
  exclusive := fun _ a b _ x ha hb => by
    simp only [Set.mem_preimage] at ha hb
    exact Option.some.inj (ha ▸ hb)

/-- **The unified de-isolation model.** A `DeisolationModel` over the NONTRIVIAL isolated dynamics
`productDynamics H hH p₀` (the `exp(-itH)` Hamiltonian flow), on the same `Σ = ℂℙ^{M} × T²`. The
interaction is the LF5 measurement flow on the base fibre `(p,θ) ↦ (measurementFlow p, θ)`; the readout is
the base pointer outcome; the outcome regions are the fibred pointer fibres. Every field is discharged by
an LF4/LF5 lemma. -/
noncomputable def unifiedDeisolationModel :
    DeisolationModel (productDynamics H hH p₀) (vnRecordSignature N)
      (vnRecordSemanticsProd e ψ' hψ'0) Unit where
  interaction := fun _ _ x => (measurementFlow N e x.1, x.2)
  measurable_interaction := fun _ _ =>
    Measurable.prodMk ((measurementFlow_measurable e).comp measurable_fst) measurable_snd
  interaction_preserves := fun _ _ =>
    (measurementFlow_measurePreserving e p₀).prod (MeasurePreserving.id (volume : Measure KTorus))
  outcomeRegion := fun _ _ i => (fun x : KSigma (M + 1) => vnPointerOutcome ψ' hψ'0 e x.1) ⁻¹' {some i}
  measurable_outcomeRegion := fun _ _ i =>
    measurable_fst ((vnPointerOutcome_preimage_some ψ' hψ'0 e i).symm ▸
      MeasurableSet.iUnion (fun n => bornRegion_measurable_uncond ψ' hψ'0 (e (n, i))))
  pairwise_disjoint := fun _ _ i _ j _ hij => by
    simp only [Function.onFun, Set.disjoint_left, Set.mem_preimage]
    exact fun x hi hj => hij (Option.some.inj (hi ▸ hj))
  readout := fun _ _ x => vnPointerOutcome ψ' hψ'0 e x.1
  readout_eq_some_iff := fun _ _ _ _ => Iff.rfl

/-- **The readout records the established outcome (B5) on the unified model.** -/
theorem unifiedDeisolationModel_records :
    DeisolationModel.RecordsEstablishedOutcome (unifiedDeisolationModel H hH p₀ e ψ' hψ'0) :=
  fun _ _ _ _ _ h => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr h)

/-- **Almost-everywhere defined readout (T6) on the unified model.** For almost every ontic state
`(p,θ)` under the product Liouville measure `μFS ⊗ vol`, the pointer readout after the de-isolation
interaction is defined. The predicate depends only on the base `p`, so it lifts the base statement
`vnDeisolationModel_ae_total` through `Prod.fst` (whose pushforward of `kMuL` is `μFS`). -/
theorem unifiedDeisolationModel_ae_total (hψ' : ‖ψ'‖ = 1) :
    (unifiedDeisolationModel H hH p₀ e ψ' hψ'0).AETotalReadout () () 0 (kMuL p₀) := by
  have hbase : ∀ᵐ p ∂ fubiniStudyMeasure p₀,
      (vnPointerOutcome ψ' hψ'0 e (measurementFlow N e p)).isSome :=
    vnDeisolationModel_ae_total p₀ e ψ' hψ'0 hψ'
  have hQ : MeasurableSet
      {p : CPN (M + 1) | (vnPointerOutcome ψ' hψ'0 e (measurementFlow N e p)).isSome} := by
    have hset : {p : CPN (M + 1) | (vnPointerOutcome ψ' hψ'0 e (measurementFlow N e p)).isSome}
        = ⋃ i : Fin N, (fun p => vnPointerOutcome ψ' hψ'0 e (measurementFlow N e p)) ⁻¹' {some i} := by
      ext p
      simp only [Set.mem_ofPred_eq, Option.isSome_iff_exists, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [hset]
    refine MeasurableSet.iUnion (fun i => ?_)
    have hpre : (fun p : CPN (M + 1) => vnPointerOutcome ψ' hψ'0 e (measurementFlow N e p)) ⁻¹' {some i}
        = measurementFlow N e ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}) := rfl
    rw [hpre]
    exact measurementFlow_measurable e ((vnPointerOutcome_preimage_some ψ' hψ'0 e i).symm ▸
      MeasurableSet.iUnion (fun n => bornRegion_measurable_uncond ψ' hψ'0 (e (n, i))))
  have hmap : Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀ := by
    rw [kMuL]; exact Measure.fst_prod
  rw [← hmap] at hbase
  exact (ae_map_iff measurable_fst.aemeasurable hQ).mp hbase

/-- **FND-T5: dynamics and measurement on one many-to-one ontic model.** For `Σ = ℂℙ^{M} × T²`, the
Liouville measure `μFS ⊗ vol` and `π = Prod.fst`, the SAME `productDynamics H hH p₀` carries:

1. a measure-preserving isolated Hamiltonian flow;
2. projectable through `π` to the Schrödinger flow `exp(-itH) • ·`;
3. `π_* μL = μFS` (Fubini-Study bridge);
4. a measure-preserving de-isolation measurement interaction (on the same `Σ`, `μL`);
5. an almost-everywhere defined contextual pointer readout;
6. record establishment.

One ontic model behind isolated evolution, measurement, records and the Born/Fubini-Study content. -/
theorem unified_projectiveSector_capstone (hψ' : ‖ψ'‖ = 1) :
    (∀ t, MeasurePreserving ((productDynamics H hH p₀).flow t) (kMuL p₀) (kMuL p₀))
    ∧ (∀ t x, (productSector H hH p₀).pi ((productDynamics H hH p₀).flow t x)
        = productProjectedFlow H hH t ((productSector H hH p₀).pi x))
    ∧ HasFubiniStudyPushforward (productSector H hH p₀) p₀
    ∧ (∀ t c, MeasurePreserving ((unifiedDeisolationModel H hH p₀ e ψ' hψ'0).interaction t c)
        (kMuL p₀) (kMuL p₀))
    ∧ (unifiedDeisolationModel H hH p₀ e ψ' hψ'0).AETotalReadout () () 0 (kMuL p₀)
    ∧ DeisolationModel.RecordsEstablishedOutcome (unifiedDeisolationModel H hH p₀ e ψ' hψ'0) :=
  ⟨(productDynamics H hH p₀).flow_preserves,
    (productDynamicsBridge H hH p₀).projectable,
    productSector_hasFubiniStudyPushforward H hH p₀,
    fun _ _ =>
      (measurementFlow_measurePreserving e p₀).prod (MeasurePreserving.id (volume : Measure KTorus)),
    unifiedDeisolationModel_ae_total H hH p₀ e ψ' hψ'0 hψ',
    unifiedDeisolationModel_records H hH p₀ e ψ' hψ'0⟩

end CSD.SigmaLayer
