import CsdLean4.FND.UnifiedMeasurement
import CsdLean4.FND.TimeIndexedRecord

/-!
# FND/UnifiedFlowedRecords: time-indexed records ON the unified model (#5)

**Category:** 7-FND (the Choice A ontology layer).

`unified_choiceA_capstone` (`UnifiedMeasurement.lean`) bundles the dynamics + measurement core of the ONE
ontic model `productDynamics H hH p₀` on `Σ = ℂℙ^M × T²`, but its record layer `vnRecordSemanticsProd`
uses a STATIC event (it ignores the recorded time). This module puts the GENUINELY TIME-INDEXED record
semantics `flowedSemantics` onto that same model, with the ISOLATED Hamiltonian flow `Φ = exp(-itH)` as
the evolution — so the model's records become time-physical, with the persistence (probability conserved +
flow-covariant) of `flowedSemantics_persistence` instantiated on it.

The construction is pure assembly: `flowedSemantics` needs a base outcome-region family, its
measurability, and outcome-exclusivity — all three are exactly the fields already proved in
`vnRecordSemanticsProd`. The static `vnRecordSemanticsProd` is recovered as the `t = 0` slice
(`unifiedFlowedSemantics_zero`), so nothing about the working capstone changes; this ADDS the time-indexed
layer.

## What this establishes (all on the unified model `productDynamics H hH p₀`)

* `unifiedFlowedSemantics` — the time-indexed record semantics, `event ⟨c,i,t⟩ = Φ_t⁻¹'(pointer fibre)`;
* `unified_records_persistence` — its Born weight is time-invariant AND the record is flow-covariant under
  the isolated evolution (`flowedSemantics_persistence`);
* `unifiedFlowedSemantics_zero` — at `t = 0` it is the capstone's `vnRecordSemanticsProd` (consistency).

So the "records are time-physical on the unified model" claim, previously supported only by the generic
`flowedSemantics`, is now instantiated on the actual model — the piece L9 needs to list records in the
"proved on the unified model" tier.

References: `FND/UnifiedMeasurement.lean` (`vnRecordSemanticsProd`, `unifiedDeisolationModel`),
`FND/TimeIndexedRecord.lean` (`flowedSemantics`, `flowedSemantics_persistence`).
-/

open MeasureTheory

namespace CSD.FND

open CSD.LF4 CSD.LF5

variable {N M : ℕ} [NeZero N] (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
  (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)

/-- **Time-indexed records on the unified model.** `flowedSemantics` over the isolated flow
`productDynamics H hH p₀`, with base region = the pointer fibre (the same region `vnRecordSemanticsProd`
uses), its measurability and exclusivity reused verbatim. `event ⟨c,i,t⟩ = Φ_t⁻¹'(pointer fibre i)`. -/
noncomputable def unifiedFlowedSemantics :
    RecordSemantics (KSigma (M + 1)) (vnRecordSignature N) :=
  flowedSemantics (productDynamics H hH p₀)
    (fun _ i => (fun x : KSigma (M + 1) => vnPointerOutcome ψ' hψ'0 e x.1) ⁻¹' {some i})
    (fun c i => (vnRecordSemanticsProd e ψ' hψ'0).measurable_event ⟨c, i, 0⟩)
    (fun c a b y => (vnRecordSemanticsProd e ψ' hψ'0).exclusive c a b 0 y)

/-- **Records are time-physical on the unified model.** For every context/outcome, the time-indexed record
probability is conserved by the isolated Hamiltonian evolution AND the record transforms covariantly with
the flow — `flowedSemantics_persistence` instantiated on `productDynamics H hH p₀`. So the unified model's
records are genuine time-physical evidence carried consistently by its own isolated dynamics. -/
theorem unified_records_persistence (c : (vnRecordSignature N).Context)
    (i : (vnRecordSignature N).Outcome c) :
    (∀ t, ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
        ((unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t⟩)
      = ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
        ((fun x : KSigma (M + 1) => vnPointerOutcome ψ' hψ'0 e x.1) ⁻¹' {some i}))
    ∧ (∀ s t, (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t + s⟩
        = (productDynamics H hH p₀).flow s ⁻¹'
          (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t⟩) :=
  flowedSemantics_persistence (productDynamics H hH p₀) _ _ _ c i

/-- **Consistency: the static capstone semantics is the `t = 0` slice.** At `t = 0` the time-indexed
record event coincides with `vnRecordSemanticsProd`'s (since `Φ₀ = id`), so adding the flowed layer does
not disturb `unified_choiceA_capstone`. -/
theorem unifiedFlowedSemantics_zero (c : (vnRecordSignature N).Context)
    (i : (vnRecordSignature N).Outcome c) :
    (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, 0⟩
      = (vnRecordSemanticsProd e ψ' hψ'0).event ⟨c, i, 0⟩ := by
  ext x
  simp only [unifiedFlowedSemantics, flowedSemantics_event, vnRecordSemanticsProd,
    Set.mem_preimage, (productDynamics H hH p₀).flow_zero]

end CSD.FND
