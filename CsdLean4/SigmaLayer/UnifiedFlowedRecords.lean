import CsdLean4.SigmaLayer.UnifiedMeasurement
import CsdLean4.SigmaLayer.TimeIndexedRecord
import CsdLean4.LF4.ManyToOnePillars

/-!
# SigmaLayer/UnifiedFlowedRecords: time-indexed records ON the unified model (#5)

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

`unified_projectiveSector_capstone` (`UnifiedMeasurement.lean`) bundles the dynamics + measurement core of the ONE
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

References: `SigmaLayer/UnifiedMeasurement.lean` (`vnRecordSemanticsProd`, `unifiedDeisolationModel`),
`SigmaLayer/TimeIndexedRecord.lean` (`flowedSemantics`, `flowedSemantics_persistence`).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace CSD.SigmaLayer

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
not disturb `unified_projectiveSector_capstone`. -/
theorem unifiedFlowedSemantics_zero (c : (vnRecordSignature N).Context)
    (i : (vnRecordSignature N).Outcome c) :
    (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, 0⟩
      = (vnRecordSemanticsProd e ψ' hψ'0).event ⟨c, i, 0⟩ := by
  ext x
  simp only [unifiedFlowedSemantics, flowedSemantics, vnRecordSemanticsProd,
    Set.mem_preimage, (productDynamics H hH p₀).flow_zero]

/-! ### #2: Born-frequency ON the unified model

`manyToOneSetup_born_frequency` (the independent-trial LLN Born frequency) transfers directly to the
unified model, because `(productDynamics H hH p₀).muL = (manyToOneSetup (schrodingerUnitary hH) p₀)
.liouvilleMeasure` (by `productDynamics_muL_eq`, itself `rfl`) and `(productSector H hH p₀).pi` is that
setup's `π`. So the Born frequencies are stated on the SAME model that carries the dynamics, measurement,
and records — no separate base object. -/

/-- **Born frequency on the unified model.** For i.i.d. trials `X` whose law is the unified model's own
Liouville measure `(productDynamics H hH p₀).muL`, the frequency of trials landing in the `i`-th outcome
region `π⁻¹(bornRegion i)` converges a.s. to the Born weight `‖⟨eᵢ,ψ⟩‖²`. A direct transfer of
`manyToOneSetup_born_frequency` through the definitional identity `productDynamics.muL = liouvilleMeasure`
— so Born frequencies are now stated on the unified model itself. -/
theorem unified_born_frequency {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (X : ℕ → Ω → KSigma (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr
      = ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1))))
    (hindep : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator
          ((X n) ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i)) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  manyToOneSetup_born_frequency (schrodingerUnitary hH) p₀ ψ hψ0 hψ X hX hlaw hindep

end CSD.SigmaLayer
