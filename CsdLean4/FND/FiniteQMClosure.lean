import CsdLean4.FND.UnifiedMeasurement
import CsdLean4.FND.UnifiedFlowedRecords
import CsdLean4.FND.ConditioningLuders

/-!
# FND/FiniteQMClosure: the tiered finite-dimensional QM closure (#6)

**Category:** 7-FND (the Choice A ontology layer).

The capstone bundle. Every earlier module proves ONE reconstructed fact on the single many-to-one ontic
model `productDynamics H hH p₀` (isolated Hamiltonian flow `exp(-itH)` on `Σ = ℂℙ^M × T²`, Liouville
measure `μL = μFS ⊗ vol`, projection `π = Prod.fst`). This module collects the ones that are GENUINELY
PROVED on that model into a single record `FiniteQMClosure`, discharged by `unifiedFiniteQMClosure`, and —
crucially — states honestly, tier by tier, what is a theorem here, what is a Choice-A posit, what is a
textbook-QM adapter, and what is still open. No field is `sorry`; the structure carries only real theorems,
and the non-theorem tiers live in this docstring, not in fabricated fields.

## Tier 1 — PROVED on the unified model (the fields of `FiniteQMClosure`)

All nine on the ONE model `productDynamics H hH p₀`:

* `isolated_flow_measure_preserving` — the isolated flow preserves `μL` (`ConstraintDynamics.flow_preserves`);
* `schrodinger_projection` — `π ∘ Φ_t = exp(-itH) • ·` (`productDynamicsBridge.projectable`);
* `fubini_study_bridge` — `π_* μL = μFS`, i.e. B1 (`productSector_hasFubiniStudyPushforward`);
* `measurement_preserving` — the de-isolation interaction preserves `μL`
  (`measurementFlow_measurePreserving`);
* `readout_ae_total` — the contextual pointer readout is a.e. defined (T6, `unifiedDeisolationModel_ae_total`);
* `records_established` — the readout records the established outcome, B5 (`unifiedDeisolationModel_records`);
* `records_time_physical` — the time-indexed record probability is conserved and flow-covariant, #5
  (`unified_records_persistence`);
* `born_frequency` — i.i.d. trials of `μL` have outcome-region frequency → `‖⟨eᵢ,ψ⟩‖²`, #2
  (`unified_born_frequency`);
* `conditioning_is_luders` — record conditioning = Lüders update as predictions, #3/#4
  (`conditioning_luders_effect_equivalence`).

## Tier 2 — ASSUMED under Choice A

The interpretive commitment that makes the above a reconstruction of QM rather than a study of a measure
space: taking the Fubini-Study/Liouville measure on `ℂℙ^M × T²` to BE the ontic probability law (Choice A;
see `specs/future-work.md`). This is a stance, not a Lean proposition, and is deliberately NOT a field. The
structural sub-posits that a bare Choice-A reconstruction would ALSO assume are, on this concrete model,
already DISCHARGED (hence they appear as tier-1 `fubini_study_bridge` etc., not here) — with one honest
exception recorded separately:

* **B6 (composite tensor structure)** — that a joint system's algebra is `M_m ⊗ M_n`. Posited per instance
  in `CompositeSector`, OR derived: `CSD.FND.CompositeSector.ofReconstruction`
  (`FND/TensorReconstruction.lean`, `composite_dim_eq`) builds a `CompositeSector` whose `tensor_dimension`
  is PROVED from the composite algebra being simple — so B6 is "assumed OR dischargeable", not a gap. This
  is single-system closure; B6 belongs to the composite track and is intentionally outside `FiniteQMClosure`.

## Tier 3 — QM ADAPTERS (restatements into textbook QM, elsewhere)

`FND/Adapters.lean`, `FND/CompositeAdapters.lean`: the maps taking these ontic facts to their standard
Hilbert-space QM statements (density operators, Lüders channel, Born rule). They translate; they do not add
reconstruction content.

## Tier 4 — OPEN

* mixed-state / ensemble representation (#8): the statistical side is now closed — finite ensembles and
  the spectral decomposition (`FND/MixedEnsemble.lean`: every density operator is a convex ensemble of
  pure states, Born rule = eigenvalue-weighted average of pure Born rules), #8 A+B. What remains open is
  #8 C — the ONTIC-side mixed representation on this unified model (a classical mixture over ontic
  preparations reproducing `Tr(ρ E)`), which would add a `mixed_born_frequency` field here;
* the ECDLP circuit track's capstone `denote = divstepRev` + termination (`ECDLP/SafegcdDivstepCircuit.lean`)
  — independent of this QM closure, tracked separately.

## References

`specs/future-work.md` (FND-T5, FND-T6, Choice A); `specs/reconstruction-status.md`;
`specs/connectivity-manifest.md` (L9). Source theorems: `unified_choiceA_capstone`
(`FND/UnifiedMeasurement.lean`), `unified_records_persistence`, `unified_born_frequency`
(`FND/UnifiedFlowedRecords.lean`), `conditioning_luders_effect_equivalence`
(`FND/ConditioningLuders.lean`), `CompositeSector.ofReconstruction` (`FND/TensorReconstruction.lean`).
-/

open MeasureTheory

namespace CSD.FND

open CSD.LF4 CSD.LF5

variable {N M : ℕ} [NeZero N] (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
  (p₀ : CPN (M + 1)) (e : Fin N × Fin N ≃ Fin (M + 1))
  (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
  (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)

/-- **The tiered finite-dimensional QM closure (Tier 1).** A record of exactly the reconstructed QM facts
that are GENUINELY PROVED on the single ontic model `productDynamics H hH p₀` (measurement reference state
`ψ'`, Born state `ψ`). Every field is a theorem discharged by `unifiedFiniteQMClosure`; the Choice-A posit,
QM adapters, and open residue are documented in the module header, not encoded as fields. -/
structure FiniteQMClosure : Prop where
  /-- The isolated Hamiltonian flow preserves the Liouville measure. -/
  isolated_flow_measure_preserving :
    ∀ t, MeasurePreserving ((productDynamics H hH p₀).flow t) (kMuL p₀) (kMuL p₀)
  /-- The isolated flow projects through `π` to the Schrödinger flow `exp(-itH) • ·` (Schrödinger pillar). -/
  schrodinger_projection :
    ∀ t x, (productSector H hH p₀).pi ((productDynamics H hH p₀).flow t x)
      = productProjectedFlow H hH t ((productSector H hH p₀).pi x)
  /-- `π_* μL = μFS`: the Fubini-Study bridge (B1). -/
  fubini_study_bridge : HasFubiniStudyPushforward (productSector H hH p₀) p₀
  /-- The de-isolation measurement interaction preserves `μL` (on the same `Σ`, `μL`). -/
  measurement_preserving :
    ∀ t c, MeasurePreserving ((unifiedDeisolationModel H hH p₀ e ψ' hψ'0).interaction t c)
      (kMuL p₀) (kMuL p₀)
  /-- The contextual pointer readout is defined almost everywhere (T6). -/
  readout_ae_total : (unifiedDeisolationModel H hH p₀ e ψ' hψ'0).AETotalReadout () () 0 (kMuL p₀)
  /-- The readout records the established outcome (B5). -/
  records_established : DeisolationModel.RecordsEstablishedOutcome (unifiedDeisolationModel H hH p₀ e ψ' hψ'0)
  /-- Time-indexed records are physical: probability is conserved and the record is flow-covariant (#5). -/
  records_time_physical : ∀ (c : (vnRecordSignature N).Context) (i : (vnRecordSignature N).Outcome c),
    (∀ t, ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
        ((unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t⟩)
      = ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
        ((fun x : KSigma (M + 1) => vnPointerOutcome ψ' hψ'0 e x.1) ⁻¹' {some i}))
    ∧ (∀ s t, (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t + s⟩
        = (productDynamics H hH p₀).flow s ⁻¹'
          (unifiedFlowedSemantics H hH p₀ e ψ' hψ'0).event ⟨c, i, t⟩)
  /-- Born frequency on the model: i.i.d. trials of `μL` land in `π⁻¹(bornRegion i)` with frequency →
  `‖⟨eᵢ,ψ⟩‖²` (#2). -/
  born_frequency : ∀ {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (_ : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    (X : ℕ → Ω → KSigma (M + 1)) (_ : ∀ n, Measurable (X n))
    (_ : ∀ n, Measure.map (X n) Pr = ((productDynamics H hH p₀).muL : Measure (KSigma (M + 1))))
    (_ : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
        (fun n => Set.indicator
          ((X n) ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i)) (fun _ => (1 : ℝ))))),
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Filter.Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        Filter.atTop (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2))
  /-- Record conditioning = Lüders update as predictions, for every pointer-basis effect (#3/#4). -/
  conditioning_is_luders : ∀ (S T : Finset (Fin (M + 1))), ‖ψ‖ = 1 →
    bayesianConditional
        (fun U : Finset (Fin (M + 1)) =>
          (((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
            ((productSector H hH p₀).pi ⁻¹' ⋃ k ∈ U, bornRegion ψ hψ0 k)).toReal) T S
      = bayesianConditional
          (fun U : Finset (Fin (M + 1)) => ∑ k ∈ U, ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2)
          T S

/-- **The finite-dimensional QM closure holds on the unified model.** Every tier-1 field is discharged by
its source lemma on the single ontic model `productDynamics H hH p₀`. Requires only the normalisations of
the measurement reference state `ψ'` and the Born state `ψ` — the whole reconstruction (dynamics,
measurement, records, Born frequency, conditioning=Lüders) is a theorem on one model, with the Choice-A
posit and open residue as documented (module header), not as hidden gaps. -/
theorem unifiedFiniteQMClosure (hψ' : ‖ψ'‖ = 1) (hψ : ‖ψ‖ = 1) :
    FiniteQMClosure H hH p₀ e ψ' hψ'0 ψ hψ0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := unified_choiceA_capstone H hH p₀ e ψ' hψ'0 hψ'
  exact
    { isolated_flow_measure_preserving := h1
      schrodinger_projection := h2
      fubini_study_bridge := h3
      measurement_preserving := h4
      readout_ae_total := h5
      records_established := h6
      records_time_physical := fun c i => unified_records_persistence H hH p₀ e ψ' hψ'0 c i
      born_frequency := fun hpos X hX hlaw hindep =>
        unified_born_frequency H hH p₀ ψ hψ0 hψ hpos X hX hlaw hindep
      conditioning_is_luders := fun S T hψn =>
        conditioning_luders_effect_equivalence H hH p₀ ψ hψ0 hψn S T }

end CSD.FND
