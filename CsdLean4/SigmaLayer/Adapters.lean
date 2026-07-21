import CsdLean4.SigmaLayer.ProjectiveSector
import CsdLean4.SigmaLayer.TheoremTargets

/-!
# FND/Adapters: the postulate ledger and the ontic-setup Rosetta

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

This module documents the FND postulate ledger and records the correspondence (the "Rosetta") between
the four ontic-setup abstractions in the corpus, together with faithfulness lemmas for the adapters. It
introduces no new postulate: the ledger below classifies what is a postulate, what is a bridge
assumption to be discharged in concrete models, and what is a theorem target.

## Postulate ledger

Core ontic postulates.

* P1. There exists a measurable ontic constraint surface `Sigma` (`ConstraintSurface`; generic theory
  keeps `Sigma` abstract).
* P2. `Sigma` carries a finite Liouville reference measure `muL` (`ConstraintDynamics.muL`).
* P3. `Sigma` carries deterministic real-parameter ontic evolution (`ConstraintDynamics.flow`,
  `flow_zero`, `flow_add`).
* P4. Ontic evolution preserves `muL` (`ConstraintDynamics.flow_preserves`).
* P5. Physical records correspond to measurable, contextual, time-indexed regions of `Sigma`
  (`RecordSemantics`; the genuinely time-indexed instance `FND/TimeIndexedRecord.lean` `flowedSemantics`,
  `event ⟨c,i,t⟩ = Φ_t⁻¹'(region)`, with record-probability persistence and flow-covariance).
* P6. Isolation introduces no new physical record; its probability law is conditional uncertainty over
  `Sigma` given the existing record history (`HistoryPreparation`, `HistoryPreparation.conditionalMeasure_apply`).
  A de-isolating measurement extends the history with the established record, yielding the post-outcome
  preparation (`FND/PostMeasurement.lean` `HistoryPreparation.appendFact` / `appendFactOfPos`, with proven
  nonzero compatible measure when the outcome is possible).

projective sector postulates.

* P7. For each finite sector dimension `N`, the operational pure-state target is `CP^{N-1}`
  (`ProjectiveState`).
* P8. There exists a measurable projection `pi : Sigma -> CP^{N-1}` (`ProjectiveSector.pi`).
* P9. `pi` need not be injective (many-to-one supported; no injectivity field).

Bridge assumptions, to be proved for concrete models whenever possible.

* B1. The relevant ontic measure pushes forward to the required projective measure
  (`HasProjectivePushforward`; a theorem for the product model).
* B2. Relevant ontic flows are projectable through `pi` (`ProjectiveDynamicsBridge.projectable`, later
  tranche; already available as `KahlerOnticSetup.projectable`).
* B3. The projected flow has a unitary or Hamiltonian realisation (`HasUnitaryRealisation`,
  `HasHamiltonianRealisation`).
* B4. De-isolating interactions realise measurable, almost-everywhere complete contextual outcome
  regions (`DeisolationModel`, later tranche).
* B5. The post-measurement record is compatible with the realised outcome region (later tranche).
* B6. Composite sectors realise the finite-dimensional tensor-product structure (`CompositeSector`,
  later tranche; the P3 tensor-derivation debt is parked by standing instruction, so this stays a bridge
  field).
* B7. Repeated experiments satisfy either an independent-trial hypothesis (LF4 `TrialWitness`) or a
  separately proved ergodic hypothesis (`IsErgodicForOutcomeRegions`).

Theorem targets, never unconditional postulates.

* T1 Born from volume (`BornFromVolume`). T2 Born from independent-trial frequencies (LF4
  `born_frequency_convergence_N`). T3 Born from deterministic-flow frequencies (`BornFromFlow`). T4
  projected unitary dynamics (`HasUnitaryRealisation`). T5 Schrödinger evolution
  (`HasHamiltonianRealisation`). T6 unique contextual outcome a.e. (`vnDeisolationModel_ae_total`). T7
  conditional state update (`conditionalUpdate_capstone`: the general Kraus/effect update, normalised, Born
weight `Re⟨x, M†M x⟩`, and the sequential/Wigner conditionalisation rule, `FND/ConditionalUpdate.lean`).
T8 Lüders update (`luders_capstone`: the projective post-measurement update is normalised, repeatable,
and reproduces conditional Born probabilities, `FND/Luders.lean`; the sharp special case of T7; linked to
the ontic record conditioning via `FND/ConditioningLink.lean`
`luders_record_conditioning_correspondence` -- both are the same `bayesianConditional w(fine)/w(coarse)`
rule, over the Born weight and `μL` respectively). T9
mixed-state representation (`FND/MixedState.lean`: `mixedState_capstone`/`traceForm_mix` -- convex
  mixtures are density operators and the Born rule is affine in the state; `rankOneDensity_isPure`,
  `maximallyMixed_not_isPure`; full purity characterisation `IsPure ρ ↔ Tr(ρ²)=1` via the spectral
  theorem, `isPure_iff_trace_sq_one`). T10 POVM
  by dilation
  (`POVMWeightsProbability`, `LF4.povm_born_frequency_volume_canonical`). T11 composite quantum
  probabilities. T12 entangled predictions. T13 contextuality (`NoNonContextualValuation`). T14 Bell
  correlations (`NoLocalHiddenVariableTable`, `HasTsirelsonSeparation`). T15 operational no-signalling
  (`HasNoSignalling`; operator form `tensorSector_no_signalling`). T16 two-path Born interference
  (`HasBornInterference`, from the Hadamard test). T6 to T16 are defined with their
  measurement/composition modules (`FND/LiftedMeasurement.lean`, `FND/CompositeInterface.lean`,
  `FND/CompositeAdapters.lean`, `FND/Interference.lean`, `FND/TensorSector.lean`).

Interference and tensors, specifically. Interference (T16) is NOT a postulate: it is a consequence of
P7 (the sector is a COMPLEX projective space) and T1/T2 (Born weights), realised as the phase-dependent
two-path probability `(1 + Re⟨ψ,Uψ⟩)/2`. The tensor product is likewise DERIVED, not posited: the finite
`ℂ^{NA} ⊗ ℂ^{NB} = ℂ^{NA·NB}` is the projective sector on the product index `Fin NA × Fin NB`
(`FND/TensorSector.lean` `tensorIndexEquiv`), on which the local operator algebra commutes
(`aliceOp_bobOp_commute`) and no-signalling holds (`tensorSector_no_signalling`). The ONLY tensor posit
is bridge B6 (`CompositeSector.tensor_dimension`, `dim = NA·NB`): the "why `⊗`" reconstruction (P3) is
parked by standing instruction, so composite structure is posited per instance.

## The ontic-setup Rosetta (resolving the drift)

Four ontic-setup abstractions exist; the FND canonical core is `ConstraintDynamics + ProjectiveSector`
(the only one carrying the one-parameter-group law and no `True` placeholders). The intended tower:

    ConstraintDynamics + ProjectiveSector      (FND canonical core)
      ── (fix time + region) ─────────────►  LF1.OnticSetup        (single-Phi typicality)
      ── (+ placeholders, + group law) ───►  LF4.KahlerOnticSetup  (W-series forward dynamics)

Adapters (all one-directional, no existing file altered):

* `Preparation.toOnticSetup : Preparation D -> OnticTime -> LF1.OnticSetup Sigma` (fix time + region).
* `kahlerConstraintDynamics : KahlerOnticSetup N -> ... -> ConstraintDynamics K.Sigma` (partial: takes
  the group laws `KahlerOnticSetup` lacks and `IsFiniteMeasure`).
* `kahlerProjectiveSector : KahlerOnticSetup N -> ProjectiveSector N D` (total; `pi` is dynamics independent).

`LF4.KahlerOnticSetup` field status: `IsKahlerSector` / `kahler_condition` and (on the trivial witness)
`IsLiouvilleKahlerVolume` are documented placeholders; its `flow` is time-parameterised but does NOT
carry `flow_zero` / `flow_add`, which the adapter supplies explicitly. This is exactly the drift the
canonical core removes.
-/

open MeasureTheory

namespace CSD.SigmaLayer

universe u

variable {N : ℕ} {Sigma : Type u} [MeasurableSpace Sigma] [Nonempty Sigma]

/-- **Faithfulness of the LF1 adapter (region).** The adapter's preparation region is the FND
preparation's region. -/
theorem toOnticSetup_region {D : ConstraintDynamics Sigma} (P : Preparation D) (t : OnticTime) :
    (P.toOnticSetup t).Ω0 = P.region := rfl

/-- **Faithfulness of the LF1 adapter (flow).** The adapter's `Φ` is the flow at the chosen time. -/
theorem toOnticSetup_flow {D : ConstraintDynamics Sigma} (P : Preparation D) (t : OnticTime) :
    (P.toOnticSetup t).Φ = D.flow t := rfl

/-- **Faithfulness of the Kähler `ConstraintDynamics` adapter (flow).** The adapter's flow is the
Kähler setup's flow. -/
theorem kahlerConstraintDynamics_flow (K : CSD.LF4.KahlerOnticSetup N)
    [IsFiniteMeasure K.liouvilleMeasure]
    (hzero : ∀ x, K.flow 0 x = x) (hadd : ∀ s t x, K.flow (s + t) x = K.flow s (K.flow t x)) :
    (kahlerConstraintDynamics K hzero hadd).flow = K.flow := rfl

/-- **Faithfulness of the Kähler `ProjectiveSector` adapter (projection).** The adapter's `pi` is the
Kähler setup's projection. -/
theorem kahlerProjectiveSector_pi (K : CSD.LF4.KahlerOnticSetup N)
    {D : ConstraintDynamics K.Sigma} :
    (kahlerProjectiveSector K (D := D)).pi = K.pi := rfl

end CSD.SigmaLayer

