import CsdLean4.FND.ChoiceASector
import CsdLean4.FND.TheoremTargets

/-!
# FND/Adapters: the postulate ledger and the ontic-setup Rosetta

**Category:** 7-FND (the Choice A ontological layer).

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
  (`RecordSemantics`).
* P6. Isolation introduces no new physical record; its probability law is conditional uncertainty over
  `Sigma` given the existing record history (`HistoryPreparation`, `HistoryPreparation.conditionalMeasure_apply`).

Choice A sector postulates.

* P7. For each finite sector dimension `N`, the operational pure-state target is `CP^{N-1}`
  (`ProjectiveState`).
* P8. There exists a measurable projection `pi : Sigma -> CP^{N-1}` (`ChoiceASector.pi`).
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
  (`HasHamiltonianRealisation`). T6 unique contextual outcome a.e. (later). T7 conditional state update.
  T8 Lüders update. T9 mixed-state representation. T10 POVM by dilation. T11 composite quantum
  probabilities. T12 entangled predictions. T13 contextuality. T14 Bell correlations. T15 operational
  no-signalling. T6 to T15 are defined with their measurement/composition modules in later tranches.

## The ontic-setup Rosetta (resolving the drift)

Four ontic-setup abstractions exist; the FND canonical core is `ConstraintDynamics + ChoiceASector`
(the only one carrying the one-parameter-group law and no `True` placeholders). The intended tower:

    ConstraintDynamics + ChoiceASector      (FND canonical core)
      ── (fix time + region) ─────────────►  LF1.OnticSetup        (single-Phi typicality)
      ── (+ placeholders, + group law) ───►  LF4.KahlerOnticSetup  (W-series forward dynamics)

Adapters (all one-directional, no existing file altered):

* `Preparation.toOnticSetup : Preparation D -> OnticTime -> LF1.OnticSetup Sigma` (fix time + region).
* `kahlerConstraintDynamics : KahlerOnticSetup N -> ... -> ConstraintDynamics K.Sigma` (partial: takes
  the group laws `KahlerOnticSetup` lacks and `IsFiniteMeasure`).
* `kahlerChoiceASector : KahlerOnticSetup N -> ChoiceASector N D` (total; `pi` is dynamics independent).

`LF4.KahlerOnticSetup` field status: `IsKahlerSector` / `kahler_condition` and (on the trivial witness)
`IsLiouvilleKahlerVolume` are documented placeholders; its `flow` is time-parameterised but does NOT
carry `flow_zero` / `flow_add`, which the adapter supplies explicitly. This is exactly the drift the
canonical core removes.
-/

open MeasureTheory

namespace CSD.FND

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

/-- **Faithfulness of the Kähler `ChoiceASector` adapter (projection).** The adapter's `pi` is the
Kähler setup's projection. -/
theorem kahlerChoiceASector_pi (K : CSD.LF4.KahlerOnticSetup N)
    {D : ConstraintDynamics K.Sigma} :
    (kahlerChoiceASector K (D := D)).pi = K.pi := rfl

end CSD.FND

