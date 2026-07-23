# Reconstruction status — a thorough review of what is machine-verified (2026-07-23)

**Purpose.** A single honest review of what the `csd-lean4` corpus actually proves, at commit `HEAD`
(after the Σ-layer (projective-sector, Paper C) and the honest-alignment closeout). It supersedes scattered
claims; where it and an older document disagree, this file and
[`connectivity-manifest.md`](connectivity-manifest.md) win. Everything below is `sorry`-free,
`lake build CsdLeanTests` green, and AxiomAudit-pinned to the foundational triple (`propext`,
`Classical.choice`, `Quot.sound`) unless explicitly noted otherwise.

> **Two endpoints — do not conflate them.**
> 1. **Operational finite-QM closure** on a concrete projective product witness — this is what the Lean
>    proofs deliver, and it is essentially complete.
> 2. **A faithful derivation of the Paper C/D architecture** from a primitive ontology — this is *not*
>    complete, and the corpus does not claim it.
>
> The precise, defensible claim is:
>
> > The repository proves operational finite-QM closure on a concrete projective product witness satisfying
> > the exact formalised subset of the Paper C assumptions.
>
> It does **not** claim that this witness *derives* projective geometry, the Fubini–Study measure, or
> Schrödinger evolution from a more primitive ontic model — those ingredients are **built into** the witness.

## 1. One-paragraph verdict

The corpus is a **rigorous, forward, finite-dimensional QM reconstruction on one concrete projective-sector
ontic witness.** A single genuine `Φ ≠ id` Kähler sector yields BOTH pillars (Born + Schrödinger) at general
`N` with arbitrary Hermitian `H` (`manyToOneSchrodingerSetup_both_pillars`), and ONE ontic model
`(Σ = ℂℙ^{M}×T², μL = μFS⊗vol, Φ, π = Prod.fst)` carries isolated Hamiltonian dynamics and de-isolating
measurement together. `unified_projectiveSector_capstone` BUNDLES the dynamics + measurement core (six proved
properties). Time-indexed record semantics, Born-frequency convergence (for EVERY unit `ψ`), and the
conditioning = Lüders correspondence are ASSEMBLED into one tiered record: **`FiniteQMClosure`** /
`unifiedFiniteQMClosure` (`SigmaLayer/FiniteQMClosure.lean`) collects all eleven proved-on-the-model facts as
fields, each discharged by its source lemma, and states honestly what is a theorem here vs. a projective-sector
posit vs. a QM adapter vs. still open (no field is `sorry`). **This is a concrete consistency witness, not a
derivation of the Paper C architecture:** the witness has `μL = μFS ⊗ vol` and `Φ_t = (e^{-itH}·[p], θ)` built
in, so the pushforward-to-`μFS` and the Schrödinger pillar are *compatibility facts about the witness*, not
derivations of `μFS` or of unitary evolution from a fibre-primitive ontology. Two genuinely open questions sit
outside the closure: **SO-1** (the sector-origin problem — the origin of `(Σ, π, μL)`; the trials SAMPLE `μL`
i.i.d.) and the **A7 measurement-partition mismatch** (the present outcome cells are preparation-indexed, not
context-fixed apparatus basins — tracked as **MD-1**). This scope matches Paper C's own (§A, and §3.6 "the
deeper physical origin of the quantum-effective sector selected by A5 is left for later work").

## 2. The Paper C axiom map (A1–A7) — canonical formalisation status

This is the canonical map of *what the Lean corpus formalises against each Paper C axiom.* "Partial",
"witness", and "exact ε=0" are used honestly; do not read "represented" as "derived".

| Paper C axiom | Lean status |
|---|---|
| **A1** compact Kähler ontic surface | **Partial.** Compactness and the *pointwise* Kähler compatibility core are represented (`IsFubiniStudyKahler`, `fubiniStudy_pointwise_kahler_compatibility`); full manifold exterior calculus (`dω=0`, `ωⁿ/n! = μ_FS`) is not formalised (no Mathlib API). |
| **A2** Hamiltonian ontic dynamics | **Partial.** A measure-preserving one-parameter group flow is formalised (`ConstraintDynamics.flow`, `flow_preserves`); a *generic* ontic Hamiltonian vector field `X_H` on `Σ` is not — the witness uses the projected `e^{-itH}` lift. |
| **A3** smooth many-to-one projection | **Partial interface, concrete witness.** Lean requires *measurability* of `π` (not smoothness); the product witness `π = Prod.fst` is genuinely many-to-one (the `T²` fibre). |
| **A4** pushforward measure `π_*μL = μ_FS` | **Proved for the witness** (`productSector_hasFubiniStudyPushforward`, B1) **and forced under full unitary symmetry** (`localised_sectorPostulate_capstone`); **not derived** from arbitrary ontic dynamics. The witness has `μL = μFS ⊗ vol` built in. |
| **A5** quantum-effective Hamiltonians (projectability) | **Exact `ε=0` represented.** The exact fibre-invariant / projectable case `H = h∘π` is formalised (the projected flow closes and is `e^{-itH}` on rays). The *approximate* `(ε, T)`-projectability (`sup‖d(δH)|_V‖ ≤ ε`) is **not** formalised. |
| **A6** composites + marginal stability | **Partial.** Operational tensor structure, reduced states and no-signalling exist (`compositeTensorEquiv`, `compositeAlgReconstruction`, `tensorSector_no_signalling`); the general **non-factorising ontic composite** architecture (`Σ_AB ≠ Σ_A × Σ_B` as a primitive) is not reconstructed. |
| **A7** context-defined measurement partitions | **Partial — the genuine architecture gap (MD-1).** Measurable exclusive outcomes and a.e. readout exist, but the present cell *shapes* are `bornRegion ψ'`-indexed — they depend on the prepared/dilated state — rather than being derived as context-fixed apparatus basins `Ωᵢ(M)`. Labelled a **preparation-indexed operational witness**, not the general Paper C A7 mechanism. |

### 2a. Target inventory (T1–T16) — inhabited reconstruction targets

The A1–A7 map above is the *axiom-formalisation* status. The following is the separate inventory of
*reconstruction targets* that are inhabited by proved theorems on the witness. NONE of these is an `axiom`;
postulates are structure fields, bridges are named assumptions discharged per model, targets are `Prop`
predicates inhabited by proved theorems. Full ledger in
[`../CsdLean4/SigmaLayer/Adapters.lean`](../CsdLean4/SigmaLayer/Adapters.lean) and [`../AXIOMS.md`](../AXIOMS.md) §3.7.

| # | Target | Key theorem | Status |
|---|---|---|---|
| T1 | Born from volume | `BornFromVolume`, LF4 `fs_born_volume_ratio_N` | proved |
| T2 | Born from i.i.d. frequencies | `born_frequency_convergence_N` | proved |
| T3 | Born from deterministic-flow frequencies | `BornFromFlow` predicate | **OPEN (= SO-1 face)** — a single flow cannot pin `μ_FS` (no-go below); residual gap is the Mathlib-absent pointwise Birkhoff theorem, and the unitary no-gos exclude the hypothesis |
| T4 | Unitary projected dynamics | `HasUnitaryRealisation` | proved (witness) |
| T5 | Schrödinger evolution | `HasHamiltonianRealisation`, `productProjectedFlow_hasHamiltonianRealisation` | proved (witness) |
| T6 | Unique contextual outcome a.e. | `vnDeisolationModel_ae_total` | proved (preparation-indexed cells — MD-1) |
| T7 | General conditional update | `conditionalUpdate_capstone` | proved |
| T8 | Lüders update | `luders_capstone` (sharp special case of T7) | proved |
| T9 | Mixed states | `mixedState_capstone`, `isPure_iff_trace_sq_one`; ensemble #8 A+B `traceForm_ensemble`, `density_isPureEnsemble`, `mixedEnsemble_capstone`; ontic-side #8 C weight `mixed_ontic_born_weight` (= `FiniteQMClosure.mixed_born`) **and frequency** `unified_mixed_born_frequency` (= `FiniteQMClosure.mixed_born_frequency`) | **proved (weights + a.s. frequency; both closed)** |
| T10 | POVM by dilation | `POVMWeightsProbability`, `LF4.povm_born_frequency_volume_canonical` | proved |
| T11 | Composite probabilities | joint Born-frequency capstones | per-instance (A6-gated for sector-intrinsic) |
| T12 | Entangled predictions | = T14 | per-instance |
| T13 | Contextuality | `NoNonContextualValuation`: Cabello-18 / Mermin-Peres / GHZ; `general_ks_noNonContextualValuation` | proved (+ general KS) |
| T14 | Bell correlations | `NoLocalHiddenVariableTable` (CGLMP), `HasTsirelsonSeparation`, `bell_general_separation`, `lhv_chsh_le_two`, `qm_chsh_le_tsirelson` | proved (+ universal bounds) |
| T15 | No-signalling | `HasNoSignalling` (singlet), `tensorSector_no_signalling` (operator) | proved |
| T16 | Two-path interference | `HasBornInterference` (Hadamard test) | proved (derived, not postulated) |

## 3. The connectivity chain (L1–L9)

See [`connectivity-manifest.md`](connectivity-manifest.md) for full evidence.

| Link | Claim | Status |
|---|---|---|
| L1 | Kähler geometry ⇒ sector fields | PARTIAL — volume forced; 2-form's **pointwise** compatibility core now genuine & consumed (`IsKahlerSector := IsFubiniStudyKahler`); only manifold closedness `dω=0` / `ω^{∧n}/n!=μ_FS` unformalizable (no Mathlib API) |
| L2 | Σ+Φ+π ⇒ projected flow | CONNECTED |
| L3 | projected flow ⇒ Schrödinger | CONNECTED — general `N`, arbitrary `H`; C¹-Stone derivation EXERCISED on the real nonzero generator (`manyToOneSchrodingerSetup_schrodinger_derived`) |
| L4 | genuine `Φ ≠ id` inhabitant | CONNECTED — `rotationSetup`, `manyToOneSetup`, `unitaryFlowSetup` (4 total) |
| L5 | sector ⇒ Born frequencies | CONNECTED (structural) |
| L6/L8 | ONE object, both pillars, many-to-one `π` | CONNECTED — `manyToOneSchrodingerSetup_both_pillars` |
| **L9** | ONE model: dynamics + measurement + records + Born + update | CONNECTED — **`FiniteQMClosure` / `unifiedFiniteQMClosure`** assembles all 11 proved-on-model facts into ONE tiered record, each field discharged by its source lemma; projective-sector posit / QM adapters / open residue documented, not encoded as fields |
| **L7** ★ | Born weights derived FROM the flow | **OPEN — = SO-1** (boundary proved; ergodic face sharpened) — the sector is posited; a single flow provably cannot pin `μ_FS` (`flow_admits_invariant_ne_fubiniStudy`, `obsFlow_not_uniquely_ergodic`). The gap to `BornFromFlow` is exactly the Mathlib-absent pointwise Birkhoff theorem. Typicality itself is forced by the LLN, not this route (Papers A/B) |

## 4. The forward reconstruction — what each pillar delivers (on the witness)

* **Born rule** (LF1–LF4): the Born weight `‖⟨eᵢ,ψ⟩‖²` is a Fubini–Study typicality volume; i.i.d.
  FS-typical trial frequencies converge a.s. to it, Gleason-free, general `N`, including **general POVMs**
  (`povm_born_frequency_volume`, canonical Naimark dilation from CFC `√Eᵢ`).
* **Schrödinger dynamics** (the W-series, LF4): given the Kähler sector interface, Wigner rigidity +
  Bargmann branch selection + phase lift + a C¹ (and continuity-only) finite-dim Stone theorem force the
  projected flow to be `exp(-itH)` on rays. Instantiated non-trivially at general `N`
  (`manyToOneSchrodingerSetup`); the C¹-Stone derivation is EXERCISED on the real object at general `N`
  with arbitrary Hermitian `H` — `manyToOneSchrodingerSetup_schrodinger_derived`.
* **Measurement** (LF5 + SigmaLayer): a measure-preserving von Neumann de-isolation flow realises the Naimark
  dilation; the per-microstate pointer outcome is defined a.e.; frequencies are Born. **Honest caveat (MD-1):**
  the outcome *cells* are the dilated Born regions `bornRegion ψ'` — preparation-indexed, not the
  context-fixed `Ωᵢ(M)` of Paper C A7. This is a preparation-indexed operational witness.
* **Records / state update** (SigmaLayer): records are time-indexed measurable events (`flowedSemantics`),
  with probability conserved and flow-covariant under isolation; the record conditioning equals the Lüders
  update as an OPERATIONAL EQUIVALENCE (`conditioning_luders_effect_equivalence`), resting on the proved
  weight agreement `onticRegion_measure_eq_born`.
* **Entanglement / non-locality** (LF6): Bell-forced non-factorisation in the Σ-engine at full
  generality — CGLMP for every `d`, GHZ/Mermin for every party count `n`, no-signalling; the universal
  bounds (`lhv_chsh_le_two`, `qm_chsh_le_tsirelson`, `cglmp_lhv_le_two`, `bell_general_separation`).
* **Open-system dynamics** (LF6-2): the two canonical qubit dissipators as continuous quantum dynamical
  semigroups — T2 dephasing (`dephasingChannel`) and T1 amplitude damping (`dampingChannel`).

## 5. Adjacent arms (honest scope)

* **Empirical / CSD arm** — thermodynamics (TH1–TH4), CV track (finite position/momentum, approximate
  CCR, oscillator spectrum), algorithms (Deutsch–Jozsa, Simon, BV, Grover, QFT, full Shor), metrology
  (Ramsey, Heisenberg, quantum Fisher), QEC, contextuality, channels/decoherence. These share the same
  complex-sector + Born + unitary primitives but are independent theorems consuming them, not a formal
  cascade from the SigmaLayer ledger.
* **Reversible-arithmetic / circuit arm** — the general reversible quantum-arithmetic library
  (`Mathlib/QuantumInfo/Reversible/`) presupposes the unitary-evolution pillar; its theorems are circuit
  semantics and cost bounds, NOT a QM reconstruction. (The ecdsa.fail / ECDLP resource-estimation track was
  extracted to its own repository 2026-07-20 and is no longer present here.)

## 6. Axiom hygiene

* Foundational triple only on every SigmaLayer/LF headline pin.
* **Zero imported axioms** (since 2026-07-21). The last one, `busch_effect_gleason`, was proved —
  now `OperationalPackage.effect_gleason_representation` (`LF2/EffectGleason.lean`), foundational
  triple. See [`../AXIOMS.md`](../AXIOMS.md) §2.2.
* No global `axiom` declarations in the Σ-layer; no `sorry`/`admit`.
* Static guards (connectivity, sector-linkage, axiom-imports, claims) pass and are run in CI.

## 7. The honest frontier — what is NOT claimed

*(Actionable open items are tracked in the canonical [`BACKLOG.md`](BACKLOG.md).)*

* **SO-1 ★ — the sector-origin problem.** Deriving the sector `(Σ, π, μL)` and its Born weights FROM a
  primitive ontology / deterministic flow. The sector is posited; the trials sample `μL`. This is the one
  deep gap, research-grade, and it is **distinct from Paper C A5** (A5 is the projectability condition that
  *selects* the quantum-effective sector; SO-1 is the deeper origin of the sector, which Paper C §3.6 itself
  leaves "for later work"). SO-1 now has **both a proved boundary and a localized partial**:
  * **No-go (why the gap is real, not a formalisation debt)** (`SigmaLayer/SectorPostulateNoGo.lean`): a single
    projective unitary flow does NOT uniquely determine an invariant measure — a flow with two distinct fixed
    rays admits (at least) two distinct invariant probability measures, so at least one is not `μ_FS`
    (`flow_admits_invariant_ne_fubiniStudy`), exhibited on the concrete nontrivial phase-flip `diag(1,-1)` on
    `ℂℙ¹` (`phaseFlip_admits_invariant_ne_fubiniStudy`).
  * **Localized partial (what DOES pin it)** (`SigmaLayer/LocalisedTypicality.lean`): the sector posit is
    discharged AT sectors carrying the full `U(N)` symmetry — the typicality measure and Born weights are
    symmetry-forced there (`localised_sectorPostulate_capstone`, `region_measure_symmetry_forced`). Residual:
    the bare flow is one one-parameter subgroup, not all of `U(N)`. Together: a single flow is provably
    insufficient; the full symmetry is provably sufficient — the frontier is exactly the gap between them.
* **MD-1 — the A7 measurement-partition mismatch.** Paper C A7 makes outcome regions depend on the
  measurement context, `Ωᵢ = Ωᵢ(M)`, as context-fixed measurable partitions with `μ_FS`-null boundaries. The
  present `vnPointerOutcome` uses `bornRegion ψ'`, so the cell *shapes* depend on the prepared/dilated state.
  This is a genuine architecture gap, recorded — not redesigned — as the next scientific tranche:
  > **MD-1.** Separate preparation laws from context-fixed outcome partitions, then derive the outcome
  > probabilities by integrating the preparation law over those fixed regions.
  A later Paper D strengthening would additionally prove that the interaction generates stable pointer basins
  and persistent apparatus memory.
* **A6 "why ⊗"** — SUFFICIENCY + NECESSITY both proved (`SigmaLayer/TensorSolved.lean`
  `composite_is_tensor_product`; `SigmaLayer/TensorReconstruction.lean` `compositeAlgReconstruction`,
  `composite_dim_eq`). Residual: local tomography itself is the one operational axiom that cannot be derived
  from nothing (it singles out quantum `⊗`); and the general non-factorising ontic composite (A6 as a
  primitive) is not reconstructed.
* **A1 / KG-1** — the Kähler closed 2-form `dω = 0` and the global volume identity, blocked on missing
  Mathlib manifold exterior calculus (the volume is forced; the pointwise form is proved).
* **A5 approximate regime** — the `(ε, T)`-projectable case (`sup‖d(δH)|_V‖ ≤ ε`, `ε > 0`) is not
  formalised; only the exact `ε = 0` fibre-invariant case is.
* **LF6-9** — the general Lindblad generator + complete positivity (the two bounded dissipators are done).
* **IP-1** — identical particles / spin-statistics, not in the corpus.

### 7a. Settled non-goals — do NOT re-litigate these

Two positions are **decided** and recorded here so they are not re-argued. Both are backed by
machine-checked facts in the corpus.

* **NG1 — "derive Born from a single deterministic flow" (the Birkhoff / single-trajectory ergodic
  route) is a PROVED DEAD-END that CSD deliberately does not take.** CSD forces typicality by the **law
  of large numbers over fresh i.i.d. preparations**, NOT by time-averaging one trajectory
  (`specs/active-todo.md`, framing correction 2026-06-29, Papers A & B). The single-flow route is
  provably impossible: `flow_admits_invariant_ne_fubiniStudy` (`SigmaLayer/SectorPostulateNoGo.lean`),
  `obsFlow_not_ergodic` / `obsFlow_not_uniquely_ergodic` (`LF4/TypicalityForcing.lean`). The ergodic
  scaffolding is **boundary-marking only**. The genuine open ★ residue is narrower: the sector/symmetry
  ORIGIN (SO-1 above), not "Born from flow".
* **NG2 — the Busch effect-Gleason axiom is NOT needed for CSD's core claim; discharging it is
  cosmetic.** CSD's ontic Born rule is **Gleason-free**: it is a Fubini–Study / Duistermaat–Heckman
  *volume* (`bornRegion_fs_measure`, `born_frequency_convergence_N`). The former axiom
  `busch_effect_gleason` entered only the **operational effect/POVM stratum**, off the reconstruction path.
  It was **proved in-repo 2026-07-21** (`OperationalPackage.effect_gleason_representation`), taking the
  imported-axiom count to zero — an **audit-posture** improvement, NOT a strengthening of the CSD
  reconstruction.

## 8. Bottom line

The corpus proves **operational finite-QM closure on a concrete projective product witness** satisfying the
exact formalised subset of the Paper C assumptions: one witness model, one measurement/record/update loop, the
full T1–T16 target inventory inhabited, axiom-clean. It does **not** derive the Paper C architecture from a
primitive ontology — the projective geometry, Fubini–Study measure and unitary evolution are built into the
witness. The two genuine open frontiers are **SO-1** (the *origin* of the posited sector) and **MD-1** (the
A7 preparation-indexed vs. context-fixed measurement-partition mismatch) — genuine open problems, honestly
flagged, not papered over. This is exactly Paper C's own scope.

References: [`connectivity-manifest.md`](connectivity-manifest.md), [`future-work.md`](future-work.md),
[`../AXIOMS.md`](../AXIOMS.md), [`../CsdLean4/SigmaLayer/Adapters.lean`](../CsdLean4/SigmaLayer/Adapters.lean).
