# Reconstruction status — a thorough review of what is machine-verified (2026-07-23)

**Purpose.** A single honest review of what the `csd-lean4` corpus actually proves, at commit `HEAD`
(after the Σ-layer (projective-sector, Paper C) and the honest-alignment closeout). It supersedes scattered
claims; where it and an older document disagree, this file and
[`connectivity-manifest.md`](connectivity-manifest.md) win. Everything below is `sorry`-free,
`lake build CsdLeanTests` green, and AxiomAudit-pinned to the foundational triple (`propext`,
`Classical.choice`, `Quot.sound`) unless explicitly noted otherwise.

> **The engine vs. the thesis — do not conflate them** (frame: [`CSD-CHARTER.md`](CSD-CHARTER.md)).
> 1. **The QM calculation engine, on a concrete projective witness** — Ω-region volume ratios → Born, the
>    T1–T16 inventory inhabited. This is what the Lean proofs deliver, and it is essentially complete. It is
>    the **consistency floor**, not the thesis. (Reproducing QM ≠ the achievement.)
> 2. **Completing the reconstruction** — making QM genuinely *arise from* Σ and Ω-regions on the ontic
>    surface, not accumulating more QM on the epistemic side. The record layer that does this is now
>    **formalized end-to-end** (2026-07-25, `record-layer-plan.md §4`): measurement = `context + unknown
>    microstate → record` on the base×fibre Σ, Born = the law of large numbers over the unknown microstate,
>    outcome probabilities = the Kähler moment map. See §7.
>
> The precise, defensible claim about the Lean today is:
>
> > The repository proves the finite-QM calculation engine on a concrete projective product witness satisfying
> > the exact formalised subset of the Paper C assumptions.
>
> It does **not** claim to *derive* projective geometry, μ_FS, or Schrödinger evolution from a more primitive
> model — those are **built into** the witness. And **Σ is the floor and is everything; deriving Σ is a
> non-question**, not an open goal.

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
derivations of `μFS` or of unitary evolution from a fibre-primitive ontology. **This closure is the QM
*calculation engine* demonstrated — the consistency floor, not the thesis** (see [`CSD-CHARTER.md`](CSD-CHARTER.md)).
**Σ is the floor and is everything; deriving it is a non-question** (Paper C is explicitly "a reconstruction,
not a derivation"). The goal — **complete the reconstruction of QM from Σ and Ω-regions** — is met: the
**record layer (MD-1)** is now formalized end-to-end in Lean (2026-07-25, `record-layer-plan.md §4`), on
the base×fibre ontic space Σ, with Born = the law of large numbers over the unknown microstate and the
outcome probabilities = the Kähler moment map. The only residue is a mechanical field naming in the pinned
closure (no new theorem). (The Ω-regions are epistemic, on `ℂℙⁿ⁻¹`; the record is the ontic selection in Σ.)
The earlier "SO-1 = derive the sector" framing that appeared here is a **retired error** (§7).

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
| **A7** context-defined measurement partitions | **Addressed by the record layer (MD-1, built 2026-07-25 — `record-layer-plan.md §4`); ★ QUBIT FAITHFULNESS DISCHARGED 2026-07-26.** The record layer formalizes measurement as `context + unknown microstate → record` on the base×fibre Σ, with outcome probabilities = the Kähler moment map (`MomentMapRace`, forced not injected) and frequencies = the LLN over the unknown microstate (`Measurement.bornMeasurement_frequency`). **The A7 residual — that the epistemic partition be genuinely *context-fixed* (a function of the measurement context alone, not the preparation, rather than the corpus's preparation-indexed `bornRegion ψ`) — is now discharged for the qubit** (`LF4/QubitBorn.lean` `qubitBorn`, foundational-triple, pinned): the hemisphere partition `{H±(n)}` depends only on the axis `n`, and the Born weight `|⟨n\|ψ⟩|²` is *derived* from the ontic Fubini–Study typicality volume via the CSD spread density `4(2·blochProj ψ − 1)₊`. The 7-module `CP¹` chain (`QubitReflection`→`BlochProjection`→`AxisBridge`→`QubitDipole`→`QubitCrossTerm`→`QubitBorn`, + `HatBox`) is `record-layer-plan.md §2/§4`. Remaining: the general-`N` context-fixed partition — and here we learned a **structural fact about Σ** ([`sigma-fibre-contextuality.md`](sigma-fibre-contextuality.md)): a base-only, `U(N)`-covariant, nonnegative context-fixed density **cannot** reproduce Born for `N ≥ 3` (proven numerically + operator-theoretically; the `CP¹=S²` antipode has no analogue — and this is **not** Gleason, CSD being contextual). For `N ≥ 3` the contextuality necessarily lives in the **fibre** of Σ (a Born fibre-partition exists — Phase-2b Gumbel/softmax); deriving that mechanism from a de-isolation dynamics is the open frontier. So A7-as-base-regions is a qubit accident, not the general form. The pinned `FiniteQMClosure` field still names the preparation-indexed `bornRegion ψ'` cells (a mechanical residue; `KSigmaRecord.born_frequency_region_eq_record` shows its region already *is* the record-layer event). |

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

*(Actionable open items in [`BACKLOG.md`](BACKLOG.md); the mission frame in [`CSD-CHARTER.md`](CSD-CHARTER.md).)*

**Framing (read first).** **Σ is the floor and is everything** — deriving it is a *non-question*, not an open
problem. QM (the T1–T16 inventory in §2a) is the **calculation engine** the Ω-region/volume-ratio structure
computes. The goal now is to **complete the reconstruction of QM from Σ and Ω-regions** — QM genuinely
*arising from* the ontic surface, not accumulated on the epistemic side.

* **The record layer (MD-1) — the KINEMATIC interface is BUILT (2026-07-25), formalized end-to-end;
  MD-1 itself is NOT discharged.** ⚠️ *Corrected 2026-07-28 (external review): the partition is
  preparation-indexed, so general-`N` A7 is open (`N=2` is done, `LF4/QubitBorn.lean`); the
  de-isolation Hamiltonian is not constructed (`DeIsolationInteraction.basin_rate` is a hypothesis
  field); and the fibred Σ below is a measurable record model, not a proven A1 ontic sector.*
  Measurement = de-isolation, on
  the model space **Σ = base × fibre** (`SigmaLayer/FibredSigma.lean`): the **base** `CPN n` is
  the *epistemic* projective point (pinned to `[ψ]` for a sharp prep), the **fibre** carries the *ontic*
  record coordinate. The measurement is `context + unknown microstate → record` (`SigmaLayer/Measurement.lean`):
  the context fixes the basin partition, the unknown microstate selects the basin it occupies, and the
  combined result is the P5 `RecordSemantics` record (`SigmaLayer/FibreRecord.lean`,
  `SigmaLayer/ProjectiveRecord.lean`). The outcome probabilities are the **Kähler torus moment map**
  (`SigmaLayer/MomentMapRace.lean`, `bornRate_eq_momentMap` — forced by the geometry, not injected), and
  the frequencies are the **law of large numbers over the unknown initial microstate**
  (`Measurement.bornMeasurement_frequency`, `ProjectiveRecord.projRecord_frequency` — no dynamical
  postulate; randomness = ignorance of the initial condition). This is realized on the corpus's actual Σ:
  `KSigmaRecord.born_frequency_region_eq_record` proves the region `FiniteQMClosure.born_frequency` lands
  in **is definitionally the record-layer event**. Arbitrary observables via `SigmaLayer/BasisMeasurement.lean`.
  All foundational-triple, no `sorry`, axiom-pinned. **Only residue:** the pinned
  `unifiedFiniteQMClosure.records_time_physical` field still *names* the coarse `vnPointerOutcome` (a
  block-sum of these events); rewriting it carries no new theorem. See `record-layer-plan.md §4`.

**Constraining Σ (legitimate — *not* deriving it).** Σ is the floor (deriving it is a non-question), but it
is not directly seen, so **constraining its structure as tightly as possible — from above, from what it must
do — is valuable work**: the more forced/less arbitrary the hidden substrate, the stronger the theory. The
structure-forcing results are exactly this. μ_FS is the **unique** SU(n)-compatible measure (Paper B),
realized in Lean by `fubiniStudy_forced_by_symmetry` / `LocalisedTypicality.lean`
(`region_measure_symmetry_forced`) — so Σ's typicality measure is *forced*, not chosen. The companion no-go
(`SectorPostulateNoGo.lean`, `flow_admits_invariant_ne_fubiniStudy`) records only that a single *epistemic
unitary* flow does not time-average to μ_FS — expected, and irrelevant to CSD's mechanism (typicality is
repeated-preparation ignorance over `Ω₀` on Σ, not epistemic time-averaging). These are **constraint work on
Σ** — pinning the hidden substrate down — not a *research frontier*, and NOT the retired
"derive Σ / SO-1 / L7 Born-from-flow" non-question.

**Remaining formalization gaps (engine-level, not the thesis):**

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

* **NG1 — CORRECTED 2026-07-24 (the earlier wording was wrong and misleading).** Do **not** call the
  single-trajectory / deterministic-flow account a route "CSD rejects" — **CSD *is* a single-trajectory
  theory** (Paper D §4.2: physical reality is one trajectory `ω(t)` on Σ). What *is* a proved dead-end is
  time-averaging one infinite *epistemic unitary* trajectory on `ℂℙⁿ⁻¹` (`obsFlow_not_ergodic` /
  `obsFlow_not_uniquely_ergodic`, `LF4/TypicalityForcing.lean`; `flow_admits_invariant_ne_fubiniStudy`,
  `SigmaLayer/SectorPostulateNoGo.lean`), so building out the epistemic ergodic scaffolding
  (`SigmaLayer/UniqueErgodicity.lean`, `BornFromFlow`, `IsErgodicForOutcomeRegions`) is **not progress**.
  CSD's typicality is **repeated-preparation ignorance over the prepared region `Ω₀` on Σ** (Paper D, "Note on
  repeated preparations"; classical-statistical-mechanics style) — each experiment is one trajectory;
  statistics come from not knowing the exact microstate in `Ω₀`. That is neither time-averaging one epistemic
  trajectory nor "fresh i.i.d. preparations *instead of* single-trajectory." Do not round the narrow
  epistemic-`ℂℙ` no-go up to a rejection of the ontology, and do not treat "deriving Σ" as the residue
  (Σ is the floor — a non-question).
* **NG2 — the Busch effect-Gleason axiom is NOT needed for CSD's core claim; discharging it is
  cosmetic.** CSD's ontic Born rule is **Gleason-free**: it is a Fubini–Study / Duistermaat–Heckman
  *volume* (`bornRegion_fs_measure`, `born_frequency_convergence_N`). The former axiom
  `busch_effect_gleason` entered only the **operational effect/POVM stratum**, off the reconstruction path.
  It was **proved in-repo 2026-07-21** (`OperationalPackage.effect_gleason_representation`), taking the
  imported-axiom count to zero — an **audit-posture** improvement, NOT a strengthening of the CSD
  reconstruction.

## 8. Bottom line

The corpus proves the **QM calculation engine on a concrete projective witness** — the *consistency floor*:
the full T1–T16 target inventory inhabited, axiom-clean, Born = Ω-region volume ratio, on one witness model
with μ_FS and `exp(-itH)` built in. **Σ is the floor and is everything; deriving it is a non-question.** The
goal now is to **complete the reconstruction of QM from Σ and Ω-regions** — making QM genuinely *arise from*
the ontic surface. The **record layer** (MD-1) is now **formalized in Lean** (2026-07-25; see §7): measurement as
`context + unknown microstate → record` on the base×fibre Σ, Born = the law of large numbers over the
unknown microstate, outcome probabilities = the Kähler moment map. The residual MD-1 item is making the
*pinned closure's* regions context-fixed (it still names the preparation-indexed `bornRegion ψ'`). The
genuine near frontier is now the **extensions** — continuous spectra (CV), relativistic locality,
identical particles. (The earlier "SO-1 = derive the sector, the central frontier" framing is a retired
error — §7.)

References: [`connectivity-manifest.md`](connectivity-manifest.md), [`future-work.md`](future-work.md),
[`../AXIOMS.md`](../AXIOMS.md), [`../CsdLean4/SigmaLayer/Adapters.lean`](../CsdLean4/SigmaLayer/Adapters.lean).
