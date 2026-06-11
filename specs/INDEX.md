# specs/ index — orientation map for plans, todos, and references

**Start here.** This indexes every planning / todo / reference doc in the corpus, with
one-line status. Updated 2026-06-11. When starting a session, read this first, then the
LIVE doc for the tranche you are on.

## Live (actionable) — pick up work here

| Doc | What it is | Status |
|---|---|---|
| [`carve-out-plan.md`](carve-out-plan.md) → **D1** | **The open frontier.** Exercise real measurement *dynamics* on `Σ`; the deepest structural debt, beneath A5. | **OPEN at the deeper strata.** `Φ≠id` (non-collapse) done 2026-06-05 (`LF4/ObservableFlow.lean`); collapse semantics DECIDED 2026-06-09 (§6: the de-isolation reading); **the measurement-event half is now exercised at the single-system projective tier — LF5 COMPLETE 2026-06-11** (`measurement_flow_born_frequency`). Remaining: entangled/non-local de-isolation, the per-microstate outcome map (gated on `bornRegion` pairwise disjointness), A5 sector origin, `SectorData` instances still `Φ = id`. |
| [`lf5-plan.md`](lf5-plan.md) | Staged plan for **LF5 (measurement dynamics, the D1 frontier)**: realise a projective measurement as a measure-preserving von Neumann de-isolation flow `Φ_vN ≠ id` on the joint `ℂℙ^{N·N−1}`, pointer regions = `blockProj` (apparatus basis, context-fixed), committed volume = Born, chained to frequencies. **Heavily reuses the POVM Naimark tranche** (block-Born = FS-volume already proved); the genuine new content is realising the static dilation isometry as a dynamical flow. | **COMPLETE 2026-06-11.** LF5-A (vN unitary, 06-09); LF5-B (measurement flow `Φ_vN ≠ id`, FS-preserving, 06-10); LF5-C (de-isolation realises the dilation: `vnNaimark`, flow carries `[ψ⊗a₀] ↦ [Vψ]`, 06-11); LF5-D (the **unconditional engine** `LF4/BornRegionUncond.lean` — retires the `hpos` genericity of the general-`N` + POVM engines, additively — + `vnDilation_pointer_volume` / `vnDilation_pointer_frequency`, 06-11); LF5-E (capstone, 06-11): **layer headline `measurement_flow_born_frequency`** (`LF5/Capstone.lean`) — `Φ_vN ≠ id` + FS-preserving + dilation realised ∀ preparations + pointer-block volume = Born + a.s. frequencies → Born, every unit `ψ`. All foundational-triple-only, AxiomAudit-pinned, Tier-A audited SOUND. Remaining D1 strata: entangled/non-local tier, per-microstate outcome map (`bornRegion` disjointness), A5. |
| [`povm-plan.md`](povm-plan.md) | **POVM tranche** (DONE 2026-06-03): the ontic Born derivation extended to general (non-projective) POVMs via Naimark dilation. | **CLOSED** — P.1–P.5 done (type, dilation + Born transfer, volume reading, frequency capstone, canonical-dilation existence); all foundational-triple-only, Gleason-free. P.6 docs done. |
| [`LF4-todo.md`](LF4-todo.md) | Ledger of items deferred from LF2/LF3 to LF4, numbered §1–§14, with bridge-discipline rules. | LIVE ledger. §14.2 done; general-N DH + LF3 re-route done; §2 done for pure states. ⏸ **§13 Wigner-rigidity programme PAUSED 2026-06-09 at the (2c-iii) phase-cocycle crux** — `transProb` API + `TransProbPreserving` + injectivity + frame reduction (`reducedMap` fixes basis rays) all built/audited SOUND in `Mathlib/.../Projectivization/{TransitionProbability,WignerRigidity}.lean`; residual = one Wigner normal-form lemma; decision deferred (full proof vs `wigner_fs_rigidity` axiom). See §13 banner. Other items still open. |
| [`qm-empirical-tests.md`](qm-empirical-tests.md) | QM-validity regression-suite roadmap (Bell, no-cloning, teleportation, GHZ, Hardy, gates, crypto…). | LIVE. Many items done; E7/E91/BB84 + full no-broadcasting deferred (need fidelity/CPTP/LF5). |
| [`qi-qec-roadmap.md`](qi-qec-roadmap.md) | Forward roadmap for the QI / QEC / algorithm branches: the four keystone gaps (entropy, channels, fidelity, LF5), the QEC tranche, algorithms + stabilisation as operational faces of D1, and the project-structure decision (topics as subfolders under QM+CSD; infra → Mathlib staging; LF5 as a new layer). | LIVE plan. **K2 channels DONE** (C1–C4); **K3 trace-distance metric COMPLETE** (`TraceDistance.lean`; defs + nonneg + distinguishability + symmetry + **triangle inequality** done 2026-06-08; only the data-processing inequality deferred); QEC 3-qubit codes + bit-flip channel DONE. **K3 COMPLETE 2026-06-09** — metric (triangle) + **data-processing inequality** (`channel_traceDist_le`, via the channel adjoint `Φ.adjoint` + variational characterisation) + closers (`traceDist_le_one` bounded `[0,1]`; `traceDist_conj_unitary` unitary invariance); all in `DataProcessing.lean`, Tier-A audited SOUND. Remaining keystones: K1 entropy, K4/LF5. |
| [`csd-departures-eft.md`](csd-departures-eft.md) | The "beyond reproducing QM" thread: candidate CSD-vs-QM departures (G3b → third-order/Sorkin interference, V≈1−I → complementarity, determinism → finite-sample statistics, finite-N), their physical-test handles, the CSD-specific negative tests, and the finite-EFT correction tower. | LIVE map. Theory-gated (corrections not pinned); leading order = QM is done, subleading owed by the paper sequence. |
| [`nqubit-register-plan.md`](nqubit-register-plan.md) | Plan for the **n-qubit register** + quantum-algorithm branch (Deutsch–Jozsa → QFT → Grover → Shor). `QReg n = EuclideanSpace ℂ (Fin n → Fin 2)`; Cat-1 in `Mathlib/QuantumInfo/Register.lean`, algorithms in `Empirical/QM/Algorithms/`. | **COMPLETE 2026-06-08.** R1–R5 + Grover done 2026-06-06; full Shor done 2026-06-07/08 → see [`shor-plan.md`](shor-plan.md). All AxiomAudit-pinned, foundational-triple-only. Coverage breadth, not the thesis. |
| [`shor-plan.md`](shor-plan.md) | Plan for **Shor's algorithm**, staged S1–S7 + assembly. In scope (finite QM + finite number theory, never field theory). | **COMPLETE 2026-06-08 — entire chain machine-checked end to end.** Quantum core (M1/M1.5/S4, `ShorCore.lean`), recovery (S5, `ShorRecovery.lean`), factoring + bridge (S6, `ShorRecovery.lean`), random-`a` success ≥ 1/2 for arbitrary odd composite `N` (S7 + S7-gen, `ShorRandomA.lean`), factoring capstone (`ShorCapstone.lean`). All foundational-triple-only, AxiomAudit-pinned, Tier-A-audited SOUND. Honest-scope deferrals (not load-bearing): constructive CF computation of `r`; two-register `r∤T` joint marginal. |
| [`trace-distance-triangle-plan.md`](trace-distance-triangle-plan.md) | Plan for the K3 trace-distance **triangle inequality** (= trace-norm subadditivity on Hermitian matrices), via the positive/negative-part decomposition + the TR-PSD linchpin (`0 ≤ Re Tr(S·P)` for PSD `S,P`), working with the `PosSemidef` predicate (Mathlib has no Loewner `≤`) and `IsHermitian.cfc` (defined for discontinuous `f`, dodging the `sgn` continuity gap). | **DONE 2026-06-08.** `traceNorm_add_le` + `traceDist_triangle` landed (metric complete), foundational-triple-only, AxiomAudit-pinned, Tier-A-audited SOUND. Jordan primitives `posPart`/`negPart`/`posProj` exposed for reuse. Remaining K3: the *data-processing* inequality (separate, larger tranche; its load-bearing half is already built here). |
| [`channels-plan.md`](channels-plan.md) | The K2 CPTP-channel infrastructure plan (Kraus core → Stinespring dilation → canonical channels → no-comm CPTP / QEC error channel). Built on the existing `canonicalNaimark` + `PartialTrace` primitives; the on-ramp to `Φ≠id`. | **C1–C4 DONE 2026-06-05** (`QuantumInfo.Channel`; TP/PSD/Hermitian core; Kraus↔Stinespring bridge; `unitaryChannel`/`traceOutChannel`/`mixedUnitaryChannel`; `tensorRight` + `channel_no_communication` **retiring the E3 CPTP gap**; `bitFlipChannel` error channel; all AxiomAudit-pinned). The **channel adjoint** `Φ.adjoint` (unital, positive, duality `Tr(P·Φρ)=Tr(Φ†P·ρ)`) landed 2026-06-09 with the K3 data-processing inequality; full CP / Choi-positivity (C5) remains, off critical path. |
| [`carve-out-plan.md`](carve-out-plan.md) | Carve-out diagnosis (Born = volume?) + the moment-map programme + the ontic-primitive (A5) / D1 frontier. | LIVE for the frontier (D1). Qubit Born-from-volume CLOSED; general-N superseded it (see in-file update). |
| [`audit-sweep-plan.md`](audit-sweep-plan.md) | Extend the adversarial audit **below the Tier-A headlines**: per-module csd-lean-auditor gap sweeps over the Tier-B-and-below strata (supporting lemmas, Cat-1 staging tree, bridge bundles), with a running per-sweep ledger. | **Planned 2026-06-10, not started.** Sweep order: Mathlib staging → LF2/LF3 support → LF4 non-headline → Empirical/bridges → LF1. |

## Done / historical (context, mostly closed)

| Doc | What it is | Status |
|---|---|---|
| [`general-n-dh-plan.md`](general-n-dh-plan.md) | General-N Duistermaat–Heckman / Born-from-Kähler-volume plan (Slices A–E). | **CLOSED 2026-06-02.** Headline + Born lift + apex + empirical capstone + N=2 reduction all done. |
| [`plan-b-detail.md`](plan-b-detail.md) | Plan B: discharge the qubit DH axiom `fs_moment_pushforward_uniform` (Gaussian + FS-uniqueness route). | CLOSED 2026-05-31 (axiom is now a theorem). |
| [`partial-trace-plan.md`](partial-trace-plan.md) | Partial-trace Cat-1 tranche (`PartialTrace.lean`, reduced density). | DONE. Tooling now feeds the POVM tranche. |
| [`pre-LF4-plan.md`](pre-LF4-plan.md) | Pre-LF4 plan: option-(B) chain design, the PureSingletPreparation bundle. | DONE (note: the chain was re-routed off Busch 2026-06-02; this doc describes the older Busch-mediated form). |
| [`LF1-plan.md`](LF1-plan.md), [`LF2-plan.md`](LF2-plan.md), [`LF3-plan.md`](LF3-plan.md) | Per-layer construction plans. | DONE (LF1/LF2/LF3 all merged + verified). |
| [`projectivization-plan.md`](projectivization-plan.md) | Mathlib-staging plan for the `Projectivization` topology/measure API. | DONE (the `CsdLean4/Mathlib/` staging tree). |
| [`empirical-csd-bridge-plan.md`](empirical-csd-bridge-plan.md) | Discipline for `Empirical/CSD/` bridge files (load-bearing-hypothesis rules). | LIVE discipline doc; see `../BRIDGE-OBLIGATIONS.md` for the ledger. |

## Reference (not todos)

| Doc | What it is |
|---|---|
| [`expert-system-prompt.md`](expert-system-prompt.md) | The project's expert-posture / system-prompt reference. |
| [`spec-to-lean.md`](spec-to-lean.md) | Spec-to-Lean mapping notes. |
| [`../README.md`](../README.md) | Authoritative status overview (layers, theorem tables, axiom posture). |
| [`../EMPIRICAL.md`](../EMPIRICAL.md) | Per-test index of the empirical suite (both branches: file, headline theorem, claim, source). |
| [`../CLAUDE.md`](../CLAUDE.md) | Working-with-the-code guide (architecture, conventions, module chains). |
| [`../AXIOMS.md`](../AXIOMS.md) | Axiom posture: the one standing axiom (`busch_effect_gleason`, §2.2; `invariant_measure_uniqueness` removed 2026-06-04, §2.1), discharged ones (§2.3–§2.4), structural assumptions (§3, incl. A5/D1/V≈1−I), per-theorem audit (§5). |
| [`../CONVENTIONS.md`](../CONVENTIONS.md) | Three-category (Cat-1/2/3) discipline, naming, namespace rules. |
| [`../BRIDGE-OBLIGATIONS.md`](../BRIDGE-OBLIGATIONS.md) | Ledger of load-bearing Empirical/CSD bridge fields with LF4-todo cross-refs. |
| [`../PLACEHOLDERS.md`](../PLACEHOLDERS.md) | Placeholder / stub tracking. |

## Current state of the programme (one paragraph)

LF1–LF5 + Empirical merged and machine-verified. Born is **derived as the Fubini–Study
typicality volume** on the ontic `Σ = ℂℙ^{N-1}` for general `N`, Gleason-free, and the
LF3 empirical chain runs on that derivation. The **POVM tranche is closed** (2026-06-03):
the ontic Born derivation now covers general (non-projective) measurements via the
canonical Naimark dilation — `povm_born_frequency_volume` lands the POVM Born weight as a
sum of FS volumes on a dilated `Σ'`, unconditionally and Gleason-free. The corpus has
exactly **one** standing axiom (`busch_effect_gleason`); `invariant_measure_uniqueness` was
**removed 2026-06-04** (the abstract bridge it served was unused; the concrete `ℂℙ^{N-1}`
uniqueness is a proved theorem). `busch_effect_gleason` is confined to the **operational
stratum** — it is no longer in the ontic Born path for *either* projective or POVM
measurements. The **quantum-algorithm branch** (Deutsch–Jozsa, QFT, Grover, full Shor) is
**complete 2026-06-08** — coverage breadth, foundational-triple-only, Tier-A-audited SOUND.
The **LF5 measurement-dynamics layer is complete** (2026-06-11, single-system projective
tier): the layer headline `measurement_flow_born_frequency` chains the de-isolation flow
`Φ_vN ≠ id` (FS measure-preserving) through the dynamically-realised Naimark dilation to
pointer-block volumes = Born and a.s. frequencies → Born, for every unit preparation (the
engine's `hpos` genericity retired by `LF4/BornRegionUncond.lean`). The **open frontier is
D1's deeper strata** (entangled/non-local de-isolation; the per-microstate outcome map,
gated on `bornRegion` pairwise disjointness; the A5 sector origin; the concrete `SectorData`
instances still carry `Φ = id` — see `carve-out-plan.md` §6). Axiom posture is
regression-protected by
`CsdLean4/Tests/AxiomAudit.lean` (`#guard_msgs` against `#print axioms`); build with
`lake build` + `lake build CsdLeanTests`.
