# specs/ index — orientation map for plans, todos, and references

**Start here.** This indexes every planning / todo / reference doc in the corpus, with
one-line status. Updated 2026-06-08. When starting a session, read this first, then the
LIVE doc for the tranche you are on.

## Live (actionable) — pick up work here

| Doc | What it is | Status |
|---|---|---|
| [`carve-out-plan.md`](carve-out-plan.md) → **D1** | **The open frontier.** Exercise real measurement *dynamics* on `Σ`; the deepest structural debt, beneath A5. | **OPEN.** First physically-meaningful `Φ≠id` done 2026-06-05 (`LF4/ObservableFlow.lean`: the measured observable's Hamiltonian flow, measure-preserving, Born weights = its conserved quantities). **Remaining half = the measurement *event* (collapse), i.e. LF5 / measurement-update.** |
| [`povm-plan.md`](povm-plan.md) | **POVM tranche** (DONE 2026-06-03): the ontic Born derivation extended to general (non-projective) POVMs via Naimark dilation. | **CLOSED** — P.1–P.5 done (type, dilation + Born transfer, volume reading, frequency capstone, canonical-dilation existence); all foundational-triple-only, Gleason-free. P.6 docs done. |
| [`LF4-todo.md`](LF4-todo.md) | Ledger of items deferred from LF2/LF3 to LF4, numbered §1–§14, with bridge-discipline rules. | LIVE ledger. §14.2 done; general-N DH + LF3 re-route done (see header). Remaining items still open. |
| [`qm-empirical-tests.md`](qm-empirical-tests.md) | QM-validity regression-suite roadmap (Bell, no-cloning, teleportation, GHZ, Hardy, gates, crypto…). | LIVE. Many items done; E7/E91/BB84 + full no-broadcasting deferred (need fidelity/CPTP/LF5). |
| [`qi-qec-roadmap.md`](qi-qec-roadmap.md) | Forward roadmap for the QI / QEC / algorithm branches: the four keystone gaps (entropy, channels, fidelity, LF5), the QEC tranche, algorithms + stabilisation as operational faces of D1, and the project-structure decision (topics as subfolders under QM+CSD; infra → Mathlib staging; LF5 as a new layer). | LIVE plan. **K2 channels DONE** (C1–C4); **K3 trace-distance metric core DONE** (`TraceDistance.lean`; defs + nonneg + distinguishability + symmetry; triangle/data-processing deferred); QEC 3-qubit codes + bit-flip channel DONE. Remaining keystones: K1 entropy, K4/LF5, K3 deep theorems. |
| [`csd-departures-eft.md`](csd-departures-eft.md) | The "beyond reproducing QM" thread: candidate CSD-vs-QM departures (G3b → third-order/Sorkin interference, V≈1−I → complementarity, determinism → finite-sample statistics, finite-N), their physical-test handles, the CSD-specific negative tests, and the finite-EFT correction tower. | LIVE map. Theory-gated (corrections not pinned); leading order = QM is done, subleading owed by the paper sequence. |
| [`nqubit-register-plan.md`](nqubit-register-plan.md) | Plan for the **n-qubit register** + quantum-algorithm branch (Deutsch–Jozsa → QFT → Grover → Shor). `QReg n = EuclideanSpace ℂ (Fin n → Fin 2)`; Cat-1 in `Mathlib/QuantumInfo/Register.lean`, algorithms in `Empirical/QM/Algorithms/`. | **COMPLETE 2026-06-08.** R1–R5 + Grover done 2026-06-06; full Shor done 2026-06-07/08 → see [`shor-plan.md`](shor-plan.md). All AxiomAudit-pinned, foundational-triple-only. Coverage breadth, not the thesis. |
| [`shor-plan.md`](shor-plan.md) | Plan for **Shor's algorithm**, staged S1–S7 + assembly. In scope (finite QM + finite number theory, never field theory). | **COMPLETE 2026-06-08 — entire chain machine-checked end to end.** Quantum core (M1/M1.5/S4, `ShorCore.lean`), recovery (S5, `ShorRecovery.lean`), factoring + bridge (S6, `ShorRecovery.lean`), random-`a` success ≥ 1/2 for arbitrary odd composite `N` (S7 + S7-gen, `ShorRandomA.lean`), factoring capstone (`ShorCapstone.lean`). All foundational-triple-only, AxiomAudit-pinned, Tier-A-audited SOUND. Honest-scope deferrals (not load-bearing): constructive CF computation of `r`; two-register `r∤T` joint marginal. |
| [`trace-distance-triangle-plan.md`](trace-distance-triangle-plan.md) | Plan for the K3 trace-distance **triangle inequality** (= trace-norm subadditivity on Hermitian matrices), via the positive/negative-part decomposition + the TR-PSD linchpin (`0 ≤ Re Tr(S·P)` for PSD `S,P`), working with the `PosSemidef` predicate (Mathlib has no Loewner `≤`) and `IsHermitian.cfc` (defined for discontinuous `f`, dodging the `sgn` continuity gap). | **Planned, not started.** ~200–350 lines. Completes the metric core; the *data-processing* inequality is a separate, larger tranche. |
| [`channels-plan.md`](channels-plan.md) | The K2 CPTP-channel infrastructure plan (Kraus core → Stinespring dilation → canonical channels → no-comm CPTP / QEC error channel). Built on the existing `canonicalNaimark` + `PartialTrace` primitives; the on-ramp to `Φ≠id`. | **C1–C4 DONE 2026-06-05** (`QuantumInfo.Channel`; TP/PSD/Hermitian core; Kraus↔Stinespring bridge; `unitaryChannel`/`traceOutChannel`/`mixedUnitaryChannel`; `tensorRight` + `channel_no_communication` **retiring the E3 CPTP gap**; `bitFlipChannel` error channel; all AxiomAudit-pinned). Only C5 (full CP / data-processing, needs K3) remains, off critical path. |
| [`carve-out-plan.md`](carve-out-plan.md) | Carve-out diagnosis (Born = volume?) + the moment-map programme + the ontic-primitive (A5) / D1 frontier. | LIVE for the frontier (D1). Qubit Born-from-volume CLOSED; general-N superseded it (see in-file update). |

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
| [`../AXIOMS.md`](../AXIOMS.md) | Axiom posture: the two standing axioms (§2.1–§2.2), discharged ones (§2.3–§2.4), structural assumptions (§3, incl. A5/D1/V≈1−I), per-theorem audit (§5). |
| [`../CONVENTIONS.md`](../CONVENTIONS.md) | Three-category (Cat-1/2/3) discipline, naming, namespace rules. |
| [`../BRIDGE-OBLIGATIONS.md`](../BRIDGE-OBLIGATIONS.md) | Ledger of load-bearing Empirical/CSD bridge fields with LF4-todo cross-refs. |
| [`../PLACEHOLDERS.md`](../PLACEHOLDERS.md) | Placeholder / stub tracking. |

## Current state of the programme (one paragraph)

LF1–LF4 + Empirical merged and machine-verified. Born is **derived as the Fubini–Study
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
With POVMs and the algorithm branch closed, the **single open frontier is D1** (exercising
real measurement dynamics on `Σ`; `Φ = id` in every concrete sector instance today — see
`carve-out-plan.md`). Axiom posture is regression-protected by
`CsdLean4/Tests/AxiomAudit.lean` (`#guard_msgs` against `#print axioms`); build with
`lake build` + `lake build CsdLeanTests`.
