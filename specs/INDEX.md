# specs/ index — orientation map for plans, todos, and references

**Start here.** This indexes every planning / todo / reference doc in the corpus, with
one-line status. Updated 2026-06-02. When starting a session, read this first, then the
LIVE doc for the tranche you are on.

## Live (actionable) — pick up work here

| Doc | What it is | Status |
|---|---|---|
| [`carve-out-plan.md`](carve-out-plan.md) → **D1** | **The open frontier.** Exercise real measurement *dynamics* on `Σ` (`Φ = id` everywhere today); the deepest structural debt, beneath A5. | **OPEN — next session starts here.** |
| [`povm-plan.md`](povm-plan.md) | **POVM tranche** (DONE 2026-06-03): the ontic Born derivation extended to general (non-projective) POVMs via Naimark dilation. | **CLOSED** — P.1–P.5 done (type, dilation + Born transfer, volume reading, frequency capstone, canonical-dilation existence); all foundational-triple-only, Gleason-free. P.6 docs done. |
| [`LF4-todo.md`](LF4-todo.md) | Ledger of items deferred from LF2/LF3 to LF4, numbered §1–§14, with bridge-discipline rules. | LIVE ledger. §14.2 done; general-N DH + LF3 re-route done (see header). Remaining items still open. |
| [`qm-empirical-tests.md`](qm-empirical-tests.md) | QM-validity regression-suite roadmap (Bell, no-cloning, teleportation, GHZ, Hardy, gates, crypto…). | LIVE. Many items done; E7/E91/BB84 + full no-broadcasting deferred (need fidelity/CPTP/LF5). |
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
exactly **two** standing axioms (`invariant_measure_uniqueness`, `busch_effect_gleason`),
both spec-mandated; `busch_effect_gleason` is now confined to the **operational stratum**
— it is no longer in the ontic Born path for *either* projective or POVM measurements. With
POVMs closed, the **single open frontier is D1** (exercising real measurement dynamics on
`Σ`; `Φ = id` everywhere today — see `carve-out-plan.md`). Axiom posture is
regression-protected by `CsdLean4/Tests/AxiomAudit.lean` (`#guard_msgs` against
`#print axioms`); build with `lake build` + `lake build CsdLeanTests`.
