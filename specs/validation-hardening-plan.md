# Validation hardening: warnings-as-errors, the concrete-witness suite, and CI depth

Adopted 2026-08-12. Campaign doc for the validation-hardening work order (user-supplied
plan, amended per the pre-dispatch review). Run in gated phases, C1-campaign style:
each phase lands green with its own commit(s); a phase is not "done" until both targets
build `--wfail`-clean and every blocking guard passes. **A row in the status table
flips to DONE in the same commit as its landing, never before** (the B1b staleness
lesson, in both directions).

**What this campaign is, foundationally.** This is *validation machinery* — it narrows
the trust gap on the **sufficiency/inhabitation leg**: the corpus's assumption packages
(`OnticSetup`, `SectorData`, `TrialModel`, `PureSingletPreparation`, …) have explicit,
nontrivial inhabitants, and those inhabitants drive the actual headline theorem chains.
It is **not** reconstruction progress and must never be sold as such (witness ≠ result;
see the necessity audit, 2026-08-09: the conditionality gap is a *different* gap, and
adding witnesses does not narrow it). No claim in `validation-claims.tsv`, no README
headline, no landing-surface edit arises from this campaign.

## Baseline (recorded 2026-08-12, HEAD `56ca11d`)

* `lake build CsdLean4` — green, 4001 jobs.
* `lake build CsdLeanTests` — green, 4012 jobs.
* `lake build --wfail` on both targets — **green already** (the corpus is
  warning-clean; the only replayed diagnostics are `info:`-level `#eval` outputs in
  `Mathlib/QuantumInfo/Reversible/` and two `Try this:` notes in
  `SigmaLayer/ShearWitness.lean`).
* All 12 blocking guards PASS: module-coverage, validation-ledger, semantic-mutations,
  connectivity, sector-linkage, axiom-imports, claims, claim-provenance, citation-use,
  axiom-sweep, import-negative, guards.

## Standing rules (binding for every phase)

1. No new axioms, no `sorry`, no placeholder scaffolding (CLAUDE.md mandatory rule).
   A walled witness is reported honestly as a blocker row here, never stubbed.
2. **Anti-duplication (the rule 5 discipline):** a witness module *instantiates and
   applies* production theorems through their public interfaces. It never restates,
   re-proves, or shadows a production theorem, and it never adds parallel mathematics.
   Production non-vacuity theorems (`*_nonvacuous`, `isJointLift_pointerEvolve`, …)
   are *cited*, not re-derived.
3. Witness modules live under `CsdLean4/Tests/Witnesses/` (CsdLeanTests target only —
   never in the production dependency graph). Their headline constructions get axiom
   pins in `Tests/AxiomAudit/Witnesses.lean` (precedent: the `Incubator` part).
4. **Every new blocking guard gets a permanent mutation case in `check-guards.sh`** —
   the repo's standing watch-the-watchmen mechanism — not a one-off hand test recorded
   in a report. (`--wfail` is lake's own mechanism and is exempt; its mutation test is
   run once, by hand, and recorded below when run.)
5. Scientific theorem statements are not altered to make tests easier.
6. Doc-currency: `specs/INDEX.md` row + this file's status table updated in the same
   commit as each landing.

## Workstreams and status

Order of implementation: A → B → E+H → I → C → D → F+G → J → K → L → M → N → O.
(E+H and I precede the routine LF examples because they exercise the most
scientifically load-bearing structures; C may need to precede E+H if the honest
i.i.d. infrastructure turns out to be shared.)

| # | Workstream | Amendments from the pre-dispatch review | Status |
|---|---|---|---|
| A | Warnings-as-errors (`--wfail` both targets in CI) | none — verified nearly free at baseline | **DONE 2026-08-12** — ci.yml: `--wfail` on both build steps; mutation-tested (see record below) |
| B | Witness framework skeleton (`Tests/Witnesses/` + umbrella + AxiomAudit part) | Anti-duplication rule in the umbrella docstring; new `Tests/AxiomAudit/Witnesses.lean` part | **DONE 2026-08-12** — umbrella + lakefile root + pin part (7 pins, all foundational-triple), landed non-empty (with C and J) |
| E+H | LF3 singlet/Bell witness (priority) | Build on the C1 tranche (`C1BellConsistency` → `lhvCHSH_abs_le_two`; `compatibleGlobalCHSH_nonvacuous`); may share i.i.d. infrastructure with C | **DONE 2026-08-12** — `Witnesses/SingletBell.lean`: `perpContext` (a = ẑ, b = x̂; `P_st = ¼` computed, `hgen` **discharged**), the chain capstone on the fully concrete model with honest `infinitePi` trials (`perpContext_singlet_frequency_convergence` → ¼ a.s.), setting-dependence nontriviality, and the C1 CHSH obstruction + non-vacuity instantiated on the same arena `(KSigma 4, kMuPsi)`. The shared-i.i.d. prediction held: C's infrastructure carries E's trials |
| I | Composite nonfactorisation witness | Cite, don't construct (`no_product_partition_realises_singlet`, GHZ chain) | **DONE 2026-08-12** — `Witnesses/Composite.lean`: the partition-level obstruction (where CSD's composite claim lives) instantiated on `(KSigma 4, kMuPsi)` + non-vacuity + the GHZ tripartite analogue on `(ℂℙ⁷, μ_FS)`. A Hilbert-level `singlet ≠ u ⊗ v` lemma deliberately NOT added (would be parallel QM-side mathematics; scope note in-module) |
| C | LF1 honest i.i.d. `TrialModel` | Check `Measure.infinitePi` on the pinned Mathlib **before** declaring a wall (check-impossible-first); if walled, document the exact missing upstream theorem here — never an axiom | **DONE 2026-08-12** — NOT walled: `Measure.infinitePi` + `iIndepFun_infinitePi` are on the pin. `Witnesses/IIDSampling.lean` (the honest model for **every** `OnticSetup`, `hindep` a theorem) + `Witnesses/LF1Trial.lean` (`coinTrialModel`, weight = ½ from Liouville volumes, convergence to ½). Examples.lean's stale "Mathlib-substantial" caveat superseded at source |
| D | LF2 bridge witness | The targets are the G1 transport theorems (`MeasureBridgeData.integral_comp_pi`, `OperationalPackage.fromPreparation_liouville_apply`, CL-003-guarded) | **DONE 2026-08-12** — `Witnesses/LF2Bridge.lean`: both transport theorems consumed on the concrete `kBridge p₀` (`c = 1`, `hc` by `rfl`): ontic-to-projective integral transport, the Liouville operational form, `c ≠ 0` nontriviality, and the Born endpoint `‖⟨ψ, φ⟩‖²` via the production `born_rank_one_direct` at `kPurePrep` |
| F+G | LF4 operational (mixed state / POVM / partial trace) + LF5 sequential witnesses | Invoke existing LF4/LF5 surfaces, never reimplement | **DONE 2026-08-12** — F: `Witnesses/Operational.lean` (`mixedHalf` = ½·I as a proved `DensityOperator`, ≠ `|0⟩⟨0|` by entry; `weakPOVM` at η = ½ exercised: weights sum to 1 + strictly-between unsharpness; `plusVec` reduction: trace 1 + purity < 1 — pure entangled composite, properly mixed marginal). G: `Witnesses/Sequential.lean` (repeatability on the concrete superposition `[e₀+e₁]` through the production Lüders update: first outcome hpos **discharged** at a non-vertex preparation, repeat = 1, others = 0) |
| J | Dynamics witness | **Cite the existing production flows** (`kSectorDataFlow`, `cpSectorDataFlow`, `rotationSetup`, …) — D1c discharged this 2026-06-29; construct nothing | **DONE 2026-08-12** — `Witnesses/Dynamics.lean`: `exists_cp/kSectorData_nontrivial_flow` (inhabited existentials, every clause a named production theorem), `qubit_dynamics_witness` (concrete `N = 2`), `cpSectorDataFlow_frequency_convergence_concrete` (production capstone on honest `infinitePi` trials). ⚠️ Snag for the ledger: applying the capstone with an **unannotated** sample lambda put unification under metas and whnf-exploded (same class as the B3b/B5-geom notes); fix = pin `(Ω := …) (Pr := …)` and annotate the lambda — normal heartbeats after |
| K | Standard linter integration | Baseline-first per the §9.5 ratchet; F3 naming decisions on the documented-exclusions list from day one; advisory unless zero-churn | queued |
| L | Import hygiene guard | Extend the `check-import-negative.sh` idiom; permanent mutation cases in `check-guards.sh` | queued |
| M | Forward-compat workflow | **Tagged Mathlib releases only** (cache hits); nothing committed to lakefile.toml | queued |
| N | Docs smoke workflow | Manual/scheduled; representative-page checks; failure visible | queued |
| O | macOS platform build (optional, last) | Does not contradict G7 (Windows dropped because local dev covers it; macOS is uncovered) | queued |

## Witness coverage (deliverable table — a row appears here only when it is green)

| Layer | Explicit witness | Nontriviality | Headline theorem exercised |
|---|---|---|---|
| LF1 | `coinTrialModel` (`Witnesses/LF1Trial.lean`) — honest i.i.d. product on `ℕ → Bool` via `Measure.infinitePi`, coordinate trials, every `TrialModel` field proved | weight = ½ (`headsOutcome_weightReal`, from `weight_eq_prepEvent_div`), `coin_witness_nontrivial`: ∉ {0, 1} | `LF1_main_theorem_ae` via `iidTrialModel_frequency_convergence` — zero abstract hypotheses |
| LF1 (generic) | `iidTrialModel` (`Witnesses/IIDSampling.lean`) — the honest trial model for **every** `OnticSetup`; `hindep` discharged by `iIndepFun_infinitePi` | law + independence are Mathlib theorems, not posits | `LF1_main_theorem_ae`, all setups |
| Dynamics | `exists_cp/kSectorData_nontrivial_flow`, `qubit_dynamics_witness` (`Witnesses/Dynamics.lean`) — production `cpSectorDataFlow`/`kSectorDataFlow` cited, nothing constructed | `Φ ≠ id` (production `obsFlow_ne_id`/`kFlow_ne_id`); concrete shift `(½, 0) ≠ 0` proved | `cpSectorDataFlow_frequency_convergence` on honest `infinitePi` trials (`_concrete`) |
| LF3 (singlet) | `perpContext` + `ofKählerPreparation` at it (`Witnesses/SingletBell.lean`) — concrete sector, preparation, context; `hgen` discharged (`P_st = ¼` computed) | `P_st_setting_dependent` (parallel axes give 0 ≠ ¼); all four weights ∉ {0, 1} | `LF3_singlet_frequency_convergence` via `ofKählerPreparation_singlet_frequency_convergence`, honest trials → ¼ a.s. |
| LF6/Bell | `kMuPsi_no_global_chsh_assignment` + `kMuPsi_chsh_obstruction_nonvacuous` on `(KSigma 4, kMuPsi)` | obstruction populated (compatible families exist, correlation 1) — a genuine separation | `no_compatible_global_chsh_assignment_realises_singlet` (→ `lhvCHSH_abs_le_two`), `compatibleGlobalCHSH_nonvacuous` |
| Composite | `kMuPsi_no_product_partition` (+ non-vacuity) on `(KSigma 4, kMuPsi)`; `fs_no_product_partition_ghz` on `(ℂℙ⁷, μ_FS)` | partition-level: product partitions exist but cannot reproduce the singlet/GHZ — nonfactorisation forced, not assumed | `no_product_partition_realises_singlet`, `productPartition_nonvacuous`, `no_product_partition_realises_ghz` |
| LF2 | `kBridge p₀` consumed (`Witnesses/LF2Bridge.lean`) | `c = 1 ≠ 0`; the transport is extensional (`bridge_eq` fires), not type-level | `MeasureBridgeData.integral_comp_pi`, `fromPreparation_liouville_apply`, `born_rank_one_direct` |
| LF4 (operational) | `mixedHalf` (½·I, all fields proved), `weakPOVM` at η = ½, `plusVec` reduction (`Witnesses/Operational.lean`) | mixed ≠ pure by entry; weight strictly in (½, 1); reduced purity < 1 with trace 1 | `POVM.weights_sum_eq_normSq`, `weak_partial_information_witness`, `decohereReduced_trace`, `decohere_purity_lt_one_of_superposition` |
| LF5 (sequential) | superposition preparation + ready register, `hpos` discharged (`Witnesses/Sequential.lean`) | prepared ray ≠ collapsed vertex (`superposition_ne_vertex`) — certainty comes from the update, not the preparation | `csd_repeatability_same` / `csd_repeatability_other` (→ `swap_luders_born`) |

## Mutation-test record (one-off hand-run probes; permanent probes live in check-guards.sh)

| Control | Probe | Result |
|---|---|---|
| `--wfail` CI steps (WS-A) | appended `private def wfailProbe (unusedArg : Nat) : Nat := 0` (unused-variable warning) to `Tests/Examples.lean` | `lake build --wfail CsdLeanTests` exit 1 with probe; exit 0 restored. Probe removed, not committed |
| Witness suite (WS-B/C/J) | falsified `coin_frequency_convergence`'s limit (`nhds (1/2)` → `nhds 1`) | `lake build --wfail CsdLeanTests` exit 1 with probe; exit 0 restored. Probe removed, not committed |

## Blockers (genuine walls only; classified Mathlib gap / CSD API gap / missing physical construction / engineering)

None recorded yet.

## Cross-references

Theorem names cited by the witness suite are cross-linked in each module docstring per
the repo convention; forward pointers live in [`future-work.md`](future-work.md).
Campaign follow-ups (if any wall) get rows in [`BACKLOG.md`](BACKLOG.md) §V.
