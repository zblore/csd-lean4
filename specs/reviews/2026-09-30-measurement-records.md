# Measurement and record review

Date: 2026-09-30. Reviewer: Codex, current review session. Base: `4b396fa31cc9f0c0042e4d681bf838338049378b`.
Worktree: `C:/Zayn/csd/lean4-gleason-integration`, branch `codex/record-review`.
The worktree name is retained to reuse its own build outputs and the existing dependency cache.
Prepared for integration on 2026-10-01 after all blocking checks passed.

## Scope and result

Full source and comment review: `RecordLayer/Measurement.lean`, `FibreRecord.lean`,
`DrivenTwoTime.lean`. No false Lean theorem found. Two mathematical interface improvements
are implemented: normalized generic contexts now have proved probabilities and almost-sure
record production; the driven joint-law endpoint now covers zero-probability first outcomes.

Supporting definitions and selected proofs were inspected in BornFibrePartition,
DeIsolationFlow, RecordedFact, GlobalBasin, RotatedContext, RotatedSwap, MixedSwap,
MixedLuders, SwapWitness, SwapLuders and TwoTimeLuders. These are dependency checks, not
full-file review credit. JarzynskiRecord's one direct caller is migrated; its entire
thermodynamic development has not been reviewed in this batch.

## Findings and repairs

| ID | Finding | Disposition |
|---|---|---|
| CR-RECORD-003 | Measurement.outcome claimed almost-sure totality for an arbitrary FibreContext, which assumes only nonnegativity. The all-zero context returns none everywhere; a one-outcome half-rate context misses part of the unit fibre. | Corrected the scope; proved `Measurement.prob_eq_rate` and `Measurement.ae_record_of_sum_eq_one` under rate normalization. The existing unit-state Born probability theorem now uses the generic result. No new normalization field is imposed on existing contexts. |
| CR-RECORD-004 | The driven joint probability formula excluded a zero first Born weight because its proof used conditioning. The joint event is a subset of the first-record event, so its measure is zero whenever the first marginal is zero. | Strengthened the existing `driven_mixed_two_time_born` by removing `hpos`. The old positive-case proof is `driven_mixed_two_time_born_of_ne_zero`; the zero case uses the proved first marginal and measure monotonicity. Updated the Jarzynski caller and retained the existing endpoint axiom pin. External callers passing `hpos` must drop that argument or use the conditional helper. |
| CR-RECORD-005 | Generic context rates were described as Born weights and an arbitrary measurable base map as a flow. The real-fibre readout prose also blurred packaging a RecordedFact with changing an apparatus register, and the trial independence assumption with ignorance of an initial state. | Comments now distinguish the exact structures and point to the register-changing construction. No dynamics, independence, or Born-rate axiom was added or discharged by this correction. |

These repairs strengthen the code rather than merely lowering a headline claim. The old
positive-case theorem was valid; its missing zero case was an unnecessary restriction.

## Mathematical trace

### Measurement and FibreRecord

CDF cells are half-open intervals, with pairwise disjointness from nonnegative rates.
`fibreTypicality` is Lebesgue measure restricted to `[0,1)`. Under sum-one normalization,
every cell lies in that interval, so restriction preserves its measure and the finite union
has measure one. Cell membership then gives the recorded fact via `record_of_mem_basin`.
The generic theorem does not claim pointwise totality on the whole real line.

`fibreRecordSemantics` ignores the time label and asserts exclusivity within a context.
`compatibleSet_fibre_single` is an event identity, not a posterior probability formula or
an interaction law. The Born constructor supplies squared component norms; normalization
follows from unit norm. Moment-map identification does not force every nonnegative context
to use Born rates. The frequency theorem requires the specified marginal law and pairwise
independence of the outcome indicators, not just deterministic selection.

### DrivenTwoTime

`driveStage` changes only the system coordinate. The two registers and banks keep their
positions; `stageTwo` preserves the first record structurally. `swapEvolve_register_comp`
uses the fact that a bank swap leaves the pointer register unchanged. Therefore the joint
record event after a drive is the undriven event with the second selector precomposed by
the drive. No measure-preservation or invertibility of the drive is required for this identity.

The generic joint law uses `twoStagePrep`, explicitly a product of the system/first-register
law, independent first-bank slots, second register, and second-bank slots. On a selected
first outcome the system becomes bank slot i; `swap_luders_marginal` supplies its law.
Thus calibration to basis rays supplies the rank-one post-state. Record creation alone does
not force calibration: the existing `swap_luders_iff_calibrated` theorem identifies the
bank law as the necessary and sufficient condition.

The mixed preparation is a spectral mixture. The first basis-context mixture is identified
with the density-matrix trace by `spectral_born_ctx_eq_traceForm`. After a base drive the
second factor is the supplied context rate at the transported basis ray. A ContextField
can be constant and need not be a quantum basis measurement. Specializing to a basis
context gives the usual second Born weight. The endpoint now handles all first outcomes;
this does not define a normalized conditional state on a null event.

## Validation

Passed on the saved source hashes:

- `lake build --wfail CsdLean4 CsdLeanTests`: exit 0, **4,686 jobs**, including the
  final incremental run after the last comment clarification.
- `lake env lean -DwarningAsError=true specs/reviews/2026-09-30-measurement-records/BoundaryAudit.lean`:
  exit 0; eleven boundary examples, three axiom reports, only `propext`, `Classical.choice`
  and `Quot.sound`. The production audit pins also passed in the full test build.
- Thirteen selected repository guards: claims, claim provenance, doc promises, residues,
  references, terms, labels, category tags, placeholder status, negative imports,
  import hygiene, validation ledger and semantic mutations: all exit 0.
- `git diff --check`: passed. Source/config hashes were rechecked after validation.

[Machine-readable validation and hashes](2026-09-30-measurement-records/manifest.json),
[per-file review rows](2026-09-30-measurement-records/batch-review.tsv),
[boundary probes](2026-09-30-measurement-records/BoundaryAudit.lean), and
[final build log](2026-09-30-measurement-records/final-build.log) are saved.
The three reviewed files contain 690 lines at this snapshot.

All **22 blocking CI guards** subsequently passed on the staged batch, including the
repository-wide axiom sweep, citation-use check, reconstruction-dependency scan and guard
mutation tests. [Integration checks](2026-09-30-measurement-records/integration-checks.json)
record each command and exit code. These results identify the recorded source base;
any rebase onto newer main is checked separately before pushing.

## Coverage and next work

[Reconciliation](2026-09-30-measurement-records/coverage-reconciliation.json) counts **791
tracked Lean files** at this base, including tests, tooling and archived Lean audits.
Of the old ledger's 39 reviewed entries, 35 have changed source and four have changed
dependency context. This is a freshness result, not evidence that 39 earlier reviews were
wrong. Their reports remain historical evidence; review-branch-only repairs must be
reconciled individually before being declared applied on current main.

The separate 16-module Busch–Gleason review is not silently folded into that old ledger.
Neither this source comparison nor a successful full build grants fresh manual-review credit
to uninspected files. This batch adds three complete file reviews at the saved hashes.

The [30-file pilot](2026-09-30-measurement-records/pilot-30.json) is now selected, not reviewed:
seed 20260930, six files from each existing stratum, 735 eligible files, explicit inclusion
probabilities. Previously full-reviewed files and the current targeted scopes are excluded;
historical-only entries remain eligible and are labeled. Review and repair times remain
blank until measured. It can estimate work in this eligible population, not the separately
selected headline packages or stale-review renewal queue.

Next targeted batch: POVMDilation, POVMNaimark and POVMVolume. Next record dependency batch:
full review of the two-stage/swap engines inspected here, followed by the LF5 event-to-record
connection tracked under CR-LF2-006. This batch does not close that broader bridge obligation.

## Integration — 2026-10-01

Committed after all 22 blocking guards passed, then rebased onto main `2e0cf246`.
All recorded source/configuration hashes are unchanged. The combined warning-fatal library
and test build passed (**4,693 jobs**); [log](2026-09-30-measurement-records/rebased-build.log).
The upstream baseline has green GitHub CI; the manifest records the separate validation scopes.
This commit carries the source repairs and evidence for publication to `origin/main`.
The other window's staged work in the main checkout is preserved; that checkout is not reset.
