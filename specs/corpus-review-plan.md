# Corpus review: execution plan

Updated 2026-09-30. Aim: review every tracked Lean file for mathematical content, assumptions,
proof dependencies and comments, improving the Lean results where justified.

## Baseline and evidence

Current batch base: `4b396fa3`, **791 tracked Lean files**. The previous **39/691 (5.64%)**
register is historical: 35 of those files changed and four have changed dependency context.
Renew their evidence individually; do not reset their history or count them as current by default.
The separate 16-module Busch–Gleason review and its integration remain recorded in their reports.

[Current review and reconciliation](reviews/2026-09-30-measurement-records.md) records the new
three-file batch, its source hashes, executable probes, findings and validation status.
Work in the isolated `codex/record-review` branch at `C:/Zayn/csd/lean4-gleason-integration`.
The older `lean4-codex-review` checkout retains its unrelated edits; reconcile those separately.

## Execution order

| Work | Completion criterion |
|---|---|
| Measurement, FibreRecord, DrivenTwoTime | Full code/comment pass, normalized-record and zero-probability repairs, boundary probes and consumer validation; current batch |
| POVMDilation, POVMNaimark, POVMVolume | Trace the dilation, measurement and volume claims through their definitions and assumptions; repair and validate |
| Selected 30-file pilot | Six batches of five, one file from each stratum per batch; record actual review and repair time, findings and follow-up scope |
| Record-engine dependencies and LF5 bridge | Complete the supporting swap/two-stage reviews; resolve the actual event-to-record connection under CR-LF2-006 |
| Remaining corpus and renewal queue | Dependency-ordered batches of 5–10; include geometry/FS, foundations, dynamics, empirical claims, library infrastructure and tests/facades |

The [pilot manifest](reviews/2026-09-30-measurement-records/pilot-30.json) fixes the seed,
735-file eligible population, strata, 30 selections and inclusion probabilities. Historical-only
entries remain eligible; earlier full reviews and targeted packages are excluded. No sample file
is credited before its review. Forecast eligible-population effort after measuring the pilot,
weighting each stratum by its size; estimate targeted packages and renewal work separately.

## What every review must establish

Read all definitions, statements, proofs and comments. Check intended meaning, quantifiers,
edge cases, implicit instances, assumption consistency, nonvacuity, circularity and imported
results. Compilation checks the stated proposition; it does not certify the physical reading.
For important endpoints, save concrete witnesses, boundary/counterexamples and axiom checks.

When a claim exceeds the theorem, first formulate and try to prove the intended stronger
statement. Do not add the desired conclusion as a hypothesis. If blocked, retain the precise
proof obligation and affected consumers in BACKLOG; correcting prose alone does not close it.

## Close and track each batch

Save file/dependency hashes, per-file reasoning, issue IDs, repair scope and command results.
Build affected modules and consumers; require the full warning-fatal library/test build and
blocking repository checks before integration. Distinguish source-reviewed, validated,
committed and landed-on-main states. Include downstream changes in the same issue's scope.

Report current full-file coverage separately from historical evidence, partial checks,
material comment corrections and changes to Lean statements/proofs. Reconcile review records
against a pinned main revision after each integrated batch. Palomar package verification can
proceed independently of whole-corpus completion.
