# Corpus review coverage

The live file register is [corpus-review.tsv](corpus-review.tsv). Findings and wider
repairs belong in [BACKLOG.md](BACKLOG.md#corpus-file-review); detailed evidence belongs in
[reviews/](reviews/). The method remains [corpus-review-plan.md](corpus-review-plan.md).

## Commands

Run from the repository root:

```text
python -B scripts/corpus_review.py status
python -B scripts/corpus_review.py sync
python -B scripts/corpus_review.py check
python -B scripts/test_corpus_review.py
```

`status` computes current coverage without writing. `sync` refreshes the inventory and
effective statuses, preserving review evidence and issue links. `check` fails if the saved
inventory/statuses differ from the working tree. It does not demand that every file be reviewed.

Record a review only after writing its report, for example:

```text
python -B scripts/corpus_review.py record CsdLean4/LF1/Setup.lean --scope full --reviewer Codex --code pass --comments findings --evidence specs/reviews/2026-09-17-lf1-foundations.md --validation-status passed --validation "See report for commands and outcomes" --issues CR-LF1-002
```

## What the statuses mean

| Status | Meaning |
|---|---|
| unreviewed | No file-specific evidence has been reconciled into this register. |
| historical | Older evidence is linked, but has no verified current review snapshot. |
| partial | A recorded review covered only part of the current file or its checklist. |
| source-reviewed | The complete code/comment pass is recorded; validation remains pending. |
| reviewed | Complete code/comment review and reported validation match current source/context. |
| stale-source | The file changed after its review. |
| stale-dependency | A transitive local import or recorded dependency configuration changed. |
| retired | A previously recorded path is no longer tracked; its evidence is retained. |

Only `reviewed` counts toward current full coverage. A reviewed file may still have open issues:
**review completion and repair completion are separate**. The code/comment columns record whether
findings were encountered, even when repaired in the same batch. BACKLOG records their disposition.

## Reproducibility and limits

- Scope: every Git-tracked `.lean` file, including tests, facades and tooling. New untracked Lean
  files enter the inventory after they are tracked. Tracked missing files cause an error.
- `blob` is Git's hash of the working file with its clean filters. The reviewed blob, commit,
  reviewer, date, report and validation evidence are stored separately; uncommitted reviewed
  source is identified by its blob, not misrepresented as the unchanged HEAD.
- `context_hash` covers the file and all transitively imported local Lean files, the toolchain,
  Lake configuration/lockfile, and installed Mathlib HEAD. A comment edit conservatively
  invalidates importing files too. Re-review can be brief when the change is demonstrably harmless,
  but the tool never silently grants that judgment.
- The import scan masks nested comments and strings and accepts the repository's single-module
  import lines, including modifiers and `import all`. Unsupported import syntax and missing local
  imports fail rather than silently omitting dependencies. This is a static import graph, not Lean
  elaboration or proof-dependency analysis.
- Tracked Mathlib modifications stop the scan. Other dependencies are represented by the Lake
  lockfile; this is not an audit of untracked files or arbitrary edits inside every package.
- Hash agreement is a freshness check, not proof of a review. Human reports remain the evidence.
  Deep mathematical/physical claims retain their independent-review requirements.
- External citations and associated prose are followed where material; this denominator is Lean
  files, not a claim to have reviewed every repository document.
- The tool is manually invoked; it is not yet a CI gate. Full library/test builds and blocking
  guards remain required before integration.

## Reconciled history and next work

[Review history](reviews/history.md) preserves the 443-file older source review and the
46-module bridge-review scope without inflating current completion. Seven earlier reviews
mentioned in the plan still need file-specific provenance.

The first recorded batch is [LF1 foundations](reviews/2026-09-17-lf1-foundations.md).
The second batch covers the [frequency chain and product witness](reviews/2026-09-17-lf1-frequency.md).
The third batch covers [LF2 sector, bridge, preparations and interface](reviews/2026-09-21-lf2-bridge.md).
The fourth batch covers [phase independence, partitions and preparation densities](reviews/2026-09-21-lf2-phase-density.md).
At its completion on 2026-09-21, current verified coverage is **20 of 691 files (2.89%)**.
CR-LF2-005 (representative independence) is fixed and validated locally;
CR-LF2-006 (downstream projected dynamics) remains open. Reviewed status does not
imply that every improvement is finished.

Next dependency-ordered work: `LF3/Interface.lean` and `LF3/PurePreparation.lean`
alongside the relevant `LF2/FlowChannel.lean` sections, to trace fixed-ray assumptions
against the intended projected dynamics. Split deeper files into explicit partial slices
as needed. Import/build coverage alone does not mark them reviewed.

The 30-file stratified pilot is still pending. Before drawing it, freeze the eligibility rule
for historical versus never-reviewed files, strata, population sizes, seed and inclusion
probabilities. Record measured review/repair time; do not estimate corpus effort from this
targeted dependency batches.
