# Reconciled review history

Recorded 2026-09-17 at baseline `c06f8e18512862876943602f0c9ff69611abcd9b`.

## Older foundational and remaining-file review

[FOUNDATIONAL-CODE-REVIEW.md](../FOUNDATIONAL-CODE-REVIEW.md), dated 2026-08-06, reports
38 foundational files and 405 appendix files. Its tables contain **443 distinct file paths**,
all still tracked at this baseline. The register links those rows as historical evidence.

That report explicitly says compilation was unverified and does not identify reviewed Git blobs.
Some large files are marked as needing specialist review. Its source/API judgments remain useful
triage; they do not establish current full-review completion or that its old findings remain open.
Reconcile any rediscovered issue against today's BACKLOG before opening a duplicate.

## Bridge reviews, September 16–17

The [A/B brief](../review-briefs/physlib-bridge-2026-09-16.md) and
[Brief C](../review-briefs/brief-c-2026-09-17.md) concern a targeted mathematical dependency closure.
The current slice list identifies **46 modules**, **11** also present in the older 443-file ledger.
The register links all 46 as previous targeted scope, not as 46 complete file reviews.

Brief C's review at `2b78ee5` (mathematical baseline `2a71b34`) reported:
smoothness missing from the almost-Kähler predicate; arbitrary metric-volume normalization;
a sign-convention comment error; a missing normalization factor in a Kähler header;
a duplicate complex product-basis construction; derivable tangent-bundle assumptions;
an atlas-transition API gap; and stale metric/closed-ball comments.
These were definition/API or prose findings, not a discovered false Lean theorem.

Commit `c06f8e1` records the fixes. They are not independently marked closed by this
coverage reconciliation. Their canonical disposition remains BACKLOG #33's review residue.
Rechecking those changes does not by itself complete every-file review of the closure.

## Seven earlier reviews

The one-page plan records seven earlier complete reviews, but this session has no reconciled
file list, blob snapshots and validation records for that set. They receive no additional
coverage credit until that provenance is recovered. They may overlap other historical work.

## Build baseline

At this baseline GitHub reports successful
[CI](https://github.com/zblore/csd-lean4/actions/runs/35225228709) and
[Glossary](https://github.com/zblore/csd-lean4/actions/runs/35225228698).
Those results apply to the committed baseline, not the subsequent uncommitted LF1 changes.
Local batch validation is recorded separately in its report.
