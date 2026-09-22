# Corpus review: plan on a page

**Aim:** improve the Lean mathematics and its explanation, prioritising the reconstruction goal in [CSD-CHARTER.md](CSD-CHARTER.md). Strengthen existing results where the intended claim is supportable; a smaller prose claim alone does not close a mathematical gap.

**Baseline (2026-09-16, `f24ad46`):** 680 tracked Lean files; 74 rows in [validation-claims.tsv](validation-claims.tsv). Seven files received earlier full reviews (1.03%); carry their evidence forward and reconcile it with this commit. That small sample cannot forecast corpus-wide impact. Comment-only changes can materially alter a scientific claim.

**Operational status (2026-09-22, `eb8fdf1` plus recorded local edits):** 691 tracked Lean files; 32 currently reviewed (4.63%). The [coverage register and commands](corpus-review-tracking.md) are implemented. [Historical evidence](reviews/history.md) includes 443 older source-review rows and the 46-module targeted bridge scope; neither is counted as current full completion without matching evidence and validation. Batch reports and BACKLOG hold findings; the 30-file pilot and effort forecast remain pending.

## 1. Establish coverage and a reproducible starting point

Work in `lean4-codex-review`, branch `codex/corpus-review`, with its own build outputs. Keep Claude's checkout separate and coordinate overlapping files before integration. Capture the commit, tracked-file inventory, full CI baseline and existing advisory reports. Introduce a file-review manifest recording path, reviewed blob hash, reviewer, code/comment outcomes, evidence and linked findings. This tracks coverage; [BACKLOG.md](BACKLOG.md) remains the canonical work queue, and the existing claim ledger, posit and residue registers retain their roles. Changed files and affected consumers require renewed review.

## 2. Order the work and calibrate the forecast

Prioritise headline claims, shared definitions, bridge assumptions and known residues. Trace advertised results backwards through their dependencies, then review foundations before consumers. Use `check-review-surface.sh` to rank questions, never as a correctness score. Separately draw a reproducible, stratified random pilot of 30 previously unreviewed files across library mathematics, foundations, record/dynamics, empirical modules and tests/facades. Record sampling probabilities, file size, review time, material findings and repair time. Forecast remaining effort with stratum-weighted estimates and uncertainty; report targeted findings separately. Recalibrate after each 30-file tranche. Ultimately cover every tracked Lean file.

## 3. Apply the same checklist to every file

| Pass | Required judgement |
|---|---|
| Definitions and statements | Do objects model the intended mathematics? Inspect quantifiers, domains, dimensions, measures, limits and edge cases; distinguish existence, sufficiency and necessity. |
| Assumptions and proofs | Expose implicit instances and structure fields; check consistency, nonvacuity, circular assumptions and premise/conclusion equivalences. Trace imported results and axiom dependencies. Compilation proves the stated proposition, not its interpretation. |
| Lean design | Check reusable interfaces, redundant definitions, imports, naming and maintainable proofs. Refactor for a demonstrated benefit. |
| Every comment | Read module docs, declaration docs and inline comments against exact statements. Check examples, theorem links, citations and scope; follow material findings into README, TOUR, status documents and ledger entries. |

## 4. Repair the mathematics, then align the claims

For each material mismatch, write the intended Lean statement and identify the missing proof or hypothesis. First try strengthening the existing terminal theorem, discharging assumptions or connecting existing results (CONVENTIONS §8.3b). Preserve callers and update the existing claim row. Add concrete nontrivial witnesses and boundary/counterexample checks where they distinguish the stronger result from the old one. If the claim is false or blocked, explain why, correct the current description and retain the mathematical objective in BACKLOG with its next proof obligation. Never add the desired conclusion as an assumption and count it as progress.

## 5. Validate and close each batch

Use small batches of 5–10 files, splitting deep files as needed. Build affected modules and consumers; run relevant axiom audits, regression tests and claim/document guards. Before integration, require `lake build --wfail CsdLean4`, `lake build --wfail CsdLeanTests` and all blocking CI checks. Seek independent mathematical review for deep claims and preserve existing sign-off requirements. Close a finding only when evidence, affected prose and registers agree. Report separately: files reviewed; material comment corrections; Lean/API repairs; strengthened claims or discharged assumptions; unresolved gaps; and time spent. Corpus completion means full recorded coverage and explicit disposition of every finding—not a percentage of edited files.
