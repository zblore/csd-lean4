# Headline claim validation ledger

Review date: 2026-08-06  
Machine-readable source: `specs/validation-claims.tsv`

## Purpose

Lean checks that a proof term has its declared type. This ledger checks the separate question: whether
the declared type, definitions, hypotheses, and public description support the intended mathematical
or physical claim.

Statuses:

- `validated`: statement and intended claim align at the present review depth.
- `qualified`: correct under important scope or interpretation qualifications.
- `needs-change`: the public claim/API should be narrowed or strengthened.
- `specialist-review`: mathematically deep proof requiring independent domain proof review.

The TSV is canonical for automation. It records 30 headline claims, their defining modules, exact Lean
constants, load-bearing assumptions, an independent validation route, and any linked review finding.

## Current result

| Status | Count | Meaning |
|---|---:|---|
| Validated | 8 | No material claim mismatch found at current depth. |
| Qualified | 20 | Formally coherent, but assumptions or construction scope must accompany the claim. |
| Needs change | 2 | Concrete semantic/API mismatch recorded in the main review ledger. |
| Specialist review | 0 | All three commissioned audits (CL-005/CL-022+CL-023/CL-024) completed 2026-08-06. |

(Counts updated 2026-08-06 after same-day resolution of CL-003 (G1 discharge, -> qualified) and the
three specialist audits with author sign-off: CL-005 -> validated; CL-022, CL-023, CL-024 ->
qualified. Audit payloads summarized in `audit-sweep-plan.md`; residue rows in `BACKLOG.md` SG.)

## Highest-priority validations

(Original five priorities, status as of 2026-08-06:)

1. `CL-003` — DONE (G1 discharge: transport theorems consume `bridge_eq`; mutation guard requires them).
2. `CL-011` — standing: the preparation-indexed vs context-fixed distinction is the MD-1 frontier
   (qubit done; general-`N` per `sigma-fibre-contextuality.md`).
3. `CL-023` — DONE (audit verified the reduction + repo-wide wording sweep; hDPI discharge itself
   stays the E2 backlog row).
4. `CL-027` — DECIDED (G5: index-style capstone names kept, rename on-touch; docstrings carry the
   framing).
5. `CL-024`/`CL-005`/`CL-022` — audits completed 2026-08-06 and signed off. Remaining residue:
   the human hand pass on the five named Wigner tactic blocks + optional uniqueness formalization
   (BACKLOG G11).

## Required evidence for promotion to validated

A claim may move to `validated` only when:

1. its Lean module and constant still exist and compile;
2. `#print axioms` has only the accepted foundational footprint;
3. every load-bearing assumption is identified;
4. non-vacuity is established by an inhabitant or consistency witness;
5. the statement is compared with an authoritative mathematical reference;
6. at least one independent check is completed (alternative proof, exhaustive finite model, numerical
   oracle, or specialist proof review);
7. the README/spec wording is no stronger than the exact Lean statement.

## Control boundary

The automated checker validates ledger structure and declaration linkage. It cannot certify the human
judgments in the `status`, `load_bearing`, or `independent_check` columns. Those remain review evidence
and must be signed off claim by claim.
