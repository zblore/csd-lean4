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
| Validated | 7 | No material claim mismatch found at current depth. |
| Qualified | 16 | Formally coherent, but assumptions or construction scope must accompany the claim. |
| Needs change | 4 | Concrete semantic/API mismatch recorded in the main review ledger. |
| Specialist review | 3 | Wigner rigidity, effect-Gleason, and entropy proofs need independent experts. |

## Highest-priority validations

1. `CL-003`: demonstrate mechanically that the LF2 bridge is not extensionally consumed.
2. `CL-011`: distinguish preparation-indexed regions from context-fixed apparatus outcomes.
3. `CL-023`: preserve the explicit DPI premise in every SSA-facing public claim.
4. `CL-027`: prevent heterogeneous witnesses being advertised as one unified measurement model.
5. `CL-024`, `CL-005`, `CL-022`: commission independent proof audits using standard references.

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
