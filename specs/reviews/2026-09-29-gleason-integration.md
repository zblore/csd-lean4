# Applied Busch–Gleason review corrections

Date: 2026-09-29. Integration base: main `ff5c7998`.

## Changes

The eight reviewed Lean modules now contain the corrected comments. This covers the real
extension names, Gleason citation, probability-assignment terminology, frame-function
nonnegativity, pole/equator degeneracies, dependent vector pairs, unit reflection normal,
obsolete imported-axiom header, moved theorem pointers and outer-product terminology.
Existing definitions, theorem statements and proofs in those eight modules are unchanged.

`scripts/gleason-free.lean` now traverses local/corpus declarations across namespaces and
checks eight roots: the Busch headline, density and matrix constructors, the proved real
three-dimensional core and its underlying regularity theorem, complex/real projection representation and real frame representation.
It scans the prior eleven modules plus `Tests/Witnesses/SingletBell`. Direct roots and six
aliases must be detected; a benign scalar lemma must remain allowed. Missing roots or declared
modules fail the guard. This guards the listed production scope, not every CSD independence claim.

The original review report, per-file notes, source manifest and four audits are included so
another reviewer can inspect both the source changes and the evidence. The old snapshot stays
reproducible; `validate-current.py` checks this checkout's built source instead.

## Validation

Validation passed on the corrected tree based on `ff5c7998`:

- `lake build --wfail CsdLean4 CsdLeanTests`: exit 0, **4,674 jobs**.
- All four saved audits: exit 0, warnings fatal; terminal axioms remain the foundational triple.
- Production dependency guard: exit 0; **269 declarations in 12 modules**, eight forbidden
  roots, six alias controls and the allowed-route control all passed.
- Twelve repository guards: module coverage, claims, claim provenance, doc promises, residues,
  references, terms, labels, category tags, placeholder status, negative imports and import hygiene.
- Comment-stripped comparison against the reviewed revision: all sixteen proof modules unchanged.
- `git diff --cached --check`: passed. The archived patch has a per-file whitespace attribute
  because unified-diff blank context lines contain a required space; source checks remain enabled.

[Machine-readable results and source hashes](2026-09-28-gleason-submission/integration/validation.json),
[build log](2026-09-28-gleason-submission/integration/build.log),
[guard log](2026-09-28-gleason-submission/integration/gleason-free.lean.log), and
[static checks](2026-09-28-gleason-submission/integration/static-checks.log) are archived.
Newer concurrent main commits are reconciled separately; the hashes identify precisely the
proof sources covered by these results.

## Independent reproduction

From this checkout, with the pinned Lean/Mathlib toolchain and cache installed:

```powershell
$env:LEAN_NUM_THREADS = '2'
lake build --wfail CsdLean4 CsdLeanTests
lake env python -u -B specs/reviews/2026-09-28-gleason-submission/validate-current.py
```

The second command runs all four saved Lean audits plus the actual production guard, with
warnings fatal. It records each input hash, source hashes and logs under the review's
`integration/` directory. `run.py` and `probe.py` intentionally reproduce the older pinned
source; they are not the validation commands for this applied change.

## Scope retained

No proof was weakened. The legacy dimension-restricted wrappers and redundant package field
remain for compatibility; the main Busch theorem already covers dimensions one and two and
its checked plain-matrix audit adapter derives boundedness. Production API promotion is an
optional follow-up, not an unresolved mathematical correction. Unrelated source edits in the
older Codex review worktree are preserved and excluded from this integration.
