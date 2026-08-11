# The prose audit

Started 2026-08-11, after the C1 correction found two false claims that lived
**only in prose**. This file records the method, the surface, and every finding.

It exists because a single clean pass is weak evidence, and burying that in a
commit message lets "we looked once" harden into "the corpus is clean".

## The class being hunted

Both C1 defects were **prose giving a *reason* for a formal fact** — why
`nudgedSinglet` is what it is, why collinear settings are excluded. This is
distinct from what the guards catch, and it is invisible to all of them:

* `check-claim-provenance` targets claims *about objects* — a definition
  asserting a property it does not have. A wrong **reason** attached to a
  **true** statement trips nothing.
* Lean cannot help at all. Nothing in Lean states reasons, so nothing can
  disagree with one. The theorem is true; only the explanation is false.

**No guard can close this class.** It needs a reader who knows the mathematics.
That is a real limitation, and it is the reason this file tracks progress
explicitly rather than reporting a pass/fail.

## Surface

An extraction over every tracked module finds **201 doc blocks** that both
explain a restriction and mention a hypothesis, exclusion or degeneracy. That is
the audit surface — bounded, but several passes.

```
git ls-files 'CsdLean4/**/*.lean' | xargs awk '...'   # see the commit for the script
```

Highest block counts: `LF2/EffectGleason.lean` (6), `SigmaLayer/ContextFixedA7.lean`
(5), `Mathlib/LinearAlgebra/Projectivization/{WignerRigidity,Topology}.lean` (5
each), `Empirical/QM/Algorithms/ShorRandomA.lean` (4).

## Passes

### Pass 1 (2026-08-11) — quantitative explanatory prose

**No defect found.** One candidate checked and cleared: `Einselection.lean`
reports a rotated off-diagonal of `3/2`, impossible for a trace-one density
matrix. It is correct — `einselectionWitness = (2,1)` is deliberately
unnormalised, so the trace is 5. A clarity note was added, since the auditor
misread it.

Coverage: roughly a tenth of the surface.

### Pass 2 (2026-08-11) — SigmaLayer and LF4 clusters

**One defect found and corrected: the `[0,1)` reason.** ★

Five modules and one spec row explained the restriction in
`RecordLayer.fibreTypicality_uncovered` to `Ico 0 1` by saying **"because
Lebesgue measure on the line is infinite"**. Wrong twice over:

1. `fibreTypicality` is **not** Lebesgue measure on the line. It is
   `volume.restrict (Ico 0 1)`, and it carries `instIsProbabilityMeasure`,
   proved a dozen lines above the theorem the reason was attached to. Total mass
   on `univ` is one.
2. The restriction was **not forced**. `fibreTypicality_uncovered_univ` now
   proves the identical `univ`-form statement on `ℝ`.

**The comparison the prose was drawing is still real, but it is a different
one.** The difference between the `ℝ` fibre and the compact fibre is not which
sets the statement ranges over — it is **where the mass one comes from**. On `ℝ`
it is imposed by fiat: `fibreTypicality_Ici_one` shows the fibre's complement,
of *infinite* Lebesgue measure, is assigned typicality **zero**, so an uncovered
point off `[0,1)` is *excused by the measure* rather than covered by a cell. On
`CircleFibre` / `TorusFibre` the mass is Haar mass on a compact group, every
nonempty open set has positive measure, and an uncovered point has nowhere to
hide.

Sites corrected: `SigmaLayer/{CircleRecord,GlobalRecordClosure,RecordLayerClosure,TorusFibre}.lean`
and `specs/BACKLOG.md`.

⚠️ **`specs/BACKLOG.md` contained both readings at once** — the correct
diagnosis ("what restricted Lebesgue on `ℝ` only had **by fiat**") three
sentences before the wrong one. The right answer was already written down and
the wrong sentence still propagated to four modules. **A defect being known
somewhere in the repository does not stop it spreading**, which is an argument
for settling this kind of claim with a theorem rather than a better sentence.

## Method note

Both passes converged on the same tactic, and it is the one to keep: **when
prose gives a reason for a formal restriction, try to prove the restriction is
unnecessary.** If the proof goes through, the reason was wrong. That converts an
unfalsifiable sentence into a Lean obligation, which is the only durable fix —
the two theorems added in pass 2 are pinned, so the corrected reason cannot
silently rot back.

## Status

**Roughly a fifth of the surface covered. One defect found.** The remaining
blocks are recorded here rather than implied to be clean.

## References

`specs/future-work.md`; `specs/c1-closure-report.md` (the correction that
motivated this); `specs/publication-errata.md`;
`scripts/check-claim-provenance.sh` (what the guards *can* catch, and its stated
limits); `CsdLean4/SigmaLayer/DeIsolationFlow.lean`
(`fibreTypicality_uncovered_univ`, `fibreTypicality_Ici_one`).
