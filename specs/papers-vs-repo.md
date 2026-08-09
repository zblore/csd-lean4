# Repository versus published papers: axiom reconciliation

Where the repository and the published LF-series papers diverge, the repository is
current. The papers were written against earlier states of the formalisation and
record several results as imported named axioms. This page states, for each, what
is true at HEAD.

Verified 2026-08-09 by direct inspection of HEAD and of the pinned
`#print axioms` outputs in `CsdLean4/Tests/AxiomAudit/`.

## Findings

| Recorded in the papers as an imported axiom | State at HEAD | Where it lives now | Pinned axiom output |
|---|---|---|---|
| `invariant_measure_uniqueness_CPN` | Absent as an axiom. The abstract axiom was removed on 2026-06-04 together with the abstract `measure_bridge` lemma it served, which nothing downstream used. Its concrete content is a proved theorem, with the name differing in case from the papers. | `Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn`, `CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean` | `[propext, Classical.choice, Quot.sound]` (`Tests/AxiomAudit/MathlibStaging.lean`) |
| Busch effect-Gleason | Discharged. Proved on 2026-07-21 by Busch's finite-dimensional argument, and the `axiom` declaration removed. | `CSD.LF2.OperationalPackage.effect_gleason_representation`, `CsdLean4/LF2/EffectGleason.lean` | `[propext, Classical.choice, Quot.sound]` (`Tests/AxiomAudit/Foundations.lean`) |
| Rank-one density uniqueness | Discharged on 2026-05-18 via `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`. Now a proved theorem. | `CSD.LF2.rankOneDensity_unique_of_certainty`, `CsdLean4/LF2/BornWrapper.lean` | `[propext, Classical.choice, Quot.sound]`, verified directly. This theorem carries no `AxiomAudit` pin; see the note below. |
| `fs_moment_pushforward_uniform` | Discharged on 2026-05-31. Now a theorem of the same name, proved downstream to break an import cycle. | `CSD.LF4.fs_moment_pushforward_uniform`, `CsdLean4/LF4/MomentUniform.lean` | `[propext, Classical.choice, Quot.sound]` (`Tests/AxiomAudit/LF4.lean`) |

## Consequences

No `axiom` declaration remains anywhere in `CsdLean4/`. Every result the papers
present as conditional on one of the four items above is unconditional at HEAD,
in the sense that it depends only on Lean's foundational triple. This is a
statement about logical axioms alone. CSD's physical posits are unchanged and are
listed in `AXIOMS.md` section 3; they enter as hypotheses on the types and are
therefore invisible to `#print axioms` by construction, not by omission.

## Recorded gap

`rankOneDensity_unique_of_certainty` has no pin in `CsdLean4/Tests/AxiomAudit/`.
Its axiom footprint was verified directly during this reconciliation and is the
foundational triple, but it is not covered by the CI regression that would catch
future drift. Adding the pin is a one-line change, deliberately not made here
because this pass does not touch Lean source. Recorded in `specs/BACKLOG.md`.
