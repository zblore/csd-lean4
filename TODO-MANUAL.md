# Manual items outstanding after the landing-surface rewrite

## 1. Zenodo DOIs

Done, not outstanding. Retrieved from constraintsurfacedynamics.com/papers on
2026-08-09 and written into `CITATION.cff`:

| Record | DOI |
|---|---|
| LF3 (preferred citation for this repository) | 10.5281/zenodo.20354293 |
| LF2 | 10.5281/zenodo.20100580 |
| LF1 | 10.5281/zenodo.19472011 |
| Paper C, the reconstruction paper | 10.5281/zenodo.18098064 |

Judgement call, flagged for the maintainer: LF3 is used as `preferred-citation`
because it is the most recent Lean-formalisation record of the three, and the
site lists no concept DOI covering all versions. The repository now spans more
than LF3 covers. If a concept DOI is minted for the series, or a later LF record
is published, replace the `preferred-citation` DOI with it. The other records are
listed under `references:`.

## 2. GitHub repository settings

Done, not outstanding. Applied on 2026-08-09 with `gh repo edit`:

Description:

> Lean 4 formalisation of a deterministic reconstruction of finite-dimensional quantum mechanics: the Born rule as a Liouville volume ratio

Topics: `lean4`, `mathlib`, `formal-verification`, `quantum-foundations`,
`born-rule`, `quantum-mechanics`, `interactive-theorem-proving`.

Verified live via `gh repo view --json description,repositoryTopics`. Recorded
here so the strings are recoverable if the settings are ever reset.

## 3. Missing axiom pin

`CSD.LF2.rankOneDensity_unique_of_certainty` has no `#print axioms` pin in
`CsdLean4/Tests/AxiomAudit/`. Its footprint was verified directly during the
axiom reconciliation and is the foundational triple, but it is not covered by the
CI regression. Adding the pin is a one-line change to
`Tests/AxiomAudit/Foundations.lean`, deliberately not made during the
landing-surface rewrite because that pass does not touch Lean source. Also
recorded in `specs/papers-vs-repo.md` and `specs/BACKLOG.md`.
