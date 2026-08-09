# Manual items outstanding after the landing-surface rewrite

## 1. Zenodo DOI for `CITATION.cff` (blocking for the preferred citation)

No Zenodo DOI is recorded anywhere in the repository, so none was written into
`CITATION.cff`. A DOI was not invented for it. The file is schema-valid without
one (validated against CFF 1.2.0 with `cffconvert`).

To complete the citation, add the DOI line to the `preferred-citation` block:

```yaml
preferred-citation:
  type: generic
  title: "Constraint-Surface Dynamics: the LF series"
  doi: "10.5281/zenodo.XXXXXXX"          # <- add this line
  authors:
    - family-names: Blore
      given-names: Zayn
      orcid: "https://orcid.org/0009-0009-8447-7247"
  url: "https://constraintsurfacedynamics.com"
```

A top-level `identifiers:` entry with the concept DOI can be added at the same
time if the record has one.

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
