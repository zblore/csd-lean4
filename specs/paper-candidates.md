# Paper candidates — which landed clusters have no manuscript home

Created 2026-08-19, from a ledger-vs-manuscript inventory. **Authorial planning, not
a work queue**: nothing here is scheduled, and no row implies Lean work is owed.

## The finding that motivates the page

**39 of the 52 ledger claims have no recorded paper home.** Attribution lives in
`specs/spec-to-lean.md` (Paper A → LF1, Paper B → LF2, Paper D → LF3),
`CITATION.cff` (the C1 pair CL-031 + CL-052 at tag `v1.4.1-c1-complete`), and
`docs/C1-FORMAL-SUPPORT.md`. The ledger itself has no paper column.

Two structural reasons:

* `CITATION.cff:40-41` — **"DO NOT cite the manuscript layers 'LF5' or 'LF6' as
  documents. They are unpublished."** So LF5 (measurement dynamics) and LF6
  (entanglement / open systems) have no citable document, and everything downstream
  of them (RecordLayer, SigmaLayer, CV, Thermo, Empirical, QuantumChaos) is
  unattributed by construction.
* The Q17 census extension (CL-032…CL-051, admitted 2026-08-13) plus CL-052 —
  **21 claims that postdate every published paper.**

And the sharpest line, from `specs/necessity-audit.md`: *"The corpus's
strongest-direction results are mostly not among its declared headlines."* It names
`stone_continuous`, `no_exact_finite_ccr` and the three measurement no-gos. All four
are now ledger claims. **None has a paper.**

## Candidates

Ordered by value per unit of effort. "Stands alone" = a reader need not accept the
CSD reconstruction to accept the paper.

| # | Candidate | Core claims | Stands alone | State |
|---|---|---|---|---|
| 1 | **Impossibility paper** | `no_exact_finite_ccr` (CSD-free, transfers to rival programmes), no continuous propagator correlating everywhere (pure topology), no measure-preserving exact collapse (pure measure theory), collapse accuracy priced by ready-state improbability, the positive-measure no-record set, the RG no-go `exists_unitary_compress_not_unitary` | **Yes** | All landed; this is the repair the necessity audit asked for |
| 2 | **Methodology paper** | The necessity audit's classification of 51 claims by logical strength (one unconditional necessity; every "forced" resting on exactly two posits), plus the guard family: AxiomAudit pins, `check-claims`, the prose audit, contradictions sweep, semantic mutations | **Yes** (not a physics claim at all) | Finished; needs writing, not mathematics. Audience: ITP/CPP formalisation |
| 3 | **Thermodynamics / typicality** | TH1 canonical typicality (expectation core), TH2 second law as pinching monotonicity, TH3 Gibbs variational principle, TH4 Landauer/Reeb–Wolf, joined to the field setting by CV-24 exact KMS | **Yes** | `thermo-plan.md:155` calls TH1 **"manuscript-strong"** — the only cluster in the corpus so described. See the scope warning below |
| 4 | **Rigidity paper** | Wigner rigidity (the *single* unconditional necessity in the corpus), Stone's theorem, `μ_FS` forced by `U(N)`, record-statistics invariance forcing `μ_FS` | Mostly | All landed; theme is "what forces what, and on what" |
| 5 | **Σ-fibre paper** | Born as ontic typicality volume at every `N`, with contextuality placed in the fibre for `N ≥ 3` — driven by a covariance + non-negativity constraint chain that stops short of a no-go (⚠️ the paper cannot claim impossibility), **not** Gleason/KS | Yes | `specs/sigma-fibre-contextuality.md`; an honest-limitation result that narrows the programme |

**Held back: the finite-cutoff EFT chain** (CV-1…CV-26). Largest cluster, but the
most exposed to the P3 ceiling (`specs/eft-pillars-plan.md`): it must be sold as an
acceptance-test *specification*, never as a field theory on spacetime. Harder pitch
than any of the five above; revisit after one of them lands.

## Scope warning for candidate 3

TH1 proves the **first moment** (`E[Tr_E |ψ⟩⟨ψ|] = I_S/d_S`), not the concentration
statement the literature means by canonical typicality — that needs Levy's lemma /
spherical isoperimetry, absent from Mathlib and parked as Mathlib-gated in
`BACKLOG.md` ("reopen only with cause"). A title claiming canonical typicality is
proved would oversell. The defensible contribution is **conceptual plus
verification**: the FS first moment is standard mathematics, but it is machine-checked
here, and the measure it integrates against has a uniqueness result (Paper B) and a
grounding argument (Paper A) behind it — which answers the standing objection that
`μ_FS` enters canonical typicality as an unmotivated prior. Expect, and pre-empt, the
Valentini-style reply that typicality arguments presuppose the measure they justify.

## Prerequisite before any of this

`specs/publication-errata.md` carries **two OPEN debts requiring manuscript edits**
(E-1 the LF3 type-separation argument, E-2 the "nudge" local-rotation claim). E-1 is
entangled with CL-031, half of the C1 citation pair. A referee who finds a
known-wrong argument in a cited paper discounts everything downstream, so clear those
first.

## References

`specs/VALIDATION-LEDGER.md` / `specs/validation-claims.tsv`; `specs/spec-to-lean.md`;
`CITATION.cff`; `docs/C1-FORMAL-SUPPORT.md`; `specs/necessity-audit.md`;
`specs/thermo-plan.md`; `specs/sigma-fibre-contextuality.md`;
`specs/eft-pillars-plan.md`; `specs/publication-errata.md`.
