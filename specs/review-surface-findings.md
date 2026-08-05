# Review-surface triage — first-run findings and open questions (2026-08-05)

**Source:** `scripts/check-review-surface.sh`, first full run at HEAD `20f3796`,
captured verbatim in [`docs/review-surface-baseline-2026-08-05.txt`](../docs/review-surface-baseline-2026-08-05.txt).
**Motivation:** Ilin & Nugent, *Sorries Are Not the Hard Part* (arXiv 2606.13925) —
a sorry-free, kernel-green formalisation in which an expert reviewer found 61 of 62
agent-written definitions wrong as library code. Their review rate (one
expert-week per theorem) extrapolates to ~25 expert-weeks for this corpus, so the
review surface is triaged mechanically here and consumed by a human. **These are
findings and questions, not a pass/fail** — every metric is a proxy, and each row
below is the question "would this survive a library reviewer?", not the verdict
"this would not".

## What the first run found

**Scale.** 1,285 distinct definitions, 4,314 theorem/lemma statements measured
(comment- and docstring-stripped, exact-token references, `Tests/AxiomAudit.lean`
excluded as a consumer and read only as the headline registry).

**(A) 118 thin definitions** (1–2 references). The dominant signal is not 118
independent problems but a few *patterns*: nine `*_realisable_for` defs in
`Empirical/CSD/Gates/` each referenced exactly once (and all nine also appear in
(E) as theorem-style underscored names — one design question, asked nine times);
a `*Security` trio in `Empirical/QM/Crypto/`; paired `k*`/`cp*` bridge objects in
LF4. Question, per pattern: deliberate seam, or definition-shaped documentation?

**(B) 608 definitions are reached through (`unfold`/`delta`/`simp [name]`); 26
have no lemma interface at all.** Worst: `alphaOff`/`betaOff`
(`LF6/CGLMPQudit.lean`, 18 reach-throughs each, zero lemmas),
`cuccaroMulModLayout3` (14/0), `gateCost` (23 through, one lemma). The
`Mathlib/QuantumInfo/Reversible/` circuit-layout tier dominates — relevant to the
BACKLOG B6 upstreaming row, since mathlib review would hit exactly this. This is
the paper's central API finding operationalised, and the count is a floor
(`show`/`rfl`-against-def sites are not attributable by grep and are not counted).

**(C) 1,102 statements referenced exactly once** (~27% of all statements; pinned
headlines excluded). Much of it is per-file scaffolding with a clear local shape —
e.g. the nine `reindex_sigma*` lemmas in `MerminPeresVolume.lean`. The paper's
reading ("proved exactly what it needed") and the benign reading (honest local
factoring) are both live; the list ranks where to look, nothing more.

**(D) Proof style.** Corpus mean 1.19 `have`/theorem. Absolute-count outlier, as
predicted when the metric was designed: `WignerRigidity.lean` (370 `have` in
3,180 lines). Density outliers: `ShorRecovery.lean` (8.0/thm),
`ContextFixedA7FS.lean` (7.6/thm). Longest proof blocks: `cuccaroModAdd_spec`
(313 lines), `cuccaroModDouble_spec` (239). Note `join_luders_marginal` at 123
lines — independent corroboration of the BACKLOG B3b sizing note that the
conditioning half of Lüders proofs is where the difficulty lives.

**(E) 30 off-norm definition names.** The corpus def norm is overwhelmingly
single-segment camelCase (1,255/1,285; 1.04±0.27 segments), so a theorem-style
underscored *definition* name is itself the anomaly — the `*_realisable_for`
family again, plus long camelCase (`bellClassicalBoundValue`).

**Reconciliation.** check-vacuity remains the zero-reference authority: 3 dead
defs today (`bell_prep_compose`, `mzOutput`, `productMeasureBridge`). The earlier
token-level estimate of ~22 was collision-inflated (short names) and is retired.

## Coverage against the paper's five review categories — honestly

| Category | Coverage | Why |
|---|---|---|
| API design | **Covered (best)** | (B) is their central finding made mechanical; undercounts stated. |
| Definitions | **Partial** | (A)/(E) + check-vacuity rank candidates; *definitionally-equal duplicates* and "is this the right definition at all" need Lean elaboration and a mathematician — out of scope, listed in the script header. |
| Proof style | **Partial** | (D) catches have-walls and monster proofs; term-vs-tactic idiom, `calc` use, golfing judgement are not greppable. |
| Theorem statements | **Weak** | (C) catches the over-specialisation *shape* only. Whether a statement says what its docstring claims is human review; `connectivity-manifest.md` + `check-claims.sh` govern the corpus's claim discipline. |
| File structure | **Not covered** | Namespace/import design is partially `check-connectivity.sh` ground; no new mechanical signal shipped rather than a weak one. |

## Open questions (the human review queue, ranked)

1. Should the `Reversible/` layout defs get equation-lemma interfaces before any
   B6 mathlib upstreaming? (26 no-API defs; mathlib review would demand it.)
2. Is the `*_realisable_for` family (nine thin, theorem-named defs) the right
   shape, or nine instances of one definition that should exist once?
3. Does `alphaOff`/`betaOff` (18 unfolds, 0 lemmas) deserve an interface, or is
   CGLMPQudit a leaf computation where transparency is honest?
4. `WignerRigidity.lean` and the two Shor files: refactor candidates, or
   necessarily computational and fine as-is?
5. Should any of the 1,102 single-use lemmas be generalised *when next touched*
   (not as a sweep — the paper's finding was about statements proved too narrow
   to reuse, and the test is the next consumer that fails to reuse one).

The guard is not a CI gate and must not become one on these numbers: 118+26+1102
"findings" as a blocking gate would be a proxy worshipped as a target — the
paper's own warning.
