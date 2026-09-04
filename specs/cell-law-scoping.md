# Cell-law scoping: what forces the outcome rates, and what does not

**Status:** created 2026-09-04. Scopes `specs/POSITS.md` Posit 1. Stage 1 is **done**
(`CsdLean4/RecordLayer/CellLawFreedom.lean`); stage 2 is **open and unstarted**.

## The question

`RecordLayer/GlobalBasin.lean` defines `momentContext : ContextField N`, whose rate is the
Fubini–Study torus moment map, and `globalBasin_born` reads the Born weights off the fibre partition
at that field. Corpus prose has described this as *the rates being forced by the Kähler structure,
not injected*. The question this note scopes: **forced by what, exactly, and verified where?**

Three candidate forcing arguments, and they have very different standing.

| # | Argument | Standing |
|---|----------|----------|
| A | Symplectic: a moment map for `Tⁿ` is unique up to a constant; the simplex pins it | **Sound, unformalised** — no symplectic API in Mathlib |
| B | Symmetry: the rates are torus-invariant and normalised, hence the moment map | **Invalid** — refuted, stage 1 |
| C | Cross-basis consistency: a rate field additive under merging outcomes is a frame function | **Open** — stage 2 |

The prose sites were, in effect, asserting A while citing Lean lemmas that only support B — and B is
false. That is the defect: not the claim, but its attribution.

## Stage 1 — done (2026-09-04)

`RecordLayer/CellLawFreedom.lean` builds `sqRate p i = (momentMap p i)² / ∑ₖ (momentMap p k)²` and
shows it is a `ContextField` in good standing (`sqContext`) with every property the corpus verifies
of the moment map:

* torus-invariant — `sqRate_phaseDiag_invariant`
* normalised, non-negative, measurable — the `ContextField` fields
* the same support — `sqRate_eq_zero_iff`
* it drives the whole basin machinery — `globalBasin_prob_sqContext`

and yet **★★ `rate_field_not_forced_by_torus_symmetry`**: at `[(2,1,1)] ∈ ℂℙ²` the moment map gives
outcome `0` the rate `⅔` while `sqRate` gives `8/9`. So argument **B is refuted**. Since B is the
only one of the three that the Lean corpus could be said to verify, the honest position is: *the
cell law is a posit relative to the machine-checked corpus.*

**What stage 1 does not do.** It does not touch argument A. `sqRate` is torus-invariant but is not a
moment map — there is no `ι_{X_i} ω = d(sqRateᵢ)` — so the symplectic uniqueness argument stands
untouched, and the corrected prose must keep it rather than deny it. Nor does stage 1 claim that
*nothing* in the corpus distinguishes the two fields: the Duistermaat–Heckman pushforward results
(`fs_moment_pushforward_uniform`, `fs_moment_joint_dirichlet_N`) and the flow-carved witness
(`shearDeIsolationInteraction`) are proved asymmetries. They are asymmetries, not characterisations,
and no record-layer selection argument currently invokes them.

## Stage 2 — open: does cross-basis consistency force it?

The natural remaining candidate. A rate field defined for **every** orthogonal decomposition, and
additive when outcomes are merged, is a *frame function*; for `N ≥ 3` that is Gleason's hypothesis,
and Gleason's theorem would then force the rates to be `tr(ρ Pᵢ)` — the Born form.

**Why this is not a quick win, and may not be wanted at all.**

1. **The corpus's Gleason-type result points the other way.** `effect_gleason_representation`
   (`LF2/EffectGleason.lean`, Route B) fixes a *state* and varies *effects*. The cell law fixes a
   *context* and varies the *state*. Whether the one transfers to the other is genuinely open; do
   not assume it.
2. **⚠️ The cost, which is the sharpest point in this note.** Cross-basis consistency is a
   **noncontextuality** assumption. If that is what forces the cell law, then "Gleason-free" — a
   standing corpus claim — remains true of the *volume theorem* and becomes **false of the choice of
   cell law**. Those are two different claims and the distinction must survive any prose sweep.
   Buying the cell law with noncontextuality would be a real change in the programme's commitments,
   not a technical tidy-up, and CSD is on record as contextual.
3. **A single context may not constrain enough.** The record layer as built fixes one context at a
   time; a frame-function hypothesis is a statement about the whole family of contexts at once, so
   stage 2 would first have to give the record layer a notion of a *family* of contexts. That is
   structural work, not a lemma.

**Acceptance for stage 2, if it is attempted:** either a theorem that a cross-basis-consistent
`ContextField` family is `momentContext`, or an honest no-go showing what such a family would have
to assume. Either outcome closes the question; neither should be started without settling (2) first.

## References

`RecordLayer/CellLawFreedom.lean` (stage 1); `specs/POSITS.md` (Posit 1);
`RecordLayer/GlobalBasin.lean` (`ContextField`, `momentContext`, `globalBasin_born`);
`RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap`); `LF4/MomentMap.lean` (the definition and
its boundary note); `LF4/MomentUniform.lean`, `LF4/MomentDirichletN.lean` (the DH pushforward laws);
`LF2/EffectGleason.lean` (`effect_gleason_representation`); `specs/future-work.md`;
`specs/TERMS.md` (Kähler, Liouville, Hamiltonian).
