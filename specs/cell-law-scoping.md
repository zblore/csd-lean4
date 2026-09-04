# Cell-law scoping: what forces the outcome rates, and what does not

**Status:** created 2026-09-04, **resolved the same day**. Scopes `specs/POSITS.md` Posit 1. Stage 1
is done (`CsdLean4/RecordLayer/CellLawFreedom.lean`); the characterisation landed by a **different
route** — argument A below, formalised at the linear level in
`CsdLean4/RecordLayer/CellLawForced.lean` (`torusGenerated_eq_momentMap`). The frame-function
stage 2 was **declined, not attempted**, and its cost analysis is kept below as the record of why.

## The question

`RecordLayer/GlobalBasin.lean` defines `momentContext : ContextField N`, whose rate is the
Fubini–Study torus moment map, and `globalBasin_born` reads the Born weights off the fibre partition
at that field. Corpus prose has described this as *the rates being forced by the Kähler structure,
not injected*. The question this note scopes: **forced by what, exactly, and verified where?**

Three candidate forcing arguments, and they have very different standing.

| # | Argument | Standing |
|---|----------|----------|
| A | Symplectic: a rate field **generating** the torus is the moment map | ✅ **PROVED** at the linear level — `torusGenerated_eq_momentMap` |
| B | Symmetry: the rates are torus-**invariant** and normalised, hence the moment map | ❌ **Invalid** — refuted, stage 1 |
| C | Cross-basis consistency: a rate field additive under merging outcomes is a frame function | ⛔ **DECLINED** — costs noncontextuality; not needed once A landed |

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
outcome `0` the rate `⅔` while `sqRate` gives `8/9`. So argument **B is refuted**. At the time this
was written B was the only one of the three the Lean corpus verified, which made the cell law a bare
posit relative to the machine-checked corpus. That held for about an hour — see argument A below.

**What stage 1 does not do.** It does not touch argument A. `sqRate` is torus-invariant but is not a
moment map — there is no `ι_{X_i} ω = d(sqRateᵢ)` — so the symplectic uniqueness argument stands
untouched, and the corrected prose must keep it rather than deny it. Nor does stage 1 claim that
*nothing* in the corpus distinguishes the two fields: the Duistermaat–Heckman pushforward results
(`fs_moment_pushforward_uniform`, `fs_moment_joint_dirichlet_N`) and the flow-carved witness
(`shearDeIsolationInteraction`) are proved asymmetries. They are asymmetries, not characterisations,
and no record-layer selection argument currently invokes them.

## Argument A — LANDED (2026-09-04), and it is the answer

`RecordLayer/CellLawForced.lean`. The gap between A and B is one word: `sqRate` is **invariant**
under the torus; the moment map **generates** it. Generation is the moment-map equation
`ι_{X_i} ω = dΦᵢ`, and it does pin the field.

* ★ `isPhaseHamiltonian_coordEnergy` — the coordinate energy `‖xᵢ‖²/2` generates the `i`-th phase
  rotation. This is the instantiation, at the coordinate projection, of the corpus's existing
  `quadraticEnergy_hamiltonian_duality` — an ingredient that had been sitting in
  `Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean` unused.
* ★ `IsPhaseHamiltonian.eq_coordEnergy_add` — uniqueness up to an additive constant, from
  `is_const_of_fderiv_eq_zero` on the connected flat model.
* ★★ `torusGenerated_eq_momentMap` — a `ContextField` whose rates generate the phase rotations **is**
  the moment map. Exactly, and with no side hypothesis: the additive constant dies by *homogeneity*
  (the rate is a function of the ray, the homogenisation has degree two, so `k = 4k`), not by the
  simplex axioms and not by any `N ≥ 2` assumption.
* ★ `sqContext_not_torusGenerated` — and the stage-1 rival fails the generating condition, in one
  line from the two modules together.

**Why the manifold API turned out not to be needed.** The forcing argument needs the moment-map
equation on the *vector space* `ℂᴺ`, where `ω` is constant and a single global chart covers
everything; the descent to `ℂℙᴺ⁻¹` is by explicit degree-0 homogenisation inside `IsTorusGenerated`.
The manifold statement — that this is the moment map of the `Tⁿ` action on `ℂℙᴺ⁻¹` for `ω_FS` — is
still unformalised and is **posited** (author decision 2026-09-04: Kähler and manifold structure are
a reasonable posit). Blocking on `MATHLIB-ABSENT(file:Mathlib/Geometry/Manifold/DifferentialForm)`
was the wrong read: that wall stands for the manifold form, not for forcing.

⚠️ **What A does not do.** `IsTorusGenerated` is extensionally equivalent to the conclusion, so this
is a characterisation and Posit 1 is **restated, not discharged**. Nothing in the corpus compels a
context's rates to generate its pointer torus; deriving that from the de-isolation dynamics is the
`H_int` frontier. The gain is anti-circularity — the premise mentions no probability.

## Stage 2 — DECLINED (not open, not answered)

⛔ **Do not re-raise this as queued work.** Argument A landed instead, so the corpus does not need
argument C, and taking it would *cost* something the programme is not willing to spend. Recorded
here in full because the reasoning is the valuable part, and because "we could still try Gleason"
is the kind of suggestion that recurs. The frame-function question itself remains open mathematics;
it simply no longer carries corpus status.

The candidate was this. A rate field defined for **every** orthogonal decomposition, and
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

`RecordLayer/CellLawFreedom.lean` (stage 1, the refutation of B);
`RecordLayer/CellLawForced.lean` (argument A, the characterisation);
`Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean`
(`quadraticEnergy_hamiltonian_duality`, the linear machinery A instantiates);
`specs/POSITS.md` (Posit 1, restated);
`RecordLayer/GlobalBasin.lean` (`ContextField`, `momentContext`, `globalBasin_born`);
`RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap`); `LF4/MomentMap.lean` (the definition and
its boundary note); `LF4/MomentUniform.lean`, `LF4/MomentDirichletN.lean` (the DH pushforward laws);
`LF2/EffectGleason.lean` (`effect_gleason_representation`); `specs/future-work.md`;
`specs/TERMS.md` (Kähler, Liouville, Hamiltonian).
