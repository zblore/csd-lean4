# Batch 002: LF1 frequency chain and independent-product witness

Reviewer: Codex. Date: 2026-09-17. Baseline at completion: `330e824`, plus the working
LF1 changes recorded by blob in [corpus-review.tsv](../corpus-review.tsv).
Scope: every definition, statement, proof body and comment in the five files below.

| File under CsdLean4 | Assessment |
|---|---|
| LF1/Expectation.lean | Correct indicator-integral calculation under a probability measure; event probabilities are finite before conversion to real numbers. All expectations agree from equal marginal laws, without independence. |
| LF1/Convergence.lean | Correct use of Etemadi's pairwise-independence strong law, with integrability and identical distribution proved upstream. The weight identification is proved, not an additional caller assumption. |
| LF1/GeneralFrequency.lean | Valid law-agnostic theorem under weaker hypotheses than its i.i.d. wording suggested. The common target law is a probability measure by measurable pushforward; no explicit extra instance is missing. CR-LF1-004 corrects the scope description. |
| LF1/MainTheorem.lean | Existing single-region statement was valid. CR-LF1-003 formalizes the advertised simultaneous-family consequence and makes the existing single-region API a specialization. |
| Tests/Witnesses/IIDSampling.lean | Correct product construction: coordinate maps have the preparation law and independently sampled coordinates yield pairwise-independent measurable indicators. The frequency theorem is applied, not assumed or re-proved. The supplied OnticSetup remains an input. |

## CR-LF1-003: put simultaneous convergence into Lean

The MainTheorem and Outcomes headers explained that a finite family follows by intersecting
full-measure sets, but the public frequency API only stated the single-region result.

Added `TrialModel.main_theorem_ae_all` for a countable family. It combines the existing
per-region theorem using Mathlib's `ae_all_iff`
(`Mathlib/MeasureTheory/OuterMeasure/AE.lean:97`). One full-measure set supports convergence
for every outcome in the family. The only independence required is across trials for each
selected outcome; no independence between outcomes or disjointness assumption is added.

The existing `main_theorem_ae` retains its signature and is the Unit-indexed specialization.
Its top-level alias and current consumers remain unchanged. This strengthens the existing LF1
API, without introducing another closure/capstone or deriving independence from equal laws.

The finite partition use case is included; the empty index type is vacuous as expected.
The countability hypothesis is essential to this intersection argument and is explicit.
No claim is made for an uncountable family of arbitrary measurable regions.

## CR-LF1-004: state the actual independence requirement

`freq_tendsto_of_iid` takes pairwise independence only of the chosen indicator process,
not independence of the full state-valued trials. Updated its module/declaration comments
to state that requirement. Retained the existing public name and signature for callers,
with a note that i.i.d. trials are a sufficient special case.

Pinned Mathlib's `strong_law_ae_real` at `Probability/StrongLaw.lean:598` has exactly
the pairwise-independence form used here. This was a description mismatch; no false
convergence theorem was found.

## Validation

Post-change validation passed:

- `lake build --wfail CsdLean4.Tests.Witnesses.IIDSampling CsdLean4.LF1.GeneralFrequency`
  (3031 jobs, mostly cached): covers the LF1 chain and its independent-product witness.
- Read-only `lake env lean --stdin` axiom checks for `TrialModel.identDistrib_X`,
  `TrialModel.main_theorem_ae_all`, `OnticSetup.LF1_main_theorem_ae`, and
  `Witnesses.iidTrialModel_frequency_convergence`: each reports only
  `[propext, Classical.choice, Quot.sound]`.
- `scripts/check-doc-promises.sh`, `scripts/check-category-tags.sh`,
  `scripts/check-references.sh`, and `git diff --check` passed.
- `python -B scripts/test_corpus_review.py`: five tests passed, covering source/dependency
  invalidation, toolchain drift, added/retired paths, partial/historical status and import parsing.

The initial family-theorem build caught missing explicit `(S := S)` arguments; these were
corrected before the successful build above. No pending Lean build error remains in this batch.
Review/repair time was not separately instrumented; these targeted batches are excluded from
statistical effort estimates. Full `CsdLean4`/`CsdLeanTests` builds and all blocking CI guards
remain required before integration; the focused build is not a substitute for them.


## Next review batch

LF2/Setup.lean, LF2/MeasureBridge.lean, LF2/EffectFn.lean, LF2/Preparation.lean,
LF2/Interface.lean. Reconcile the older foundational ledger's bridge/probability findings
against the current definitions before proposing repairs. This is a targeted batch,
not part of the still-pending stratified random pilot.
