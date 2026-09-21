# Batch 001: LF1 foundations

Reviewer: Codex. Date: 2026-09-17. Baseline: `c06f8e18512862876943602f0c9ff69611abcd9b`.
The checkout advanced externally to `330e824` during the review; the tracked LF1 files
were unchanged by those commits. Working LF1 edits were preserved.
Scope: all definitions, theorem statements, proof bodies, module/declaration docs and inline
comments in the five files below. Reviewed working-file blobs and import-context fingerprints
are stored in [corpus-review.tsv](../corpus-review.tsv).

| File under CsdLean4/LF1 | Code assessment | Comment assessment |
|---|---|---|
| Setup.lean | Coherent measurable-space/finite-measure/time-map input. No symplectic structure or flow group law is asserted by its type. | CR-LF1-002: corpus-wide nonuse/future-work descriptions had become stale. |
| Preparation.lean | Nonzero restricted mass is established before using normalization's nonzero branch. The division formula uses measurability and finite mass correctly. | No material mismatch found. The reflexive unfolding lemma is explicitly identified as definitional. |
| Outcomes.lean | Pullback/preparation events are measurable. Probability weight is the normalized preparation mass of the pullback. Empty and full events are allowed; no partition structure is claimed. | The simultaneous-family documentation now points to the theorem added in batch 002 (CR-LF1-003). |
| Trials.lean | Equal marginal laws are explicit; independence is not a field. Added a reusable arbitrary-pair distribution theorem (CR-LF1-001). | CR-LF1-001: header incorrectly described a product/i.i.d. model; structure doc incorrectly described identical distribution as an extra hypothesis. |
| Indicators.lean | Measurability, 0/1 bounds, integrability and identical distribution follow from the stated model. The frequency at N=0 uses Lean's zero-division convention; asymptotic results are unaffected. | Fixed the inline description of the auxiliary indicator's codomain. |

## Findings and repairs

### CR-LF1-001: equal laws versus independent sampling

`TrialModel.hLaw` gives each `X n` the preparation law. It cannot imply independence:
take one nondegenerate random variable and reuse it at every index. The `TrialModel`
conditions allow that correlated family.

The production frequency theorem already asks separately for pairwise independence of the
chosen outcome indicators. The corpus already has the stronger independent-product construction
in `Tests/Witnesses/IIDSampling.lean`; adding independence to every `TrialModel` would
unnecessarily restrict the interface and duplicate existing work.

Repair: expose `TrialModel.identDistrib_X (n m)` for any two sampled initial conditions and
reuse it in `indicatorRV_identDistrib`. This generalizes the previously local proof for
indices n and 0 and makes it available for other measurable observables. Align the comments
with the equal-law interface and point to the actual product construction.

Impact: useful Lean API extraction/generalization and a material clarification of an assumption.
No stronger final frequency theorem or derivation of independence is claimed.

### CR-LF1-002: obsolete corpus-wide measure-preservation claims

`Setup.lean` described full measure preservation as unused throughout the current corpus and
its LF4 use as future work. `LF4/KahlerFlow.lean` already proves
`kFlow_frequency_convergence`, whose evolved-law calculation uses `hmp.map_eq`.
The distinction matters: the abstract LF1 argument uses only measurability, while this
concrete later construction uses full measure preservation.

Repair: narrow the nonuse statement to the abstract route and cite the existing concrete
construction. The `OnticSetup` fields remain unchanged. Inspecting that consumer for this
claim does not count as a complete review of `KahlerFlow.lean`.

## Assumptions, boundary cases and dependencies

- `OnticSetup` assumes an inhabited measurable space, a finite measure, a measurable positive-mass
  preparation region and a measure-preserving map. This is supplied physical/model data.
- Positive preparation mass rules out the zero-measure normalization fallback; finiteness rules
  out division by infinite preparation mass.
- Outcome regions can be empty or universal. Nontriviality is not a claim of their structure.
- Trial-model equal laws neither force nor secretly assume independence. Empty sample spaces
  cannot carry the required probability measure.
- The indicator proofs use boundedness under a probability measure and measurable composition,
  not an independence assumption.
- Existing nondegenerate test evidence is the coin model in
  `Tests/Witnesses/LF1Trial.lean`. Its source was inspected for orientation; its full test target
  is not claimed built by the batch build.

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


## Next batch

Completed in [batch 002](2026-09-17-lf1-frequency.md): Expectation, Convergence,
GeneralFrequency, MainTheorem, and Witnesses/IIDSampling. Next: the LF2 bridge chain.
