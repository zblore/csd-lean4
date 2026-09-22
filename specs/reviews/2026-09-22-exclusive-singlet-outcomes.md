# Batch 006: exclusive singlet outcomes and the frequency witness

Reviewer: Codex. Date: 2026-09-22. Baseline:
`b364cd441792b31a41121201bbfbf4a8728e2390` plus the reviewed local edits
identified by blob and context hash in the coverage register.

The preceding batch was committed as requested; this batch is separate local work.

## Full review scope

| File under CsdLean4 | Assessment |
|---|---|
| LF3/SharedContextMap.lean | The shared-domain map, discrete sign measurability, wing projections and real-valued responses are valid. Added reusable measurable-fibre, exact disjointness, exact coverage and indicator-sum lemmas. Non-measure statements do not retain a measurable-space premise. |
| RecordLayer/BornFibrePartition.lean | Cumulative ordering, disjointness, classical outcome selection, Born rates and union measures are valid. Measure identities do not require normalized rates; probability interpretations do. Corrected the claim of almost-everywhere totality on ambient R and distinguished measure identities from frequency theorems. |
| RecordLayer/CircleFibre.lean | Haar mass one, measurable canonical representative, disjoint right-closed arcs and their masses are valid. The volume proof uses the measure-preserving Ioc chart and explicitly bounds each interval within one turn. Corrected stale compact-record/product-measure work descriptions and clarified the endpoint convention. |
| LF6/C1BellConsistency.lean | The CHSH obstruction derives measurable local responses from compatibility, uses the four-setting bound and the strict singlet violation. The positive construction is total by its final fallback branch and reproduces the full table by cell masses and a complement calculation. Marginal and no-signalling corollaries are valid. Added a preparation adapter for the same recorded outcomes; reused the shared fibre lemmas. |
| Tests/Witnesses/SingletBell.lean | Concrete axes discharge genericity, setting dependence is nontrivial, and the Bell witnesses cite the existing production results. Replaced the frequency witness's overlapping events with the existing contextual model's exclusive recorded outcomes, added exact indicator normalization, and used the existing simultaneous LF3 convergence theorem. |

Supporting checks: CircleRecord's almost-everywhere totality proof; the existing LF3/LF4
preparation and frequency APIs; ContextMap's signatures; the referenced CHSH bound and
singlet-violation statements along the C1 proof path; the existing witness axiom pin.
These do not give new full-review credit to supporting files or dependencies.

## CR-LF3-003: fixed for the stationary frequency witness

The old witness counted four overlapping anchored regions. The C1 contextual model
already assigned a single sign pair to every sample, but the frequency witness did not
use that map. This batch connects the existing constructions:

1. SharedContextOutcomeMaps now exposes measurability, exact disjointness and coverage
   of its fibres, plus `sum_indicator_outcome_eq_one`. The latter needs no measure.
2. `singletContextualOutcomeRegion` packages the recorded sign-pair fibres as LF1 regions
   on the stationary Kähler sector.
3. `singletContextualPreparation` uses the existing trial law and static spin preparation,
   then feeds `singletContextualModel_table` into `PureSingletPreparation.ofWeights`.
   Its pre-event lemma identifies exactly which recorded event the LF3 theorem scores.
4. The existing `perpContext_singlet_frequency_convergence` now asserts exactly one
   outcome per state and, almost surely, convergence of all four recorded frequencies
   simultaneously to 1/4 under independent coordinate sampling.

This changes the witness's proposition and result shape: it is now a conjunction,
with simultaneous convergence in the second component. It also replaces the events
being scored; it is not merely a logically stronger statement about the old events.
A repository search found its existing axiom pin, and no production proof callers.
The anchored-region production theorem remains available unchanged. The validation
hardening matrix was updated in place; no rival capstone or claim row was introduced.
The C1 production capstone and its existing CL-052 row are unchanged.

The adapter is valid for generic contexts because `kJED` requires positive weights.
The underlying contextual outcome table is valid at every context, including collinear
zero-weight cases. Extending the spin-vector adapter to those cases is a separate issue;
it is not needed by the perpendicular witness. Flow-evolved measurements remain under
CR-LF2-006; this batch does not claim to settle their general integration.

This repairs the concrete frequency/Bell witness connection. It does not derive Born
weights from independent dynamics: the arc lengths still use the prescribed weights.

## CR-RECORD-001: measure domain and stale prose

BornFibrePartition's outcome-map comment said a probability vector made readout total
off a null set, without specifying the law. Its ambient measure is Lebesgue measure on
R, while the cells occupy a finite-measure set. Readout can be none outside that set;
the unit-rate, one-outcome probe below checks the value at 2. Corrected the comment and
the certainty/frequency interpretation of the measure-only statements. The real-line
probability construction elsewhere restricts Lebesgue measure to the unit interval.

CircleFibre still described compact readout and the torus product step as future work.
CircleRecord already provides compact record semantics, and C1BellConsistency already
proves the relevant singlet product mass. Updated these references and removed the
claim that restricted Lebesgue probability was only available by fiat. Also made explicit
that circle cells use Ioc while real-line cdfCell uses Ico.

No existing Lean theorem was found false. These comment corrections are material
interpretation fixes; the exclusive-outcome connection is the mathematical/API change.

## Wider follow-up

- Complete the partial FlowChannel review and specify evolved-state measurement weights
  before extending the stationary adapter (CR-LF2-006).
- Retain the projective-vector versus ray outcome issue (CR-LF3-004).
- Review CircleRecord in full. Its totality theorem is almost-everywhere, while its
  scope prose says uncovered points have nowhere to hide. Full support excludes
  nonempty open null sets, not arbitrary nonempty null sets; exact coverage needs
  its own argument. This supporting observation is tracked as CR-RECORD-002.

## Validation

- Passed: `lake build --wfail CsdLean4.Tests.Witnesses.SingletBell CsdLean4.RecordLayer.CircleRecord CsdLean4.RecordLayer.Measurement` (3227 jobs).
- Passed: doc-promises, category-tags, semantic-mutations, references and import-hygiene guards.
- Passed: claims guard and validation-ledger guard (76 linked headline claims).
- Passed: all six boundary examples below. The existing witness axiom guard passed; it and the three additional axiom checks use only propext, Classical.choice and Quot.sound.
- Git whitespace and review-register consistency: checked before completion.

An initial adapter build exposed a missing namespace qualification; the witness build
then required an explicit pre-event rewrite. A deprecated Mathlib rewrite name was
replaced with the pinned `Set.preimage_ofPred_eq`. Final builds are warning-free.
These were implementation fixes, not discovered corpus proof failures.

Full library/test targets and all blocking CI guards remain required before integration.
No full CI success is claimed for this focused batch.

## Coverage

30 of 691 tracked Lean files reviewed (4.34%). FlowChannel and CircleRecord remain partial and excluded.
The five prior batches are not counted again. No statistical pilot has been drawn;
these targeted reviews do not provide an unbiased defect-rate or effort forecast.

## Reproducible boundary and axiom checks

Run the following input through `lake env lean --stdin` after the focused build.

```lean
import CsdLean4.Tests.Witnesses.SingletBell
open CSD CSD.LF3 CSD.LF4 CSD.LF6 CSD.Tests.Witnesses MeasureTheory Set

example (C : MeasurementContext) :
    Disjoint {l | singletContextualModel.F C l = (Sign.plus, Sign.plus)}
      {l | singletContextualModel.F C l = (Sign.plus, Sign.minus)} :=
  singletContextualModel.outcome_fibres_disjoint C (by decide)

example (C : MeasurementContext) :
    (⋃ p : Sign × Sign, {l | singletContextualModel.F C l = p}) = univ :=
  singletContextualModel.iUnion_outcome_fibres C

example (p₀ : CPN 4) :
    (singletContextualPreparation perpContext p₀ perpContext_hgen).μψ = kMuPsi := rfl

example (p₀ : CPN 4) (s t : Sign) :
    ((singletContextualPreparation perpContext p₀ perpContext_hgen).O_region s t).preEvent
      = {l | singletContextualModel.F perpContext l = (s, t)} :=
  singletContextualPreparation_preEvent _ _ _ _ _

example : kMuPsi {l | singletContextualModel.F
    ⟨detector3 0 0 1 (by norm_num), detector3 0 0 1 (by norm_num)⟩ l
      = (Sign.plus, Sign.plus)} = 0 := by
  have hdot : dotR (detector3 0 0 1 (by norm_num))
      (detector3 0 0 1 (by norm_num)) = 1 := by
    rw [dotR]
    simp
  rw [singletContextualModel_table]
  change ENNReal.ofReal (P_st (detector3 0 0 1 (by norm_num))
    (detector3 0 0 1 (by norm_num)) Sign.plus Sign.plus) = 0
  rw [P_st, hdot]
  norm_num [Sign.val]

example : RecordLayer.fibreOutcome (fun _ : Fin 1 => (1 : ℝ)) 2 = none := by
  rw [RecordLayer.fibreOutcome_eq_none_iff]
  intro i
  fin_cases i
  norm_num [RecordLayer.cdfCell, RecordLayer.loSum]

/-- info: 'CSD.Tests.Witnesses.perpContext_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.perpContext_singlet_frequency_convergence
#print axioms CSD.LF6.singletContextualPreparation
#print axioms CSD.LF3.SharedContextOutcomeMaps.sum_indicator_outcome_eq_one
#print axioms CSD.LF6.c1_singlet_contextual_capstone
```
