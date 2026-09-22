# Batch 005: LF3 singlet calibration and concrete fibre flow

Reviewer: Codex. Date: 2026-09-22. Baseline:
`0ccd3b7b7c054ca420b2b9e2106f8413ccfec36d` plus this batch's local edits,
identified by Git blob and dependency context in the coverage register.

## Scope and result

Five additional files received a complete definition, statement, proof and comment pass:

| File under CsdLean4 | Assessment |
|---|---|
| LF3/SingletProjective.lean | Singleton preimages are measurable and disjoint under the stated hypotheses. OP identities correctly compose the supplied Born overlaps. The abstract bundle does not assert eigen-equations or orthogonality; exact representative-vector preimages are phase-sensitive and need not cover the target. Corrected obsolete axiom and future-constructor descriptions. |
| LF3/PurePreparation.lean | Calibration is a supplied structure field; weight_eq_P_st correctly composes it with direct Dirac integration. Added ofWeights to derive that field from calculated pre-event masses. Clarified the distinction between the ambient reference measure and the preparation pushforward used by OP. |
| LF3/Interface.lean | Eight- and four-conjunct packages correctly assemble their constituent results. All six frequency variants follow from the common-law SLLN with pairwise independent indicators for each fixed sector. The simultaneous variants swap countable quantifiers; they do not establish an outcome partition. Corrected the claimed proof route and independence requirements. |
| LF4/SingletKahler.lean | Dirac-product preparation, circle-arc mass calculation, isometry transport of genuine singlet vectors, and calibration are valid. Genericity excludes zero-weight contexts. The anchored regions overlap. Refactored the constructor through ofWeights while retaining its public type and data. |
| LF4/SingletKahlerFlow.lean | Product Haar translations preserve the preparation law, so pulled-back event masses retain their calibration. The zero shift is permitted; nonidentity requires the separately stated nonzero premise. Refactored through ofWeights and distinguished preparation-law preservation from ambient Liouville preservation. |

No false Lean theorem was found in these five files. The code change is an API and
proof-maintenance improvement, not a stronger Born derivation or removal of calibration
assumptions. Existing public theorem statements and structure fields are unchanged.

Supporting checks covered ContextMap, the concrete SingletBell witness, relevant
SpectralCarving and C1BellConsistency constructions, and FlowChannel's unitary-lift /
barycentre covariance sections. These supporting files are not credited as full reviews.
FlowChannel receives an explicit partial record; its entire module remains to be reviewed.

## CR-LF2-006: flow audit

The LF3 frequency chain does not call the LF2 ray-fixed helper and has no hypothesis
`π ∘ Φ = π`. Its scored events are already `Φ⁻¹' Ω`; calibration is required for those
actual pre-events. A repository caller search found only the old helpers' definitions
and audit references, not a production LF3 caller requiring migration.

The concrete stationary constructor uses identity flow. The moving-fibre constructor
uses a nonidentity translation for nonzero shifts, but fixes the projective ray. It proves
preservation of `kMuPsi`, the preparation measure. Ambient preservation alone would not
justify this step.

`LF2.FlowChannel.barycenter_flow` already handles nontrivial projective evolution under
an explicit unitary lift; `isUnitaryLift_of_smul` supplies such a lift from an equivariant
projective action and a unit section. Evolving the density does not in general preserve
its probabilities against fixed measurement effects. Therefore no unchanged-P_st claim
was generalized to arbitrary unitary evolution. The remaining work is a full FlowChannel
review and a precise evolved-state/measurement-frequency connection if the intended
terminal claim requires it. This broader issue remains open.

## CR-LF3-001: stale descriptions corrected

Removed claims that concrete constructors or reindex wiring were still future work,
that the chain depended on an imported Busch axiom, and that weight_eq_P_st consumed
sectorVolume_eq_LF2_Born or LF1_main_theorem_projective. The direct chain integrates
against the preparation pushforward and uses the supplied overlap identity. The separate
trace-form route is proved too; it has only foundational axioms.

Corrected the advertised independence requirement, the unused dimension bound on the
direct route, the zero-shift boundary, and the distinction between a calibrated family
of events and an exclusive outcome partition. These are material scope corrections,
not changes to the Lean conclusions.

## CR-LF3-002: shared calibration constructor

`PureSingletPreparation.ofWeights` accepts the existing raw data and proofs of
`μψ ((O_region s t).preEvent) = ofReal (P_st ...)`. It derives the OP bridge using
`OP_p_at_jointEig_eq_P_st_direct` and constructs the existing bundle. Both concrete LF4
constructors now supply just their measure calculation; duplicated direct-Born proof
steps are removed. This makes the actual model-specific obligation explicit and provides
a reusable entry point for a future disjoint-outcome construction. It does not claim to
prove the input calibration, and it introduces no new assumption into existing results.

## CR-LF3-003: exclusive-outcome integration remains open

The four `kRegion` arcs all start at zero. At the concrete perpendicular context all
weights are 1/4, so all four regions coincide and their intersection has positive
preparation mass. The existing convergence theorem is correct for these four event
indicators; it does not prove that each trial records exactly one of four outcomes.

This limitation was already recognized in SpectralCarving, which supplies shifted
arcs. C1BellConsistency separately constructs contextual single-outcome maps reproducing
the singlet table, and SingletBell contains both the frequency witness and that contextual
model witness. They must not be conflated merely because they use the same arena.

Next code task: inspect and reuse the existing single-outcome maps or shifted partition;
prove disjointness and coverage for the chosen event family; connect their masses through
ofWeights to the existing LF3 frequency API. Place any composition downstream of its
imports to avoid introducing an LF4-to-LF6 cycle. Preserve the anchored-region API where
other observable proofs rely on it. No claim of a new corpus-wide absence is made here.

## CR-LF3-004: vector outcomes versus rays

`MeasurementJointEig` records unit norm, vector distinctness and Born overlaps only.
Its concrete singlet instance uses genuine spin vectors, but the abstract type does not
encode operators, eigen-equations or orthogonality. `SingletProjectiveOutcome` uses exact
vector equality; a change of representative phase can change this set. Distinct vectors
can also represent the same ray, so replacing the definition by ray equality would not
preserve its disjointness theorem under the current assumptions.

The reviewed comments now state that boundary. A wider API decision remains open:
determine whether consumers need genuine projective measurement cells; if so, supply
ray-distinctness or orthogonality from the concrete construction, prove phase independence,
and migrate callers. The calibrated LF4 fibre events are a separate construction.

## Validation

- Final focused build passed: `lake build --wfail CsdLean4.LF4.SingletKahlerFlow CsdLean4.Tests.Witnesses.SingletBell CsdLean4.LF2.FlowChannel` (3180 jobs).
- `check-doc-promises.sh`, `check-category-tags.sh`, `check-references.sh`, `check-semantic-mutations.sh`, and `check-claims.sh` passed.
- Five Lean boundary examples passed: equal perpendicular-context regions, positive intersection mass, unchanged stationary and flow pre-event reductions, and identity at zero shift. Seven axiom probes returned only `[propext, Classical.choice, Quot.sound]`. Reproduce with the Lean input below via `lake env lean --stdin`.
- Coverage register consistency and Git whitespace check: checked before closing the batch.

Full library/test targets and all blocking CI guards remain required before integration.
This is a focused batch validation, not a claim that full CI ran.

## Progress and next work

25 of 691 tracked Lean files reviewed (3.62%); FlowChannel is partial and excluded.
Next: review the existing disjoint-outcome construction and connect its recorded outcomes
to the frequency API; then complete the flow/density review. The 30-file statistical pilot
is still pending. This targeted batch supplies no corpus-wide effort or defect-rate estimate.

## Reproducible boundary checks

```lean
import CsdLean4.LF4.SingletKahlerFlow
import CsdLean4.Tests.Witnesses.SingletBell
open CSD CSD.LF3 CSD.LF4 CSD.Tests.Witnesses MeasureTheory Set

example (s t s' t' : Sign) :
    kRegion perpContext s t = kRegion perpContext s' t' := by
  simp only [kRegion, perpContext_P_st]

example : 0 < kMuPsi
    (kRegion perpContext .plus .plus ∩ kRegion perpContext .plus .minus) := by
  have h : kRegion perpContext .plus .plus = kRegion perpContext .plus .minus := by
    simp only [kRegion, perpContext_P_st]
  rw [h, Set.inter_self, kMuPsi_kRegion, perpContext_P_st]
  norm_num

example (p₀ : CPN 4) (s t : Sign) :
    ((ofKählerPreparation perpContext p₀ perpContext_hgen).O_region s t).preEvent
      = kRegion perpContext s t := rfl

example (p₀ : CPN 4) (sh : KTorus) (s t : Sign) :
    ((ofKählerPreparationFlow perpContext p₀ sh perpContext_hgen).O_region s t).preEvent
      = kFlow sh ⁻¹' kRegion perpContext s t := rfl

example : kFlow (N := 4) (0 : KTorus) = id := by
  funext x
  simp [kFlow]

#print axioms CSD.LF3.PureSingletPreparation.ofWeights
#print axioms CSD.LF3.PureSingletPreparation.weight_eq_P_st
#print axioms CSD.LF3.OP_p_at_jointEig_eq_P_st
#print axioms CSD.LF3.LF3_singlet_frequency_convergence_joint
#print axioms CSD.LF4.ofKählerPreparation
#print axioms CSD.LF4.ofKählerPreparationFlow
#print axioms CSD.LF4.ofKählerPreparationFlow_flow_frequency_convergence
```
