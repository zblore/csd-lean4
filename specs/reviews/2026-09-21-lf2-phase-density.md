# Batch 004: phase independence, partitions and preparation densities

Reviewer: Codex. Date: 2026-09-21. Baseline: `330e8248b17884d21cbbccbd937b12b339026fe3`
plus the local review edits recorded by blob in the coverage register.

## Scope and assessment

Five additional files received a complete definition, statement, proof and comment pass:

| File under CsdLean4/LF2 | Assessment |
|---|---|
| BornWrapper.lean | Effect/density definitions, unitary conjugation, outer-product algebra, spectral expansion, Born pairing and certainty-to-purity proof are valid. The purity proof correctly uses a PSD zero-trace sandwich and then the PSD zero-quadratic-form criterion. Several comments still described a removed axiom or future covariance work. |
| PhaseInvariance.lean | Correct unit-modulus cancellation in outer products and proof-irrelevant wrapper equalities. Generalized the outer-product lemma from Fin N to arbitrary finite indices and connected the previously advertised effect-function consequence. |
| Weights.lean | Correct normalization of a probability-measure partition up to null sets. Added the documented transfer from a reference-measure partition under absolute continuity. No identification of arbitrary preparation laws with the reference measure is assumed. |
| PreparationQdensity.lean | Valid composition of the operational package with the proved effect-Gleason representation, followed by entropy and trace-distance bounds. Its channel theorem is deliberately general; the flow connection exists in a separate module. |
| PreparationBarycenter.lean | Correct entrywise integral construction, Hermitian/PSD/unit-trace proofs, trace-form identification, uniqueness comparison and Radon–Nikodym formula. Added phase invariance for the matrix and preparation density; clarified which hypotheses the separate region-preparation result discharges. |

Also rechecked the new code in EffectFn.lean and Preparation.lean against their batch-003
review, and refreshed Interface.lean after its Weights dependency changed. Those three
files do not count again. Their prior reports remain linked in the register.

Supporting source checks included the entropy and data-processing theorem signatures,
SigmaLayer/PreparationDensityBridge's actual hypotheses, the FlowChannel header and
its advertised covariance theorem, and pinned Mathlib matrix/measure APIs. These are
supporting checks, not full-file completion for those modules. In particular, this is
not a new complete review of EffectGleason's reconstruction proof.

## CR-LF2-005: phase independence connected in Lean

The existing outer-product theorem showed that multiplying a vector by a complex scalar
of norm one leaves its projector unchanged. The advertised connection to effect
probabilities was missing from the API. This batch adds:

1. `effectProjFn_phase_invariant`: pointwise unit phases leave the entire effect
   function unchanged. The proof transports outer-product equality through the trace
   pairing using pinned Mathlib's `mul_vecMulVec` and `trace_vecMulVec`.
2. `OperationalPackage.fromPreparation_phase_invariant`: integrating those functions
   gives the same probability for every effect in the preparation package.
3. `barycenterMatrix_phase_invariant`: the averaged projector matrix is unchanged,
   for any finite index type, including product indices.
4. `preparationDensity_phase_invariant`: using the existing barycentre identification,
   the density operator selected by effect-Gleason is unchanged too.

The outer-product lemma is generalized in place to arbitrary finite indices, matching
BornWrapper's existing definition. Existing Fin N calls still infer their types; the
repository has no callers supplying an explicit `(N := ...)` to this lemma. No new
terminal closure or assumed phase-independence field is introduced.

The algebraic function/matrix identities need neither unit norm of the representative
nor measurability of the phase. The probability-package/density statements assume unit
representatives and measurable phases so both constructed packages are well formed.
They compare phase-related maps; they do not identify arbitrary maps into different rays.
The matrix statement for arbitrary measures is an equality of identical integral
expressions, not a claim that an arbitrary such integral is a normalized density.

## CR-LF2-007: stale axiom/covariance description

BornWrapper's category and introduction still said it imported `busch_effect_gleason`,
contradicting both its current code and its later history note. Corrected these to point
to the downstream proved representation theorem. Also corrected the pure-state wrapper's
cross-reference and the distinction between its explicit trace-agreement premise and
the stronger certainty-based theorem.

The operational-package comment proposed a future covariance API. It now distinguishes
invariance of a fixed preparation from covariance of transformed preparations and points
to existing `LF2/FlowChannel.lean:barycenter_flow`. This does not add covariance as a
new operational field or assert that an arbitrary SectorData flow lifts a unitary.
The raw outer-product docstring now includes the zero-vector boundary: rank at most one,
with unit vectors giving rank-one projectors. Production statements are unchanged.

## CR-LF2-008: transfer measurable partitions

`MeasurablePartition.of_absolutelyContinuous` transports a partition relative to `ν`
to one relative to `μ` when `μ ≪ ν`. Parts and measurability proofs are retained; absolute
continuity transports both null intersections and the null uncovered set. The existing
`weights_sum_eq_one` consumes the resulting partition unchanged.

This formalizes the consequence already described in the module header. The direction
of absolute continuity matters: a reference-null set need not be preparation-null
without it. No general reference/preparation-measure equality follows from this helper.

## CR-LF2-009: clarify density/flow scope

PreparationBarycenter described the region-preparation formula as having "no hypothesis".
The actual theorem in SigmaLayer/PreparationDensityBridge retains bridge and structural
hypotheses; it discharges the separate absolute-continuity premise. The header now states
that precise result. PreparationQdensity now describes its channels as general inputs
and points to the existing flow connection, instead of suggesting that connection is
still absent. These corrections do not weaken any Lean statement.

## Boundary and design observations

- In dimension zero, a unit vector or trace-one density cannot exist. The statements
  using those inputs are consequently empty in that case; arbitrary outer-product
  identities remain valid, including the zero vector. No hidden positive-dimension
  assumption was needed for the added identities.
- The Radon–Nikodym formula explicitly assumes absolute continuity; the raw barycentre
  and its identification do not. Finite-measure integrability is proved from measurable
  bounded coordinates before sums and integrals are interchanged.
- The existing concrete LF2 bridge witness remains a build consumer, providing
  nonvacuity for the preparation construction. The new general identities are not a
  new derivation of the physical preparation protocol or of Born weights from regions.
- Matrix operations use pinned Mathlib's trace, PSD, action and integral APIs. No new
  parallel matrix or measure representation was introduced.

## Validation

All final checks passed on 2026-09-21:

- `lake build --wfail CsdLean4.LF2.PreparationBarycenter CsdLean4.LF2.Interface CsdLean4.Tests.Witnesses.LF2Bridge CsdLean4.LF2.PreparationPurity CsdLean4.LF2.PreparationCoarseGraining CsdLean4.LF2.FlowChannel CsdLean4.LF3.Interface`
  completed successfully (3177 jobs, mostly cached). This includes the existing Fin N
  phase wrappers and the changed definitions' operational, density and flow consumers.
- The reproducible `lake env lean --stdin` probe below passed: point-dependent phases
  on product indices, the non-identity phase `Complex.I`, explicit scalar values 4 and
  1 showing why non-unit scaling is excluded, and partition transfer into the existing
  weight-normalization theorem.
- Eight axiom checks in that probe report only `[propext, Classical.choice, Quot.sound]`:
  the generalized outer-product lemma, all four new phase lemmas, the partition
  constructor, the existing certainty-to-purity theorem and the barycentre identification.
- `check-doc-promises.sh`, `check-category-tags.sh`, `check-references.sh`,
  `check-semantic-mutations.sh`, `check-claims.sh`, and `git diff --check` passed.
  The existing reference-coverage advisory remains; it is not full citation verification.

The initial effect-function builds exposed pointwise conjugation and dot-product ordering
mismatches in the new proof. Explicit finite-sum simplification (`Matrix.mulVec`,
`dotProduct`, `Pi.star_apply`, `mul_comm`) resolved both. Direct checking and the final
consumer build passed; no production Lean error remains from this batch.

Coverage at completion: 20 of 691 tracked Lean files (2.89%). Five new full reviews plus
three source/dependency refreshes; the refreshed files were not counted a second time.
The register's `check` validates the recorded source/context snapshots.

Full library/test builds and all blocking CI checks remain required before integration.
This is a targeted dependency review, not part of the still-pending statistical pilot;
review/repair time was not separately instrumented.

## Next work

CR-LF2-006 remains open: review the LF3 fixed-ray callers against the intended projected
flows. Read LF3/Interface.lean and LF3/PurePreparation.lean alongside the relevant
FlowChannel sections, splitting the latter into partial slices if needed. The quantum
information consumers built here receive no review credit until read in full.

## Reproducible Lean probe

Run this with `lake env lean --stdin` after the focused build:

```lean
import CsdLean4.LF2.PreparationBarycenter
import CsdLean4.LF2.Weights

open CSD.LF2 MeasureTheory Matrix

#print axioms outerProduct_phase_invariant
#print axioms effectProjFn_phase_invariant
#print axioms OperationalPackage.fromPreparation_phase_invariant
#print axioms barycenterMatrix_phase_invariant
#print axioms preparationDensity_phase_invariant
#print axioms MeasurablePartition.of_absolutelyContinuous
#print axioms rankOneDensity_unique_of_certainty
#print axioms preparationDensity_eq_barycenter

-- The generalized index includes composite systems, and the phase can vary by point.
example {Q : Type*} [MeasurableSpace Q]
    (rep : Q → EuclideanSpace ℂ (Fin 2 × Fin 3)) (μ : Measure Q) (choosePhase : Q → Bool) :
    barycenterMatrix (fun p => (if choosePhase p then Complex.I else -1) • rep p) μ
      = barycenterMatrix rep μ := by
  classical
  apply barycenterMatrix_phase_invariant
  intro p
  split_ifs <;> simp

-- An actual non-identity phase leaves the effect function unchanged.
example {P : Type*} {N : ℕ} (rep : P → EuclideanSpace ℂ (Fin N)) (E : Effect N) :
    effectProjFn (fun p => Complex.I • rep p) E = effectProjFn rep E :=
  effectProjFn_phase_invariant rep (fun _ => Complex.I) (fun _ => by simp) E

-- Non-unit scaling changes the quadratic value: 4 rather than 1 in dimension one.
example : effectProjFn (fun _ : Unit => WithLp.toLp 2 (fun _ : Fin 1 => (2 : ℂ)))
    Effect.one () = 4 := by
  norm_num [effectProjFn, Effect.one, Matrix.one_mulVec, dotProduct]

example : effectProjFn (fun _ : Unit => WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ)))
    Effect.one () = 1 := by
  norm_num [effectProjFn, Effect.one, Matrix.one_mulVec, dotProduct]

-- The transferred reference partition feeds the existing normalization theorem.
example {SigmaSpace P G : Type*}
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace] [MeasurableSpace P]
    [Group G] [MulAction G SigmaSpace] [MulAction G P] [MulAction.IsPretransitive G P]
    (D : SectorData SigmaSpace P G) (μprep : Measure SigmaSpace)
    [IsProbabilityMeasure μprep] {ν : Measure P} {n : ℕ}
    (partition : MeasurablePartition P ν n) (habs : Measure.map D.π μprep ≪ ν) :
    ∑ i, projectiveWeight D μprep (partition.parts i) = 1 :=
  weights_sum_eq_one D μprep (partition.of_absolutelyContinuous habs)
```
