# Batch 007: exact circle readout and evolved effect probabilities

Reviewer: Codex. Date: 2026-09-22. Baseline:
`eb8fdf1eaa5fd86ac1159a25562ce8604a2f4f49` plus the recorded local edits.
The preceding exclusive-outcome batch was committed at the user's request.

## Scope

Two previously partial files received full code and comment reviews:

| File under CsdLean4 | Assessment |
|---|---|
| RecordLayer/CircleRecord.lean | Record-event exclusivity, single-record compatibility, outcome selection and normalized Born probabilities are valid. The old almost-everywhere proof was correct, but its explanation incorrectly inferred pointwise coverage from full support. Proved exact coverage from cumulative intervals and unique pointwise readout, then reduced the old theorem to the empty uncovered set. Corrected stale migration and consumer descriptions. |
| LF2/FlowChannel.lean | Reviewed all pushforward/integral identities, pure and mixed environment constructions, spectral Kraus normalization, product-measure barycentres, projective lifts and reindexing. The hypotheses support the statements. Added the effect-probability consequence of barycentre covariance and clarified the supplied lift/product hypotheses. |

CircleFibre received an in-place coverage extension and re-review. Its earlier review
counts once; prior evidence is [batch 006](2026-09-22-exclusive-singlet-outcomes.md). C1BellConsistency and SingletBell were refreshed after the additive import
change, with their own source and mathematical claims unchanged. Supporting inspections
of TorusRecord, GlobalRecordClosure, FlowBornFrequency and concrete channel consumers
are not full-review credit for those files.

## CR-RECORD-002: exact totality proved

Haar full support says every nonempty open set has positive measure. It does not imply
that every measure-zero set is empty, so it cannot upgrade an almost-everywhere readout
theorem to pointwise totality. This construction nevertheless supports that upgrade:

- `iUnion_circleCell` proves that rates summing to one cover every circle point. It uses
  pinned Mathlib's `Ioc_subset_biUnion_Ioc`, applied to cumulative finite sums, and the
  canonical representative in `(0,1]`. Endpoint membership is retained explicitly.
- Coverage alone does not require nonnegative rates: even a non-monotone chain of
  consecutive intervals contains the interval between its initial and final endpoints.
  Nonnegativity remains required for the separate disjointness/uniqueness argument.
- `circleOutcome_total` combines exact coverage and existing disjointness to give a
  unique recorded outcome at each point for normalized nonnegative rates.
- `circleBornMeasurement_cover` specializes coverage to a unit state's rates.
  The existing `circleBornMeasurement_ae_total` retains its signature and now follows
  because the uncovered set is empty, rather than by a measure-only calculation.

Zero-weight cells may be empty without making gaps. If there are no outcome indices,
the normalization premise is impossible. If normalization is absent, the zero-rate
example below yields no outcome everywhere. No measurability or full-support premise
is used to prove the combinatorial coverage statement.

CircleRecord also said nothing outside axiom auditing imported it and that the torus
successor was still future work. GlobalRecordClosure already imports and reuses its
readout, and TorusRecord already exists. Updated those references without asserting
that a readout theorem proves a measurement interaction or the full sector geometry.

## CR-LF2-010 and CR-LF2-006: effect probabilities along a flow

`fromPreparation_flow_apply` connects the existing operational package to the existing
barycentre evolution theorem. For a measurable flow with the stated projector lift,
its effect probability is

    p_after(E) = Re Tr((U B_before U†) E).

The proof composes the proved preparation trace-form and barycentre identifications
with `barycenter_flow`. No fixed-ray premise or ambient measure-preservation premise
is introduced. The flowed preparation is a probability law by measurable pushforward.

`IsUnitaryLift` itself is a projector identity for a supplied matrix; it does not include
`U†U = I`. The matrix identity and new probability identity need only that lift, whereas
the channel constructors separately require unitarity. The new doc comments state this
boundary. Also corrected the suggestion that the open-system channel required no supplied
data: the theorem constructs it from U and the ready environment and proves the connection
under its lift and product-preparation hypotheses.

The mixed-environment result requires a product preparation, a projector-level tensor
factorization, and the environment barycentre's positivity and unit trace. It is not a
claim that an arbitrary initially correlated preparation defines the same system channel.
The spectral construction and its square-root coefficients handle zero eigenvalues.
Matrix-only identities with total Bochner integrals do not by themselves assert that
arbitrary unnormalized representatives define physical density operators.

The full FlowChannel review is now complete. CR-LF2-006 remains open only for the concrete
recorded-event/measurement connection: audit the existing LF5/FlowBornFrequency and
LF6/MeasurementFlowChannel routes, checking their actual preparation laws and calibration.
Both routes already exist; this report does not claim the corpus lacks all dynamic frequency
results. Fixed-effect probabilities generally change under a unitary, so unchanged singlet
weights cannot simply be carried over to arbitrary projected dynamics.

## Validation

- Final build passed: `lake build --wfail CsdLean4.RecordLayer.CircleRecord CsdLean4.RecordLayer.GlobalRecordClosure CsdLean4.Tests.Witnesses.SingletBell CsdLean4.LF6.MeasurementFlowChannel CsdLean4.LF6.DecoherenceChannel` (3366 jobs).
- Passed: doc-promises, category-tags, claims, semantic-mutations, references and import-hygiene guards.
- Passed: three circle-boundary examples and five axiom checks below. Every audited declaration uses only propext, Classical.choice and Quot.sound.
- Review-register consistency and Git whitespace: checked at completion.

The old CircleRecord axiom pin was exercised directly. No new axiom or sorry is added.
Initial proof attempts required explicit finite-sum rewrites and current names for the
pinned set-difference lemma; final production builds pass with warnings treated as errors.
Full library/test targets and all blocking CI checks are still required before integration.

## Coverage and next work

32 of 691 tracked Lean files reviewed (4.63%). Both old partial reviews are now complete;
refreshed files are not counted again. Review completion is separate from issue closure.
Next: follow the concrete LF5/LF6 flow-to-measurement interfaces and retain CR-LF3-004's
separate projective-vector/phase question. The stratified pilot remains pending; targeted
review percentages do not estimate the corpus-wide defect rate or remaining effort.

## Reproducible boundary and axiom checks

Run with `lake env lean --stdin` after the focused build.

```lean
import CsdLean4.RecordLayer.CircleRecord
import CsdLean4.LF2.FlowChannel
open CSD CSD.RecordLayer CSD.LF2 MeasureTheory Set

example (x : CircleFibre) :
    circleOutcome (fun i : Fin 3 => if i = 1 then 1 else 0) x = some 1 := by
  apply (circleOutcome_eq_some_iff _
    (by intro i; split_ifs <;> norm_num) x 1).mpr
  have hlo : loSum (fun i : Fin 3 => if i = 1 then (1 : ℝ) else 0) 1 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    have hne : j ≠ 1 := by intro h; subst j; omega
    simp [hne]
  have hx : rep x ∈ Ioc 0 1 := by
    simpa only [rep, zero_add] using (AddCircle.equivIoc (1 : ℝ) 0 x).property
  simpa [circleCell, hlo] using hx

example : ∃! i,
    circleOutcome (fun i : Fin 3 => if i = 1 then 1 else 0) (0 : CircleFibre) = some i :=
  circleOutcome_total _ (by intro i; split_ifs <;> norm_num)
    (by norm_num [Fin.sum_univ_three]) _

example (x : CircleFibre) : circleOutcome (fun _ : Fin 2 => (0 : ℝ)) x = none := by
  simp [circleOutcome, circleCell, loSum]

/-- info: 'CSD.RecordLayer.circleBornMeasurement_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleBornMeasurement_ae_total
#print axioms CSD.RecordLayer.iUnion_circleCell
#print axioms CSD.RecordLayer.circleOutcome_total
#print axioms CSD.LF2.fromPreparation_flow_apply
#print axioms CSD.LF2.traceRight_barycenter_flow_prod
```
