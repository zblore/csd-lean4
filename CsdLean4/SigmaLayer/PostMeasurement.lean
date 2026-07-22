/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.SigmaLayer.IsolationPreparation
import CsdLean4.SigmaLayer.MeasurementRecord

/-!
# SigmaLayer/PostMeasurement: the post-outcome isolation preparation

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

SL-T5 follow-on. A de-isolating measurement establishes a `RecordedFact` and appends it to the record
history (`appendEstablishedFact`, `compatibleSet_appendEstablishedFact`:
`compatibleSet (history ++ [r]) = compatibleSet history ∩ event r`). The external review (2026-07-14)
flagged that the corpus did not yet PROVE the extended history has nonzero compatible measure, nor
construct the resulting post-measurement `HistoryPreparation`. This module does both.

* `HistoryPreparation.appendFact` — given that the established outcome is POSSIBLE
  (`μL(compatibleSet ∩ event r) ≠ 0`), the extended history is a valid `HistoryPreparation`: its
  compatible region `compatibleSet ∩ event r` has nonzero Liouville measure, so its conditional law is
  well defined.
* `HistoryPreparation.appendFactOfPos` — the same, from outcome-possibility phrased as positive
  conditional probability `conditionalMeasure(event r) ≠ 0`: the post-outcome preparation exists exactly
  when the established outcome had positive probability in the current isolated law.
* `HistoryPreparation.appendFact_conditionalMeasure_apply` — the post-measurement epistemic law is `μL`
  conditioned on `compatibleSet ∩ event r`: the Bayesian update of the isolated law on the new record.

This closes the measurement/record loop on the unified model: measure, establish a record, and the state
updates to a genuine (nonzero-measure) post-outcome preparation whose conditional law is the Bayesian
update. Its `bayesianConditional` form is the ontic half of the conditional→Lüders correspondence
(`SigmaLayer/ConditioningLink.lean`).

References: `specs/future-work.md` (SL-T5 follow-on); `SigmaLayer/IsolationPreparation.lean`
(`HistoryPreparation`, `conditionalMeasure_apply`), `SigmaLayer/MeasurementRecord.lean`
(`appendEstablishedFact`, `compatibleSet_appendEstablishedFact`, `DeisolationModel.establishedFact`),
`SigmaLayer/ConditioningLink.lean` (`bayesianConditional`).
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace CSD.SigmaLayer

universe w

variable {Sigma : Type w} [MeasurableSpace Sigma] [Nonempty Sigma]
  {D : ConstraintDynamics Sigma} {R : RecordSignature} {S : RecordSemantics Sigma R}

/-- **The post-measurement isolation preparation.** After a de-isolation establishes the record `r`,
provided the outcome is possible (`μL(compatibleSet ∩ event r) ≠ 0`), the extended history
`appendEstablishedFact history r` is a valid `HistoryPreparation`. Its compatible region is
`compatibleSet ∩ event r` (`compatibleSet_appendEstablishedFact`), which has nonzero Liouville measure —
so the post-outcome conditional law is well defined. -/
def HistoryPreparation.appendFact (HP : HistoryPreparation D R S) (r : RecordedFact R)
    (hpos : (D.muL : Measure Sigma) (compatibleSet S HP.history ∩ S.event r) ≠ 0) :
    HistoryPreparation D R S where
  history := appendEstablishedFact HP.history r
  nonzero_compatible := by rw [compatibleSet_appendEstablishedFact]; exact hpos

@[simp] theorem HistoryPreparation.appendFact_history (HP : HistoryPreparation D R S)
    (r : RecordedFact R)
    (hpos : (D.muL : Measure Sigma) (compatibleSet S HP.history ∩ S.event r) ≠ 0) :
    (HP.appendFact r hpos).history = appendEstablishedFact HP.history r := rfl

/-- The post-measurement compatible region is the prior region intersected with the record event. -/
theorem HistoryPreparation.appendFact_compatibleSet (HP : HistoryPreparation D R S)
    (r : RecordedFact R)
    (hpos : (D.muL : Measure Sigma) (compatibleSet S HP.history ∩ S.event r) ≠ 0) :
    compatibleSet S (HP.appendFact r hpos).history = compatibleSet S HP.history ∩ S.event r :=
  compatibleSet_appendEstablishedFact HP.history r

/-- **The post-measurement conditional law.** After establishing `r`, the epistemic state is `μL`
conditioned on `compatibleSet ∩ event r`:
`muH'(A) = μL(A ∩ (compatibleSet ∩ event r)) / μL(compatibleSet ∩ event r)` — the Bayesian update of the
isolated law on the newly established record. -/
theorem HistoryPreparation.appendFact_conditionalMeasure_apply (HP : HistoryPreparation D R S)
    (r : RecordedFact R)
    (hpos : (D.muL : Measure Sigma) (compatibleSet S HP.history ∩ S.event r) ≠ 0)
    (A : Set Sigma) (hA : MeasurableSet A) :
    ((HP.appendFact r hpos).toPreparation.conditionalMeasure : Measure Sigma) A =
      (D.muL : Measure Sigma) (A ∩ (compatibleSet S HP.history ∩ S.event r)) /
        (D.muL : Measure Sigma) (compatibleSet S HP.history ∩ S.event r) := by
  rw [HistoryPreparation.conditionalMeasure_apply (HP.appendFact r hpos) A hA,
    HistoryPreparation.appendFact_compatibleSet]

/-- **The post-outcome preparation exists exactly when the outcome was possible.** Build the
post-measurement preparation from outcome-possibility phrased as positive conditional probability
`conditionalMeasure(event r) ≠ 0`: an outcome with positive probability in the current isolated law can be
conditioned on, yielding a genuine (nonzero-measure) post-outcome preparation. -/
def HistoryPreparation.appendFactOfPos (HP : HistoryPreparation D R S) (r : RecordedFact R)
    (hcpos : (HP.toPreparation.conditionalMeasure : Measure Sigma) (S.event r) ≠ 0) :
    HistoryPreparation D R S :=
  HP.appendFact r (by
    rw [HistoryPreparation.conditionalMeasure_apply HP (S.event r) (S.measurable_event r)] at hcpos
    intro h0
    apply hcpos
    rw [Set.inter_comm] at h0
    rw [h0, ENNReal.zero_div])

end CSD.SigmaLayer
