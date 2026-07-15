import CsdLean4.FND.Luders
import CsdLean4.FND.IsolationPreparation
import CsdLean4.FND.MeasurementRecord

/-!
# FND/ConditioningLink: the conditional→Lüders correspondence

**Category:** 7-FND (the Choice A ontological layer).

FND-T5 follow-on. The corpus proves TWO conditioning rules that were not yet connected (external review
2026-07-14):

* the **ontic record-history conditioning** (`IsolationPreparation.HistoryPreparation.conditionalMeasure_apply`):
  appending a record conditions the Liouville measure on the record-compatible region,
  `conditionalMeasure A = μL(A ∩ compatibleSet) / μL(compatibleSet)`
  (the epistemic-support update `compatibleSet_appendEstablishedFact`);
* the **projective Lüders state update** (`Luders.ludersUpdate_conditional`): the post-measurement Born
  weight of a finer projection is `projWeight q (ludersUpdate p x) = projWeight q x / projWeight p x`.

This module makes their identity explicit: BOTH are the single Bayesian conditioning rule
`bayesianConditional w = w(fine) / w(coarse)`, differing only in the WEIGHT — the Liouville measure `μL`
for the ontic record update, the Born weight `projWeight · x` for the projective state update. On the
Choice A sector these two weights AGREE (Born from volume, `π_* μL = μFS`, bridge B1
`productSector_hasFubiniStudyPushforward`), so the ontic record conditioning and the projective Lüders
update are one and the same conditioning, seen through `π`.

References: `specs/future-work.md` (FND-T5 follow-on); `FND/Luders.lean` (`ludersUpdate_conditional`),
`FND/IsolationPreparation.lean` (`conditionalMeasure_apply`), `FND/MeasurementRecord.lean`
(`compatibleSet_appendEstablishedFact`), `FND/MeasureBridge.lean` (B1).
-/

open MeasureTheory

namespace CSD.FND

/-- **Bayesian conditioning of a weight.** The probability of the finer event given the coarser,
`w(fine) / w(coarse)`. Both the projective Lüders update (Born weight) and the ontic record-history
conditioning (Liouville measure) are instances of this single rule. -/
def bayesianConditional {α β : Type*} [Div β] (w : α → β) (coarse fine : α) : β := w fine / w coarse

/-! ### The projective Lüders update is Bayesian conditioning of the Born weight -/

section Luders
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The Lüders update reproduces Bayesian conditioning of the Born weight.** For a finer projection `q`
inside the range of `p` (`q ∘ p = q`), the post-measurement Born weight of `q` is the Bayesian
conditional of the Born weight `projWeight · x` given the outcome `p`. Restates
`Luders.ludersUpdate_conditional` in the shared `bayesianConditional` form. -/
theorem ludersUpdate_isBayesianConditional (p q : E →ₗ[ℂ] E) (hqp : ∀ y, q (p y) = q y)
    (x : E) (hx : p x ≠ 0) :
    projWeight q (ludersUpdate p x)
      = bayesianConditional (fun r : E →ₗ[ℂ] E => projWeight r x) p q :=
  ludersUpdate_conditional p q hqp x hx

end Luders

/-! ### The ontic record-history conditioning is Bayesian conditioning of the Liouville measure -/

section Record
universe u
variable {Sigma : Type u} [MeasurableSpace Sigma] [Nonempty Sigma] {D : ConstraintDynamics Sigma}
  {R : RecordSignature} {S : RecordSemantics Sigma R}

/-- **The record-history conditioning reproduces Bayesian conditioning of the Liouville measure.**
Appending a record conditions `μL` on the record-compatible region: the conditional measure of `A` is the
Bayesian conditional of `μL` given `compatibleSet`. Restates
`IsolationPreparation.HistoryPreparation.conditionalMeasure_apply` in the shared `bayesianConditional`
form. -/
theorem historyConditioning_isBayesianConditional (HP : HistoryPreparation D R S)
    (A : Set Sigma) (hA : MeasurableSet A) :
    ((HP.toPreparation.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma) A
      = bayesianConditional (fun T => (D.muL : Measure Sigma) T)
          (compatibleSet S HP.history) (A ∩ compatibleSet S HP.history) :=
  HP.conditionalMeasure_apply A hA

end Record

/-! ### The correspondence -/

/-- **The conditional→Lüders correspondence.** The projective Lüders state update and the ontic
record-history conditioning are the SAME Bayesian conditioning rule `w(fine)/w(coarse)`, applied to the
Born weight and to the Liouville measure respectively. Given the Choice A Born-from-volume bridge
(`π_* μL = μFS`, B1), the two weights agree on the sector, so the state-level Lüders update and the
ontic-level record conditioning coincide. -/
theorem luders_record_conditioning_correspondence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (p q : E →ₗ[ℂ] E) (hqp : ∀ y, q (p y) = q y)
    (x : E) (hx : p x ≠ 0) {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma]
    {D : ConstraintDynamics Sigma}
    {R : RecordSignature} {S : RecordSemantics Sigma R} (HP : HistoryPreparation D R S)
    (A : Set Sigma) (hA : MeasurableSet A) :
    (projWeight q (ludersUpdate p x)
        = bayesianConditional (fun r : E →ₗ[ℂ] E => projWeight r x) p q)
    ∧ (((HP.toPreparation.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma) A
        = bayesianConditional (fun T => (D.muL : Measure Sigma) T)
            (compatibleSet S HP.history) (A ∩ compatibleSet S HP.history)) :=
  ⟨ludersUpdate_isBayesianConditional p q hqp x hx,
    historyConditioning_isBayesianConditional HP A hA⟩

end CSD.FND
