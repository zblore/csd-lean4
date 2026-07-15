import CsdLean4.FND.RecordedFact
import CsdLean4.FND.ConstraintDynamics

/-!
# FND/TimeIndexedRecord: time-indexed records and their persistence under isolated evolution

**Category:** 7-FND (the Choice A ontological layer).

FND-T5 final follow-on. `RecordSemantics.event` already takes a full `RecordedFact` (context, outcome AND
time), but the concrete pointer semantics (`vnRecordSemantics`) ignored the recorded time — the event was
the same pointer fibre for every `t` (external review 2026-07-14: "ignores the recorded time"). This
module builds a genuinely TIME-INDEXED record semantics from the isolated dynamics, and proves the two
physical persistence facts.

* `flowedSemantics` — from a base outcome-region family and the isolated flow, the event of ⟨c,i,t⟩ is
  the set of ontic states whose time-`t` isolated evolution lies in the outcome region:
  `event ⟨c,i,t⟩ = Φ_t⁻¹'(region c i)`. A record asserts the outcome held at the state's time-`t`
  evolution, so it genuinely depends on `t`.
* `flowedSemantics_event_measure` — the record PROBABILITY is time-invariant:
  `μL(event ⟨c,i,t⟩) = μL(region c i)`, because the isolated flow preserves `μL`. The Born weight of a
  record is conserved by isolated evolution — persistence of the record probability.
* `flowedSemantics_event_flow` — record COVARIANCE: the record at a later time is the flow-preimage of the
  record at the earlier time, `event ⟨c,i,t+s⟩ = Φ_s⁻¹'(event ⟨c,i,t⟩)`. The time-indexed evidence
  transforms covariantly with the isolated dynamics (the "living history" evolves with the flow).
* `flowedSemantics_persistence` — bundles both.

## Honest scope

This makes records genuinely time-physical: the event uses the recorded time, the record probability is
conserved, and the evidence is flow-covariant. This is NOT a model of persistent apparatus MEMORY (a
pointer physically latching to its value and remaining there); consistent with `FND/RecordedFact.lean`, a
value recorded at time `t` is time-indexed evidence, not required to persist as a later value. A
latching-memory model would be a separate record-stability postulate.

References: `specs/future-work.md` (FND-T5 follow-on); `FND/RecordedFact.lean` (`RecordSemantics`, P5),
`FND/ConstraintDynamics.lean` (`flow_preserves`, `flow_add`), `FND/UnifiedMeasurement.lean` (the concrete
pointer regions that instantiate `region`).
-/

open MeasureTheory

namespace CSD.FND

universe u v w

variable {Sigma : Type w} [MeasurableSpace Sigma] {R : RecordSignature}
  (D : ConstraintDynamics Sigma)
  (region : (c : R.Context) → R.Outcome c → Set Sigma)
  (hmeas : ∀ c i, MeasurableSet (region c i))
  (hexcl : ∀ (c : R.Context) (a b : R.Outcome c) (y : Sigma),
    y ∈ region c a → y ∈ region c b → a = b)

/-- **A time-indexed record semantics from a base outcome-region family and the isolated flow.** The
event of a record ⟨c,i,t⟩ is the set of ontic states whose time-`t` isolated evolution lies in the
outcome region: `event ⟨c,i,t⟩ = Φ_t⁻¹'(region c i)`. Genuinely uses the recorded time `t`. -/
noncomputable def flowedSemantics : RecordSemantics Sigma R where
  event := fun r => D.flow r.time ⁻¹' region r.context r.outcome
  measurable_event := fun r => (D.measurable_flow r.time) (hmeas r.context r.outcome)
  exclusive := fun c a b t x ha hb => hexcl c a b (D.flow t x) ha hb

@[simp] theorem flowedSemantics_event (c : R.Context) (i : R.Outcome c) (t : OnticTime) :
    (flowedSemantics D region hmeas hexcl).event ⟨c, i, t⟩ = D.flow t ⁻¹' region c i := rfl

/-- **Record probability is time-invariant (persistence under isolated evolution).** The Liouville
measure of a record event does not depend on the recorded time: `μL(event ⟨c,i,t⟩) = μL(region c i)`,
because the isolated flow preserves `μL`. The Born weight of a record is conserved by isolated evolution. -/
theorem flowedSemantics_event_measure (c : R.Context) (i : R.Outcome c) (t : OnticTime) :
    (D.muL : Measure Sigma) ((flowedSemantics D region hmeas hexcl).event ⟨c, i, t⟩)
      = (D.muL : Measure Sigma) (region c i) := by
  rw [flowedSemantics_event]
  exact (D.flow_preserves t).measure_preimage (hmeas c i).nullMeasurableSet

/-- **Record covariance under the flow (the living history evolves with the dynamics).** The record at a
later time is the flow-preimage of the record at the earlier time: `event ⟨c,i,t+s⟩ = Φ_s⁻¹'(event
⟨c,i,t⟩)`. The time-indexed evidence transforms covariantly under isolated evolution. -/
theorem flowedSemantics_event_flow (c : R.Context) (i : R.Outcome c) (s t : OnticTime) :
    (flowedSemantics D region hmeas hexcl).event ⟨c, i, t + s⟩
      = D.flow s ⁻¹' (flowedSemantics D region hmeas hexcl).event ⟨c, i, t⟩ := by
  rw [flowedSemantics_event, flowedSemantics_event]
  ext x
  simp only [Set.mem_preimage]
  rw [D.flow_add t s x]

/-- **Record persistence (physical).** For every context/outcome, the time-indexed record probability is
conserved by isolated evolution AND the record transforms covariantly with the flow: records are genuine
time-physical evidence carried consistently by the isolated dynamics. -/
theorem flowedSemantics_persistence (c : R.Context) (i : R.Outcome c) :
    (∀ t, (D.muL : Measure Sigma) ((flowedSemantics D region hmeas hexcl).event ⟨c, i, t⟩)
        = (D.muL : Measure Sigma) (region c i))
    ∧ (∀ s t, (flowedSemantics D region hmeas hexcl).event ⟨c, i, t + s⟩
        = D.flow s ⁻¹' (flowedSemantics D region hmeas hexcl).event ⟨c, i, t⟩) :=
  ⟨fun t => flowedSemantics_event_measure D region hmeas hexcl c i t,
    fun s t => flowedSemantics_event_flow D region hmeas hexcl c i s t⟩

end CSD.FND
