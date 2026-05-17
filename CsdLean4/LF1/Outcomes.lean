import CsdLean4.LF1.Preparation

/-!
# LF1 Outcomes

**Category:** 3-Local (LF1 outcome regions and their weights).

Outcome regions are measurable ontic regions associated with a fixed
experimental context. In LF1 they are treated abstractly as measurable sets.
The realised outcome of a single trial is determined by whether the deterministic
evolution of the sampled microstate lands in the corresponding outcome region.

No stochastic outcome law is postulated at this stage.

## Coding choice: single region, not a partition family

The manuscript describes a measurable outcome partition {Ω_i^Σ} of the ontic state space.
This file formalises one element of that partition at a time via `OutcomeRegion`.

This is deliberate and mathematically sufficient for LF1: the frequency theorem is proved
for an arbitrary fixed `O : OutcomeRegion`. To obtain the joint almost-sure statement for
a finite partition {O_1, ..., O_k}, apply the theorem once per element and intersect the
resulting full-measure sets — a finite intersection of full-measure sets is still
full-measure, so no new structure is needed.

A formalised `OutcomePartition` type (carrying disjointness, exhaustion, and a measurable
family) would be the right object if a future layer (LF2/LF4) needs to reason about
partition sums such as Σ_i weight(O_i) = 1 or POVM completeness. That extension should
be built in the layer that first requires it, not here.
-/

open MeasureTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

/-- A single measurable outcome region in the ontic state space.
    Parameterized by `S` so that `S.OutcomeRegion` works as dot notation. -/
structure OutcomeRegion {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    (_S : OnticSetup SigmaSpace) where
  Ω : Set SigmaSpace
  hΩ_meas : MeasurableSet Ω

namespace OutcomeRegion

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
         {S : OnticSetup SigmaSpace} (O : OutcomeRegion S)

/-- The pullback event of an outcome region under the deterministic flow `Φ`. -/
noncomputable def preEvent : Set SigmaSpace :=
  S.Φ ⁻¹' O.Ω

lemma measurable_preEvent : MeasurableSet O.preEvent :=
  O.hΩ_meas.preimage S.measurable_Φ

/-- The preparation-side version of the event. -/
noncomputable def prepEvent : Set SigmaSpace :=
  S.Ω0 ∩ O.preEvent

lemma measurable_prepEvent : MeasurableSet O.prepEvent :=
  S.hΩ0_meas.inter O.measurable_preEvent

/-- The outcome weight under the preparation probability measure. -/
noncomputable def weight : ENNReal :=
  ((S.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) O.preEvent

/-- The outcome weight as a real number, for use in convergence statements. -/
noncomputable def weightReal : ℝ :=
  ENNReal.toReal O.weight

/-- The outcome weight equals the Liouville volume of `prepEvent` divided
by `μL(Ω0)`: `weight = μL(Ω0 ∩ Φ⁻¹(O.Ω)) / μL(Ω0)`.

Connects the abstract `weight` (defined via `prepMeasure`) to the
preparation-side initial-condition event `prepEvent = Ω0 ∩ Φ⁻¹(O.Ω)`. The
right-hand side is the fraction of the preparation region whose
deterministic evolution lands in the outcome region: the volume-typicality
reading of the weight. -/
lemma weight_eq_prepEvent_div :
    O.weight (S := S) =
      (S.μL : Measure SigmaSpace) O.prepEvent / (S.μL : Measure SigmaSpace) S.Ω0 := by
  unfold weight prepEvent
  rw [S.prepMeasure_apply O.preEvent O.measurable_preEvent]
  congr 1
  rw [Set.inter_comm]

end OutcomeRegion

end OnticSetup

end LF1
end CSD
