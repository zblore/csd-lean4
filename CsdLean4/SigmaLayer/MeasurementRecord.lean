/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.SigmaLayer.ConstraintDynamics
import CsdLean4.SigmaLayer.RecordedFact

/-!
# SigmaLayer/MeasurementRecord: de-isolating measurement and record establishment

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Bridge assumptions B4, B5. A `DeisolationModel` is a physical interaction (measure-preserving, per
context) together with preparation-dependent outcome regions and a partial readout. De-isolation is a
deterministic interaction followed by a contextual readout that establishes a new `RecordedFact`
(`establishedFact`). The outcome regions may depend on the preparation, as the LF5 pointer-outcome
construction requires. Totality is not required everywhere (boundaries may have measure zero); the
`AETotalReadout` predicate states almost-everywhere completeness for a given preparation measure.

We do NOT assume that later ontic states retain the measured value: a record states that a value held at
its time, not for all later times. Persistent apparatus memory would be a separate record-stability
model.
-/

open MeasureTheory

namespace CSD.SigmaLayer

universe u v w

variable {Sigma : Type u} [MeasurableSpace Sigma]

/-- **A de-isolating measurement model (B4, B5 interface).** A measure-preserving interaction per
context, preparation-dependent measurable pairwise-disjoint outcome regions, and a partial readout
whose `some i` values are exactly membership in the `i`-th outcome region. -/
structure DeisolationModel (D : ConstraintDynamics Sigma) (R : RecordSignature)
    (S : RecordSemantics Sigma R) (Prep : Type w) where
  /-- The measurement interaction at a time and context. -/
  interaction : OnticTime → (c : R.Context) → Sigma → Sigma
  /-- Each interaction is measurable. -/
  measurable_interaction : ∀ t c, Measurable (interaction t c)
  /-- Each interaction preserves the Liouville measure. -/
  interaction_preserves : ∀ t c,
    MeasurePreserving (interaction t c) (D.muL : Measure Sigma) (D.muL : Measure Sigma)
  /-- The preparation-dependent outcome regions. -/
  outcomeRegion : Prep → (c : R.Context) → R.Outcome c → Set Sigma
  /-- Each outcome region is measurable. -/
  measurable_outcomeRegion : ∀ p c i, MeasurableSet (outcomeRegion p c i)
  /-- Distinct outcomes have disjoint regions. -/
  pairwise_disjoint : ∀ p c, Set.PairwiseDisjoint Set.univ (outcomeRegion p c)
  /-- The partial contextual readout. -/
  readout : Prep → (c : R.Context) → Sigma → Option (R.Outcome c)
  /-- The readout returns `some i` exactly on the `i`-th outcome region. -/
  readout_eq_some_iff : ∀ p c x i, readout p c x = some i ↔ x ∈ outcomeRegion p c i

namespace DeisolationModel

variable {D : ConstraintDynamics Sigma} {R : RecordSignature} {S : RecordSemantics Sigma R}
  {Prep : Type w} (Mdl : DeisolationModel D R S Prep)

/-- **The established fact.** De-isolation with preparation `p`, context `c`, at time `t`: interact,
then read out; a `some i` readout establishes the record `⟨c, i, t⟩`. -/
def establishedFact (p : Prep) (c : R.Context) (t : OnticTime) (x : Sigma) :
    Option (RecordedFact R) :=
  (Mdl.readout p c (Mdl.interaction t c x)).map (fun i => ⟨c, i, t⟩)

/-- **Almost-everywhere total readout (a form of B4).** For a given preparation measure the readout is
defined for almost every initial ontic state after the interaction. Boundaries of measure zero are
permitted. -/
def AETotalReadout (p : Prep) (c : R.Context) (t : OnticTime) (mu : Measure Sigma) : Prop :=
  ∀ᵐ x ∂mu, (Mdl.readout p c (Mdl.interaction t c x)).isSome

/-- **The post-measurement record is compatible with the realised outcome region (B5).** If the readout
after the interaction is `some i`, the post-interaction state lies in the record event `S.event ⟨c,i,t⟩`.
Stated as a predicate; proved for concrete models where the record semantics matches the outcome regions. -/
def RecordsEstablishedOutcome : Prop :=
  ∀ (p : Prep) (c : R.Context) (t : OnticTime) (x : Sigma) (i : R.Outcome c),
    Mdl.readout p c (Mdl.interaction t c x) = some i →
    Mdl.interaction t c x ∈ S.event ⟨c, i, t⟩

end DeisolationModel

/-! ### Record-history update -/

variable {R : RecordSignature} {S : RecordSemantics Sigma R}

/-- Append an established fact to a record history. -/
def appendEstablishedFact (Hist : RecordHistory R) (r : RecordedFact R) : RecordHistory R :=
  Hist ++ [r]

/-- **The post-measurement compatible region.** Appending the new record intersects the prior compatible
region with the new record's event: `compatibleSet S (appendEstablishedFact Hist r) =
compatibleSet S Hist ∩ S.event r`. This is the conditional update of the epistemic support (ordinary
conditioning; not called Lüders update until an equality with the Lüders rule is proved). -/
theorem compatibleSet_appendEstablishedFact (Hist : RecordHistory R) (r : RecordedFact R) :
    compatibleSet S (appendEstablishedFact Hist r) = compatibleSet S Hist ∩ S.event r :=
  compatibleSet_append_singleton S Hist r

end CSD.SigmaLayer
