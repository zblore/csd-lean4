import Mathlib.MeasureTheory.MeasurableSpace.Basic
import CsdLean4.SigmaLayer.ConstraintSurface

/-!
# FND/RecordedFact: physical records as measurable contextual ontic events

**Category:** 7-SigmaLayer (the Choice A ontological layer).

This is the genuinely new FND content: physical records represented as measurable, contextual,
time-indexed ontic events (postulate P5), and a finite record history whose compatible region is the
intersection of the corresponding events. Isolation (postulate P6) is then conditioning `muL` on this
compatible region; see `FND/IsolationPreparation.lean`.

## Scientific reading

A `RecordedFact` states that a contextual property had a specified value at a specified time. The
property may subsequently change; the historical record is not thereby invalidated. So the compatible
region records time-indexed evidence, and we do NOT require a value measured at time `t` to persist at
later times. Exclusivity is asserted only within a single context at a single time.
-/

namespace CSD.SigmaLayer

universe u v w

/-- **A record signature (postulate P5 data).** A type of measurement contexts, and for each context a
type of possible outcomes. -/
structure RecordSignature where
  /-- The type of measurement contexts. -/
  Context : Type u
  /-- For each context, the type of possible outcomes. -/
  Outcome : Context → Type v

/-- **A recorded fact.** A contextual property (`context`) had value `outcome` at time `time`. -/
structure RecordedFact (R : RecordSignature) where
  /-- The measurement context of the record. -/
  context : R.Context
  /-- The recorded outcome (in the context's outcome type). -/
  outcome : R.Outcome context
  /-- The ontic time at which the record was established. -/
  time : OnticTime

/-- **Record semantics (postulate P5).** Each recorded fact is interpreted as a measurable ontic event
(the region of `Sigma` compatible with that record), and within a single context at a single time the
events for distinct outcomes are mutually exclusive. No exclusivity is asserted across contexts. -/
structure RecordSemantics (Sigma : Type w) [MeasurableSpace Sigma] (R : RecordSignature) where
  /-- The measurable ontic event associated with a recorded fact. -/
  event : RecordedFact R → Set Sigma
  /-- Each record event is measurable. -/
  measurable_event : ∀ r, MeasurableSet (event r)
  /-- Within one context at one time, distinct outcomes have disjoint events (membership form): a
  state cannot simultaneously record two different outcomes of the same context at the same time. -/
  exclusive : ∀ (c : R.Context) (a b : R.Outcome c) (t : OnticTime) (x : Sigma),
    x ∈ event ⟨c, a, t⟩ → x ∈ event ⟨c, b, t⟩ → a = b

/-- A finite record history is a list of recorded facts (the time-indexed evidence). -/
abbrev RecordHistory (R : RecordSignature) := List (RecordedFact R)

variable {Sigma : Type w} [MeasurableSpace Sigma] {R : RecordSignature}

/-- **The compatible region of a record history.** The set of ontic states consistent with every
record in the history: `univ` for the empty history, and the intersection of the head event with the
tail's compatible region for a cons. This is the epistemic support during isolation. -/
def compatibleSet (S : RecordSemantics Sigma R) : RecordHistory R → Set Sigma
  | [] => Set.univ
  | (r :: H) => S.event r ∩ compatibleSet S H

@[simp] theorem compatibleSet_nil (S : RecordSemantics Sigma R) :
    compatibleSet S ([] : RecordHistory R) = Set.univ := rfl

@[simp] theorem compatibleSet_cons (S : RecordSemantics Sigma R)
    (r : RecordedFact R) (H : RecordHistory R) :
    compatibleSet S (r :: H) = S.event r ∩ compatibleSet S H := rfl

/-- The compatible region is measurable (intersection of measurable record events). -/
theorem compatibleSet_measurable (S : RecordSemantics Sigma R) (H : RecordHistory R) :
    MeasurableSet (compatibleSet S H) := by
  induction H with
  | nil => rw [compatibleSet_nil]; exact MeasurableSet.univ
  | cons r H ih => rw [compatibleSet_cons]; exact (S.measurable_event r).inter ih

/-- Membership in the compatible region is compatibility with every record in the history. -/
theorem mem_compatibleSet (S : RecordSemantics Sigma R) (H : RecordHistory R) (x : Sigma) :
    x ∈ compatibleSet S H ↔ ∀ r ∈ H, x ∈ S.event r := by
  induction H with
  | nil => simp [compatibleSet_nil]
  | cons r H ih => simp only [compatibleSet_cons, Set.mem_inter_iff, ih, List.mem_cons,
      forall_eq_or_imp]

/-- Every record in the history holds on the compatible region. -/
theorem mem_event_of_mem_compatibleSet (S : RecordSemantics Sigma R) {H : RecordHistory R}
    {x : Sigma} (hx : x ∈ compatibleSet S H) {r : RecordedFact R} (hr : r ∈ H) :
    x ∈ S.event r := (mem_compatibleSet S H x).1 hx r hr

/-- **Appending a record shrinks the compatible region.** More evidence never enlarges the compatible
support: `compatibleSet S (H ++ [r]) ⊆ compatibleSet S H`. -/
theorem compatibleSet_append_subset (S : RecordSemantics Sigma R) (H : RecordHistory R)
    (r : RecordedFact R) : compatibleSet S (H ++ [r]) ⊆ compatibleSet S H := by
  intro x hx
  rw [mem_compatibleSet] at hx ⊢
  exact fun r' hr' => hx r' (List.mem_append.mpr (Or.inl hr'))

/-- The compatible region of an appended history is the prior region intersected with the new event. -/
theorem compatibleSet_append_singleton (S : RecordSemantics Sigma R) (H : RecordHistory R)
    (r : RecordedFact R) :
    compatibleSet S (H ++ [r]) = compatibleSet S H ∩ S.event r := by
  ext x
  rw [mem_compatibleSet, Set.mem_inter_iff, mem_compatibleSet]
  constructor
  · intro h
    exact ⟨fun r' hr' => h r' (List.mem_append.mpr (Or.inl hr')),
      h r (List.mem_append.mpr (Or.inr (List.mem_singleton_self r)))⟩
  · rintro ⟨hH, hr⟩ r' hr'
    rcases List.mem_append.mp hr' with h | h
    · exact hH r' h
    · rw [List.mem_singleton.mp h]; exact hr

end CSD.SigmaLayer
