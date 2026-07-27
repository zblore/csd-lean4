/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.DeIsolationFlow
public import CsdLean4.SigmaLayer.RecordedFact

/-!
# SigmaLayer/FibreRecord: the record layer as a `RecordSemantics` instance (MD-1, step 3)

**Category:** 7-SigmaLayer (the record layer — the ontic record of the fibre outcome).

This wires the record-layer fibre partition into the corpus's **postulate-P5 record infrastructure**
(`SigmaLayer/RecordedFact.lean`): the de-isolation outcome becomes a genuine `RecordedFact`, and its
ontic event is the fibre cell `cdfCell`. This is step 3 of `specs/record-layer-plan.md` — the *record*
half — and it makes the record-layer readout a first-class `RecordSemantics`, the intended replacement
for the ad-hoc, preparation-indexed `LF5/PointerOutcome.lean` (`vnPointerOutcome`) readout.

Concretely, on the fibre `Σ = ℝ`:
* a **context** is a nonnegative rate vector `FibreContext` (the measurement `M` applied to the
  prepared state — the moment-map/Born rates over the outcomes);
* the **record event** of "context `c` recorded outcome `i`" is the CDF cell `cdfCell c.rate i`
  (`fibreRecordSemantics`), measurable, and **exclusive** within a context — distinct outcomes have
  disjoint cells (from `cdfCell_pairwiseDisjoint`);
* the **ontic selection** `fibreOutcome` records `i` at a fibre point exactly when the point lies in
  the record event (`fibreOutcome_eq_some_iff`) — the selection *is* the record;
* the **compatible region** of a single record is that cell (`compatibleSet_fibre_single`), so
  isolation on this record is conditioning on the outcome cell (the P6 story of `RecordedFact.lean`);
* **Born meets the record:** for the Born context, the fibre typicality of the record event is exactly
  `‖ψ i‖²` (`fibreTypicality_bornRecord`) — the ontic typicality of *recording* outcome `i` is the
  Born weight.

What this is **not**: the record events here are the fibre cells `cdfCell c.rate`, whose measures are
the (context-fixed-probability) Born weights, but whose *rate data* still comes with the state. The
context-fixed-region form of Paper C A7 and the physical de-isolation flow generating the cells remain
the open items (plan §3c / step 2b′); this file discharges the record-*infrastructure* obligation, not
those. Foundational-triple, no `sorry`.

## References
`specs/record-layer-plan.md` (record layer, MD-1; step 3 = the record); `SigmaLayer/RecordedFact.lean`
(`RecordSignature`, `RecordSemantics`, `compatibleSet`, postulates P5/P6); `SigmaLayer/DeIsolationFlow.lean`
(`fibreTypicality`, `fibreTypicality_bornCell`); `SigmaLayer/BornFibrePartition.lean`
(`cdfCell`, `cdfCell_pairwiseDisjoint`, `fibreOutcome`, `bornRate`); `LF5/PointerOutcome.lean`
(`vnPointerOutcome`, the prep-indexed readout this replaces).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ}

/-- **A measurement context on the fibre:** a nonnegative rate vector over the `n` outcomes. In the
record layer this is the context `M` applied to the prepared state — the moment-map/Born rates. -/
structure FibreContext (n : ℕ) where
  /-- The outcome rates (the moment-map weights of the context). -/
  rate : Fin n → ℝ
  /-- The rates are nonnegative. -/
  rate_nonneg : ∀ i, 0 ≤ rate i

/-- The **fibre record signature (P5 data):** contexts are rate vectors, outcomes are `Fin n`. -/
def fibreSignature (n : ℕ) : RecordSignature where
  Context := FibreContext n
  Outcome := fun _ => Fin n

/-- **The fibre record semantics (P5) on `Σ = ℝ`.** The ontic event of "context `c` recorded outcome
`i`" is the CDF cell `cdfCell c.rate i`: measurable (`measurableSet_cdfCell`), and within one context
at one time distinct outcomes are mutually exclusive — a fibre point cannot lie in two different
outcome cells (from `cdfCell_pairwiseDisjoint`). This is the record-layer readout as a first-class
`RecordSemantics`. -/
noncomputable def fibreRecordSemantics (n : ℕ) : RecordSemantics ℝ (fibreSignature n) where
  event r := cdfCell r.context.rate r.outcome
  measurable_event _ := measurableSet_cdfCell _ _
  exclusive c a b _ x ha hb := by
    by_contra hab
    exact absurd hb (Set.disjoint_left.mp (cdfCell_pairwiseDisjoint c.rate c.rate_nonneg hab) ha)

@[simp] theorem fibreRecordSemantics_event (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    (fibreRecordSemantics n).event ⟨c, i, t⟩ = cdfCell c.rate i := rfl

/-- The compatible region of the single-record history `[⟨c, i, t⟩]` is exactly the outcome cell:
isolation on this record conditions the ontic state onto the fibre cell. -/
theorem compatibleSet_fibre_single (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    compatibleSet (fibreRecordSemantics n) [⟨c, i, t⟩] = cdfCell c.rate i := by
  rw [compatibleSet_cons, compatibleSet_nil, Set.inter_univ, fibreRecordSemantics_event]

/-- **The ontic selection is the record.** The outcome map records `i` at a fibre point exactly when
that point lies in the record event `⟨c, i, t⟩` — reading the de-isolation outcome and testing
membership in the record event agree. -/
theorem fibreOutcome_eq_record (c : FibreContext n) (i : Fin n) (t : OnticTime) (ξ : ℝ) :
    fibreOutcome c.rate ξ = some i ↔ ξ ∈ (fibreRecordSemantics n).event ⟨c, i, t⟩ := by
  rw [fibreRecordSemantics_event]
  exact fibreOutcome_eq_some_iff c.rate c.rate_nonneg ξ i

/-- The **Born context** of a state: the rate vector is the Born rates `‖ψ i‖²`. -/
noncomputable def bornContext (ψ : EuclideanSpace ℂ (Fin n)) : FibreContext n where
  rate := bornRate ψ
  rate_nonneg := bornRate_nonneg ψ

@[simp] theorem bornContext_rate (ψ : EuclideanSpace ℂ (Fin n)) :
    (bornContext ψ).rate = bornRate ψ := rfl

/-- **Born meets the record.** For the Born context the fibre-typicality measure of the record event
of outcome `i` is exactly `‖ψ i‖² = |⟨eᵢ, ψ⟩|²`: the ontic typicality of *recording* outcome `i` is
the Born weight. This is the record-layer form of the Born rule — the outcome probability is the
typicality of the ontic record event. -/
theorem fibreTypicality_bornRecord (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n)
    (t : OnticTime) :
    fibreTypicality ((fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩)
      = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  rw [fibreRecordSemantics_event, bornContext_rate]
  exact fibreTypicality_bornCell ψ hψ i

end CSD.RecordLayer
