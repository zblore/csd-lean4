/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CircleFibre
public import CsdLean4.RecordLayer.Measurement

/-!
# RecordLayer/CircleRecord: the record layer, re-plumbed onto the compact fibre

**Category:** 7-SigmaLayer (the record layer — A1 compactness).

`CircleFibre.lean` moved the Born *partition* onto a compact fibre. This moves the rest of the
record layer with it: the postulate-P5 record semantics, the isolation-is-conditioning reading,
measurement-as-`context + unknown microstate → record`, the Born probabilities, and the
pointwise totality of the normalized readout — all on `CircleFibre = AddCircle 1` instead of `ℝ`.

The point is that **nothing physical changes**. The record signature is reused *verbatim*
(`fibreSignature`: contexts are non-negative rate vectors, outcomes are `Fin n`) — it never
mentioned the fibre — so only the *semantics*, the assignment of ontic events, is different. Every
Born weight comes out identical (`volume_circleCell`), which is the content of the swap.

## What this gives

* `circleRecordSemantics` — a postulate-P5 `RecordSemantics` on the **compact** `CircleFibre`:
  events are the circle Born arcs, measurable and mutually exclusive within a context.
* `compatibleSet_circle_single` — isolation is conditioning: the states compatible with one record
  are exactly that record's arc (the P6 reading).
* `circleOutcome_eq_record` — the ontic selection *is* the record: reading which arc the microstate
  occupies agrees with testing membership of the record event.
* `CircleMeasurement` / `prob` / `circleBornMeasurement` — measurement as context-plus-microstate,
  with `circleBornMeasurement_prob : prob i = ‖ψ i‖²`.
* `circleOutcome_total` — normalized nonnegative rates give a unique outcome at
  every circle point, using exact consecutive-arc coverage.
* `circleBornMeasurement_cover` — unit-state basins cover the whole circle.
  The existing `circleBornMeasurement_ae_total` follows as a measure corollary.

## What is still not claimed

Compactness and a genuine Haar probability measure, yes. **A1 in full, no** — and ⚠️ **not for the
reason an earlier version of this docstring gave.** It said `dω = 0` was blocked on Mathlib's absent
manifold exterior calculus. The real obstruction is **dimension parity**: `ℂℙⁿ⁻¹ × AddCircle 1` has
real dimension `2n-1`, which is odd, and no odd-dimensional manifold admits a symplectic — hence a
Kähler — structure. More tooling would not fix it. The successor construction moves to
`KSigma = ℂℙⁿ⁻¹ × T²` (real dimension `2n`, even), putting the Born arcs on one torus coordinate;
see `CircleFibre.lean`'s scope note and the ★★ `BACKLOG.md` row. The fibre measure is also exhibited
as Haar, not shown to be a Liouville measure.

This file provides the circle counterpart of the real-line semantics. The corpus
also has `TorusRecord.lean` on the even-dimensional fibre and
`GlobalRecordClosure.lean` on the compact sector; the latter imports this module
and reuses `circleOutcome`. The older real-line closure remains available.
The general measurement-dynamics and closure-migration obligations belong to
those modules and the current BACKLOG; this circle result is a readout theorem.

## References

`RecordLayer/CircleFibre.lean` (the compact fibre and its Born arcs);
`RecordLayer/FibreRecord.lean`, `RecordLayer/Measurement.lean` (the `ℝ` originals this mirrors);
`SigmaLayer/RecordedFact.lean` (`RecordSemantics`, and the warning that it is trivially inhabited —
the content is in the non-vacuity results, of which `circleBornMeasurement_ae_total` is one);
`specs/BACKLOG.md` (the ★★ fibre/A1 row).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ}

/-! ### The P5 record semantics on the compact fibre -/

/-- **The circle record semantics (P5) on the compact `Σ`-fibre.** The ontic event of "context `c`
recorded outcome `i`" is the Born arc `circleCell c.rate i` — measurable, and within one context at
one time distinct outcomes are mutually exclusive.

The *signature* is `fibreSignature`, reused unchanged: it only ever mentioned rate vectors and
outcome indices, never the fibre. Swapping `ℝ` for the circle touches the semantics alone. -/
noncomputable def circleRecordSemantics (n : ℕ) :
    RecordSemantics CircleFibre (fibreSignature n) where
  event := fun r => circleCell r.context.rate r.outcome
  measurable_event := fun r => measurableSet_circleCell r.context.rate r.outcome
  exclusive := fun c a b t x hxa hxb => by
    by_contra hab
    exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint c.rate c.rate_nonneg hab) hxa hxb

@[simp] theorem circleRecordSemantics_event (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    (circleRecordSemantics n).event ⟨c, i, t⟩ = circleCell c.rate i := rfl

/-- **Isolation is conditioning (P6).** The ontic states compatible with the single record
"context `c` recorded `i` at `t`" are exactly that record's arc. -/
theorem compatibleSet_circle_single (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    compatibleSet (circleRecordSemantics n) [⟨c, i, t⟩] = circleCell c.rate i := by
  simp [compatibleSet]

/-! ### The ontic selection is the record -/

/-- The outcome the unknown microstate selects on the circle: the arc it occupies. -/
noncomputable def circleOutcome (r : Fin n → ℝ) (x : CircleFibre) : Option (Fin n) :=
  open Classical in
  if h : ∃ i, x ∈ circleCell r i then some h.choose else none

/-- **Reading the outcome and testing the record event agree.** For non-negative rates the arcs are
disjoint, so "the microstate occupies arc `i`" and "the record says `i`" are the same statement. -/
theorem circleOutcome_eq_some_iff (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (x : CircleFibre)
    (i : Fin n) : circleOutcome r x = some i ↔ x ∈ circleCell r i := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ j, x ∈ circleCell r j
    · rw [circleOutcome, dif_pos hex] at h
      have : hex.choose = i := by simpa using h
      exact this ▸ hex.choose_spec
    · rw [circleOutcome, dif_neg hex] at h; exact absurd h (by simp)
  · intro hx
    have hex : ∃ j, x ∈ circleCell r j := ⟨i, hx⟩
    rw [circleOutcome, dif_pos hex]
    -- Disjointness forces the chosen index to be `i`.
    by_cases hij : hex.choose = i
    · rw [hij]
    · exact absurd hx (Set.disjoint_left.mp (circleCell_pairwiseDisjoint r hr hij) hex.choose_spec)

/-- Normalized nonnegative rates give exactly one recorded outcome at every
    circle point. This uses interval coverage, not an inference from full support. -/
theorem circleOutcome_total (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (x : CircleFibre) :
    ∃! i, circleOutcome r x = some i := by
  have hx : x ∈ ⋃ i, circleCell r i := by rw [iUnion_circleCell r hsum]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hout := (circleOutcome_eq_some_iff r hr x i).mpr hi
  refine ⟨i, hout, ?_⟩
  intro j hj
  exact Option.some.inj (hj.symm.trans hout)

/-- **The ontic selection is the record**, at the record-layer level. -/
theorem circleOutcome_eq_record (c : FibreContext n) (i : Fin n) (t : OnticTime)
    (x : CircleFibre) :
    circleOutcome c.rate x = some i ↔ x ∈ (circleRecordSemantics n).event ⟨c, i, t⟩ := by
  rw [circleRecordSemantics_event]
  exact circleOutcome_eq_some_iff c.rate c.rate_nonneg x i

/-! ### Measurement on the compact fibre -/

/-- A **measurement** on the compact fibre: a context awaiting an unknown microstate. -/
structure CircleMeasurement (n : ℕ) where
  /-- The measurement context — fixes the arcs, hence the probabilities. -/
  context : FibreContext n
  /-- The ontic time at which the record is established. -/
  time : OnticTime

namespace CircleMeasurement

variable (m : CircleMeasurement n)

/-- The **basin** of outcome `i`: the arc the context assigns to it. -/
def basin (i : Fin n) : Set CircleFibre :=
  (circleRecordSemantics n).event ⟨m.context, i, m.time⟩

/-- The **probability** of outcome `i`: the Haar measure of its basin. -/
noncomputable def prob (i : Fin n) : ENNReal := volume (m.basin i)

theorem basin_eq (i : Fin n) : m.basin i = circleCell m.context.rate i := rfl

end CircleMeasurement

/-- The **Born measurement** on the compact fibre for a prepared state `ψ`. -/
noncomputable def circleBornMeasurement (ψ : EuclideanSpace ℂ (Fin n)) (t : OnticTime) :
    CircleMeasurement n :=
  ⟨bornContext ψ, t⟩

/-- **★ The Born rule on the compact fibre.** The outcome-`i` probability of the Born measurement is
`‖ψ i‖²` — the same weight the `ℝ` fibre gave. Compactifying changed nothing. -/
theorem circleBornMeasurement_prob (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n)
    (t : OnticTime) :
    (circleBornMeasurement ψ t).prob i = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  have hrate : (circleBornMeasurement ψ t).context.rate = bornRate ψ := rfl
  rw [CircleMeasurement.prob, CircleMeasurement.basin_eq, hrate]
  exact volume_circleBornCell ψ hψ i

/-- Unit-state Born basins cover every circle point, including the seam and
    cell boundaries. Zero-weight cells may be empty; they do not create gaps. -/
theorem circleBornMeasurement_cover (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1)
    (t : OnticTime) : (⋃ i, (circleBornMeasurement ψ t).basin i) = univ :=
  iUnion_circleCell (bornRate ψ) (sum_bornRate_unit ψ hψ)

/-- The uncovered set has measure zero because it is empty. Exact coverage
    follows from normalized cumulative arcs, not merely from Haar full support.
    The real-line probability construction instead uses restricted Lebesgue
    measure; its totality statement is relative to that preparation law. -/
theorem circleBornMeasurement_ae_total (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1)
    (t : OnticTime) :
    volume (univ \ ⋃ i, (circleBornMeasurement ψ t).basin i) = 0 := by
  rw [circleBornMeasurement_cover ψ hψ t, Set.sdiff_self, measure_empty]

end CSD.RecordLayer
