/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusFibre
public import CsdLean4.RecordLayer.Measurement

/-!
# SigmaLayer/TorusRecord: the record layer on the even-dimensional fibre

**Category:** 7-SigmaLayer (the record layer, A1 compactness *and parity*).

`CircleFibre`/`CircleRecord` moved the Born partition and then the record
layer onto a **compact** fibre, which fixed the non-compactness of the
original `ℝ` fibre. It did not fix parity: a single circle is
one-dimensional, so `ℂℙ^{N-1} × S¹` has odd real dimension and cannot
carry a symplectic or Kähler structure at all. `TorusFibre` responded by
putting the Born cells on `T² = S¹ × S¹`, constraining the first angle and
leaving the second free, so that the total space `KSigma = ℂℙ^{N-1} × T²`
is compact, **even-dimensional**, and a product of Kähler manifolds.

This file moves the rest of the record layer across, so that the active
fibre and the A1-admissible arena are finally the same object:

* `torusRecordSemantics` — a postulate-P5 `RecordSemantics` on `KTorus`.
  The signature is `fibreSignature`, reused unchanged: it only ever
  mentioned rate vectors and outcome indices, never the fibre.
* `compatibleSet_torus_single` — isolation is conditioning (P6).
* `torusOutcome_eq_record` — the ontic selection *is* the record: reading
  which cell the microstate occupies and testing the record event are the
  same statement.
* `TorusMeasurement` / `prob` / `torusBornMeasurement` — measurement as
  context plus unknown microstate.
* ★ `torusBornMeasurement_prob` — the Born weight is `‖ψ i‖²`, the same
  number the `ℝ` and `S¹` fibres gave. Moving to the even-dimensional
  fibre changes no probability.
* `torusBornMeasurement_ae_total` — the cells cover `T²` up to a null set.

## Scope

What this delivers is an **active** record fibre on a compact,
even-dimensional arena: the outcome is read off the fibre coordinate
rather than pulled back from the base, and the arena's dimension no longer
forbids the structure Paper C A1 asks for. It does **not** construct a
Kähler form on that arena, and does not prove the fibre measure is a
Liouville volume for one: Mathlib has no manifold differential-forms API,
which is the standing KG-1 block. Parity is a necessary condition that was
previously violated and now is not; it is not sufficiency, and no A1
discharge is claimed here.

## References

`SigmaLayer/TorusFibre.lean` (the cells and the parity argument);
`SigmaLayer/CircleRecord.lean` (the compact-fibre record layer this
ports); `SigmaLayer/Measurement.lean` (P5/P6, `bornContext`);
`specs/BACKLOG.md` (the A1 sector row); `MATHLIB-GAPS.md` (KG-1).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ}

/-! ### The P5 record semantics on the even-dimensional fibre -/

/-- **The torus record semantics (P5).** The ontic event of "context `c`
recorded outcome `i`" is the Born cell `torusCell c.rate i`: measurable,
and within one context at one time distinct outcomes are mutually
exclusive. -/
noncomputable def torusRecordSemantics (n : ℕ) :
    RecordSemantics LF4.KTorus (fibreSignature n) where
  event := fun r => torusCell r.context.rate r.outcome
  measurable_event := fun r => measurableSet_torusCell r.context.rate r.outcome
  exclusive := fun c a b t x hxa hxb => by
    by_contra hab
    exact Set.disjoint_left.mp
      (torusCell_pairwiseDisjoint c.rate c.rate_nonneg hab) hxa hxb

@[simp] theorem torusRecordSemantics_event (c : FibreContext n) (i : Fin n)
    (t : OnticTime) :
    (torusRecordSemantics n).event ⟨c, i, t⟩ = torusCell c.rate i := rfl

/-- **Isolation is conditioning (P6).** The ontic states compatible with
the single record "context `c` recorded `i` at `t`" are exactly that
record's cell. -/
theorem compatibleSet_torus_single (c : FibreContext n) (i : Fin n)
    (t : OnticTime) :
    compatibleSet (torusRecordSemantics n) [⟨c, i, t⟩] = torusCell c.rate i := by
  simp [compatibleSet]

/-! ### The ontic selection is the record -/

/-- The outcome the unknown microstate selects: the cell it occupies. -/
noncomputable def torusOutcome (r : Fin n → ℝ) (x : LF4.KTorus) :
    Option (Fin n) :=
  open Classical in
  if h : ∃ i, x ∈ torusCell r i then some h.choose else none

/-- **Reading the outcome and testing the record event agree.** For
non-negative rates the cells are disjoint, so "the microstate occupies
cell `i`" and "the record says `i`" are the same statement. -/
theorem torusOutcome_eq_some_iff (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (x : LF4.KTorus) (i : Fin n) :
    torusOutcome r x = some i ↔ x ∈ torusCell r i := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ j, x ∈ torusCell r j
    · rw [torusOutcome, dif_pos hex] at h
      have : hex.choose = i := by simpa using h
      exact this ▸ hex.choose_spec
    · rw [torusOutcome, dif_neg hex] at h; exact absurd h (by simp)
  · intro hx
    have hex : ∃ j, x ∈ torusCell r j := ⟨i, hx⟩
    rw [torusOutcome, dif_pos hex]
    by_cases hij : hex.choose = i
    · rw [hij]
    · exact absurd hx (Set.disjoint_left.mp
        (torusCell_pairwiseDisjoint r hr hij) hex.choose_spec)

/-- **The ontic selection is the record**, at the record-layer level. -/
theorem torusOutcome_eq_record (c : FibreContext n) (i : Fin n)
    (t : OnticTime) (x : LF4.KTorus) :
    torusOutcome c.rate x = some i
      ↔ x ∈ (torusRecordSemantics n).event ⟨c, i, t⟩ := by
  rw [torusRecordSemantics_event]
  exact torusOutcome_eq_some_iff c.rate c.rate_nonneg x i

/-! ### Measurement on the even-dimensional fibre -/

/-- A **measurement**: a context awaiting an unknown microstate. -/
structure TorusMeasurement (n : ℕ) where
  /-- The measurement context, which fixes the cells and the weights. -/
  context : FibreContext n
  /-- The ontic time at which the record is established. -/
  time : OnticTime

namespace TorusMeasurement

variable (m : TorusMeasurement n)

/-- The **basin** of outcome `i`: the cell the context assigns to it. -/
def basin (i : Fin n) : Set LF4.KTorus :=
  (torusRecordSemantics n).event ⟨m.context, i, m.time⟩

/-- The **probability** of outcome `i`: the Haar measure of its basin. -/
noncomputable def prob (i : Fin n) : ENNReal := volume (m.basin i)

theorem basin_eq (i : Fin n) : m.basin i = torusCell m.context.rate i := rfl

end TorusMeasurement

/-- The **Born measurement** on the even-dimensional fibre. -/
noncomputable def torusBornMeasurement (ψ : EuclideanSpace ℂ (Fin n))
    (t : OnticTime) : TorusMeasurement n :=
  ⟨bornContext ψ, t⟩

/-- ★ **The Born rule on the even-dimensional fibre.** The outcome-`i`
probability is `‖ψ i‖²`, the same weight the `ℝ` and `S¹` fibres gave:
fixing the parity defect costs no probability. -/
theorem torusBornMeasurement_prob (ψ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (i : Fin n) (t : OnticTime) :
    (torusBornMeasurement ψ t).prob i = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  have hrate : (torusBornMeasurement ψ t).context.rate = bornRate ψ := rfl
  rw [TorusMeasurement.prob, TorusMeasurement.basin_eq, hrate]
  exact volume_torusBornCell ψ hψ i

/-- **A.e. every microstate yields a record.** The cells cover `T²` up to
a null set, so there is no positive-measure "no outcome" region. -/
theorem torusBornMeasurement_ae_total (ψ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (t : OnticTime) :
    volume (univ \ ⋃ i, (torusBornMeasurement ψ t).basin i) = 0 := by
  classical
  have hrate : (torusBornMeasurement ψ t).context.rate = bornRate ψ := rfl
  have hcell : ∀ i, (torusBornMeasurement ψ t).basin i
      = torusCell (bornRate ψ) i := by
    intro i
    rw [TorusMeasurement.basin_eq, hrate]
  have hset : (⋃ i, (torusBornMeasurement ψ t).basin i)
      = ⋃ i, torusCell (bornRate ψ) i := by
    exact Set.iUnion_congr hcell
  rw [hset]
  exact torusBornCell_ae_total ψ hψ

end CSD.RecordLayer
