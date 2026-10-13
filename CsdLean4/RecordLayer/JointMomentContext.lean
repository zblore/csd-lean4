/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SkewBasin
public import CsdLean4.RecordLayer.OutcomeField

/-!
# The joint moment context: an I3 rate field that comes from the base

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #136, the open half of it.

[`SkewBasin.lean`](SkewBasin.lean) built the skew-cell record layer (I3) over an arbitrary
`JointContextField`, and exhibited exactly one: `constJointContext`, whose table does not move with
the ontic point. I1 has `momentContext`, whose rates *are* the Born weights of the base point, so
the I1/I3 comparison was not like for like. This file supplies I3's analogue, and the comparison
becomes a theorem rather than a remark.

* `jointMomentContext b` — the joint field of a **degeneracy map** `b : Fin N → Fin m × Fin n`:
  the joint rate of the outcome pair `(s, t)` is the moment map summed over the directions `b`
  sends to that pair. Every field condition comes from the moment map's, as it does for
  `blockField`;
* ★★★ `jointMomentContext_rowSum` — **A's marginal is `blockField`'s rate at A's coarsening.**
  This is the parity statement: the wing-A reading of I3 at this field *is* the I1 reading at the
  same coarse-graining, not merely analogous to it. ★★ `jointMomentContext_colSum` is B's half;
* ★★★ `skewBasin_prob_jointMomentContext` — so the skew basins carry the block-coarsened Born
  weights, which is what makes the field a record layer rather than a table;
* ★ `jointMomentContext_rowSum_single` — the nondegenerate recovery: at `n = 1` with `b j = (j, 0)`
  A's marginal is `momentContext`'s rate, so I1 is the degenerate case of this field and not a
  separate construction.

## What was reused rather than rebuilt

`blockField` ([`OutcomeField.lean`](OutcomeField.lean)) is the **single-index** version of this
construction and already existed: the same finite sum of moment coordinates, with the same three
obligations discharged the same way. It cannot be instantiated here, because `OutcomeField N K`
indexes its outcomes by `Fin K` while a joint table is indexed by a *product*, and bridging that
through `Fin m × Fin n ≃ Fin (m * n)` would make the definition unreadable for no gain. So the
definition is written out and the relationship is proved instead —
`jointMomentContext_rowSum` and `jointMomentContext_colSum` are the two statements that say this is
`blockField` coarsened on each wing, which is the honest substitute for literal reuse.

## Honest scope

⚠️ **The degeneracy map is a posit, as it is for I1.** `b` says which directions of `ℂℙ^{N-1}` the
apparatus cannot tell apart, in both wings at once. Nothing derives it; `POSITS.md` Posit 10 is
where that sits, and this file changes nothing about it.

⚠️ **No correlation is created.** The joint table is whatever the moment map and `b` make it: for a
`b` whose two components are independent of each other on the support, the table factorises. A
*correlated* table at a *moving* base point is this field at a `b` that entangles the two
coordinates, and which `b` the two-wing experiment wants is the question
[`SkewBasin.lean`](SkewBasin.lean)'s `constJointContext` sidestepped by fixing the table by hand.

⚠️ **This is the field, not the comparison.** It puts I3's rates on the same footing as I1's; it
does not re-run I1's theorems at I3, and `POSITS.md`'s decision between the two readings is
unaffected.

References: [`SkewBasin.lean`](SkewBasin.lean) (`JointContextField`, `skewBasin`, `skewBasin_prob`,
`constJointContext`), [`OutcomeField.lean`](OutcomeField.lean) (`blockField`, the single-index
original), [`GlobalBasin.lean`](GlobalBasin.lean) (`momentContext`, I1's field),
[`SkewFibrePartition.lean`](SkewFibrePartition.lean) (`JointRates`, `rowSum`, `colSum`);
`specs/POSITS.md` Posit 10; `specs/BACKLOG.md` #136, #135, #134.
-/

@[expose] public section

open MeasureTheory

namespace CSD.RecordLayer

variable {N m n : ℕ}

/-! ### The field -/

/-- **The joint moment context**: the moment map, coarse-grained by a degeneracy map that assigns
each direction to a pair of wing outcomes. This is `blockField` with a product index, and every
field condition comes from the moment map's in the same way. -/
noncomputable def jointMomentContext (b : Fin N → Fin m × Fin n) :
    JointContextField N m n where
  rate p s t := ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j
  measurable_rate s t := by
    classical
    exact Finset.measurable_sum _ fun j _ => LF4.measurable_momentMap j
  nonneg p s t := Finset.sum_nonneg fun j _ => LF4.momentMap_nonneg p j
  sum_one p := by
    classical
    rw [← LF4.momentMap_sum_eq_one p, ← Fintype.sum_prod_type']
    simp only [Prod.mk.eta]
    exact Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (b j)) _

@[simp] theorem jointMomentContext_rate (b : Fin N → Fin m × Fin n) (p : LF4.CPN N)
    (s : Fin m) (t : Fin n) :
    (jointMomentContext (N := N) b).rate p s t
      = ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j := rfl

/-! ### Parity with I1: the marginals are `blockField` -/

/-- ★★★ **A's marginal is `blockField`'s rate at A's coarsening.**

This is the statement #136 wanted: wing A's reading under I3 at this field *is* the I1 reading at
the coarse-graining `b` induces on A, so the two layers are comparable at the level of rates rather
than by analogy. The proof is one regrouping: the fibres of `b` over `(s, ·)` partition the fibre of
`(b ·).1` over `s`. -/
theorem jointMomentContext_rowSum (b : Fin N → Fin m × Fin n) (p : LF4.CPN N) (s : Fin m) :
    ((jointMomentContext (N := N) b).rates p).rowSum s
      = (blockField (fun j => (b j).1)).rate p s := by
  classical
  have hfil : ∀ t : Fin n, Finset.univ.filter (fun j => b j = (s, t))
      = (Finset.univ.filter (fun j => (b j).1 = s)).filter (fun j => (b j).2 = t) := by
    intro t
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  show ∑ t, ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j
      = ∑ j ∈ Finset.univ.filter (fun j => (b j).1 = s), LF4.momentMap p j
  calc ∑ t, ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j
      = ∑ t : Fin n, ∑ j ∈ (Finset.univ.filter (fun j => (b j).1 = s)).filter
          (fun j => (b j).2 = t), LF4.momentMap p j :=
        Finset.sum_congr rfl fun t _ => by rw [hfil t]
    _ = ∑ j ∈ Finset.univ.filter (fun j => (b j).1 = s), LF4.momentMap p j :=
        Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ ((b j).2)) _

/-- ★★ **And B's marginal is `blockField`'s rate at B's coarsening.** -/
theorem jointMomentContext_colSum (b : Fin N → Fin m × Fin n) (p : LF4.CPN N) (t : Fin n) :
    ((jointMomentContext (N := N) b).rates p).colSum t
      = (blockField (fun j => (b j).2)).rate p t := by
  classical
  have hfil : ∀ s : Fin m, Finset.univ.filter (fun j => b j = (s, t))
      = (Finset.univ.filter (fun j => (b j).2 = t)).filter (fun j => (b j).1 = s) := by
    intro s
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    tauto
  show ∑ s, ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j
      = ∑ j ∈ Finset.univ.filter (fun j => (b j).2 = t), LF4.momentMap p j
  calc ∑ s, ∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j
      = ∑ s : Fin m, ∑ j ∈ (Finset.univ.filter (fun j => (b j).2 = t)).filter
          (fun j => (b j).1 = s), LF4.momentMap p j :=
        Finset.sum_congr rfl fun s _ => by rw [hfil s]
    _ = ∑ j ∈ Finset.univ.filter (fun j => (b j).2 = t), LF4.momentMap p j :=
        Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ ((b j).1)) _

/-! ### The record layer at this field -/

/-- ★★★ **The skew basins carry the block-coarsened Born weights.** `skewBasin_prob` is generic in
the field, so this is immediate once the field exists — which is the point of building the field
rather than a table: the record layer was already waiting for it. -/
theorem skewBasin_prob_jointMomentContext (b : Fin N → Fin m × Fin n) (s : Fin m) (t : Fin n)
    (p : LF4.CPN N) :
    epistemicMeasure p (skewBasin (jointMomentContext (N := N) b) s t)
      = ENNReal.ofReal (∑ j ∈ Finset.univ.filter (fun j => b j = (s, t)), LF4.momentMap p j) :=
  skewBasin_prob _ s t p

/-- ★ **I1 is the degenerate case, not a separate construction.** At one B-outcome and the identity
degeneracy on A, wing A's marginal is `momentContext`'s rate — the same recovery `blockField_id`
records for the single-index field. -/
theorem jointMomentContext_rowSum_single (p : LF4.CPN N) (s : Fin N) :
    ((jointMomentContext (N := N) (m := N) (n := 1) (fun j => (j, 0))).rates p).rowSum s
      = (momentContext N).rate p s := by
  rw [jointMomentContext_rowSum]
  exact blockField_id p s

end CSD.RecordLayer

end
