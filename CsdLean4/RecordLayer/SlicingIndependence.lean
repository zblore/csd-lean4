/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OnticMarginals

/-!
# Slicing independence of spacelike records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #285, part (ii).

#285 asks whether the ontic time's frame is hidden from records. Part (ii): for two records
written at spacelike separation, the joint record law should not depend on which one the ontic
time writes first. On a composite `ℂ^{nA} ⊗ ℂ^{nB}`, "spacelike" is taken as *local*: between the
writes each wing evolves by its own operators, with no coupling across the cut. Each wing's
history is a sequence of local operators — its evolution, its record write (a projector or any
Kraus operator) — and the ontic time interleaves the two sequences in some order.

## Main results

* `actB` (the local `B`-action, `1 ⊗ W`, in coordinates beside `OnticMarginals`' `actA`),
  `actB_apply`, `actB_actB`, `actB_one`;
* ★★ `actA_actB_comm` (**local actions on different factors commute**);
* `LocalOp`, `applyOp`, `applyOps` (a history: a list of local operations, latest first), `wingA`, `wingB`
  (each wing's own sequence, multiplied in order);
* ★★★ `applyOps_eq` (**any interleaving acts as `actA (wingA) ∘ actB (wingB)`**: the final branch
  vector depends only on each wing's local sequence);
* ★★★ `slicing_independent` (**two interleavings with the same local sequences give the same branch
  vector, hence the same joint record weights** — the ontic order of spacelike writes is invisible
  in the joint law);
* ★★ `joint_weight_order_indep` (the two-record case: `A` writes then `B`, or `B` then `A`, with
  any local evolutions before each write, give the same joint weight).

## Honest scope

⚠️ **Branch weights, not yet the ontic record tier**: the joint law here is the Born weight of the
branch `‖K_B ⋯ K_A ⋯ v‖²` (Lüders/Kraus form). The record tier reads single local records as
reduced Born weights (`composite_local_record_born`); a two-wing record arena with two record
writes and a re-slicing map, delivering this law dynamically, is the instance still owed.

⚠️ **Spacelike as tensor locality**: no coupling across the cut during the writes. On the Dirac
chain wings interact through the Hamiltonian; there spacelike separation gives only approximate
locality (the light-cone and Lieb–Robinson bounds, #246), and slicing independence would hold to
that bound's error.

References: `specs/BACKLOG.md` #285, #39, Q27, #246; `RecordLayer/OnticMarginals.lean` (`actA`,
`actA_actA`, `actA_one`); `RecordLayer/LocalLuders.lean` (`localProjB`);
`RecordLayer/CompositeRecord.lean` (`composite_local_record_born`);
`CV/CompositeArena.lean` (`composite_no_signalling`).
-/

@[expose] public section

open Matrix

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-- **The local `B`-action on composite vectors**: `(actB W v)(j,k) = ∑_b W k b · v(j,b)`, the
vector form of `1 ⊗ W`. -/
noncomputable def actB (W : Matrix (Fin nB) (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun jk => ∑ b, W jk.2 b * v (jk.1, b)

@[simp] theorem actB_apply (W : Matrix (Fin nB) (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (j : Fin nA) (k : Fin nB) :
    actB W v (j, k) = ∑ b, W k b * v (j, b) := rfl

theorem actB_actB (W V : Matrix (Fin nB) (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    actB W (actB V v) = actB (W * V) v := by
  apply PiLp.ext
  intro jk
  show ∑ b, W jk.2 b * (∑ c, V b c * v (jk.1, c)) = ∑ c, (W * V) jk.2 c * v (jk.1, c)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem actB_one (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : actB 1 v = v := by
  apply PiLp.ext
  intro jk
  show ∑ b, (1 : Matrix (Fin nB) (Fin nB) ℂ) jk.2 b * v (jk.1, b) = v jk
  rw [Finset.sum_eq_single jk.2]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- ★★ **Local actions on different factors commute.** -/
theorem actA_actB_comm (U : Matrix (Fin nA) (Fin nA) ℂ) (W : Matrix (Fin nB) (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    actA U (actB W v) = actB W (actA U v) := by
  apply PiLp.ext
  intro jk
  show ∑ a, U jk.1 a * (∑ b, W jk.2 b * v (a, b)) = ∑ b, W jk.2 b * (∑ a, U jk.1 a * v (a, b))
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- A local operation: on wing `A` (left) or on wing `B` (right). -/
abbrev LocalOp (nA nB : ℕ) := Matrix (Fin nA) (Fin nA) ℂ ⊕ Matrix (Fin nB) (Fin nB) ℂ

/-- One local operation acting on a composite vector. -/
noncomputable def applyOp : LocalOp nA nB → EuclideanSpace ℂ (Fin nA × Fin nB)
    → EuclideanSpace ℂ (Fin nA × Fin nB)
  | Sum.inl U => actA U
  | Sum.inr W => actB W

/-- **A history**: a list of local operations, the latest first, acting on the preparation. -/
noncomputable def applyOps : List (LocalOp nA nB) → EuclideanSpace ℂ (Fin nA × Fin nB)
    → EuclideanSpace ℂ (Fin nA × Fin nB)
  | [], v => v
  | o :: os, v => applyOp o (applyOps os v)

/-- **Wing `A`'s own sequence**, multiplied in order (latest on the left). -/
noncomputable def wingA (os : List (LocalOp nA nB)) : Matrix (Fin nA) (Fin nA) ℂ :=
  (os.filterMap Sum.getLeft?).prod

/-- **Wing `B`'s own sequence**, multiplied in order (latest on the left). -/
noncomputable def wingB (os : List (LocalOp nA nB)) : Matrix (Fin nB) (Fin nB) ℂ :=
  (os.filterMap Sum.getRight?).prod

/-- ★★★ **Any interleaving acts as the two wings' sequences, one after the other.** -/
theorem applyOps_eq (os : List (LocalOp nA nB)) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    applyOps os v = actA (wingA os) (actB (wingB os) v) := by
  induction os with
  | nil => simp [applyOps, wingA, wingB, actA_one, actB_one]
  | cons o os ih =>
    cases o with
    | inl U =>
      simp only [applyOps, applyOp, ih, wingA, wingB, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, List.prod_cons]
      rw [actA_actA]
    | inr W =>
      simp only [applyOps, applyOp, ih, wingA, wingB, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, List.prod_cons]
      rw [← actA_actB_comm, actB_actB]

/-- ★★★ **Slicing independence.** Two histories that interleave the same local sequences — wing
`A`'s operations in the same order, wing `B`'s in the same order — give the same branch vector,
hence the same joint record weights: the ontic order of spacelike writes does not appear in the
joint law. -/
theorem slicing_independent {os os' : List (LocalOp nA nB)}
    (hA : os.filterMap Sum.getLeft? = os'.filterMap Sum.getLeft?)
    (hB : os.filterMap Sum.getRight? = os'.filterMap Sum.getRight?)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    applyOps os v = applyOps os' v
    ∧ ‖applyOps os v‖ ^ 2 = ‖applyOps os' v‖ ^ 2 := by
  have h : applyOps os v = applyOps os' v := by
    rw [applyOps_eq, applyOps_eq, wingA, wingA, wingB, wingB, hA, hB]
  exact ⟨h, by rw [h]⟩

/-- ★★ **Two records, either order.** `A` evolves by `U` and writes by `K_A`; `B` evolves by `W`
and writes by `K_B`. Whether the ontic time runs `A`'s evolution and write before `B`'s or after,
the joint weight `‖branch‖²` is the same. -/
theorem joint_weight_order_indep (U KA : Matrix (Fin nA) (Fin nA) ℂ)
    (W KB : Matrix (Fin nB) (Fin nB) ℂ) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ‖actB KB (actB W (actA KA (actA U v)))‖ ^ 2
      = ‖actA KA (actA U (actB KB (actB W v)))‖ ^ 2 := by
  have h := (slicing_independent (nA := nA) (nB := nB)
    (os := [Sum.inr KB, Sum.inr W, Sum.inl KA, Sum.inl U])
    (os' := [Sum.inl KA, Sum.inl U, Sum.inr KB, Sum.inr W])
    (by simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getLeft?_inr, List.filterMap_nil])
    (by simp only [List.filterMap_cons, Sum.getRight?_inl, Sum.getRight?_inr, List.filterMap_nil])
    v).2
  simpa [applyOps, applyOp] using h

end CSD.RecordLayer
