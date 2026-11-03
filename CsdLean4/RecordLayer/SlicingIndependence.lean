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
* `LocalOp`, `applyOp`, `applyOps` (a history: a list of local operations, latest first), `wingA`,
  `wingB`
  (each wing's own sequence, multiplied in order);
* ★★★ `applyOps_eq` (**any interleaving acts as `actA (wingA) ∘ actB (wingB)`**: the final branch
  vector depends only on each wing's local sequence);
* ★★★ `slicing_independent` (**two interleavings with the same local sequences give the same branch
  vector, hence the same joint record weights** — the ontic order of spacelike writes is invisible
  in the joint law);
* ★★ `joint_weight_order_indep` (the two-record case: `A` writes then `B`, or `B` then `A`, with
  any local evolutions before each write, give the same joint weight).

## The two-record law of isolated QM

This section is a statement about **quantum statistics** — the Born rule of the isolated composite
system — not about Σ's records, which are definite facts of the one trajectory (their ontic-order
independence is `CV/SigmaSlicing.lean`). The Born rule is taken as the corpus has it, not rebuilt.

* `swapV`, `norm_swapV`, `swapV_actB`, `norm_actB` (the `B`-side read off the `A`-side by swapping
  the factors), `sum_norm_sq_actA_single`, `sum_norm_sq_actB_single` (the basis projectors resolve
  the norm on each wing);
* `twoRecordLaw` (**the joint law of `A`'s record `i` and `B`'s record `j`** after local evolutions
  `U`, `W` — every local projective measurement is a basis measurement after a local unitary);
* ★★★ `twoRecordLaw_props` (**slicing independent** — `B` written first gives the same law;
  **normalised** — the weights sum to `1`; **no-signalling** — `A`'s marginal is its own Born weight
  `‖P_i U v‖²`, whatever `B`'s evolution and setting and whichever record the ontic time writes
  first).

## Honest scope

⚠️ **QM statistics, not Σ records**: `twoRecordLaw` is the Born law of the isolated composite;
Σ records and their ontic-order independence are `CV/SigmaSlicing.lean`. No measurement protocol is
rebuilt here.

⚠️ **Spacelike as tensor locality**: no coupling across the cut during the writes. On the Dirac
chain wings interact through the Hamiltonian; there spacelike separation gives only approximate
locality (the light-cone and Lieb–Robinson bounds, #246), and slicing independence would hold to
that bound's error.

References: `specs/BACKLOG.md` #285, #39, Q27, #246; `RecordLayer/OnticMarginals.lean` (`actA`,
`actA_actA`, `actA_one`); `RecordLayer/LocalLuders.lean` (`localProjB`);
`RecordLayer/CompositeRecord.lean` (`composite_local_record_born`);
`CV/CompositeArena.lean` (`composite_no_signalling`); `CV/SigmaSlicing.lean`
(`sigma_record_write_order_indep`, `sigma_record_kick_order`).
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

/-! ### The two-record law, with the Born weights given -/

/-- The factor swap on composite vectors: `(swapV v)(k, j) = v(j, k)`. -/
noncomputable def swapV (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    EuclideanSpace ℂ (Fin nB × Fin nA) :=
  WithLp.toLp 2 fun kj => v (kj.2, kj.1)

theorem norm_swapV (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : ‖swapV v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm (Fin nB) (Fin nA)) _ _ fun kj => rfl

/-- The local `B`-action is the local `A`-action with the factors swapped. -/
theorem swapV_actB (W : Matrix (Fin nB) (Fin nB) ℂ) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    swapV (actB W v) = actA W (swapV v) := rfl

theorem norm_actB {W : Matrix (Fin nB) (Fin nB) ℂ} (hW : W ∈ Matrix.unitaryGroup (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : ‖actB W v‖ = ‖v‖ := by
  rw [← norm_swapV, swapV_actB, norm_actA hW, norm_swapV]

/-- **The computational-basis projectors resolve the norm on wing `A`.** -/
theorem sum_norm_sq_actA_single (w : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ i, ‖actA (Matrix.single i i (1 : ℂ)) w‖ ^ 2 = ‖w‖ ^ 2 := by
  have hpt : ∀ i (a : Fin nA) (k : Fin nB),
      actA (Matrix.single i i (1 : ℂ)) w (a, k) = if a = i then w (i, k) else 0 := by
    intro i a k
    rw [actA_apply, Finset.sum_eq_single i]
    · by_cases h : a = i
      · subst h; simp
      · simp only [Matrix.single_apply]
        simp [Ne.symm h, h]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- **The computational-basis projectors resolve the norm on wing `B`.** -/
theorem sum_norm_sq_actB_single (w : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, ‖actB (Matrix.single j j (1 : ℂ)) w‖ ^ 2 = ‖w‖ ^ 2 := by
  simp only [← norm_swapV (actB _ w), swapV_actB]
  rw [sum_norm_sq_actA_single, norm_swapV]

/-- **The two-record law**: wing `A` evolves by `U` and records `i` in its computational basis,
wing `B` evolves by `W` and records `j` — the joint record weight, as the corpus gives it, is the
Born weight of the branch (`composite_local_record_born` for one wing; the Lüders branch for two).
Any local projective measurement is a basis measurement after a local unitary, so `U`, `W` range
over all of them. -/
noncomputable def twoRecordLaw (U : Matrix (Fin nA) (Fin nA) ℂ) (W : Matrix (Fin nB) (Fin nB) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (i : Fin nA) (j : Fin nB) : ℝ :=
  ‖actB (Matrix.single j j 1) (actB W (actA (Matrix.single i i 1) (actA U v)))‖ ^ 2

/-- ★★★ **The two-record law at the record tier: slicing independent, normalised, and
no-signalling.** For unitary local evolutions `U`, `W` and a unit preparation `v`:
* **either ontic order** — `B` written first gives the same law;
* **a probability law** — the weights sum to `1`;
* **each wing's marginal is its own Born weight** — summing over `B`'s records leaves `A`'s weight
  `‖P_i U v‖²`, whatever `B`'s evolution and setting `W`, and whichever record the ontic time
  writes first. -/
theorem twoRecordLaw_props {U : Matrix (Fin nA) (Fin nA) ℂ} {W : Matrix (Fin nB) (Fin nB) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin nB) ℂ)
    {v : EuclideanSpace ℂ (Fin nA × Fin nB)} (hv : ‖v‖ = 1) :
    (∀ i j, twoRecordLaw U W v i j
      = ‖actA (Matrix.single i i 1) (actA U (actB (Matrix.single j j 1) (actB W v)))‖ ^ 2)
    ∧ ∑ i, ∑ j, twoRecordLaw U W v i j = 1
    ∧ (∀ i, ∑ j, twoRecordLaw U W v i j = ‖actA (Matrix.single i i 1) (actA U v)‖ ^ 2) := by
  have hmarg : ∀ i, ∑ j, twoRecordLaw U W v i j = ‖actA (Matrix.single i i 1) (actA U v)‖ ^ 2 :=
    fun i => by
      simp only [twoRecordLaw]
      rw [sum_norm_sq_actB_single, norm_actB hW]
  refine ⟨fun i j => joint_weight_order_indep U _ W _ v, ?_, hmarg⟩
  simp only [hmarg]
  rw [sum_norm_sq_actA_single, norm_actA hU, hv, one_pow]

end CSD.RecordLayer
