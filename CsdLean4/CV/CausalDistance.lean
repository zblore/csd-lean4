/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.RecordCausalOrder
public import Mathlib.Order.RelSeries

/-!
# The longest causal chain is a Lorentzian distance on record events

**Category:** 3-Local (CV; the event layer of `ST-1`).
BACKLOG #111, the first of the two geometry bricks priced in the records→spacetime answer.

`RecordCausalOrder.lean` gives a partial order on record events
(`isPartialOrder_causalPrecedes`) and #98 gives a cone with a boost symmetry. Neither gives a
**distance**: before this file the event order carried no interval, no chain length and no numerical
separation at all. This file supplies the causal-set one — the **length of the longest chain** — and
proves the two properties that make it Lorentzian rather than metric.

## What is proved

* `strictPrecedes E` — strict causal precedence as a relation chains can run on, with
  `isTrans_strictPrecedes` (transitive because the order is antisymmetric: a strict step cannot
  return);
* `causalDist E e₁ e₂` — **the length of the longest causal chain** from `e₁` to `e₂`, as the
  supremum of `chainLengths`. It is well defined because ★★ `bddAbove_chainLengths`: a chain's
  events are distinct and all lie between `e₁` and `e₂`, so there are at most
  `2 ^ K · (e₂.time + 1 − e₁.time)` of them — ★ `causalDist_le` states that bound, and it is the
  finiteness of the arena doing the work, not an assumption about the order;
* ★★★ `causalDist_add_le` — **the reverse triangle inequality**:
  `causalDist e₁ e₂ + causalDist e₂ e₃ ≤ causalDist e₁ e₃` for `e₁ ⪯ e₂ ⪯ e₃`. This is the
  signature of Lorentzian geometry and the discrete twin paradox: going by way of `e₂` is **never
  longer** than the longest path, so the longest chain is the straight one. A metric satisfies the
  inequality the other way;
* ★★ `causalDist_pos_iff` — **the distance is positive exactly on the strictly causally related
  pairs**, so it vanishes exactly on the spacelike-or-equal ones, and ★ `causalDist_self`,
  ★ `causalDist_eq_zero_of_not_causalPrecedes` for the two ways of vanishing;
* ★ `causalDist_le_of_causalPrecedes_right` — and it is monotone into the causal future, which is the
  reverse triangle inequality with one leg thrown away.

## Honest scope

⚠️ **This is not the metric, and order plus *length* is not order plus *volume*.** The classical route
from a causal order to a Lorentzian metric (Hawking–King–McCarthy and Malament for manifolds, "order
plus number equals geometry" for causal sets) determines the metric only up to a conformal factor from
the order, and fixes the factor from a **volume element**. This corpus has no volume element on the
event order — the measure it has lives on `Σ` and weights events by Born probability, which is not a
spacetime volume. That companion brick is not built here and nothing below pretends it is.

⚠️ **No embedding, and none is available.** That a discrete order with a volume is approximated by a
Lorentzian manifold is a *programme* (sprinkling; the Hauptvermutung is open), not a theorem, so no
statement here says the event order is a spacetime, or that `causalDist` approximates a proper time.

⚠️ **Relative to a coupling graph.** Everything is stated for a fixed `E`, exactly as `ST-1` is: the
causal structure is relative to an assumed interaction graph and is not derived from `Σ`.

⚠️ **No continuum limit, no curvature, no dimension estimator.** The chain length is an integer on a
finite interval; nothing is said about limits of refinements, about dimension, or about any geometric
invariant beyond the two properties listed.

⚠️ **`causalDist` is `0` on unrelated pairs by construction** (`sSup ∅ = 0` in `ℕ`), which is the
usual convention for a Lorentzian distance — spacelike separation has no timelike path, not a negative
one. It means `causalDist` is not a metric and its vanishing does not imply equality; that is
`causalDist_pos_iff`'s content, not a defect.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) §8 and
`ST-1`; [`future-work.md`](../../specs/future-work.md); `RecordCausalOrder.lean`
(`CausalPrecedes`, `isPartialOrder_causalPrecedes`, `EventSpacelike`), `TwoCones.lean` (#98);
L. Bombelli, J. Lee, D. Meyer, R. Sorkin, *Space-time as a causal set*, PRL 59 (1987) 521;
D. Malament, *The class of continuous timelike curves determines the topology of spacetime*,
J. Math. Phys. 18 (1977) 1399; `specs/BACKLOG.md` #111, #98, #39, #38.
-/

@[expose] public section

open MeasureTheory Set

open scoped SetRel

namespace CSD.CV

variable {K : ℕ}

/-! ### Strict causal precedence, as a relation chains run on -/

/-- **Strict causal precedence**: `e₁` is in the causal past of `e₂` and is a different event. The
relation a causal chain steps along. -/
def strictPrecedes (E : Finset (Fin K × Fin K)) :
    SetRel (RecordEvent K) (RecordEvent K) :=
  {q | CausalPrecedes E q.1 q.2 ∧ q.1 ≠ q.2}

theorem mem_strictPrecedes {E : Finset (Fin K × Fin K)} {a b : RecordEvent K} :
    a ~[strictPrecedes E] b ↔ CausalPrecedes E a b ∧ a ≠ b := Iff.rfl

theorem causalPrecedes_of_strictPrecedes {E : Finset (Fin K × Fin K)} {a b : RecordEvent K}
    (h : a ~[strictPrecedes E] b) : CausalPrecedes E a b := h.1

theorem ne_of_strictPrecedes {E : Finset (Fin K × Fin K)} {a b : RecordEvent K}
    (h : a ~[strictPrecedes E] b) : a ≠ b := h.2

/-- ★ **Strict precedence is transitive** — and it is antisymmetry that makes it so: a strict step
cannot return, so the composite is strict as well as causal. -/
theorem isTrans_strictPrecedes (E : Finset (Fin K × Fin K)) : (strictPrecedes E).IsTrans := by
  refine ⟨fun a b c hab hbc => mem_strictPrecedes.2
    ⟨causalPrecedes_trans (causalPrecedes_of_strictPrecedes hab)
      (causalPrecedes_of_strictPrecedes hbc), ?_⟩⟩
  intro hac
  have hba : CausalPrecedes E b a := by
    rw [hac]
    exact causalPrecedes_of_strictPrecedes hbc
  exact ne_of_strictPrecedes hab
    (causalPrecedes_antisymm (causalPrecedes_of_strictPrecedes hab) hba)

/-! ### The chain lengths between two events -/

/-- The lengths of the causal chains from `e₁` to `e₂`. -/
def chainLengths (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : Set ℕ :=
  {n | ∃ p : RelSeries (strictPrecedes E), p.head = e₁ ∧ p.last = e₂ ∧ p.length = n}

/-- ★★ **A chain is bounded by the arena.** Its events are distinct — a strict chain cannot
repeat — and all lie between the endpoints in time, so there are at most
`2 ^ K · (e₂.time + 1 − e₁.time)` of them. The finiteness doing the work is the arena's, not an
assumption about the order. -/
theorem chainLengths_le {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K} {n : ℕ}
    (hn : n ∈ chainLengths E e₁ e₂) : n ≤ 2 ^ K * (e₂.time + 1 - e₁.time) := by
  have hT := isTrans_strictPrecedes E
  obtain ⟨p, hhead, hlast, rfl⟩ := hn
  set B : Finset (Finset (Fin K) × ℕ) :=
    (Finset.univ : Finset (Finset (Fin K))) ×ˢ Finset.Icc e₁.time e₂.time with hB
  -- every event of the chain lies between the endpoints in time
  have hmaps : ∀ i : Fin (p.length + 1), ((p i).region, (p i).time) ∈ B := by
    intro i
    have hlo : CausalPrecedes E e₁ (p i) := by
      rcases p.rel_or_eq_of_le (i := 0) (j := i) (Fin.zero_le i) with h | h
      · have : CausalPrecedes E (p 0) (p i) := causalPrecedes_of_strictPrecedes h
        rwa [show p 0 = e₁ from hhead] at this
      · have : CausalPrecedes E (p 0) (p i) := by rw [h]; exact causalPrecedes_refl E _
        rwa [show p 0 = e₁ from hhead] at this
    have hhi : CausalPrecedes E (p i) e₂ := by
      rcases p.rel_or_eq_of_le (i := i) (j := Fin.last _) (Fin.le_last i) with h | h
      · have : CausalPrecedes E (p i) (p (Fin.last _)) :=
          causalPrecedes_of_strictPrecedes h
        rwa [show p (Fin.last _) = e₂ from hlast] at this
      · have : CausalPrecedes E (p i) (p (Fin.last _)) := by
          rw [← h]; exact causalPrecedes_refl E _
        rwa [show p (Fin.last _) = e₂ from hlast] at this
    exact Finset.mem_product.2 ⟨Finset.mem_univ _,
      Finset.mem_Icc.2 ⟨hlo.1, hhi.1⟩⟩
  -- and they are pairwise distinct
  have hinj : ∀ i ∈ (Finset.univ : Finset (Fin (p.length + 1))), ∀ j ∈
      (Finset.univ : Finset (Fin (p.length + 1))),
      ((p i).region, (p i).time) = ((p j).region, (p j).time) → i = j := by
    intro i _ j _ hij
    have heq : p i = p j := RecordEvent.ext (congrArg Prod.fst hij) (congrArg Prod.snd hij)
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ne_of_strictPrecedes (p.rel_of_lt h) heq
    · exact ne_of_strictPrecedes (p.rel_of_lt h) heq.symm
  have hcard : (Finset.univ : Finset (Fin (p.length + 1))).card ≤ B.card :=
    Finset.card_le_card_of_injOn _ (fun i _ => hmaps i) hinj
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hBcard : B.card = 2 ^ K * (e₂.time + 1 - e₁.time) := by
    rw [hB, Finset.card_product, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
      Nat.card_Icc]
  calc p.length ≤ p.length + 1 := Nat.le_succ _
    _ ≤ B.card := hcard
    _ = 2 ^ K * (e₂.time + 1 - e₁.time) := hBcard

theorem bddAbove_chainLengths (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    BddAbove (chainLengths E e₁ e₂) :=
  ⟨2 ^ K * (e₂.time + 1 - e₁.time), fun _ hn => chainLengths_le hn⟩

/-! ### The distance -/

/-- **The Lorentzian distance on record events**: the length of the longest causal chain from `e₁`
to `e₂`, and `0` when there is none. -/
noncomputable def causalDist (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : ℕ :=
  sSup (chainLengths E e₁ e₂)

/-- ★ **The distance is bounded by the arena**, explicitly. -/
theorem causalDist_le (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    causalDist E e₁ e₂ ≤ 2 ^ K * (e₂.time + 1 - e₁.time) := by
  rcases Set.eq_empty_or_nonempty (chainLengths E e₁ e₂) with h | h
  · rw [causalDist, h]
    simp
  · exact csSup_le h fun _ hn => chainLengths_le hn

theorem zero_mem_chainLengths (E : Finset (Fin K × Fin K)) (e : RecordEvent K) :
    0 ∈ chainLengths E e e :=
  ⟨RelSeries.singleton _ e, RelSeries.head_singleton e, RelSeries.last_singleton e, rfl⟩

theorem one_mem_chainLengths {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : e₁ ~[strictPrecedes E] e₂) : 1 ∈ chainLengths E e₁ e₂ := by
  refine ⟨(RelSeries.singleton (strictPrecedes E) e₂).cons e₁ ?_, ?_, ?_, ?_⟩
  · rw [RelSeries.head_singleton]
    exact h
  · exact RelSeries.head_cons _ _ _
  · rw [RelSeries.last_cons, RelSeries.last_singleton]
  · simp

theorem nonempty_chainLengths_of_causalPrecedes {E : Finset (Fin K × Fin K)}
    {e₁ e₂ : RecordEvent K} (h : CausalPrecedes E e₁ e₂) :
    (chainLengths E e₁ e₂).Nonempty := by
  by_cases hne : e₁ = e₂
  · subst hne
    exact ⟨0, zero_mem_chainLengths E e₁⟩
  · exact ⟨1, one_mem_chainLengths ⟨h, hne⟩⟩

/-- The longest chain is attained: the supremum is itself a chain length. -/
theorem causalDist_mem_chainLengths {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : CausalPrecedes E e₁ e₂) : causalDist E e₁ e₂ ∈ chainLengths E e₁ e₂ :=
  Nat.sSup_mem (nonempty_chainLengths_of_causalPrecedes h) (bddAbove_chainLengths E e₁ e₂)

/-! ### It vanishes exactly on the spacelike-or-equal pairs -/

theorem causalDist_eq_zero_of_not_causalPrecedes {E : Finset (Fin K × Fin K)}
    {e₁ e₂ : RecordEvent K} (h : ¬ CausalPrecedes E e₁ e₂) : causalDist E e₁ e₂ = 0 := by
  have hempty : chainLengths E e₁ e₂ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun n hn => ?_
    obtain ⟨p, hhead, hlast, _⟩ := hn
    have hT := isTrans_strictPrecedes E
    have hpre : CausalPrecedes E (p 0) (p (Fin.last _)) := by
      rcases p.rel_or_eq_of_le (i := 0) (j := Fin.last _) (Fin.zero_le _) with hr | hr
      · exact causalPrecedes_of_strictPrecedes hr
      · rw [hr]
        exact causalPrecedes_refl E _
    rw [show p 0 = e₁ from hhead, show p (Fin.last _) = e₂ from hlast] at hpre
    exact h hpre
  rw [causalDist, hempty]
  simp

/-- ★ **A record is at no distance from itself.** -/
theorem causalDist_self (E : Finset (Fin K × Fin K)) (e : RecordEvent K) :
    causalDist E e e = 0 := by
  refine le_antisymm (csSup_le ⟨0, zero_mem_chainLengths E e⟩ fun n hn => ?_) (Nat.zero_le _)
  obtain ⟨p, hhead, hlast, rfl⟩ := hn
  by_contra hpos
  have hT := isTrans_strictPrecedes E
  have hlen : 0 < p.length := by omega
  have hlt : (0 : Fin (p.length + 1)) < Fin.last _ := by
    refine Fin.lt_def.2 ?_
    simpa using hlen
  refine ne_of_strictPrecedes (p.rel_of_lt hlt) ?_
  rw [show p 0 = e from hhead, show p (Fin.last _) = e from hlast]

/-- ★★ **The distance is positive exactly on the strictly causally related pairs** — so it vanishes
exactly on the pairs that are spacelike or equal, which is what a Lorentzian distance does. -/
theorem causalDist_pos_iff {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K} :
    0 < causalDist E e₁ e₂ ↔ CausalPrecedes E e₁ e₂ ∧ e₁ ≠ e₂ := by
  refine ⟨fun hpos => ?_, fun h => ?_⟩
  · by_cases hc : CausalPrecedes E e₁ e₂
    · refine ⟨hc, ?_⟩
      rintro rfl
      rw [causalDist_self] at hpos
      exact absurd hpos (lt_irrefl 0)
    · rw [causalDist_eq_zero_of_not_causalPrecedes hc] at hpos
      exact absurd hpos (lt_irrefl 0)
  · exact lt_of_lt_of_le Nat.zero_lt_one
      (le_csSup (bddAbove_chainLengths E e₁ e₂) (one_mem_chainLengths h))

/-! ### The reverse triangle inequality -/

/-- ★★★ **The reverse triangle inequality** — the signature of Lorentzian geometry, and the discrete
twin paradox: a path through `e₂` is never longer than the longest path, so the longest chain is the
*straight* one. A metric satisfies the inequality the other way round.

The proof is chain concatenation: the longest chains to and from `e₂` are attained
(`causalDist_mem_chainLengths`), and smashing them gives a chain of the summed length. -/
theorem causalDist_add_le {E : Finset (Fin K × Fin K)} {e₁ e₂ e₃ : RecordEvent K}
    (h₁ : CausalPrecedes E e₁ e₂) (h₂ : CausalPrecedes E e₂ e₃) :
    causalDist E e₁ e₂ + causalDist E e₂ e₃ ≤ causalDist E e₁ e₃ := by
  obtain ⟨p, hp1, hp2, hp3⟩ := causalDist_mem_chainLengths h₁
  obtain ⟨q, hq1, hq2, hq3⟩ := causalDist_mem_chainLengths h₂
  refine le_csSup (bddAbove_chainLengths E e₁ e₃) ⟨p.smash q (by rw [hp2, hq1]), ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash, hp1]
  · rw [RelSeries.last_smash, hq2]
  · rw [RelSeries.smash_length, hp3, hq3]

/-- ★ **And the distance is monotone into the causal future**: the reverse triangle inequality with
one leg discarded. -/
theorem causalDist_le_of_causalPrecedes_right {E : Finset (Fin K × Fin K)}
    {e₁ e₂ e₃ : RecordEvent K} (h₁ : CausalPrecedes E e₁ e₂) (h₂ : CausalPrecedes E e₂ e₃) :
    causalDist E e₁ e₂ ≤ causalDist E e₁ e₃ :=
  le_trans (Nat.le_add_right _ _) (causalDist_add_le h₁ h₂)

end CSD.CV

end
