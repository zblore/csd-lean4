/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.CausalDistance

/-!
# Chronological precedence: the causal order with its same-period steps removed

**Category:** 3-Local (CV; the event layer of `ST-1`).
BACKLOG #192 (out of #39; the second of #191–#197).

`CausalPrecedes E e₁ e₂` allows `e₁.time = e₂.time` with `e₁.region ⊆ e₂.region`-type steps: a
region-inclusion step at an unchanged period index is a strict causal step, and `CausalDistance.lean`
counts it. That is exactly how the inflation theorems of #188 and #190 are built: inserting "both ends
of the edge, at the period of the reception" between the emission and the reception adds a strict step
with **no elapsed period**. This file names the sub-relation whose strict part demands a strictly
later period, and proves what it changes and what it does not.

* `ChronoPrecedes E e₁ e₂ := CausalPrecedes E e₁ e₂ ∧ (e₁ = e₂ ∨ e₁.time < e₂.time)`;
  `ChronoPrecedes.causalPrecedes` — it is a sub-relation; `chronoPrecedes_iff_of_time_ne` — **on events
  of distinct periods the two relations agree**; `chronoPrecedes_of_causalPrecedes_of_lt`;
  ★ `not_chronoPrecedes_of_time_eq` — **distinct simultaneous events are chrono-incomparable** (this is
  how simultaneous writes are handled: neither precedes the other);
* ★ `isPartialOrder_chronoPrecedes` — a partial order (`chronoPrecedes_refl/trans/antisymm`);
* `strictChrono E` — the strict part as a relation chains run on; ★ `time_lt_of_strictChrono` — **its
  strict part excludes every transition with unchanged period**; `isTrans_strictChrono`,
  `isIrrefl_strictChrono` (so a strict chrono chain is acyclic: the period strictly increases along it,
  `time_add_length_le_of_chain`); `strictChrono_le_strictPrecedes` — every chrono step is a causal step;
* `chronoChainLengths`, `chronoDist` — the longest chrono chain, built exactly as `causalDist`;
  ★★ `chronoChainLengths_le_elapsed`, ★★ `chronoDist_le_elapsed` — **the longest chrono chain is
  bounded by the elapsed periods** `e₂.time − e₁.time`; ★ `chronoDist_le_causalDist` — and never
  exceeds the causal longest chain; `chronoDist_add_le` — the reverse triangle inequality survives;
  `chronoDist_pos_iff`.

## What this is not

⚠️ **`CausalPrecedes` is not redefined.** It keeps its name, its theorems and its distance; the
inflation theorems `three_le_causalDist` and `two_mul_le_causalDist` stand untouched, and this file
says *why* they inflate: the steps they insert are strict causal steps with zero elapsed period, which
`strictChrono` excludes (`RecordLayer/ChainChrono.lean` exhibits them).

⚠️ **Chrono chain length is not clock time in general.** The bound `chronoDist ≤ elapsed periods` is an
inequality: a system may write several records in one period, and nothing here forces equality. Where
equality holds — the site chain of the path graph, `RecordLayer/ChainChrono.lean` — it is a property
of that witness.

⚠️ Everything is relative to the assumed coupling graph `E`, as in `RecordCausalOrder.lean`; no metric,
no volume element, no continuum.

References: `specs/BACKLOG.md` #192, #188, #190, #111, #39; `CV/RecordCausalOrder.lean`
(`CausalPrecedes`, `isPartialOrder_causalPrecedes`), `CV/CausalDistance.lean` (`strictPrecedes`,
`chainLengths`, `causalDist`), `RecordLayer/ChainClocks.lean` (`pairEvent`, `two_mul_le_causalDist`).
-/

@[expose] public section

open MeasureTheory Set

open scoped SetRel

namespace CSD.CV

variable {K : ℕ}

/-! ### The relation -/

/-- **Chronological precedence**: causal precedence whose strict part demands a strictly later
period. -/
def ChronoPrecedes (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : Prop :=
  CausalPrecedes E e₁ e₂ ∧ (e₁ = e₂ ∨ e₁.time < e₂.time)

theorem ChronoPrecedes.causalPrecedes {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : ChronoPrecedes E e₁ e₂) : CausalPrecedes E e₁ e₂ := h.1

theorem chronoPrecedes_refl (E : Finset (Fin K × Fin K)) (e : RecordEvent K) :
    ChronoPrecedes E e e := ⟨causalPrecedes_refl E e, Or.inl rfl⟩

/-- A causal step to a strictly later period is a chrono step. -/
theorem chronoPrecedes_of_causalPrecedes_of_lt {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : CausalPrecedes E e₁ e₂) (ht : e₁.time < e₂.time) : ChronoPrecedes E e₁ e₂ := ⟨h, Or.inr ht⟩

/-- **On events of distinct periods the two relations agree.** -/
theorem chronoPrecedes_iff_of_time_ne {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (ht : e₁.time ≠ e₂.time) : ChronoPrecedes E e₁ e₂ ↔ CausalPrecedes E e₁ e₂ :=
  ⟨ChronoPrecedes.causalPrecedes, fun h => ⟨h, Or.inr (lt_of_le_of_ne h.1 ht)⟩⟩

/-- ★ **Distinct simultaneous events are chrono-incomparable.** -/
theorem not_chronoPrecedes_of_time_eq {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (ht : e₁.time = e₂.time) (hne : e₁ ≠ e₂) : ¬ ChronoPrecedes E e₁ e₂ := by
  rintro ⟨_, h | h⟩
  · exact hne h
  · omega

theorem chronoPrecedes_trans {E : Finset (Fin K × Fin K)} {e₁ e₂ e₃ : RecordEvent K}
    (h₁ : ChronoPrecedes E e₁ e₂) (h₂ : ChronoPrecedes E e₂ e₃) : ChronoPrecedes E e₁ e₃ := by
  refine ⟨causalPrecedes_trans h₁.1 h₂.1, ?_⟩
  rcases h₁.2 with rfl | hlt₁
  · exact h₂.2
  · rcases h₂.2 with rfl | hlt₂
    · exact Or.inr hlt₁
    · exact Or.inr (hlt₁.trans hlt₂)

theorem chronoPrecedes_antisymm {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h₁ : ChronoPrecedes E e₁ e₂) (h₂ : ChronoPrecedes E e₂ e₁) : e₁ = e₂ :=
  causalPrecedes_antisymm h₁.1 h₂.1

/-- ★ **Chronological precedence is a partial order on record events.** -/
theorem isPartialOrder_chronoPrecedes (E : Finset (Fin K × Fin K)) :
    IsPartialOrder (RecordEvent K) (ChronoPrecedes E) where
  refl := chronoPrecedes_refl E
  trans := fun _ _ _ => chronoPrecedes_trans
  antisymm := fun _ _ => chronoPrecedes_antisymm

/-! ### The strict part, as a relation chains run on -/

/-- **Strict chronological precedence**: a chrono step to a different event. -/
def strictChrono (E : Finset (Fin K × Fin K)) : SetRel (RecordEvent K) (RecordEvent K) :=
  {q | ChronoPrecedes E q.1 q.2 ∧ q.1 ≠ q.2}

theorem mem_strictChrono {E : Finset (Fin K × Fin K)} {a b : RecordEvent K} :
    a ~[strictChrono E] b ↔ ChronoPrecedes E a b ∧ a ≠ b := Iff.rfl

/-- ★ **A strict chrono step moves to a strictly later period**: no transition with unchanged
occurrence time is a step. -/
theorem time_lt_of_strictChrono {E : Finset (Fin K × Fin K)} {a b : RecordEvent K}
    (h : a ~[strictChrono E] b) : a.time < b.time := by
  rcases h.1.2 with heq | hlt
  · exact absurd heq h.2
  · exact hlt

theorem strictChrono_of_causalPrecedes_of_lt {E : Finset (Fin K × Fin K)} {a b : RecordEvent K}
    (h : CausalPrecedes E a b) (ht : a.time < b.time) : a ~[strictChrono E] b :=
  ⟨chronoPrecedes_of_causalPrecedes_of_lt h ht, fun heq => by
    have h' : a = b := heq
    rw [h'] at ht
    exact lt_irrefl _ ht⟩

/-- Every chrono step is a causal step. -/
theorem strictChrono_le_strictPrecedes (E : Finset (Fin K × Fin K)) :
    strictChrono E ≤ strictPrecedes E := fun _ hq => ⟨hq.1.1, hq.2⟩

theorem isTrans_strictChrono (E : Finset (Fin K × Fin K)) : (strictChrono E).IsTrans :=
  ⟨fun a _ c hab hbc => ⟨chronoPrecedes_trans hab.1 hbc.1, fun hac => by
    have hlt := (time_lt_of_strictChrono hab).trans (time_lt_of_strictChrono hbc)
    have h' : a = c := hac
    rw [h'] at hlt
    exact lt_irrefl _ hlt⟩⟩

/-- A strict chrono step never returns: the relation is irreflexive, hence (with transitivity)
acyclic. -/
theorem isIrrefl_strictChrono (E : Finset (Fin K × Fin K)) : (strictChrono E).IsIrrefl :=
  ⟨fun _ ha => ha.2 rfl⟩

/-! ### Along a chrono chain the period strictly increases -/

/-- The period at step `i` of a strict chrono chain is at least the head's period plus `i`. -/
theorem time_add_le_of_chain {E : Finset (Fin K × Fin K)} (p : RelSeries (strictChrono E))
    (i : Fin (p.length + 1)) : (p 0).time + (i : ℕ) ≤ (p i).time := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      have hlt := time_lt_of_strictChrono (p.step i)
      rw [Fin.val_castSucc] at ih
      rw [Fin.val_succ]
      omega

/-- ★ **A strict chrono chain is acyclic and its length is at most the elapsed periods**: the head's
period plus the length is at most the last's period. -/
theorem time_add_length_le_of_chain {E : Finset (Fin K × Fin K)} (p : RelSeries (strictChrono E)) :
    p.head.time + p.length ≤ p.last.time := by
  have h := time_add_le_of_chain p (Fin.last _)
  rw [Fin.val_last] at h
  exact h

/-! ### The chrono chain lengths and the chrono distance -/

/-- The lengths of the strict chrono chains from `e₁` to `e₂`. -/
def chronoChainLengths (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : Set ℕ :=
  {n | ∃ p : RelSeries (strictChrono E), p.head = e₁ ∧ p.last = e₂ ∧ p.length = n}

/-- ★★ **Every chrono chain is bounded by the elapsed periods.** -/
theorem chronoChainLengths_le_elapsed {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K} {n : ℕ}
    (hn : n ∈ chronoChainLengths E e₁ e₂) : n ≤ e₂.time - e₁.time := by
  obtain ⟨p, hhead, hlast, rfl⟩ := hn
  have h := time_add_length_le_of_chain p
  rw [hhead, hlast] at h
  omega

/-- A chrono chain is a causal chain of the same length. -/
theorem chronoChainLengths_subset_chainLengths (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    chronoChainLengths E e₁ e₂ ⊆ chainLengths E e₁ e₂ := by
  rintro n ⟨p, hhead, hlast, rfl⟩
  exact ⟨p.ofLE (strictChrono_le_strictPrecedes E), hhead, hlast, rfl⟩

theorem bddAbove_chronoChainLengths (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    BddAbove (chronoChainLengths E e₁ e₂) :=
  ⟨e₂.time - e₁.time, fun _ hn => chronoChainLengths_le_elapsed hn⟩

/-- **The chrono distance**: the length of the longest strict chrono chain, `0` when there is none. -/
noncomputable def chronoDist (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : ℕ :=
  sSup (chronoChainLengths E e₁ e₂)

/-- ★★ **The longest chrono chain is bounded by the elapsed periods.** -/
theorem chronoDist_le_elapsed (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    chronoDist E e₁ e₂ ≤ e₂.time - e₁.time := by
  rcases Set.eq_empty_or_nonempty (chronoChainLengths E e₁ e₂) with h | h
  · rw [chronoDist, h]
    simp
  · exact csSup_le h fun _ hn => chronoChainLengths_le_elapsed hn

/-- ★ **The chrono distance never exceeds the causal distance.** -/
theorem chronoDist_le_causalDist (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) :
    chronoDist E e₁ e₂ ≤ causalDist E e₁ e₂ := by
  rcases Set.eq_empty_or_nonempty (chronoChainLengths E e₁ e₂) with h | h
  · rw [chronoDist, h]
    simp
  · exact csSup_le h fun n hn =>
      le_csSup (bddAbove_chainLengths E e₁ e₂) (chronoChainLengths_subset_chainLengths E e₁ e₂ hn)

theorem zero_mem_chronoChainLengths (E : Finset (Fin K × Fin K)) (e : RecordEvent K) :
    0 ∈ chronoChainLengths E e e :=
  ⟨RelSeries.singleton _ e, RelSeries.head_singleton e, RelSeries.last_singleton e, rfl⟩

theorem one_mem_chronoChainLengths {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : e₁ ~[strictChrono E] e₂) : 1 ∈ chronoChainLengths E e₁ e₂ := by
  refine ⟨(RelSeries.singleton (strictChrono E) e₂).cons e₁ ?_, ?_, ?_, ?_⟩
  · rw [RelSeries.head_singleton]
    exact h
  · exact RelSeries.head_cons _ _ _
  · rw [RelSeries.last_cons, RelSeries.last_singleton]
  · simp

theorem nonempty_chronoChainLengths_of_chronoPrecedes {E : Finset (Fin K × Fin K)}
    {e₁ e₂ : RecordEvent K} (h : ChronoPrecedes E e₁ e₂) :
    (chronoChainLengths E e₁ e₂).Nonempty := by
  by_cases hne : e₁ = e₂
  · subst hne
    exact ⟨0, zero_mem_chronoChainLengths E e₁⟩
  · exact ⟨1, one_mem_chronoChainLengths ⟨h, hne⟩⟩

/-- The longest chrono chain is attained. -/
theorem chronoDist_mem_chronoChainLengths {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : ChronoPrecedes E e₁ e₂) : chronoDist E e₁ e₂ ∈ chronoChainLengths E e₁ e₂ :=
  Nat.sSup_mem (nonempty_chronoChainLengths_of_chronoPrecedes h) (bddAbove_chronoChainLengths E e₁ e₂)

theorem chronoDist_eq_zero_of_not_chronoPrecedes {E : Finset (Fin K × Fin K)}
    {e₁ e₂ : RecordEvent K} (h : ¬ ChronoPrecedes E e₁ e₂) : chronoDist E e₁ e₂ = 0 := by
  have hempty : chronoChainLengths E e₁ e₂ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun n hn => ?_
    obtain ⟨p, hhead, hlast, _⟩ := hn
    have hT := isTrans_strictChrono E
    have hpre : ChronoPrecedes E (p 0) (p (Fin.last _)) := by
      rcases p.rel_or_eq_of_le (i := 0) (j := Fin.last _) (Fin.zero_le _) with hr | hr
      · exact hr.1
      · rw [hr]
        exact chronoPrecedes_refl E _
    rw [show p 0 = e₁ from hhead, show p (Fin.last _) = e₂ from hlast] at hpre
    exact h hpre
  rw [chronoDist, hempty]
  simp

theorem chronoDist_self (E : Finset (Fin K × Fin K)) (e : RecordEvent K) : chronoDist E e e = 0 :=
  Nat.le_zero.mp (by simpa using chronoDist_le_elapsed E e e)

/-- ★ **The chrono distance is positive exactly on the strictly chrono-related pairs.** -/
theorem chronoDist_pos_iff {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K} :
    0 < chronoDist E e₁ e₂ ↔ ChronoPrecedes E e₁ e₂ ∧ e₁ ≠ e₂ := by
  refine ⟨fun hpos => ?_, fun h => ?_⟩
  · by_cases hc : ChronoPrecedes E e₁ e₂
    · refine ⟨hc, ?_⟩
      rintro rfl
      rw [chronoDist_self] at hpos
      exact absurd hpos (lt_irrefl 0)
    · rw [chronoDist_eq_zero_of_not_chronoPrecedes hc] at hpos
      exact absurd hpos (lt_irrefl 0)
  · exact lt_of_lt_of_le Nat.zero_lt_one
      (le_csSup (bddAbove_chronoChainLengths E e₁ e₂) (one_mem_chronoChainLengths h))

/-- The reverse triangle inequality survives the restriction: chrono chains concatenate. -/
theorem chronoDist_add_le {E : Finset (Fin K × Fin K)} {e₁ e₂ e₃ : RecordEvent K}
    (h₁ : ChronoPrecedes E e₁ e₂) (h₂ : ChronoPrecedes E e₂ e₃) :
    chronoDist E e₁ e₂ + chronoDist E e₂ e₃ ≤ chronoDist E e₁ e₃ := by
  obtain ⟨p, hp1, hp2, hp3⟩ := chronoDist_mem_chronoChainLengths h₁
  obtain ⟨q, hq1, hq2, hq3⟩ := chronoDist_mem_chronoChainLengths h₂
  refine le_csSup (bddAbove_chronoChainLengths E e₁ e₃) ⟨p.smash q (by rw [hp2, hq1]), ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash, hp1]
  · rw [RelSeries.last_smash, hq2]
  · rw [RelSeries.smash_length, hp3, hq3]

end CSD.CV

end
