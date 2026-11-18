/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedDiracClockTicks

/-!
# A tick takes time: the count of a history is bounded

**Category:** 7-SigmaLayer. BACKLOG #439, third brick (Task 3 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (3); plan `specs/unified-records-spacetime-task-plans.md` §1).

The macroscopic projection of `RecordLayer/UnifiedRadarMacrostate.lean` caps each count at a
parameter `B`. A count is a number of passages from a resting set to a displaying set, and
a passage takes time when the two sets are apart and the history moves at a bounded speed.

* ★★★ `HasTicks.mul_le` — if the history moves at speed at most `K` up to `T` and the two sets
  are at distance at least `d`, then `n` ticks by `T` need `n d ≤ K T`;
* ★★ `IsTickCount.mul_le`, ★★ `IsTickCount.le_div` — so a count at `T` is at most `K T / d`.

## Honest scope

⚠️ **For any history in a metric space; not instantiated.** For a pointer of the arena the
speed is at most `|z| ‖G‖` and `d` is the gap between the ready and the displaying arc in
the circle's metric. Neither is shown here, so the radar's cap is not yet a number.

⚠️ **An upper bound.** It does not say how many ticks there are.

References: `specs/BACKLOG.md` #439; `specs/unified-record-spacetime-plan.md` (UO-25, UD-223,
UD-225, UD-228); `specs/unified-records-spacetime-task-plans.md` (§1);
`RecordLayer/UnifiedDiracClockTicks.lean` (`HasTicks`, `IsTickCount`);
`RecordLayer/UnifiedRadarMacrostate.lean` (`TickReadout.tickMacro`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

namespace CSD.RecordLayer

variable {X : Type*} [PseudoMetricSpace X] {rest disp : Set X} {γ : ℝ → X}

/-- ★★★ **A tick takes time.** If the history moves at speed at most `K` up to `T` and the
resting and displaying sets are at distance at least `d`, then `n` ticks by `T` need
`n d ≤ K T`. -/
theorem HasTicks.mul_le {K d T : ℝ} {n : ℕ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hγ : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → dist (γ s) (γ t) ≤ K * (t - s))
    (hd : ∀ x ∈ rest, ∀ y ∈ disp, d ≤ dist x y) (h : HasTicks rest disp γ T n) :
    (n : ℝ) * d ≤ K * T := by
  obtain ⟨a, b, h1, h2⟩ := h
  have key : ∀ m : ℕ, m < n → ((m + 1 : ℕ) : ℝ) * d ≤ K * b m := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨ha, hab, hb, hr, hdd⟩ := h1 0 hm
      have hstep := (hd _ hr _ hdd).trans (hγ (a 0) (b 0) ha hab.le hb)
      have hKa : 0 ≤ K * a 0 := mul_nonneg hK ha
      push_cast
      linarith only [hstep, hKa, mul_sub K (b 0) (a 0)]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      obtain ⟨ha, hab, hb, hr, hdd⟩ := h1 (m + 1) hm
      have hstep := (hd _ hr _ hdd).trans (hγ (a (m + 1)) (b (m + 1)) ha hab.le hb)
      have hord : K * b m ≤ K * a (m + 1) := mul_le_mul_of_nonneg_left (h2 m hm).le hK
      have hih := ih hm'
      push_cast at hih ⊢
      linarith only [hstep, hord, hih, mul_sub K (b (m + 1)) (a (m + 1))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using mul_nonneg hK hT
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hb : b m ≤ T := (h1 m (Nat.lt_succ_self m)).2.2.1
    exact (key m (Nat.lt_succ_self m)).trans (mul_le_mul_of_nonneg_left hb hK)

/-- ★★ **The count of a history is bounded by its duration**: under the hypotheses of
`HasTicks.mul_le`, a count `N` at `T` satisfies `N d ≤ K T`. -/
theorem IsTickCount.mul_le {K d T : ℝ} {N : ℕ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hγ : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → dist (γ s) (γ t) ≤ K * (t - s))
    (hd : ∀ x ∈ rest, ∀ y ∈ disp, d ≤ dist x y) (h : IsTickCount rest disp γ T N) :
    (N : ℝ) * d ≤ K * T :=
  h.1.mul_le hK hT hγ hd

/-- ★★ **A cap for the count**: for `d > 0` the count at `T` is at most `K T / d`. -/
theorem IsTickCount.le_div {K d T : ℝ} {N : ℕ} (hK : 0 ≤ K) (hT : 0 ≤ T) (hd0 : 0 < d)
    (hγ : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → dist (γ s) (γ t) ≤ K * (t - s))
    (hd : ∀ x ∈ rest, ∀ y ∈ disp, d ≤ dist x y) (h : IsTickCount rest disp γ T N) :
    (N : ℝ) ≤ K * T / d := by
  rw [le_div_iff₀ hd0]
  exact h.mul_le hK hT hγ hd

end CSD.RecordLayer

end
