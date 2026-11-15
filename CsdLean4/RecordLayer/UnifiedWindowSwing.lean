/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGatedReading

/-!
# A swing that starts in the middle: the count of a gate that opens late

**Category:** 7-SigmaLayer (the record layer). BACKLOG #398 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, eighth brick: the pointer side of the return reading. No new assumption.

Of the five readings of UA-18 (d), four belong to gates that are open from the flow time `0`,
when the clock's swing is at its start; #394 reads those. The fifth, the moving observer's
ticks while the messenger is not with it, belongs to a gate that opens in the middle of the
run. By #393 the displacement of its pointer is the clock's own displacement minus that of
the emission pointer, so while the messenger is away it is `(1/4)(1 − cos R t) − c`, with `c`
the displacement at which the emission pointer stopped. This module counts the ticks of such
a pointer.

* `IsWindowSwing` — a swing on a window `[s, T]`, read against a phase `R t + φ`, resting
  where the cosine of the phase equals `κ`; `IsSwing` (#358) is `s = 0`, `φ = 0`, `κ = 1`;
* ★★ `IsWindowSwing.hasTicks_le`, ★★ `IsWindowSwing.hasTicks_add` — at most one tick a turn,
  and one tick in every turn completed, inside the window;
* ★★★ `IsWindowSwing.abs_count_sub_le`, `IsWindowSwing.exists_tickCount` — the count advances
  over the window by the phase advanced, within three turns;
* `pshift_notMem_readyArc_of_nonpos`, `pshift_mem_displayArc_iff_of_nonpos`;
* ★★ `isWindowSwing_snd_high`, ★★ `isWindowSwing_snd_low` — a pointer whose displacement is
  within `η < 1/12` of `(1/4)(1 − cos R t) − c` is a window swing when its lower turning
  point `p = θ₁ − c` is in `(−1/6 + η, 1/6 − η]` (its upper end displays) or in
  `(−1/2 + η, −1/6 − η)` (its lower end displays, a turn back);
* ★★★ `offset_swing_count` — in either band: `|2π (N_T − N_s) − R (T − s)| ≤ 6π`;
* ★★ `offset_swing_dead` — for `p` in `(1/6 + η, 1/2 − η]` the pointer is never in the ready
  arc on the window and its count advances by at most one, however far the phase advances.

## Exact scope

* **The return reading is conditional on where the emission pointer stopped.** With both
  pointers started at `1/12`, `p = 1/12 − c`. The count over the window follows the clock
  when `c` is in `[−1/12 + η, 1/4 − η)` or in `(1/4 + η, 7/12 − η)`. It stops when `c`,
  taken modulo one turn, is in `[7/12 + η, 11/12 − η)`. Within `η` of `1/4`, `7/12` and
  `11/12` nothing is proved; there the count can differ from the phase by up to one tick in
  every turn (a calculation, not in Lean). No choice of the arcs and the amplitude removes
  the edges: as the offset goes once round, the number of passages per turn must change
  somewhere (a calculation, not in Lean).
* **Where `c` lies is not shown.** `c` is the emission pointer's displacement when its gate
  has closed. While the gate closes it is bounded only by the pointer's speed (#394), so it
  is not shown to lie in `[0, 1/2]`, nor in either band. That it does is a hypothesis about
  the run, to be stated in the return reading.
* **A pointer's history, on no arena.** No flow, carrier or gate appears in this module. The
  return reading itself, with the gate that closes, opens and closes again, is the next
  brick.
* **The numbers are those of the clock pointer of #391**: half-amplitude `1/4`, arcs
  `(0, 1/6]` and `(1/3, 5/6]`.
* **Counts of passages**, as #358; flow times.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-61, UD-146, UD-147, UD-155, UD-156); `RecordLayer/UnifiedDiracClockTicks.lean`
(#358: `IsSwing`, `HasTicks`, `IsTickCount`, `cos_le_max_cos`, `pshift_mem_readyArc_iff`,
`pshift_mem_displayArc_iff`); `RecordLayer/UnifiedTwoCounts.lean` (#381:
`hasTicks_le_succ_of_no_passage`, `exists_tickCount_of_bdd`);
`RecordLayer/UnifiedGatedReading.lean` (#394: `gated_pointer_count`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincShift_gateOp_add_not`);
`RecordLayer/ActivatedWrite.lean` (`rep_pshift_of_mem_neg`, `displayArc`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### A swing on a window, with a phase and a resting phase -/

section Window

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- **A swing history on the window `[s, T]`**, read against the phase `R t + φ`: resting
wherever the cosine of the phase equals `κ`, displaying wherever it is below `d`, and separated
by the threshold `c` (resting only where the cosine is at least `c`, displaying only where it
is below `c`). `IsSwing` (#358) is the case `s = 0`, `φ = 0`, `κ = 1`. -/
structure IsWindowSwing (rest disp : Set X) (γ : ℝ → X) (R φ c d κ s T : ℝ) : Prop where
  /-- The phase advances. -/
  rate_pos : 0 < R
  /-- The displaying threshold is reached at the half turn. -/
  neg_one_lt : -1 < d
  /-- The displaying threshold is below the separating one. -/
  thresh_le : d ≤ c
  /-- The resting phase is before the half turn. -/
  neg_one_lt_rest : -1 < κ
  /-- The resting value is a cosine. -/
  rest_le_one : κ ≤ 1
  /-- The history rests wherever the cosine equals `κ`. -/
  rest_of_cos : ∀ t, s ≤ t → t ≤ T → Real.cos (R * t + φ) = κ → γ t ∈ rest
  /-- The history displays wherever the cosine is below `d`. -/
  disp_of_cos : ∀ t, s ≤ t → t ≤ T → Real.cos (R * t + φ) < d → γ t ∈ disp
  /-- The history rests only where the cosine is at least `c`. -/
  le_cos_of_rest : ∀ t, s ≤ t → t ≤ T → γ t ∈ rest → c ≤ Real.cos (R * t + φ)
  /-- The history displays only where the cosine is below `c`. -/
  cos_lt_of_disp : ∀ t, s ≤ t → t ≤ T → γ t ∈ disp → Real.cos (R * t + φ) < c

/-- ★★ **A window swing ticks at most once a turn.** A history without `N₀ + 1` ticks by `s`
that is a swing on `[s, T]` has at most `N₀ + R (T − s)/(2π) + 3` ticks by `T`. -/
theorem IsWindowSwing.hasTicks_le {R φ c d κ s T : ℝ}
    (h : IsWindowSwing rest disp γ R φ c d κ s T) (hsT : s ≤ T) {m N₀ : ℕ}
    (hm : HasTicks rest disp γ T m) (hN : ¬ HasTicks rest disp γ s (N₀ + 1)) :
    (m : ℝ) ≤ N₀ + R * (T - s) / (2 * Real.pi) + 3 := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  have hX0 : 0 ≤ R * (T - s) / (2 * Real.pi) :=
    div_nonneg (mul_nonneg hR.le (sub_nonneg.2 hsT)) (by positivity)
  obtain ⟨a, b, h1, h2⟩ := hm
  by_cases hle : m ≤ N₀ + 1
  · have hc : (m : ℝ) ≤ (N₀ : ℝ) + 1 := by exact_mod_cast hle
    linarith
  obtain ⟨e₀, rfl⟩ : ∃ e₀, m = N₀ + 2 + e₀ := ⟨m - N₀ - 2, by omega⟩
  -- the ends of the ticks increase
  have hb : ∀ j, j < N₀ + 2 + e₀ → ∀ i, i ≤ j → b i ≤ b j := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      rw [Nat.le_zero.1 hi]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact ((ih (by omega) i (by omega)).trans (h2 j hj).le).trans (h1 (j + 1) hj).2.1.le
      · rw [le_antisymm hi hge]
  -- the tick `N₀` ends after `s`
  have hbN : s < b N₀ := by
    by_contra hc
    rw [not_lt] at hc
    exact hN ⟨a, b, fun i hi =>
      ⟨(h1 i (by omega)).1, (h1 i (by omega)).2.1, (hb N₀ (by omega) i (by omega)).trans hc,
        (h1 i (by omega)).2.2.2.1, (h1 i (by omega)).2.2.2.2⟩, fun i hi => h2 i (by omega)⟩
  -- the later ticks begin after `s`
  have hsa : ∀ e, N₀ + 1 + e < N₀ + 2 + e₀ → s ≤ a (N₀ + 1 + e) := by
    intro e he
    have h3 := h2 (N₀ + e) (by omega)
    have e1 : N₀ + e + 1 = N₀ + 1 + e := by omega
    rw [e1] at h3
    exact (hbN.le.trans (hb (N₀ + e) (by omega) N₀ (by omega))).trans h3.le
  -- each later display is one more whole turn on
  have hk0 : (⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ R * s + φ := by
    have := Int.floor_le ((R * s + φ) / (2 * Real.pi))
    rwa [le_div_iff₀ (by positivity)] at this
  have hk1 : R * s + φ < ((⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
    have := Int.lt_floor_add_one ((R * s + φ) / (2 * Real.pi))
    rwa [div_lt_iff₀ (by positivity)] at this
  have key : ∀ e, N₀ + 1 + e < N₀ + 2 + e₀ →
      ((⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) + e) * (2 * Real.pi) ≤ R * b (N₀ + 1 + e) + φ := by
    intro e
    induction e with
    | zero =>
      intro he
      have hs := hsa 0 he
      have hab := (h1 (N₀ + 1 + 0) he).2.1
      have : R * s ≤ R * b (N₀ + 1 + 0) := mul_le_mul_of_nonneg_left (hs.trans hab.le) hR.le
      push_cast
      linarith
    | succ e ih =>
      intro he
      have he' : N₀ + 1 + e < N₀ + 2 + e₀ := by omega
      have hI := ih he'
      obtain ⟨-, hab0, hb0, -, hd0⟩ := h1 (N₀ + 1 + e) he'
      have hj : N₀ + 1 + e + 1 = N₀ + 1 + (e + 1) := by omega
      obtain ⟨-, hab1, hb1, hr1, hd1⟩ := h1 (N₀ + 1 + (e + 1)) he
      have hba := h2 (N₀ + 1 + e) (by omega)
      rw [hj] at hba
      have hs0 := hsa e he'
      have hs1 := hsa (e + 1) he
      by_contra hlt
      rw [not_le] at hlt
      push_cast at hlt
      have hK1 : (⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
          ≤ R * b (N₀ + 1 + e) + φ := by
        have := Int.floor_le ((R * b (N₀ + 1 + e) + φ) / (2 * Real.pi))
        rwa [le_div_iff₀ (by positivity)] at this
      have hiK : (⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) + e
          ≤ (⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ : ℝ) := by
        have : ⌊(R * s + φ) / (2 * Real.pi)⌋ + (e : ℤ)
            ≤ ⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ :=
          Int.le_floor.2 (by
            rw [le_div_iff₀ (by positivity)]
            push_cast
            exact hI)
        exact_mod_cast this
      have hx := h.cos_lt_of_disp (b (N₀ + 1 + e)) (hs0.trans hab0.le) hb0 hd0
      have hy := h.le_cos_of_rest (a (N₀ + 1 + (e + 1))) hs1 (hab1.le.trans hb1) hr1
      have hz := h.cos_lt_of_disp (b (N₀ + 1 + (e + 1))) (hs1.trans hab1.le) hb1 hd1
      have hRab : R * b (N₀ + 1 + e) < R * a (N₀ + 1 + (e + 1)) :=
        mul_lt_mul_of_pos_left hba hR
      have hRab1 : R * a (N₀ + 1 + (e + 1)) < R * b (N₀ + 1 + (e + 1)) :=
        mul_lt_mul_of_pos_left hab1 hR
      have hmax := cos_le_max_cos
        (x := R * b (N₀ + 1 + e) + φ
          - (⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (y := R * a (N₀ + 1 + (e + 1)) + φ
          - (⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (z := R * b (N₀ + 1 + (e + 1)) + φ
          - (⌊(R * b (N₀ + 1 + e) + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (by linarith) (by linarith) (by linarith)
        (by
          have := mul_le_mul_of_nonneg_right hiK (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          linarith)
      rw [Real.cos_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi,
        Real.cos_sub_int_mul_two_pi] at hmax
      exact absurd (hy.trans hmax) (not_le.2 (max_lt hx hz))
  have hlast := key e₀ (by omega)
  have hbT := (h1 (N₀ + 1 + e₀) (by omega)).2.2.1
  have hRb : R * b (N₀ + 1 + e₀) ≤ R * T := mul_le_mul_of_nonneg_left hbT hR.le
  have hfin : (e₀ : ℝ) * (2 * Real.pi) ≤ R * (T - s) + 2 * Real.pi := by nlinarith
  have hdiv : (e₀ : ℝ) ≤ R * (T - s) / (2 * Real.pi) + 1 := by
    rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
    linarith
  push_cast
  linarith

/-- ★★ **A window swing ticks once in every turn it completes.** A history with `m` ticks by
`s` that is a swing on `[s, T]` whose phase advances through `2π n + π` in the window has
`m + n` ticks by `T`. -/
theorem IsWindowSwing.hasTicks_add {R φ c d κ s T : ℝ}
    (h : IsWindowSwing rest disp γ R φ c d κ s T) (hs0 : 0 ≤ s) {m n : ℕ}
    (hm : HasTicks rest disp γ s m)
    (hn : (n : ℝ) * (2 * Real.pi) + Real.pi ≤ R * (T - s)) :
    HasTicks rest disp γ T (m + n) := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  obtain ⟨a, b, h1, h2⟩ := hm
  have hk0 : (⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ R * s + φ := by
    have := Int.floor_le ((R * s + φ) / (2 * Real.pi))
    rwa [le_div_iff₀ (by positivity)] at this
  have hk1 : R * s + φ < ((⌊(R * s + φ) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
    have := Int.lt_floor_add_one ((R * s + φ) / (2 * Real.pi))
    rwa [div_lt_iff₀ (by positivity)] at this
  generalize hkd : (⌊(R * s + φ) / (2 * Real.pi)⌋ : ℤ) = k at hk0 hk1
  have hacos0 := Real.arccos_nonneg κ
  have hacos1 : Real.arccos κ < Real.pi := Real.arccos_lt_pi.2 h.neg_one_lt_rest
  -- the new passages
  have hθa : ∀ j : ℕ, R * ((((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.arccos κ - φ) / R) + φ
      = Real.arccos κ + ((k + 1 + (j : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    intro j
    push_cast
    field_simp
    ring
  have hθb : ∀ j : ℕ, R * ((((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.pi - φ) / R) + φ
      = ((k + 1 + (j : ℤ) : ℤ) : ℝ) * (2 * Real.pi) + Real.pi := by
    intro j
    push_cast
    field_simp
    ring
  have hsa : ∀ j : ℕ, s < (((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.arccos κ - φ) / R := by
    intro j
    rw [lt_div_iff₀ hR]
    have hj : (0 : ℝ) ≤ (j : ℝ) * (2 * Real.pi) := by positivity
    nlinarith
  have hab : ∀ j : ℕ, (((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.arccos κ - φ) / R
      < (((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.pi - φ) / R := fun j =>
    div_lt_div_of_pos_right (by linarith) hR
  have hbT : ∀ j : ℕ, j < n →
      (((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.pi - φ) / R ≤ T := by
    intro j hj
    rw [div_le_iff₀ hR]
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have := mul_le_mul_of_nonneg_right hjn (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    nlinarith
  have hba : ∀ j : ℕ, (((k : ℝ) + 1 + j) * (2 * Real.pi) + Real.pi - φ) / R
      < (((k : ℝ) + 1 + (j + 1 : ℕ)) * (2 * Real.pi) + Real.arccos κ - φ) / R := by
    intro j
    refine div_lt_div_of_pos_right ?_ hR
    push_cast
    linarith
  refine ⟨fun i => if i < m then a i
      else (((k : ℝ) + 1 + (i - m : ℕ)) * (2 * Real.pi) + Real.arccos κ - φ) / R,
    fun i => if i < m then b i
      else (((k : ℝ) + 1 + (i - m : ℕ)) * (2 * Real.pi) + Real.pi - φ) / R,
    fun i hi => ?_, fun i hi => ?_⟩
  · by_cases him : i < m
    · simp only [him, ite_true]
      obtain ⟨ha, hab', hb, hr, hd⟩ := h1 i him
      have hsT : s ≤ T := by
        have h0 : 0 ≤ R * (T - s) := by
          have : (0 : ℝ) ≤ (n : ℝ) * (2 * Real.pi) := by positivity
          linarith
        have := nonneg_of_mul_nonneg_right h0 hR
        linarith
      exact ⟨ha, hab', hb.trans hsT, hr, hd⟩
    · simp only [him, ite_false]
      have hj : i - m < n := by omega
      have hs := hsa (i - m)
      refine ⟨hs0.trans hs.le, hab (i - m), hbT (i - m) hj,
        h.rest_of_cos _ hs.le ((hab (i - m)).le.trans (hbT (i - m) hj)) ?_,
        h.disp_of_cos _ (hs.le.trans (hab (i - m)).le) (hbT (i - m) hj) ?_⟩
      · rw [hθa, Real.cos_add_int_mul_two_pi, Real.cos_arccos h.neg_one_lt_rest.le
          h.rest_le_one]
      · rw [hθb, Real.cos_int_mul_two_pi_add_pi]
        exact h.neg_one_lt
  · by_cases him : i + 1 < m
    · have him' : i < m := by omega
      simp only [him, him', ite_true]
      exact h2 i him
    · by_cases him' : i < m
      · simp only [him, him', ite_true, ite_false]
        exact (h1 i him').2.2.1.trans_lt (hsa _)
      · simp only [him, him', ite_false]
        have e : i + 1 - m = (i - m) + 1 := by omega
        rw [e]
        exact hba (i - m)

/-- ★★★ **The count over a window of a swing is the phase advanced, within three turns.** If
the count is `N_s` at `s` and `N_T` at `T`, and the history is a swing on `[s, T]`, then
`|2π (N_T − N_s) − R (T − s)| ≤ 6π`. -/
theorem IsWindowSwing.abs_count_sub_le {R φ c d κ s T : ℝ}
    (h : IsWindowSwing rest disp γ R φ c d κ s T) (hs0 : 0 ≤ s) (hsT : s ≤ T) {Ns NT : ℕ}
    (hNs : IsTickCount rest disp γ s Ns) (hNT : IsTickCount rest disp γ T NT) :
    |((NT : ℝ) - Ns) * (2 * Real.pi) - R * (T - s)| ≤ 3 * (2 * Real.pi) := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  have hX0 : 0 ≤ R * (T - s) := mul_nonneg hR.le (sub_nonneg.2 hsT)
  have hup := h.hasTicks_le hsT hNT.1 hNs.2
  have hup' : ((NT : ℝ) - Ns) * (2 * Real.pi) ≤ R * (T - s) + 3 * (2 * Real.pi) := by
    have h1 : (NT : ℝ) - Ns ≤ R * (T - s) / (2 * Real.pi) + 3 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have e : (R * (T - s) / (2 * Real.pi) + 3) * (2 * Real.pi)
        = R * (T - s) + 3 * (2 * Real.pi) := by
      field_simp
    linarith
  have hmono : Ns ≤ NT := by
    by_contra hlt
    rw [not_le] at hlt
    exact hNT.2 ((hNs.1.mono_time hsT).mono_count (by omega))
  have hmono' : (Ns : ℝ) ≤ NT := by exact_mod_cast hmono
  have hlo : R * (T - s) - 3 * (2 * Real.pi) ≤ ((NT : ℝ) - Ns) * (2 * Real.pi) := by
    by_cases hsmall : R * (T - s) < Real.pi
    · have : 0 ≤ ((NT : ℝ) - Ns) * (2 * Real.pi) :=
        mul_nonneg (sub_nonneg.2 hmono') (by positivity)
      linarith
    · rw [not_lt] at hsmall
      have ha0 : 0 ≤ (R * (T - s) - Real.pi) / (2 * Real.pi) :=
        div_nonneg (by linarith) (by positivity)
      have hfl := Nat.floor_le ha0
      have hfl' := Nat.lt_floor_add_one ((R * (T - s) - Real.pi) / (2 * Real.pi))
      rw [le_div_iff₀ (by positivity)] at hfl
      rw [div_lt_iff₀ (by positivity)] at hfl'
      have hadd := h.hasTicks_add hs0 (n := ⌊(R * (T - s) - Real.pi) / (2 * Real.pi)⌋₊)
        hNs.1 (by linarith)
      have hle : Ns + ⌊(R * (T - s) - Real.pi) / (2 * Real.pi)⌋₊ ≤ NT := by
        by_contra hlt
        rw [not_le] at hlt
        exact hNT.2 (hadd.mono_count (by omega))
      have hle' : (Ns : ℝ) + (⌊(R * (T - s) - Real.pi) / (2 * Real.pi)⌋₊ : ℝ) ≤ NT := by
        exact_mod_cast hle
      nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **A window swing has a count at the end of the window**, if it has one at the start. -/
theorem IsWindowSwing.exists_tickCount {R φ c d κ s T : ℝ}
    (h : IsWindowSwing rest disp γ R φ c d κ s T) (hsT : s ≤ T) {Ns : ℕ}
    (hNs : IsTickCount rest disp γ s Ns) : ∃ NT, IsTickCount rest disp γ T NT := by
  refine exists_tickCount_of_bdd (B := Ns + ⌈R * (T - s) / (2 * Real.pi)⌉₊ + 3) fun m hm => ?_
  have h1 := h.hasTicks_le hsT hm hNs.2
  have h2 := Nat.le_ceil (R * (T - s) / (2 * Real.pi))
  have h3 : (m : ℝ) ≤ ((Ns + ⌈R * (T - s) / (2 * Real.pi)⌉₊ + 3 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

end Window

/-! ### A pointer whose swing is offset -/

section Pointer

variable {Y : Type*}

/-- A pointer turned back past zero, by less than `5/6` of a turn, is not in the ready arc. -/
theorem pshift_notMem_readyArc_of_nonpos {q : KTorus} {a : ℝ} (h0 : -5 / 6 < rep q.1 + a)
    (h1 : rep q.1 + a ≤ 0) : pshift a q ∉ readyArc 2 := by
  intro hr
  have hr' : rep (pshift a q).1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hr
  rw [shearWidth_two, rep_pshift_of_mem_neg q ⟨by linarith, h1⟩] at hr'
  linarith [hr'.2]

/-- A pointer turned back past zero, by less than `2/3` of a turn, is in the displayed arc
exactly when it is at least a sixth of a turn back. -/
theorem pshift_mem_displayArc_iff_of_nonpos {q : KTorus} {a : ℝ} (h0 : -2 / 3 < rep q.1 + a)
    (h1 : rep q.1 + a ≤ 0) : pshift a q ∈ displayArc ↔ rep q.1 + a ≤ -1 / 6 := by
  have e := rep_pshift_of_mem_neg q (a := a) ⟨by linarith, h1⟩
  show rep (pshift a q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) ↔ _
  rw [shearWidth_two, e]
  constructor
  · intro h
    linarith [h.2]
  · intro h
    exact ⟨by linarith, by linarith⟩

/-- ★★ **An offset swing whose upper end displays.** A last pointer whose displacement on
`[s, T]` is within `η < 1/12` of `(1/4)(1 − cos R t) − c`, with the lower turning point
`p = θ₁ − c` in `(−1/6 + η, 1/6 − η]`: a window swing at the phase `R t`, resting where the
pointer is at `max p (1/12)`. -/
theorem isWindowSwing_snd_high {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ}
    {R c η s T : ℝ} (hR : 0 < R) (hη : 0 ≤ η) (hη1 : η < 1 / 12)
    (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hD : ∀ t, s ≤ t → t ≤ T → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η)
    (h₁ : -1 / 6 + η < rep q.1 - c) (h₂ : rep q.1 - c ≤ 1 / 6 - η) :
    IsWindowSwing {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc} γ R 0
      (1 - 4 * (1 / 6 - (rep q.1 - c) + η)) (1 - 4 * (1 / 3 - (rep q.1 - c) + η))
      (min 1 (2 / 3 + 4 * (rep q.1 - c))) s T := by
  have key : ∀ t, s ≤ t → t ≤ T →
      rep q.1 - c + 1 / 4 * (1 - Real.cos (R * t + 0)) - η ≤ rep q.1 + D t
      ∧ rep q.1 + D t ≤ rep q.1 - c + 1 / 4 * (1 - Real.cos (R * t + 0)) + η
      ∧ -1 / 6 < rep q.1 + D t ∧ rep q.1 + D t ≤ 5 / 6 := by
    intro t hst htT
    have hs := abs_le.1 (hD t hst htT)
    have hc1 := Real.cos_le_one (R * t)
    have hc2 := Real.neg_one_le_cos (R * t)
    rw [add_zero]
    refine ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨hR, by linarith, by linarith, lt_min (by norm_num) (by linarith), min_le_left _ _,
    ?_, ?_, ?_, ?_⟩
  · intro t hst htT hcos
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    rw [hcos] at hlo hhi
    show (γ t).2 ∈ readyArc 2
    rcases le_total 1 (2 / 3 + 4 * (rep q.1 - c)) with hk | hk
    · rw [min_eq_left hk] at hlo hhi
      rw [hγ t hst htT, pshift_mem_readyArc_iff (by linarith) (by linarith)]
      linarith
    · rw [min_eq_right hk] at hlo hhi
      rw [hγ t hst htT, pshift_mem_readyArc_iff (by linarith) (by linarith)]
      linarith
  · intro t hst htT hcos
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    show (γ t).2 ∈ displayArc
    rw [hγ t hst htT, pshift_mem_displayArc_iff (by linarith) hM]
    linarith
  · intro t hst htT hr
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    have hr' : (γ t).2 ∈ readyArc 2 := hr
    rw [hγ t hst htT] at hr'
    rcases lt_or_ge 0 (rep q.1 + D t) with hpos | hneg
    · rw [pshift_mem_readyArc_iff hpos (by linarith)] at hr'
      linarith
    · exact absurd hr' (pshift_notMem_readyArc_of_nonpos (by linarith) hneg)
  · intro t hst htT hd
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    have hd' : (γ t).2 ∈ displayArc := hd
    rw [hγ t hst htT] at hd'
    rcases lt_or_ge 0 (rep q.1 + D t) with hpos | hneg
    · rw [pshift_mem_displayArc_iff hpos hM] at hd'
      linarith
    · rw [pshift_mem_displayArc_iff_of_nonpos (by linarith) hneg] at hd'
      linarith

/-- ★★ **An offset swing whose lower end displays.** A last pointer whose displacement on
`[s, T]` is within `η < 1/12` of `(1/4)(1 − cos R t) − c`, with the lower turning point
`p = θ₁ − c` in `(−1/2 + η, −1/6 − η)`: a window swing at the phase `R t + π`, displaying at
its lower turning point, a turn back. -/
theorem isWindowSwing_snd_low {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ}
    {R c η s T : ℝ} (hR : 0 < R) (hη : 0 ≤ η) (hη1 : η < 1 / 12)
    (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hD : ∀ t, s ≤ t → t ≤ T → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η)
    (h₁ : -1 / 2 + η < rep q.1 - c) (h₂ : rep q.1 - c < -1 / 6 - η) :
    IsWindowSwing {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc} γ R
      Real.pi (-1 + 4 * (-(rep q.1 - c) - η)) (-1 + 4 * (-1 / 6 - (rep q.1 - c) - η))
      (min 1 (-2 / 3 - 4 * (rep q.1 - c))) s T := by
  have key : ∀ t, s ≤ t → t ≤ T →
      rep q.1 - c + 1 / 4 * (1 + Real.cos (R * t + Real.pi)) - η ≤ rep q.1 + D t
      ∧ rep q.1 + D t ≤ rep q.1 - c + 1 / 4 * (1 + Real.cos (R * t + Real.pi)) + η
      ∧ -2 / 3 < rep q.1 + D t ∧ rep q.1 + D t < 1 / 3 := by
    intro t hst htT
    have hs := abs_le.1 (hD t hst htT)
    have hc1 := Real.cos_le_one (R * t)
    have hc2 := Real.neg_one_le_cos (R * t)
    rw [Real.cos_add_pi]
    refine ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨hR, by linarith, by linarith, lt_min (by norm_num) (by linarith), min_le_left _ _,
    ?_, ?_, ?_, ?_⟩
  · intro t hst htT hcos
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    rw [hcos] at hlo hhi
    show (γ t).2 ∈ readyArc 2
    rcases le_total 1 (-2 / 3 - 4 * (rep q.1 - c)) with hk | hk
    · rw [min_eq_left hk] at hlo hhi
      rw [hγ t hst htT, pshift_mem_readyArc_iff (by linarith) (by linarith)]
      linarith
    · rw [min_eq_right hk] at hlo hhi
      rw [hγ t hst htT, pshift_mem_readyArc_iff (by linarith) (by linarith)]
      linarith
  · intro t hst htT hcos
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    show (γ t).2 ∈ displayArc
    rw [hγ t hst htT, pshift_mem_displayArc_iff_of_nonpos hm (by linarith)]
    linarith
  · intro t hst htT hr
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    have hr' : (γ t).2 ∈ readyArc 2 := hr
    rw [hγ t hst htT] at hr'
    rcases lt_or_ge 0 (rep q.1 + D t) with hpos | hneg
    · linarith
    · exact absurd hr' (pshift_notMem_readyArc_of_nonpos (by linarith) hneg)
  · intro t hst htT hd
    obtain ⟨hlo, hhi, hm, hM⟩ := key t hst htT
    have hd' : (γ t).2 ∈ displayArc := hd
    rw [hγ t hst htT] at hd'
    rcases lt_or_ge 0 (rep q.1 + D t) with hpos | hneg
    · rw [pshift_mem_displayArc_iff hpos (by linarith)] at hd'
      linarith
    · rw [pshift_mem_displayArc_iff_of_nonpos hm hneg] at hd'
      linarith

/-- ★★★ **The count of an offset swing over a window.** A last pointer whose displacement on
`[s, T]` is within `η < 1/12` of `(1/4)(1 − cos R t) − c`, with the lower turning point
`p = θ₁ − c` in `(−1/6 + η, 1/6 − η]` or in `(−1/2 + η, −1/6 − η)`: if its count is `N_s` at
`s` it has a count `N_T` at `T`, and `|2π (N_T − N_s) − R (T − s)| ≤ 6π`. -/
theorem offset_swing_count {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ} {R c η s T : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hη1 : η < 1 / 12) (hs0 : 0 ≤ s) (hsT : s ≤ T)
    (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hD : ∀ t, s ≤ t → t ≤ T → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η)
    (hband : (-1 / 6 + η < rep q.1 - c ∧ rep q.1 - c ≤ 1 / 6 - η)
      ∨ (-1 / 2 + η < rep q.1 - c ∧ rep q.1 - c < -1 / 6 - η)) {Ns : ℕ}
    (hNs : IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
      {x : Y × KTorus | x.2 ∈ displayArc} γ s Ns) :
    ∃ NT : ℕ, IsTickCount {x : Y × KTorus | x.2 ∈ readyArc 2}
        {x : Y × KTorus | x.2 ∈ displayArc} γ T NT
      ∧ |((NT : ℝ) - Ns) * (2 * Real.pi) - R * (T - s)| ≤ 3 * (2 * Real.pi) := by
  rcases hband with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hsw := isWindowSwing_snd_high hR hη hη1 hγ hD h₁ h₂
    obtain ⟨NT, hNT⟩ := hsw.exists_tickCount hsT hNs
    exact ⟨NT, hNT, hsw.abs_count_sub_le hs0 hsT hNs hNT⟩
  · have hsw := isWindowSwing_snd_low hR hη hη1 hγ hD h₁ h₂
    obtain ⟨NT, hNT⟩ := hsw.exists_tickCount hsT hNs
    exact ⟨NT, hNT, hsw.abs_count_sub_le hs0 hsT hNs hNT⟩

/-- ★★ **The dead band: an offset swing that never rests.** A last pointer whose displacement
on `[s, T]` is within `η` of `(1/4)(1 − cos R t) − c`, with the lower turning point
`p = θ₁ − c` in `(1/6 + η, 1/2 − η]`: it is never in the ready arc on the window, so a history
without `N₀ + 1` ticks by `s` has at most `N₀ + 1` ticks by `T`, however far the phase
advances. -/
theorem offset_swing_dead {γ : ℝ → Y × KTorus} {q : KTorus} {D : ℝ → ℝ} {R c η s T : ℝ}
    (hγ : ∀ t, s ≤ t → t ≤ T → (γ t).2 = pshift (D t) q)
    (hD : ∀ t, s ≤ t → t ≤ T → |D t - (1 / 4 * (1 - Real.cos (R * t)) - c)| ≤ η)
    (h₁ : 1 / 6 + η < rep q.1 - c) (h₂ : rep q.1 - c ≤ 1 / 2 - η) {m N₀ : ℕ}
    (hm : HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
      γ T m)
    (hN : ¬ HasTicks {x : Y × KTorus | x.2 ∈ readyArc 2} {x : Y × KTorus | x.2 ∈ displayArc}
      γ s (N₀ + 1)) : m ≤ N₀ + 1 := by
  refine hasTicks_le_succ_of_no_passage (fun a b hsa hab hbT hr => ?_) hm hN
  exfalso
  have hs := abs_le.1 (hD a hsa (hab.trans hbT))
  have hc1 := Real.cos_le_one (R * a)
  have hc2 := Real.neg_one_le_cos (R * a)
  have hr' : (γ a).2 ∈ readyArc 2 := hr
  rw [hγ a hsa (hab.trans hbT),
    pshift_mem_readyArc_iff (by linarith [hs.1]) (by linarith [hs.2])] at hr'
  linarith [hs.1]

end Pointer

end CSD.RecordLayer

end
