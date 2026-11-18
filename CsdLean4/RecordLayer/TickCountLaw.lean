/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedDiracClockTicks

/-!
# The law of a tick count for a pointer that only advances

**Category:** 7-SigmaLayer. BACKLOG #441, first brick (Task 6 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (6); plan `specs/unified-records-spacetime-task-plans.md` §4).

A click of a threshold pointer has a probability that is linear in the accumulated weight up
to a cut-off and then constant (`RecordLayer/DiracPointerClick.lean`). A tick count is not a
click. Here the count is computed exactly for a pointer whose angle only advances, and then
averaged over where the pointer starts.

## On the line

* `periodicArc`, `tickIndices`, `mem_tickIndices`, `card_tickIndices`;
* `exists_time_eq`, `lt_of_lt_of_monotoneOn`, ★★ `hasTicks_of_le_card`, ★★ `le_card_of_hasTicks`;
* ★★★ `isTickCount_line` — for a lifted angle that is continuous and non-decreasing from `x₀`
  to `x₀ + Δ`, a resting arc `(r₁, r₂]` and a displaying arc `(p₁, p₂]` in cyclic order, the
  count is the number of integers `k` with `x₀ ≤ r₂ + k` and `p₁ + k < x₀ + Δ`.

## The mean over the starting angle

* `integral_ceil_add_sub_ceil_add`;
* ★★★ `integral_card_tickIndices` — **the count averaged over a starting angle uniform on one
  turn is `Δ − (p₁ − r₂)`**, for `Δ` at least the gap `p₁ − r₂`.

## The pointer's arcs

* `coe_intCast_circleFibre`, ★ `rep_add_coe_mem_Ioc_iff`, `hasTicks_congr`;
* ★★★ `isTickCount_pointer` — the count for the ready arc `(0, 1/6]` and the displaying arc
  `(1/3, 5/6]` of a pointer read through any projection, turned by a non-decreasing `D`;
* ★★★ `integral_card_tickIndices_pointer` — its mean over the starting angle is `D(T) − 1/6`.

## What it says

The mean count is **linear in the displacement, with a dead zone of one gap and no upper
cut-off**. The click probability saturates because it asks only whether the count is at
least one. The displacement of a pointer coupled to an observable `G` with strength `z` is
`−2 z ∫₀ᵀ ⟨G⟩` along the orbit, so for an observable of one sign the mean count is that
accumulated expectation less `1/6`.

## Honest scope

⚠️ **Not yet a statement about Born weights.** No weight, preparation or observable appears.
That the displacement of a pointer of the arena is the accumulated expectation of its
observable, monotone for an observable of one sign, and equal to `2 |z| w T` for a weight `w`
that is constant over the window, is not shown here. Until it is, this is the law of a
count given a displacement, not a bridge.

⚠️ **The mean, not the distribution's relation to a weight.** The count takes two adjacent
values; only its mean is linear. A single run's count is not the weight.

⚠️ **Uniform starting angle, as an integral over the representative.** The average is
`∫₀¹ … dx₀` over the starting angle's representative. It is not stated as an integral against
the arena's measure `μ_FS ⊗ vol⁵`, and the pointer's conserved angle is held fixed.

⚠️ **Only for a pointer that never turns back.** The clocks' pointers of the radar swing
(their observable is a level swap, of both signs), and this law does not apply to them. It
applies to a pointer coupled to a projector.

References: `specs/BACKLOG.md` #441; `specs/unified-record-spacetime-plan.md` (UO-25, UD-50 to
UD-52, UD-208, UD-229); `specs/unified-records-spacetime-task-plans.md` (§4);
`RecordLayer/UnifiedDiracClockTicks.lean` (`HasTicks`, `IsTickCount`);
`RecordLayer/DiracPointerClick.lean` (`diracClickProb_eq_lintegral`);
`RecordLayer/UnifiedRadarSkeleton.lean` (`IsGatedHistory.exists_count`);
`RecordLayer/CircleFibre.lean` (`rep`, `rep_coe_of_mem_Ioc`); `LF4/PentaPointerInert.lean`
(`fiveCoupledFlow_shiftPenta`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace CSD.RecordLayer

/-- **An arc repeated with period one**: the reals `y` with `y − k ∈ (c, d]` for an integer
`k`. The lift to the line of an arc `(c, d]` of a circle of length one. -/
def periodicArc (c d : ℝ) : Set ℝ := {y | ∃ k : ℤ, y - k ∈ Ioc c d}

/-- **The turns that give a tick**: the integers `k` for which a path from `x₀` to `x₀ + Δ`
meets the resting arc ending at `r₂ + k` and then the displaying arc starting at `p₁ + k`. -/
def tickIndices (r2 p1 x₀ Δ : ℝ) : Finset ℤ := Finset.Ico ⌈x₀ - r2⌉ ⌈x₀ + Δ - p1⌉

theorem mem_tickIndices {r2 p1 x₀ Δ : ℝ} {k : ℤ} :
    k ∈ tickIndices r2 p1 x₀ Δ ↔ x₀ ≤ r2 + k ∧ p1 + k < x₀ + Δ := by
  rw [tickIndices, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem card_tickIndices (r2 p1 x₀ Δ : ℝ) :
    (tickIndices r2 p1 x₀ Δ).card = (⌈x₀ + Δ - p1⌉ - ⌈x₀ - r2⌉).toNat :=
  Int.card_Ico _ _

section Path

variable {x : ℝ → ℝ} {T x₀ Δ r1 r2 p1 p2 : ℝ}

/-- A path that only advances reaches every value between its ends. -/
theorem exists_time_eq (hx : ContinuousOn x (Icc 0 T)) (hT : 0 ≤ T) (h0 : x 0 = x₀)
    (hTΔ : x T = x₀ + Δ) {y : ℝ} (hy1 : x₀ ≤ y) (hy2 : y ≤ x₀ + Δ) :
    ∃ t ∈ Icc (0 : ℝ) T, x t = y := by
  have h := intermediate_value_Icc hT hx
  rw [h0, hTΔ] at h
  obtain ⟨t, ht, rfl⟩ := h ⟨hy1, hy2⟩
  exact ⟨t, ht, rfl⟩

/-- On a path that only advances, a smaller value is taken earlier. -/
theorem lt_of_lt_of_monotoneOn (hm : MonotoneOn x (Icc 0 T)) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (ht : t ∈ Icc (0 : ℝ) T) (h : x s < x t) : s < t := by
  by_contra hne
  exact absurd (hm ht hs (not_lt.1 hne)) (not_le.2 h)

/-- ★★ **Enough turns give the ticks.** -/
theorem hasTicks_of_le_card (hx : ContinuousOn x (Icc 0 T)) (hm : MonotoneOn x (Icc 0 T))
    (hT : 0 ≤ T) (h0 : x 0 = x₀) (hTΔ : x T = x₀ + Δ) (h12 : r1 < r2) (h2p : r2 ≤ p1)
    (hp : p1 < p2) (hp1 : p2 ≤ r1 + 1) {n : ℕ} (hn : n ≤ (tickIndices r2 p1 x₀ Δ).card) :
    HasTicks (periodicArc r1 r2) (periodicArc p1 p2) x T n := by
  have hΔ : 0 ≤ Δ := by
    have := hm (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
    rw [h0, hTΔ] at this
    linarith only [this]
  have hk : ∀ i : ℕ, i < n → x₀ ≤ r2 + ((⌈x₀ - r2⌉ + (i : ℤ) : ℤ) : ℝ)
      ∧ p1 + ((⌈x₀ - r2⌉ + (i : ℤ) : ℤ) : ℝ) < x₀ + Δ := by
    intro i hi
    refine mem_tickIndices.1 ?_
    rw [card_tickIndices] at hn
    rw [tickIndices, Finset.mem_Ico]
    omega
  have ha : ∀ i : ℕ, i < n → ∃ t ∈ Icc (0 : ℝ) T,
      x t = r2 + ((⌈x₀ - r2⌉ + (i : ℤ) : ℤ) : ℝ) := fun i hi =>
    exists_time_eq hx hT h0 hTΔ (hk i hi).1 (by linarith only [(hk i hi).2, h2p])
  have hb : ∀ i : ℕ, i < n → ∃ t ∈ Icc (0 : ℝ) T,
      x t = min (p2 + ((⌈x₀ - r2⌉ + (i : ℤ) : ℤ) : ℝ)) (x₀ + Δ) := fun i hi =>
    exists_time_eq hx hT h0 hTΔ
      (le_min (by linarith only [(hk i hi).1, h2p, hp]) (by linarith only [hΔ]))
      (min_le_right _ _)
  choose! a ha1 ha2 using ha
  choose! b hb1 hb2 using hb
  refine ⟨a, b, fun i hi => ⟨(ha1 i hi).1, ?_, (hb1 i hi).2, ?_, ?_⟩, fun i hi => ?_⟩
  · refine lt_of_lt_of_monotoneOn hm (ha1 i hi) (hb1 i hi) ?_
    rw [ha2 i hi, hb2 i hi]
    exact lt_min (by linarith only [h2p, hp]) (by linarith only [(hk i hi).2, h2p])
  · refine ⟨⌈x₀ - r2⌉ + (i : ℤ), ?_⟩
    rw [ha2 i hi, add_sub_cancel_right]
    exact ⟨h12, le_rfl⟩
  · refine ⟨⌈x₀ - r2⌉ + (i : ℤ), ?_⟩
    rw [hb2 i hi]
    constructor
    · rw [lt_sub_iff_add_lt]
      exact lt_min (by linarith only [hp]) (hk i hi).2
    · rw [sub_le_iff_le_add]
      exact min_le_left _ _
  · have hi' : i < n := Nat.lt_of_succ_lt hi
    refine lt_of_lt_of_monotoneOn hm (hb1 i hi') (ha1 (i + 1) hi) ?_
    rw [hb2 i hi', ha2 (i + 1) hi]
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    push_cast
    linarith only [hp1, h12]

/-- ★★ **The ticks need that many turns.** -/
theorem le_card_of_hasTicks (hm : MonotoneOn x (Icc 0 T)) (hT : 0 ≤ T) (h0 : x 0 = x₀)
    (hTΔ : x T = x₀ + Δ) (h2p : r2 ≤ p1) (hp1 : p2 ≤ r1 + 1) {n : ℕ}
    (h : HasTicks (periodicArc r1 r2) (periodicArc p1 p2) x T n) :
    n ≤ (tickIndices r2 p1 x₀ Δ).card := by
  obtain ⟨a, b, h1, h2⟩ := h
  have hmem : ∀ i : ℕ, i < n → a i ∈ Icc (0 : ℝ) T ∧ b i ∈ Icc (0 : ℝ) T := fun i hi => by
    obtain ⟨ha, hab, hb, -, -⟩ := h1 i hi
    exact ⟨⟨ha, hab.le.trans hb⟩, ⟨ha.trans hab.le, hb⟩⟩
  have hjk : ∀ i : ℕ, i < n → ∃ j k : ℤ, x (a i) - j ∈ Ioc r1 r2 ∧ x (b i) - k ∈ Ioc p1 p2 :=
    fun i hi => by
      obtain ⟨-, -, -, ⟨j, hj⟩, ⟨k, hk⟩⟩ := h1 i hi
      exact ⟨j, k, hj, hk⟩
  choose! j k hjk using hjk
  have hxa : ∀ i : ℕ, i < n → x₀ ≤ x (a i) := fun i hi => by
    have := hm (left_mem_Icc.2 hT) (hmem i hi).1 (hmem i hi).1.1
    rwa [h0] at this
  have hxab : ∀ i : ℕ, i < n → x (a i) ≤ x (b i) := fun i hi =>
    hm (hmem i hi).1 (hmem i hi).2 (h1 i hi).2.1.le
  have hxb : ∀ i : ℕ, i < n → x (b i) ≤ x₀ + Δ := fun i hi => by
    have := hm (hmem i hi).2 (right_mem_Icc.2 hT) (hmem i hi).2.2
    rwa [hTΔ] at this
  have hjle : ∀ i : ℕ, i < n → j i ≤ k i := fun i hi => by
    obtain ⟨⟨hj1, -⟩, ⟨-, hk2⟩⟩ := hjk i hi
    have h3 : ((j i : ℤ) : ℝ) < ((k i + 1 : ℤ) : ℝ) := by
      push_cast
      linarith only [hj1, hk2, hxab i hi, hp1]
    exact Int.lt_add_one_iff.1 (by exact_mod_cast h3)
  have hin : ∀ i ∈ Finset.range n, k i ∈ tickIndices r2 p1 x₀ Δ := fun i hi => by
    have hi' := Finset.mem_range.1 hi
    obtain ⟨⟨-, hj2⟩, ⟨hk1, -⟩⟩ := hjk i hi'
    have hjk' : ((j i : ℤ) : ℝ) ≤ ((k i : ℤ) : ℝ) := by exact_mod_cast hjle i hi'
    exact mem_tickIndices.2 ⟨by linarith only [hxa i hi', hj2, hjk'],
      by linarith only [hk1, hxb i hi']⟩
  have hstep : ∀ i : ℕ, i + 1 < n → k i < k (i + 1) := fun i hi => by
    have hi' : i < n := Nat.lt_of_succ_lt hi
    obtain ⟨-, ⟨hk1, -⟩⟩ := hjk i hi'
    obtain ⟨⟨-, hj2⟩, -⟩ := hjk (i + 1) hi
    have hba : x (b i) ≤ x (a (i + 1)) := hm (hmem i hi').2 (hmem (i + 1) hi).1 (h2 i hi).le
    have h3 : ((k i : ℤ) : ℝ) < ((j (i + 1) : ℤ) : ℝ) := by
      linarith only [hk1, hba, hj2, h2p]
    exact lt_of_lt_of_le (by exact_mod_cast h3) (hjle (i + 1) hi)
  have hmono : ∀ m i : ℕ, i < m → m < n → k i < k m := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ m ih =>
      intro i hi hm'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact (ih i hlt (Nat.lt_of_succ_lt hm')).trans (hstep m hm')
      · exact hstep i hm'
  have hinj : Set.InjOn k (Finset.range n : Set ℕ) := by
    intro i hi m hm' hkm
    have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hm'' := Finset.mem_range.1 (Finset.mem_coe.1 hm')
    rcases lt_trichotomy i m with hlt | heq | hgt
    · exact absurd hkm (hmono m i hlt hm'').ne
    · exact heq
    · exact absurd hkm.symm (hmono i m hgt hi').ne
  have := Finset.card_le_card_of_injOn k hin hinj
  rwa [Finset.card_range] at this

/-- ★★★ **The count of a pointer that only advances.** Let the lifted angle `x` be continuous
and non-decreasing on `[0, T]`, from `x₀` to `x₀ + Δ`, and let the resting arc `(r₁, r₂]` and
the displaying arc `(p₁, p₂]` be in the cyclic order `r₁ < r₂ ≤ p₁ < p₂ ≤ r₁ + 1`. Then the
count at `T` is the number of integers `k` with `x₀ ≤ r₂ + k` and `p₁ + k < x₀ + Δ`. -/
theorem isTickCount_line (hx : ContinuousOn x (Icc 0 T)) (hm : MonotoneOn x (Icc 0 T))
    (hT : 0 ≤ T) (h0 : x 0 = x₀) (hTΔ : x T = x₀ + Δ) (h12 : r1 < r2) (h2p : r2 ≤ p1)
    (hp : p1 < p2) (hp1 : p2 ≤ r1 + 1) :
    IsTickCount (periodicArc r1 r2) (periodicArc p1 p2) x T (tickIndices r2 p1 x₀ Δ).card :=
  ⟨hasTicks_of_le_card hx hm hT h0 hTΔ h12 h2p hp hp1 le_rfl, fun h =>
    absurd (le_card_of_hasTicks hm hT h0 hTΔ h2p hp1 h) (Nat.not_succ_le_self _)⟩

end Path

/-! ### The mean count over the starting angle -/

/-- **The mean of a difference of ceilings over one period is the difference of the shifts.** -/
theorem integral_ceil_add_sub_ceil_add (a b : ℝ) :
    ∫ y in (0 : ℝ)..1, (((⌈y + a⌉ : ℤ) : ℝ) - ((⌈y + b⌉ : ℤ) : ℝ)) = a - b := by
  have hper : Function.Periodic (fun y : ℝ => ((⌈y⌉ : ℤ) : ℝ) - y) 1 := fun y => by
    simp only [Int.ceil_add_one, Int.cast_add, Int.cast_one]
    ring
  have hmono : ∀ c : ℝ, Monotone fun y : ℝ => ((⌈y + c⌉ : ℤ) : ℝ) := fun c y z hyz =>
    Int.cast_le.2 (Int.ceil_mono (by linarith only [hyz] : y + c ≤ z + c))
  have hint : ∀ c u v : ℝ,
      IntervalIntegrable (fun y : ℝ => ((⌈y + c⌉ : ℤ) : ℝ) - (y + c)) volume u v := fun c u v =>
    ((hmono c).intervalIntegrable).sub
      ((continuous_id.add continuous_const).intervalIntegrable _ _)
  have hshift : ∀ c : ℝ, ∫ y in (0 : ℝ)..1, (((⌈y + c⌉ : ℤ) : ℝ) - (y + c))
      = ∫ y in c..c + 1, (((⌈y⌉ : ℤ) : ℝ) - y) := fun c => by
    have := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => ((⌈y⌉ : ℤ) : ℝ) - y) c
    rw [zero_add, add_comm 1 c] at this
    exact this
  have hsplit : ∀ y : ℝ, ((⌈y + a⌉ : ℤ) : ℝ) - ((⌈y + b⌉ : ℤ) : ℝ)
      = (((⌈y + a⌉ : ℤ) : ℝ) - (y + a)) - (((⌈y + b⌉ : ℤ) : ℝ) - (y + b)) + (a - b) := fun y => by
    ring
  simp only [hsplit]
  rw [intervalIntegral.integral_add ((hint a 0 1).sub (hint b 0 1)) intervalIntegrable_const,
    intervalIntegral.integral_sub (hint a 0 1) (hint b 0 1), hshift a, hshift b,
    hper.intervalIntegral_add_eq a b, sub_self, zero_add, intervalIntegral.integral_const]
  simp

/-- ★★★ **The mean count over the starting angle is the displacement less the gap.** For a
displacement `Δ` at least the gap `p₁ − r₂` between the end of the resting arc and the start
of the displaying arc, the count of `isTickCount_line` averaged over a starting angle uniform
on one turn is `Δ − (p₁ − r₂)`. -/
theorem integral_card_tickIndices {r2 p1 Δ : ℝ} (hΔ : p1 - r2 ≤ Δ) :
    ∫ x₀ in (0 : ℝ)..1, ((tickIndices r2 p1 x₀ Δ).card : ℝ) = Δ - (p1 - r2) := by
  have hpt : ∀ x₀ : ℝ, ((tickIndices r2 p1 x₀ Δ).card : ℝ)
      = ((⌈x₀ + (Δ - p1)⌉ : ℤ) : ℝ) - ((⌈x₀ + -r2⌉ : ℤ) : ℝ) := fun x₀ => by
    have hle : ⌈x₀ - r2⌉ ≤ ⌈x₀ + Δ - p1⌉ := Int.ceil_mono (by linarith only [hΔ])
    have hnat : (((⌈x₀ + Δ - p1⌉ - ⌈x₀ - r2⌉).toNat : ℕ) : ℤ) = ⌈x₀ + Δ - p1⌉ - ⌈x₀ - r2⌉ :=
      Int.toNat_of_nonneg (sub_nonneg.2 hle)
    rw [card_tickIndices, show x₀ + (Δ - p1) = x₀ + Δ - p1 by ring,
      show x₀ + -r2 = x₀ - r2 by ring, ← Int.cast_sub, ← hnat]
    norm_cast
  simp only [hpt]
  rw [integral_ceil_add_sub_ceil_add]
  ring

/-! ### The pointer's arcs on the circle -/

/-- An integer is the zero of the circle of length one. -/
theorem coe_intCast_circleFibre (k : ℤ) : (((k : ℝ) : ℝ) : CircleFibre) = 0 := by
  have h : (k : ℝ) = k • (1 : ℝ) := by simp
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

/-- ★ **An arc of the circle, read on the line.** For an arc `(c, d]` inside `(0, 1]`, the
point `θ` turned by `a` is in the arc exactly when `rep θ + a` is in the arc repeated with
period one. -/
theorem rep_add_coe_mem_Ioc_iff (θ : CircleFibre) (a : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) :
    rep (θ + (a : CircleFibre)) ∈ Ioc c d ↔ rep θ + a ∈ periodicArc c d := by
  have hsum : θ + (a : CircleFibre) = ((rep θ + a : ℝ) : CircleFibre) := by
    rw [AddCircle.coe_add, coe_rep]
  have hrep : ∀ k : ℤ, rep θ + a - k ∈ Ioc (0 : ℝ) 1 →
      rep (θ + (a : CircleFibre)) = rep θ + a - k := fun k hk => by
    have e : ((rep θ + a - k : ℝ) : CircleFibre) = θ + (a : CircleFibre) := by
      rw [hsum, AddCircle.coe_sub, coe_intCast_circleFibre, sub_zero]
    rw [← e, rep_coe_of_mem_Ioc hk]
  constructor
  · intro h
    have h0 : rep θ + a - ((⌈rep θ + a⌉ - 1 : ℤ) : ℝ) ∈ Ioc (0 : ℝ) 1 := by
      have h1 := Int.ceil_lt_add_one (rep θ + a)
      have h2 := Int.le_ceil (rep θ + a)
      push_cast
      constructor <;> linarith only [h1, h2]
    rw [hrep _ h0] at h
    exact ⟨_, h⟩
  · rintro ⟨k, hk⟩
    rw [hrep k ⟨lt_of_le_of_lt hc hk.1, hk.2.trans hd⟩]
    exact hk

/-- The ticks of two histories whose memberships agree at every time of `[0, T]`. -/
theorem hasTicks_congr {X Y : Type*} {rest disp : Set X} {rest' disp' : Set Y} {γ : ℝ → X}
    {γ' : ℝ → Y} {T : ℝ}
    (h : ∀ t, 0 ≤ t → t ≤ T → (γ t ∈ rest ↔ γ' t ∈ rest') ∧ (γ t ∈ disp ↔ γ' t ∈ disp'))
    (n : ℕ) : HasTicks rest disp γ T n ↔ HasTicks rest' disp' γ' T n := by
  constructor
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨a, b, fun i hi => ?_, h2⟩
    obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
    exact ⟨ha, hab, hb, (h (a i) ha (hab.le.trans hb)).1.1 hr,
      (h (b i) (ha.trans hab.le) hb).2.1 hd⟩
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨a, b, fun i hi => ?_, h2⟩
    obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
    exact ⟨ha, hab, hb, (h (a i) ha (hab.le.trans hb)).1.2 hr,
      (h (b i) (ha.trans hab.le) hb).2.2 hd⟩

/-- ★★★ **The count of a pointer of the arena that only advances.** A pointer read through
`π`, started at `q`, whose angle at the time `t` is `q` turned by `D t`, with `D` continuous
and non-decreasing on `[0, T]` from `0`: its count at `T`, for the ready arc `(0, 1/6]` and
the displaying arc `(1/3, 5/6]`, is the number of integers `k` with `rep q ≤ 1/6 + k` and
`1/3 + k < rep q + D T`. -/
theorem isTickCount_pointer {X : Type*} {π : X → LF4.KTorus} {γ : ℝ → X} {q : LF4.KTorus}
    {D : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hD : ContinuousOn D (Icc 0 T))
    (hm : MonotoneOn D (Icc 0 T)) (hD0 : D 0 = 0)
    (hγ : ∀ t, 0 ≤ t → t ≤ T → π (γ t) = pshift (D t) q) :
    IsTickCount {x : X | π x ∈ readyArc 2} {x : X | π x ∈ displayArc} γ T
      (tickIndices (1 / 6) (1 / 3) (rep q.1) (D T)).card := by
  have hline := isTickCount_line (x := fun t => rep q.1 + D t) (x₀ := rep q.1) (Δ := D T)
    (r1 := 0) (r2 := 1 / 6) (p1 := 1 / 3) (p2 := 5 / 6)
    (continuousOn_const.add hD) (fun s hs t ht hst => by
      have := hm hs ht hst
      show rep q.1 + D s ≤ rep q.1 + D t
      linarith only [this]) hT
    (by rw [hD0, add_zero]) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hc : ∀ n : ℕ, HasTicks {x : X | π x ∈ readyArc 2} {x : X | π x ∈ displayArc} γ T n
      ↔ HasTicks (periodicArc 0 (1 / 6)) (periodicArc (1 / 3) (5 / 6))
        (fun t => rep q.1 + D t) T n := fun n => by
    refine hasTicks_congr (fun t ht0 htT => ?_) n
    have e := hγ t ht0 htT
    constructor
    · show π (γ t) ∈ readyArc 2 ↔ _
      rw [e]
      show rep (q.1 + ((D t : ℝ) : CircleFibre)) ∈ Ioc (0 : ℝ) (shearWidth 2) ↔ _
      rw [shearWidth_two]
      exact rep_add_coe_mem_Ioc_iff q.1 (D t) le_rfl (by norm_num)
    · show π (γ t) ∈ displayArc ↔ _
      rw [e]
      show rep (q.1 + ((D t : ℝ) : CircleFibre))
        ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) ↔ _
      rw [shearWidth_two, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
        show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num]
      exact rep_add_coe_mem_Ioc_iff q.1 (D t) (by norm_num) (by norm_num)
  exact ⟨(hc _).2 hline.1, fun h => hline.2 ((hc _).1 h)⟩

/-- ★★★ **The mean count of such a pointer over its starting angle**: for a displacement
`Δ ≥ 1/6`, the count of `isTickCount_pointer` averaged over a starting angle uniform on one
turn is `Δ − 1/6`. Linear in the displacement, with a dead zone of one gap and no upper
cut-off. -/
theorem integral_card_tickIndices_pointer {Δ : ℝ} (hΔ : 1 / 6 ≤ Δ) :
    ∫ x₀ in (0 : ℝ)..1, ((tickIndices (1 / 6) (1 / 3) x₀ Δ).card : ℝ) = Δ - 1 / 6 := by
  rw [integral_card_tickIndices (by linarith only [hΔ])]
  ring

end CSD.RecordLayer

end
