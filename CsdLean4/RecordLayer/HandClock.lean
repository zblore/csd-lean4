/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ActivatedHamiltonian
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The drift pointer as an autonomous hand clock

**Category:** 7-SigmaLayer (the record layer). BACKLOG #201 (out of #39; the author's third
operational-geometry brief, §2: make the reference clock internally driven).

#185's record clock writes its ticks by a schedule: slot `n` is written on the window `[nT, (n+1)T]`
of `t_Σ`. Here the clock is #194's activated write read differently. One carrier (message `1`,
prepared at `A`) and one pointer (at `B`, prepared in the first half-arc) are the whole device; the
carrier shuttles between the sites on its own, the pointer turns at the rate `−(2g/ħ) f'(θ₂) n_B`
**only while the carrier is at `B`**, and its lifted displacement after time `t` is
`D(t) = κ (ωt − sin ωt cos ωt)/(2ω)` with `κ = −(2g/ħ) f'(θ₂)(J/Ω)²`, `ω = Ω/ħ`: a staircase of mean
slope `κ/2` whose steps are the carrier's visits. Read in `K` equal arcs, the pointer is a hand and
each arc crossing is a tick written by the carrier itself. **The smallest finite clock whose internal
state activates its tick writes**: one carrier, one pointer, `K` arcs, against #185's `K` slot tori.

* `handCount`, `handReading`, `handArc`, ★ `handCount_eq_iff` — **the hand read in `K` arcs**: the
  tick count is the arc index of the pointer's representative, and the arcs are disjoint intervals;
  `handReady` — the preparation (first half-arc);
* `hand`, `hand_eq` — **the hand's motion** is #194's pointer, `pshift (pointerDrift κ ω t) q`;
  ★ `pointerDrift_mono` — **the hand never turns back** (the group law of the accumulated occupancy);
  `rep_hand_of_le` — no wrap below one turn;
* `tickTime` — **the derived calibration** `τ_tick = 2/(Kκ)`: the time in which the mean slope
  crosses one arc; ★ `pointerDrift_tickTime` — after `n τ_tick` the hand has crossed `n` arcs up to
  the band `κ/(4ω)`; `handHorizon` — **the horizon**, one turn: `(2/κ)(1 − 1/K) − 1/(2ω)`;
  `handHorizon_pos`;
* ★★ `handCount_mono` — **ticks persist**: the count is non-decreasing over the horizon;
  ★★ `abs_handReading_sub_le` — **the resolution bound** `|handReading − t| ≤ τ_tick + 1/(2ω)` over
  the horizon: one arc of count uncertainty plus the band of the staircase about its mean;
* `tickStart`, `tickEnd`, `tickWindow`; ★★ `hand_before_tick`, `hand_at_tick` — **tick `n` is a
  write**: before `(2n−1)/(2Kκ)` the count is below `n`, and on
  `[n τ_tick + 1/(2ω), n τ_tick + 1/(2ω) + (τ_tick/2 − 1/ω)]` it is exactly `n`, under the slowness
  `Kκ ≤ ω` (the hand gains at most one arc per Rabi radian); ★★★ `tickWrite` — **each tick as an
  `ActualOccurrence`** (#191) at site `{B}`, from the start `0`, value `n`, for `1 ≤ n ≤ K − 1`;
  `tickWrite_value_ne` — **successive ticks are distinguishable**; `tickEnd_succ` — they are spaced by
  `τ_tick`; ★ `handTick_persists` — once written, the count never drops below `n` over the horizon;
* ★ `handClock_generated` — **generation inherited from #195**: the clock's dynamics is the flow of
  the activated energy on the arena, no new geometry;
* ★★★ `hand_clock` — the package.

## Honest scope

* The controller is explicit and in the model: the carrier of message `1`, with its back-reaction
  (the detuning `g f(θ₂)`) on the hand's own dynamics. There is no schedule anywhere; the only
  parameter is the time `t` at which the arena is inspected.
* The hand is a staircase, not a uniform rotation: it moves while the carrier is at `B` and is
  nearly still while the carrier is at `A` (the loss `1 − (J/Ω)²` keeps it from stopping exactly).
  The resolution bound pays for this with the band `1/(2ω)`, which is the clock's intrinsic jitter
  — half a Rabi radian.
* Over one turn only; wrapping is the horizon. A clock that counts turns is a further register.
* The preparation is the first half-arc, finer than #194's ready arc: the record windows need the
  preparation width below the arc width, as #194's analysis showed.

References: `specs/BACKLOG.md` #201, #194, #195, #185, #202, #39; `RecordLayer/ActivatedWrite.lean`
(`activeFlow`, `pointerDrift`, `driftRate`, `pointerDrift_lower`, `pointerDrift_upper`,
`pointerAmount_add`), `RecordLayer/ActivatedHamiltonian.lean` (`hamiltonianFlow_activeFlow`),
`RecordLayer/RecordClock.lean` (the scheduled clock this replaces), `RecordLayer/RecordOccurrence.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The hand read in `K` arcs -/

/-- **The tick count**: the arc index of the pointer's representative among `K` equal arcs
`(n/K, (n+1)/K]`. -/
noncomputable def handCount (K : ℕ) (q : LF4.KTorus) : ℕ := ⌈(K : ℝ) * rep q.1⌉₊ - 1

theorem measurable_handCount (K : ℕ) : Measurable (handCount K) := by
  show Measurable fun q : LF4.KTorus => ⌈(K : ℝ) * rep q.1⌉₊ - 1
  exact (measurable_from_top (f := fun n : ℕ => n - 1)).comp
    (Measurable.comp Nat.measurable_ceil ((measurable_rep.comp measurable_fst).const_mul (K : ℝ)))

/-- The clock reading: the tick count times the calibration. -/
noncomputable def handReading (K : ℕ) (τ : ℝ) (q : LF4.KTorus) : ℝ := (handCount K q : ℝ) * τ

/-- The arc displaying count `n`. -/
def handArc (K n : ℕ) : Set LF4.KTorus := {q | handCount K q = n}

theorem handArc_disjoint (K : ℕ) {n m : ℕ} (h : n ≠ m) : Disjoint (handArc K n) (handArc K m) :=
  Set.disjoint_left.mpr fun _ hn hm => h (hn.symm.trans hm)

/-- ★ **The arcs are intervals**: `handCount q = n` iff `rep q ∈ (n/K, (n+1)/K]`. -/
theorem handCount_eq_iff {K : ℕ} (hK : 0 < K) (q : LF4.KTorus) (n : ℕ) :
    handCount K q = n ↔ rep q.1 ∈ Ioc ((n : ℝ) / K) ((n + 1 : ℝ) / K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < (K : ℝ) * rep q.1 := mul_pos hKr (rep_mem_Ioc q.1).1
  have h1 : 1 ≤ ⌈(K : ℝ) * rep q.1⌉₊ := Nat.one_le_ceil_iff.2 hpos
  unfold handCount
  rw [Nat.sub_eq_iff_eq_add h1, Nat.ceil_eq_iff (Nat.succ_ne_zero n), Nat.succ_sub_one,
    Nat.cast_succ, mem_Ioc, div_lt_iff₀ hKr, le_div_iff₀ hKr, mul_comm (rep q.1) (K : ℝ)]

/-- The hand's preparation: the first half-arc. -/
def handReady (K : ℕ) : Set LF4.KTorus := {q | rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ)))}

theorem measurableSet_handReady (K : ℕ) : MeasurableSet (handReady K) :=
  (measurable_rep.comp measurable_fst) measurableSet_Ioc

/-! ### The hand's motion -/

section Hand

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- The hand's mean rate `κ = −(2g/ħ) f'(θ₂) (J/Ω)²`. -/
noncomputable def handRate (q : LF4.KTorus) : ℝ := driftRate J ħ g hf q.2

/-- The hand's Rabi rate `ω = Ω/ħ`. -/
noncomputable def handFreq (q : LF4.KTorus) : ℝ := rabiRate J ħ (detuningAt g hf q.2)

/-- **The hand**: the pointer of #194's activated write with the carrier prepared as message `1`. -/
noncomputable def hand (t : ℝ) (q : LF4.KTorus) : LF4.KTorus :=
  (activeFlow J ħ g hf t (msgPoint 1, q)).2

theorem handFreq_pos (hJ : 0 < J) (hħ : 0 < ħ) (q : LF4.KTorus) : 0 < handFreq J ħ g hf q :=
  rabiRate_pos hJ hħ _

/-- The hand's motion in closed form: the drift `κ (ωt − sin ωt cos ωt)/(2ω)`. -/
theorem hand_eq (hJ : 0 < J) (hħ : 0 < ħ) (t : ℝ) (q : LF4.KTorus) :
    hand J ħ g hf t q = pshift (pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t) q :=
  activeFlow_msgPoint_one_snd J ħ g hf hJ hħ q t

theorem hand_zero (q : LF4.KTorus) : hand J ħ g hf 0 q = q := by
  unfold hand
  rw [activeFlow_zero]
  rfl

/-- The pointer's own rate is positive when the mean rate is. -/
theorem rateAt_pos_of_handRate_pos (hJ : 0 < J) {q : LF4.KTorus} (hκ : 0 < handRate J ħ g hf q) :
    0 < rateAt g ħ hf q.2 := by
  unfold handRate driftRate at hκ
  exact (mul_pos_iff_of_pos_right (div_rabiFreq_sq_pos hJ _)).1 hκ

/-- ★ **The hand never turns back**: the drift is non-decreasing, by the group law of the
accumulated occupancy. -/
theorem pointerDrift_mono (hJ : 0 < J) (hħ : 0 < ħ) {q : LF4.KTorus} (hκ : 0 < handRate J ħ g hf q)
    {s t : ℝ} (hst : s ≤ t) :
    pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) s
      ≤ pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t := by
  have h := pointerAmount_add J ħ g hf s (t - s) (msgPoint 1, q)
  have hts : s + (t - s) = t := by ring
  rw [hts, pointerAmount_msgPoint_one J ħ g hf hJ hħ, pointerAmount_msgPoint_one J ħ g hf hJ hħ] at h
  have hnn : 0 ≤ pointerAmount J ħ g hf (t - s) (activeFlow J ħ g hf s (msgPoint 1, q)) := by
    unfold pointerAmount
    rw [activeFlow_angle]
    exact mul_nonneg (rateAt_pos_of_handRate_pos J ħ g hf hJ hκ).le
      (occAccum_nonneg _ _ _ _ (by linarith))
  unfold handRate handFreq
  linarith

/-- No wrap: below one turn the representative of the hand is the prepared representative plus the
drift. -/
theorem rep_hand_of_le (hJ : 0 < J) (hħ : 0 < ħ) {q : LF4.KTorus} (hq0 : 0 < rep q.1) {t : ℝ}
    (hD : 0 ≤ pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t)
    (h : rep q.1 + pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t ≤ 1) :
    rep (hand J ħ g hf t q).1
      = rep q.1 + pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t := by
  rw [hand_eq J ħ g hf hJ hħ]
  exact rep_pshift_of_mem _ _ ⟨by linarith, h⟩

end Hand

/-! ### Calibration and horizon -/

/-- **The derived calibration**: the time `τ_tick = 2/(Kκ)` in which the mean slope `κ/2` crosses
one arc `1/K`. -/
noncomputable def tickTime (K : ℕ) (κ : ℝ) : ℝ := 2 / (K * κ)

/-- **The horizon**: one turn, `(2/κ)(1 − 1/K) − 1/(2ω)`. -/
noncomputable def handHorizon (K : ℕ) (κ ω : ℝ) : ℝ := (2 / κ) * (1 - 1 / K) - 1 / (2 * ω)

theorem tickTime_pos {K : ℕ} (hK : 0 < K) {κ : ℝ} (hκ : 0 < κ) : 0 < tickTime K κ := by
  unfold tickTime
  have : (0 : ℝ) < K := by exact_mod_cast hK
  positivity

theorem mul_tickTime {K : ℕ} (hK : 0 < K) {κ : ℝ} (hκ : 0 < κ) : K * κ * tickTime K κ = 2 := by
  unfold tickTime
  have : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp

/-- A hand slower than its Rabi rate has a positive horizon once `K ≥ 2`. -/
theorem handHorizon_pos {K : ℕ} (hK : 2 ≤ K) {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (hslow : κ ≤ ω) :
    0 < handHorizon K κ ω := by
  unfold handHorizon
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : 1 / (K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : 1 / (2 * ω) < 1 / κ := by
    rw [div_lt_div_iff₀ (by positivity) hκ]
    linarith
  have h3 : 1 / κ ≤ (2 / κ) * (1 - 1 / K) := by
    rw [show (1 : ℝ) / κ = (2 / κ) * (1 / 2) by field_simp]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- At the horizon the upper band reaches `1 − 1/K`. -/
theorem band_at_handHorizon {K : ℕ} {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) :
    κ * (handHorizon K κ ω / 2 + 1 / (4 * ω)) = 1 - 1 / K := by
  unfold handHorizon
  field_simp
  ring

/-- ★ **The calibration is derived**: after `n` tick times the hand has crossed `n` arcs, up to the
band `κ/(4ω)`. -/
theorem pointerDrift_tickTime {K : ℕ} (hK : 0 < K) {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (n : ℕ) :
    (n : ℝ) / K - κ / (4 * ω) ≤ pointerDrift κ ω (n * tickTime K κ)
      ∧ pointerDrift κ ω (n * tickTime K κ) ≤ (n : ℝ) / K + κ / (4 * ω) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hl := pointerDrift_lower hκ.le hω (n * tickTime K κ)
  have hu := pointerDrift_upper hκ.le hω (n * tickTime K κ)
  have e : κ * (n * tickTime K κ / 2) = (n : ℝ) / K := by
    unfold tickTime
    field_simp
  constructor
  · calc (n : ℝ) / K - κ / (4 * ω) = κ * (n * tickTime K κ / 2 - 1 / (4 * ω)) := by rw [mul_sub, e]; ring
      _ ≤ _ := hl
  · calc pointerDrift κ ω (n * tickTime K κ) ≤ κ * (n * tickTime K κ / 2 + 1 / (4 * ω)) := hu
      _ = (n : ℝ) / K + κ / (4 * ω) := by rw [mul_add, e]; ring

/-! ### Persistence and resolution -/

section Reading

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- Over the horizon the hand has not wrapped. -/
theorem rep_hand (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    rep (hand J ħ g hf t q).1
      = rep q.1 + pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t := by
  have hω := handFreq_pos J ħ g hf hJ hħ q
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hhalf : 1 / (2 * (K : ℝ)) ≤ 1 / K := by
    rw [div_le_div_iff₀ (by positivity) hKr]
    linarith
  have hu := pointerDrift_upper hκ.le hω t
  have hb := band_at_handHorizon (K := K) hκ hω
  have hD : pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t ≤ 1 - 1 / K := by
    rw [← hb]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith) hκ.le)
  exact rep_hand_of_le J ħ g hf hJ hħ hr.1 (pointerDrift_nonneg hκ.le hω ht0)
    (by linarith [hr.2])

/-- ★★ **Ticks persist**: over the horizon the count never decreases. -/
theorem handCount_mono (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    handCount K (hand J ħ g hf s q) ≤ handCount K (hand J ħ g hf t q) := by
  unfold handCount
  rw [rep_hand J ħ g hf hJ hħ hK hq hκ hs (by linarith), rep_hand J ħ g hf hJ hħ hK hq hκ
    (by linarith) ht]
  exact Nat.sub_le_sub_right (Nat.ceil_mono (mul_le_mul_of_nonneg_left
    (by linarith [pointerDrift_mono J ħ g hf hJ hħ hκ hst]) (Nat.cast_nonneg K))) 1

/-- The count is within one of `K` times the drift (the preparation lies in the first half-arc). -/
theorem abs_handCount_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |(handCount K (hand J ħ g hf t q) : ℝ)
        - K * pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t| ≤ 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hKhalf : (K : ℝ) * rep q.1 ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hr.2 hKr.le
    rwa [show (K : ℝ) * (1 / (2 * K)) = 1 / 2 by field_simp] at this
  set D := pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t with hDdef
  have hD0 : 0 ≤ D := pointerDrift_nonneg hκ.le (handFreq_pos J ħ g hf hJ hħ q) ht0
  unfold handCount
  rw [rep_hand J ħ g hf hJ hħ hK hq hκ ht0 ht]
  set y := (K : ℝ) * (rep q.1 + D) with hy
  have hy0 : 0 < y := by rw [hy]; exact mul_pos hKr (by linarith [hr.1])
  have h1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_ceil_iff.2 hy0
  have hle := Nat.le_ceil y
  have hlt := Nat.ceil_lt_add_one hy0.le
  rw [Nat.cast_sub h1, Nat.cast_one, abs_le]
  have hyD : y = K * rep q.1 + K * D := by rw [hy]; ring
  constructor <;> nlinarith [mul_pos hKr hr.1]

/-- ★★ **The resolution bound**: calibrated with `τ_tick = 2/(Kκ)`, the hand reads within
`τ_tick + 1/(2ω)` of `t` over the horizon — one arc of count uncertainty plus the staircase's band
about its mean. -/
theorem abs_handReading_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf t q) - t|
      ≤ tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q) := by
  set κ := handRate J ħ g hf q with hκdef
  set ω := handFreq J ħ g hf q with hωdef
  have hω : 0 < ω := handFreq_pos J ħ g hf hJ hħ q
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set τ := tickTime K κ with hτ
  have hτ0 : 0 < τ := tickTime_pos hK hκ
  set D := pointerDrift κ ω t with hD
  set c := (handCount K (hand J ħ g hf t q) : ℝ) with hc
  have h1 : |c - K * D| ≤ 1 := abs_handCount_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht
  have h2 : |D - κ * t / 2| ≤ κ / (4 * ω) := by
    have hl := pointerDrift_lower hκ.le hω t
    have hu := pointerDrift_upper hκ.le hω t
    rw [← hD] at hl hu
    have e1 : κ * (t / 2 - 1 / (4 * ω)) = κ * t / 2 - κ / (4 * ω) := by ring
    have e2 : κ * (t / 2 + 1 / (4 * ω)) = κ * t / 2 + κ / (4 * ω) := by ring
    rw [e1] at hl
    rw [e2] at hu
    rw [abs_le]
    constructor <;> linarith
  have hτK : τ * K * κ = 2 := by rw [hτ, ← mul_tickTime hK hκ]; ring
  have e : handReading K τ (hand J ħ g hf t q) - t = τ * (c - K * D) + τ * K * (D - κ * t / 2) := by
    unfold handReading
    rw [← hc]
    linear_combination (t / 2) * hτK
  rw [e]
  calc |τ * (c - K * D) + τ * K * (D - κ * t / 2)|
      ≤ |τ * (c - K * D)| + |τ * K * (D - κ * t / 2)| := abs_add_le _ _
    _ = τ * |c - K * D| + τ * K * |D - κ * t / 2| := by
        rw [abs_mul, abs_mul, abs_of_pos hτ0, abs_of_pos (mul_pos hτ0 hKr)]
    _ ≤ τ * 1 + τ * K * (κ / (4 * ω)) := by gcongr
    _ = τ + 1 / (2 * ω) := by
        rw [mul_one]
        congr 1
        rw [hτ]
        unfold tickTime
        field_simp
        ring

end Reading

/-! ### Each tick as a write -/

/-- Tick `n` cannot have been written before `(2n − 1)/(2Kκ)`. -/
noncomputable def tickStart (K : ℕ) (κ : ℝ) (n : ℕ) : ℝ := (2 * n - 1) / (2 * K * κ)

/-- Tick `n` is written by `n τ_tick + 1/(2ω)`. -/
noncomputable def tickEnd (K : ℕ) (κ ω : ℝ) (n : ℕ) : ℝ := n * tickTime K κ + 1 / (2 * ω)

/-- The window on which tick `n` displays: `τ_tick/2 − 1/ω`. -/
noncomputable def tickWindow (K : ℕ) (κ ω : ℝ) : ℝ := tickTime K κ / 2 - 1 / ω

theorem tickEnd_succ (K : ℕ) (κ ω : ℝ) (n : ℕ) :
    tickEnd K κ ω (n + 1) = tickEnd K κ ω n + tickTime K κ := by
  unfold tickEnd
  push_cast
  ring

theorem tickStart_nonneg {K : ℕ} (hK : 0 < K) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ tickStart K κ n := by
  unfold tickStart
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (by positivity)

theorem tickStart_le_tickEnd {K : ℕ} (hK : 0 < K) {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (n : ℕ) :
    tickStart K κ n ≤ tickEnd K κ ω n := by
  unfold tickStart tickEnd tickTime
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : (2 * n - 1) / (2 * K * κ) ≤ n * (2 / (K * κ)) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e : (n : ℝ) * (2 / (K * κ)) = (4 * n) / (2 * K * κ) := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : 0 ≤ 1 / (2 * ω) := by positivity
  linarith

/-- The window is a window exactly when the hand gains at most one arc per Rabi radian: `Kκ ≤ ω`. -/
theorem tickWindow_nonneg {K : ℕ} (hK : 0 < K) {κ ω : ℝ} (hκ : 0 < κ) (hslow : K * κ ≤ ω) :
    0 ≤ tickWindow K κ ω := by
  unfold tickWindow tickTime
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKκ : 0 < (K : ℝ) * κ := mul_pos hKr hκ
  have h : 1 / ω ≤ 1 / ((K : ℝ) * κ) := one_div_le_one_div_of_le hKκ hslow
  have e : 2 / ((K : ℝ) * κ) / 2 = 1 / (K * κ) := by field_simp
  rw [e]
  linarith

theorem band_at_tickEnd {K : ℕ} (hK : 0 < K) {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (n : ℕ) :
    κ * (tickEnd K κ ω n / 2 - 1 / (4 * ω)) = (n : ℝ) / K := by
  unfold tickEnd tickTime
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp
  ring

theorem band_at_tickWindow_end {K : ℕ} (hK : 0 < K) {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (n : ℕ) :
    κ * ((tickEnd K κ ω n + tickWindow K κ ω) / 2 + 1 / (4 * ω)) = (n : ℝ) / K + 1 / (2 * K) := by
  unfold tickEnd tickWindow tickTime
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp
  ring

section Ticks

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- ★★ **Before its start, tick `n` has not been written**: the count is below `n`. -/
theorem hand_before_tick (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < tickStart K (handRate J ħ g hf q) n) :
    handCount K (hand J ħ g hf t q) < n := by
  set κ := handRate J ħ g hf q with hκdef
  set ω := handFreq J ħ g hf q with hωdef
  have hω : 0 < ω := handFreq_pos J ħ g hf hJ hħ q
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnK' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hnK
  have hD0 := pointerDrift_nonneg hκ.le hω ht0
  have hD : pointerDrift κ ω t < (n : ℝ) / K - 1 / (2 * K) := by
    calc pointerDrift κ ω t ≤ κ * t := pointerDrift_le hκ.le hω ht0
      _ < κ * tickStart K κ n := mul_lt_mul_of_pos_left ht hκ
      _ = (n : ℝ) / K - 1 / (2 * K) := by unfold tickStart; field_simp
  have hsum : rep q.1 + pointerDrift κ ω t < (n : ℝ) / K := by linarith [hr.2]
  have hnK2 : (n : ℝ) / K ≤ 1 := by
    rw [div_le_one hKr]
    linarith
  have hrep := rep_hand_of_le J ħ g hf hJ hħ hr.1 hD0 (by linarith)
  rw [← hκdef, ← hωdef] at hrep
  unfold handCount
  rw [hrep]
  have hceil : ⌈(K : ℝ) * (rep q.1 + pointerDrift κ ω t)⌉₊ ≤ n := by
    rw [Nat.ceil_le]
    have := mul_lt_mul_of_pos_left hsum hKr
    rw [mul_div_cancel₀ _ hKr.ne'] at this
    exact this.le
  omega

/-- ★★ **Through its window, tick `n` displays**: the count is exactly `n`. -/
theorem hand_at_tick (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {n : ℕ} (hnK : n + 1 ≤ K) {t : ℝ}
    (ht₁ : tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n ≤ t)
    (ht₂ : t ≤ tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n
      + tickWindow K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    handCount K (hand J ħ g hf t q) = n := by
  set κ := handRate J ħ g hf q with hκdef
  set ω := handFreq J ħ g hf q with hωdef
  have hω : 0 < ω := handFreq_pos J ħ g hf hJ hħ q
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (1 / (2 * (K : ℝ))) := hq
  have hnK' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hnK
  have hl := pointerDrift_lower hκ.le hω t
  have hu := pointerDrift_upper hκ.le hω t
  have hDl : (n : ℝ) / K ≤ pointerDrift κ ω t := by
    rw [← band_at_tickEnd hK hκ hω n]
    exact (mul_le_mul_of_nonneg_left (by linarith) hκ.le).trans hl
  have hDu : pointerDrift κ ω t ≤ (n : ℝ) / K + 1 / (2 * K) := by
    rw [← band_at_tickWindow_end hK hκ hω n]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith) hκ.le)
  have hD0 : 0 ≤ pointerDrift κ ω t := le_trans (by positivity) hDl
  have hhalf : 1 / (2 * (K : ℝ)) + 1 / (2 * K) = 1 / K := by field_simp; ring
  have hwrap : rep q.1 + pointerDrift κ ω t ≤ 1 := by
    have : (n : ℝ) / K + 1 / K ≤ 1 := by
      rw [← add_div, div_le_one hKr]
      exact hnK'
    linarith [hr.2]
  rw [handCount_eq_iff hK, rep_hand_of_le J ħ g hf hJ hħ hr.1 hD0 hwrap, mem_Ioc]
  constructor
  · linarith [hr.1]
  · rw [show ((n : ℝ) + 1) / K = n / K + 1 / K by ring]
    linarith [hr.2]

/-- ★★★ **Tick `n` as an actual occurrence** (#191): the hand at `B` (site `{1}`), history from `0`,
value `n`, write interval `[(2n−1)/(2Kκ), n τ_tick + 1/(2ω)]`, window `τ_tick/2 − 1/ω`. The
hypotheses: the hand prepared in the first half-arc, a positive mean rate, the slowness `Kκ ≤ ω`,
and `1 ≤ n ≤ K − 1`. -/
noncomputable def tickWrite (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K) :
    ActualOccurrence ActiveArena ℕ 2 where
  evolve := activeEvolve J ħ g hf
  evolve_self := activeEvolve_self J ħ g hf
  evolve_comp := activeEvolve_comp J ħ g hf
  measurable_evolve := measurable_activeEvolve J ħ g hf hf1
  readout := fun x => handCount K x.2
  measurable_readout := (measurable_handCount K).comp measurable_snd
  ready := {x | x.2 ∈ handReady K}
  measurableSet_ready := measurable_snd (measurableSet_handReady K)
  prep := (msgPoint 1, q)
  prep_mem := hq
  site := {1}
  start := 0
  value := n
  writeStart := tickStart K (handRate J ħ g hf q) n
  writeEnd := tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n
  window := tickWindow K (handRate J ħ g hf q) (handFreq J ħ g hf q)
  isWrite :=
    { start_le := tickStart_nonneg hK hκ hn1
      interval := tickStart_le_tickEnd hK hκ (handFreq_pos J ħ g hf hJ hħ q) n
      window_nonneg := tickWindow_nonneg hK hκ hslow
      before := fun t ht0 ht => by
        show handCount K (activeFlow J ħ g hf (t - 0) (msgPoint 1, q)).2 ≠ n
        rw [sub_zero]
        exact (hand_before_tick J ħ g hf hJ hħ hK hq hκ hn1 hnK ht0 ht).ne
      holds := fun t ht₁ ht₂ => by
        show handCount K (activeFlow J ħ g hf (t - 0) (msgPoint 1, q)).2 = n
        rw [sub_zero]
        exact hand_at_tick J ħ g hf hJ hħ hK hq hκ hnK ht₁ ht₂ }

/-- **Successive ticks are distinguishable**: their values differ, so their arcs are disjoint. -/
theorem tickWrite_value_ne (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n + 2 ≤ K) :
    (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow hn1 (by omega)).value
      ≠ (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow (n := n + 1) (by omega) hnK).value := by
  show n ≠ n + 1
  omega

/-- ★ **Once written, a tick persists**: from the completion of tick `n` to the horizon the count is
at least `n`. -/
theorem handTick_persists (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) {n : ℕ} (hnK : n + 1 ≤ K) {t : ℝ}
    (ht₁ : tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    n ≤ handCount K (hand J ħ g hf t q) := by
  have hω := handFreq_pos J ħ g hf hJ hħ q
  have h0 : 0 ≤ tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n := by
    unfold tickEnd
    have := tickTime_pos hK hκ
    positivity
  have hat := hand_at_tick J ħ g hf hJ hħ hK hq hκ hnK (le_refl _)
    (by linarith [tickWindow_nonneg hK hκ hslow])
  rw [← hat]
  exact handCount_mono J ħ g hf hJ hħ hK hq hκ h0 ht₁ ht

/-- ★ **Generation inherited from #195, no new geometry**: the hand clock's dynamics is the flow of
the activated energy on the arena, read at the clock's preparation. -/
theorem handClock_generated (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (t : ℝ) (q : LF4.KTorus) :
    (arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t
        (fibredArenaEquiv 2 2 (msgPoint 1, q))
      = fibredArenaEquiv 2 2 (activeFlow J ħ g hf t (msgPoint 1, q)) :=
  hamiltonianFlow_activeFlow J ħ g hf hc t _

/-- ★★★ **The hand clock.** One carrier and one pointer, read in `K` arcs, with the mean rate `κ`
and the Rabi rate `ω` of the preparation: the hand is #194's pointer; it never turns back; its count
never decreases over the horizon; calibrated with `τ_tick = 2/(Kκ)` it reads within
`τ_tick + 1/(2ω)` of `t`; each tick `n` with `1 ≤ n ≤ K − 1` is an `ActualOccurrence` at site `{B}`
from the start `0` with value `n`, successive ticks spaced by `τ_tick`, and once written a tick
persists to the horizon. -/
theorem hand_clock (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q)
    (hslow : K * handRate J ħ g hf q ≤ handFreq J ħ g hf q) :
    (∀ t, hand J ħ g hf t q
        = pshift (pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t) q)
      ∧ (∀ s t, s ≤ t → pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) s
          ≤ pointerDrift (handRate J ħ g hf q) (handFreq J ħ g hf q) t)
      ∧ (∀ s t, 0 ≤ s → s ≤ t →
          t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q) →
          handCount K (hand J ħ g hf s q) ≤ handCount K (hand J ħ g hf t q))
      ∧ (∀ t, 0 ≤ t → t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q) →
          |handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf t q) - t|
            ≤ tickTime K (handRate J ħ g hf q) + 1 / (2 * handFreq J ħ g hf q))
      ∧ (∀ (n : ℕ) (hn1 : 1 ≤ n) (hnK : n + 1 ≤ K),
          (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow hn1 hnK).site = {1}
            ∧ (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow hn1 hnK).prep = (msgPoint 1, q)
            ∧ (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow hn1 hnK).value = n
            ∧ (tickWrite J ħ g hf hJ hħ hf1 hK hq hκ hslow hn1 hnK).writeEnd
              = tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n)
      ∧ (∀ n : ℕ, tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) (n + 1)
          = tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n
            + tickTime K (handRate J ħ g hf q))
      ∧ (∀ (n : ℕ), n + 1 ≤ K → ∀ t,
          tickEnd K (handRate J ħ g hf q) (handFreq J ħ g hf q) n ≤ t →
          t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q) →
          n ≤ handCount K (hand J ħ g hf t q)) :=
  ⟨fun t => hand_eq J ħ g hf hJ hħ t q, fun _ _ hst => pointerDrift_mono J ħ g hf hJ hħ hκ hst,
    fun _ _ hs hst ht => handCount_mono J ħ g hf hJ hħ hK hq hκ hs hst ht,
    fun _ ht0 ht => abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht,
    fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩, tickEnd_succ K _ _,
    fun _ hnK _ ht₁ ht => handTick_persists J ħ g hf hJ hħ hK hq hκ hslow hnK ht₁ ht⟩

end Ticks

end CSD.RecordLayer

end
