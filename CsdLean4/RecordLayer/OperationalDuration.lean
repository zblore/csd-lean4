/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ChainChrono
public import CsdLean4.RecordLayer.RecordOccurrence

/-!
# Operational duration: what a calibrated clock measures, against what the longest chain counts

**Category:** 7-SigmaLayer (the record layer — the duration half of the author's second brief).
BACKLOG #193 (out of #39; the third of #191–#197).

A duration is the difference of two readings of **one** physical clock history. This file defines
it from the record clock of #185 and proves the properties the brief asks for, naming each for what
it is.

* `clockHistory T τ c t` — the calibrated reading of clock `c`, run from the switch-on, at `t`;
  `duration T τ c s t` — **the operational duration** from `s` to `t` along that history;
* ★ `duration_nonneg` — non-negative for chronologically ordered readings (`tickCount_mono`);
* `duration_add` — **additivity on consecutive intervals is the telescoping identity**: an algebraic
  consistency of one history with itself, not a derivation of proper time; `duration_self`,
  `duration_neg`;
* `tickCount_clockEvolve_of_nonpos`, `offsetHistory`, ★ `duration_offset` — **clock-origin
  invariance** twice over: a switch-on reference anywhere before `0` gives the same readings, and a
  constant offset on every reading leaves every duration unchanged;
* ★ `duration_rescale` — the unit rescaling `τ ↦ λ τ` scales every duration by `λ`;
* ★★ `abs_duration_sub_lt` — **the resolution bound**: calibrated with the period, a duration is
  within two ticks of the elapsed ontic parameter over the horizon (`abs_tickReading_sub_lt` twice);
* `duration_eq_zero_of_writeEnd_eq` — **two descriptions of one write** (occurrences with the same
  completion time, #191) are at zero duration from one another;
* `edgeDuration_nonneg`, ★ `sum_edgeDuration` — along an occurrence chain the edge durations read off
  one clock are non-negative and sum to the end-to-end duration (telescoping again, and named so);
* **the chain witness** (#190, #192): ★★ `duration_reception` — the clock at site `m` measures
  `m τ_hop` from the switch-on to the reception; ★★★ `duration_eq_chronoDist_mul` — **that duration
  is the chrono distance times the tick**, while `two_mul_le_causalDist` keeps the causal longest
  chain at `≥ 2m`;
* ★★★ `operational_duration` — the package.

## The deliverable, in words

`causalDist e₁ e₂` is the length of the longest chain of strict steps of **permitted influence** on
the assumed coupling graph. A region inclusion at an unchanged period is such a step, so the quantity
measures the depth of the influence order and may exceed the elapsed periods without bound in the
number of regions (#188, #190). `chronoDist` keeps only the steps that advance the period and is bounded
by the elapsed periods (#192). A **clock duration** is the difference of two tick counts of one
calibrated register, times the tick. On the chain witness, with calibration `T = τ_hop` and every
edge on for one period, the duration from the switch-on to the reception at site `m` equals `m`
ticks and equals the chrono distance; the causal longest chain is at least `2m`. The calibration and
the resolution of the events are hypotheses: a different `T` changes the tick count, and several
records may be written per tick. Nothing here is a proper time, a metric, or a universal speed.

References: `specs/BACKLOG.md` #193, #185, #188, #190, #191, #192, #39; `RecordLayer/RecordClock.lean`
(`tickReading`, `tickCount_mono`, `abs_tickReading_sub_lt`), `RecordLayer/ChainClocks.lean`,
`RecordLayer/ChainChrono.lean` (`chronoDist_siteEvents`), `RecordLayer/RecordOccurrence.lean`,
`CV/RadarCoordinates.lean` (`rescale`, `shift`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### The clock history and its durations -/

/-- **The clock history**: the calibrated reading of clock `c`, run from the switch-on, at `t`. -/
noncomputable def clockHistory (T τ : ℝ) (c : ClockArena K) (t : ℝ) : ℝ :=
  tickReading τ (clockEvolve T 0 t c)

theorem clockHistory_eq (T τ : ℝ) (c : ClockArena K) (t : ℝ) :
    clockHistory T τ c t = (tickCount (clockEvolve T 0 t c) : ℝ) * τ := rfl

/-- **Operational duration** from `s` to `t`: the difference of the two readings of one history. -/
noncomputable def duration (T τ : ℝ) (c : ClockArena K) (s t : ℝ) : ℝ :=
  clockHistory T τ c t - clockHistory T τ c s

theorem duration_self (T τ : ℝ) (c : ClockArena K) (t : ℝ) : duration T τ c t t = 0 := sub_self _

theorem duration_neg (T τ : ℝ) (c : ClockArena K) (s t : ℝ) :
    duration T τ c t s = -duration T τ c s t := by
  unfold duration
  ring

/-- ★ **Non-negativity for chronologically ordered readings**: the tick count is monotone. -/
theorem duration_nonneg (hK : 0 < K) {T τ : ℝ} (hT : 0 < T) (hτ : 0 ≤ τ) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {s t : ℝ} (hst : s ≤ t) : 0 ≤ duration T τ c s t := by
  unfold duration clockHistory tickReading
  rw [← sub_mul]
  refine mul_nonneg (sub_nonneg.2 ?_) hτ
  exact_mod_cast tickCount_mono hK hT hc hst

/-- **Additivity on consecutive intervals is the telescoping identity** — an algebraic consistency of
one history with itself, not a derivation of proper time. -/
theorem duration_add (T τ : ℝ) (c : ClockArena K) (s t u : ℝ) :
    duration T τ c s t + duration T τ c t u = duration T τ c s u := by
  unfold duration
  ring

/-! ### Clock-origin invariance -/

/-- A switch-on reference anywhere before `0` gives the readings of the clock run from `0`
(the general form of `tickCount_clock_neg_one`). -/
theorem tickCount_clockEvolve_of_nonpos {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ≤ 0) (t : OnticTime)
    (c : ClockArena K) : tickCount (clockEvolve T s t c) = tickCount (clockEvolve T 0 t c) := by
  have h : (clockEvolve T s t c).2 = (clockEvolve T 0 t c).2 := by
    funext n
    rw [clockEvolve_slot, clockEvolve_slot,
      winElapsed_of_le hT (n := n) (u := s)
        (by linarith [mul_nonneg (Nat.cast_nonneg (n : ℕ) : (0 : ℝ) ≤ _) hT.le]),
      winElapsed_of_le hT (n := n) (u := 0) (by positivity)]
  unfold tickCount
  rw [h]

/-- The history with a constant offset `a` on every reading: another zero of the same clock. -/
noncomputable def offsetHistory (T τ : ℝ) (c : ClockArena K) (a t : ℝ) : ℝ :=
  clockHistory T τ c t + a

/-- ★ **Clock-origin invariance**: a constant offset on every reading leaves every duration
unchanged. -/
theorem duration_offset (T τ : ℝ) (c : ClockArena K) (a s t : ℝ) :
    offsetHistory T τ c a t - offsetHistory T τ c a s = duration T τ c s t := by
  unfold offsetHistory duration
  ring

/-! ### Unit rescaling and resolution -/

/-- ★ **Unit rescaling**: measuring in the unit `λ τ` scales every duration by `λ`. -/
theorem duration_rescale (T τ lam : ℝ) (c : ClockArena K) (s t : ℝ) :
    duration T (lam * τ) c s t = lam * duration T τ c s t := by
  unfold duration clockHistory tickReading
  ring

/-- ★★ **The resolution bound**: calibrated with the period, a duration is within two ticks of the
elapsed ontic parameter, for readings inside the horizon. -/
theorem abs_duration_sub_lt (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {s t : ℝ} (hs0 : 0 ≤ s) (hsK : s ≤ K * T) (ht0 : 0 ≤ t)
    (htK : t ≤ K * T) : |duration T T c s t - (t - s)| < 2 * T := by
  have h1 := abs_tickReading_sub_lt hK hT hc ht0 htK
  have h2 := abs_tickReading_sub_lt hK hT hc hs0 hsK
  have heq : duration T T c s t - (t - s)
      = (tickReading T (clockEvolve T 0 t c) - t) - (tickReading T (clockEvolve T 0 s c) - s) := by
    unfold duration clockHistory
    ring
  rw [heq]
  calc |(tickReading T (clockEvolve T 0 t c) - t) - (tickReading T (clockEvolve T 0 s c) - s)|
      ≤ |tickReading T (clockEvolve T 0 t c) - t| + |tickReading T (clockEvolve T 0 s c) - s| :=
        abs_sub _ _
    _ < T + T := add_lt_add h1 h2
    _ = 2 * T := by ring

/-! ### Duplicate descriptions and occurrence chains -/

/-- **Two descriptions of one write are at zero duration**: occurrences completing at the same time
(#191) have no duration between them, on any clock. -/
theorem duration_eq_zero_of_writeEnd_eq {X : Type*} [MeasurableSpace X] {Ω : Type*}
    [MeasurableSpace Ω] {L : ℕ} (o₁ o₂ : ActualOccurrence X Ω L) (h : o₁.writeEnd = o₂.writeEnd)
    (T τ : ℝ) (c : ClockArena K) : duration T τ c o₁.writeEnd o₂.writeEnd = 0 := by
  rw [h]
  exact duration_self T τ c _

/-- Along an occurrence chain with non-decreasing completion times, every edge duration is
non-negative. -/
theorem edgeDuration_nonneg (hK : 0 < K) {T τ : ℝ} (hT : 0 < T) (hτ : 0 ≤ τ) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {ts : ℕ → ℝ} (hts : Monotone ts) (i : ℕ) :
    0 ≤ duration T τ c (ts i) (ts (i + 1)) :=
  duration_nonneg hK hT hτ hc (hts (Nat.le_succ i))

/-- ★ **The edge durations of an occurrence chain sum to the end-to-end duration** — telescoping,
named as such. -/
theorem sum_edgeDuration (T τ : ℝ) (c : ClockArena K) (ts : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, duration T τ c (ts i) (ts (i + 1)) = duration T τ c (ts 0) (ts m) := by
  unfold duration
  exact Finset.sum_range_sub (fun i => clockHistory T τ c (ts i)) m

/-! ### The chain witness: duration against chrono and causal distance -/

variable {n : ℕ}

/-- ★★ **The clock at site `m` measures `m` ticks from the switch-on to the reception.** -/
theorem duration_reception {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ) (hK : 0 < K)
    (hnK : n ≤ K) {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K) (m : ℕ)
    (hm : m ≤ n) :
    duration T T (c ⟨m, Nat.lt_succ_of_le hm⟩) 0 (m * hopTime J ħ) = m * T := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  have h0 := tickCount_at_period hK hTpos (hc ⟨m, Nat.lt_succ_of_le hm⟩) (m := 0) (Nat.zero_le _)
  rw [Nat.cast_zero, zero_mul] at h0
  unfold duration clockHistory tickReading
  rw [← hT, tickCount_at_period hK hTpos (hc _) (hm.trans hnK), h0, Nat.cast_zero, zero_mul, sub_zero]

/-- ★★★ **Clock duration is the chrono distance times the tick** on the chain witness, while the
causal longest chain is at least twice the tick count. -/
theorem duration_eq_chronoDist_mul {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 0 < K) (hnK : n ≤ K) {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K)
    (m : ℕ) (hm : m ≤ n) :
    duration T T (c ⟨m, Nat.lt_succ_of_le hm⟩) 0 (m * hopTime J ħ)
        = (chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) : ℝ) * T
      ∧ 2 * m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  refine ⟨?_, two_mul_le_causalDist m hm⟩
  rw [duration_reception hJ hħ hT hK hnK hc m hm, chronoDist_siteEvents m hm]

/-! ### The package -/

/-- ★★★ **Operational duration.** Non-negative for ordered readings; additive (telescoping);
invariant under a constant offset of the readings; scaling under unit rescaling; within two ticks of
the elapsed ontic parameter when calibrated with the period; zero between two descriptions of one
write; and on the chain witness the clock at site `m` measures `m` ticks, equal to the chrono
distance, while the causal longest chain is at least `2m`. -/
theorem operational_duration {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (hT : T = hopTime J ħ)
    (hK : 0 < K) (hnK : n ≤ K) {c : Fin (n + 1) → ClockArena K} (hc : ∀ j, c j ∈ ClockReady K) :
    (∀ (j : Fin (n + 1)) (τ : ℝ), 0 ≤ τ → ∀ s t : ℝ, s ≤ t → 0 ≤ duration T τ (c j) s t)
      ∧ (∀ (j : Fin (n + 1)) (τ s t u : ℝ),
          duration T τ (c j) s t + duration T τ (c j) t u = duration T τ (c j) s u)
      ∧ (∀ (j : Fin (n + 1)) (τ a s t : ℝ),
          offsetHistory T τ (c j) a t - offsetHistory T τ (c j) a s = duration T τ (c j) s t)
      ∧ (∀ (j : Fin (n + 1)) (τ lam s t : ℝ),
          duration T (lam * τ) (c j) s t = lam * duration T τ (c j) s t)
      ∧ (∀ (j : Fin (n + 1)) (s t : ℝ), 0 ≤ s → s ≤ K * T → 0 ≤ t → t ≤ K * T →
          |duration T T (c j) s t - (t - s)| < 2 * T)
      ∧ (∀ m (hm : m ≤ n),
          duration T T (c ⟨m, Nat.lt_succ_of_le hm⟩) 0 (m * hopTime J ħ)
              = (chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) : ℝ) * T
            ∧ 2 * m ≤ causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)) := by
  have hTpos : 0 < T := hT ▸ hopTime_pos hJ hħ
  exact ⟨fun j τ hτ s t hst => duration_nonneg hK hTpos hτ (hc j) hst,
    fun j τ s t u => duration_add T τ (c j) s t u,
    fun j τ a s t => duration_offset T τ (c j) a s t,
    fun j τ lam s t => duration_rescale T τ lam (c j) s t,
    fun j s t hs0 hsK ht0 htK => abs_duration_sub_lt hK hTpos (hc j) hs0 hsK ht0 htK,
    fun m hm => duration_eq_chronoDist_mul hJ hħ hT hK hnK hc m hm⟩

end CSD.RecordLayer

end
