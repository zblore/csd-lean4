/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.EchoArena
public import CsdLean4.RecordLayer.RadarDetector

/-!
# Round-trip radar from the sender's records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #200 (out of #39; the author's third
operational-geometry brief, §1's proof target).

#197 read a radar coordinate off one clock at `A` and a detection at `B`: a one-way flight. Here
both radar timestamps are readings of **`A`'s** clock, taken at **`A`'s** two records — the emission
arc and the return arc of the one register at `A` that the carrier itself writes (#199). The arena
is #199's echo arena with #185's record clock alongside; the ideal readings are `(0, 2τ_hop)`, the
round trip, whose radar separation is `τ_hop` (`radarSep_roundTrip`). Every contribution to the
error is derived for the witness; the two input bounds are labelled.

* `EchoClockedArena`, `echoClockedEvolve` — **the echo arena with the record clock**: a two-time,
  measure-preserving dynamics; ★★ `clockedEmissionRecord`, `clockedReturnRecord` — **`A`'s two
  writes registered on it** (#191), with the clock ready alongside the pointers; `echoClockReading`,
  `emissionEvent_time`, `returnEvent_time` — their events, labelled by the clock at the completion
  of each write; ★ `emission_causalPrecedes_return` — the emission precedes the return on the hop
  graph;
* ★ `abs_detunedRoundTrip_sub_roundTrip_le` — **outward transfer + return transfer**: the detuned
  round trip is within `2 transferError` of `2τ_hop`;
* `echoReturnDelay` — **the detector response of the return write**: its completion minus the
  detuned round trip, explicit in the preparation (`echoReturnDelay_eq`); the emission write's
  response is its completion `emitEnd` itself;
* `echoReadings` — **the measured readings**: `A`'s clock at a time in the emission window and at a
  time in the return window; ★★ `echoReadings_eq_labels` — **taken at the completions of the two
  writes, the radar timestamps are `T` times the clock labels of `A`'s two record events**;
* `echoRadarBudget` — `T + senderWindow + emitEnd + |echoReturnDelay| + 2 transferError`: clock
  resolution (derived), the retention window (input: each reading is taken while its record
  displays), the two detector responses (derived), the two transfers (derived); ★★
  `abs_echoReadings_emit_sub_le`, `abs_echoReadings_ret_sub_le`;
* ★★★ `radar_from_sender_records` — **one bound on radar time, separation and distance** against
  the ideal round-trip readings `(0, 2τ_hop)`, both records displayed at their reading times, the
  ideal separation being `τ_hop`: **a radar separation read entirely at one station**.

## Honest scope

* The emission timestamp is late by the emission write's completion: the pointer at `A` reaches
  its first arc only after the carrier has left. This is a detector response, derived, and it enters
  the budget as `emitEnd`.
* The clock is still #185's scheduled device; the internally driven clock is #201, and the two on
  one arena is #202.
* **No universal `c`, no Lorentz invariance.** `c₀` is a calibration constant, the hop time is the
  exchange's own, the arena has no metric. The #187 and #190 headers stand.
* The input bounds are the two retention windows and the clock horizon (`t ≤ K T`).

References: `specs/BACKLOG.md` #200, #199, #197, #187, #185, #39; `RecordLayer/EchoArena.lean`,
`RecordLayer/RadarDetector.lean` (`transferError`, `abs_detunedHopTime_sub_hopTime_le`),
`CV/RadarCoordinates.lean` (`RadarReadings`, `ofDuration`, `radarSep_roundTrip`,
`abs_radarTime_sub_le`), `RecordLayer/RecordClock.lean` (`tickReading`, `abs_tickReading_sub_lt`,
`tickCount_mono`), `RecordLayer/CoupledReception.lean` (the clocked-arena pattern).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Both transfers -/

/-- ★ **Outward transfer and return transfer**: the detuned round trip `πħ/Ω` is within
`2 transferError` of `2τ_hop`. -/
theorem abs_detunedRoundTrip_sub_roundTrip_le {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    |detunedRoundTrip J ħ Δ - roundTrip J ħ| ≤ 2 * transferError J ħ Δ := by
  rw [detunedRoundTrip_eq, roundTrip, ← mul_sub, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (abs_detunedHopTime_sub_hopTime_le hJ hħ Δ) (by norm_num)

/-! ### The echo arena with the record clock -/

section Clocked

variable {K : ℕ} (J ħ : ℝ) (A B : PointerCoupling)

/-- **The echo arena with the record clock of #185.** -/
abbrev EchoClockedArena (K : ℕ) := EchoArena × ClockArena K

/-- The joint two-time propagator: the echo dynamics and the clock. -/
noncomputable def echoClockedEvolve (T : ℝ) (s t : OnticTime) :
    EchoClockedArena K → EchoClockedArena K :=
  Prod.map (echoEvolve J ħ A B s t) (clockEvolve T s t)

theorem echoClockedEvolve_self (T : ℝ) (t : OnticTime) :
    echoClockedEvolve (K := K) J ħ A B T t t = id := by
  rw [echoClockedEvolve, echoEvolve_self, clockEvolve_self, Prod.map_id]

/-- The two-time law on the clocked echo arena. -/
theorem echoClockedEvolve_comp (T : ℝ) (s t u : OnticTime) :
    echoClockedEvolve (K := K) J ħ A B T t u ∘ echoClockedEvolve J ħ A B T s t
      = echoClockedEvolve J ħ A B T s u := by
  rw [echoClockedEvolve, echoClockedEvolve, echoClockedEvolve, Prod.map_comp_map, echoEvolve_comp,
    clockEvolve_comp]

theorem measurable_echoClockedEvolve (T : ℝ) (s t : OnticTime) :
    Measurable (echoClockedEvolve (K := K) J ħ A B T s t) :=
  (measurable_echoEvolve J ħ A B s t).prodMap (measurable_clockEvolve T s t)

/-- Liouville on the clocked echo arena. -/
theorem echoClockedEvolve_measurePreserving (T : ℝ) (s t : OnticTime) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoClockedEvolve (K := K) J ħ A B T s t)
      (((fsMeasure p₀).prod volume).prod volume) (((fsMeasure p₀).prod volume).prod volume) :=
  (echoEvolve_measurePreserving J ħ A B s t p₀).prod (clockEvolve_measurePreserving T s t)

/-- The arena clock's reading. -/
noncomputable def echoClockReading (x : EchoClockedArena K) : ℕ := tickCount x.2

end Clocked

/-! ### `A`'s two writes on the clocked arena -/

section Records

variable {K : ℕ} {J ħ : ℝ} (A B : PointerCoupling) {qA qB : LF4.KTorus}

/-- ★★ **The emission record on the clocked arena** (#191): `A`'s first arc, the clock ready
alongside. -/
noncomputable def clockedEmissionRecord (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ActualOccurrence (EchoClockedArena K) (Fin 3) 2 where
  evolve := echoClockedEvolve J ħ A B T
  evolve_self := echoClockedEvolve_self J ħ A B T
  evolve_comp := echoClockedEvolve_comp J ħ A B T
  measurable_evolve := measurable_echoClockedEvolve J ħ A B T
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := {x | x.1 ∈ echoReady ∧ x.2 ∈ ClockReady K}
  measurableSet_ready :=
    (measurable_fst measurableSet_echoReady).inter (measurable_snd measurableSet_clockReady)
  prep := ((msgPoint 1, (qA, qB)), c)
  prep_mem := ⟨⟨hqA, hqB⟩, hc⟩
  site := {0}
  start := 0
  value := 1
  writeStart := emitStart (senderRate A ħ qA)
  writeEnd := emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite := (emissionRecord A B hJ hħ hqA hqB hr hslow).isWrite

/-- ★★ **The return record on the clocked arena** (#191): `A`'s second arc. -/
noncomputable def clockedReturnRecord (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ActualOccurrence (EchoClockedArena K) (Fin 3) 2 where
  evolve := echoClockedEvolve J ħ A B T
  evolve_self := echoClockedEvolve_self J ħ A B T
  evolve_comp := echoClockedEvolve_comp J ħ A B T
  measurable_evolve := measurable_echoClockedEvolve J ħ A B T
  readout := fun x => senderRead x.1
  measurable_readout := measurable_senderRead.comp measurable_fst
  ready := {x | x.1 ∈ echoReady ∧ x.2 ∈ ClockReady K}
  measurableSet_ready :=
    (measurable_fst measurableSet_echoReady).inter (measurable_snd measurableSet_clockReady)
  prep := ((msgPoint 1, (qA, qB)), c)
  prep_mem := ⟨⟨hqA, hqB⟩, hc⟩
  site := {0}
  start := 0
  value := 2
  writeStart := returnStart (senderRate A ħ qA)
  writeEnd := returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite := (returnRecord A B hJ hħ hqA hqB hr hslow).isWrite

theorem emissionEvent_region (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedEmissionRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading).region
      = {0} := rfl

/-- The emission event's period is the clock's tick count at the completion of the emission write. -/
theorem emissionEvent_time (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedEmissionRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading).time
      = tickCount (clockEvolve T 0
          (emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) c) := rfl

theorem returnEvent_region (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedReturnRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading).region
      = {0} := rfl

/-- The return event's period is the clock's tick count at the completion of the return write. -/
theorem returnEvent_time (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    {c : ClockArena K} (hc : c ∈ ClockReady K) (T : ℝ) :
    ((clockedReturnRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading).time
      = tickCount (clockEvolve T 0
          (returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) c) := rfl

theorem emitEnd_nonneg {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω) :
    0 ≤ emitEnd r l ω := by
  unfold emitEnd
  exact div_nonneg (by linarith [band_nonneg hr.le hl0 hω]) (meanRate_pos hr hl).le

theorem returnEnd_nonneg {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω) :
    0 ≤ returnEnd r l ω := by
  unfold returnEnd
  exact div_nonneg (by linarith [band_nonneg hr.le hl0 hω]) (meanRate_pos hr hl).le

/-- The emission write completes before the return write. -/
theorem emitEnd_le_returnEnd {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω)
    (hslow : 3 * (r * l) ≤ ω) : emitEnd r l ω ≤ returnEnd r l ω := by
  have h := emitEnd_add_window_lt_returnEnd hr hl0 hl hω hslow
  have h2 := senderWindow_nonneg hr hl hω hslow
  linarith

/-- ★ **The emission precedes the return on the hop graph**: same site, the later clock label. -/
theorem emission_causalPrecedes_return (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) (hK : 0 < K)
    {c : ClockArena K} (hc : c ∈ ClockReady K) {T : ℝ} (hT : 0 < T) :
    CausalPrecedes hopGraph
      ((clockedEmissionRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading)
      ((clockedReturnRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent echoClockReading) := by
  rw [CausalPrecedes, emissionEvent_time, emissionEvent_region, returnEvent_time, returnEvent_region]
  refine ⟨tickCount_mono hK hT hc (emitEnd_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le
    (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) hslow), ?_⟩
  exact subset_graphBall hopGraph {0} _

end Records

/-! ### The readings, the budget and the bound -/

section Radar

variable {K : ℕ} {J ħ : ℝ} (A B : PointerCoupling) {qA qB : LF4.KTorus}

/-- **The detector response of the return write**: its completion minus the detuned round trip. -/
noncomputable def echoReturnDelay (J ħ : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    - detunedRoundTrip J ħ (echoDetuning A B qA qB)

/-- The return delay, explicit in the preparation:
`(2/3 + r_A λ/(4ω))/(r_A (1 − λ/2)) − πħ/Ω'`. -/
theorem echoReturnDelay_eq (J ħ : ℝ) (qA qB : LF4.KTorus) :
    echoReturnDelay A B J ħ qA qB
      = (2 / 3 + senderRate A ħ qA * echoLoss A B J qA qB / (4 * echoRate A B J ħ qA qB))
          / (senderRate A ħ qA * (1 - echoLoss A B J qA qB / 2))
        - Real.pi * ħ / rabiFreq J (echoDetuning A B qA qB) := rfl

/-- **The error budget of the round trip**: clock resolution `T`, the retention window, the emission
write's response `emitEnd`, the return write's response `|echoReturnDelay|`, and the two transfers
`2 transferError`. -/
noncomputable def echoRadarBudget (J ħ : ℝ) (qA qB : LF4.KTorus) (T : ℝ) : ℝ :=
  T + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
    + |echoReturnDelay A B J ħ qA qB| + 2 * transferError J ħ (echoDetuning A B qA qB)

/-- **The measured readings**: `A`'s clock at the time `t₁` of the emission reading and at the time
`t₂` of the return reading. -/
noncomputable def echoReadings (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂) : RadarReadings :=
  ⟨tickReading T (clockEvolve T 0 t₁ c), tickReading T (clockEvolve T 0 t₂ c),
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 (tickCount_mono hK hT hc h₁₂)) hT.le⟩

theorem echoReadings_emit (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂) :
    (echoReadings hK hT hc h₁₂).emit = tickReading T (clockEvolve T 0 t₁ c) := rfl

theorem echoReadings_ret (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂) :
    (echoReadings hK hT hc h₁₂).ret = tickReading T (clockEvolve T 0 t₂ c) := rfl

/-- ★★ **Taken at the completions of the two writes, the radar timestamps are `T` times the clock
labels of `A`'s two record events.** -/
theorem echoReadings_eq_labels (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) :
    (echoReadings hK hT hc (emitEnd_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le
        (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) hslow)).emit
      = (((clockedEmissionRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent
          echoClockReading).time : ℝ) * T
    ∧ (echoReadings hK hT hc (emitEnd_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le
        (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) hslow)).ret
      = (((clockedReturnRecord A B hJ hħ hqA hqB hr hslow hc T).toRecordEvent
          echoClockReading).time : ℝ) * T :=
  ⟨rfl, rfl⟩

/-- The ideal round-trip readings: emission at `0`, return at `2τ_hop`. -/
noncomputable def idealEchoReadings (hJ : 0 < J) (hħ : 0 < ħ) : RadarReadings :=
  RadarReadings.ofDuration 0 (roundTrip J ħ) (roundTrip_pos hJ hħ).le

theorem idealEchoReadings_emit (hJ : 0 < J) (hħ : 0 < ħ) :
    (idealEchoReadings (J := J) (ħ := ħ) hJ hħ).emit = 0 := rfl

theorem idealEchoReadings_ret (hJ : 0 < J) (hħ : 0 < ħ) :
    (idealEchoReadings (J := J) (ħ := ħ) hJ hħ).ret = roundTrip J ħ := by
  show (0 : ℝ) + roundTrip J ħ = roundTrip J ħ
  rw [zero_add]

/-- The ideal radar separation of the round trip is the hop time. -/
theorem idealEchoReadings_radarSep (hJ : 0 < J) (hħ : 0 < ħ) :
    (idealEchoReadings (J := J) (ħ := ħ) hJ hħ).radarSep = hopTime J ħ :=
  RadarReadings.radarSep_roundTrip hJ hħ 0

theorem echoRadarBudget_nonneg (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) {T : ℝ}
    (hT : 0 < T) : 0 ≤ echoRadarBudget A B J ħ qA qB T := by
  unfold echoRadarBudget
  have h1 := senderWindow_nonneg hr (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB)
    hslow
  have h2 := emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have h3 := abs_nonneg (echoReturnDelay A B J ħ qA qB)
  have h4 := transferError_nonneg hJ hħ (echoDetuning A B qA qB)
  linarith

/-- ★★ **The emission reading is within the budget of `0`.** Clock resolution (derived), the
emission write's completion (derived), the retention window (input: the reading is taken while the
emission record displays). -/
theorem abs_echoReadings_emit_sub_le (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    (ht₁K : t₁ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(echoReadings hK hT hc h₁₂).emit - 0| ≤ echoRadarBudget A B J ħ qA qB T := by
  rw [echoReadings_emit, sub_zero]
  have hE := emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have h1 := abs_tickReading_sub_lt hK hT hc (by linarith [hemit.1]) ht₁K
  have h2 : |t₁| ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
      + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) := by
    rw [abs_of_nonneg (by linarith [hemit.1])]
    exact hemit.2
  have h3 := abs_nonneg (echoReturnDelay A B J ħ qA qB)
  have h4 := transferError_nonneg hJ hħ (echoDetuning A B qA qB)
  calc |tickReading T (clockEvolve T 0 t₁ c)|
      = |(tickReading T (clockEvolve T 0 t₁ c) - t₁) + t₁| := by rw [sub_add_cancel]
    _ ≤ |tickReading T (clockEvolve T 0 t₁ c) - t₁| + |t₁| := abs_add_le _ _
    _ ≤ echoRadarBudget A B J ħ qA qB T := by
        unfold echoRadarBudget
        linarith [h1.le, h2]

/-- ★★ **The return reading is within the budget of `2τ_hop`.** Clock resolution (derived), the
retention window (input: the reading is taken while the return record displays), the return write's
response (derived), the two transfers (derived). -/
theorem abs_echoReadings_ret_sub_le (hJ : 0 < J) (hħ : 0 < ħ) (hr : 0 < senderRate A ħ qA)
    (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    (ht₂K : t₂ ≤ K * T)
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    |(echoReadings hK hT hc h₁₂).ret - roundTrip J ħ| ≤ echoRadarBudget A B J ħ qA qB T := by
  rw [echoReadings_ret]
  set r := senderRate A ħ qA
  set l := echoLoss A B J qA qB
  set ω := echoRate A B J ħ qA qB
  set Δ := echoDetuning A B qA qB
  have hE := emitEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have hR := returnEnd_nonneg hr (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB)
    (echoRate_pos A B hJ hħ qA qB)
  have h1 := abs_tickReading_sub_lt hK hT hc (by linarith [hret.1]) ht₂K
  have h2 : |t₂ - returnEnd r l ω| ≤ senderWindow r l ω := by
    rw [abs_le]
    constructor <;> linarith [hret.1, hret.2]
  have h3 : |returnEnd r l ω - detunedRoundTrip J ħ Δ| = |echoReturnDelay A B J ħ qA qB| := rfl
  have h4 := abs_detunedRoundTrip_sub_roundTrip_le hJ hħ Δ
  calc |tickReading T (clockEvolve T 0 t₂ c) - roundTrip J ħ|
      ≤ |tickReading T (clockEvolve T 0 t₂ c) - t₂| + |t₂ - roundTrip J ħ| := abs_sub_le _ _ _
    _ ≤ |tickReading T (clockEvolve T 0 t₂ c) - t₂|
        + (|t₂ - returnEnd r l ω| + |returnEnd r l ω - roundTrip J ħ|) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ |tickReading T (clockEvolve T 0 t₂ c) - t₂|
        + (|t₂ - returnEnd r l ω|
          + (|returnEnd r l ω - detunedRoundTrip J ħ Δ| + |detunedRoundTrip J ħ Δ - roundTrip J ħ|)) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ echoRadarBudget A B J ħ qA qB T := by
        rw [h3]
        unfold echoRadarBudget
        linarith [h1.le, h2, h4]

/-- ★★★ **Round-trip radar from the sender's records.** Both timestamps are readings of `A`'s clock,
taken while `A`'s emission record (value `1`) and `A`'s return record (value `2`) display; against
the ideal round-trip readings `(0, 2τ_hop)` — whose radar separation is `τ_hop` — the measured radar
time, separation and distance are within the budget `T + senderWindow + emitEnd + |echoReturnDelay|
+ 2 transferError` (times `c₀` for the distance). A radar separation read entirely at one station. -/
theorem radar_from_sender_records (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) (hK : 0 < K)
    {T : ℝ} (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {t₁ t₂ : ℝ}
    (ht₁K : t₁ ≤ K * T) (ht₂K : t₂ ≤ K * T)
    (hemit : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₁
      ∧ t₁ ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    (hret : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t₂
      ∧ t₂ ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB))
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    ∃ h₁₂ : t₁ ≤ t₂,
      senderRead (echoFlow J ħ A B t₁ (msgPoint 1, (qA, qB))) = 1
      ∧ senderRead (echoFlow J ħ A B t₂ (msgPoint 1, (qA, qB))) = 2
      ∧ (idealEchoReadings hJ hħ).radarSep = hopTime J ħ
      ∧ |(echoReadings hK hT hc h₁₂).radarTime - (idealEchoReadings hJ hħ).radarTime|
          ≤ echoRadarBudget A B J ħ qA qB T
      ∧ |(echoReadings hK hT hc h₁₂).radarSep - (idealEchoReadings hJ hħ).radarSep|
          ≤ echoRadarBudget A B J ħ qA qB T
      ∧ |(echoReadings hK hT hc h₁₂).radarDist c₀ - (idealEchoReadings hJ hħ).radarDist c₀|
          ≤ c₀ * echoRadarBudget A B J ħ qA qB T := by
  have h₁₂ : t₁ ≤ t₂ := by
    have := emitEnd_add_window_lt_returnEnd hr (echoLoss_pos A B hJ qA qB).le
      (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) hslow
    linarith [hemit.2, hret.1]
  refine ⟨h₁₂, sender_emitted A B hJ hħ hqA hr qB hemit.1 hemit.2,
    sender_returned A B hJ hħ hqA hr qB hret.1 hret.2, idealEchoReadings_radarSep hJ hħ, ?_, ?_, ?_⟩
  all_goals
    have he : |(echoReadings hK hT hc h₁₂).emit - (idealEchoReadings hJ hħ).emit|
        ≤ echoRadarBudget A B J ħ qA qB T := by
      rw [idealEchoReadings_emit]
      exact abs_echoReadings_emit_sub_le A B hJ hħ hr hK hT hc h₁₂ ht₁K hemit
    have hre : |(echoReadings hK hT hc h₁₂).ret - (idealEchoReadings hJ hħ).ret|
        ≤ echoRadarBudget A B J ħ qA qB T := by
      rw [idealEchoReadings_ret]
      exact abs_echoReadings_ret_sub_le A B hJ hħ hr hK hT hc h₁₂ ht₂K hret
  · exact RadarReadings.abs_radarTime_sub_le he hre
  · exact RadarReadings.abs_radarSep_sub_le he hre
  · exact RadarReadings.abs_radarDist_sub_le hc₀ he hre

end Radar

end CSD.RecordLayer

end
