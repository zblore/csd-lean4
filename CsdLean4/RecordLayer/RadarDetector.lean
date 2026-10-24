/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CoupledReception
public import CsdLean4.CV.RadarCoordinates

/-!
# Radar with a detector: the activated reception read as a radar coordinate

**Category:** 7-SigmaLayer (the record layer). BACKLOG #197 (out of #39; the last row of the
author's second operational-geometry brief, #191–#197; the brief's §7).

#187 read radar coordinates off a clock whose registers were written by a schedule. Here the
reception is #196's: the detector at `B` is set in motion by the arriving carrier and completes its
write over an interval, so the reading at the detection is later than the arrival by a **detector
delay**, and the carrier it reads arrived under the detuning its own back-reaction imposed. Every
contribution to the radar error is derived for this witness; the two input bounds are labelled.

* `transferError`, ★ `abs_detunedHopTime_sub_hopTime_le` — **the transfer error**: the detuned
  arrival `πħ/(2Ω)` differs from #183's `τ_hop = πħ/(2J)` by at most `πħ Δ²/(16 J³)`;
* `detectorDelay` — **the detector delay of the witness**, the completion of the write minus the
  detuned arrival, `2/(3κ) + 1/(2ω) − π/(2ω)`, explicit in the preparation's `κ` and `ω`;
* `detectorReadings`, `detectorReadings_emit`, ★★ `abs_detectorReadings_ret_sub_le` — **the
  measured readings** are the arena clock at the emission (`0`, exactly) and at a reading time inside
  the retention window; the return reading is within
  `T + retention + |detectorDelay| + transferError` of `τ_hop`: clock resolution
  (`abs_tickReading_sub_lt`, derived), the retention window (input bound: the reading is taken while
  the record displays), the detector delay (derived), the transfer error (derived);
* ★★★ `radar_with_detector` — **one bound on radar time, separation and distance** through
  `abs_radarTime_sub_le` / `abs_radarSep_sub_le` / `abs_radarDist_sub_le` against the ideal one-way
  readings `(0, τ_hop)`, with the record displayed at the reading time;
* ★ `radarTime_delayed`, `radarSep_delayed` — **the interpretation**: a detector with response
  time `d` shifts both radar coordinates by `d/2`; the shift is a property of the detector, read off
  the coordinates, not of the signal.

## Honest scope

* **One clock, at `A`, and a one-way flight.** The "return" reading is the detection, so the radar
  separation is half the time of flight plus half the detector delay. Nothing here is an echo; the
  echo witness is #187's and stands.
* **No universal `c`, no Lorentz invariance.** `c₀` is a calibration constant (`radarDist`), the
  hop time is the exchange's own, and the arena has no metric. The #187 and #190 headers stand.
* The input bounds are the retention window (the reading is taken while the record displays) and
  the clock horizon (`t ≤ K T`); everything else is derived from the witness.

References: `specs/BACKLOG.md` #197, #196, #194, #187, #189, #185, #183, #39;
`CV/RadarCoordinates.lean` (`RadarReadings`, `abs_radarTime_sub_le`, `abs_radarSep_sub_le`,
`abs_radarDist_sub_le`, `ofDuration`), `RecordLayer/RecordClock.lean` (`abs_tickReading_sub_lt`,
`tickCount_mono`, `tickCount_at_period`), `RecordLayer/CoupledReception.lean` (`rabiFreq_sub_le`),
`RecordLayer/ActivatedWrite.lean` (`writeEnd`, `retention`, `message_one_displayed`),
`CV/DetunedExchange.lean` (`detunedHopTime`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The transfer error -/

/-- The transfer error of the detuned arrival: `πħ Δ²/(16 J³)`. -/
noncomputable def transferError (J ħ Δ : ℝ) : ℝ := Real.pi * ħ * Δ ^ 2 / (16 * J ^ 3)

theorem transferError_nonneg {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    0 ≤ transferError J ħ Δ := by
  unfold transferError
  have := Real.pi_pos
  positivity

/-- ★ **The transfer error**: the detuned arrival `πħ/(2Ω)` is within `πħ Δ²/(16 J³)` of #183's
`τ_hop = πħ/(2J)`. -/
theorem abs_detunedHopTime_sub_hopTime_le {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (Δ : ℝ) :
    |detunedHopTime J ħ Δ - hopTime J ħ| ≤ transferError J ħ Δ := by
  have hΩ := rabiFreq_pos hJ Δ
  have hJΩ := le_rabiFreq hJ.le Δ
  have hsub := rabiFreq_sub_le hJ Δ
  have hpi := Real.pi_pos
  have heq : detunedHopTime J ħ Δ - hopTime J ħ
      = -(Real.pi * ħ * (rabiFreq J Δ - J) / (2 * J * rabiFreq J Δ)) := by
    unfold detunedHopTime hopTime
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) (by linarith))
    (by positivity)), transferError, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (rabiFreq J Δ - J) * (8 * J) ≤ Δ ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at hsub
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.pi * ħ * (2 * J ^ 2)),
    mul_le_mul_of_nonneg_left hJΩ (by positivity : (0 : ℝ) ≤ Real.pi * ħ * Δ ^ 2 * 2 * J)]

/-! ### The interpretation: a detector delay shifts both coordinates by half of itself -/

/-- One-way readings with the detection delayed by `d`. -/
theorem radarTime_delayed (τ : ℝ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (RadarReadings.ofDuration τ (a + d) (by linarith)).radarTime
      = (RadarReadings.ofDuration τ a ha).radarTime + d / 2 := by
  unfold RadarReadings.radarTime RadarReadings.ofDuration
  ring

/-- ★ **A detector of response time `d` shifts the radar separation by `d/2`**: the shift is a
property of the detector, and it is read off the coordinate. -/
theorem radarSep_delayed (τ : ℝ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (RadarReadings.ofDuration τ (a + d) (by linarith)).radarSep
      = (RadarReadings.ofDuration τ a ha).radarSep + d / 2 := by
  unfold RadarReadings.radarSep RadarReadings.ofDuration
  ring

/-! ### The witness: the activated reception read on the arena clock -/

section Witness

variable {K : ℕ} {f : ℝ → ℝ} {J ħ : ℝ} (g : ℝ) (hf : Function.Periodic f 1)

/-- **The detector delay of the witness**: the completion of the write minus the detuned arrival,
`2/(3κ) + 1/(2ω) − π/(2ω)`. -/
noncomputable def detectorDelay (J ħ g : ℝ) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) :
    ℝ :=
  writeEnd (driftRate J ħ g hf φ) (rabiRate J ħ (detuningAt g hf φ))
    - detunedHopTime J ħ (detuningAt g hf φ)

theorem detectorDelay_eq (hJ : 0 < J) (φ : AddCircle (1 : ℝ)) :
    detectorDelay J ħ g hf φ
      = 2 / (3 * driftRate J ħ g hf φ) + 1 / (2 * rabiRate J ħ (detuningAt g hf φ))
        - Real.pi / (2 * rabiRate J ħ (detuningAt g hf φ)) := by
  have hΩ := (rabiFreq_pos hJ (detuningAt g hf φ)).ne'
  unfold detectorDelay writeEnd detunedHopTime rabiRate
  field_simp

/-- **The measured readings**: the arena clock at the emission (time `0`) and at the reading time
`t`. The domain condition is the monotonicity of the tick count. -/
noncomputable def detectorReadings (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t : ℝ} (ht : 0 ≤ t) : RadarReadings :=
  ⟨tickReading T (clockEvolve T 0 0 c), tickReading T (clockEvolve T 0 t c),
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 (tickCount_mono hK hT hc ht)) hT.le⟩

/-- The emission reading is exactly `0`: a ready clock has not ticked at the switch-on. -/
theorem detectorReadings_emit (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t : ℝ} (ht : 0 ≤ t) :
    (detectorReadings hK hT hc ht).emit = 0 := by
  show tickReading T (clockEvolve T 0 0 c) = 0
  have h := tickCount_at_period hK hT hc (m := 0) (Nat.zero_le _)
  rw [Nat.cast_zero, zero_mul] at h
  rw [tickReading, h, Nat.cast_zero, zero_mul]

theorem detectorReadings_ret (hK : 0 < K) {T : ℝ} (hT : 0 < T) {c : ClockArena K}
    (hc : c ∈ ClockReady K) {t : ℝ} (ht : 0 ≤ t) :
    (detectorReadings hK hT hc ht).ret = tickReading T (clockEvolve T 0 t c) := rfl

/-- The ideal one-way readings: emission at `0`, arrival at #183's `τ_hop`. -/
noncomputable def idealReadings (hJ : 0 < J) (hħ : 0 < ħ) : RadarReadings :=
  RadarReadings.ofDuration 0 (hopTime J ħ) (hopTime_pos hJ hħ).le

theorem idealReadings_emit (hJ : 0 < J) (hħ : 0 < ħ) : (idealReadings (J := J) (ħ := ħ) hJ hħ).emit = 0 := rfl

theorem idealReadings_ret (hJ : 0 < J) (hħ : 0 < ħ) :
    (idealReadings (J := J) (ħ := ħ) hJ hħ).ret = hopTime J ħ := by
  show (0 : ℝ) + hopTime J ħ = hopTime J ħ
  rw [zero_add]

/-- The total error budget of the witness. -/
noncomputable def radarBudget (J ħ g : ℝ) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ))
    (T : ℝ) : ℝ :=
  T + retention (driftRate J ħ g hf φ) (rabiRate J ħ (detuningAt g hf φ))
    + |detectorDelay J ħ g hf φ| + transferError J ħ (detuningAt g hf φ)

/-- ★★ **The return reading is within the budget of `τ_hop`.** Clock resolution (derived), the
retention window (input: the reading is taken while the record displays), the detector delay
(derived), the transfer error (derived). -/
theorem abs_detectorReadings_ret_sub_le (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) {T : ℝ}
    (hT : 0 < T) {c : ClockArena K} (hc : c ∈ ClockReady K) {q : LF4.KTorus} {t : ℝ} (ht : 0 ≤ t)
    (htK : t ≤ K * T)
    (hdet : writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ t
      ∧ t ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
        + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) :
    |(detectorReadings hK hT hc ht).ret - hopTime J ħ| ≤ radarBudget J ħ g hf q.2 T := by
  rw [detectorReadings_ret, radarBudget]
  have h1 := abs_tickReading_sub_lt hK hT hc ht htK
  have h2 : |t - writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))|
      ≤ retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) := by
    rw [abs_le]
    constructor <;> linarith [hdet.1, hdet.2]
  have h3 : |writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
      - detunedHopTime J ħ (detuningAt g hf q.2)| = |detectorDelay J ħ g hf q.2| := rfl
  have h4 := abs_detunedHopTime_sub_hopTime_le hJ hħ (detuningAt g hf q.2)
  calc |tickReading T (clockEvolve T 0 t c) - hopTime J ħ|
      ≤ |tickReading T (clockEvolve T 0 t c) - t| + |t - hopTime J ħ| := abs_sub_le _ _ _
    _ ≤ |tickReading T (clockEvolve T 0 t c) - t|
        + (|t - writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))|
          + |writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
              - hopTime J ħ|) := by gcongr; exact abs_sub_le _ _ _
    _ ≤ |tickReading T (clockEvolve T 0 t c) - t|
        + (|t - writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))|
          + (|writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
              - detunedHopTime J ħ (detuningAt g hf q.2)|
            + |detunedHopTime J ħ (detuningAt g hf q.2) - hopTime J ħ|)) := by
          gcongr; exact abs_sub_le _ _ _
    _ ≤ _ := by rw [h3]; linarith [h1.le, h2, h4]

/-- ★★★ **Radar with a detector.** Against the ideal one-way readings `(0, τ_hop)`, the measured
radar time, separation and distance are within the budget `T + retention + |detectorDelay| +
transferError` (times `c₀` for the distance), the emission reading is exactly `0`, and the record
displays at the reading time. -/
theorem radar_with_detector (hJ : 0 < J) (hħ : 0 < ħ) (hK : 0 < K) {T : ℝ} (hT : 0 < T)
    {c : ClockArena K} (hc : c ∈ ClockReady K) {q : LF4.KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 < driftRate J ħ g hf q.2) {t : ℝ} (ht : 0 ≤ t) (htK : t ≤ K * T)
    (hdet : writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ t
      ∧ t ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
        + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)))
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    (detectorReadings hK hT hc ht).emit = 0
      ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 ∈ displayArc
      ∧ |(detectorReadings hK hT hc ht).radarTime - (idealReadings hJ hħ).radarTime|
          ≤ radarBudget J ħ g hf q.2 T
      ∧ |(detectorReadings hK hT hc ht).radarSep - (idealReadings hJ hħ).radarSep|
          ≤ radarBudget J ħ g hf q.2 T
      ∧ |(detectorReadings hK hT hc ht).radarDist c₀ - (idealReadings hJ hħ).radarDist c₀|
          ≤ c₀ * radarBudget J ħ g hf q.2 T := by
  have hbud : 0 ≤ radarBudget J ħ g hf q.2 T := by
    unfold radarBudget
    have := transferError_nonneg hJ hħ (detuningAt g hf q.2)
    have := abs_nonneg (detectorDelay J ħ g hf q.2)
    have hret : 0 ≤ retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) := by
      linarith [hdet.1, hdet.2]
    linarith
  have he : |(detectorReadings hK hT hc ht).emit - (idealReadings hJ hħ).emit|
      ≤ radarBudget J ħ g hf q.2 T := by
    rw [detectorReadings_emit, idealReadings_emit, sub_zero, abs_zero]
    exact hbud
  have hr : |(detectorReadings hK hT hc ht).ret - (idealReadings hJ hħ).ret|
      ≤ radarBudget J ħ g hf q.2 T := by
    rw [idealReadings_ret]
    exact abs_detectorReadings_ret_sub_le g hf hJ hħ hK hT hc ht htK hdet
  exact ⟨detectorReadings_emit hK hT hc ht, message_one_displayed g hf hJ hħ hq hκ hdet.1 hdet.2,
    RadarReadings.abs_radarTime_sub_le he hr, RadarReadings.abs_radarSep_sub_le he hr,
    RadarReadings.abs_radarDist_sub_le hc₀ he hr⟩

end Witness

end CSD.RecordLayer

end
