/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MovingExchange
public import CsdLean4.CV.RadarCoordinates

/-!
# Radar coordinates of the moving observer's reflections

**Category:** 7-SigmaLayer (the record layer). BACKLOG #245 (the author's fourth operational-geometry
brief, step 5), for the control candidate (A).

~~#244~~ gave the observer at rest its emission and return records for every messenger reflected off
the moving observer. Here those records become **radar coordinates** in the brief's sense —
`T = (τ_emit + τ_return)/2`, `D = (τ_return − τ_emit)/2`, in clock units, through #184's
`RadarReadings` — and are matched to events. **An event is one physical record write** (#191): the
moving observer's reception write of messenger `k`. The observer at rest charts it from **its own**
emission and return writes for the same messenger; the moving observer charts it by its own clock at
its reception write.

## Exactly

* `radarOffset`; `ExchGeom.radar` (the readings at the completions of the two writes),
  `ExchGeom.bounceTime_sub_emitEnd`; ★★ `ExchGeom.radarTime_radar` — **the radar time is the bounce's
  time plus `radarOffset`**; ★★ `ExchGeom.radarSep_radar`;
* ★ `receptionEnd_eq` — **the detector's response delay**: the reception completes at `τ + 1/(2w)`;
* ★★★ `radar_at_rest` — **at relative rest the two charts agree exactly**: the radar time is the
  reception's completion and the separation is the distance over the messenger's speed;
* ★★ `radarOffset_strictAnti`; ★★★ `radarTime_ne_of_speed_ne` — **the control's negative**: two
  messengers of different speeds bouncing off the receding observer at the same event get different
  radar times. There is no preparation-independent chart.

## On the clocks

* ★ `handReading_mono`; `clockRadar` (the readings on the observer's own clock); ★★
  `abs_clockRadar_sub_le` — **propagated errors**: radar time and separation within the clock's error;
* ★★ `train_radar` — on `exchange_train`: radar time `41/16 + 3k/2`, separation `35/16 + k/2`, the
  reception at `(11 + 8k)/6`, **the charts disagreeing by `35/48 + k/6`**, growing with the distance;
* ★★★ `moving_radar` — the package: the readings *are* the two writes' completion times (the
  matching), the exact formula, the propagated errors, the moving observer's own reading of the same
  event, with the coverage conditions as hypotheses (the exchange inside each clock's horizon).

## Honest scope

⚠️ **Only the observer at rest charts events at a distance.** The moving observer charts the events
on its own worldline by its clock; its radar chart of events at the observer at rest (messengers it
launches, reflected there) is #257.

⚠️ **`D` is in clock units**; the length calibration `c₀` is #184's `radarDist`, kept separate as the
brief asks — and in the control no `c₀` is preparation-independent, by `radarTime_ne_of_speed_ne`.

⚠️ **This is the control (A).** The test candidate's charts (B) are part of #256.

References: `specs/BACKLOG.md` #245, #244, #246, #257, #256, #184, #191, #39; `CV/RadarCoordinates.lean`
(`RadarReadings`, `abs_radarTime_sub_le`, `abs_radarSep_sub_le`); `RecordLayer/MovingExchange.lean`
(`ExchGeom`, `emissionWrite`, `returnWrite`, `receptionWrite`, `exchange_train`);
`RecordLayer/HandClock.lean` (`handCount_mono`, `abs_handReading_sub_le`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The radar coordinates of a bounce, exactly -/

/-- **The radar time's offset from the bounce** when the moving observer is at `D` and recedes at
`y`, the messenger's speed relative to it being `w`: half the return leg's duration minus half the
outward leg's, measured from the window's edges. -/
noncomputable def radarOffset (D y w : ℝ) : ℝ := ((D + 1 / 2) / (w - y) - (D - 1 / 2) / (y + w)) / 2

namespace ExchGeom

variable {d y ρ w : ℝ} (h : ExchGeom d y ρ w)
include h

/-- **The first observer's radar readings of the bounce**, in the time of the dynamics: the
completion of its emission record and of its return record. -/
noncomputable def radar : RadarReadings :=
  ⟨exchEmitEnd d y ρ w, exchReturnEnd d y ρ w,
    h.emitEnd_le_bounceTime.trans (h.bounceTime_le_returnStart.trans h.returnStart_le_returnEnd)⟩

/-- The outward leg, from the window's edge to the bounce. -/
theorem bounceTime_sub_emitEnd :
    bounceTime ρ w - exchEmitEnd d y ρ w = (bounceSep d y ρ w - 1 / 2) / outSpeed y w := by
  have ha := h.out_pos
  rw [exchEmitEnd, eq_div_iff ha.ne', sub_mul, div_mul_cancel₀ _ ha.ne']
  linarith [h.start_add_bounce]

/-- ★★ **The radar time of the bounce**: the bounce's time plus `radarOffset`. -/
theorem radarTime_radar :
    h.radar.radarTime = bounceTime ρ w + radarOffset (bounceSep d y ρ w) y w := by
  have he := h.bounceTime_sub_emitEnd
  simp only [RadarReadings.radarTime, radar, exchReturnEnd, radarOffset, retSpeed, outSpeed] at he ⊢
  linarith

/-- ★★ **The radar separation of the bounce**: half the two legs' durations. -/
theorem radarSep_radar :
    h.radar.radarSep = ((bounceSep d y ρ w + 1 / 2) / retSpeed y w
      + (bounceSep d y ρ w - 1 / 2) / outSpeed y w) / 2 := by
  have he := h.bounceTime_sub_emitEnd
  simp only [RadarReadings.radarSep, radar, exchReturnEnd] at he ⊢
  linarith

end ExchGeom

/-- ★ **The detector's response delay**: the reception record completes half a cell after the bounce,
at `τ + 1/(2w)`. -/
theorem receptionEnd_eq {ρ w : ℝ} (hw : 0 < w) :
    (1 / 2 - ρ) / w = bounceTime ρ w + 1 / (2 * w) := by
  rw [bounceTime]
  field_simp
  ring

/-- ★★★ **At relative rest the two charts agree exactly**: the first observer's radar time of the
bounce is the time at which the moving observer's reception record completes, and its radar
separation is the separation over the messenger's speed. -/
theorem radar_at_rest {d ρ w : ℝ} (h : ExchGeom d 0 ρ w) :
    h.radar.radarTime = (1 / 2 - ρ) / w ∧ h.radar.radarSep = bounceSep d 0 ρ w / w := by
  have hw := h.w_pos
  refine ⟨?_, ?_⟩
  · rw [h.radarTime_radar, receptionEnd_eq hw, radarOffset, sub_zero, zero_add]
    congr 1
    field_simp
    ring
  · rw [h.radarSep_radar, retSpeed, outSpeed, sub_zero, zero_add]
    field_simp
    ring

/-- ★★ **The offset decreases strictly with the messenger's speed** when the observer recedes. -/
theorem radarOffset_strictAnti {D y w w' : ℝ} (hy : 0 < y) (hD : 1 / 2 ≤ D) (hw : y < w)
    (hww' : w < w') : radarOffset D y w' < radarOffset D y w := by
  have h1 : 0 < w - y := by linarith
  have h2 : 0 < w' - y := by linarith
  have h3 : 0 < y + w := by linarith
  have h4 : 0 < y + w' := by linarith
  have hX : (D + 1 / 2) / (w - y) - (D + 1 / 2) / (w' - y)
      = (D + 1 / 2) * ((w' - w) / ((w - y) * (w' - y))) := by
    field_simp
    ring
  have hY : (D - 1 / 2) / (y + w) - (D - 1 / 2) / (y + w')
      = (D - 1 / 2) * ((w' - w) / ((y + w) * (y + w'))) := by
    field_simp
    ring
  have hlt : (w' - w) / ((y + w) * (y + w')) < (w' - w) / ((w - y) * (w' - y)) :=
    div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)
  have hYpos : 0 < (w' - w) / ((y + w) * (y + w')) := div_pos (by linarith) (by positivity)
  have key : (D - 1 / 2) * ((w' - w) / ((y + w) * (y + w')))
      < (D + 1 / 2) * ((w' - w) / ((w - y) * (w' - y))) := by
    calc (D - 1 / 2) * ((w' - w) / ((y + w) * (y + w')))
        ≤ (D + 1 / 2) * ((w' - w) / ((y + w) * (y + w'))) :=
          mul_le_mul_of_nonneg_right (by linarith) hYpos.le
      _ < (D + 1 / 2) * ((w' - w) / ((w - y) * (w' - y))) :=
          mul_lt_mul_of_pos_left hlt (by linarith)
  unfold radarOffset
  linarith

/-- ★★★ **The control's negative: the radar chart depends on the messenger.** Two messengers of
different speeds that bounce off the receding observer at the same event — the same time, hence the
same place — are assigned **different radar times** by the observer at rest. There is no
preparation-independent chart: the messenger has no universal speed. -/
theorem radarTime_ne_of_speed_ne {d y ρ w ρ' w' : ℝ} (h : ExchGeom d y ρ w)
    (h' : ExchGeom d y ρ' w') (hy : 0 < y) (hτ : bounceTime ρ w = bounceTime ρ' w') (hww' : w < w') :
    h'.radar.radarTime < h.radar.radarTime := by
  rw [h.radarTime_radar, h'.radarTime_radar, ← hτ]
  have hD : bounceSep d y ρ' w' = bounceSep d y ρ w := by rw [bounceSep, bounceSep, hτ]
  rw [hD]
  have hw : y < w := by linarith [h.ret_pos, show retSpeed y w = w - y from rfl]
  linarith [radarOffset_strictAnti hy h.beyond hw hww']

/-! ### The charts read on the observers' clocks -/

section Clocks

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- ★ **Readings of the hand clock are monotone over its horizon.** -/
theorem handReading_mono (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf s q)
      ≤ handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf t q) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have htick : 0 ≤ tickTime K (handRate J ħ g hf q) := by
    unfold tickTime
    positivity
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast handCount_mono J ħ g hf hJ hħ hK hq hκ hs hst ht) htick

/-- **The first observer's radar readings on its own clock**: its clock read at the completion of its
emission record and of its return record (both within its horizon). -/
noncomputable def clockRadar (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {d y ρ w : ℝ} (h : ExchGeom d y ρ w)
    (hcov : exchReturnEnd d y ρ w ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    RadarReadings :=
  ⟨handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf (exchEmitEnd d y ρ w) q),
    handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf (exchReturnEnd d y ρ w) q),
    handReading_mono J ħ g hf hJ hħ hK hq hκ
      (h.emitStart_nonneg.trans h.emitStart_le_emitEnd) h.radar.emit_le_ret hcov⟩

/-- ★★ **Propagated errors**: the clock-read radar time and separation are within the clock's error
of the exact ones, when the exchange lies within the clock's horizon. -/
theorem abs_clockRadar_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {d y ρ w : ℝ} (h : ExchGeom d y ρ w)
    (hcov : exchReturnEnd d y ρ w ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |(clockRadar J ħ g hf hJ hħ hK hq hκ h hcov).radarTime - h.radar.radarTime|
        ≤ handClockErr J ħ g hf K q
      ∧ |(clockRadar J ħ g hf hJ hħ hK hq hκ h hcov).radarSep - h.radar.radarSep|
        ≤ handClockErr J ħ g hf K q := by
  have he := abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ
    (h.emitStart_nonneg.trans h.emitStart_le_emitEnd) (h.radar.emit_le_ret.trans hcov)
  have hr := abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ
    (h.emitStart_nonneg.trans (h.emitStart_le_emitEnd.trans h.radar.emit_le_ret)) hcov
  exact ⟨RadarReadings.abs_radarTime_sub_le he hr, RadarReadings.abs_radarSep_sub_le he hr⟩

end Clocks

/-! ### The train -/

/-- ★★ **The train's charts disagree increasingly**: for messenger `k` of `exchange_train`, the
observer at rest assigns radar time `41/16 + 3k/2` and separation `35/16 + k/2` to the bounce,
whose reception record completes at `(11 + 8k)/6`: the radar time runs ahead of the reception by
`35/48 + k/6`, growing with the distance. -/
theorem train_radar (k : ℝ) (hk : 0 ≤ k) :
    ((exchange_train k hk).1.radar.radarTime = 41 / 16 + 3 * k / 2)
      ∧ ((exchange_train k hk).1.radar.radarSep = 35 / 16 + k / 2)
      ∧ (1 / 2 - (-5 - 4 * k)) / 3 = (11 + 8 * k) / 6
      ∧ (exchange_train k hk).1.radar.radarTime - (1 / 2 - (-5 - 4 * k)) / 3 = 35 / 48 + k / 6 := by
  obtain ⟨_, -, he, -, hr⟩ := exchange_train k hk
  have hT : (exchange_train k hk).1.radar.radarTime = 41 / 16 + 3 * k / 2 := by
    simp only [RadarReadings.radarTime, ExchGeom.radar, he, hr]
    ring
  refine ⟨hT, ?_, by ring, ?_⟩
  · simp only [RadarReadings.radarSep, ExchGeom.radar, he, hr]
    ring
  · rw [hT]
    ring

/-! ### The package -/

section Capstone

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ) {N : ℕ}

/-- ★★★ **Radar coordinates of the moving observer's reflections (#245).** For each messenger `k` of
`moving_exchange`, the **event** is the reflection, recorded by the moving observer's reception
write. The observer at rest charts it by its own clock read at the completions of **its own emission
and return writes for the same messenger** — the readings are those writes' completion times —
within its clock error of the exact radar time `τ + radarOffset` and separation; the moving observer
charts the same event by its own clock at its reception write's completion, `τ + 1/(2w)`, within its
clock error. Coverage: the exchange inside the first clock's horizon, the reception inside the
second's. -/
theorem moving_radar (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (hK : 0 < K) {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) {x : ExchArena N}
    (hx₁ : x.2.1.1 = (msgPoint 1, q₁)) (hS : x.2.2.2.1 = 0) (k : Fin N)
    (hG : ExchGeom (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2)
    (hcov₀ : exchReturnEnd (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2
      ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (hcov₁ : (1 / 2 - (x.2.2.1 k).1) / (x.2.2.1 k).2
      ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁)) {Ks : ℕ}
    (site : Finset (Fin Ks)) :
    hG.radar.emit = (emissionWrite J ħ g hf m gd hf1 hgd site k x (congrFun hS k) hG).writeEnd
    ∧ hG.radar.ret = (returnWrite J ħ g hf m gd hf1 hgd site k x (congrFun hS k) hG).writeEnd
    ∧ hG.radar.radarTime = bounceTime (x.2.2.1 k).1 (x.2.2.1 k).2
        + radarOffset (bounceSep (exchSep x) (exchSepVel m x) (x.2.2.1 k).1 (x.2.2.1 k).2)
          (exchSepVel m x) (x.2.2.1 k).2
    ∧ |(clockRadar J ħ g hf hJ hħ hK hq₀ hκ₀ hG hcov₀).radarTime - hG.radar.radarTime|
        ≤ handClockErr J ħ g hf K q₀
    ∧ |(clockRadar J ħ g hf hJ hħ hK hq₀ hκ₀ hG hcov₀).radarSep - hG.radar.radarSep|
        ≤ handClockErr J ħ g hf K q₀
    ∧ (1 / 2 - (x.2.2.1 k).1) / (x.2.2.1 k).2
        = bounceTime (x.2.2.1 k).1 (x.2.2.1 k).2 + 1 / (2 * (x.2.2.1 k).2)
    ∧ |handReading K (tickTime K (handRate J ħ g hf q₁))
          (exchFlow J ħ g hf m gd ((1 / 2 - (x.2.2.1 k).1) / (x.2.2.1 k).2) x).2.1.1.2
        - (1 / 2 - (x.2.2.1 k).1) / (x.2.2.1 k).2| ≤ handClockErr J ħ g hf K q₁ := by
  have hc := abs_clockRadar_sub_le J ħ g hf hJ hħ hK hq₀ hκ₀ hG hcov₀
  refine ⟨rfl, rfl, hG.radarTime_radar, hc.1, hc.2, receptionEnd_eq hG.w_pos, ?_⟩
  exact abs_movingObsReading_sub_le J ħ g hf m gd hJ hħ hK hq₁ hκ₁ hx₁
    (div_nonneg (by linarith [hG.behind]) hG.w_pos.le) hcov₁

end Capstone

end CSD.RecordLayer

end
