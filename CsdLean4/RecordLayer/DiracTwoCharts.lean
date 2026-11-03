/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracBRadar
public import CsdLean4.RecordLayer.DiracWorldline

/-!
# Both observers' charts of two common events, and the Lorentz map between them

**Category:** 7-SigmaLayer (the record layer). BACKLOG #278, third and fourth landings; #280, the
scaling law.

`dirac_b_radar` gives, in one evolution, `B`'s emission and return, `A`'s relay firing `R` and the
meeting `M` of the two observers, with both clocks' ticks. `R` and `M` are the common events: both
observers chart both of them from their own records.

* **`A`'s chart**: `R` and `M` are on `A`'s worldline — position `0`, times read off `A`'s clock
  (`R` between `A`'s ticks `46`–`48`, `M` between `76`–`81`).
* **`B`'s chart**: `M` is on `B`'s worldline — position `0`, time between `B`'s ticks `61`–`65`;
  `R` is charted by radar — `B`'s readings `e` of its emission (ticks `2`–`3`) and `r` of its return
  (ticks `44`–`50`), time `(e + r)/2`, position `(r − e)/2`: the messenger moves at `c = 1` both
  ways in `B`'s frame. That isotropy is `B`'s convention (Einstein's), and it is part of what
  landing 4 tests.

## The charts

* `bRadarPos` (`B`'s radar position, messenger speed `1` both ways); `radarTime` and `minkowskiSq`
  are `DiracWorldline.lean`'s;
* ★★ `two_chart_bounds` — **from whole-tick readings in the records' brackets**: in `A`'s chart `R`
  is `28`–`35` periods before `M` at position `0`; in `B`'s chart `R` is `34.5`–`42` periods before
  `M`, `20.5`–`24` light-periods away; the squared intervals are `[784, 1225]` in `A`'s chart and
  `[2457/4, 5375/4]` in `B`'s, the first inside the second.

## The map

* `lorentzBoost_approach` (the boost at `−3/5` of an event at `A`, `D` before the meeting:
  `(−(5/4) D, −(3/4) D)`);
* ★★★ `lorentz_chart_bounds` — **the Lorentz boost of `A`'s chart lands within `37/4` periods in
  time and `23/4` light-periods in position of `B`'s radar chart**, for every reading in the
  brackets (Lorentz values `≈ 39.8`, `≈ 23.9`).

## The scaling law (#280)

* ★★★ `radar_lorentz_exact` (**Einstein's radar with a dilated clock is the Lorentz boost**: for an
  observer approaching at any `v ∈ [0, 1)`, messengers at speed `1` and a clock at
  `s = √(1 − v²)`, the radar coordinates of the other's event relative to the meeting are exactly
  the boost at `−v` of `(t_R − t_M, 0)` — symbolic, no arena numbers);
* ★★★ `radar_lorentz_error` (**the Lorentz residual is linear in the reading errors**:
  `(d_E + d_Ret)/2 + d_MB + (d_R + d_MA)/s` in time, `(d_E + d_Ret)/2 + v (d_R + d_MA)/s` in
  position); `abs_record_sub_le` (a record in `encounter_record_window`'s window is within
  `y/Ω + θ/κ` of its encounter — each record's reading error);
* ★★★ `radar_lorentz_scaling` (**the scaling law**: for every `ε > 0` there is a reading
  resolution below which the radar chart is within `ε` of the Lorentz boost — so along any family
  of finer records and clocks the Lorentz residuals tend to `0`).

## The capstone

* ★★★ `dirac_two_charts` — the tick brackets of `dirac_b_radar` (one evolution), the chart
  bounds for every reading in them, and the Lorentz map between the charts within the errors.

## The finding

**Both charts of the two common events exist from the records of one evolution, and the Lorentz
map carries one to the other within the records' resolution**: `≈ 23%` in time, `≈ 24%` in
position; the intervals agree within the brackets (`A`'s `[784, 1225]` inside `B`'s
`[614.25, 1343.75]`; the Lorentz value `(2·10¹³ / 2π·10¹¹)² ≈ 1013` lies in both). The errors are
the width of the event records' windows (`B`'s return `3.7·10¹²`, the meeting `2.2·10¹²`), not the
tick spacing: continuous clock readings would bring them only to `≈ 17–20%` (estimate). Σ's time is
continuous and the dynamics are Lorentzian exactly (`clock_rate_lorentz`, `dirac_massless_limit`);
what the records add is finite resolution — deriving it from the physical localisation limits, and
shrinking it, is #280.

## Honest scope

⚠️ **Discriminating power is modest at this resolution**: the Galilean map (`ΔT_B = ΔT_A`,
`ΔX_B = (3/5) ΔT_A`) also meets the brackets (at `ΔT ∈ [34.5, 35]`, `ΔX ∈ [20.7, 21]`); `B`'s clock
rate excludes it at the dynamics level (`clock_rate_lorentz`, #259). The target is Lorentz within
explicit errors, not the exclusion.

⚠️ **`B`'s emission record lags its event**: `B`'s register needs `≈ 2.1·10¹²` of encounter to
reach its threshold, so the emission is recorded two to three ticks after the messenger leaves `B`
(the bracket `[2, 3]` covers the record, not the departure). The chart uses records, so the lag is
inside the bounds; `B` does not correct for it.

⚠️ **The scaling law is kinematic**: `radar_lorentz_exact` takes the messenger at exactly `1` and
the clock at exactly `√(1 − v²)`; on the chain they hold to `dirac_massless_limit`'s `O((ap)²)` and
`clock_rate_lorentz`'s `2.5·10⁻⁴`, which enter `radar_lorentz_error` as reading errors (rate error
times elapsed time). The family along which every error shrinks is not instantiated on the arenas;
its ingredients are `DiracResolution.lean`'s tails and record windows.

⚠️ **Two events only**: `R` and `M`. `B`'s speed calibration (a round trip to a relay at known
proper distance) is not done; the isotropy of `B`'s messenger is assumed in `bRadarPos`.

References: `specs/BACKLOG.md` #278, #280, #248, #259, #277, #274, #256, #39;
`RecordLayer/DiracBRadar.lean` (`dirac_b_radar`, `bMeeting`); `RecordLayer/DiracWorldline.lean`
(`radarTime`, `minkowskiSq`, `dirac_lorentz_worldline`, `clock_rate_lorentz`);
`RecordLayer/DiracRadar.lean` (`dirac_radar`); `RecordLayer/DiracResolution.lean`
(`encounter_record_window`, `sine_packet_tail`, `sine_massless_tail`);
`RecordLayer/GalileanTransformation.lean`
(`lorentzBoost`); `CV/DiracMassless.lean` (`dirac_massless_limit`).
-/

@[expose] public section

namespace CSD.RecordLayer

open Set

/-- `B`'s radar position of an event, from its readings `e` of the emission and `r` of the return,
the messenger moving at `1` both ways in `B`'s frame. -/
noncomputable def bRadarPos (e r : ℝ) : ℝ := (r - e) / 2

/-- ★★ **Both charts of the reception and the meeting, from whole-tick readings.** For readings in
the brackets the records give — `B`'s emission between its ticks `2` and `3`, its return between
`44` and `50`, the meeting between `61` and `65`; `A`'s reception between `A`'s ticks `46` and `48`,
the meeting between `76` and `81` — in `A`'s chart the reception is `28`–`35` periods before the
meeting, in `B`'s chart `34.5`–`42` periods before it and `20.5`–`24` light-periods away; `A`'s
squared interval lies in `[784, 1225]`, `B`'s in `[2457/4, 5375/4]`. -/
theorem two_chart_bounds {e r μ ρ m : ℝ} (he : e ∈ Icc (2 : ℝ) 3) (hr : r ∈ Icc (44 : ℝ) 50)
    (hμ : μ ∈ Icc (61 : ℝ) 65) (hρ : ρ ∈ Icc (46 : ℝ) 48) (hm : m ∈ Icc (76 : ℝ) 81) :
    28 ≤ m - ρ ∧ m - ρ ≤ 35
    ∧ 69 / 2 ≤ μ - radarTime e r ∧ μ - radarTime e r ≤ 42
    ∧ 41 / 2 ≤ bRadarPos e r ∧ bRadarPos e r ≤ 24
    ∧ 784 ≤ minkowskiSq (m - ρ) 0 ∧ minkowskiSq (m - ρ) 0 ≤ 1225
    ∧ 2457 / 4 ≤ minkowskiSq (μ - radarTime e r) (bRadarPos e r)
    ∧ minkowskiSq (μ - radarTime e r) (bRadarPos e r) ≤ 5375 / 4 := by
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hμ1, hμ2⟩ := hμ
  obtain ⟨hρ1, hρ2⟩ := hρ
  obtain ⟨hm1, hm2⟩ := hm
  have hA1 : 28 ≤ m - ρ := by linarith
  have hA2 : m - ρ ≤ 35 := by linarith
  have hT1 : 69 / 2 ≤ μ - radarTime e r := by unfold radarTime; linarith
  have hT2 : μ - radarTime e r ≤ 42 := by unfold radarTime; linarith
  have hX1 : 41 / 2 ≤ bRadarPos e r := by unfold bRadarPos; linarith
  have hX2 : bRadarPos e r ≤ 24 := by unfold bRadarPos; linarith
  refine ⟨hA1, hA2, hT1, hT2, hX1, hX2, ?_, ?_, ?_, ?_⟩ <;> unfold minkowskiSq <;> nlinarith

/-! ### The map -/

/-- **The Lorentz boost into `B`'s frame**: with the meeting as origin and `A` at position `0`,
`B` moves at `−3/5` in `A`'s chart; an event at `A`, `D` before the meeting, goes to time
`−(5/4) D` and position `−(3/4) D`. -/
theorem lorentzBoost_approach (D : ℝ) :
    lorentzBoost 1 (-(3 / 5)) (-D, 0) = (-(5 / 4 * D), -(3 / 4 * D)) := by
  have hs : Real.sqrt (1 - (-(3 / 5 : ℝ)) ^ 2 / 1 ^ 2) = 4 / 5 := by
    rw [show (1 : ℝ) - (-(3 / 5)) ^ 2 / 1 ^ 2 = (4 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [lorentzBoost, hs, Prod.mk.injEq]
  constructor <;> ring

/-- ★★★ **The Lorentz map between the two charts, within explicit errors** (BACKLOG #278, fourth
landing). For readings in the records' brackets, the Lorentz boost at `−3/5` of `A`'s chart of the
relay firing `R` (meeting at the origin, `R` at `A`, `m − ρ` before the meeting) lands within
`37/4` periods in time and `23/4` light-periods in position of `B`'s radar chart of `R` (time
`−(μ − (e + r)/2)`, position `−(r − e)/2`: `A` is on `B`'s negative side). The Lorentz values are
`≈ 39.8` and `≈ 23.9`: the errors are `≈ 23%` and `≈ 24%`, set by the records' windows. -/
theorem lorentz_chart_bounds {e r μ ρ m : ℝ} (he : e ∈ Icc (2 : ℝ) 3) (hr : r ∈ Icc (44 : ℝ) 50)
    (hμ : μ ∈ Icc (61 : ℝ) 65) (hρ : ρ ∈ Icc (46 : ℝ) 48) (hm : m ∈ Icc (76 : ℝ) 81) :
    |(lorentzBoost 1 (-(3 / 5)) (-(m - ρ), 0)).1 - (-(μ - radarTime e r))| ≤ 37 / 4
    ∧ |(lorentzBoost 1 (-(3 / 5)) (-(m - ρ), 0)).2 - (-bRadarPos e r)| ≤ 23 / 4 := by
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hμ1, hμ2⟩ := hμ
  obtain ⟨hρ1, hρ2⟩ := hρ
  obtain ⟨hm1, hm2⟩ := hm
  rw [lorentzBoost_approach]
  unfold radarTime bRadarPos
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-! ### The scaling law: Lorentz within the records' resolution, at any parameters -/

/-- ★★★ **Einstein's radar with a dilated clock is the Lorentz boost.** An observer `B` meeting `A`
at time `t_M` while approaching at speed `v ∈ [0, 1)` sends a messenger at speed `1` at `t_E` that
reaches `A` at `t_R` (`t_R − t_E = v (t_M − t_E)`, the separation at emission) and receives its
echo at `t_Ret` (`t_Ret − t_R = v (t_M − t_Ret)`). With `B`'s clock running at
`s = √(1 − v²)`, `B`'s radar time of `A`'s event relative to the meeting,
`s (t_E + t_Ret)/2 − s t_M`, and its radar position `−s (t_Ret − t_E)/2` (`A` on `B`'s negative
side) are exactly the Lorentz boost at `−v` of `A`'s chart `(t_R − t_M, 0)`. -/
theorem radar_lorentz_exact {v tE tR tRet tM : ℝ} (hv0 : 0 ≤ v) (hv : v < 1)
    (hE : tR - tE = v * (tM - tE)) (hRet : tRet - tR = v * (tM - tRet)) :
    lorentzBoost 1 (-v) (tR - tM, 0)
      = (Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2) - Real.sqrt (1 - v ^ 2) * tM,
        -(Real.sqrt (1 - v ^ 2) * ((tRet - tE) / 2))) := by
  have h1v : 0 < 1 - v := by linarith
  have h1v' : 0 < 1 + v := by linarith
  have hs2 : Real.sqrt (1 - v ^ 2) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have heE : tE - tM = (tR - tM) / (1 - v) := by
    field_simp
    linarith
  have heR : tRet - tM = (tR - tM) / (1 + v) := by
    field_simp
    linarith
  have hsq : Real.sqrt (1 - (-v) ^ 2 / 1 ^ 2) = Real.sqrt (1 - v ^ 2) := by
    congr 1
    ring
  simp only [lorentzBoost, hsq, Prod.mk.injEq]
  constructor
  · rw [show Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2) - Real.sqrt (1 - v ^ 2) * tM
        = Real.sqrt (1 - v ^ 2) * ((tE - tM) + (tRet - tM)) / 2 by ring, heE, heR]
    field_simp
    rw [hs2]
    ring
  · rw [show tRet - tE = (tRet - tM) - (tE - tM) by ring, heE, heR]
    field_simp
    rw [hs2]
    ring

/-- ★★★ **The Lorentz residual is linear in the reading errors.** If `B`'s readings `e`, `r`, `μ`
are within `d_E`, `d_Ret`, `d_MB` of its proper times of the emission, the return and the meeting,
and `A`'s readings `ρ`, `m` within `d_R`, `d_MA` of the relay event and the meeting, the Lorentz
boost of `A`'s chart lands within `(d_E + d_Ret)/2 + d_MB + (d_R + d_MA)/s` in time and
`(d_E + d_Ret)/2 + v (d_R + d_MA)/s` in position of `B`'s radar chart. -/
theorem radar_lorentz_error {v tE tR tRet tM e r μ ρ m dE dRet dMB dR dMA : ℝ} (hv0 : 0 ≤ v)
    (hv : v < 1) (hE : tR - tE = v * (tM - tE)) (hRet : tRet - tR = v * (tM - tRet))
    (he : |e - Real.sqrt (1 - v ^ 2) * tE| ≤ dE)
    (hr : |r - Real.sqrt (1 - v ^ 2) * tRet| ≤ dRet)
    (hμ : |μ - Real.sqrt (1 - v ^ 2) * tM| ≤ dMB) (hρ : |ρ - tR| ≤ dR) (hm : |m - tM| ≤ dMA) :
    |(lorentzBoost 1 (-v) (ρ - m, 0)).1 - ((e + r) / 2 - μ)|
        ≤ (dE + dRet) / 2 + dMB + (dR + dMA) / Real.sqrt (1 - v ^ 2)
    ∧ |(lorentzBoost 1 (-v) (ρ - m, 0)).2 - (-((r - e) / 2))|
        ≤ (dE + dRet) / 2 + v * (dR + dMA) / Real.sqrt (1 - v ^ 2) := by
  have hs0 : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hx := radar_lorentz_exact hv0 hv hE hRet
  have hsq : Real.sqrt (1 - (-v) ^ 2 / 1 ^ 2) = Real.sqrt (1 - v ^ 2) := by
    congr 1
    ring
  have hb : ∀ p : ℝ × ℝ, lorentzBoost 1 (-v) p
      = ((p.1 + v * p.2) / Real.sqrt (1 - v ^ 2), (p.2 + v * p.1) / Real.sqrt (1 - v ^ 2)) :=
    fun p => by
      simp only [lorentzBoost, hsq, Prod.mk.injEq]
      constructor <;> ring
  rw [hb] at hx ⊢
  simp only [Prod.mk.injEq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  simp only [mul_zero, add_zero, zero_add] at hx1 hx2 ⊢
  set s := Real.sqrt (1 - v ^ 2)
  have hd : |(ρ - m) - (tR - tM)| ≤ dR + dMA := by
    rw [show (ρ - m) - (tR - tM) = (ρ - tR) - (m - tM) by ring]
    exact (abs_sub _ _).trans (add_le_add hρ hm)
  have hd1 : |(ρ - m) / s - (tR - tM) / s| ≤ (dR + dMA) / s := by
    rw [← sub_div, abs_div, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right hd hs0.le
  have hd2 : |v * (ρ - m) / s - v * (tR - tM) / s| ≤ v * (dR + dMA) / s := by
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_nonneg hv0, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hv0) hs0.le
  rw [abs_le] at he hr hμ hd1 hd2 ⊢
  rw [abs_le]
  constructor <;> constructor <;> nlinarith

/-- **A record locates its encounter.** A record in `encounter_record_window`'s window
`[t_c − y/Ω + 2θ, t_c − h + θ/κ]` (`h ≥ 0`, `θ ≥ 0`) is within `y/Ω + θ/κ` of the encounter time
`t_c`: the reading error each record contributes to `radar_lorentz_error`. -/
theorem abs_record_sub_le {τ t_c y Ω θ κ h : ℝ} (hy : 0 ≤ y / Ω) (hθ : 0 ≤ θ) (hκ : 0 ≤ θ / κ)
    (hh : 0 ≤ h) (h1 : t_c - y / Ω + 2 * θ ≤ τ) (h2 : τ ≤ t_c - h + θ / κ) :
    |τ - t_c| ≤ y / Ω + θ / κ := by
  rw [abs_le]
  constructor <;> linarith

/-- ★★★ **The scaling law.** Along any family of radar exchanges whose readings' errors tend to `0`
— finer records (`encounter_record_window`'s window `≈ y/Ω + θ/κ`, `y ≈ 2(ρ + ρ_A + ρ_B)`, chords
from `sine_packet_tail`/`sine_massless_tail`) and finer clocks — the Lorentz residuals tend to `0`:
for every `ε > 0` there is a reading resolution `d > 0` below which `B`'s radar chart is within `ε`
of the Lorentz boost of `A`'s, in time and in position. -/
theorem radar_lorentz_scaling {v : ℝ} (hv0 : 0 ≤ v) (hv : v < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ tE tR tRet tM e r μ ρ m : ℝ, tR - tE = v * (tM - tE) →
      tRet - tR = v * (tM - tRet) →
      |e - Real.sqrt (1 - v ^ 2) * tE| ≤ d → |r - Real.sqrt (1 - v ^ 2) * tRet| ≤ d →
      |μ - Real.sqrt (1 - v ^ 2) * tM| ≤ d → |ρ - tR| ≤ d → |m - tM| ≤ d →
      |(lorentzBoost 1 (-v) (ρ - m, 0)).1 - ((e + r) / 2 - μ)| ≤ ε
      ∧ |(lorentzBoost 1 (-v) (ρ - m, 0)).2 - (-((r - e) / 2))| ≤ ε := by
  have hs0 : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  set s := Real.sqrt (1 - v ^ 2)
  set K := 2 + 2 / s with hK
  have hK0 : 0 < K := by positivity
  refine ⟨ε / K, div_pos hε hK0, fun tE tR tRet tM e r μ ρ m hE hRet he hr hμ hρ hm => ?_⟩
  obtain ⟨h1, h2⟩ := radar_lorentz_error hv0 hv hE hRet he hr hμ hρ hm
  have hd0 : 0 ≤ ε / K := (div_pos hε hK0).le
  have e1 : (ε / K + ε / K) / 2 + ε / K + (ε / K + ε / K) / s = ε := by
    rw [hK]
    field_simp
    ring
  have hv1 : v * (ε / K + ε / K) / s ≤ (ε / K + ε / K) / s :=
    div_le_div_of_nonneg_right (by nlinarith) hs0.le
  constructor
  · linarith
  · have : 0 ≤ ε / K := hd0
    linarith

variable {L : ℕ} [NeZero L]

/-- ★★★ **Both observers' charts of two common events** (BACKLOG #278, third landing). In the one
evolution of `dirac_b_radar`:

* the records' tick brackets: `B`'s emission between `B`'s ticks `2`–`3`, its return between
  `44`–`50`, the meeting between `61`–`65`; `A`'s relay firing between `A`'s ticks `46`–`48`, the
  meeting between `76`–`81`;
* for every reading in those brackets, `A`'s chart puts the relay firing `28`–`35` periods before
  the meeting at position `0`, and `B`'s radar chart puts it `34.5`–`42` periods before the meeting,
  `20.5`–`24` light-periods away; `A`'s squared interval `[784, 1225]` lies inside `B`'s
  `[2457/4, 5375/4]`;
* **the map** (fourth landing): the Lorentz boost at `−3/5` takes `A`'s chart of the relay firing
  to `B`'s within `37/4` periods in time and `23/4` light-periods in position. -/
theorem dirac_two_charts (hL : 10 ^ 19 ≤ L) {w : ℝ} (hw : 0 ≤ w) :
    let em := bEmission (L := L) hL hw
    let rc := aReception (L := L) hL hw
    let ret := bReturn (L := L) hL hw
    let meet := bMeeting (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => bRestTick (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 100) => bApproachTick (L := L) hL n hn hw
    (rc.evolve = em.evolve ∧ ret.evolve = em.evolve ∧ meet.evolve = em.evolve
      ∧ rc.prep = em.prep ∧ ret.prep = em.prep ∧ meet.prep = em.prep)
    ∧ ((b 2 (by norm_num)).writeEnd ≤ em.writeStart ∧ em.writeEnd ≤ (b 3 (by norm_num)).writeStart
      ∧ (b 44 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (b 50 (by norm_num)).writeStart
      ∧ (b 61 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (b 65 (by norm_num)).writeStart)
    ∧ ((a 46 (by norm_num)).writeEnd ≤ rc.writeStart
      ∧ rc.writeEnd ≤ (a 48 (by norm_num)).writeStart
      ∧ (a 76 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (a 81 (by norm_num)).writeStart)
    ∧ (∀ e r μ ρ m : ℝ, e ∈ Icc (2 : ℝ) 3 → r ∈ Icc (44 : ℝ) 50 → μ ∈ Icc (61 : ℝ) 65 →
        ρ ∈ Icc (46 : ℝ) 48 → m ∈ Icc (76 : ℝ) 81 →
        28 ≤ m - ρ ∧ m - ρ ≤ 35
        ∧ 69 / 2 ≤ μ - radarTime e r ∧ μ - radarTime e r ≤ 42
        ∧ 41 / 2 ≤ bRadarPos e r ∧ bRadarPos e r ≤ 24
        ∧ 784 ≤ minkowskiSq (m - ρ) 0 ∧ minkowskiSq (m - ρ) 0 ≤ 1225
        ∧ 2457 / 4 ≤ minkowskiSq (μ - radarTime e r) (bRadarPos e r)
        ∧ minkowskiSq (μ - radarTime e r) (bRadarPos e r) ≤ 5375 / 4
        ∧ |(lorentzBoost 1 (-(3 / 5)) (-(m - ρ), 0)).1 - (-(μ - radarTime e r))| ≤ 37 / 4
        ∧ |(lorentzBoost 1 (-(3 / 5)) (-(m - ρ), 0)).2 - (-bRadarPos e r)| ≤ 23 / 4) := by
  intro em rc ret meet a b
  obtain ⟨⟨hrc1, hrc2, hret1, hret2, hm1, hm2, -, -⟩, -, -, -, -, -, -, hB, hA⟩ :=
    dirac_b_radar (L := L) hL hw
  exact ⟨⟨hrc1, hret1, hm1, hrc2, hret2, hm2⟩, hB, hA,
    fun e r μ ρ m he hr hμ hρ hm => ⟨two_chart_bounds he hr hμ hρ hm |>.1,
      (two_chart_bounds he hr hμ hρ hm).2.1, (two_chart_bounds he hr hμ hρ hm).2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.1, (two_chart_bounds he hr hμ hρ hm).2.2.2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.2.2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.2.2.2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.2.2.2.2.2.1,
      (two_chart_bounds he hr hμ hρ hm).2.2.2.2.2.2.2.2.2,
      lorentz_chart_bounds he hr hμ hρ hm⟩⟩

end CSD.RecordLayer
