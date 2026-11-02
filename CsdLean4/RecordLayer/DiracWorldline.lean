/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracHalfTicks
public import CsdLean4.RecordLayer.GalileanTransformation

/-!
# The coordinate transformation on the moving observer's worldline

**Category:** 7-SigmaLayer (the record layer). BACKLOG #259, first brick (split 2026-11-02);
the Galilean exclusion from the records, BACKLOG #277.

#259 asks for the map between two observers' charts on the Dirac chain. The observer at rest `A`
charts events by radar: ~~#274~~'s messenger leaves `A`, is turned round by `B`'s relay, and comes
back. `B` sends nothing, so `B` charts only the events it is present at — the reception (its own
relay firing) and the meeting with `A` — by its own clock. On those events the Lorentz map with
`x_B = 0` says `B`'s clock reads the **Minkowski interval** `√(ΔT² − ΔX²)` of `A`'s chart, and the
Galilean map says it reads `ΔT`. This brick puts both against the records and against the clock's
dynamics.

## The radar chart and the interval

* `radarTime`, `radarPos` (`A`'s radar coordinates from its readings `e`, `r` of the emission and
  the return, messenger speed `4/5` both ways), `minkowskiSq`;
* ★★ `radar_interval_bounds` — **from whole-tick readings in the records' brackets**: the meeting is
  `36`–`46` of `A`'s periods after the reception, `B` was `23.2`–`27.2` light-periods away, the
  squared Minkowski interval lies in `[13904/25, 39444/25]`, and `B`'s own interval lies in
  `[30, 36]` — inside the Lorentz range; the Galilean prediction `ΔT` is at least `36`, the
  measured interval at most `36`: **at whole-tick resolution the records do not separate them**;
* ★★ `radar_interval_bounds_half` — **with `A`'s half-ticks** (`restHalfTickRadar`, #277) the
  return is before half-tick `72.5` and the meeting after half-tick `76.5`: the meeting is at least
  `36.75` periods after the reception, `B`'s interval at most `36` — **the Galilean prediction is
  strictly excluded**, and `B`'s interval squares into the Minkowski range `[9945/16, 39444/25]`.

## The clock's rate

* ★★ `clock_rate_lorentz` — **`B`'s clock runs at `4/5`–`0.8002` of `A`'s**, and the Lorentz map of
  `B`'s worldline at speed `3/5` (`lorentzBoost_worldline`) dilates its time by exactly
  `√(1 − (3/5)²) = 4/5`; the Galilean rate `1` is excluded.

## The capstone

* ★★★ `dirac_lorentz_worldline` — the records' tick brackets (`dirac_radar`), the radar chart and
  interval bounds at whole ticks, the half-tick brackets of the return and the meeting with the
  strict Galilean exclusion, and the clock's rate against the Lorentz dilation.

## The finding

**On the moving observer's worldline the transformation is Lorentz's, at the level of the
dynamics**: `B`'s clock rate relative to `A`'s is the dilation `√(1 − β²)` of its worldline in `A`'s
frame, to `2.5·10⁻⁴`, not the Galilean `1`. **The records alone agree**: read to whole ticks they
are consistent with Lorentz and tie with Galilean (`≤ 36` against `≥ 36`); with two half-ticks of
`A`'s clock they exclude Galilean strictly (`≤ 36` against `≥ 36.75`) and stay inside the Lorentz
range (#277).

## Honest scope

⚠️ **Only events on `B`'s worldline**: `B` sends no messengers, so it has no chart of distant
events; `B`'s own radar and the full map are #278.

⚠️ **The rate is a device fact, not a record**: `clock_rate_lorentz` uses `approach_rate` (the
moving clock's splitting), which the records read only through the tick brackets.

⚠️ **The separation is narrow**: `0.75` of a period, from two half-ticks of `A`'s clock; `B`'s
brackets are whole ticks (its half-ticks would not clear the windows of the reception and the
meeting). Lattice corrections are #279 (`DiracLatticeCorrections.lean`).

References: `specs/BACKLOG.md` #259, #277, #278, #279, #274, #256, #253, #247, #249, #246, #39;
`RecordLayer/DiracRadar.lean` (`dirac_radar`); `RecordLayer/DiracHalfTicks.lean`
(`restHalfTickRadar`); `RecordLayer/DiracDoppler.lean` (`approach_rate`);
`RecordLayer/DiracTwin.lean` (`twin_rest_rate`); `RecordLayer/GalileanTransformation.lean`
(`lorentzBoost`, `lorentzBoost_worldline`, `lorentz_refuted`).
-/

@[expose] public section

open Set CSD.CV

namespace CSD.RecordLayer

/-! ### The radar chart and the interval -/

/-- `A`'s radar time of an event, from its readings `e` of the emission and `r` of the return. -/
noncomputable def radarTime (e r : ℝ) : ℝ := (e + r) / 2

/-- `A`'s radar position of an event, the messenger moving at `4/5` both ways. -/
noncomputable def radarPos (e r : ℝ) : ℝ := 4 / 5 * ((r - e) / 2)

/-- The squared Minkowski interval (`c = 1`). -/
def minkowskiSq (dT dX : ℝ) : ℝ := dT ^ 2 - dX ^ 2

/-- ★★ **The radar chart and the intervals from whole-tick readings.** For readings in the brackets
the records give — the emission between `A`'s ticks `5` and `7`, the return between `65` and `73`,
the meeting between `76` and `81`; the reception between `B`'s ticks `29` and `31`, the meeting
between `61` and `65` — the meeting is `36`–`46` periods after the reception in `A`'s radar chart,
the reception `23.2`–`27.2` light-periods from `A`, the squared Minkowski interval in
`[13904/25, 39444/25]`, and `B`'s interval in `[30, 36]`, whose square lies inside it. The Galilean
prediction `ΔT` is at least `36` and the measured interval at most `36`. -/
theorem radar_interval_bounds {e r m ρ μ : ℝ} (he : e ∈ Icc (5 : ℝ) 7) (hr : r ∈ Icc (65 : ℝ) 73)
    (hm : m ∈ Icc (76 : ℝ) 81) (hρ : ρ ∈ Icc (29 : ℝ) 31) (hμ : μ ∈ Icc (61 : ℝ) 65) :
    36 ≤ m - radarTime e r ∧ m - radarTime e r ≤ 46
    ∧ 116 / 5 ≤ radarPos e r ∧ radarPos e r ≤ 136 / 5 ∧ radarPos e r < m - radarTime e r
    ∧ 13904 / 25 ≤ minkowskiSq (m - radarTime e r) (radarPos e r)
    ∧ minkowskiSq (m - radarTime e r) (radarPos e r) ≤ 39444 / 25
    ∧ 30 ≤ μ - ρ ∧ μ - ρ ≤ 36
    ∧ 13904 / 25 ≤ (μ - ρ) ^ 2 ∧ (μ - ρ) ^ 2 ≤ 39444 / 25
    ∧ μ - ρ ≤ 36 ∧ 36 ≤ m - radarTime e r := by
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hρ1, hρ2⟩ := hρ
  obtain ⟨hμ1, hμ2⟩ := hμ
  have hT1 : 36 ≤ m - radarTime e r := by unfold radarTime; linarith
  have hT2 : m - radarTime e r ≤ 46 := by unfold radarTime; linarith
  have hX1 : 116 / 5 ≤ radarPos e r := by unfold radarPos; linarith
  have hX2 : radarPos e r ≤ 136 / 5 := by unfold radarPos; linarith
  have hD1 : 30 ≤ μ - ρ := by linarith
  have hD2 : μ - ρ ≤ 36 := by linarith
  refine ⟨hT1, hT2, hX1, hX2, by linarith, ?_, ?_, hD1, hD2, by nlinarith, by nlinarith, hD2, hT1⟩
  · unfold minkowskiSq
    nlinarith
  · unfold minkowskiSq
    nlinarith

/-- ★★ **With half-ticks the records exclude Galilean.** For readings in the brackets the records
give once `A`'s half-ticks are counted — the return before `A`'s half-tick `72.5`, the meeting after
its half-tick `76.5` (`restHalfTickRadar`), the other brackets as before — the meeting is at least
`36.75` periods after the reception in `A`'s radar chart, while `B`'s interval is at most `36`: the
Galilean prediction is strictly excluded. The squared Minkowski interval lies in
`[9945/16, 39444/25]`, and `B`'s interval squares into it. -/
theorem radar_interval_bounds_half {e r m ρ μ : ℝ} (he : e ∈ Icc (5 : ℝ) 7)
    (hr : r ∈ Icc (65 : ℝ) (145 / 2)) (hm : m ∈ Icc (153 / 2 : ℝ) 81) (hρ : ρ ∈ Icc (29 : ℝ) 31)
    (hμ : μ ∈ Icc (61 : ℝ) 65) :
    147 / 4 ≤ m - radarTime e r ∧ m - radarTime e r ≤ 46
    ∧ 116 / 5 ≤ radarPos e r ∧ radarPos e r ≤ 27
    ∧ 9945 / 16 ≤ minkowskiSq (m - radarTime e r) (radarPos e r)
    ∧ minkowskiSq (m - radarTime e r) (radarPos e r) ≤ 39444 / 25
    ∧ 9945 / 16 ≤ (μ - ρ) ^ 2 ∧ (μ - ρ) ^ 2 ≤ 39444 / 25
    ∧ μ - ρ < m - radarTime e r := by
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hρ1, hρ2⟩ := hρ
  obtain ⟨hμ1, hμ2⟩ := hμ
  have hT1 : 147 / 4 ≤ m - radarTime e r := by unfold radarTime; linarith
  have hT2 : m - radarTime e r ≤ 46 := by unfold radarTime; linarith
  have hX1 : 116 / 5 ≤ radarPos e r := by unfold radarPos; linarith
  have hX2 : radarPos e r ≤ 27 := by unfold radarPos; linarith
  have hD1 : 30 ≤ μ - ρ := by linarith
  have hD2 : μ - ρ ≤ 36 := by linarith
  refine ⟨hT1, hT2, hX1, hX2, ?_, ?_, by nlinarith, by nlinarith, by linarith⟩
  · unfold minkowskiSq
    nlinarith
  · unfold minkowskiSq
    nlinarith

/-! ### The clock's rate -/

/-- ★★ **The moving clock runs at the Lorentz rate of its worldline.** A clock whose splitting `R`
is in `[8, 8.002]·10⁻¹²` (`approach_rate`) runs at `4/5`–`0.8002` of the rest clock's `10⁻¹¹`; the
Lorentz map of a worldline at speed `3/5` dilates its time by exactly `√(1 − (3/5)²) = 4/5`; and
the Galilean rate `1` is excluded. -/
theorem clock_rate_lorentz {R : ℝ} (h1 : 8 / 10 ^ 12 ≤ R) (h2 : R ≤ 8002 / 10 ^ 15) :
    4 / 5 ≤ R / (1 / 10 ^ 11) ∧ R / (1 / 10 ^ 11) ≤ 4001 / 5000 ∧ R / (1 / 10 ^ 11) < 1
    ∧ Real.sqrt (1 - (3 / 5 : ℝ) ^ 2 / 1 ^ 2) = 4 / 5
    ∧ ∀ τ : ℝ, lorentzBoost 1 (3 / 5) (τ, 3 / 5 * τ) = (τ * (4 / 5), 0) := by
  have hs : Real.sqrt (1 - (3 / 5 : ℝ) ^ 2 / 1 ^ 2) = 4 / 5 := by
    rw [show (1 : ℝ) - (3 / 5) ^ 2 / 1 ^ 2 = (4 / 5) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, ?_, hs, fun τ => ?_⟩
  · rw [le_div_iff₀ (by norm_num)]
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_one (by norm_num)]
    linarith
  · rw [lorentzBoost_worldline (by norm_num : |(3 / 5 : ℝ)| < 1) τ, hs]

/-! ### The capstone -/

variable {L : ℕ} [NeZero L]

/-- ★★★ **The transformation on the moving observer's worldline (#259, first brick).** In the radar
arena of ~~#274~~ (`A` at rest, `B` approaching at `3/5`, the messenger at `4/5`, one evolution):

* the records bracket the emission, the return and the meeting by `A`'s ticks and the reception and
  the meeting by `B`'s (`dirac_radar`);
* for every reading in those brackets, `A`'s radar chart puts the meeting `36`–`46` periods after
  the reception and the reception `23.2`–`27.2` light-periods away; the squared Minkowski interval
  lies in `[13904/25, 39444/25]`, and `B`'s measured interval, `30`–`36` ticks, squares into it; the
  Galilean prediction (`≥ 36`) and the measurement (`≤ 36`) tie at this resolution;
* `A`'s half-ticks `72.5` and `76.5` are records of the same evolution, the first after the return,
  the second before the meeting; for every reading in the sharpened brackets the measurement is
  strictly below the Galilean prediction (`≤ 36 < 36.75 ≤ ΔT`) and squares into the Minkowski range
  `[9945/16, 39444/25]` (#277);
* `B`'s clock runs at `4/5`–`0.8002` of `A`'s — the Lorentz dilation of its worldline, exactly
  `4/5`, and not the Galilean `1`. -/
theorem dirac_lorentz_worldline (hL : 10 ^ 19 ≤ L) {w : ℝ} (hw : 0 ≤ w) :
    let em := radarEmission (L := L) hL hw
    let rc := radarReception (L := L) hL hw
    let ret := radarReturn (L := L) hL hw
    let meet := radarMeeting (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => restTickRadar (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 100) => approachTickRadar (L := L) hL n hn hw
    let h := fun (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 130) => restHalfTickRadar (L := L) hL n hn1 hn hw
    let R := levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * (9 / 4)))
    ((a 5 (by norm_num)).writeEnd ≤ em.writeStart ∧ em.writeEnd ≤ (a 7 (by norm_num)).writeStart
      ∧ (a 65 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (a 73 (by norm_num)).writeStart
      ∧ (a 76 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (a 81 (by norm_num)).writeStart)
    ∧ ((b 29 (by norm_num)).writeEnd ≤ rc.writeStart
      ∧ rc.writeEnd ≤ (b 31 (by norm_num)).writeStart
      ∧ (b 61 (by norm_num)).writeEnd ≤ meet.writeStart
      ∧ meet.writeEnd ≤ (b 65 (by norm_num)).writeStart)
    ∧ (∀ e r m ρ μ : ℝ, e ∈ Icc (5 : ℝ) 7 → r ∈ Icc (65 : ℝ) 73 → m ∈ Icc (76 : ℝ) 81 →
        ρ ∈ Icc (29 : ℝ) 31 → μ ∈ Icc (61 : ℝ) 65 →
        13904 / 25 ≤ minkowskiSq (m - radarTime e r) (radarPos e r)
        ∧ minkowskiSq (m - radarTime e r) (radarPos e r) ≤ 39444 / 25
        ∧ 13904 / 25 ≤ (μ - ρ) ^ 2 ∧ (μ - ρ) ^ 2 ≤ 39444 / 25
        ∧ μ - ρ ≤ 36 ∧ 36 ≤ m - radarTime e r)
    ∧ ((h 73 (by norm_num) (by norm_num)).evolve = em.evolve
      ∧ (h 73 (by norm_num) (by norm_num)).prep = em.prep
      ∧ (h 77 (by norm_num) (by norm_num)).evolve = em.evolve
      ∧ (h 77 (by norm_num) (by norm_num)).prep = em.prep
      ∧ ret.writeEnd ≤ (h 73 (by norm_num) (by norm_num)).writeStart
      ∧ (h 77 (by norm_num) (by norm_num)).writeEnd ≤ meet.writeStart)
    ∧ (∀ e r m ρ μ : ℝ, e ∈ Icc (5 : ℝ) 7 → r ∈ Icc (65 : ℝ) (145 / 2) → m ∈ Icc (153 / 2 : ℝ) 81 →
        ρ ∈ Icc (29 : ℝ) 31 → μ ∈ Icc (61 : ℝ) 65 →
        9945 / 16 ≤ minkowskiSq (m - radarTime e r) (radarPos e r)
        ∧ minkowskiSq (m - radarTime e r) (radarPos e r) ≤ 39444 / 25
        ∧ 9945 / 16 ≤ (μ - ρ) ^ 2 ∧ (μ - ρ) ^ 2 ≤ 39444 / 25
        ∧ μ - ρ < m - radarTime e r)
    ∧ (4 / 5 ≤ R / (1 / 10 ^ 11) ∧ R / (1 / 10 ^ 11) ≤ 4001 / 5000 ∧ R / (1 / 10 ^ 11) < 1
      ∧ Real.sqrt (1 - (3 / 5 : ℝ) ^ 2 / 1 ^ 2) = 4 / 5
      ∧ ∀ τ : ℝ, lorentzBoost 1 (3 / 5) (τ, 3 / 5 * τ) = (τ * (4 / 5), 0)) := by
  intro em rc ret meet a b h R
  obtain ⟨-, -, -, ⟨-, -, -, -, -, hrE, hmS, -⟩, -, ⟨hR1, hR2, -⟩, -, hA, hB, -, -⟩ :=
    dirac_radar (L := L) hL hw
  obtain ⟨h73e, h73p, h73s, -⟩ :=
    restHalfTickRadar_fields (L := L) hL 73 (by norm_num) (by norm_num) hw
  obtain ⟨h77e, h77p, -, h77t⟩ :=
    restHalfTickRadar_fields (L := L) hL 77 (by norm_num) (by norm_num) hw
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  refine ⟨hA, hB, fun e r m ρ μ he hr hm hρ hμ => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun e r m ρ μ he hr hm hρ hμ => ?_, clock_rate_lorentz hR1 hR2⟩
  · obtain ⟨-, -, -, -, -, h1, h2, -, -, h3, h4, h5, h6⟩ := radar_interval_bounds he hr hm hρ hμ
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · exact h73e.trans (radarEmission_fields (L := L) hL hw).1.symm
  · exact h73p.trans (radarEmission_fields (L := L) hL hw).2.1.symm
  · exact h77e.trans (radarEmission_fields (L := L) hL hw).1.symm
  · exact h77p.trans (radarEmission_fields (L := L) hL hw).2.1.symm
  · show ret.writeEnd ≤ (restHalfTickRadar (L := L) hL 73 (by norm_num) (by norm_num) hw).writeStart
    rw [hrE, h73s]
    refine le_max_of_le_right ?_
    push_cast
    nlinarith
  · show (restHalfTickRadar (L := L) hL 77 (by norm_num) (by norm_num) hw).writeEnd
      ≤ meet.writeStart
    rw [hmS, h77t]
    push_cast
    nlinarith
  · obtain ⟨-, -, -, -, h1, h2, h3, h4, h5⟩ := radar_interval_bounds_half he hr hm hρ hμ
    exact ⟨h1, h2, h3, h4, h5⟩

end CSD.RecordLayer

end
