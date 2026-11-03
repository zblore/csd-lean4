/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTwoCharts

/-!
# The effective geometry does not depend on the apparatus

**Category:** 7-SigmaLayer (the record layer). BACKLOG #248, part (b).

#248 (b) asks to vary the detector and clock construction within a stated class and prove that the
same effective geometry survives. **The class:** every apparatus — detector and clock — whose
readings of an exchange's events lie within a stated error of the events' ideal times. The
detectors of the record layer belong to it: a threshold register at any rate, chord and threshold
reads its encounter within `y/Ω + θ/κ` (`record_window`, `encounter_record_window`,
`abs_record_sub_le`); a clock belongs with its reading error. Two apparatus in the class, with
errors `d₁` and `d₂`, are then compared through the events they both read.

## The control chain (A): the Galilean geometry

* ★★★ `galilean_apparatus_indep` (**two reading sets within `ε₁`, `ε₂` of the same exchange give
  transit charts, velocity and separation estimates within `err(ε₁) + err(ε₂)` of each other** —
  `ReadingsNear`'s stability, read twice).

## The Dirac chain (B): the Lorentz geometry

* ★★ `radar_velocity_exact` (**`B`'s radar reads the relative velocity off its own records**: the
  radar distance of `A`'s event over its radar time before the meeting is exactly `v`);
* ★★★ `radar_velocity_error` (**with readings within `d`, the estimate is within
  `3d/(T − 2d)` of `v`**, `T` the radar time before the meeting);
* ★★★ `radar_apparatus_indep` (**two apparatus in the class, errors `d₁` and `d₂`, give velocity
  estimates within `3d₁/(T − 2d₁) + 3d₂/(T − 2d₂)` of each other, and each radar chart within its
  own `radar_lorentz_error` bound of the Lorentz boost of `A`'s chart at the true `v`** — the
  effective geometry, velocity and map, is the events', not the apparatus').

## Honest scope

⚠️ **The class is defined by reading errors**: an apparatus belongs once its readings are within
`d` of the events' ideal times; the theorems say nothing about apparatus outside it (a detector
with an unbounded lag, a clock with an unknown rate). Membership of the record layer's threshold
detectors is `abs_record_sub_le`; a clock's membership is its own reading error (#283 for the
continuous reading).

⚠️ **Two events on (B)**: the relay event and the meeting; `v̂` uses the meeting as the second
event. The Dirac-chain statements are kinematic, as `radar_lorentz_exact` is.

References: `specs/BACKLOG.md` #248, #280, #283, #278, #247, #39;
`RecordLayer/GalileanTransformation.lean` (`ReadingsNear`, `transitChart`, `relVelEst`, `sepEst`,
`ReadingsNear.abs_chartTime_sub_le`, `ReadingsNear.abs_chartSep_sub_le`,
`ReadingsNear.abs_relVelEst_sub_le`, `ReadingsNear.abs_sepEst_sub_le`);
`RecordLayer/DiracTwoCharts.lean` (`radar_lorentz_exact`, `radar_lorentz_error`,
`abs_record_sub_le`); `RecordLayer/DiracResolution.lean` (`record_window`,
`encounter_record_window`).
-/

@[expose] public section

namespace CSD.RecordLayer

/-! ### The control chain -/

/-- ★★★ **Two apparatus, one Galilean geometry.** Two reading sets, within `ε₁` and `ε₂` of the
same exchange's record times (writes lasting `≥ δ`, ends within `H`), give transit-chart times,
separations, velocity estimates and separation estimates within the sum of their errors. -/
theorem galilean_apparatus_indep {eS eE rS rE a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ε₁ ε₂ δ H : ℝ}
    (h₁ : ReadingsNear eS eE rS rE a₁ b₁ c₁ d₁ ε₁ δ H)
    (h₂ : ReadingsNear eS eE rS rE a₂ b₂ c₂ d₂ ε₂ δ H) :
    |(transitChart a₁ b₁ c₁ d₁).1 - (transitChart a₂ b₂ c₂ d₂).1|
        ≤ chartTimeErr ε₁ δ H + chartTimeErr ε₂ δ H
    ∧ |(transitChart a₁ b₁ c₁ d₁).2 - (transitChart a₂ b₂ c₂ d₂).2|
        ≤ chartSepErr ε₁ δ H + chartSepErr ε₂ δ H
    ∧ |relVelEst a₁ b₁ c₁ d₁ - relVelEst a₂ b₂ c₂ d₂| ≤ relVelErr ε₁ δ + relVelErr ε₂ δ
    ∧ |sepEst a₁ b₁ c₁ d₁ - sepEst a₂ b₂ c₂ d₂| ≤ sepEstErr ε₁ δ H + sepEstErr ε₂ δ H := by
  have tri : ∀ x y z u v : ℝ, |x - z| ≤ u → |y - z| ≤ v → |x - y| ≤ u + v := fun x y z u v h h' =>
    (abs_sub_le x z y).trans (add_le_add h (by rw [abs_sub_comm]; exact h'))
  exact ⟨tri _ _ _ _ _ h₁.abs_chartTime_sub_le h₂.abs_chartTime_sub_le,
    tri _ _ _ _ _ h₁.abs_chartSep_sub_le h₂.abs_chartSep_sub_le,
    tri _ _ _ _ _ h₁.abs_relVelEst_sub_le h₂.abs_relVelEst_sub_le,
    tri _ _ _ _ _ h₁.abs_sepEst_sub_le h₂.abs_sepEst_sub_le⟩

/-! ### The Dirac chain -/

/-- ★★ **The radar reads the velocity.** For an exchange as in `radar_lorentz_exact`, `B`'s radar
distance `s (t_Ret − t_E)/2` of the event is `v` times its radar time before the meeting,
`s t_M − s (t_E + t_Ret)/2`. -/
theorem radar_velocity_exact {v tE tR tRet tM : ℝ} (hv0 : 0 ≤ v) (hv : v < 1)
    (hE : tR - tE = v * (tM - tE)) (hRet : tRet - tR = v * (tM - tRet)) :
    Real.sqrt (1 - v ^ 2) * ((tRet - tE) / 2)
      = v * (Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2)) := by
  have h1v : 0 < 1 - v := by linarith
  have h1v' : 0 < 1 + v := by linarith
  have heE : tE - tM = (tR - tM) / (1 - v) := by
    field_simp
    linarith
  have heR : tRet - tM = (tR - tM) / (1 + v) := by
    field_simp
    linarith
  rw [show tRet - tE = (tRet - tM) - (tE - tM) by ring,
    show Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2)
      = -(Real.sqrt (1 - v ^ 2) * ((tE - tM) + (tRet - tM)) / 2) by ring, heE, heR]
  field_simp
  ring

/-- ★★★ **The velocity from imperfect readings.** With `B`'s readings `e`, `r`, `μ` within `d` of
its proper times of the emission, the return and the meeting, and the true radar time before the
meeting `T > 2d`, the estimate `((r − e)/2) / (μ − (e + r)/2)` is within `3d/(T − 2d)` of `v`. -/
theorem radar_velocity_error {v tE tR tRet tM e r μ d : ℝ} (hv0 : 0 ≤ v) (hv : v < 1)
    (hE : tR - tE = v * (tM - tE)) (hRet : tRet - tR = v * (tM - tRet))
    (he : |e - Real.sqrt (1 - v ^ 2) * tE| ≤ d) (hr : |r - Real.sqrt (1 - v ^ 2) * tRet| ≤ d)
    (hμ : |μ - Real.sqrt (1 - v ^ 2) * tM| ≤ d)
    (hT : 2 * d < Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2)) :
    |(r - e) / 2 / (μ - (e + r) / 2) - v|
      ≤ 3 * d
        / (Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2) - 2 * d) := by
  set s := Real.sqrt (1 - v ^ 2)
  set T := s * tM - s * ((tE + tRet) / 2) with hTdef
  have hX := radar_velocity_exact hv0 hv hE hRet
  rw [abs_le] at he hr hμ
  have hTh : T - 2 * d ≤ μ - (e + r) / 2 := by linarith
  have hd0 : 0 ≤ d := by linarith [he.1, he.2]
  have hpos : 0 < μ - (e + r) / 2 := by linarith
  have hpos' : 0 < T - 2 * d := by linarith
  rw [div_sub' hpos.ne', abs_div, abs_of_pos hpos]
  have hnum : |(r - e) / 2 - (μ - (e + r) / 2) * v| ≤ 3 * d := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |(r - e) / 2 - (μ - (e + r) / 2) * v| / (μ - (e + r) / 2)
      ≤ 3 * d / (μ - (e + r) / 2) := div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ 3 * d / (T - 2 * d) := div_le_div_of_nonneg_left (by linarith) hpos' hTh

/-- ★★★ **Two apparatus, one Lorentz geometry.** Two apparatus in the class — readings within
`d₁` and `d₂` of the same exchange's proper times — give velocity estimates within
`3d₁/(T − 2d₁) + 3d₂/(T − 2d₂)` of each other, and each its own radar chart within its
`radar_lorentz_error` bound of the Lorentz boost of `A`'s chart at the true `v`. -/
theorem radar_apparatus_indep {v tE tR tRet tM : ℝ} {e₁ r₁ μ₁ ρ₁ m₁ e₂ r₂ μ₂ ρ₂ m₂ d₁ d₂ : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hE : tR - tE = v * (tM - tE))
    (hRet : tRet - tR = v * (tM - tRet))
    (he₁ : |e₁ - Real.sqrt (1 - v ^ 2) * tE| ≤ d₁)
    (hr₁ : |r₁ - Real.sqrt (1 - v ^ 2) * tRet| ≤ d₁)
    (hμ₁ : |μ₁ - Real.sqrt (1 - v ^ 2) * tM| ≤ d₁) (hρ₁ : |ρ₁ - tR| ≤ d₁) (hm₁ : |m₁ - tM| ≤ d₁)
    (he₂ : |e₂ - Real.sqrt (1 - v ^ 2) * tE| ≤ d₂)
    (hr₂ : |r₂ - Real.sqrt (1 - v ^ 2) * tRet| ≤ d₂)
    (hμ₂ : |μ₂ - Real.sqrt (1 - v ^ 2) * tM| ≤ d₂) (hρ₂ : |ρ₂ - tR| ≤ d₂) (hm₂ : |m₂ - tM| ≤ d₂)
    (hT₁ : 2 * d₁ < Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2))
    (hT₂ : 2 * d₂ < Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2)) :
    |(r₁ - e₁) / 2 / (μ₁ - (e₁ + r₁) / 2) - (r₂ - e₂) / 2 / (μ₂ - (e₂ + r₂) / 2)|
        ≤ 3 * d₁ / (Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2) - 2 * d₁)
          + 3 * d₂
            / (Real.sqrt (1 - v ^ 2) * tM - Real.sqrt (1 - v ^ 2) * ((tE + tRet) / 2) - 2 * d₂)
    ∧ |(lorentzBoost 1 (-v) (ρ₁ - m₁, 0)).1 - ((e₁ + r₁) / 2 - μ₁)|
        ≤ (d₁ + d₁) / 2 + d₁ + (d₁ + d₁) / Real.sqrt (1 - v ^ 2)
    ∧ |(lorentzBoost 1 (-v) (ρ₂ - m₂, 0)).1 - ((e₂ + r₂) / 2 - μ₂)|
        ≤ (d₂ + d₂) / 2 + d₂ + (d₂ + d₂) / Real.sqrt (1 - v ^ 2) := by
  have v₁ := radar_velocity_error hv0 hv hE hRet he₁ hr₁ hμ₁ hT₁
  have v₂ := radar_velocity_error hv0 hv hE hRet he₂ hr₂ hμ₂ hT₂
  refine ⟨(abs_sub_le _ v _).trans (add_le_add v₁ (by rw [abs_sub_comm]; exact v₂)),
    (radar_lorentz_error hv0 hv hE hRet he₁ hr₁ hμ₁ hρ₁ hm₁).1,
    (radar_lorentz_error hv0 hv hE hRet he₂ hr₂ hμ₂ hρ₂ hm₂).1⟩

end CSD.RecordLayer
