/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTwoCharts

/-!
# The effective geometry does not depend on the apparatus

**Category:** 7-SigmaLayer (the record layer). BACKLOG #248, part (b); #283.

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

## Clocks in the class (#283)

* ★★ `register_reads_time` (**a register within `E` of a response rising at slope `≥ g` reads the
  time of any threshold within `E/g`**);
* ★★★ `clock_reading_error` (**the clock-reading law**: read by thresholds spaced `Δ`, an event is
  read within `(Δ + 3E)/g` — the spacing (the tick size) enters only as `Δ/g` and can be made as
  fine as wanted; the floor is the tracking error `E/g`; a clock belongs to the class with
  `d = (Δ + 3E)/g`).

## The quadrature clock (#283, the device)

* `star_tickMark_mul_eq`, `re_star_I_tickMark_mul` (the quarter-turned mark reads the sine),
  `abs_rateWeight_sub_le_of_mark` (a drifting rate against any unit mark);
* `quadRate` (**the four clipped readings against `±ū`, `±iū`**), `continuous_quadRate`,
  ★★ `abs_quadRate_sub_le` (**within four drifts of `R |C₀| (|cos Rs| + |sin Rs|)`**),
  `one_le_abs_cos_add_abs_sin` (the quadrature rate never stalls);
* `quadResponse`, ★★ `quadResponse_slope` (**the response rises at slope `≥ R |C₀|`**),
  ★★★ `abs_integral_quadRate_sub_le` (**the register tracks the response within
  `4ε (t + R t²/2)`**);
* ★★★ `quad_clock_reading_error` (**the quadrature clock reads time with no tick period: thresholds
  spaced `Δ` read an event within `(Δ + 12ε(T + RT²/2))/(R|C₀|)` — `Δ` arbitrary, the floor the
  drift**).

## Honest scope

⚠️ **The class is defined by reading errors**: an apparatus belongs once its readings are within
`d` of the events' ideal times; the theorems say nothing about apparatus outside it (a detector
with an unbounded lag, a clock with an unknown rate). Membership of the record layer's threshold
detectors is `abs_record_sub_le`; a clock's membership is `clock_reading_error`, given its
response `F`, slope `g` and tracking error `E` — for the chain's clock devices,
`quad_clock_reading_error` (a single rectified register stalls twice a period, `g = 0`; the
quadrature register does not). The arenas carry single-mark tick registers; carrying the
quadrature register is the parked instance, #282.

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

open Complex CSD.CV CSD.SigmaLayer
open scoped Matrix

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

/-! ### Clocks in the class (#283) -/

/-- ★★ **A register that tracks a rising response reads time.** If `F` rises at slope at least
`g > 0` on `[0, T]` and the register `G` stays within `E` of it, then a time `τ` at which `G`
reads `θ` is within `E/g` of the time `t*` at which `F` reads `θ`. -/
theorem register_reads_time {G F : ℝ → ℝ} {g E θ τ tstar T : ℝ} (hg : 0 < g)
    (hF : ∀ t t', 0 ≤ t → t ≤ t' → t' ≤ T → g * (t' - t) ≤ F t' - F t)
    (htrack : ∀ t, 0 ≤ t → t ≤ T → |G t - F t| ≤ E) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T)
    (hcross : G τ = θ) (hs0 : 0 ≤ tstar) (hsT : tstar ≤ T) (hstar : F tstar = θ) :
    |τ - tstar| ≤ E / g := by
  have hE : |F τ - F tstar| ≤ E := by
    rw [hstar, ← hcross, abs_sub_comm]
    exact htrack τ hτ0 hτT
  rw [le_div_iff₀ hg]
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  rcases le_total τ tstar with h | h
  · have := hF τ tstar hτ0 h hsT
    rw [abs_of_nonpos (by linarith : τ - tstar ≤ 0)]
    nlinarith
  · have := hF tstar τ hs0 h hτT
    rw [abs_of_nonneg (by linarith : 0 ≤ τ - tstar)]
    nlinarith

/-- ★★★ **The clock-reading law.** A clock register `G` tracking a response `F` within `E`, `F`
rising at slope at least `g`, read by thresholds `θ_k`, `θ_{k+1} = θ_k + Δ`: an event at time `t`
between the two records (`τ_k ≤ t ≤ τ_{k+1}`) is read as `t*_k` (where `F` reaches `θ_k`) within
`(Δ + 3E)/g`. The threshold spacing enters only as `Δ/g` and can be made as fine as wanted; the
floor is the tracking error `E/g` — so a clock belongs to `#248`'s class with
`d = (Δ + 3E)/g`, and the tick period leaves `radar_lorentz_error`. -/
theorem clock_reading_error {G F : ℝ → ℝ} {g E θ Δ τ₀ τ₁ t₀ t₁ t T : ℝ} (hg : 0 < g)
    (hF : ∀ t t', 0 ≤ t → t ≤ t' → t' ≤ T → g * (t' - t) ≤ F t' - F t)
    (htrack : ∀ t, 0 ≤ t → t ≤ T → |G t - F t| ≤ E)
    (h₀ : 0 ≤ τ₀) (h₁ : τ₁ ≤ T) (hc₀ : G τ₀ = θ) (hc₁ : G τ₁ = θ + Δ)
    (ht₀0 : 0 ≤ t₀) (ht₁T : t₁ ≤ T) (hF₀ : F t₀ = θ) (hF₁ : F t₁ = θ + Δ) (ht₀₁ : t₀ ≤ t₁)
    (hτ : τ₀ ≤ t) (hτ' : t ≤ τ₁) :
    |t - t₀| ≤ (Δ + 3 * E) / g := by
  have hτ₀₁ : τ₀ ≤ τ₁ := hτ.trans hτ'
  have r₀ := register_reads_time hg hF htrack h₀ (hτ₀₁.trans h₁) hc₀ ht₀0 (ht₀₁.trans ht₁T) hF₀
  have r₁ := register_reads_time hg hF htrack (h₀.trans hτ₀₁) h₁ hc₁ (ht₀0.trans ht₀₁) ht₁T hF₁
  have hsp : t₁ - t₀ ≤ Δ / g := by
    have := hF t₀ t₁ ht₀0 ht₀₁ ht₁T
    rw [hF₀, hF₁, show θ + Δ - θ = Δ by ring] at this
    rw [le_div_iff₀ hg]
    linarith
  rw [abs_le] at r₀ r₁
  have e : (Δ + 3 * E) / g = Δ / g + 3 * (E / g) := by ring
  rw [e, abs_le]
  constructor <;> linarith [r₀.1, r₀.2, r₁.1, r₁.2]

/-! ### The quadrature clock (#283, the device) -/

section Quadrature

variable {L : ℕ} [NeZero L]

/-- The coherence turned through `−Rs`, read against the tick mark: `|C₀| e^{−iRs}`. -/
theorem star_tickMark_mul_eq {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hC : deviceCoherence Ψ₀ ≠ 0)
    (R s : ℝ) :
    star (tickMark Ψ₀) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)
      = ((‖deviceCoherence Ψ₀‖ : ℝ) : ℂ) * exp (((-R * s : ℝ) : ℂ) * I) := by
  rw [tickMark]
  set C₀ := deviceCoherence Ψ₀
  have hn : ((‖C₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hC
  have hstar : star C₀ * C₀ = ((‖C₀‖ : ℝ) : ℂ) * ((‖C₀‖ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', sq]
  have hs : star ((‖C₀‖ : ℝ) : ℂ) = ((‖C₀‖ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [star_div₀, hs]
  calc star C₀ / ((‖C₀‖ : ℝ) : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * C₀)
      = star C₀ * C₀ / ((‖C₀‖ : ℝ) : ℂ) * exp (I * (((-R : ℝ) : ℂ) * s)) := by ring
    _ = _ := by
      rw [hstar, mul_div_cancel_right₀ _ hn]
      congr 2
      push_cast
      ring

/-- The quarter-turned mark reads the sine: `Re(conj(i ū) e^{−iRs} C₀) = −|C₀| sin(Rs)`. -/
theorem re_star_I_tickMark_mul {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hC : deviceCoherence Ψ₀ ≠ 0)
    (R s : ℝ) :
    (star (I * tickMark Ψ₀) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)).re
      = -(‖deviceCoherence Ψ₀‖ * Real.sin (R * s)) := by
  rw [star_mul', mul_assoc, star_tickMark_mul_eq hC,
    show star I = -I from Complex.conj_I]
  rw [show -I * (((‖deviceCoherence Ψ₀‖ : ℝ) : ℂ) * exp (((-R * s : ℝ) : ℂ) * I))
    = ((‖deviceCoherence Ψ₀‖ : ℝ) : ℂ) * (-I * exp (((-R * s : ℝ) : ℂ) * I)) by ring,
    Complex.re_ofReal_mul]
  have : (-I * exp (((-R * s : ℝ) : ℂ) * I)).re = Real.sin (-R * s) := by
    rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_im]
    ring
  rw [this, neg_mul, Real.sin_neg]
  ring

/-- **A drifting rate, against any unit mark**: within the drift of the ideal clipped reading. -/
theorem abs_rateWeight_sub_le_of_mark {J μ₀ μ₁ : ℝ} {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    {u : ℂ} (hu : ‖u‖ = 1) {R s ε : ℝ}
    (h : ‖splitCoherence J μ₀ μ₁ Ψ
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ ε) :
    |rateWeight J μ₀ μ₁ u Ψ
      - max (star u * ((R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀))).re 0|
      ≤ ε := by
  rw [rateWeight]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star, hu, one_mul]
  exact h

/-- **The quadrature clock's rate**: the four clipped readings against `±ū`, `±iū`. -/
noncomputable def quadRate (J μ₀ μ₁ : ℝ) (Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  rateWeight J μ₀ μ₁ (tickMark Ψ₀) Ψ + rateWeight J μ₀ μ₁ (-tickMark Ψ₀) Ψ
    + rateWeight J μ₀ μ₁ (I * tickMark Ψ₀) Ψ + rateWeight J μ₀ μ₁ (-(I * tickMark Ψ₀)) Ψ

/-- ★★ **The quadrature rate, pointwise**: within four drifts of `R |C₀| (|cos Rs| + |sin Rs|)`. -/
theorem abs_quadRate_sub_le {J μ₀ μ₁ : ℝ} {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) {R s ε : ℝ} (hR : 0 ≤ R)
    (h : ‖splitCoherence J μ₀ μ₁ Ψ
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ ε) :
    |quadRate J μ₀ μ₁ Ψ₀ Ψ
      - R * ‖deviceCoherence Ψ₀‖ * (|Real.cos (R * s)| + |Real.sin (R * s)|)| ≤ 4 * ε := by
  have hτ := norm_tickMark hC
  have hIτ : ‖I * tickMark Ψ₀‖ = 1 := by rw [norm_mul, Complex.norm_I, hτ, one_mul]
  have e1 := abs_rateWeight_sub_le_of_mark (u := tickMark Ψ₀) hτ h
  have e2 := abs_rateWeight_sub_le_of_mark (u := -tickMark Ψ₀) (by rw [norm_neg, hτ]) h
  have e3 := abs_rateWeight_sub_le_of_mark (u := I * tickMark Ψ₀) hIτ h
  have e4 := abs_rateWeight_sub_le_of_mark (u := -(I * tickMark Ψ₀)) (by rw [norm_neg, hIτ]) h
  have r : ∀ u : ℂ, (star u * ((R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀))).re
      = R * (star u * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)).re := fun u => by
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have c1 := re_star_tickMark_mul hC R s
  have c3 := re_star_I_tickMark_mul hC R s
  have c2 : (star (-tickMark Ψ₀) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)).re
      = -(‖deviceCoherence Ψ₀‖ * Real.cos (R * s)) := by
    rw [star_neg, neg_mul, Complex.neg_re, c1]
  have c4 : (star (-(I * tickMark Ψ₀)) * (exp (I * (((-R : ℝ) : ℂ) * s))
      * deviceCoherence Ψ₀)).re = ‖deviceCoherence Ψ₀‖ * Real.sin (R * s) := by
    rw [star_neg, neg_mul, Complex.neg_re, c3, neg_neg]
  rw [r, c1] at e1
  rw [r, c2] at e2
  rw [r, c3] at e3
  rw [r, c4] at e4
  have habs : ∀ x : ℝ, max x 0 + max (-x) 0 = |x| := fun x => by
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith), abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, max_eq_right (by linarith), abs_of_nonneg hx]; ring
  have hκ := norm_nonneg (deviceCoherence Ψ₀)
  set κ := ‖deviceCoherence Ψ₀‖
  have hc := habs (R * (κ * Real.cos (R * s)))
  have hs := habs (R * -(κ * Real.sin (R * s)))
  rw [show R * -(κ * Real.cos (R * s)) = -(R * (κ * Real.cos (R * s))) by ring] at e2
  rw [show R * (κ * Real.sin (R * s)) = -(R * -(κ * Real.sin (R * s))) by ring] at e4
  have hRc : |R * (κ * Real.cos (R * s))| + |R * -(κ * Real.sin (R * s))|
      = |R| * κ * (|Real.cos (R * s)| + |Real.sin (R * s)|) := by
    simp only [abs_mul, abs_neg, abs_of_nonneg hκ]
    ring
  rw [abs_of_nonneg hR] at hRc
  rw [quadRate]
  rw [abs_le] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

theorem continuous_quadRate (J μ₀ μ₁ : ℝ) (Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    Continuous (quadRate (L := L) J μ₀ μ₁ Ψ₀) :=
  (((continuous_rateWeight J μ₀ μ₁ _).add (continuous_rateWeight J μ₀ μ₁ _)).add
    (continuous_rateWeight J μ₀ μ₁ _)).add (continuous_rateWeight J μ₀ μ₁ _)

/-- `|cos x| + |sin x| ≥ 1`: the quadrature rate never stalls. -/
theorem one_le_abs_cos_add_abs_sin (x : ℝ) : 1 ≤ |Real.cos x| + |Real.sin x| := by
  have h := Real.cos_sq_add_sin_sq x
  have hc := abs_nonneg (Real.cos x)
  have hs := abs_nonneg (Real.sin x)
  have h2 : (|Real.cos x| + |Real.sin x|) ^ 2 ≥ 1 := by
    nlinarith [sq_abs (Real.cos x), sq_abs (Real.sin x), mul_nonneg hc hs]
  nlinarith

/-- **The quadrature clock's ideal response**: `F(t) = ∫₀ᵗ R |C₀| (|cos Rs| + |sin Rs|) ds`. -/
noncomputable def quadResponse (R κ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, R * κ * (|Real.cos (R * s)| + |Real.sin (R * s)|)

/-- ★★ **The response rises at slope at least `R κ`.** -/
theorem quadResponse_slope {R κ : ℝ} (hR : 0 ≤ R) (hκ : 0 ≤ κ) {t t' : ℝ} (h : t ≤ t') :
    R * κ * (t' - t) ≤ quadResponse R κ t' - quadResponse R κ t := by
  have hc : Continuous fun s => R * κ * (|Real.cos (R * s)| + |Real.sin (R * s)|) := by fun_prop
  rw [quadResponse, quadResponse, intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable 0 t') (hc.intervalIntegrable 0 t)]
  have hm := intervalIntegral.integral_mono_on h
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := R * κ))
    (hc.intervalIntegrable t t') fun s _ => by
      have := one_le_abs_cos_add_abs_sin (R * s)
      have hRk : 0 ≤ R * κ := mul_nonneg hR hκ
      nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  linarith

/-- ★★★ **The quadrature clock tracks its response.** With the device's drift
`‖S(s) − R e^{−iRs} C₀‖ ≤ (1 + R|s|) ε`, the register `∫₀ᵗ quadRate` stays within
`4ε (t + R t²/2)` of the response. -/
theorem abs_integral_quadRate_sub_le {J μ₀ μ₁ R ε : ℝ} {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) (hR : 0 ≤ R)
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
    {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, quadRate J μ₀ μ₁ Ψ₀ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      - quadResponse R ‖deviceCoherence Ψ₀‖ t| ≤ 4 * ε * (t + R * t ^ 2 / 2) := by
  have hG := (continuous_weight_deviceProp J μ₀ μ₁ (continuous_quadRate J μ₀ μ₁ Ψ₀)
    Ψ₀).intervalIntegrable (μ := MeasureTheory.volume) 0 t
  have hF : IntervalIntegrable (fun s => R * ‖deviceCoherence Ψ₀‖
      * (|Real.cos (R * s)| + |Real.sin (R * s)|)) MeasureTheory.volume 0 t :=
    (by fun_prop : Continuous fun s => R * ‖deviceCoherence Ψ₀‖
      * (|Real.cos (R * s)| + |Real.sin (R * s)|)).intervalIntegrable 0 t
  rw [quadResponse, ← intervalIntegral.integral_sub hG hF, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => 4 * ε * (1 + R * s)) ht
    (Filter.Eventually.of_forall fun s hs => ?_)
    ((by fun_prop : Continuous fun s : ℝ => 4 * ε * (1 + R * s)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 t)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    have h := abs_quadRate_sub_le hC hR (hdrift s)
    rw [abs_of_pos hs.1] at h
    exact h.trans_eq (by ring)
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => R * x).intervalIntegrable 0 t),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
    ring

/-- ★★★ **The quadrature clock reads time, with no tick period.** A device with drift
`(1 + R|s|) ε`, splitting `R > 0` and coherence `C₀ ≠ 0`, read by thresholds `θ`, `θ + Δ` on its
quadrature register: an event at time `t` between the two records, within `[0, T]`, is read as the
time `t₀` at which the response reaches `θ` within `(Δ + 12ε(T + RT²/2))/(R|C₀|)`. The threshold
spacing `Δ` is arbitrary; the floor is the drift. -/
theorem quad_clock_reading_error {J μ₀ μ₁ R ε : ℝ} {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) (hR : 0 < R)
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
    {θ Δ τ₀ τ₁ t₀ t₁ t T : ℝ}
    (h₀ : 0 ≤ τ₀) (h₁ : τ₁ ≤ T)
    (hc₀ : ∫ s in (0 : ℝ)..τ₀, quadRate J μ₀ μ₁ Ψ₀ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀) = θ)
    (hc₁ : ∫ s in (0 : ℝ)..τ₁, quadRate J μ₀ μ₁ Ψ₀ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      = θ + Δ)
    (ht₀0 : 0 ≤ t₀) (ht₁T : t₁ ≤ T) (hF₀ : quadResponse R ‖deviceCoherence Ψ₀‖ t₀ = θ)
    (hF₁ : quadResponse R ‖deviceCoherence Ψ₀‖ t₁ = θ + Δ) (ht₀₁ : t₀ ≤ t₁)
    (hτ : τ₀ ≤ t) (hτ' : t ≤ τ₁) :
    |t - t₀| ≤ (Δ + 3 * (4 * ε * (T + R * T ^ 2 / 2))) / (R * ‖deviceCoherence Ψ₀‖) := by
  have hε : 0 ≤ ε := by
    have h0 := hdrift 0
    rw [abs_zero, mul_zero, add_zero, one_mul] at h0
    exact (norm_nonneg _).trans h0
  have hκ : 0 < ‖deviceCoherence Ψ₀‖ := norm_pos_iff.2 hC
  exact clock_reading_error (G := fun t => ∫ s in (0 : ℝ)..t,
      quadRate J μ₀ μ₁ Ψ₀ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
    (F := quadResponse R ‖deviceCoherence Ψ₀‖) (by positivity)
    (fun a b _ hab _ => quadResponse_slope hR.le hκ.le hab)
    (fun a ha haT => (abs_integral_quadRate_sub_le hC hR.le hdrift ha).trans (by
      have : a + R * a ^ 2 / 2 ≤ T + R * T ^ 2 / 2 := by
        have : a ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ha haT 2
        nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)))
    h₀ h₁ hc₀ hc₁ ht₀0 ht₁T hF₀ hF₁ ht₀₁ hτ hτ'


end Quadrature

end CSD.RecordLayer
