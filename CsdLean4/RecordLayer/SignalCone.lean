/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MovingRadar
public import CsdLean4.CV.DiracPacket
public import CsdLean4.CV.LocalLiebRobinson

/-!
# Is there a common signal cone?

**Category:** 7-SigmaLayer (the record layer). BACKLOG #246 (the author's fourth operational-geometry
brief, step 6).

The brief asks whether the two observers share a **limiting signal speed**, and asks that three things
be kept apart: the Lieb–Robinson **upper bound** (`localLRVelocity = 8eΔγ`, ~~#213~~), the **measured**
propagation (the fastest group velocity over the admissible preparations), and a limiting speed
**shared across observers**. This file answers for the control (A) and prices the measured
propagation of the test chain (B) against the bound.

## The control (A): there is no cone

* `bounceTime_neg_mul`; ★★ `exchGeom_through` — the messenger of relative speed `w` prepared at
  `ρ = −wτ` reaches the event (the bounce at time `τ`) once `w` exceeds `|y|` and the window's reach;
  ★★★ `admissible_speed_unbounded` — **through every event, messengers faster than any proposed
  limit are admissible**;
* `radarOffset_eq` (closed form `(2Dy + w)/(2(w² − y²))`); ★★ `radarTime_through` — the first
  observer's radar time of the event through messenger `w` is `τ + radarOffset`; ★★
  `tendsto_radarOffset` — **the radar time reaches the event's time only as `w → ∞`**, and ★★
  `radarOffset_pos` — never at a finite speed when the observer recedes or rests;
* `exchEmit_duration`, `exchReturn_duration`, `reception_duration` and their record forms ★★
  `emissionWrite_duration`, `returnWrite_duration`, `receptionWrite_duration` — **the speeds the
  records measure**: each write lasts one cell over the messenger's speed past that detector, so the
  first observer measures `y + w` out and `w − y` back and the moving observer measures `w`;
* ★★★ `half_anisotropy` — **the relative velocity is read off any messenger**: half the difference
  of the two speeds the first observer measures is `y`, whatever the preparation; ★★ `mean_speed`
  (Galilean addition: their mean is the moving observer's `w`); ★★ `outSpeed_ne_retSpeed` — **no
  speed is common to the two observers** once they move.

## The test chain (B): the measured propagation against the bound

* `maxGroupVel J μ = √(μ² + (2J)²) − μ`, ★ `maxGroupVel_eq_bandwidth` (the upper band's width);
* ★★★ `abs_groupVel_le_maxGroupVel` and ★★★ `exists_groupVel_eq_maxGroupVel` — **the fastest
  packet of the species `μ` moves at exactly `√(μ² + (2J)²) − μ`**, reached at
  `sin² θ = μ/(R + μ)`; the identity behind the bound is
  `((R − μ)E)² − (4J² sin θ cos θ)² = (R − μ)²(μ − (R + μ) sin² θ)²`. By ~~#250~~'s `dirac_packet`
  a packet centred at `θ` is carried at `groupVel J μ θ`, so this is the measured propagation;
* ★★ `abs_two_mul_sub_le_maxGroupVel`, `maxGroupVel_le`, ★★★ `maxGroupVel_lt` — `2|J| − μ ≤ v_max <
  2|J|`: **a massive species never reaches `c = 2|J|`**, and ★★ `exists_maxGroupVel_gt` — `c` is the
  supremum over all species;
* `localLRVelocity_two` (`8e · 2|J|`), ★★★ `twentyOne_mul_maxGroupVel_lt` — **the bound exceeds the
  measured propagation more than twenty-one times** (the ratio to `c` is `8e ≈ 21.7`);
* ★★★ `signal_cone` — the capstone.

## The findings

1. **(A) has no common cone, and the dependence is quantified.** Admissible messengers have every
   speed; the chart of one event depends on the messenger by `radarOffset`, and the
   preparation-independent time, the event's own time, appears only in the limit of infinitely fast
   messengers. That limit is Galilean absolute simultaneity, as the control's dispersion class
   (#241) predicts. **What every messenger agrees on is the relative velocity** (`half_anisotropy`),
   which is the input #247 wants for the control's transformation.
2. **(B)'s bound is not its propagation.** On the Dirac chain the measured propagation is capped by
   `c = 2|J|`, which is the supremum over species and preparations and is reached by none. The local
   Lieb–Robinson velocity is `8e` times `c`. So the bound does not supply the chain's `c`; the band
   does.
3. **On the lattice each massive species has its own cap, `√(c² + μ²) − μ`.** In the continuum every
   species approaches `c` at high momentum. Here the lattice's bounded momentum stops it short, by
   a positive amount of at most `μ`. This is a lattice effect, a preferred frame, like
   ~~#249~~'s `lattice_dilation_defect`, now on speeds.

## Honest scope

⚠️ **The Lieb–Robinson comparison is between numbers.** `localLRVelocity 2 |J|` is #213's velocity at
degree `2` and edge strength `|J|`, the Dirac hop's coupling. #213 proves its bound for field-structured
flows; the Dirac chain is a one-particle operator on `ZMod L × Fin 2`, and its own light-cone bound is
#258.

⚠️ **Whether (B)'s `c` is shared by observers in relative motion is #256** (exchanges and radar charts
on the chain, behind #252 and #253). This file shows only that `c` bounds every packet of every
species in the chain's frame.

⚠️ **(A)'s speeds are in the time of the dynamics.** Read on the observers' clocks they carry #243's
clock errors (`abs_restReading_sub_le`, `abs_movingObsReading_sub_le`), which these durations do not
restate.

References: `specs/BACKLOG.md` #246, #241, #245, #247, #256, #258, #213, #250, #39;
`RecordLayer/MovingRadar.lean` (`radarOffset`, `ExchGeom.radarTime_radar`,
`radarTime_ne_of_speed_ne`); `RecordLayer/MovingExchange.lean` (`ExchGeom`, `emissionWrite`,
`returnWrite`, `receptionWrite`); `CV/DiracPacket.lean` (`groupVel`, `groupVel_eq`,
`dirac_packet`); `CV/DiracClockChain.lean` (`dispE`, `abs_groupVel_le`);
`CV/LocalLiebRobinson.lean` (`localLRVelocity`).
-/

@[expose] public section

open Filter Topology Set CSD.CV

namespace CSD.RecordLayer

/-! ### The control (A): messengers of every speed through every event -/

theorem bounceTime_neg_mul {w : ℝ} (hw : w ≠ 0) (τ : ℝ) : bounceTime (-(w * τ)) w = τ := by
  rw [bounceTime, neg_neg, mul_comm, mul_div_assoc, div_self hw, mul_one]

/-- ★★ **A messenger of any large enough speed reaches any event.** The bounce off the moving
observer at time `τ > 0`, when it is beyond the first observer's window, is reached by the messenger
of relative speed `w` prepared at `ρ = −wτ`, as soon as `w` exceeds `|y|` and the window's reach. -/
theorem exchGeom_through {d y τ w : ℝ} (hD : 1 / 2 ≤ d + y * τ) (hy : |y| < w)
    (hd : d + 1 / 2 < w * τ) (h1 : 1 / 2 < w * τ) :
    ExchGeom d y (-(w * τ)) w ∧ bounceTime (-(w * τ)) w = τ := by
  have hw : 0 < w := lt_of_le_of_lt (abs_nonneg y) hy
  have hb := bounceTime_neg_mul hw.ne' τ
  refine ⟨⟨hw, ?_, ?_, by linarith, by linarith, ?_⟩, hb⟩
  · rw [outSpeed]
    linarith [neg_abs_le y]
  · rw [retSpeed]
    linarith [le_abs_self y]
  · rw [bounceSep, hb]
    exact hD

/-- ★★★ **The control has no speed bound**: through every event, messengers faster than any
proposed limit `V` are admissible preparations. -/
theorem admissible_speed_unbounded {d y τ : ℝ} (hτ : 0 < τ) (hD : 1 / 2 ≤ d + y * τ) (V : ℝ) :
    ∃ w, V < w ∧ ExchGeom d y (-(w * τ)) w ∧ bounceTime (-(w * τ)) w = τ := by
  set M := max (max V |y|) (max ((d + 1 / 2) / τ) (1 / 2 / τ))
  have hA : max V |y| ≤ M := le_max_left _ _
  have hB : max ((d + 1 / 2) / τ) (1 / 2 / τ) ≤ M := le_max_right _ _
  have hV : V ≤ M := (le_max_left _ _).trans hA
  have hy : |y| ≤ M := (le_max_right _ _).trans hA
  have hd : (d + 1 / 2) / τ ≤ M := (le_max_left _ _).trans hB
  have h1 : 1 / 2 / τ ≤ M := (le_max_right _ _).trans hB
  refine ⟨M + 1, by linarith, exchGeom_through hD (by linarith) ?_ ?_⟩
  · exact (div_lt_iff₀ hτ).1 (by linarith)
  · exact (div_lt_iff₀ hτ).1 (by linarith)

/-- **The radar offset in closed form**: `(2Dy + w) / (2(w² − y²))`. -/
theorem radarOffset_eq {D y w : ℝ} (hy : |y| < w) :
    radarOffset D y w = (2 * D * y + w) / (2 * (w ^ 2 - y ^ 2)) := by
  have h1 : 0 < w - y := by linarith [le_abs_self y]
  have h2 : 0 < y + w := by linarith [neg_abs_le y]
  have h3 : w ^ 2 - y ^ 2 = (w - y) * (y + w) := by ring
  rw [radarOffset, h3]
  field_simp
  ring

/-- ★★ **The radar time reaches the event's time only in the limit of infinitely fast
messengers.** -/
theorem tendsto_radarOffset (D y : ℝ) : Tendsto (radarOffset D y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun w : ℝ => w - y) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-y) tendsto_id
  have h2 : Tendsto (fun w : ℝ => y + w) atTop atTop := by
    simpa using tendsto_atTop_add_const_left atTop y tendsto_id
  have h := (((tendsto_const_nhds (x := D + 1 / 2)).div_atTop h1).sub
    ((tendsto_const_nhds (x := D - 1 / 2)).div_atTop h2)).div_const 2
  simp only [sub_zero, zero_div] at h
  exact h

/-- ★★ **…and never reaches it**: when the observer recedes (or rests), every admissible messenger
dates the event strictly later than it happened. -/
theorem radarOffset_pos {D y w : ℝ} (hy : 0 ≤ y) (hD : 0 ≤ D) (hw : y < w) :
    0 < radarOffset D y w := by
  have hy' : |y| < w := by rwa [abs_of_nonneg hy]
  rw [radarOffset_eq hy']
  have hDy : 0 ≤ 2 * D * y := mul_nonneg (mul_nonneg zero_le_two hD) hy
  have hww : 0 < (w - y) * (w + y) := mul_pos (by linarith) (by linarith)
  exact div_pos (by linarith) (by nlinarith)

/-- ★★ **The radar time of one event through each admissible messenger**: the event's time plus the
offset at the event's separation. -/
theorem radarTime_through {d y τ w : ℝ} (h : ExchGeom d y (-(w * τ)) w) :
    h.radar.radarTime = τ + radarOffset (d + y * τ) y w := by
  rw [h.radarTime_radar, bounceSep, bounceTime_neg_mul h.w_pos.ne']

/-! ### The control (A): the speeds the records measure -/

/-- The emission write lasts `1/(y + w)`: **the outward speed measured by the first observer's
detector** (one cell over the time the messenger takes to cross it). -/
theorem exchEmit_duration (d y ρ w : ℝ) :
    exchEmitEnd d y ρ w - exchEmitStart d y ρ w = 1 / outSpeed y w := by
  rw [exchEmitEnd, exchEmitStart, ← sub_div]
  congr 1
  ring

/-- The return write lasts `1/(w − y)`: **the return speed measured by the same detector**. -/
theorem exchReturn_duration (d y ρ w : ℝ) :
    exchReturnEnd d y ρ w - exchReturnStart d y ρ w = 1 / retSpeed y w := by
  rw [exchReturnEnd, exchReturnStart, add_sub_add_left_eq_sub, ← sub_div]
  congr 1
  ring

/-- The reception write lasts `1/w`: **the speed measured by the moving observer's detector**. -/
theorem reception_duration (ρ w : ℝ) : (1 / 2 - ρ) / w - (-(1 / 2) - ρ) / w = 1 / w := by
  rw [← sub_div]
  congr 1
  ring

/-- ★★★ **The relative velocity is read off any messenger**: half the difference of the outward and
return speeds the first observer measures is `y`, whatever the messenger. -/
theorem half_anisotropy (y w : ℝ) : (outSpeed y w - retSpeed y w) / 2 = y := by
  rw [outSpeed, retSpeed]
  ring

/-- ★★ **Galilean addition**: the mean of the two speeds the first observer measures is the speed
the moving observer measures. -/
theorem mean_speed (y w : ℝ) : (outSpeed y w + retSpeed y w) / 2 = w := by
  rw [outSpeed, retSpeed]
  ring

/-- ★★ **No speed is common to the two observers**: in relative motion, every messenger has
different outward and return speeds for the first observer, while the moving observer measures one
speed both ways. -/
theorem outSpeed_ne_retSpeed {y : ℝ} (hy : y ≠ 0) (w : ℝ) : outSpeed y w ≠ retSpeed y w := by
  intro h
  apply hy
  rw [← half_anisotropy y w, h, sub_self, zero_div]

section Writes

variable {N : ℕ} {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★ **The outward speed as a record**: the emission write's duration. -/
theorem emissionWrite_duration (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (site : Finset (Fin K)) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.1 k = 0)
    (hG : ExchGeom (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :
    (emissionWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeEnd
        - (emissionWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeStart
      = 1 / outSpeed (exchSepVel m x₀) (x₀.2.2.1 k).2 :=
  exchEmit_duration _ _ _ _

/-- ★★ **The return speed as a record**: the return write's duration. -/
theorem returnWrite_duration (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (site : Finset (Fin K)) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.1 k = 0)
    (hG : ExchGeom (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :
    (returnWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeEnd
        - (returnWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeStart
      = 1 / retSpeed (exchSepVel m x₀) (x₀.2.2.1 k).2 :=
  exchReturn_duration _ _ _ _

/-- ★★ **The moving observer's speed as a record**: the reception write's duration. -/
theorem receptionWrite_duration (hf1 : ContDiff ℝ 1 f) {K : ℕ} (site : Finset (Fin K)) (θ : ℝ)
    (hθ0 : 0 < θ) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.2 k = 0) (hw : 0 < (x₀.2.2.1 k).2)
    (hρ : (x₀.2.2.1 k).1 < -(1 / 2)) (hθ : θ ≤ gd * ((x₀.2.2.1 k).2)⁻¹) :
    (receptionWrite J ħ g hf m gd hf1 site θ hθ0 k x₀ hreg hw hρ hθ).writeEnd
        - (receptionWrite J ħ g hf m gd hf1 site θ hθ0 k x₀ hreg hw hρ hθ).writeStart
      = 1 / (x₀.2.2.1 k).2 :=
  reception_duration _ _

end Writes

/-! ### The test chain (B): the measured propagation against the bound -/

/-- **The fastest group velocity of the Dirac chain**, `√(μ² + (2J)²) − μ`. -/
noncomputable def maxGroupVel (J μ : ℝ) : ℝ := dispE μ (2 * J) - μ

/-- ★ **It is the band's width**: the top of the upper band minus its bottom. -/
theorem maxGroupVel_eq_bandwidth (J : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    maxGroupVel J μ = bandE J μ (Real.pi / 2) - bandE J μ 0 := by
  simp [maxGroupVel, bandE, dispE, Real.sqrt_sq hμ]

/-- ★★★ **No packet of the species `μ` outruns `√(μ² + (2J)²) − μ`.** The identity behind it:
`((R − μ)E)² − (4J² sin θ cos θ)² = (R − μ)²(μ − (R + μ) sin² θ)²`. -/
theorem abs_groupVel_le_maxGroupVel {J μ : ℝ} (hμ : 0 < μ) (θ : ℝ) :
    |groupVel J μ θ| ≤ maxGroupVel J μ := by
  have hE := dispE_pos hμ (2 * J * Real.sin θ)
  have hE2 := dispE_sq μ (2 * J * Real.sin θ)
  have hR2 := dispE_sq μ (2 * J)
  have hRμ := le_dispE μ (2 * J)
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [groupVel_eq hμ, bandE, abs_div, abs_of_pos hE, div_le_iff₀ hE, Real.sin_two_mul, maxGroupVel]
  apply abs_le_of_sq_le_sq _ (mul_nonneg (by linarith) hE.le)
  set R := dispE μ (2 * J)
  set E := dispE μ (2 * J * Real.sin θ)
  set S := Real.sin θ
  set C := Real.cos θ
  have key : ((R - μ) * E) ^ 2 - (2 * J ^ 2 * (2 * S * C)) ^ 2
      = (R - μ) ^ 2 * (μ - (R + μ) * S ^ 2) ^ 2 := by
    linear_combination (R - μ) ^ 2 * hE2
      + (S ^ 2 * (-(R - μ) ^ 2 + (1 - S ^ 2) * (R ^ 2 - μ ^ 2 + 4 * J ^ 2))) * hR2
      - (4 * J ^ 2) ^ 2 * S ^ 2 * hsc
  have : 0 ≤ (R - μ) ^ 2 * (μ - (R + μ) * S ^ 2) ^ 2 := by positivity
  linarith

/-- ★★★ **…and some packet reaches it**: at `sin² θ = μ/(R + μ)`. -/
theorem exists_groupVel_eq_maxGroupVel {J μ : ℝ} (hμ : 0 < μ) :
    ∃ θ, groupVel J μ θ = maxGroupVel J μ := by
  have hR2 := dispE_sq μ (2 * J)
  have hRμ := le_dispE μ (2 * J)
  set R := dispE μ (2 * J)
  have hRμ' : 0 < R + μ := by linarith
  set x := Real.sqrt (μ / (R + μ))
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = μ / (R + μ) := Real.sq_sqrt (div_nonneg hμ.le hRμ'.le)
  have hxm : x ^ 2 * (R + μ) = μ := by
    rw [hx2]
    field_simp
  have hx1 : x ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hRμ').2 (by linarith))
  refine ⟨Real.arcsin x, ?_⟩
  have hS : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hC0 := Real.cos_arcsin_nonneg x
  have hsc := Real.sin_sq_add_cos_sq (Real.arcsin x)
  rw [hS] at hsc
  have hE := dispE_pos hμ (2 * J * x)
  have hE2 := dispE_sq μ (2 * J * x)
  rw [groupVel_eq hμ, bandE, Real.sin_two_mul, hS, div_eq_iff hE.ne', maxGroupVel]
  set C := Real.cos (Real.arcsin x)
  set E := dispE μ (2 * J * x)
  rw [← pow_left_inj₀ (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg zero_le_two hx0) hC0))
    (mul_nonneg (by linarith) hE.le) two_ne_zero]
  linear_combination (-(R - μ) ^ 2 * (x ^ 2 * (R + μ) - μ)) * hxm
    + (x ^ 2 * (1 - x ^ 2) * ((R ^ 2 - μ ^ 2 - 4 * J ^ 2) - 2 * (R ^ 2 - μ ^ 2))
      + (R - μ) ^ 2 * x ^ 2) * hR2
    + (4 * J ^ 2) ^ 2 * x ^ 2 * hsc - (R - μ) ^ 2 * hE2

/-- ★★ **The species' cap lies within `μ` below `c = 2|J|`.** -/
theorem abs_two_mul_sub_le_maxGroupVel (J μ : ℝ) : |2 * J| - μ ≤ maxGroupVel J μ := by
  have := abs_le_dispE μ (2 * J)
  rw [maxGroupVel]
  linarith

theorem maxGroupVel_le (J : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) : maxGroupVel J μ ≤ |2 * J| := by
  rw [maxGroupVel, sub_le_iff_le_add, dispE,
    show |2 * J| + μ = Real.sqrt ((|2 * J| + μ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_abs (2 * J), mul_nonneg (abs_nonneg (2 * J)) hμ])

/-- ★★★ **A massive species never reaches `c`**: its cap is strictly below `2|J|`. -/
theorem maxGroupVel_lt {J μ : ℝ} (hJ : J ≠ 0) (hμ : 0 < μ) : maxGroupVel J μ < |2 * J| := by
  have hJ' : 0 < |2 * J| := abs_pos.2 (mul_ne_zero two_ne_zero hJ)
  rw [maxGroupVel, sub_lt_iff_lt_add, dispE,
    show |2 * J| + μ = Real.sqrt ((|2 * J| + μ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith [sq_abs (2 * J), mul_pos hJ' hμ])

/-- ★★ **`c = 2|J|` is the supremum over every species**: light enough species come within any
`ε` of it. -/
theorem exists_maxGroupVel_gt (J : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ, 0 < μ ∧ |2 * J| - ε < maxGroupVel J μ :=
  ⟨ε / 2, by positivity, by linarith [abs_two_mul_sub_le_maxGroupVel J (ε / 2)]⟩

/-- **#213's local Lieb–Robinson velocity at degree `2` and edge strength `|J|`** is `8e · 2|J|`. -/
theorem localLRVelocity_two (J : ℝ) : localLRVelocity 2 |J| = 8 * Real.exp 1 * |2 * J| := by
  rw [localLRVelocity, abs_mul, abs_two]
  push_cast
  ring

/-- ★★★ **The measured propagation is far below the bound**: more than twenty-one times. -/
theorem twentyOne_mul_maxGroupVel_lt {J μ : ℝ} (hJ : J ≠ 0) (hμ : 0 ≤ μ) :
    21 * maxGroupVel J μ < localLRVelocity 2 |J| := by
  rw [localLRVelocity_two]
  have he := Real.exp_one_gt_d9
  have hJ' : 0 < |2 * J| := abs_pos.2 (mul_ne_zero two_ne_zero hJ)
  have := maxGroupVel_le J hμ
  nlinarith [mul_pos hJ' (by linarith : (0 : ℝ) < 8 * Real.exp 1 - 21)]

/-! ### The capstone -/

/-- ★★★ **Is there a common signal cone? (#246).** For the control (A), at any event (the bounce at
time `τ > 0`, the moving observer beyond the first's window): messengers of every speed reach it; the
first observer's radar time of it through the messenger of speed `w` is `τ + radarOffset`, the offset
positive when the observer recedes and tending to `0` only as `w → ∞`; the speeds the records measure
are `y + w` out and `w − y` back for the first observer, their half-difference the relative velocity
`y` whatever the messenger, their mean the moving observer's `w`. For the test chain (B), at
coupling `J ≠ 0` and rest energy `μ > 0`: no packet's group velocity exceeds `√(μ² + (2J)²) − μ`,
some packet's equals it, it lies within `μ` below `c = 2|J|` and strictly below it, and #213's local
Lieb–Robinson velocity at the same edge strength exceeds it more than twenty-one times. -/
theorem signal_cone {d y τ : ℝ} (hτ : 0 < τ) (hD : 1 / 2 ≤ d + y * τ) {J μ : ℝ} (hJ : J ≠ 0)
    (hμ : 0 < μ) :
    (∀ V, ∃ w, V < w ∧ ExchGeom d y (-(w * τ)) w ∧ bounceTime (-(w * τ)) w = τ)
    ∧ (∀ w (h : ExchGeom d y (-(w * τ)) w), h.radar.radarTime = τ + radarOffset (d + y * τ) y w)
    ∧ Tendsto (radarOffset (d + y * τ) y) atTop (𝓝 0)
    ∧ (0 ≤ y → ∀ w, y < w → 0 < radarOffset (d + y * τ) y w)
    ∧ (∀ ρ w, exchEmitEnd d y ρ w - exchEmitStart d y ρ w = 1 / outSpeed y w
        ∧ exchReturnEnd d y ρ w - exchReturnStart d y ρ w = 1 / retSpeed y w
        ∧ (outSpeed y w - retSpeed y w) / 2 = y ∧ (outSpeed y w + retSpeed y w) / 2 = w)
    ∧ (∀ θ, |groupVel J μ θ| ≤ maxGroupVel J μ)
    ∧ (∃ θ, groupVel J μ θ = maxGroupVel J μ)
    ∧ |2 * J| - μ ≤ maxGroupVel J μ ∧ maxGroupVel J μ < |2 * J|
    ∧ 21 * maxGroupVel J μ < localLRVelocity 2 |J| :=
  ⟨admissible_speed_unbounded hτ hD, fun _ h => radarTime_through h, tendsto_radarOffset _ _,
    fun hy _ hw => radarOffset_pos hy (by linarith) hw,
    fun ρ w => ⟨exchEmit_duration d y ρ w, exchReturn_duration d y ρ w, half_anisotropy y w,
      mean_speed y w⟩,
    abs_groupVel_le_maxGroupVel hμ, exists_groupVel_eq_maxGroupVel hμ,
    abs_two_mul_sub_le_maxGroupVel J μ, maxGroupVel_lt hJ hμ, twentyOne_mul_maxGroupVel_lt hJ hμ.le⟩

end CSD.RecordLayer

end
