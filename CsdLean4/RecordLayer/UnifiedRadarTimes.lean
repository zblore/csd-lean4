/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarSkeleton
public import CsdLean4.CV.DiracClockChain

/-!
# The four times of the radar run, and what a slower messenger costs

**Category:** 7-SigmaLayer (the record layer). BACKLOG #412 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R3 of the list under
UD-164, first part. No new assumption.

The top-down statement of #402 takes four times `T_E, T_R, T_Ret, T_M` with the two relations
`T_R − T_E = v (T_M − T_E)` and `T_Ret − T_R = v (T_M − T_Ret)`, and by the test of UO-16 they
may not stay hypotheses. This module defines them for the run of UA-18 (b): the emission at
`0`, the moving observer at the distance `d` from the wall, velocity `v` toward it. It proves
the two relations, and bounds how far the crossing times of straight motion are from them
when the messenger's speed is `u ≤ 1`.

* `radarTR`, `radarTRet`, `radarTM`, ★★ `radar_times_relay`, ★★ `radar_times_return` — the
  times `d`, `2d/(1 + v)`, `d/v` satisfy the two relations of #402 with `T_E = 0`;
* `crossRelay`, `crossReturn`, `crossRelay_spec`, `crossReturn_spec` — the times at which a
  messenger of speed `u` reaches the wall, and meets the observer again after reflection;
* ★ `abs_crossRelay_sub`, ★ `abs_crossReturn_sub_le` — they differ from `T_R` and `T_Ret` by
  `d (1 − u)/u` and by at most `2 d (1 − u)/u`;
* ★★ `one_sub_vRel_le` — for a packet of rest energy `μ` at the momentum term `p > 0`:
  `1 − v ≤ μ²/(2 p²)`.

## Exact scope

* **Arithmetic of straight motion.** The times are those of points moving at constant
  speeds on the folded chain. That the gates of UA-18 close at flow times near them is not
  shown: that needs the arcs' widths over the angular speeds, and is the rest of R3.
* **The relations hold exactly because the kinematic times are defined at messenger speed
  `1`.** A messenger at speed `u < 1` reaches the wall and returns later; the two bounds are
  the least tolerances `τ_R`, `τ_Ret` that #402 must then carry, before any width.
* **The messenger must be fast.** The tolerances are of relative size `(1 − u)/u`, to be
  small against the dilation `v²/2`. With `one_sub_vRel_le` that asks `μ²/p²` small against
  `v²`. The wall states of #409 and #411 have `μ ≥ 1` and `p ≤ 1/2`, so `u ≤ 0.45`: they do
  not meet it. A messenger with `μ` small and its budgets is not built.
* **`v` here is the relativistic velocity at a momentum term**, as in #406; the lattice's
  band velocity differs from it by a factor that is not bounded here, and the clock's two
  levels move at slightly different velocities.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-171, UD-181); `RecordLayer/UnifiedRadarSkeleton.lean` (#402:
`radar_lorentz_of_histories`, the hypotheses `hE`, `hRet`, `hτR`, `hτRet`);
`CV/DiracClockChain.lean` (`vRel`, `dispE`, `dispE_sq`, `abs_le_dispE`);
`RecordLayer/UnifiedWallOrbits.lean` (#411: the slow messenger).
-/

@[expose] public section

noncomputable section

open CSD.CV

namespace CSD.RecordLayer

/-! ### The kinematic times -/

/-- **The relay time**: a messenger at speed `1` reaches the wall at the distance `d`. -/
def radarTR (d : ℝ) : ℝ := d

/-- **The return time**: reflected at the wall, it meets the observer coming at velocity
`v`. -/
def radarTRet (d v : ℝ) : ℝ := 2 * d / (1 + v)

/-- **The meeting time**: the observer reaches the wall. -/
def radarTM (d v : ℝ) : ℝ := d / v

/-- ★★ **The first relation of #402**, with the emission at `0`:
`T_R − T_E = v (T_M − T_E)`. -/
theorem radar_times_relay (d : ℝ) {v : ℝ} (hv : 0 < v) :
    radarTR d - 0 = v * (radarTM d v - 0) := by
  rw [radarTR, radarTM, sub_zero, sub_zero, mul_div_cancel₀ _ hv.ne']

/-- ★★ **The second relation of #402**: `T_Ret − T_R = v (T_M − T_Ret)`. -/
theorem radar_times_return (d : ℝ) {v : ℝ} (hv : 0 < v) :
    radarTRet d v - radarTR d = v * (radarTM d v - radarTRet d v) := by
  have h1 : (1 + v) ≠ 0 := by positivity
  have h2 : v ≠ 0 := hv.ne'
  have e : 2 * d / (1 + v) * (1 + v) = 2 * d := div_mul_cancel₀ _ h1
  rw [radarTRet, radarTR, radarTM, mul_sub, mul_div_cancel₀ _ h2]
  linear_combination e

/-! ### A messenger at speed `u` -/

/-- The time at which a messenger of speed `u` reaches the wall at the distance `d`. -/
def crossRelay (d u : ℝ) : ℝ := d / u

/-- The time at which it meets the observer again, after reflection at the wall. -/
def crossReturn (d u v : ℝ) : ℝ := 2 * d / (u + v)

theorem crossRelay_spec (d : ℝ) {u : ℝ} (hu : 0 < u) : u * crossRelay d u = d := by
  rw [crossRelay, mul_div_cancel₀ _ hu.ne']

/-- At `crossReturn` the messenger, back from the wall, is where the observer is. -/
theorem crossReturn_spec (d : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    u * (crossReturn d u v - crossRelay d u) = d - v * crossReturn d u v := by
  have h1 : u + v ≠ 0 := by positivity
  have e : crossReturn d u v * (u + v) = 2 * d := by
    rw [crossReturn, div_mul_cancel₀ _ h1]
  rw [mul_sub, crossRelay_spec d hu]
  linarith

/-- ★ **The relay comes late by `d (1 − u)/u`.** -/
theorem abs_crossRelay_sub (d : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hd : 0 ≤ d) :
    |crossRelay d u - radarTR d| = d * (1 - u) / u := by
  have e : crossRelay d u - radarTR d = d * (1 - u) / u := by
    rw [crossRelay, radarTR, eq_div_iff hu.ne', sub_mul, div_mul_cancel₀ _ hu.ne']
    ring
  rw [e, abs_of_nonneg (div_nonneg (mul_nonneg hd (by linarith)) hu.le)]

/-- ★ **The return comes late by at most `2 d (1 − u)/u`.** -/
theorem abs_crossReturn_sub_le (d : ℝ) {u v : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 ≤ v)
    (hd : 0 ≤ d) : |crossReturn d u v - radarTRet d v| ≤ 2 * d * (1 - u) / u := by
  have h1 : 0 < u + v := by positivity
  have h2 : 0 < 1 + v := by positivity
  have e : crossReturn d u v - radarTRet d v = 2 * d * (1 - u) / ((u + v) * (1 + v)) := by
    rw [crossReturn, radarTRet, div_sub_div _ _ h1.ne' h2.ne']
    congr 1
    ring
  have hnum : 0 ≤ 2 * d * (1 - u) := mul_nonneg (mul_nonneg (by norm_num) hd) (by linarith)
  rw [e, abs_of_nonneg (div_nonneg hnum (mul_pos h1 h2).le)]
  refine div_le_div_of_nonneg_left hnum hu ?_
  nlinarith [mul_nonneg hv hv, mul_nonneg hu.le hv]

/-- ★★ **How fast a packet is**: at rest energy `μ` and momentum term `p > 0`, the relativistic
velocity is within `μ²/(2 p²)` of `1`. -/
theorem one_sub_vRel_le {μ p : ℝ} (hμ : 0 < μ) (hp : 0 < p) :
    1 - vRel 1 μ p ≤ μ ^ 2 / (2 * p ^ 2) := by
  have hE := dispE_pos hμ p
  have hEp : p ≤ dispE μ p := (le_abs_self p).trans (abs_le_dispE μ p)
  have hsq := dispE_sq μ p
  have e : 1 - vRel 1 μ p = (dispE μ p - p) / dispE μ p := by
    rw [vRel, one_mul, eq_div_iff hE.ne', sub_mul, div_mul_cancel₀ _ hE.ne', one_mul]
  rw [e, div_le_div_iff₀ hE (by positivity)]
  have h1 : 2 * p ^ 2 ≤ (dispE μ p + p) * dispE μ p := by nlinarith
  have h2 : 0 ≤ dispE μ p - p := by linarith
  calc (dispE μ p - p) * (2 * p ^ 2)
      ≤ (dispE μ p - p) * ((dispE μ p + p) * dispE μ p) := mul_le_mul_of_nonneg_left h1 h2
    _ = μ ^ 2 * dispE μ p := by
        rw [show μ ^ 2 = dispE μ p ^ 2 - p ^ 2 by linarith]
        ring

end CSD.RecordLayer

end
