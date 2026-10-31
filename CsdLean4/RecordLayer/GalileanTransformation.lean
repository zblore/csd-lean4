/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SignalCone

/-!
# The coordinate transformation of the control

**Category:** 7-SigmaLayer (the record layer). BACKLOG #247 (the author's fourth operational-geometry
brief, step 7), for the control candidate (A); its stability under finite clock readings is #248 (a)
for (A).

The brief's central question: from the matched event records, what is the transformation between
the two observers' coordinates — Lorentz, Galilean or other? For the control the answer is
**Galilean, derived from the records**, and Lorentz is refuted for every candidate `c`.

The two-way radar chart of ~~#245~~ depends on the messenger. The chart here does not, because each
detector also measures the messenger's **one-way** speed: a write lasts as long as the messenger takes
to cross the observer's unit cell. The **transit chart** places a reflection where the outward and
return legs, run at the measured speeds from the cell's edge, meet.

## The chart

* `transitChart` (four record times: the emission write `[eS, eE]`, the return write `[rS, rE]`);
  ★★★ `ExchGeom.transitChart_eq` — **the transit chart is the event itself**: the bounce's time and
  the separation at it, exactly; ★★★ `ExchGeom.transitChart_indep` — **whatever the messenger**;
* `ownChart` (the midpoint of the reception write, at the observer's position), ★★
  `ownChart_reception` — the reflecting observer's own chart is the bounce;
* ★★ `relVel_of_writes` (the relative velocity from the write durations), ★★ `ExchGeom.sep_of_chart`
  (the initial separation from one chart);
* ★★ `transitChart_writes`, `ownChart_writes` — the four times and the midpoint are the start and
  completion times of the emission, return and reception writes of ~~#244~~.

## The transformation

* `galileo d y : (t, x) ↦ (t, x − d − yt)`; ★★★ `galileo_first` — it sends the observer at rest's
  chart of each reflection off the moving observer to the moving observer's own chart of it; ★★★
  `galileo_second` — and the observer at rest's own chart of each reflection off itself to the moving
  observer's transit chart of it (`flipChart`: the moving observer looks back, so its axis is
  reversed); ★ `galileo_fst_sub`, `galileo_snd_sub` — time differences and simultaneous distances
  are kept;
* ★★ `train_galilean` — on `exchange_train`: reflection `k` is charted at `((5 + 4k)/3, (17 + 4k)/3)`
  and mapped to `((5 + 4k)/3, 0)`; its two-way radar time is `41/16 + 3k/2`.

## Lorentz tested

* `lorentzBoost`, `sqrt_one_sub_pos`, `sqrt_one_sub_lt_one`; ★★ `lorentzBoost_worldline` — Lorentz
  puts the moving observer's event at time `τ √(1 − y²/c²)`, ★★ `lorentzBoost_worldline_lt` —
  earlier than `τ`;
* ★★★ `lorentz_refuted` — **a clock within `ε` of the dynamics' time refutes it** once
  `τ(1 − √(1 − y²/c²)) > 2ε`, for every `c > |y|`; ~~#243~~ supplies such clocks whatever the motion;
* `minkowski`, ★★ `minkowski_galileo`, ★★★ `minkowski_ne` — **no Minkowski interval is shared**: on the
  moving worldline the two charts' intervals differ by `y²Δt²`, whatever `c`;
* ★★★ `galilean_transformation` — the capstone.

## Finite clock readings

The exact chart divides by write durations, so a clock error in the four record times is not
simply passed through, as it is for the midpoint radar chart (`abs_clockRadar_sub_le`). Here it is
propagated explicitly.

* `relVelEst`, `sepEst` (the estimates `ŷ`, `d̂` from four record times), ★★
  `ExchGeom.relVelEst_sepEst` (exact readings give `y` and `d`); `chartTimeErr`, `chartSepErr`,
  `relVelErr`, `sepEstErr`;
* `ReadingsNear` (four readings within `ε` of the record times, writes lasting at least `δ ≥ 4ε`,
  emission end and return start in `[−H, H]`); `abs_div_add_sub_le`, `abs_div_sub_div_le`,
  `abs_one_div_sub_le`, `transitChart_fst_eq`; ★★★ `ReadingsNear.abs_chartTime_sub_le` — **the
  chart's time within `ε (3 + 4H/δ)`**; ★★★ `abs_chartSep_sub_le` — **its position within
  `(2ε/δ)(1 + 2H/δ)`**; ★★★ `abs_relVelEst_sub_le` — **the velocity within `4ε/δ²`**; ★★
  `abs_sepEst_sub_le` — the separation within `sepEstErr`; `abs_chartTime_le`, `abs_relVelEst_le`;
* ★ `abs_galileo_snd_sub_le`, `abs_ownChart_fst_sub_le`; ★★★ `galileo_first_stable`,
  `galileo_second_stable` — **the map with the estimated parameters sends each family's imperfect
  chart to within explicit bounds of the other's**: the discrepancy is bounded from the exact
  `galileo_first` / `galileo_second`; the perturbed charts are not assumed to obey any map;
* ★★ `train_stable` — on `exchange_train` (`y = 1`, writes of `1/4` and `1/2`): readings within
  `ε ≤ 1/16` chart reflection `k` within `ε (71 + 32k)` in time and `8ε (35 + 16k)` in position,
  and estimate `y` within `64ε` and `d` within `ε (978 + 448k)`;
* `handTime`, `abs_handTime_sub_le`, `clockTransit`, `clockRelVel`, `clockSep`, `clockOwn`; ★★
  `ExchGeom.readingsNear_hand` (a hand clock's readings of an exchange inside its horizon are near,
  with `ε = handClockErr`), `abs_handTime_reception_le`; ★★★ `galilean_transformation_clocks` —
  **the common chart from the observers' own clocks**: estimates, charts and both families' map
  discrepancies within explicit multiples of `handClockErr q₀` and `handClockErr q₁`.

## The findings

1. **The control's transformation is Galilean, and it is derived.** Its parameters are read off the
   records (`relVel_of_writes`, `sep_of_chart`); one map sends every matched event of both families
   from one chart to the other; time is absolute (the charts' times agree, as #243's clocks do).
   There is no preferred rest frame: the control's dynamics are Galilean-covariant, and the same map
   with the same `d` and `y` serves both families.
2. **Lorentz is refuted for every `c`**, by clock readings (`lorentz_refuted`) and by the interval
   (`minkowski_ne`). This is the expected negative the brief asks the control to prove.
3. **In the control, simultaneity is not a convention.** Each detector measures one-way speeds
   locally, so a messenger-independent chart exists (`transitChart_indep`), where the two-way radar
   chart of #245 has none. In special relativity the one-way speed is conventional; that the control
   can measure it is a mark of the Galilean class, and is what (B) must fail to reproduce if it is to
   be Lorentzian.
4. **The common chart is stable under finite clock readings, with errors linear in the clock
   error.** At fixed `δ` and `H` every error is `ε` times a constant; the time error grows like
   `H/δ`, the position and the estimates like `H/δ²` and `1/δ²`. Far reflections and fast messengers
   (short writes) amplify the clocks' error, so the train's errors grow with `k`. The bounds assume
   `4ε ≤ δ`: the one-way speeds come from dividing by write durations, which the clock must resolve.

## Derived and assumed, kept apart

**Derived** from the dynamics and the operational definitions: the four record times, the one-way
speeds (write durations), `y` and `d`, the clocks' agreement (~~#243~~), the parity of the second
family (~~#257~~'s `mirrorView_biFlow`, a symmetry of the control's dynamics), and the map.

**Assumed or supplied:**

* ⚠️ **The unit cell is the length standard**, the same for both detectors.
* ⚠️ **The messenger keeps its measured speed between the cell and the reflection.** The transit chart
  uses this; in the free dynamics it is true, but the observer does not measure it. Checking it would
  take intermediate stations.
* ⚠️ **Events are matched by the messenger's label**: the arena tells each observer which return goes
  with which emission. In the train the time order does the same job.
* ⚠️ **The clock bound `|T − τ| ≤ ε` is a hypothesis of `lorentz_refuted`**, discharged by #243's
  `handClockErr` over each clock's horizon; it is not restated here.

⚠️ **The stability bounds are upper bounds, linear in `ε`, not sharp**, and assume nothing of the
readings beyond their errors. Calibration (the unit cell), matching (the label) and free propagation
enter them exactly as they enter the exact chart: assumed, not perturbed.

⚠️ **No concrete clock is exhibited meeting `4 · handClockErr ≤ δ` over the horizon.**
`handClockErr = 2/(Kκ) + 1/(2ω)` against a horizon of about `2/κ` asks for many ticks per turn and a
fast Rabi rate; choosing parameters that satisfy `galilean_transformation_clocks` for the train is
#264.

⚠️ **This is the control (A).** The test chain's transformation is #259, behind #256; varying the
detector and clock construction (#248 (b)) is not treated.

References: `specs/BACKLOG.md` #247, #248, #264, #259, #246, #245, #244, #243, #257, #256, #39;
`RecordLayer/SignalCone.lean` (`exchEmit_duration`, `exchReturn_duration`, `half_anisotropy`);
`RecordLayer/MovingRadar.lean` (`ExchGeom.bounceTime_sub_emitEnd`, `train_radar`,
`abs_clockRadar_sub_le`); `RecordLayer/HandClock.lean` (`abs_handReading_sub_le`, `tickTime`,
`handHorizon`); `RecordLayer/TwoObservers.lean` (`handClockErr`);
`RecordLayer/MovingExchange.lean` (`ExchGeom`, `emissionWrite`, `returnWrite`, `receptionWrite`);
`RecordLayer/MovingRadarPair.lean` (`mirrorView_biFlow`, `two_radar_charts`).
-/

@[expose] public section

open Set

namespace CSD.RecordLayer

/-! ### The chart from one exchange's records -/

/-- **The transit chart** an observer builds from one exchange's four record times — its emission
write over `[eS, eE]` and its return write over `[rS, rE]`. Each write's duration is the time the
messenger takes to cross the observer's unit cell, so it gives that leg's speed; the chart places the
reflection where the outward and return legs, run at those speeds from the cell's edge, meet. -/
noncomputable def transitChart (eS eE rS rE : ℝ) : ℝ × ℝ :=
  ((eE * (rE - rS) + rS * (eE - eS)) / ((eE - eS) + (rE - rS)),
    1 / 2 + (rS - eE) / ((eE - eS) + (rE - rS)))

/-- **The chart of an event on the observer's own worldline**: the midpoint of the reception write,
at the observer's own position. -/
noncomputable def ownChart (a b : ℝ) : ℝ × ℝ := ((a + b) / 2, 0)

/-- The same chart with the spatial axis reversed: how the moving observer's chart of the second
family, which looks back at the observer at rest, reads in the common orientation. -/
def flipChart (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

namespace ExchGeom

variable {d y ρ w : ℝ} (h : ExchGeom d y ρ w)
include h

/-- ★★★ **The transit chart is the event itself**: from its emission and return records the
observer at rest charts the bounce at its time `τ` and the separation `D` at it, exactly. -/
theorem transitChart_eq :
    transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w)
      = (bounceTime ρ w, bounceSep d y ρ w) := by
  have he := h.bounceTime_sub_emitEnd
  have hu := h.out_pos
  have hv := h.ret_pos
  have hr : exchReturnStart d y ρ w
      = bounceTime ρ w + (bounceSep d y ρ w - 1 / 2) / retSpeed y w := rfl
  rw [transitChart, exchEmit_duration, exchReturn_duration, hr,
    show exchEmitEnd d y ρ w = bounceTime ρ w - (bounceSep d y ρ w - 1 / 2) / outSpeed y w by
      linarith]
  have huv : outSpeed y w + retSpeed y w ≠ 0 := by linarith
  refine Prod.ext ?_ ?_
  · dsimp only
    field_simp
    ring
  · dsimp only
    field_simp
    ring

/-- ★★★ **The transit chart does not depend on the messenger**: two admissible messengers that
bounce at the same time get the same chart — unlike the two-way radar chart
(`radarTime_ne_of_speed_ne`). -/
theorem transitChart_indep {ρ' w' : ℝ} (h' : ExchGeom d y ρ' w') (hτ : bounceTime ρ w = bounceTime ρ' w') :
    transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w)
      = transitChart (exchEmitStart d y ρ' w') (exchEmitEnd d y ρ' w') (exchReturnStart d y ρ' w')
        (exchReturnEnd d y ρ' w') := by
  rw [h.transitChart_eq, h'.transitChart_eq, bounceSep, bounceSep, hτ]

/-- ★★ **The initial separation from one chart**: `X − yT = d`. -/
theorem sep_of_chart :
    (transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w)).2
      - y * (transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w)).1 = d := by
  rw [h.transitChart_eq, bounceSep]
  ring

end ExchGeom

/-- ★★ **The relative velocity from the records**: half the difference of the inverse durations of
the emission and return writes. -/
theorem relVel_of_writes (d y ρ w : ℝ) :
    (1 / (exchEmitEnd d y ρ w - exchEmitStart d y ρ w)
        - 1 / (exchReturnEnd d y ρ w - exchReturnStart d y ρ w)) / 2 = y := by
  rw [exchEmit_duration, exchReturn_duration, one_div_one_div, one_div_one_div, half_anisotropy]

/-- ★★ **The reflecting observer's own chart is the bounce**: the midpoint of its reception write is
the bounce's time. -/
theorem ownChart_reception {ρ w : ℝ} (hw : w ≠ 0) :
    ownChart ((-(1 / 2) - ρ) / w) ((1 / 2 - ρ) / w) = (bounceTime ρ w, 0) := by
  rw [ownChart, bounceTime]
  congr 1
  field_simp
  ring

/-! ### The transformation -/

/-- **The Galilean map** with relative velocity `y` and initial separation `d`. -/
def galileo (d y : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 - d - y * p.1)

/-- ★★★ **First family**: the Galilean map sends the observer at rest's transit chart of a reflection
off the moving observer to the moving observer's own chart of it. -/
theorem galileo_first {d y ρ w : ℝ} (h : ExchGeom d y ρ w) :
    galileo d y (transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w)
        (exchReturnStart d y ρ w) (exchReturnEnd d y ρ w))
      = ownChart ((-(1 / 2) - ρ) / w) ((1 / 2 - ρ) / w) := by
  rw [h.transitChart_eq, ownChart_reception h.w_pos.ne', galileo, bounceSep]
  congr 1
  ring

/-- ★★★ **Second family**: the Galilean map sends the observer at rest's own chart of a reflection off
itself to the moving observer's transit chart of it, read in the common orientation. By #257 the
second family obeys #244's geometry with the same `d` and `y`. -/
theorem galileo_second {d y σ v : ℝ} (h : ExchGeom d y σ v) :
    galileo d y (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v))
      = flipChart (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
        (exchReturnStart d y σ v) (exchReturnEnd d y σ v)) := by
  rw [h.transitChart_eq, ownChart_reception h.w_pos.ne', galileo, flipChart, bounceSep]
  congr 1
  ring

/-- ★ **Galilean invariants**: time differences are kept. -/
theorem galileo_fst_sub (d y : ℝ) (p q : ℝ × ℝ) : (galileo d y q).1 - (galileo d y p).1 = q.1 - p.1 :=
  rfl

/-- ★ …and the distance between simultaneous events. -/
theorem galileo_snd_sub {d y : ℝ} {p q : ℝ × ℝ} (h : p.1 = q.1) :
    (galileo d y q).2 - (galileo d y p).2 = q.2 - p.2 := by
  simp only [galileo, h]
  ring

/-! ### Lorentz tested -/

/-- The Lorentz boost with velocity `v` and limiting speed `c`. -/
noncomputable def lorentzBoost (c v : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - v * p.2 / c ^ 2) / Real.sqrt (1 - v ^ 2 / c ^ 2),
    (p.2 - v * p.1) / Real.sqrt (1 - v ^ 2 / c ^ 2))

theorem sqrt_one_sub_pos {c v : ℝ} (hv : |v| < c) : 0 < Real.sqrt (1 - v ^ 2 / c ^ 2) := by
  have hc : 0 < c := lt_of_le_of_lt (abs_nonneg v) hv
  have : v ^ 2 < c ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  exact Real.sqrt_pos.2 (by rw [sub_pos, div_lt_one (by positivity)]; exact this)

/-- ★★ **What Lorentz predicts on the moving worldline**: an event of the moving observer at `τ`
(at `x − d = yτ`) is at its origin at time `τ √(1 − y²/c²)` — time dilation. -/
theorem lorentzBoost_worldline {c y : ℝ} (hy : |y| < c) (τ : ℝ) :
    lorentzBoost c y (τ, y * τ) = (τ * Real.sqrt (1 - y ^ 2 / c ^ 2), 0) := by
  have hs := sqrt_one_sub_pos hy
  have hs2 := Real.sq_sqrt (le_of_lt (by
    have := hs; exact Real.sqrt_pos.1 this : (0 : ℝ) < 1 - y ^ 2 / c ^ 2))
  rw [lorentzBoost]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [div_eq_iff hs.ne']
    have hc : c ≠ 0 := (lt_of_le_of_lt (abs_nonneg y) hy).ne'
    linear_combination (-τ) * hs2
  · simp

theorem sqrt_one_sub_lt_one {c y : ℝ} (hy0 : y ≠ 0) (hy : |y| < c) :
    Real.sqrt (1 - y ^ 2 / c ^ 2) < 1 := by
  have hc : 0 < c := lt_of_le_of_lt (abs_nonneg y) hy
  rw [Real.sqrt_lt' one_pos, one_pow]
  have : 0 < y ^ 2 / c ^ 2 := by positivity
  linarith

/-- ★★ **Lorentz dilates**: in relative motion it predicts the moving observer's event earlier than
the dynamics' time `τ > 0`. -/
theorem lorentzBoost_worldline_lt {c y : ℝ} (hy0 : y ≠ 0) (hy : |y| < c) {τ : ℝ} (hτ : 0 < τ) :
    (lorentzBoost c y (τ, y * τ)).1 < τ := by
  rw [lorentzBoost_worldline hy]
  exact mul_lt_of_lt_one_right hτ (sqrt_one_sub_lt_one hy0 hy)

/-- ★★★ **Lorentz is refuted by the moving observer's clock.** If its reading `T` of an event at
dynamical time `τ` is within `ε` of `τ` (#243: the clocks keep the dynamics' time whatever the
motion), then once `τ(1 − √(1 − y²/c²)) > 2ε` the reading is more than `ε` from the Lorentz
prediction — for every candidate `c`. -/
theorem lorentz_refuted {c y τ T ε : ℝ} (hy : |y| < c) (hT : |T - τ| ≤ ε)
    (hgap : 2 * ε < τ * (1 - Real.sqrt (1 - y ^ 2 / c ^ 2))) :
    ε < |T - (lorentzBoost c y (τ, y * τ)).1| := by
  rw [lorentzBoost_worldline hy]
  have h1 := abs_sub_abs_le_abs_sub (τ - τ * Real.sqrt (1 - y ^ 2 / c ^ 2)) (τ - T)
  have h2 : τ - τ * Real.sqrt (1 - y ^ 2 / c ^ 2) - (τ - T) = T - τ * Real.sqrt (1 - y ^ 2 / c ^ 2) := by
    ring
  rw [h2, abs_sub_comm τ T] at h1
  have h3 : |τ - τ * Real.sqrt (1 - y ^ 2 / c ^ 2)| = τ * (1 - Real.sqrt (1 - y ^ 2 / c ^ 2)) := by
    rw [show τ - τ * Real.sqrt (1 - y ^ 2 / c ^ 2) = τ * (1 - Real.sqrt (1 - y ^ 2 / c ^ 2)) by ring]
    exact abs_of_nonneg (by linarith [abs_nonneg (T - τ)])
  linarith

/-- The Minkowski interval with limiting speed `c`. -/
def minkowski (c : ℝ) (p q : ℝ × ℝ) : ℝ := c ^ 2 * (q.1 - p.1) ^ 2 - (q.2 - p.2) ^ 2

/-- ★★★ **No interval is shared**: for two events on the moving worldline the two charts' Minkowski
intervals differ by `y²Δt²`, whatever `c`. -/
theorem minkowski_galileo {d y c : ℝ} {p q : ℝ × ℝ} (hp : p.2 = d + y * p.1) (hq : q.2 = d + y * q.1) :
    minkowski c (galileo d y p) (galileo d y q) = minkowski c p q + y ^ 2 * (q.1 - p.1) ^ 2 := by
  simp only [minkowski, galileo, hp, hq]
  ring

theorem minkowski_ne {d y c : ℝ} (hy : y ≠ 0) {p q : ℝ × ℝ} (hp : p.2 = d + y * p.1)
    (hq : q.2 = d + y * q.1) (hpq : p.1 ≠ q.1) :
    minkowski c (galileo d y p) (galileo d y q) ≠ minkowski c p q := by
  rw [minkowski_galileo hp hq]
  have : 0 < y ^ 2 * (q.1 - p.1) ^ 2 := mul_pos (pow_pos (abs_pos.2 hy) 2 |>.trans_eq (sq_abs y))
    (pow_pos (abs_pos.2 (sub_ne_zero.2 (Ne.symm hpq))) 2 |>.trans_eq (sq_abs _))
  linarith

/-! ### The records, and the train -/

section Writes

variable {N : ℕ} {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★ **The transit chart is read off the records**: its four times are the completion and start
times of the emission and return writes. -/
theorem transitChart_writes (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (site : Finset (Fin K)) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.1 k = 0)
    (hG : ExchGeom (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :
    transitChart (emissionWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeStart
        (emissionWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeEnd
        (returnWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeStart
        (returnWrite J ħ g hf m gd hf1 hgd site k x₀ hreg hG).writeEnd
      = (bounceTime (x₀.2.2.1 k).1 (x₀.2.2.1 k).2,
          bounceSep (exchSep x₀) (exchSepVel m x₀) (x₀.2.2.1 k).1 (x₀.2.2.1 k).2) :=
  hG.transitChart_eq

/-- ★★ **The moving observer's own chart is read off its reception write.** -/
theorem ownChart_writes (hf1 : ContDiff ℝ 1 f) {K : ℕ} (site : Finset (Fin K)) (θ : ℝ)
    (hθ0 : 0 < θ) (k : Fin N) (x₀ : ExchArena N) (hreg : x₀.2.2.2.2 k = 0) (hw : 0 < (x₀.2.2.1 k).2)
    (hρ : (x₀.2.2.1 k).1 < -(1 / 2)) (hθ : θ ≤ gd * ((x₀.2.2.1 k).2)⁻¹) :
    ownChart (receptionWrite J ħ g hf m gd hf1 site θ hθ0 k x₀ hreg hw hρ hθ).writeStart
        (receptionWrite J ħ g hf m gd hf1 site θ hθ0 k x₀ hreg hw hρ hθ).writeEnd
      = (bounceTime (x₀.2.2.1 k).1 (x₀.2.2.1 k).2, 0) :=
  ownChart_reception hw.ne'

end Writes

/-- ★★ **The train's charts**: from the writes of `exchange_train` (emissions over
`[1/8 + k, 3/8 + k]`, returns over `[17/4 + 2k, 19/4 + 2k]`) the observer at rest charts reflection
`k` at `((5 + 4k)/3, (17 + 4k)/3)`, and the Galilean map with `d = 4`, `y = 1` sends it to
`((5 + 4k)/3, 0)`, the moving observer's own chart. The two-way radar time of the same event is
`41/16 + 3k/2` (`train_radar`). -/
theorem train_galilean (k : ℝ) :
    transitChart (1 / 8 + k) (3 / 8 + k) (17 / 4 + 2 * k) (19 / 4 + 2 * k)
        = ((5 + 4 * k) / 3, (17 + 4 * k) / 3)
      ∧ galileo 4 1 ((5 + 4 * k) / 3, (17 + 4 * k) / 3) = ((5 + 4 * k) / 3, 0) := by
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only [transitChart, galileo] <;> ring

/-! ### The capstone -/

/-- ★★★ **The coordinate transformation of the control (#247).** For any two exchanges with the same
separation `d` and recession rate `y` — the first reflecting off the moving observer and charted by
the observer at rest, the second reflecting off the observer at rest and charted by the moving one:
each transit chart is the event itself (exactly, whatever the messenger); `y` and `d` are read off
the records; the Galilean map `(t, x) ↦ (t, x − d − yt)` sends the observer at rest's chart of every
event of both families to the moving observer's; it keeps time differences and simultaneous
distances; and for every candidate `c > |y|` the Lorentz boost puts the moving observer's events at
`τ √(1 − y²/c²) < τ`, which its clock refutes once `τ(1 − √(1 − y²/c²)) > 2ε`, and the Minkowski
interval is not shared. -/
theorem galilean_transformation {d y ρ w σ v : ℝ} (hA : ExchGeom d y ρ w) (hB : ExchGeom d y σ v) :
    transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w) = (bounceTime ρ w, bounceSep d y ρ w)
    ∧ (1 / (exchEmitEnd d y ρ w - exchEmitStart d y ρ w)
        - 1 / (exchReturnEnd d y ρ w - exchReturnStart d y ρ w)) / 2 = y
    ∧ galileo d y (transitChart (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w)
        (exchReturnStart d y ρ w) (exchReturnEnd d y ρ w))
      = ownChart ((-(1 / 2) - ρ) / w) ((1 / 2 - ρ) / w)
    ∧ galileo d y (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v))
      = flipChart (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
        (exchReturnStart d y σ v) (exchReturnEnd d y σ v))
    ∧ (∀ p q, (galileo d y q).1 - (galileo d y p).1 = q.1 - p.1)
    ∧ (∀ p q : ℝ × ℝ, p.1 = q.1 → (galileo d y q).2 - (galileo d y p).2 = q.2 - p.2)
    ∧ (∀ c, |y| < c → ∀ τ, lorentzBoost c y (τ, y * τ) = (τ * Real.sqrt (1 - y ^ 2 / c ^ 2), 0))
    ∧ (y ≠ 0 → ∀ c, |y| < c → ∀ τ, 0 < τ → (lorentzBoost c y (τ, y * τ)).1 < τ)
    ∧ (∀ c, |y| < c → ∀ τ T ε, |T - τ| ≤ ε → 2 * ε < τ * (1 - Real.sqrt (1 - y ^ 2 / c ^ 2)) →
        ε < |T - (lorentzBoost c y (τ, y * τ)).1|)
    ∧ (y ≠ 0 → ∀ c (p q : ℝ × ℝ), p.2 = d + y * p.1 → q.2 = d + y * q.1 → p.1 ≠ q.1 →
        minkowski c (galileo d y p) (galileo d y q) ≠ minkowski c p q) :=
  ⟨hA.transitChart_eq, relVel_of_writes d y ρ w, galileo_first hA, galileo_second hB,
    galileo_fst_sub d y, fun _ _ h => galileo_snd_sub h,
    fun _ hc τ => lorentzBoost_worldline hc τ,
    fun hy0 _ hc _ hτ => lorentzBoost_worldline_lt hy0 hc hτ,
    fun _ hc _ _ _ hT hg => lorentz_refuted hc hT hg,
    fun hy _ _ _ hp hq hpq => minkowski_ne hy hp hq hpq⟩

/-! ### Finite clock readings -/

/-- **The velocity estimate** from one exchange's four record times: half the difference of the
inverse durations of the emission and return writes (`relVel_of_writes`). -/
noncomputable def relVelEst (eS eE rS rE : ℝ) : ℝ := (1 / (eE - eS) - 1 / (rE - rS)) / 2

/-- **The separation estimate**: `X − ŷT` on the transit chart (`ExchGeom.sep_of_chart`). -/
noncomputable def sepEst (eS eE rS rE : ℝ) : ℝ :=
  (transitChart eS eE rS rE).2 - relVelEst eS eE rS rE * (transitChart eS eE rS rE).1

/-- ★★ **Exact readings give the exact estimates**: `ŷ = y` and `d̂ = d`. -/
theorem ExchGeom.relVelEst_sepEst {d y ρ w : ℝ} (h : ExchGeom d y ρ w) :
    relVelEst (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w) = y
      ∧ sepEst (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
        (exchReturnEnd d y ρ w) = d := by
  have hy : relVelEst (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
      (exchReturnEnd d y ρ w) = y := relVel_of_writes d y ρ w
  refine ⟨hy, ?_⟩
  rw [sepEst, hy]
  exact h.sep_of_chart

/-- The time coordinate's error from readings within `ε`: `ε (3 + 4H/δ)`. -/
noncomputable def chartTimeErr (ε δ H : ℝ) : ℝ := ε * (3 + 4 * H / δ)

/-- The separation coordinate's error from readings within `ε`: `(2ε/δ)(1 + 2H/δ)`. -/
noncomputable def chartSepErr (ε δ H : ℝ) : ℝ := 2 * ε / δ * (1 + 2 * H / δ)

/-- The velocity estimate's error from readings within `ε`: `4ε/δ²`. -/
noncomputable def relVelErr (ε δ : ℝ) : ℝ := 4 * ε / δ ^ 2

/-- The separation estimate's error from readings within `ε`. -/
noncomputable def sepEstErr (ε δ H : ℝ) : ℝ :=
  chartSepErr ε δ H + 3 / (2 * δ) * chartTimeErr ε δ H + relVelErr ε δ * H

/-- **Four readings of one exchange's record times**, each within `ε` of the true time
(`eS, eE, rS, rE`), the two writes lasting at least `δ > 0` with `4ε ≤ δ`, and the emission's end
and the return's start in `[−H, H]`. Nothing is assumed of the readings beyond these bounds. -/
structure ReadingsNear (eS eE rS rE eS' eE' rS' rE' ε δ H : ℝ) : Prop where
  delta_pos : 0 < δ
  four_mul_le : 4 * ε ≤ δ
  emit_ge : δ ≤ eE - eS
  ret_ge : δ ≤ rE - rS
  emitEnd_le : |eE| ≤ H
  retStart_le : |rS| ≤ H
  eS_near : |eS' - eS| ≤ ε
  eE_near : |eE' - eE| ≤ ε
  rS_near : |rS' - rS| ≤ ε
  rE_near : |rE' - rE| ≤ ε

/-- **A fraction of a sum is stable**: perturbing `a, b ≥ 0` by at most `2ε` each moves
`a/(a + b)` by at most `2ε/δ` once the perturbed sum is at least `δ`. -/
theorem abs_div_add_sub_le {a b a' b' ε δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : 0 < a + b)
    (hδ : 0 < δ) (hS' : δ ≤ a' + b') (h1 : |a' - a| ≤ 2 * ε) (h2 : |b' - b| ≤ 2 * ε) :
    |a' / (a' + b') - a / (a + b)| ≤ 2 * ε / δ := by
  have hS'p : 0 < a' + b' := hδ.trans_le hS'
  have he : 0 ≤ ε := by linarith [abs_nonneg (a' - a)]
  rw [show a' / (a' + b') - a / (a + b) = ((a' - a) * b - a * (b' - b)) / ((a' + b') * (a + b)) by
    field_simp
    ring, abs_div, abs_of_pos (mul_pos hS'p hS)]
  have hn : |(a' - a) * b - a * (b' - b)| ≤ 2 * ε * (a + b) := by
    have e1 := abs_le.1 h1
    have e2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> nlinarith
  calc |(a' - a) * b - a * (b' - b)| / ((a' + b') * (a + b))
      ≤ 2 * ε * (a + b) / (δ * (a + b)) :=
        div_le_div₀ (by positivity) hn (mul_pos hδ hS) (mul_le_mul_of_nonneg_right hS' hS.le)
    _ = 2 * ε / δ := by
        field_simp

/-- **A ratio is stable**: perturbing `G` by `2ε` and `S ≥ 2δ` by `4ε` (to `S' ≥ δ`) moves `G/S` by
at most `(2ε/δ)(1 + 2H/δ)` when `|G| ≤ 2H`. -/
theorem abs_div_sub_div_le {G G' S S' ε δ H : ℝ} (hδ : 0 < δ) (hS : 2 * δ ≤ S) (hS' : δ ≤ S')
    (hG : |G| ≤ 2 * H) (h1 : |G' - G| ≤ 2 * ε) (h2 : |S' - S| ≤ 4 * ε) :
    |G' / S' - G / S| ≤ 2 * ε / δ * (1 + 2 * H / δ) := by
  have hSp : 0 < S := by linarith
  have hS'p : 0 < S' := hδ.trans_le hS'
  have he : 0 ≤ ε := by linarith [abs_nonneg (G' - G)]
  have hH : 0 ≤ H := by linarith [abs_nonneg G]
  rw [show G' / S' - G / S = (G' - G) / S' - G * (S' - S) / (S' * S) by
    field_simp
    ring]
  have t1 : |(G' - G) / S'| ≤ 2 * ε / δ := by
    rw [abs_div, abs_of_pos hS'p]
    exact div_le_div₀ (by positivity) h1 hδ hS'
  have t2 : |G * (S' - S) / (S' * S)| ≤ 2 * H * (4 * ε) / (δ * (2 * δ)) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hS'p hSp)]
    exact div_le_div₀ (by positivity) (mul_le_mul hG h2 (abs_nonneg _) (by positivity))
      (by positivity) (mul_le_mul hS' hS (by positivity) hS'p.le)
  have e : 2 * ε / δ * (1 + 2 * H / δ) = 2 * ε / δ + 2 * H * (4 * ε) / (δ * (2 * δ)) := by
    field_simp
    ring
  rw [e]
  exact (abs_sub _ _).trans (add_le_add t1 t2)

/-- **An inverse is stable**: `|1/a' − 1/a| ≤ 4ε/δ²` when `a ≥ δ`, `a' ≥ δ/2`, `|a' − a| ≤ 2ε`. -/
theorem abs_one_div_sub_le {a a' ε δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (ha' : δ / 2 ≤ a')
    (h : |a' - a| ≤ 2 * ε) : |1 / a' - 1 / a| ≤ 4 * ε / δ ^ 2 := by
  have hap : 0 < a := hδ.trans_le ha
  have ha'p : 0 < a' := (half_pos hδ).trans_le ha'
  have he : 0 ≤ ε := by linarith [abs_nonneg (a' - a)]
  rw [show 1 / a' - 1 / a = (a - a') / (a * a') by field_simp, abs_div,
    abs_of_pos (mul_pos hap ha'p), abs_sub_comm]
  calc |a' - a| / (a * a') ≤ 2 * ε / (δ * (δ / 2)) :=
        div_le_div₀ (by positivity) h (by positivity) (mul_le_mul ha ha' (by positivity) hap.le)
    _ = 4 * ε / δ ^ 2 := by
        field_simp
        ring

theorem transitChart_fst_eq {eS eE rS rE : ℝ} (hS : (eE - eS) + (rE - rS) ≠ 0) :
    (transitChart eS eE rS rE).1 = eE + (eE - eS) / ((eE - eS) + (rE - rS)) * (rS - eE) := by
  simp only [transitChart]
  field_simp
  ring

namespace ReadingsNear

variable {eS eE rS rE eS' eE' rS' rE' ε δ H : ℝ}
  (h : ReadingsNear eS eE rS rE eS' eE' rS' rE' ε δ H)
include h

theorem eps_nonneg : 0 ≤ ε := (abs_nonneg _).trans h.eS_near

theorem H_nonneg : 0 ≤ H := (abs_nonneg _).trans h.emitEnd_le

theorem emit_near : |(eE' - eS') - (eE - eS)| ≤ 2 * ε := by
  have e1 := abs_le.1 h.eS_near
  have e2 := abs_le.1 h.eE_near
  rw [abs_le]
  constructor <;> linarith

theorem ret_near : |(rE' - rS') - (rE - rS)| ≤ 2 * ε := by
  have e1 := abs_le.1 h.rS_near
  have e2 := abs_le.1 h.rE_near
  rw [abs_le]
  constructor <;> linarith

theorem emit'_ge : δ / 2 ≤ eE' - eS' := by
  have := abs_le.1 h.emit_near
  linarith [h.four_mul_le, h.emit_ge]

theorem ret'_ge : δ / 2 ≤ rE' - rS' := by
  have := abs_le.1 h.ret_near
  linarith [h.four_mul_le, h.ret_ge]

/-- The true chart's time lies in `[−H, H]`: it is a weighted mean of the emission's end and the
return's start. -/
theorem abs_chartTime_le : |(transitChart eS eE rS rE).1| ≤ H := by
  have hδ := h.delta_pos
  have ha : 0 < eE - eS := hδ.trans_le h.emit_ge
  have hb : 0 < rE - rS := hδ.trans_le h.ret_ge
  have hS : 0 < (eE - eS) + (rE - rS) := by linarith
  simp only [transitChart]
  rw [abs_div, abs_of_pos hS, div_le_iff₀ hS]
  calc |eE * (rE - rS) + rS * (eE - eS)| ≤ |eE| * (rE - rS) + |rS| * (eE - eS) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
    _ ≤ H * (rE - rS) + H * (eE - eS) :=
        add_le_add (mul_le_mul_of_nonneg_right h.emitEnd_le hb.le)
          (mul_le_mul_of_nonneg_right h.retStart_le ha.le)
    _ = H * ((eE - eS) + (rE - rS)) := by ring

/-- ★★★ **The chart's time from imperfect readings**: within `ε (3 + 4H/δ)` of the true one. -/
theorem abs_chartTime_sub_le :
    |(transitChart eS' eE' rS' rE').1 - (transitChart eS eE rS rE).1| ≤ chartTimeErr ε δ H := by
  have hδ := h.delta_pos
  have he := h.eps_nonneg
  have ha : 0 < eE - eS := hδ.trans_le h.emit_ge
  have hb : 0 < rE - rS := hδ.trans_le h.ret_ge
  have ha' := h.emit'_ge
  have hb' := h.ret'_ge
  have hS : 0 < (eE - eS) + (rE - rS) := by linarith
  have hS' : δ ≤ (eE' - eS') + (rE' - rS') := by linarith
  have hfr := abs_div_add_sub_le ha.le hb.le hS hδ hS' h.emit_near h.ret_near
  have hl0 : 0 ≤ (eE' - eS') / ((eE' - eS') + (rE' - rS')) := by
    apply div_nonneg <;> linarith
  have hl1 : (eE' - eS') / ((eE' - eS') + (rE' - rS')) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hG : |rS - eE| ≤ 2 * H := by
    have := abs_sub rS eE
    linarith [h.emitEnd_le, h.retStart_le]
  have hG' : |(rS' - eE') - (rS - eE)| ≤ 2 * ε := by
    have e1 := abs_le.1 h.rS_near
    have e2 := abs_le.1 h.eE_near
    rw [abs_le]
    constructor <;> linarith
  rw [transitChart_fst_eq (by linarith), transitChart_fst_eq hS.ne']
  set l' := (eE' - eS') / ((eE' - eS') + (rE' - rS'))
  set l₀ := (eE - eS) / ((eE - eS) + (rE - rS))
  rw [show eE' + l' * (rS' - eE') - (eE + l₀ * (rS - eE))
      = (eE' - eE) + l' * ((rS' - eE') - (rS - eE)) + (l' - l₀) * (rS - eE) by ring]
  have t2 : |l' * ((rS' - eE') - (rS - eE))| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hl0]
    calc l' * |(rS' - eE') - (rS - eE)| ≤ 1 * (2 * ε) :=
          mul_le_mul hl1 hG' (abs_nonneg _) zero_le_one
      _ = 2 * ε := one_mul _
  have t3 : |(l' - l₀) * (rS - eE)| ≤ 2 * ε / δ * (2 * H) := by
    rw [abs_mul]
    exact mul_le_mul hfr hG (abs_nonneg _) (by positivity)
  have e : chartTimeErr ε δ H = ε + 2 * ε + 2 * ε / δ * (2 * H) := by
    rw [chartTimeErr]
    field_simp
    ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h.eE_near t2)) t3)

/-- ★★★ **The chart's separation from imperfect readings**: within `(2ε/δ)(1 + 2H/δ)` of the true
one. -/
theorem abs_chartSep_sub_le :
    |(transitChart eS' eE' rS' rE').2 - (transitChart eS eE rS rE).2| ≤ chartSepErr ε δ H := by
  have hδ := h.delta_pos
  have hS : 2 * δ ≤ (eE - eS) + (rE - rS) := by linarith [h.emit_ge, h.ret_ge]
  have hS' : δ ≤ (eE' - eS') + (rE' - rS') := by linarith [h.emit'_ge, h.ret'_ge]
  have hG : |rS - eE| ≤ 2 * H := by
    have := abs_sub rS eE
    linarith [h.emitEnd_le, h.retStart_le]
  have hG' : |(rS' - eE') - (rS - eE)| ≤ 2 * ε := by
    have e1 := abs_le.1 h.rS_near
    have e2 := abs_le.1 h.eE_near
    rw [abs_le]
    constructor <;> linarith
  have hSS : |((eE' - eS') + (rE' - rS')) - ((eE - eS) + (rE - rS))| ≤ 4 * ε := by
    have e1 := abs_le.1 h.emit_near
    have e2 := abs_le.1 h.ret_near
    rw [abs_le]
    constructor <;> linarith
  simp only [transitChart, add_sub_add_left_eq_sub]
  exact abs_div_sub_div_le hδ hS hS' hG hG' hSS

/-- The true velocity estimate is at most `1/(2δ)` in size. -/
theorem abs_relVelEst_le : |relVelEst eS eE rS rE| ≤ 1 / (2 * δ) := by
  have hδ := h.delta_pos
  have ha : 0 < eE - eS := hδ.trans_le h.emit_ge
  have hb : 0 < rE - rS := hδ.trans_le h.ret_ge
  have i1 : 1 / (eE - eS) ≤ 1 / δ := one_div_le_one_div_of_le hδ h.emit_ge
  have i2 : 1 / (rE - rS) ≤ 1 / δ := one_div_le_one_div_of_le hδ h.ret_ge
  have p1 : 0 < 1 / (eE - eS) := one_div_pos.2 ha
  have p2 : 0 < 1 / (rE - rS) := one_div_pos.2 hb
  rw [relVelEst, abs_div, abs_two, show 1 / (2 * δ) = 1 / δ / 2 by ring]
  refine div_le_div_of_nonneg_right ?_ zero_le_two
  rw [abs_le]
  constructor <;> linarith

/-- ★★★ **The velocity estimate from imperfect readings**: within `4ε/δ²` of the true one. -/
theorem abs_relVelEst_sub_le :
    |relVelEst eS' eE' rS' rE' - relVelEst eS eE rS rE| ≤ relVelErr ε δ := by
  have hδ := h.delta_pos
  have t1 := abs_one_div_sub_le hδ h.emit_ge h.emit'_ge h.emit_near
  have t2 := abs_one_div_sub_le hδ h.ret_ge h.ret'_ge h.ret_near
  rw [relVelEst, relVelEst, show (1 / (eE' - eS') - 1 / (rE' - rS')) / 2
      - (1 / (eE - eS) - 1 / (rE - rS)) / 2
      = ((1 / (eE' - eS') - 1 / (eE - eS)) - (1 / (rE' - rS') - 1 / (rE - rS))) / 2 by ring,
    abs_div, abs_two, relVelErr]
  have := (abs_sub _ _).trans (add_le_add t1 t2)
  linarith

/-- ★★ **The separation estimate from imperfect readings**: within `sepEstErr ε δ H` of the true
one. -/
theorem abs_sepEst_sub_le :
    |sepEst eS' eE' rS' rE' - sepEst eS eE rS rE| ≤ sepEstErr ε δ H := by
  have hδ := h.delta_pos
  have he := h.eps_nonneg
  have hX := h.abs_chartSep_sub_le
  have hT := h.abs_chartTime_sub_le
  have hY := h.abs_relVelEst_sub_le
  have hT0 := h.abs_chartTime_le
  have hY0 := h.abs_relVelEst_le
  have hY' : |relVelEst eS' eE' rS' rE'| ≤ 3 / (2 * δ) := by
    have hr : relVelErr ε δ ≤ 1 / δ := by
      rw [relVelErr, div_le_div_iff₀ (by positivity) hδ]
      nlinarith [h.four_mul_le]
    have hs : 1 / (2 * δ) + 1 / δ = 3 / (2 * δ) := by
      field_simp
      ring
    have := abs_sub_abs_le_abs_sub (relVelEst eS' eE' rS' rE') (relVelEst eS eE rS rE)
    linarith
  have hct : 0 ≤ chartTimeErr ε δ H := hT.trans' (abs_nonneg _)
  set T' := (transitChart eS' eE' rS' rE').1
  set T := (transitChart eS eE rS rE).1
  set y' := relVelEst eS' eE' rS' rE'
  set y := relVelEst eS eE rS rE
  rw [sepEst, sepEst, show (transitChart eS' eE' rS' rE').2 - y' * T'
      - ((transitChart eS eE rS rE).2 - y * T)
      = ((transitChart eS' eE' rS' rE').2 - (transitChart eS eE rS rE).2)
        - (y' * (T' - T) + (y' - y) * T) by ring, sepEstErr]
  have t1 : |y' * (T' - T)| ≤ 3 / (2 * δ) * chartTimeErr ε δ H := by
    rw [abs_mul]
    exact mul_le_mul hY' hT (abs_nonneg _) (by positivity)
  have t2 : |(y' - y) * T| ≤ relVelErr ε δ * H := by
    rw [abs_mul]
    exact mul_le_mul hY hT0 (abs_nonneg _) ((abs_nonneg _).trans hY)
  have := (abs_sub _ _).trans (add_le_add hX ((abs_add_le _ _).trans (add_le_add t1 t2)))
  linarith

end ReadingsNear

/-- **The Galilean map is stable in its parameters and its argument.** -/
theorem abs_galileo_snd_sub_le (d y d' y' : ℝ) (p p' : ℝ × ℝ) :
    |(galileo d' y' p').2 - (galileo d y p).2|
      ≤ |p'.2 - p.2| + |d' - d| + |y'| * |p'.1 - p.1| + |y' - y| * |p.1| := by
  have h1 := abs_add_three (p'.2 - p.2) (-(d' - d)) (-(y' * (p'.1 - p.1)))
  have h2 := abs_add_le ((p'.2 - p.2) + -(d' - d) + -(y' * (p'.1 - p.1))) (-((y' - y) * p.1))
  simp only [abs_neg, abs_mul] at h1 h2
  rw [show (galileo d' y' p').2 - (galileo d y p).2
      = (p'.2 - p.2) + -(d' - d) + -(y' * (p'.1 - p.1)) + -((y' - y) * p.1) by
    simp only [galileo]
    ring]
  linarith

/-- The midpoint of two readings within `ε` is within `ε` of the true midpoint. -/
theorem abs_ownChart_fst_sub_le {a b a' b' ε : ℝ} (ha : |a' - a| ≤ ε) (hb : |b' - b| ≤ ε) :
    |(ownChart a' b').1 - (ownChart a b).1| ≤ ε := by
  simp only [ownChart]
  rw [show (a' + b') / 2 - (a + b) / 2 = ((a' - a) + (b' - b)) / 2 by ring, abs_div, abs_two,
    div_le_iff₀ two_pos]
  linarith [abs_add_le (a' - a) (b' - b)]

/-- ★★★ **First family, from imperfect readings.** The observer at rest estimates `ŷ`, `d̂` from one
calibration exchange (readings within `ε`) and charts a reflection off the moving observer from its
own readings within `ε`; the moving observer reads its reception write within `ε₁`. The map with
the **estimated** parameters sends the first chart to within `chartTimeErr + ε₁` in time and the
stated sum in position of the second — a bound on the discrepancy, not an assumed transformation. -/
theorem galileo_first_stable {d y ρ w ρ₁ w₁ eS eE rS rE fS fE sS sE a b ε ε₁ δ H : ℝ}
    (hC : ExchGeom d y ρ w)
    (rC : ReadingsNear (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
      (exchReturnEnd d y ρ w) eS eE rS rE ε δ H)
    (hA : ExchGeom d y ρ₁ w₁)
    (rA : ReadingsNear (exchEmitStart d y ρ₁ w₁) (exchEmitEnd d y ρ₁ w₁)
      (exchReturnStart d y ρ₁ w₁) (exchReturnEnd d y ρ₁ w₁) fS fE sS sE ε δ H)
    (ha : |a - (-(1 / 2) - ρ₁) / w₁| ≤ ε₁) (hb : |b - (1 / 2 - ρ₁) / w₁| ≤ ε₁) :
    |(galileo (sepEst eS eE rS rE) (relVelEst eS eE rS rE) (transitChart fS fE sS sE)).1
        - (ownChart a b).1| ≤ chartTimeErr ε δ H + ε₁
      ∧ |(galileo (sepEst eS eE rS rE) (relVelEst eS eE rS rE) (transitChart fS fE sS sE)).2
        - (ownChart a b).2|
        ≤ chartSepErr ε δ H + sepEstErr ε δ H + (|y| + relVelErr ε δ) * chartTimeErr ε δ H
          + relVelErr ε δ * H := by
  obtain ⟨hy, hd⟩ := hC.relVelEst_sepEst
  have hex := galileo_first hA
  have hT := rA.abs_chartTime_sub_le
  have hX := rA.abs_chartSep_sub_le
  have hT0 := rA.abs_chartTime_le
  have hY := rC.abs_relVelEst_sub_le
  have hD := rC.abs_sepEst_sub_le
  rw [hy] at hY
  rw [hd] at hD
  have hY' : |relVelEst eS eE rS rE| ≤ |y| + relVelErr ε δ := by
    have := abs_sub_abs_le_abs_sub (relVelEst eS eE rS rE) y
    linarith
  have hct : 0 ≤ chartTimeErr ε δ H := hT.trans' (abs_nonneg _)
  constructor
  · have hm := abs_ownChart_fst_sub_le ha hb
    have e1 : (galileo d y (transitChart (exchEmitStart d y ρ₁ w₁) (exchEmitEnd d y ρ₁ w₁)
        (exchReturnStart d y ρ₁ w₁) (exchReturnEnd d y ρ₁ w₁))).1
        = (ownChart ((-(1 / 2) - ρ₁) / w₁) ((1 / 2 - ρ₁) / w₁)).1 := by rw [hex]
    simp only [galileo] at e1 ⊢
    rw [← e1] at hm
    have := abs_sub_le (transitChart fS fE sS sE).1
      (transitChart (exchEmitStart d y ρ₁ w₁) (exchEmitEnd d y ρ₁ w₁) (exchReturnStart d y ρ₁ w₁)
        (exchReturnEnd d y ρ₁ w₁)).1 (ownChart a b).1
    rw [abs_sub_comm (ownChart a b).1] at hm
    linarith
  · have e2 : (galileo d y (transitChart (exchEmitStart d y ρ₁ w₁) (exchEmitEnd d y ρ₁ w₁)
        (exchReturnStart d y ρ₁ w₁) (exchReturnEnd d y ρ₁ w₁))).2 = (ownChart a b).2 := by
      rw [hex]
      rfl
    rw [← e2]
    refine (abs_galileo_snd_sub_le _ _ _ _ _ _).trans ?_
    have t1 := mul_le_mul hY' hT (abs_nonneg _) ((abs_nonneg _).trans hY')
    have t2 := mul_le_mul hY hT0 (abs_nonneg _) ((abs_nonneg _).trans hY)
    linarith

/-- ★★★ **Second family, from imperfect readings.** The observer at rest's own chart of a reflection
off itself (its reception readings within `ε`), mapped with the estimated parameters, lies within
the stated bounds of the moving observer's transit chart from its readings within `ε₁`. -/
theorem galileo_second_stable {d y ρ w σ v eS eE rS rE fS fE sS sE a b ε ε₁ δ H : ℝ}
    (hC : ExchGeom d y ρ w)
    (rC : ReadingsNear (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
      (exchReturnEnd d y ρ w) eS eE rS rE ε δ H)
    (hB : ExchGeom d y σ v)
    (rB : ReadingsNear (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
      (exchReturnStart d y σ v) (exchReturnEnd d y σ v) fS fE sS sE ε₁ δ H)
    (ha : |a - (-(1 / 2) - σ) / v| ≤ ε) (hb : |b - (1 / 2 - σ) / v| ≤ ε) :
    |(galileo (sepEst eS eE rS rE) (relVelEst eS eE rS rE) (ownChart a b)).1
        - (flipChart (transitChart fS fE sS sE)).1| ≤ ε + chartTimeErr ε₁ δ H
      ∧ |(galileo (sepEst eS eE rS rE) (relVelEst eS eE rS rE) (ownChart a b)).2
        - (flipChart (transitChart fS fE sS sE)).2|
        ≤ sepEstErr ε δ H + (|y| + relVelErr ε δ) * ε + relVelErr ε δ * H
          + chartSepErr ε₁ δ H := by
  obtain ⟨hy, hd⟩ := hC.relVelEst_sepEst
  have hex := galileo_second hB
  have hT := rB.abs_chartTime_sub_le
  have hX := rB.abs_chartSep_sub_le
  have hT0 := rB.abs_chartTime_le
  have hY := rC.abs_relVelEst_sub_le
  have hD := rC.abs_sepEst_sub_le
  rw [hy] at hY
  rw [hd] at hD
  have hY' : |relVelEst eS eE rS rE| ≤ |y| + relVelErr ε δ := by
    have := abs_sub_abs_le_abs_sub (relVelEst eS eE rS rE) y
    linarith
  have hm := abs_ownChart_fst_sub_le ha hb
  have e1 : (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v)).1
      = (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v) (exchReturnStart d y σ v)
        (exchReturnEnd d y σ v)).1 := by
    simpa only [galileo, flipChart] using congrArg Prod.fst hex
  have he : 0 ≤ ε := (abs_nonneg _).trans ha
  constructor
  · simp only [galileo, flipChart]
    rw [e1] at hm
    have := abs_sub_le (ownChart a b).1
      (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v) (exchReturnStart d y σ v)
        (exchReturnEnd d y σ v)).1 (transitChart fS fE sS sE).1
    rw [abs_sub_comm (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
      (exchReturnStart d y σ v) (exchReturnEnd d y σ v)).1] at this
    linarith
  · have e2 : (flipChart (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
        (exchReturnStart d y σ v) (exchReturnEnd d y σ v))).2
        = (galileo d y (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v))).2 := by rw [hex]
    have g := abs_galileo_snd_sub_le d y (sepEst eS eE rS rE) (relVelEst eS eE rS rE)
      (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v)) (ownChart a b)
    have hf : |(flipChart (transitChart fS fE sS sE)).2
        - (flipChart (transitChart (exchEmitStart d y σ v) (exchEmitEnd d y σ v)
          (exchReturnStart d y σ v) (exchReturnEnd d y σ v))).2| ≤ chartSepErr ε₁ δ H := by
      simp only [flipChart]
      rw [show -(transitChart fS fE sS sE).2 - -(transitChart (exchEmitStart d y σ v)
          (exchEmitEnd d y σ v) (exchReturnStart d y σ v) (exchReturnEnd d y σ v)).2
          = -((transitChart fS fE sS sE).2 - (transitChart (exchEmitStart d y σ v)
          (exchEmitEnd d y σ v) (exchReturnStart d y σ v) (exchReturnEnd d y σ v)).2) by ring,
        abs_neg]
      exact hX
    have hτ : |(ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v)).1| ≤ H := by
      rw [e1]
      exact hT0
    have hsnd : (ownChart a b).2 - (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v)).2 = 0 := by
      simp [ownChart]
    rw [hsnd, abs_zero, zero_add] at g
    have t1 := mul_le_mul hY' hm (abs_nonneg _) ((abs_nonneg _).trans hY')
    have t2 := mul_le_mul hY hτ (abs_nonneg _) ((abs_nonneg _).trans hY)
    rw [e2] at hf
    have := abs_sub_le (galileo (sepEst eS eE rS rE) (relVelEst eS eE rS rE) (ownChart a b)).2
      (galileo d y (ownChart ((-(1 / 2) - σ) / v) ((1 / 2 - σ) / v))).2
      (flipChart (transitChart fS fE sS sE)).2
    rw [abs_sub_comm] at hf
    linarith

/-- ★★ **The train from imperfect readings**: for messenger `k` of `exchange_train` (`y = 1 ≠ 0`,
writes lasting `1/4` and `1/2`), readings within `ε ≤ 1/16` of its four record times chart the
reflection within `ε (71 + 32k)` of `(5 + 4k)/3` in time and `8ε (35 + 16k)` of `(17 + 4k)/3` in
position, and estimate the velocity within `64ε` of `1` and the separation within
`ε (978 + 448k)` of `4`. The errors grow with `k`: the reflection is farther away. -/
theorem train_stable {k ε eS eE rS rE : ℝ} (hk : 0 ≤ k) (hε : ε ≤ 1 / 16)
    (h1 : |eS - (1 / 8 + k)| ≤ ε) (h2 : |eE - (3 / 8 + k)| ≤ ε)
    (h3 : |rS - (17 / 4 + 2 * k)| ≤ ε) (h4 : |rE - (19 / 4 + 2 * k)| ≤ ε) :
    |(transitChart eS eE rS rE).1 - (5 + 4 * k) / 3| ≤ ε * (71 + 32 * k)
      ∧ |(transitChart eS eE rS rE).2 - (17 + 4 * k) / 3| ≤ 8 * ε * (35 + 16 * k)
      ∧ |relVelEst eS eE rS rE - 1| ≤ 64 * ε
      ∧ |sepEst eS eE rS rE - 4| ≤ ε * (978 + 448 * k) := by
  obtain ⟨hG, he, hf, hr, hR⟩ := exchange_train k hk
  have r : ReadingsNear (1 / 8 + k) (3 / 8 + k) (17 / 4 + 2 * k) (19 / 4 + 2 * k) eS eE rS rE ε
      (1 / 4) (17 / 4 + 2 * k) :=
    ⟨by norm_num, by linarith, by linarith, by linarith,
      by rw [abs_of_nonneg (by linarith)]; linarith, le_of_eq (abs_of_nonneg (by linarith)),
      h1, h2, h3, h4⟩
  have hc := (train_galilean k).1
  obtain ⟨hy, hd⟩ := hG.relVelEst_sepEst
  rw [he, hf, hr, hR] at hy hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := r.abs_chartTime_sub_le
    rw [hc, chartTimeErr] at this
    convert this using 1
    field_simp
    ring
  · have := r.abs_chartSep_sub_le
    rw [hc, chartSepErr] at this
    convert this using 1
    field_simp
    ring
  · have := r.abs_relVelEst_sub_le
    rw [hy, relVelErr] at this
    convert this using 1
    norm_num
    ring
  · have := r.abs_sepEst_sub_le
    rw [hd, sepEstErr, chartSepErr, chartTimeErr, relVelErr] at this
    convert this using 1
    field_simp
    ring

/-! ### The charts read on the observers' clocks -/

section Clocks

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- **An observer's hand clock read at time `t`.** -/
noncomputable def handTime (K : ℕ) (q : LF4.KTorus) (t : ℝ) : ℝ :=
  handReading K (tickTime K (handRate J ħ g hf q)) (hand J ħ g hf t q)

theorem abs_handTime_sub_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K) {q : LF4.KTorus}
    (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handTime J ħ g hf K q t - t| ≤ handClockErr J ħ g hf K q :=
  abs_handReading_sub_le J ħ g hf hJ hħ hK hq hκ ht0 ht

/-- **The transit chart on clock `q`**: the exchange's four record times read on it. -/
noncomputable def clockTransit (K : ℕ) (q : LF4.KTorus) (d y ρ w : ℝ) : ℝ × ℝ :=
  transitChart (handTime J ħ g hf K q (exchEmitStart d y ρ w))
    (handTime J ħ g hf K q (exchEmitEnd d y ρ w)) (handTime J ħ g hf K q (exchReturnStart d y ρ w))
    (handTime J ħ g hf K q (exchReturnEnd d y ρ w))

/-- **The velocity estimate on clock `q`.** -/
noncomputable def clockRelVel (K : ℕ) (q : LF4.KTorus) (d y ρ w : ℝ) : ℝ :=
  relVelEst (handTime J ħ g hf K q (exchEmitStart d y ρ w))
    (handTime J ħ g hf K q (exchEmitEnd d y ρ w)) (handTime J ħ g hf K q (exchReturnStart d y ρ w))
    (handTime J ħ g hf K q (exchReturnEnd d y ρ w))

/-- **The separation estimate on clock `q`.** -/
noncomputable def clockSep (K : ℕ) (q : LF4.KTorus) (d y ρ w : ℝ) : ℝ :=
  sepEst (handTime J ħ g hf K q (exchEmitStart d y ρ w))
    (handTime J ħ g hf K q (exchEmitEnd d y ρ w)) (handTime J ħ g hf K q (exchReturnStart d y ρ w))
    (handTime J ħ g hf K q (exchReturnEnd d y ρ w))

/-- **The reflecting observer's own chart on clock `q`**: the midpoint of its reception write's
start and completion, read on it. -/
noncomputable def clockOwn (K : ℕ) (q : LF4.KTorus) (ρ w : ℝ) : ℝ × ℝ :=
  ownChart (handTime J ħ g hf K q ((-(1 / 2) - ρ) / w)) (handTime J ħ g hf K q ((1 / 2 - ρ) / w))

/-- ★★ **A clock's readings of an exchange are near**: within its error `handClockErr` over its
horizon, given that the writes last at least `δ ≥ 4 · handClockErr` and the return starts by `H`. -/
theorem ExchGeom.readingsNear_hand (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {d y ρ w δ H : ℝ}
    (h : ExchGeom d y ρ w)
    (hcov : exchReturnEnd d y ρ w ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q))
    (hδ : 0 < δ) (h4 : 4 * handClockErr J ħ g hf K q ≤ δ)
    (hdur : δ ≤ 1 / outSpeed y w ∧ δ ≤ 1 / retSpeed y w) (hH : exchReturnStart d y ρ w ≤ H) :
    ReadingsNear (exchEmitStart d y ρ w) (exchEmitEnd d y ρ w) (exchReturnStart d y ρ w)
      (exchReturnEnd d y ρ w) (handTime J ħ g hf K q (exchEmitStart d y ρ w))
      (handTime J ħ g hf K q (exchEmitEnd d y ρ w))
      (handTime J ħ g hf K q (exchReturnStart d y ρ w))
      (handTime J ħ g hf K q (exchReturnEnd d y ρ w)) (handClockErr J ħ g hf K q) δ H := by
  have h0 := h.emitStart_nonneg
  have h1 := h.emitStart_le_emitEnd
  have h2 := h.emitEnd_le_bounceTime.trans h.bounceTime_le_returnStart
  have h3 := h.returnStart_le_returnEnd
  have near : ∀ t, 0 ≤ t → t ≤ exchReturnEnd d y ρ w →
      |handTime J ħ g hf K q t - t| ≤ handClockErr J ħ g hf K q := fun t ht0 ht =>
    abs_handTime_sub_le J ħ g hf hJ hħ hK hq hκ ht0 (ht.trans hcov)
  exact ⟨hδ, h4, by rw [exchEmit_duration]; exact hdur.1, by rw [exchReturn_duration]; exact hdur.2,
    by rw [abs_of_nonneg (by linarith)]; linarith, by rw [abs_of_nonneg (by linarith)]; exact hH,
    near _ h0 (by linarith), near _ (by linarith) (by linarith), near _ (by linarith) h3,
    near _ (by linarith) le_rfl⟩

/-- A reflecting observer's reception readings are within its clock error. -/
theorem abs_handTime_reception_le (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q : LF4.KTorus} (hq : q ∈ handReady K) (hκ : 0 < handRate J ħ g hf q) {ρ w : ℝ}
    (hw : 0 < w) (hρ : ρ < -(1 / 2))
    (hcov : (1 / 2 - ρ) / w ≤ handHorizon K (handRate J ħ g hf q) (handFreq J ħ g hf q)) :
    |handTime J ħ g hf K q ((-(1 / 2) - ρ) / w) - (-(1 / 2) - ρ) / w| ≤ handClockErr J ħ g hf K q
      ∧ |handTime J ħ g hf K q ((1 / 2 - ρ) / w) - (1 / 2 - ρ) / w|
        ≤ handClockErr J ħ g hf K q := by
  have hle : (-(1 / 2) - ρ) / w ≤ (1 / 2 - ρ) / w := div_le_div_of_nonneg_right (by linarith) hw.le
  exact ⟨abs_handTime_sub_le J ħ g hf hJ hħ hK hq hκ (div_nonneg (by linarith) hw.le)
      (hle.trans hcov),
    abs_handTime_sub_le J ħ g hf hJ hħ hK hq hκ (div_nonneg (by linarith) hw.le) hcov⟩

/-- ★★★ **The common chart from the observers' clocks (#248 (a) for the control).** The observer at rest (clock `q₀`)
estimates the relative velocity and separation from a calibration exchange `C`, and charts a
reflection `A` off the moving observer; the moving observer (clock `q₁`) charts a reflection `B` off
the observer at rest; each charts the reflections off itself at its reception write. All readings
are the clocks' own, within `ε₀ = handClockErr q₀` and `ε₁ = handClockErr q₁` over their horizons.
If every write lasts at least `δ ≥ 4ε₀, 4ε₁` and every return starts by `H`, then: the estimates are
within `4ε₀/δ²` of `y` and `sepEstErr ε₀ δ H` of `d`; `A`'s chart is within `chartTimeErr` and
`chartSepErr` of the bounce; and the Galilean map **with the estimated parameters** sends each
family's chart on one clock to within the stated sums of its chart on the other. -/
theorem galilean_transformation_clocks (hJ : 0 < J) (hħ : 0 < ħ) {K : ℕ} (hK : 0 < K)
    {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁)
    {d y ρ w ρ₁ w₁ σ v δ H : ℝ} (hC : ExchGeom d y ρ w) (hA : ExchGeom d y ρ₁ w₁)
    (hB : ExchGeom d y σ v)
    (hcC : exchReturnEnd d y ρ w ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (hcA : exchReturnEnd d y ρ₁ w₁ ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (hcA₁ : (1 / 2 - ρ₁) / w₁ ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁))
    (hcB : exchReturnEnd d y σ v ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁))
    (hcB₀ : (1 / 2 - σ) / v ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (hδ : 0 < δ) (h4₀ : 4 * handClockErr J ħ g hf K q₀ ≤ δ)
    (h4₁ : 4 * handClockErr J ħ g hf K q₁ ≤ δ)
    (hdC : δ ≤ 1 / outSpeed y w ∧ δ ≤ 1 / retSpeed y w)
    (hdA : δ ≤ 1 / outSpeed y w₁ ∧ δ ≤ 1 / retSpeed y w₁)
    (hdB : δ ≤ 1 / outSpeed y v ∧ δ ≤ 1 / retSpeed y v)
    (hHC : exchReturnStart d y ρ w ≤ H) (hHA : exchReturnStart d y ρ₁ w₁ ≤ H)
    (hHB : exchReturnStart d y σ v ≤ H) :
    |clockRelVel J ħ g hf K q₀ d y ρ w - y| ≤ relVelErr (handClockErr J ħ g hf K q₀) δ
    ∧ |clockSep J ħ g hf K q₀ d y ρ w - d| ≤ sepEstErr (handClockErr J ħ g hf K q₀) δ H
    ∧ |(clockTransit J ħ g hf K q₀ d y ρ₁ w₁).1 - bounceTime ρ₁ w₁|
        ≤ chartTimeErr (handClockErr J ħ g hf K q₀) δ H
    ∧ |(clockTransit J ħ g hf K q₀ d y ρ₁ w₁).2 - bounceSep d y ρ₁ w₁|
        ≤ chartSepErr (handClockErr J ħ g hf K q₀) δ H
    ∧ |(galileo (clockSep J ħ g hf K q₀ d y ρ w) (clockRelVel J ħ g hf K q₀ d y ρ w)
          (clockTransit J ħ g hf K q₀ d y ρ₁ w₁)).1 - (clockOwn J ħ g hf K q₁ ρ₁ w₁).1|
        ≤ chartTimeErr (handClockErr J ħ g hf K q₀) δ H + handClockErr J ħ g hf K q₁
    ∧ |(galileo (clockSep J ħ g hf K q₀ d y ρ w) (clockRelVel J ħ g hf K q₀ d y ρ w)
          (clockTransit J ħ g hf K q₀ d y ρ₁ w₁)).2 - (clockOwn J ħ g hf K q₁ ρ₁ w₁).2|
        ≤ chartSepErr (handClockErr J ħ g hf K q₀) δ H + sepEstErr (handClockErr J ħ g hf K q₀) δ H
          + (|y| + relVelErr (handClockErr J ħ g hf K q₀) δ)
            * chartTimeErr (handClockErr J ħ g hf K q₀) δ H
          + relVelErr (handClockErr J ħ g hf K q₀) δ * H
    ∧ |(galileo (clockSep J ħ g hf K q₀ d y ρ w) (clockRelVel J ħ g hf K q₀ d y ρ w)
          (clockOwn J ħ g hf K q₀ σ v)).1 - (flipChart (clockTransit J ħ g hf K q₁ d y σ v)).1|
        ≤ handClockErr J ħ g hf K q₀ + chartTimeErr (handClockErr J ħ g hf K q₁) δ H
    ∧ |(galileo (clockSep J ħ g hf K q₀ d y ρ w) (clockRelVel J ħ g hf K q₀ d y ρ w)
          (clockOwn J ħ g hf K q₀ σ v)).2 - (flipChart (clockTransit J ħ g hf K q₁ d y σ v)).2|
        ≤ sepEstErr (handClockErr J ħ g hf K q₀) δ H
          + (|y| + relVelErr (handClockErr J ħ g hf K q₀) δ) * handClockErr J ħ g hf K q₀
          + relVelErr (handClockErr J ħ g hf K q₀) δ * H
          + chartSepErr (handClockErr J ħ g hf K q₁) δ H := by
  have rC := hC.readingsNear_hand J ħ g hf hJ hħ hK hq₀ hκ₀ hcC hδ h4₀ hdC hHC
  have rA := hA.readingsNear_hand J ħ g hf hJ hħ hK hq₀ hκ₀ hcA hδ h4₀ hdA hHA
  have rB := hB.readingsNear_hand J ħ g hf hJ hħ hK hq₁ hκ₁ hcB hδ h4₁ hdB hHB
  obtain ⟨hy, hd⟩ := hC.relVelEst_sepEst
  have eA := hA.transitChart_eq
  obtain ⟨a₁, b₁⟩ := abs_handTime_reception_le J ħ g hf hJ hħ hK hq₁ hκ₁ hA.w_pos hA.behind hcA₁
  obtain ⟨a₀, b₀⟩ := abs_handTime_reception_le J ħ g hf hJ hħ hK hq₀ hκ₀ hB.w_pos hB.behind hcB₀
  have f1 := galileo_first_stable hC rC hA rA a₁ b₁
  have f2 := galileo_second_stable hC rC hB rB a₀ b₀
  have v1 := rC.abs_relVelEst_sub_le
  have v2 := rC.abs_sepEst_sub_le
  have c1 := rA.abs_chartTime_sub_le
  have c2 := rA.abs_chartSep_sub_le
  rw [hy] at v1
  rw [hd] at v2
  rw [eA] at c1 c2
  exact ⟨v1, v2, c1, c2, f1.1, f1.2, f2.1, f2.2⟩

end Clocks

end CSD.RecordLayer

end
