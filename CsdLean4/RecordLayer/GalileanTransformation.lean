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
brief, step 7), for the control candidate (A).

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

⚠️ **This is the control (A).** The test chain's transformation is #259, behind #256.

References: `specs/BACKLOG.md` #247, #259, #246, #245, #244, #243, #257, #248, #256, #39;
`RecordLayer/SignalCone.lean` (`exchEmit_duration`, `exchReturn_duration`, `half_anisotropy`);
`RecordLayer/MovingRadar.lean` (`ExchGeom.bounceTime_sub_emitEnd`, `train_radar`);
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

end CSD.RecordLayer

end
