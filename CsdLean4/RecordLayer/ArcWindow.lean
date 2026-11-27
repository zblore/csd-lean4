/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A smooth periodic window: shut on one arc, open on another

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22 and the window of UA-20; `specs/unified-record-spacetime-plan.md` §9.4; route (γ5b)
of the task plans).

The window `b` of UA-20 is a smooth function of period `1` of a pointer's angle. The
statements about the released return (UD-274, UD-279) ask it to vanish on a stretch
`[a₀, a₀ + δ]` and to be `1` on a stretch `[a₀ + lo, a₀ + hi]`. Here one is exhibited:
`Real.smoothTransition` of an affine function of `cos (2π (x − x₀))`. The two plateaus come
from `cos` being non-increasing on `[0, π]`; no numerical value of a cosine is used.

* `cos_two_pi_mul_le_of_le_abs`, `cos_two_pi_mul_le_of_abs_le`;
* `arcWindow`, `arcWindow_periodic`, `contDiff_arcWindow`, `arcWindow_nonneg`,
  `arcWindow_le_one`;
* ★ `arcWindow_eq_one` — `1` within `D₁` of the centre;
* ★ `arcWindow_eq_zero` — `0` at distance between `D₀` and `1 − D₀` from the centre;
* `gateWindow` and ★★ `gateWindow_eq_zero`, ★★ `gateWindow_eq_one` — **for
  `0 ≤ δ < lo ≤ hi` with `lo + hi ≤ 1`, a smooth window of period `1` with values in
  `[0, 1]`, `0` on `[a₀, a₀ + δ]` and `1` on `[a₀ + lo, a₀ + hi]`.**

## Honest scope

⚠️ **One window, not a class.** Nothing here says a window of UA-20 must have this form.

⚠️ **The plateaus are symmetric about the centre** `a₀ + (lo + hi)/2`, so the window is also
`0` on the mirror image of `[a₀, a₀ + δ]`. The condition `lo + hi ≤ 1` is what this form
needs; a window open on a longer stretch needs another construction.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UD-274, UD-279, UD-280); `specs/unified-records-spacetime-task-plans.md` (§9, route (γ5b));
`RecordLayer/UnifiedReleasedClock.lean` (`releasedClock_eq_zero_of_obs_le`,
`le_releasedClock_of_dwell`); `RecordLayer/UnifiedReleasedBounds.lean`
(`returnClock_le_of_obs_le`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace CSD.RecordLayer

/-- `cos (2π y) ≤ cos (2π D)` when `|y|` is between `D ≥ 0` and `1 − D`. -/
theorem cos_two_pi_mul_le_of_le_abs {y D : ℝ} (hD : 0 ≤ D) (h1 : D ≤ |y|)
    (h2 : |y| ≤ 1 - D) : Real.cos (2 * Real.pi * y) ≤ Real.cos (2 * Real.pi * D) := by
  have hπ := Real.pi_pos
  rw [← Real.cos_abs (2 * Real.pi * y), abs_mul, abs_of_pos Real.two_pi_pos]
  by_cases hy : |y| ≤ 1 / 2
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
  · rw [← Real.cos_two_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [not_le.1 hy])
      (by nlinarith)

/-- `cos (2π D) ≤ cos (2π y)` when `|y| ≤ D ≤ 1/2`. -/
theorem cos_two_pi_mul_le_of_abs_le {y D : ℝ} (h : |y| ≤ D) (hD : D ≤ 1 / 2) :
    Real.cos (2 * Real.pi * D) ≤ Real.cos (2 * Real.pi * y) := by
  have hπ := Real.pi_pos
  rw [← Real.cos_abs (2 * Real.pi * y), abs_mul, abs_of_pos Real.two_pi_pos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg Real.two_pi_pos.le (abs_nonneg y))
    (by nlinarith) (by nlinarith)

/-- **A smooth window of period `1` about the centre `x₀`**: `1` within `D₁` of the centre,
`0` beyond `D₀`. -/
def arcWindow (x₀ D₀ D₁ x : ℝ) : ℝ :=
  Real.smoothTransition
    ((Real.cos (2 * Real.pi * (x - x₀)) - Real.cos (2 * Real.pi * D₀))
      / (Real.cos (2 * Real.pi * D₁) - Real.cos (2 * Real.pi * D₀)))

theorem arcWindow_periodic (x₀ D₀ D₁ : ℝ) : Function.Periodic (arcWindow x₀ D₀ D₁) 1 := by
  intro x
  unfold arcWindow
  rw [show 2 * Real.pi * (x + 1 - x₀) = 2 * Real.pi * (x - x₀) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem contDiff_arcWindow (x₀ D₀ D₁ : ℝ) : ContDiff ℝ ∞ (arcWindow x₀ D₀ D₁) := by
  unfold arcWindow
  exact Real.smoothTransition.contDiff.comp
    (((Real.contDiff_cos.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).sub
      contDiff_const).div_const _)

theorem arcWindow_nonneg (x₀ D₀ D₁ x : ℝ) : 0 ≤ arcWindow x₀ D₀ D₁ x :=
  Real.smoothTransition.nonneg _

theorem arcWindow_le_one (x₀ D₀ D₁ x : ℝ) : arcWindow x₀ D₀ D₁ x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- For `0 ≤ D₁ < D₀ ≤ 1/2` the cosines of the two radii are in the strict order. -/
theorem cos_arc_radius_lt {D₀ D₁ : ℝ} (h0 : 0 ≤ D₁) (h1 : D₁ < D₀) (h2 : D₀ ≤ 1 / 2) :
    0 < Real.cos (2 * Real.pi * D₁) - Real.cos (2 * Real.pi * D₀) := by
  have hπ := Real.pi_pos
  exact sub_pos.2 (Real.cos_lt_cos_of_nonneg_of_le_pi (mul_nonneg Real.two_pi_pos.le h0)
    (by nlinarith) (by nlinarith))

/-- ★ **The window is `1` within `D₁` of the centre.** -/
theorem arcWindow_eq_one {x₀ D₀ D₁ x : ℝ} (h0 : 0 ≤ D₁) (h1 : D₁ < D₀) (h2 : D₀ ≤ 1 / 2)
    (hx : |x - x₀| ≤ D₁) : arcWindow x₀ D₀ D₁ x = 1 := by
  unfold arcWindow
  exact Real.smoothTransition.one_of_one_le ((one_le_div (cos_arc_radius_lt h0 h1 h2)).2
    (sub_le_sub_right (cos_two_pi_mul_le_of_abs_le hx (h1.le.trans h2)) _))

/-- ★ **The window is `0` at distance between `D₀` and `1 − D₀` from the centre.** -/
theorem arcWindow_eq_zero {x₀ D₀ D₁ x : ℝ} (h0 : 0 ≤ D₁) (h1 : D₁ < D₀) (h2 : D₀ ≤ 1 / 2)
    (hx1 : D₀ ≤ |x - x₀|) (hx2 : |x - x₀| ≤ 1 - D₀) : arcWindow x₀ D₀ D₁ x = 0 := by
  unfold arcWindow
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.2 (cos_two_pi_mul_le_of_le_abs (h0.trans h1.le) hx1 hx2))
    (cos_arc_radius_lt h0 h1 h2).le)

/-- **The gate window**: for `0 ≤ δ < lo ≤ hi` with `lo + hi ≤ 1` it is `0` on
`[a₀, a₀ + δ]` and `1` on `[a₀ + lo, a₀ + hi]`. -/
def gateWindow (a₀ δ lo hi : ℝ) : ℝ → ℝ :=
  arcWindow (a₀ + (lo + hi) / 2) ((lo + hi) / 2 - δ) ((hi - lo) / 2)

theorem gateWindow_periodic (a₀ δ lo hi : ℝ) : Function.Periodic (gateWindow a₀ δ lo hi) 1 :=
  arcWindow_periodic _ _ _

theorem contDiff_gateWindow (a₀ δ lo hi : ℝ) : ContDiff ℝ ∞ (gateWindow a₀ δ lo hi) :=
  contDiff_arcWindow _ _ _

theorem gateWindow_nonneg (a₀ δ lo hi x : ℝ) : 0 ≤ gateWindow a₀ δ lo hi x :=
  arcWindow_nonneg _ _ _ _

theorem gateWindow_le_one (a₀ δ lo hi x : ℝ) : gateWindow a₀ δ lo hi x ≤ 1 :=
  arcWindow_le_one _ _ _ _

/-- ★★ **The gate is shut on `[a₀, a₀ + δ]`.** -/
theorem gateWindow_eq_zero {a₀ δ lo hi x : ℝ} (hδ : 0 ≤ δ) (hδlo : δ < lo) (hlh : lo ≤ hi)
    (hsum : lo + hi ≤ 1) (hx0 : a₀ ≤ x) (hx1 : x ≤ a₀ + δ) : gateWindow a₀ δ lo hi x = 0 := by
  unfold gateWindow
  refine arcWindow_eq_zero (by linarith) (by linarith) (by linarith) ?_ ?_
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- ★★ **The gate is open on `[a₀ + lo, a₀ + hi]`.** -/
theorem gateWindow_eq_one {a₀ δ lo hi x : ℝ} (hδ : 0 ≤ δ) (hδlo : δ < lo) (hlh : lo ≤ hi)
    (hsum : lo + hi ≤ 1) (hx0 : a₀ + lo ≤ x) (hx1 : x ≤ a₀ + hi) :
    gateWindow a₀ δ lo hi x = 1 := by
  unfold gateWindow
  refine arcWindow_eq_one (by linarith) (by linarith) (by linarith) ?_
  rw [abs_le]
  constructor <;> linarith

end CSD.RecordLayer

end
