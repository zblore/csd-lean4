/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import CsdLean4.RecordLayer.GalileanTransformation

/-!
# Lorentz kinematics in any number of space dimensions

**Category:** 7-SigmaLayer (the record layer). BACKLOG #292 (split of #289;
`specs/beyond-1p1-scoping.md`).

The 1+1 line works with `lorentzBoost` on `ℝ × ℝ`. Mathlib has no Lorentz group, so this file
builds the part the record layer uses, on `ℝ × E` for any real inner-product space `E` (`d + 1`
dimensions is `E = EuclideanSpace ℝ (Fin d)`), with `c = 1`.

## The Minkowski form and the boosts

* `minkowskiInner` (`t s − ⟪x, y⟫`), `minkowskiSqD` (`t² − ‖x‖²`), `minkowskiSqD_eq`;
* `boostGamma` (`1/√(1 − v²)`), `boostGamma_sq_mul`, `boostGamma_pos`;
* `boostD n v` — **the boost at speed `v` along the unit vector `n`**: time `γ (t − v ⟪n, x⟫)`,
  position `x + ((γ − 1) ⟪n, x⟫ − γ v t) n`; `boostD_sub` (it is additive), `boostD_time_sub`;
* ★★★ `minkowskiInner_boostD` (**every boost preserves the Minkowski inner product**),
  ★★ `minkowskiSqD_boostD`;
* ★ `boostD_real_eq_lorentzBoost` — **on `E = ℝ` along `n = 1` it is the 1+1 `lorentzBoost`**.

## Proper time and relative motion

* `properTime` (`√(t² − ‖x‖²)`), ★★★ `properTime_boostD` (**proper time is the same in every
  frame**, the `d+1` `proper_time_boost`), ★ `properTime_worldline` (`√(1 − ‖u‖²) Δt` along a
  segment of velocity `u`);
* `relGamma` (the Lorentz factor of relative motion, `⟨e, f⟩ / √(e² f²)`), ★★ `relGamma_boostD`
  (**a common boost leaves it unchanged**), ★ `relGamma_vel` (for velocities `u`, `w`:
  `(1 − ⟪u, w⟫) / (√(1 − ‖u‖²) √(1 − ‖w‖²))`).

## Time order

* ★★★ `timelike_order_boostD` (**an event later than another by at least their distance is later
  in every boosted frame**, the `d+1` `timelike_order_boost_invariant`);
* ★★★ `exists_boostD_reverses_spacelike` (**two spacelike-separated events are reversed in time by
  a boost along their separation**, the `d+1` `exists_boost_reverses_spacelike`).

## Honest scope

⚠️ **Boosts only, not the Lorentz group.** Rotations, compositions of boosts and the Thomas–Wigner
rotation are not built: the record layer's covariance runs through proper times and Minkowski
products, which every boost preserves (`specs/beyond-1p1-scoping.md` §2.4).

⚠️ **`relGamma` is the Lorentz factor of relative motion, not a relative velocity vector.** The
relative speed is `√(1 − 1/relGamma²)`; its direction is frame dependent (Wigner) and not used.

References: `specs/BACKLOG.md` #292, #289, ~~#287~~, ~~#290~~; `specs/beyond-1p1-scoping.md`;
`RecordLayer/GalileanTransformation.lean` (`lorentzBoost`); `RecordLayer/FrameCovariance.lean`
(`proper_time_boost`); `RecordLayer/SelectionOrder.lean` (`timelike_order_boost_invariant`,
`exists_boost_reverses_spacelike`); `specs/future-work.md`.
-/

@[expose] public section

open RealInnerProductSpace

noncomputable section

namespace CSD.RecordLayer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The Minkowski form and the boosts -/

/-- The Minkowski inner product on `ℝ × E`, `c = 1`: `t s − ⟪x, y⟫`. -/
def minkowskiInner (e f : ℝ × E) : ℝ := e.1 * f.1 - ⟪e.2, f.2⟫

/-- The Minkowski square `t² − ‖x‖²`. -/
def minkowskiSqD (e : ℝ × E) : ℝ := minkowskiInner e e

theorem minkowskiSqD_eq (e : ℝ × E) : minkowskiSqD e = e.1 ^ 2 - ‖e.2‖ ^ 2 := by
  rw [minkowskiSqD, minkowskiInner, real_inner_self_eq_norm_sq]
  ring

/-- The Lorentz factor `1/√(1 − v²)`. -/
def boostGamma (v : ℝ) : ℝ := (Real.sqrt (1 - v ^ 2))⁻¹

theorem one_sub_sq_pos {v : ℝ} (hv : |v| < 1) : 0 < 1 - v ^ 2 := by
  nlinarith [sq_abs v, abs_nonneg v]

theorem boostGamma_pos {v : ℝ} (hv : |v| < 1) : 0 < boostGamma v :=
  inv_pos.2 (Real.sqrt_pos.2 (one_sub_sq_pos hv))

theorem boostGamma_sq_mul {v : ℝ} (hv : |v| < 1) : boostGamma v ^ 2 * (1 - v ^ 2) = 1 := by
  rw [boostGamma, inv_pow, Real.sq_sqrt (one_sub_sq_pos hv).le]
  exact inv_mul_cancel₀ (one_sub_sq_pos hv).ne'

/-- **The boost at speed `v` along the unit vector `n`.** -/
def boostD (n : E) (v : ℝ) (e : ℝ × E) : ℝ × E :=
  (boostGamma v * (e.1 - v * ⟪n, e.2⟫),
    e.2 + ((boostGamma v - 1) * ⟪n, e.2⟫ - boostGamma v * v * e.1) • n)

theorem boostD_sub (n : E) (v : ℝ) (e f : ℝ × E) :
    boostD n v (e - f) = boostD n v e - boostD n v f := by
  simp only [boostD, Prod.fst_sub, Prod.snd_sub, inner_sub_right, Prod.mk_sub_mk]
  congr 1
  · ring
  · rw [show ((boostGamma v - 1) * (⟪n, e.2⟫ - ⟪n, f.2⟫) - boostGamma v * v * (e.1 - f.1))
        = ((boostGamma v - 1) * ⟪n, e.2⟫ - boostGamma v * v * e.1)
          - ((boostGamma v - 1) * ⟪n, f.2⟫ - boostGamma v * v * f.1) by ring, sub_smul]
    abel

/-- The boosted time difference of two events. -/
theorem boostD_time_sub (n : E) (v : ℝ) (eA eB : ℝ × E) :
    (boostD n v eB).1 - (boostD n v eA).1
      = boostGamma v * ((eB.1 - eA.1) - v * ⟪n, eB.2 - eA.2⟫) := by
  simp only [boostD, inner_sub_right]
  ring

/-- ★★★ **Every boost preserves the Minkowski inner product.** -/
theorem minkowskiInner_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) (e f : ℝ × E) :
    minkowskiInner (boostD n v e) (boostD n v f) = minkowskiInner e f := by
  have hγ := boostGamma_sq_mul hv
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  simp only [minkowskiInner, boostD, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hnn]
  rw [real_inner_comm e.2 n, real_inner_comm f.2 n]
  linear_combination (e.1 * f.1 - ⟪f.2, n⟫ * ⟪e.2, n⟫) * hγ

/-- ★★ **Every boost preserves the Minkowski square.** -/
theorem minkowskiSqD_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) (e : ℝ × E) :
    minkowskiSqD (boostD n v e) = minkowskiSqD e :=
  minkowskiInner_boostD hn hv e e

/-- ★ **On `E = ℝ` along `n = 1`, the boost is the 1+1 `lorentzBoost`.** -/
theorem boostD_real_eq_lorentzBoost (v : ℝ) (e : ℝ × ℝ) :
    boostD (1 : ℝ) v e = lorentzBoost 1 v e := by
  have hi : ⟪(1 : ℝ), e.2⟫ = e.2 := by simp
  simp only [boostD, lorentzBoost, hi, boostGamma, one_pow, div_one, smul_eq_mul, mul_one]
  ext
  · simp only
    ring
  · simp only
    ring

/-! ### Proper time and relative motion -/

/-- The proper time of a displacement, `√(t² − ‖x‖²)`. -/
def properTime (e : ℝ × E) : ℝ := Real.sqrt (minkowskiSqD e)

/-- ★★★ **Proper time is the same in every frame.** -/
theorem properTime_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) (e : ℝ × E) :
    properTime (boostD n v e) = properTime e := by
  rw [properTime, properTime, minkowskiSqD_boostD hn hv]

/-- ★ **Along a segment of velocity `u`, proper time is `√(1 − ‖u‖²) Δt`.** -/
theorem properTime_worldline (u : E) {Δt : ℝ} (hΔ : 0 ≤ Δt) :
    properTime ((Δt, Δt • u) : ℝ × E) = Real.sqrt (1 - ‖u‖ ^ 2) * Δt := by
  rw [properTime, minkowskiSqD_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔ,
    show Δt ^ 2 - (Δt * ‖u‖) ^ 2 = (1 - ‖u‖ ^ 2) * Δt ^ 2 by ring,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hΔ]

/-- The Lorentz factor of relative motion of two displacements, `⟨e, f⟩ / √(e² f²)`. -/
def relGamma (e f : ℝ × E) : ℝ := minkowskiInner e f / Real.sqrt (minkowskiSqD e * minkowskiSqD f)

/-- ★★ **A common boost leaves the relative Lorentz factor unchanged.** -/
theorem relGamma_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) (e f : ℝ × E) :
    relGamma (boostD n v e) (boostD n v f) = relGamma e f := by
  rw [relGamma, relGamma, minkowskiInner_boostD hn hv, minkowskiSqD_boostD hn hv,
    minkowskiSqD_boostD hn hv]

/-- ★ **For two velocities, the relative Lorentz factor of their four-velocities.** -/
theorem relGamma_vel {u : E} (hu : ‖u‖ ≤ 1) (w : E) :
    relGamma ((1, u) : ℝ × E) (1, w)
      = (1 - ⟪u, w⟫) / (Real.sqrt (1 - ‖u‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) := by
  have h0 : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  rw [relGamma, minkowskiSqD_eq, minkowskiSqD_eq, minkowskiInner, Real.sqrt_mul (by simpa using h0)]
  simp

/-! ### Time order -/

/-- ★★★ **Timelike or null order is the same in every boosted frame.** If `eB` is later than `eA`
by at least their distance, it is later after every boost. -/
theorem timelike_order_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) {eA eB : ℝ × E}
    (hpos : 0 < eB.1 - eA.1) (h : ‖eB.2 - eA.2‖ ≤ eB.1 - eA.1) :
    (boostD n v eA).1 < (boostD n v eB).1 := by
  have hvx : v * ⟪n, eB.2 - eA.2⟫ < eB.1 - eA.1 := by
    calc v * ⟪n, eB.2 - eA.2⟫ ≤ |v * ⟪n, eB.2 - eA.2⟫| := le_abs_self _
      _ = |v| * |⟪n, eB.2 - eA.2⟫| := abs_mul _ _
      _ ≤ |v| * (‖n‖ * ‖eB.2 - eA.2‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg v)
      _ ≤ |v| * (eB.1 - eA.1) := by
          rw [hn, one_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg v)
      _ < 1 * (eB.1 - eA.1) := mul_lt_mul_of_pos_right hv hpos
      _ = eB.1 - eA.1 := one_mul _
  have hd := boostD_time_sub n v eA eB
  have : 0 < boostGamma v * ((eB.1 - eA.1) - v * ⟪n, eB.2 - eA.2⟫) :=
    mul_pos (boostGamma_pos hv) (by linarith)
  linarith

/-- ★★★ **Spacelike order is reversed by a boost along the separation.** -/
theorem exists_boostD_reverses_spacelike {eA eB : ℝ × E} (h : |eB.1 - eA.1| < ‖eB.2 - eA.2‖) :
    ∃ n : E, ∃ v : ℝ, ‖n‖ = 1 ∧ |v| < 1 ∧ (boostD n v eB).1 < (boostD n v eA).1 := by
  set a := eB.1 - eA.1
  set x := eB.2 - eA.2
  set b := ‖x‖
  have hb : 0 < b := lt_of_le_of_lt (abs_nonneg a) h
  obtain ⟨ha1, ha2⟩ := abs_lt.1 h
  refine ⟨b⁻¹ • x, (a + b) / (2 * b), ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hb, inv_mul_cancel₀ hb.ne']
  · rw [abs_div, abs_mul, abs_two, abs_of_pos (by linarith : 0 < a + b), abs_of_pos hb,
      div_lt_one (by positivity)]
    linarith
  · have hnx : ⟪b⁻¹ • x, x⟫ = b := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      show b⁻¹ * b ^ 2 = b
      field_simp
    have hd := boostD_time_sub (b⁻¹ • x) ((a + b) / (2 * b)) eA eB
    rw [hnx] at hd
    have hub : (a + b) / (2 * b) * b = (a + b) / 2 := by field_simp
    have hneg : boostGamma ((a + b) / (2 * b)) * (a - (a + b) / (2 * b) * b) < 0 := by
      have hv : |(a + b) / (2 * b)| < 1 := by
        rw [abs_div, abs_mul, abs_two, abs_of_pos (by linarith : 0 < a + b), abs_of_pos hb,
          div_lt_one (by positivity)]
        linarith
      exact mul_neg_of_pos_of_neg (boostGamma_pos hv) (by rw [hub]; linarith)
    linarith

end CSD.RecordLayer
