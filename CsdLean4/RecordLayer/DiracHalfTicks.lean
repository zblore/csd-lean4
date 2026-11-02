/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracRadar

/-!
# Half-ticks: the rate counter read against the opposite mark

**Category:** 7-SigmaLayer (the record layer). BACKLOG #277 (residue of ~~#259~~).

#273's rate counter integrates `max(Re(ū S), 0)`, `S` the splitting coherence and `u` the mark,
and writes tick `n` at `2πn/R`. Read against the opposite mark `−u` it integrates
`max(−Re(ū S), 0)`, the same weight shifted by half a turn, and writes **half-tick** `n` at
`π(2n − 1)/R`. No new register is needed: since `max(x, 0) − max(−x, 0) = x` and `Re(ū S)` is the
rate of the **quarter reading** `Re(conj(−iu) C)`, the half-tick register is the tick register minus
the quarter reading's change — a function of the state. So half-ticks of `A`'s clock are records of
the radar arena of ~~#274~~ as it stands.

## Along the device from any start

* ★ `hasDerivAt_deviceCoherence_prop` — **`dC/dt = −i S` along `e^{−itH_dev}` from every start**;
  `quarterReading`, `hasDerivAt_quarterReading_prop`,
  ★ `integral_rate_eq` — **`∫₀ᵗ Re(ū S) = Q(t) − Q(0)`**; `rateWeight_neg`
  (**`w_{−u} = w_u − Re(ū S)`**).

## The exact half-turn

* `integral_shift_neg_cos` (the weight read against `−u` is the weight shifted by `π/R`),
  `integral_max_cos_half` (`∫₀^{π/R} = κ/R`), ★ `integral_max_neg_cos_half_tick` —
  **`∫₀^{π(2n−1)/R} max(−κ cos(Rs), 0) = (2n − 1)κ/R`**; `integral_max_neg_cos_mono`,
  `le_integral_max_neg_cos_near`.

## A drifting device

* `abs_rateWeight_neg_sub_le`, `abs_integral_rateWeight_neg_sub_le`, `integral_rateWeight_neg_mono`,
  `half_margin`, `drift_nonneg`;
  ★★ `half_register_lt`, ★★ `half_register_ge` — **the half register stays below `(2n − 1)|C₀|`
  before `π(2n−1)/R − δ` and is at least that from `π(2n−1)/R + δ`**, under the rate counter's
  margin.

## The half-ticks of the clock at rest, in the radar arena

* `restHalfTickRadar` — **half-tick `n` of `A`'s clock (`1 ≤ n ≤ 130`), written within `10¹¹` of
  `(n − 1/2) · 2π·10¹¹`**, an actual occurrence of the radar arena's one evolution;
  `restHalfTickRadar_fields`.

## Honest scope

⚠️ **The same margin as the ticks**: the write windows are `±10¹¹`, a sixth of a period, so a
half-tick sharpens a bracket only where an event's window clears it — at the return and the meeting
of ~~#259~~ (`DiracWorldline.lean`), not at the emission or `B`'s events.

References: `specs/BACKLOG.md` #277, #259, #273, #274, #271; `RecordLayer/DiracRateTicks.lean`
(`rateWeight`, `rateDriftDetector`, `hasDerivAt_quarterReading`, `splitCoherence_shift_sharp`,
`integral_max_cos_lobe`, `deviceRateTick`); `RecordLayer/DiracTicks.lean` (`integral_max_cos`,
`tickMark`, `re_star_tickMark_mul`); `RecordLayer/DiracDeviceTicks.lean`
(`le_integral_max_cos_near`); `RecordLayer/DiracRadar.lean` (`restTickRadar`, `radarWeight_one`,
`hasDerivAt_deviceProp_mulVec`); `RecordLayer/DiracTwin.lean` (`twinRestTick`, `twin_rest_rate`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

variable {L : ℕ} [NeZero L]

/-! ### Along the device from any start -/

/-- ★ **`dC/dt = −i S` along the device from every start.** -/
theorem hasDerivAt_deviceCoherence_prop (J μ₀ μ₁ : ℝ) (v : (ZMod L × Fin 2) × Fin 2 → ℂ) (t : ℝ) :
    HasDerivAt (fun s => deviceCoherence (deviceProp (L := L) J μ₀ μ₁ s *ᵥ v))
      (-I * splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ t *ᵥ v)) t := by
  have h := hasDerivAt_deviceProp_mulVec (L := L) J μ₀ μ₁ v t
  have hc := fun x => hasDerivAt_pi.1 h x
  unfold deviceCoherence splitCoherence
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun p _ =>
    ((hc (p, 0)).star).mul (hc (p, 1))
  convert hs using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_neg, Complex.star_def, Complex.conj_I]
  ring

/-- **The quarter reading** `Re(conj(−iu) C)`. -/
noncomputable def quarterReading (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  (star (-I * u) * deviceCoherence Ψ).re

theorem hasDerivAt_quarterReading_prop (J μ₀ μ₁ : ℝ) (u : ℂ) (v : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (t : ℝ) :
    HasDerivAt (fun s => quarterReading u (deviceProp (L := L) J μ₀ μ₁ s *ᵥ v))
      (star u * splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ t *ᵥ v)).re t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_deviceCoherence_prop (L := L) J μ₀ μ₁ v t).const_mul (star (-I * u)))
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  unfold quarterReading
  convert h using 2
  rw [star_mul', star_neg, show star I = -I from Complex.conj_I]
  linear_combination (star u * splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ t *ᵥ v))
    * Complex.I_sq

/-- ★ **The rate integrates to the quarter reading**: `∫₀ᵗ Re(ū S) = Q(t) − Q(0)`. -/
theorem integral_rate_eq (J μ₀ μ₁ : ℝ) (u : ℂ) (v : (ZMod L × Fin 2) × Fin 2 → ℂ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (star u * splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ v)).re
      = quarterReading u (deviceProp (L := L) J μ₀ μ₁ t *ᵥ v) - quarterReading u v := by
  have hcont : Continuous fun s =>
      (star u * splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ v)).re :=
    Complex.continuous_re.comp (continuous_const.mul
      ((continuous_splitCoherence J μ₀ μ₁).comp
        ((continuous_deviceProp_mulVec (L := L) J μ₀ μ₁).comp
          (continuous_const.prodMk continuous_id))))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_quarterReading_prop J μ₀ μ₁ u v s) (hcont.intervalIntegrable 0 t),
    deviceProp_zero, Matrix.one_mulVec]

/-- **The weight against the opposite mark** is the weight against the mark minus the rate. -/
theorem rateWeight_neg (J μ₀ μ₁ : ℝ) (u : ℂ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    rateWeight J μ₀ μ₁ (-u) Ψ
      = rateWeight J μ₀ μ₁ u Ψ - (star u * splitCoherence J μ₀ μ₁ Ψ).re := by
  unfold rateWeight
  rw [star_neg, neg_mul, Complex.neg_re]
  rcases le_total 0 (star u * splitCoherence J μ₀ μ₁ Ψ).re with h | h
  · rw [max_eq_right (by linarith), max_eq_left h]
    ring
  · rw [max_eq_left (by linarith), max_eq_right h]
    ring

/-! ### The exact half-turn -/

/-- The weight read against `−u` is the weight shifted by `π/R`. -/
theorem integral_shift_neg_cos {K R : ℝ} (hR : 0 < R) (a b : ℝ) :
    ∫ s in a..b, max (-(K * Real.cos (R * s))) 0
      = ∫ s in a + Real.pi / R..b + Real.pi / R, max (K * Real.cos (R * s)) 0 := by
  rw [← intervalIntegral.integral_comp_add_right (fun s => max (K * Real.cos (R * s)) 0)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show R * (s + Real.pi / R) = R * s + Real.pi by field_simp, Real.cos_add_pi, mul_neg]

/-- `∫₀^{π/R} max(κ cos(Rs), 0) = κ/R`: the first half lobe, and nothing after it. -/
theorem integral_max_cos_half {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R) :
    ∫ s in (0 : ℝ)..Real.pi / R, max (K * Real.cos (R * s)) 0 = K / R := by
  have hc : Continuous fun s => max (K * Real.cos (R * s)) 0 := by fun_prop
  have hlobe := (integral_max_cos_lobe hK hR 0).1
  simp only [Nat.cast_zero, mul_zero, zero_div, zero_add, one_mul] at hlobe
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (Real.pi / (2 * R)))
    (hc.intervalIntegrable _ _), hlobe]
  have hzero : ∫ s in Real.pi / (2 * R)..Real.pi / R, max (K * Real.cos (R * s)) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · exact intervalIntegral.integral_zero
    · have hle : Real.pi / (2 * R) ≤ Real.pi / R :=
        div_le_div_of_nonneg_left Real.pi_pos.le hR (by linarith)
      rw [Set.uIcc_of_le hle] at hs
      have h1 : Real.pi / 2 ≤ R * s := by
        have := mul_le_mul_of_nonneg_left hs.1 hR.le
        rwa [show R * (Real.pi / (2 * R)) = Real.pi / 2 by field_simp] at this
      have h2 : R * s ≤ Real.pi := by
        have := mul_le_mul_of_nonneg_left hs.2 hR.le
        rwa [show R * (Real.pi / R) = Real.pi by field_simp] at this
      exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hK
        (Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith [Real.pi_pos])))
  rw [hzero, add_zero]

/-- ★ **The opposite reading over `n − 1/2` turns**: `∫₀^{π(2n−1)/R} max(−κ cos(Rs), 0) =
(2n − 1)κ/R`. -/
theorem integral_max_neg_cos_half_tick {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (n : ℕ) :
    ∫ s in (0 : ℝ)..Real.pi * (2 * n - 1) / R, max (-(K * Real.cos (R * s))) 0
      = (2 * n - 1) * K / R := by
  have hc : Continuous fun s => max (K * Real.cos (R * s)) 0 := by fun_prop
  rw [integral_shift_neg_cos hR, zero_add,
    show Real.pi * (2 * n - 1) / R + Real.pi / R = 2 * Real.pi * n / R by field_simp; ring]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (Real.pi / R))
    (hc.intervalIntegrable (μ := volume) (Real.pi / R) (2 * Real.pi * n / R))
  rw [integral_max_cos hK hR n, integral_max_cos_half hK hR] at h
  have e : (2 * n - 1) * K / R = 2 * n * K / R - K / R := by ring
  linarith

theorem integral_max_neg_cos_mono {K R : ℝ} {t₁ t : ℝ} (h : t₁ ≤ t) :
    ∫ s in (0 : ℝ)..t₁, max (-(K * Real.cos (R * s))) 0
      ≤ ∫ s in (0 : ℝ)..t, max (-(K * Real.cos (R * s))) 0 := by
  have hc : Continuous fun s => max (-(K * Real.cos (R * s))) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 t₁)
    (hc.intervalIntegrable (μ := volume) t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun s _ =>
    le_max_right (-(K * Real.cos (R * s))) 0
  linarith

/-- The opposite reading gains at least `κ(b − a)/2` within `1/R` of half-tick `n`. -/
theorem le_integral_max_neg_cos_near {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (n : ℕ) {a b : ℝ}
    (hab : a ≤ b) (ha : Real.pi * (2 * n - 1) / R - 1 / R ≤ a)
    (hb : b ≤ Real.pi * (2 * n - 1) / R + 1 / R) :
    K / 2 * (b - a) ≤ ∫ s in a..b, max (-(K * Real.cos (R * s))) 0 := by
  rw [integral_shift_neg_cos hR]
  have e : Real.pi * (2 * n - 1) / R + Real.pi / R = 2 * Real.pi * n / R := by field_simp; ring
  have h := le_integral_max_cos_near hK hR n (a := a + Real.pi / R) (b := b + Real.pi / R)
    (by linarith) (by linarith) (by linarith)
  linarith

/-! ### A drifting device -/

/-- A drifting rate moves the weight against the opposite mark by at most its drift. -/
theorem abs_rateWeight_neg_sub_le {J μ₀ μ₁ : ℝ} {Ψ₀ Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ}
    (hC : deviceCoherence Ψ₀ ≠ 0) {R s ε : ℝ}
    (h : ‖splitCoherence J μ₀ μ₁ Ψ
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ ε) :
    |rateWeight J μ₀ μ₁ (-tickMark Ψ₀) Ψ
      - max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0| ≤ ε := by
  have e : R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s)
      = (star (tickMark Ψ₀)
        * ((R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀))).re := by
    rw [mul_left_comm, Complex.re_ofReal_mul, re_star_tickMark_mul hC, mul_assoc]
  rw [rateWeight, e, star_neg, neg_mul, Complex.neg_re]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [neg_sub_neg, abs_sub_comm, ← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_star, norm_tickMark hC, one_mul]
  exact h

section Drift

variable (J μ₀ μ₁ : ℝ) {R ε : ℝ} {Ψ₀ : (ZMod L × Fin 2) × Fin 2 → ℂ}

theorem abs_integral_rateWeight_neg_sub_le (hC : deviceCoherence Ψ₀ ≠ 0)
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
    {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t,
        rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      - ∫ s in (0 : ℝ)..t, max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0|
      ≤ ε * (t + R * t ^ 2 / 2) := by
  have hG := (continuous_weight_deviceProp J μ₀ μ₁ (continuous_rateWeight J μ₀ μ₁ (-tickMark Ψ₀))
    Ψ₀).intervalIntegrable (μ := volume) 0 t
  have hF : IntervalIntegrable (fun s => max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0)
      volume 0 t :=
    (by fun_prop : Continuous fun s =>
      max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0).intervalIntegrable 0 t
  rw [← intervalIntegral.integral_sub hG hF, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => ε * (1 + R * s)) ht
    (Filter.Eventually.of_forall fun s hs => ?_)
    ((by fun_prop : Continuous fun s : ℝ => ε * (1 + R * s)).intervalIntegrable
      (μ := volume) 0 t)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    have h := abs_rateWeight_neg_sub_le hC (hdrift s)
    rw [abs_of_pos hs.1] at h
    exact h.trans_eq (mul_comm _ ε)
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => R * x).intervalIntegrable 0 t),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
    ring

theorem integral_rateWeight_neg_mono {t₁ t : ℝ} (h : t₁ ≤ t) :
    (∫ s in (0 : ℝ)..t₁,
        rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      ≤ ∫ s in (0 : ℝ)..t,
        rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun s => rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      volume a b :=
    fun a b => (continuous_weight_deviceProp J μ₀ μ₁ (continuous_rateWeight J μ₀ μ₁ _)
      Ψ₀).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun s _ =>
    rateWeight_nonneg J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
  linarith

theorem half_margin (hR : 0 < R) (n : ℕ) {δ : ℝ}
    (hm : ε * ((Real.pi * (2 * n - 1) / R + δ) ^ 2 + 2 * (Real.pi * (2 * n - 1) / R + δ) / R)
      < ‖deviceCoherence Ψ₀‖ * δ) :
    ε * ((Real.pi * (2 * n - 1) / R + δ) + R * (Real.pi * (2 * n - 1) / R + δ) ^ 2 / 2)
      < R * ‖deviceCoherence Ψ₀‖ / 2 * δ := by
  have h1 := mul_lt_mul_of_pos_right hm (show 0 < R / 2 by positivity)
  have e : ε * ((Real.pi * (2 * n - 1) / R + δ) ^ 2 + 2 * (Real.pi * (2 * n - 1) / R + δ) / R)
      * (R / 2)
      = ε * ((Real.pi * (2 * n - 1) / R + δ) + R * (Real.pi * (2 * n - 1) / R + δ) ^ 2 / 2) := by
    field_simp
    ring
  rw [e] at h1
  linarith

theorem drift_nonneg
    (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε) :
    0 ≤ ε := by
  have h0 := hdrift 0
  rw [abs_zero, mul_zero, add_zero, one_mul] at h0
  exact (norm_nonneg _).trans h0

variable (hR : 0 < R) (hC : deviceCoherence Ψ₀ ≠ 0)
  (hdrift : ∀ s, ‖splitCoherence J μ₀ μ₁ (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀)
      - (R : ℂ) * (exp (I * (((-R : ℝ) : ℂ) * s)) * deviceCoherence Ψ₀)‖ ≤ (1 + R * |s|) * ε)
  (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδR : δ ≤ 1 / R)
  (hm : ε * ((Real.pi * (2 * n - 1) / R + δ) ^ 2 + 2 * (Real.pi * (2 * n - 1) / R + δ) / R)
      < ‖deviceCoherence Ψ₀‖ * δ)
include hR hC hdrift hδ hδR hm

/-- ★★ **Before the half-tick the half register is below `(2n − 1)|C₀|`.** -/
theorem half_register_lt (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < Real.pi * (2 * n - 1) / R - δ) :
    (∫ s in (0 : ℝ)..t,
        rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀))
      < (2 * n - 1) * ‖deviceCoherence Ψ₀‖ := by
  have hε := drift_nonneg J μ₀ μ₁ hdrift
  have hE := half_margin hR n hm
  have hκ : 0 ≤ R * ‖deviceCoherence Ψ₀‖ := mul_nonneg hR.le (norm_nonneg _)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set tn := Real.pi * (2 * n - 1) / R
  have htn : 0 ≤ tn := by
    have : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    positivity
  have hI : (∫ s in (0 : ℝ)..tn, max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0)
      = (2 * n - 1) * ‖deviceCoherence Ψ₀‖ := by
    rw [integral_max_neg_cos_half_tick hκ hR n]
    field_simp
  have hcI : ∀ a b : ℝ, IntervalIntegrable
      (fun s => max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0) volume a b :=
    fun a b => (by fun_prop : Continuous fun s =>
      max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0).intervalIntegrable a b
  have hRinv : 0 < 1 / R := by positivity
  have hb := (abs_le.1 (abs_integral_rateWeight_neg_sub_le J μ₀ μ₁ hC hdrift ht0)).2
  have hmono := integral_max_neg_cos_mono (K := R * ‖deviceCoherence Ψ₀‖) (R := R) ht.le
  have hnear := le_integral_max_neg_cos_near hκ hR n (a := tn - δ) (b := tn) (by linarith)
    (by linarith) (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 (tn - δ)) (hcI (tn - δ) tn)
  have hEt : ε * (t + R * t ^ 2 / 2) ≤ ε * ((tn + δ) + R * (tn + δ) ^ 2 / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hε
    have h2 : t ^ 2 ≤ (tn + δ) ^ 2 := pow_le_pow_left₀ ht0 (by linarith) 2
    have h3 : R * t ^ 2 ≤ R * (tn + δ) ^ 2 := mul_le_mul_of_nonneg_left h2 hR.le
    linarith
  rw [← hI]
  linarith

/-- ★★ **From just after the half-tick the half register is at least `(2n − 1)|C₀|`.** -/
theorem half_register_ge (hn : 1 ≤ n) {t : ℝ} (ht : Real.pi * (2 * n - 1) / R + δ ≤ t) :
    (2 * n - 1) * ‖deviceCoherence Ψ₀‖
      ≤ ∫ s in (0 : ℝ)..t,
        rateWeight J μ₀ μ₁ (-tickMark Ψ₀) (deviceProp (L := L) J μ₀ μ₁ s *ᵥ Ψ₀) := by
  have hE := half_margin hR n hm
  have hκ : 0 ≤ R * ‖deviceCoherence Ψ₀‖ := mul_nonneg hR.le (norm_nonneg _)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set tn := Real.pi * (2 * n - 1) / R
  have htn : 0 ≤ tn := by
    have : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    positivity
  have hI : (∫ s in (0 : ℝ)..tn, max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0)
      = (2 * n - 1) * ‖deviceCoherence Ψ₀‖ := by
    rw [integral_max_neg_cos_half_tick hκ hR n]
    field_simp
  have hcI : ∀ a b : ℝ, IntervalIntegrable
      (fun s => max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0) volume a b :=
    fun a b => (by fun_prop : Continuous fun s =>
      max (-(R * ‖deviceCoherence Ψ₀‖ * Real.cos (R * s))) 0).intervalIntegrable a b
  have hRinv : 0 < 1 / R := by positivity
  have hmono := integral_rateWeight_neg_mono J μ₀ μ₁ (Ψ₀ := Ψ₀) ht
  have hb := (abs_le.1 (abs_integral_rateWeight_neg_sub_le J μ₀ μ₁ hC hdrift
    (t := tn + δ) (by linarith))).1
  have hnear := le_integral_max_neg_cos_near hκ hR n (a := tn) (b := tn + δ) (by linarith)
    (by linarith) (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcI 0 tn) (hcI tn (tn + δ))
  rw [← hI]
  linarith

end Drift

theorem continuous_quarterReading (u : ℂ) :
    Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => quarterReading u Ψ := by
  unfold quarterReading deviceCoherence
  refine Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun p _ => ?_))
  exact (continuous_star.comp (continuous_apply (p, 0))).mul (continuous_apply (p, 1))

/-! ### The half-ticks of the clock at rest, in the radar arena -/

section Rest

variable (hL : 10 ^ 19 ≤ L)
include hL

omit [NeZero L] hL in
/-- `A`'s clock rate in the radar arena's notation. -/
theorem rest_rate_radar :
    levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
      = 1 / 10 ^ 11 :=
  twin_rest_rate (L := L)

/-- What a half-tick of `A`'s clock needs: its coherence is at least `κ > 0`, and its splitting
coherence drifts from the exact turn by at most `(1 + R|s|)` times the sharp drift. -/
theorem rest_half_facts :
    0 < (1 - ((3 + 1 / 10 ^ 11 - 3) / 3 : ℝ) ^ 2) / 2
    ∧ (1 - ((3 + 1 / 10 ^ 11 - 3) / 3 : ℝ) ^ 2) / 2 ≤ ‖deviceCoherence (restObserver (L := L) 0)‖
    ∧ ∀ s, ‖splitCoherence (relayHop L) 3 (3 + 1 / 10 ^ 11)
          (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0)
        - ((levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
            * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) : ℝ) : ℂ)
          * (exp (I * (((-levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1
              (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) : ℝ) : ℂ)
              * s)) * deviceCoherence (restObserver (L := L) 0))‖
        ≤ (1 + levelClockRate 3 (3 + 1 / 10 ^ 11) (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
            * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) * |s|)
          * deviceDrift 1 3 (3 + 1 / 10 ^ 11) (1 / 10 ^ 7) 0 := by
  have hf := deviceTick_facts (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0)
    (W := Finset.Ico (-1000000 : ℤ) (-1000000 + (2000000 : ℕ))) (lo := -1000000) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by positivity) (by simp) (by positivity)
    (rest_win hL) rest_spread twinAmp (twin_norm hL _)
  exact ⟨hf.1, hf.2.1, fun s => splitCoherence_shift_sharp (L := L) (c := 1) one_pos
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 3 + 1 / 10 ^ 11) (by positivity)
    (noWrap_distinct_of_window (rest_win hL)).2 rest_spread twinAmp (twin_norm hL _) 0 s⟩

omit hL in
/-- The half register along the radar arena's orbit: the tick register minus the quarter reading's
change is the integral of the weight against the opposite mark. -/
theorem half_reading_orbit (t : ℝ) :
    (radarEvolve (L := L) 0 t (radarPrep L)).2 1
        - quarterReading (tickMark (restObserver (L := L) 0))
          (devA (radarEvolve (L := L) 0 t (radarPrep L)).1.1)
        + quarterReading (tickMark (restObserver (L := L) 0)) (restObserver (L := L) 0)
      = ∫ s in (0 : ℝ)..t, rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11)
          (-tickMark (restObserver (L := L) 0))
          (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0) := by
  set u := tickMark (restObserver (L := L) 0)
  have hprop : ∀ s, restObserver (L := L) s
      = deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0 := fun s =>
    (deviceProp_devicePacket _ _ _ _ _ s).symm
  have hI : ∫ s in (0 : ℝ)..t, radarWeight 1 (relayFlow s (relayPrep L))
      = ∫ s in (0 : ℝ)..t, rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) u
        (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0) :=
    intervalIntegral.integral_congr fun s _ => by
      rw [radarWeight_one]
      show rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) u (devA (relayFlow s (relayPrep L)).1) = _
      rw [devA_relayFlow, hprop s]
  have hD : devA (radarEvolve (L := L) 0 t (radarPrep L)).1.1
      = deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) t *ᵥ restObserver 0 := by
    rw [radarEvolve_prep_fst, devA_relayFlow, hprop t]
  rw [radarEvolve_prep_snd, hI, hD]
  have hc1 : Continuous fun s => rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) u
      (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0) :=
    continuous_weight_deviceProp _ _ _ (continuous_rateWeight _ _ _ _) _
  have hc2 : Continuous fun s => (star u * splitCoherence (relayHop L) 3 (3 + 1 / 10 ^ 11)
      (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0)).re :=
    Complex.continuous_re.comp (continuous_const.mul
      ((continuous_splitCoherence _ _ _).comp
        ((continuous_deviceProp_mulVec (L := L) _ _ _).comp
          (continuous_const.prodMk continuous_id))))
  rw [intervalIntegral.integral_congr (g := fun s =>
      rateWeight (relayHop L) 3 (3 + 1 / 10 ^ 11) u
        (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0)
      - (star u * splitCoherence (relayHop L) 3 (3 + 1 / 10 ^ 11)
        (deviceProp (L := L) (relayHop L) 3 (3 + 1 / 10 ^ 11) s *ᵥ restObserver 0)).re)
      fun s _ => rateWeight_neg _ _ _ _ _,
    intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t),
    integral_rate_eq]
  ring

/-- **Half-tick `n` of `A`'s clock in the radar arena** (`1 ≤ n ≤ 130`): its register — the tick
register minus the quarter reading's change — reaches `(2n − 1)|C₀|` within `10¹¹` of
`π(2n − 1)/R`. -/
noncomputable def restHalfTickRadar (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (RadarArena L) ℕ L where
  evolve := radarEvolve
  evolve_self := radarEvolve_self
  evolve_comp := radarEvolve_comp
  measurable_evolve := measurable_radarEvolve
  readout := fun y => if (2 * n - 1) * ‖deviceCoherence (restObserver (L := L) 0)‖
      ≤ y.2 1 - quarterReading (tickMark (restObserver (L := L) 0)) (devA y.1.1)
        + quarterReading (tickMark (restObserver (L := L) 0)) (restObserver (L := L) 0)
      then 1 else 0
  measurable_readout := by
    refine Measurable.ite (measurableSet_le measurable_const ?_) measurable_const measurable_const
    refine Continuous.measurable ?_
    exact (((continuous_apply 1).comp continuous_snd).sub
      ((continuous_quarterReading _).comp (continuous_devA.comp
        (continuous_fst.comp continuous_fst)))).add continuous_const
  ready := {y | y.2 1 = 0}
  measurableSet_ready := measurableSet_eq_fun ((measurable_pi_apply 1).comp measurable_snd)
    measurable_const
  prep := radarPrep L
  prep_mem := rfl
  site := Finset.univ
  start := 0
  value := 1
  writeStart := max 0 (Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
    (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
    - 10 ^ 11)
  writeEnd := Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
    (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
    + 10 ^ 11
  window := w
  isWrite :=
    have hf := rest_half_facts hL
    have hR := rest_rate_radar (L := L)
    have hC : deviceCoherence (restObserver (L := L) 0) ≠ 0 :=
      norm_pos_iff.1 (hf.1.trans_le hf.2.1)
    have hRpos : 0 < levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
        * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) := by
      rw [hR]; norm_num
    have hδR : (10 ^ 11 : ℝ) ≤ 1 / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
        * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) := by
      rw [hR]; norm_num
    have hm : deviceDrift 1 3 (3 + 1 / 10 ^ 11) (1 / 10 ^ 7) 0
        * ((Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
            (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
            + 10 ^ 11) ^ 2
          + 2 * (Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
            (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
            + 10 ^ 11) / levelClockRate 3 (3 + 1 / 10 ^ 11)
            (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
              * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)))
        < ‖deviceCoherence (restObserver (L := L) 0)‖ * 10 ^ 11 := by
      rw [hR]
      have hπ2 : Real.pi < 63 / 20 := by
        have := Real.pi_lt_d2
        norm_num at this ⊢
        linarith
      have hn' : (n : ℝ) ≤ 130 := by exact_mod_cast hn
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hx0 : 0 ≤ Real.pi * (2 * n - 1) / (1 / 10 ^ 11) + 10 ^ 11 := by
        have : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
        positivity
      have hx1 : Real.pi * (2 * n - 1) / (1 / 10 ^ 11) + 10 ^ 11 ≤ 10 ^ 14 := by
        rw [show Real.pi * (2 * n - 1) / (1 / 10 ^ 11) = Real.pi * (2 * n - 1) * 10 ^ 11 by
          field_simp]
        have : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
        nlinarith [mul_le_mul hπ2.le (by linarith : 2 * (n : ℝ) - 1 ≤ 259) this
          (by norm_num : (0 : ℝ) ≤ 63 / 20), Real.pi_pos]
      have hsq := pow_le_pow_left₀ hx0 hx1 2
      have hd : deviceDrift 1 3 (3 + 1 / 10 ^ 11) (1 / 10 ^ 7) 0 = 1 / (36 * 10 ^ 25) := by
        simp only [deviceDrift, abs_zero]
        norm_num
      rw [hd]
      calc 1 / (36 * 10 ^ 25) * ((Real.pi * (2 * n - 1) / (1 / 10 ^ 11) + 10 ^ 11) ^ 2
            + 2 * (Real.pi * (2 * n - 1) / (1 / 10 ^ 11) + 10 ^ 11) / (1 / 10 ^ 11))
          ≤ 1 / (36 * 10 ^ 25) * ((10 ^ 14) ^ 2 + 2 * 10 ^ 14 / (1 / 10 ^ 11)) := by gcongr
        _ < (1 - ((3 + 1 / 10 ^ 11 - 3) / 3 : ℝ) ^ 2) / 2 * 10 ^ 11 := by norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right hf.2.1 (by norm_num)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have htn : 0 ≤ Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)
          * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0)) := by
      have : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
      positivity
    { start_le := le_max_left _ _
      interval := max_le (by positivity) (by linarith)
      window_nonneg := hw
      before := fun t ht0 ht => by
        rw [half_reading_orbit (L := L) t]
        have htl : t < Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
            (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
            - 10 ^ 11 := by
          rcases lt_max_iff.1 ht with h | h
          · linarith
          · exact h
        have hlt := half_register_lt (relayHop L) 3 (3 + 1 / 10 ^ 11) hRpos hC hf.2.2 n
          (by norm_num : (0 : ℝ) < 10 ^ 11) hδR hm hn1 ht0 htl
        split_ifs with h
        · exact absurd h (not_le.2 hlt)
        · decide
      holds := fun t ht _ => by
        rw [half_reading_orbit (L := L) t]
        have hle := half_register_ge (relayHop L) 3 (3 + 1 / 10 ^ 11) hRpos hC hf.2.2 n
          (by norm_num : (0 : ℝ) < 10 ^ 11) hδR hm hn1 ht
        split_ifs
        rfl }

/-- Half-tick `n`'s write: within `10¹¹` of `(n − 1/2) · 2π·10¹¹`. -/
theorem restHalfTickRadar_fields (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    (restHalfTickRadar (L := L) hL n hn1 hn hw).evolve = radarEvolve
    ∧ (restHalfTickRadar (L := L) hL n hn1 hn hw).prep = radarPrep L
    ∧ (restHalfTickRadar (L := L) hL n hn1 hn hw).writeStart
      = max 0 ((2 * n - 1) * (Real.pi * 10 ^ 11) - 10 ^ 11)
    ∧ (restHalfTickRadar (L := L) hL n hn1 hn hw).writeEnd
      = (2 * n - 1) * (Real.pi * 10 ^ 11) + 10 ^ 11 := by
  have e : Real.pi * (2 * (n : ℝ) - 1) / (1 / 10 ^ 11) = (2 * n - 1) * (Real.pi * 10 ^ 11) := by
    field_simp
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show max 0 (Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
        - 10 ^ 11) = _
    rw [rest_rate_radar (L := L), e]
  · show Real.pi * (2 * n - 1) / levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
        + 10 ^ 11 = _
    rw [rest_rate_radar (L := L), e]

end Rest

end CSD.RecordLayer

end
