/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarFamily
public import CsdLean4.RecordLayer.UnifiedWallRadar

/-!
# The family's run: five counts and the Lorentz statement with a vanishing error

**Category:** 7-SigmaLayer (the record layer). BACKLOG #426 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 8 and 10 of the research
delivery plan of 2026-11-16, on the fibres where the five profiles vanish. No new assumption
beyond UA-18.

`tri_wall_radar_lorentz` (#423) is conditional on seven angle conditions and on sizes, and
its error is a long expression. This module discharges every one of those hypotheses for the
family of #425 and bounds the error.

* `radar_error_le` — the error of #423 is at most `150 K/X` when its pieces are bounded
  (real arithmetic);
* `radar_error_pieces` — the bounds on the pieces from the bounds on the rates (real
  arithmetic);
* `radarRateB_mul_wallK` — the first level's angular rate times `K` is `vRel 1 1 (1/2)`;
* ★★★ `radar_family_lorentz` — for every `k ≥ 100` and every even ring large enough: the five
  pointers of the walled chain's run have counts in the five reading windows, and the counts
  satisfy the Lorentz statement for `v = vRel 1 1 (1/2)` within `150 K/k`, about `21/k` of the
  length of the run.

## Exact scope

* **The fibres where the five profiles vanish.** Every pointer starts at `(1/12, 0)`, where
  the carriers move freely. An open set of starts (R7, Task 9) is not in this module, and
  without it UO-16 is not met.
* **No hypothesis about angles, sizes or histories is left**: the hypotheses are `k ≥ 100`,
  the size of the ring and that its number of sites is even.
* **The error is `150 K/k` in the flow time, for both components.** The comparison with the
  length of the run (`≈ 7K`) and the number of ticks (`≈ 1.1 k`) is arithmetic in the
  docstring, not a statement.
* **The velocity is one number**, `vRel 1 1 (1/2) ∈ [2/5, 9/20]`; the distance is the whole
  chain; the emission is a coincidence with the moving clock's mirror image (#424).
* **Strengths exist; they are not chosen.** The labelling of the basis is arbitrary.
* **Counts of displacements of pointers of the five-pointer flow**, in windows of flow time.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-181, UD-193, UD-194, UD-195, UD-196);
`RecordLayer/UnifiedWallRadar.lean` (#423: `tri_wall_radar_lorentz`, `WallRadarLorentz`);
`RecordLayer/UnifiedRadarFamily.lean` (#425: `radar_family_rates`,
`radar_family_gate_conditions`, `radar_family_all_conditions`);
`RecordLayer/UnifiedWallIntervals.lean` (#424: `radar_gate_intervals`, `radar_gate_times`);
`RecordLayer/UnifiedRadarSkeleton.lean` (#402: `gatedErr`, `awayErr`);
`RecordLayer/UnifiedRadarTimes.lean` (#412: `radarTR`, `radarTRet`, `radarTM`).
-/

@[expose] public section

noncomputable section

open CSD.CV

namespace CSD.RecordLayer

/-- **The error of #423 from bounds on its pieces** (real arithmetic). With `Δ K = X ≥ 100`,
`K ≥ 10⁷ X²`, the rest rate `Δ`, strengths at most `Δ/5`, closing gaps of a few `K/(10⁵ X)`,
a rate tolerance `κ` with `κ · 8K ≤ 8X + 1`, and the five gate times within `(1/5) K/X`,
`(16/5) K/X` and `(3/2) K/X` of the kinematic times: both components of the error are at
most `150 K/X`. -/
theorem radar_error_le {K X Δ RA RB κ v s gA gB tE tb t3 t4 tM tbM tR tbR TR TRet TM : ℝ}
    (hK : 0 < K) (hX : 100 ≤ X) (hKX : 10 ^ 7 * X ^ 2 ≤ K) (hΔ : Δ * K = X) (hRA : RA = Δ)
    (hRB : RB ≤ Δ) (hgA0 : 0 ≤ gA) (hgA : gA ≤ Δ / 5) (hgB0 : 0 ≤ gB)
    (hgB : gB ≤ Δ / 5) (hκ0 : 0 ≤ κ) (hκ : κ * (8 * K) ≤ 8 * X + 1)
    (hv : v ≤ 9 / 20) (hs : 89 / 100 ≤ s) (hE0 : 0 ≤ tE) (hEb : tE ≤ tb) (h34 : t3 ≤ t4)
    (hMb : tM ≤ tbM) (hRb : tR ≤ tbR) (h38 : t3 ≤ 8 * K) (hM8 : tM ≤ 8 * K)
    (e1 : tb ≤ 12 * (K / (10 ^ 5 * X))) (e2 : t4 - t3 ≤ 12 * (K / (10 ^ 5 * X)))
    (e3 : tbM - tM ≤ 18 * (K / (10 ^ 5 * X))) (e4 : tbR - tR ≤ 6 * (K / (10 ^ 5 * X)))
    (e5 : tE ≤ K / (10 ^ 5 * X) / 2) (e6 : |t3 - TRet| ≤ 1 / 5 * (K / X))
    (e7 : |tM - TM| ≤ 16 / 5 * (K / X)) (e8 : |tR - TR| ≤ 3 / 2 * (K / X)) :
    ((gatedErr (2 * gB) tE tb / RA + κ * tE + |tE - 0|)
          + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4 + RB * (tb - tE)) / RA
              + κ * t3 + |t3 - TRet|)) / 2
        + (gatedErr (2 * gB) tM tbM / RA + κ * tM + |tM - TM|)
        + ((gatedErr (2 * gA) tR tbR / RA + |tR - TR|)
            + (gatedErr (2 * gA) tM tbM / RA + |tM - TM|)) / s
      ≤ 150 * (K / X)
    ∧ ((gatedErr (2 * gB) tE tb / RA + κ * tE + |tE - 0|)
          + ((gatedErr (2 * gB) tE tb + awayErr (2 * gB) tE tb t3 t4 + RB * (tb - tE)) / RA
              + κ * t3 + |t3 - TRet|)) / 2
        + v * ((gatedErr (2 * gA) tR tbR / RA + |tR - TR|)
            + (gatedErr (2 * gA) tM tbM / RA + |tM - TM|)) / s
      ≤ 150 * (K / X) := by
  rw [hRA]
  have hX0 : 0 < X := by linarith only [hX]
  have hπ := Real.pi_gt_three
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hΔ0 : 0 < Δ := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, hΔ, hX0]
  set U : ℝ := K / X with hU
  have hU0 : 0 < U := div_pos hK hX0
  have hΔU : Δ * U = 1 := by
    rw [hU, ← mul_div_assoc, hΔ, div_self hX0.ne']
  -- dividing by the rest rate
  have hdiv : ∀ x c : ℝ, x ≤ c → x / Δ ≤ c * U := by
    intro x c hxc
    have e : x / Δ = x * U := by
      rw [div_eq_iff hΔ0.ne', mul_assoc, mul_comm U, hΔU, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_right hxc hU0.le
  -- the closing unit
  have hD : K / (10 ^ 5 * X) = U / 10 ^ 5 := by
    rw [hU]
    field_simp
  rw [hD] at e1 e2 e3 e4 e5
  have hUbig : 10 ^ 7 * X ≤ U := by
    rw [hU, le_div_iff₀ hX0]
    nlinarith only [hKX]
  have hU9 : 10 ^ 9 ≤ U := by linarith only [hUbig, hX]
  -- a strength times a closing gap
  have hg : ∀ g x c : ℝ, 0 ≤ g → g ≤ Δ / 5 → 0 ≤ x → 0 ≤ c → x ≤ c * (U / 10 ^ 5) →
      0 ≤ g * x ∧ g * x ≤ c / (5 * 10 ^ 5) := by
    intro g x c hg0 hg5 hx0 hc0 hxc
    refine ⟨mul_nonneg hg0 hx0, ?_⟩
    calc g * x ≤ Δ / 5 * (c * (U / 10 ^ 5)) :=
          mul_le_mul hg5 hxc hx0 (by linarith only [hΔ0])
      _ = c * (Δ * U) / (5 * 10 ^ 5) := by ring
      _ = c / (5 * 10 ^ 5) := by rw [hΔU, mul_one]
  have hb0 : 0 ≤ tb - tE := sub_nonneg.2 hEb
  obtain ⟨m1, m1'⟩ := hg gB (tb - tE) 12 hgB0 hgB hb0 (by norm_num)
    (by linarith only [e1, hE0])
  obtain ⟨m2, m2'⟩ := hg gB (t4 - t3) 12 hgB0 hgB (sub_nonneg.2 h34) (by norm_num) e2
  obtain ⟨m3, m3'⟩ := hg gB (tbM - tM) 18 hgB0 hgB (sub_nonneg.2 hMb) (by norm_num) e3
  obtain ⟨m4, m4'⟩ := hg gA (tbR - tR) 6 hgA0 hgA (sub_nonneg.2 hRb) (by norm_num) e4
  obtain ⟨m5, m5'⟩ := hg gA (tbM - tM) 18 hgA0 hgA (sub_nonneg.2 hMb) (by norm_num) e3
  have m6 : RB * (tb - tE) ≤ 1 / 100 := by
    calc RB * (tb - tE) ≤ Δ * (12 * (U / 10 ^ 5)) :=
          mul_le_mul hRB (by linarith only [e1, hE0]) hb0 hΔ0.le
      _ = 12 * (Δ * U) / 10 ^ 5 := by ring
      _ ≤ 1 / 100 := by rw [hΔU]; norm_num
  -- the tick terms
  have G : ∀ y : ℝ, 0 ≤ y → y ≤ 18 / (5 * 10 ^ 5) →
      0 ≤ 2 * Real.pi * (3 * 2 * y + 7 / 2)
        ∧ 2 * Real.pi * (3 * 2 * y + 7 / 2) ≤ 2212 / 100 := by
    intro y hy0 hy
    constructor
    · have : 0 ≤ 3 * 2 * y + 7 / 2 := by linarith only [hy0]
      exact mul_nonneg (by linarith only [hπ]) this
    · nlinarith only [hy0, hy, hπu, hπ, mul_le_mul_of_nonneg_left hy Real.pi_pos.le,
        mul_nonneg Real.pi_pos.le hy0]
  have GE := G (gB * (tb - tE)) m1 (by linarith only [m1'])
  have GM := G (gB * (tbM - tM)) m3 m3'
  have GR := G (gA * (tbR - tR)) m4 (by linarith only [m4'])
  have Gm := G (gA * (tbM - tM)) m5 m5'
  have AW : 2 * Real.pi * (3 * 2 * (gB * (tb - tE) + gB * (t4 - t3)) + 7) ≤ 443 / 10 := by
    have h0 : 0 ≤ gB * (tb - tE) + gB * (t4 - t3) := add_nonneg m1 m2
    have h1 : gB * (tb - tE) + gB * (t4 - t3) ≤ 24 / (5 * 10 ^ 5) := by
      linarith only [m1', m2']
    nlinarith only [h0, h1, hπu, hπ, mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
      mul_nonneg Real.pi_pos.le h0]
  -- the rate tolerance
  have hκt : ∀ t, t ≤ 8 * K → κ * t ≤ 1 / 100 * U := by
    intro t ht
    have h1 : κ * t ≤ 8 * X + 1 := (mul_le_mul_of_nonneg_left ht hκ0).trans hκ
    nlinarith only [h1, hUbig, hX]
  have k1 := hκt tE (by
    have : U / 10 ^ 5 / 2 ≤ 8 * K := by
      rw [hU]
      have : K / X ≤ K := by
        rw [div_le_iff₀ hX0]
        nlinarith only [hK, hX]
      linarith only [this, hK]
    linarith only [e5, this])
  have k2 := hκt t3 h38
  have k3 := hκt tM hM8
  have hτ1 : |tE - 0| ≤ 1 / 100 * U := by
    rw [sub_zero, abs_of_nonneg hE0]
    linarith only [e5, hU0]
  -- the five blocks
  have eG : ∀ g ta tb' : ℝ, gatedErr (2 * g) ta tb'
      = 2 * Real.pi * (3 * 2 * (g * (tb' - ta)) + 7 / 2) := by
    intro g ta tb'
    rw [gatedErr]
    ring
  have eA : awayErr (2 * gB) tE tb t3 t4
      = 2 * Real.pi * (3 * 2 * (gB * (tb - tE) + gB * (t4 - t3)) + 7) := by
    rw [awayErr]
    ring
  rw [eG gB tE tb, eG gB tM tbM, eG gA tR tbR, eG gA tM tbM, eA]
  have d1 := hdiv _ _ GE.2
  have d2 := hdiv _ _ (by linarith only [GE.2, AW, m6] :
    2 * Real.pi * (3 * 2 * (gB * (tb - tE)) + 7 / 2)
        + 2 * Real.pi * (3 * 2 * (gB * (tb - tE) + gB * (t4 - t3)) + 7) + RB * (tb - tE)
      ≤ 2212 / 100 + 443 / 10 + 1 / 100)
  have d3 := hdiv _ _ GM.2
  have d4 := hdiv _ _ GR.2
  have d5 := hdiv _ _ Gm.2
  have d4' : 0 ≤ 2 * Real.pi * (3 * 2 * (gA * (tbR - tR)) + 7 / 2) / Δ :=
    div_nonneg GR.1 hΔ0.le
  have d5' : 0 ≤ 2 * Real.pi * (3 * 2 * (gA * (tbM - tM)) + 7 / 2) / Δ :=
    div_nonneg Gm.1 hΔ0.le
  have hs0 : 0 < s := by linarith only [hs]
  set Y : ℝ := (2 * Real.pi * (3 * 2 * (gA * (tbR - tR)) + 7 / 2) / Δ + |tR - TR|)
      + (2 * Real.pi * (3 * 2 * (gA * (tbM - tM)) + 7 / 2) / Δ + |tM - TM|) with hY
  have hY0 : 0 ≤ Y := by
    linarith only [hY, d4', d5', abs_nonneg (tM - TM), abs_nonneg (tR - TR)]
  have hY1 : Y ≤ 4894 / 100 * U := by linarith only [hY, d4, d5, e7, e8]
  have hYs : Y / s ≤ 55 * U := by
    rw [div_le_iff₀ hs0]
    nlinarith only [hY1, hU0,
      mul_le_mul_of_nonneg_left hs (by linarith only [hU0] : 0 ≤ 55 * U)]
  have hvY : v * Y / s ≤ 55 * U := by
    have h1 : v * Y ≤ Y := by nlinarith only [hY0, hv]
    have h2 : v * Y / s ≤ Y / s := (div_le_div_iff_of_pos_right hs0).2 h1
    exact h2.trans hYs
  constructor
  · linarith only [d1, d2, d3, k1, k2, k3, hτ1, e6, e7, hYs, hU0]
  · linarith only [d1, d2, k1, k2, hτ1, e6, hvY, hU0]

/-- **The pieces of the error from bounds on the rates** (real arithmetic). Rates and start as
in `radar_six_of_bounds`, `v = b₁ K` the velocity of the first level, `δ = 1/(10⁵ X)`. For the
gate times of `radar_gate_times`: the closing gaps are a few `K/(10⁵ X)`, and the return, the
meeting and the relay are within `(1/5) K/X`, `(16/5) K/X` and `(3/2) K/X` of the kinematic
times `2πK/(1 + v)`, `πK/v` and `πK`. -/
theorem radar_error_pieces {K X a b₁ b₂ τ Δ v δ : ℝ} (hK : 0 < K) (hX : 100 ≤ X)
    (hKX : 10 ^ 7 * X ^ 2 ≤ K) (hΔ : Δ * K = X) (ha1 : (1 - 2 / X ^ 2) / K ≤ a)
    (ha2 : a ≤ 1 / K) (hb1 : 2 / 5 / K ≤ b₁) (hb2 : b₁ ≤ 9 / 20 / K)
    (hb3 : b₁ - Δ / K ≤ b₂) (hb4 : b₂ ≤ b₁) (hτ0 : 0 ≤ τ) (hτ2 : τ * Δ ≤ Real.pi)
    (hv : b₁ * K = v) (hδ : δ = 1 / (10 ^ 5 * X)) :
    6 * δ / (a - b₁) ≤ 12 * (K / (10 ^ 5 * X))
      ∧ (2 * Real.pi - δ) / (a + b₂) - (2 * Real.pi - 6 * δ) / (a + b₁)
          ≤ 12 * (K / (10 ^ 5 * X))
      ∧ τ + (Real.pi - δ) / b₂ - (τ + (Real.pi - 6 * δ) / b₁) ≤ 18 * (K / (10 ^ 5 * X))
      ∧ (Real.pi - δ - b₁ * τ) / a - (Real.pi - 6 * δ - b₁ * τ) / a
          ≤ 6 * (K / (10 ^ 5 * X))
      ∧ δ / (2 * (a + b₁)) ≤ K / (10 ^ 5 * X) / 2
      ∧ |(2 * Real.pi - 6 * δ) / (a + b₁) - 2 * (Real.pi * K) / (1 + v)| ≤ 1 / 5 * (K / X)
      ∧ |τ + (Real.pi - 6 * δ) / b₁ - Real.pi * K / v| ≤ 16 / 5 * (K / X)
      ∧ |(Real.pi - 6 * δ - b₁ * τ) / a - Real.pi * K| ≤ 3 / 2 * (K / X) := by
  have hX0 : 0 < X := by linarith only [hX]
  have hπ := Real.pi_gt_three
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  set r : ℝ := 1 / X with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 100 := by
    rw [hr, div_le_div_iff₀ hX0 (by norm_num)]
    linarith only [hX]
  have hrX : r * X = 1 := by
    rw [hr]
    field_simp
  have hπr : Real.pi * r ≤ 3.15 * r := mul_le_mul_of_nonneg_right hπu.le hr0.le
  -- `2/X² ≤ r/50`
  have h2X : 2 / X ^ 2 ≤ r / 50 := by
    have e : 2 / X ^ 2 = 2 * r * r := by
      rw [hr]
      field_simp
    rw [e]
    nlinarith only [hr1, hr0]
  -- everything times `K`
  have hA1 : 1 - 2 / X ^ 2 ≤ a * K := (div_le_iff₀ hK).1 ha1
  have hA2 : a * K ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha2 hK.le
    rwa [div_mul_cancel₀ _ hK.ne'] at this
  have hB1 : 2 / 5 ≤ b₁ * K := (div_le_iff₀ hK).1 hb1
  have hB2 : b₁ * K ≤ 9 / 20 := by
    have := mul_le_mul_of_nonneg_right hb2 hK.le
    rwa [div_mul_cancel₀ _ hK.ne'] at this
  have hB3 : b₁ * K - Δ ≤ b₂ * K := by
    have := mul_le_mul_of_nonneg_right hb3 hK.le
    rwa [sub_mul, div_mul_cancel₀ _ hK.ne'] at this
  have hΔ0 : 0 < Δ := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, hΔ, hX0]
  have hΔs : Δ * (10 ^ 7 * X) ≤ 1 := by
    have h1 : Δ * (10 ^ 7 * X ^ 2) ≤ Δ * K := mul_le_mul_of_nonneg_left hKX hΔ0.le
    rw [hΔ] at h1
    have h2 : Δ * (10 ^ 7 * X) * X ≤ 1 * X := by nlinarith only [h1]
    exact le_of_mul_le_mul_right h2 hX0
  have hΔ9 : Δ ≤ 1 / 10 ^ 9 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith only [hΔs, mul_le_mul_of_nonneg_left hX hΔ0.le]
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le (by positivity) hb1
  have ha0 : 0 < a := lt_of_lt_of_le (div_pos (by linarith only [h2X, hr1]) hK) ha1
  have hb₂K : 0 < b₂ * K := by linarith only [hB3, hB1, hΔ9]
  have hb₂0 : 0 < b₂ := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, hb₂K]
  have hab : 0 < a - b₁ := by
    have : 0 < (a - b₁) * K := by linarith only [hA1, hB2, h2X, hr1]
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, this]
  have hp1 : 0 < a + b₁ := by linarith only [ha0, hb₁0]
  have hp2 : 0 < a + b₂ := by linarith only [ha0, hb₂0]
  have hsp0 : 0 ≤ b₁ - b₂ := sub_nonneg.2 hb4
  have hsp : (b₁ - b₂) * K ≤ Δ := by linarith only [hB3]
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδr : δ = r / 10 ^ 5 := by
    rw [hδ, hr]
    field_simp
  have hD : K / (10 ^ 5 * X) = δ * K := by
    rw [hδ]
    field_simp
  have hU : K / X = K * r := by
    rw [hr]
    ring
  rw [hD, hU]
  have hKp : 1 ≤ (a + b₁) * K := by linarith only [hA1, hB1, h2X, hr1]
  have hKm : 1 / 2 ≤ (a - b₁) * K := by linarith only [hA1, hB2, h2X, hr1]
  have hbτ0 : 0 ≤ b₁ * τ := mul_nonneg hb₁0.le hτ0
  -- `8Δ ≤ δ`
  have h8Δ : 8 * Δ ≤ δ := by
    have h1 : 8 * Δ * X ≤ δ * X := by
      rw [hδr]
      nlinarith only [hΔs, hrX]
    exact le_of_mul_le_mul_right h1 hX0
  -- the start
  have hτK : τ * X ≤ Real.pi * K := by
    rw [← hΔ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hτ2 hK.le
  have hτU : τ ≤ 3.15 * (K * r) := by
    have h1 : τ = τ * X * r := by rw [mul_assoc, mul_comm X, hrX, mul_one]
    rw [h1]
    calc τ * X * r ≤ Real.pi * K * r := mul_le_mul_of_nonneg_right hτK hr0.le
      _ ≤ 3.15 * K * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hπu.le hK.le) hr0.le
      _ = 3.15 * (K * r) := by ring
  have hbτ : b₁ * τ ≤ 9 / 20 * (3.15 * r) := by
    have h1 : b₁ * τ * X ≤ 9 / 20 * Real.pi := by
      have e : b₁ * τ * X = (b₁ * K) * (τ * Δ) := by rw [← hΔ]; ring
      rw [e]
      exact mul_le_mul hB2 hτ2 (mul_nonneg hτ0 hΔ0.le) (by norm_num)
    have h2 : b₁ * τ = b₁ * τ * X * r := by rw [mul_assoc, mul_comm X, hrX, mul_one]
    rw [h2]
    calc b₁ * τ * X * r ≤ 9 / 20 * Real.pi * r := mul_le_mul_of_nonneg_right h1 hr0.le
      _ ≤ 9 / 20 * (3.15 * r) := by linarith only [hπr]
  -- the closing gaps
  have g1 : 6 * δ / (a - b₁) ≤ 12 * (δ * K) := by
    rw [div_le_iff₀ hab]
    nlinarith only [mul_le_mul_of_nonneg_left hKm hδ0.le]
  have g5 : δ / (2 * (a + b₁)) ≤ δ * K / 2 := by
    rw [div_le_iff₀ (by linarith only [hp1])]
    nlinarith only [mul_le_mul_of_nonneg_left hKp hδ0.le]
  have hδKa : 99 / 100 * δ ≤ δ * K * a := by
    have := mul_le_mul_of_nonneg_left hA1 hδ0.le
    nlinarith only [this, h2X, hr1, hδ0]
  have g4 : (Real.pi - δ - b₁ * τ) / a - (Real.pi - 6 * δ - b₁ * τ) / a ≤ 6 * (δ * K) := by
    rw [← sub_div, div_le_iff₀ ha0]
    linarith only [hδKa, hδ0]
  -- the return window against the end of the away interval
  set t3 : ℝ := (2 * Real.pi - 6 * δ) / (a + b₁) with ht3
  have e3 : (a + b₁) * t3 = 2 * Real.pi - 6 * δ := mul_div_cancel₀ _ hp1.ne'
  have hδ7 : δ ≤ 1 / 10 ^ 7 := by rw [hδr]; linarith only [hr1]
  have t30 : 0 ≤ t3 := div_nonneg (by linarith only [hδ7, hπ]) hp1.le
  have t38 : t3 ≤ 8 * K := by
    rw [ht3, div_le_iff₀ hp1]
    nlinarith only [mul_le_mul_of_nonneg_left hKp (by norm_num : (0 : ℝ) ≤ 8), hπu, hδ0]
  have f1 : t3 * (b₁ - b₂) ≤ δ := by
    calc t3 * (b₁ - b₂) ≤ 8 * K * (b₁ - b₂) := mul_le_mul_of_nonneg_right t38 hsp0
      _ = 8 * ((b₁ - b₂) * K) := by ring
      _ ≤ 8 * Δ := by linarith only [hsp]
      _ ≤ δ := h8Δ
  have f3 : 0 ≤ δ * K * b₂ := by positivity
  have g2 : (2 * Real.pi - δ) / (a + b₂) - t3 ≤ 12 * (δ * K) := by
    have : (2 * Real.pi - δ) / (a + b₂) ≤ t3 + 12 * (δ * K) := by
      rw [div_le_iff₀ hp2]
      linarith only [e3, f1, hδKa, f3, hδ0]
    linarith only [this]
  -- the meeting window
  set y1 : ℝ := (Real.pi - 6 * δ) / b₁ with hy1
  have ey : b₁ * y1 = Real.pi - 6 * δ := mul_div_cancel₀ _ hb₁0.ne'
  have y10 : 0 ≤ y1 := div_nonneg (by linarith only [hδ7, hπ]) hb₁0.le
  have y18 : y1 ≤ 8 * K := by
    rw [hy1, div_le_iff₀ hb₁0]
    linarith only [hB1, hπu, hδ0]
  have fy : y1 * (b₁ - b₂) ≤ δ := by
    calc y1 * (b₁ - b₂) ≤ 8 * K * (b₁ - b₂) := mul_le_mul_of_nonneg_right y18 hsp0
      _ = 8 * ((b₁ - b₂) * K) := by ring
      _ ≤ 8 * Δ := by linarith only [hsp]
      _ ≤ δ := h8Δ
  have hδKb : 39 / 100 * δ ≤ δ * K * b₂ := by
    have := mul_le_mul_of_nonneg_left (by linarith only [hB3, hB1, hΔ9] : 39 / 100 ≤ b₂ * K)
      hδ0.le
    linarith only [this]
  have g3 : τ + (Real.pi - δ) / b₂ - (τ + y1) ≤ 18 * (δ * K) := by
    have : (Real.pi - δ) / b₂ ≤ y1 + 18 * (δ * K) := by
      rw [div_le_iff₀ hb₂0]
      linarith only [ey, fy, hδKb, hδ0]
    linarith only [this]
  -- the return against `2πK/(1 + v)`
  have hv0 : 0 < 1 + v := by linarith only [hv, hB1]
  set T : ℝ := 2 * (Real.pi * K) / (1 + v) with hT
  have eT : T * (1 + v) = 2 * (Real.pi * K) := div_mul_cancel₀ _ hv0.ne'
  have ew : T * (a + b₁) * (1 + v) = 2 * Real.pi * (a * K + v) := by
    calc T * (a + b₁) * (1 + v) = T * (1 + v) * (a + b₁) := by ring
      _ = 2 * (Real.pi * K) * (a + b₁) := by rw [eT]
      _ = 2 * Real.pi * (a * K + v) := by rw [← hv]; ring
  have w1 : T * (a + b₁) ≤ 2 * Real.pi := by
    have : T * (a + b₁) * (1 + v) ≤ 2 * Real.pi * (1 + v) := by
      rw [ew]
      nlinarith only [hA2, hπ]
    exact le_of_mul_le_mul_right this hv0
  have w2 : 2 * Real.pi * (a * K) ≤ T * (a + b₁) := by
    have : 2 * Real.pi * (a * K) * (1 + v) ≤ T * (a + b₁) * (1 + v) := by
      rw [ew]
      have h0 : 0 ≤ v * (1 - a * K) := mul_nonneg (by linarith only [hv, hB1])
        (by linarith only [hA2])
      nlinarith only [h0, hπ, mul_nonneg Real.pi_pos.le h0]
    exact le_of_mul_le_mul_right this hv0
  have w3 : 2 * Real.pi - 3.15 * r / 25 ≤ T * (a + b₁) := by
    have h1 : 2 * Real.pi * (1 - 2 / X ^ 2) ≤ 2 * Real.pi * (a * K) :=
      mul_le_mul_of_nonneg_left hA1 (by linarith only [hπ])
    have h2 : Real.pi * (2 / X ^ 2) ≤ Real.pi * (r / 50) :=
      mul_le_mul_of_nonneg_left h2X (by linarith only [hπ])
    linarith only [h1, h2, w2, hπr]
  have cP : r / 5 ≤ 1 / 5 * (K * r) * (a + b₁) := by
    have e : 1 / 5 * (K * r) * (a + b₁) = 1 / 5 * r * ((a + b₁) * K) := by ring
    rw [e]
    nlinarith only [mul_le_mul_of_nonneg_left hKp hr0.le]
  have g6 : |t3 - T| ≤ 1 / 5 * (K * r) := by
    rw [abs_le]
    constructor
    · have : T - 1 / 5 * (K * r) ≤ t3 := by
        rw [ht3, le_div_iff₀ hp1]
        linarith only [w1, cP, hδr, hr0]
      linarith only [this]
    · have : t3 ≤ T + 1 / 5 * (K * r) := by
        rw [ht3, div_le_iff₀ hp1]
        linarith only [w3, cP, hδ0, hr0]
      linarith only [this]
  -- the meeting against `πK/v`
  have eTM : Real.pi * K / v = Real.pi / b₁ := by
    rw [← hv]
    field_simp
  have e7 : τ + y1 - Real.pi * K / v = τ - 6 * δ / b₁ := by
    rw [eTM, hy1, sub_div]
    ring
  have h6b : 6 * δ / b₁ ≤ 15 * (δ * K) := by
    rw [div_le_iff₀ hb₁0]
    nlinarith only [mul_le_mul_of_nonneg_left hB1 hδ0.le]
  have h6b0 : 0 ≤ 6 * δ / b₁ := by positivity
  have hδKr : δ * K = K * r / 10 ^ 5 := by rw [hδr]; ring
  have hKr0 : 0 < K * r := mul_pos hK hr0
  have g7 : |τ + y1 - Real.pi * K / v| ≤ 16 / 5 * (K * r) := by
    rw [e7, abs_le]
    constructor
    · linarith only [h6b, hδKr, hτ0, hKr0]
    · linarith only [h6b0, hτU, hKr0]
  -- the relay against `πK`
  have hKra : 9998 / 10000 * r ≤ K * r * a := by
    have e : K * r * a = r * (a * K) := by ring
    rw [e]
    have h1 : (9998 : ℝ) / 10000 ≤ a * K := by linarith only [hA1, h2X, hr1]
    nlinarith only [mul_le_mul_of_nonneg_left h1 hr0.le]
  have hKra' : K * r * a ≤ r := by
    have e : K * r * a = r * (a * K) := by ring
    rw [e]
    nlinarith only [mul_le_mul_of_nonneg_left hA2 hr0.le]
  have hπa : Real.pi - 3.15 * r / 50 ≤ Real.pi * K * a := by
    have h1 : Real.pi * (1 - 2 / X ^ 2) ≤ Real.pi * (a * K) :=
      mul_le_mul_of_nonneg_left hA1 (by linarith only [hπ])
    have h2 : Real.pi * (2 / X ^ 2) ≤ Real.pi * (r / 50) :=
      mul_le_mul_of_nonneg_left h2X (by linarith only [hπ])
    linarith only [h1, h2, hπr]
  have hπa' : Real.pi * K * a ≤ Real.pi := by
    have := mul_le_mul_of_nonneg_left hA2 (by linarith only [hπ] : 0 ≤ Real.pi)
    linarith only [this]
  have g8 : |(Real.pi - 6 * δ - b₁ * τ) / a - Real.pi * K| ≤ 3 / 2 * (K * r) := by
    rw [abs_le]
    constructor
    · have : Real.pi * K - 3 / 2 * (K * r) ≤ (Real.pi - 6 * δ - b₁ * τ) / a := by
        rw [le_div_iff₀ ha0]
        linarith only [hπa', hKra, hbτ, hδr, hr0]
      linarith only [this]
    · have : (Real.pi - 6 * δ - b₁ * τ) / a ≤ Real.pi * K + 3 / 2 * (K * r) := by
        rw [div_le_iff₀ ha0]
        linarith only [hπa, hKra, hbτ0, hδ0, hr0]
      linarith only [this]
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩

/-- The first level's angular rate times `K` is the velocity `vRel 1 1 (1/2)`. -/
theorem radarRateB_mul_wallK {k : ℕ} (hk : 1 ≤ k) : radarRateB k * wallK k = vRel 1 1 (1 / 2) := by
  have hN1 : (1 : ℝ) ≤ wallN k := by
    have : 1 ≤ wallN k := by
      rw [wallN]
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hK0 : 0 < wallK k := by rw [wallK]; nlinarith only [hN1]
  have hKc : ((1200 * wallN k * wallN k : ℕ) : ℝ) = wallK k := by
    rw [wallK]
    push_cast
    ring
  have hπ := Real.pi_pos
  rw [radarRateB, ringLen, hKc, one_mul]
  field_simp

section Run

open CSD.LF4 Projectivization

/-- ★★★ **The family's run: five counts and the Lorentz statement, with an error that
vanishes against the length of the run.** For every `k ≥ 100` and every ring with an even
number `M + 1 = 2H` of sites, `M ≥ 210000 N³`, `N = 10¹⁶ k⁴`: take the light messenger's wall
state (rest energy `1/k`, the flat window at momentum `1/2`, started at the mirror image of
the moving clock's place), the clock at rest translated to the far wall, and the moving clock
(gap `Δ = k/K`), both clocks prepared a quarter turn early, and the five wall gates of width
`3δ`, `δ = 1/(10⁵ k)`. Then for some strengths `0 < g_A ≤ R₀/5` and `0 < g_B ≤ R_B/5`: at
every choice of flow times in the five reading windows (the gate times of #424 for the
family's rates) the five pointers of `wallRun` have counts, and the counts satisfy both
components of the Lorentz statement of #402 for the velocity `v = vRel 1 1 (1/2)` within
`150 K/k`.

The run lasts about `πK/v ≈ 7K` in the flow time and holds about `1.1 k` ticks of `2πK/k`, so
the error is about `21/k` of the run: it tends to zero along the family, while the distance
(the whole chain) and the velocity do not change. -/
theorem radar_family_lorentz {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ (hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
          (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
          (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0)
      (gA gB : ℝ)
      (hΨA : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (wallWindow (wallN k) ∪ negWin (wallWindow (wallN k)))
        (oddExt (wallWindow (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)))) ≠ 0)
      (hΨB : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (flatWindow (wallN k) (wallN k) ∪ negWin (flatWindow (wallN k) (wallN k)))
        (oddExt (flatWindow (wallN k) (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))) ≠ 0),
      0 < gA ∧ gA ≤ ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) / 5
      ∧ 0 < gB ∧ gB ≤ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5
      ∧ WallRadarLorentz M
          (fun e => wallRun (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
            gA gB e (chainRay _ hψ)
            (deviceRay (deviceShift (H : ZMod (M + 1)) _)
              (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB))
          (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) (vRel 1 1 (1 / 2))
          (famTb k) (famT3 k) (famT4 k) (famT5 k) (famTbM k M) (famTcM k M) (famTbR k M)
          (famTcR k M) (150 * (wallK k / k)) (150 * (wallK k / k)) := by
  have hk1 : 1 ≤ k := by omega
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 : (0 : ℝ) < k := by linarith only [hX]
  have hπ := Real.pi_gt_three
  obtain ⟨hK0, hKX, hΔK, ha1, ha2, hb1, hb2, hb3, hb4, hR1, hR2⟩ := radar_family_rates hk M
  obtain ⟨c_b₂, c_21, c_2a, c_fast, c_τ, c_δ, c_δπ, c_start, c_η, c_lev⟩ :=
    radar_family_gate_conditions hk M
  obtain ⟨s5, sR, sM, sτ, st₀, sHB, sHA, sclB, sclA, sband⟩ := radar_family_all_conditions hk M
  unfold famT5 at s5
  unfold famTcR at sR
  unfold famTcM at sM
  unfold famTE famTb famT3 at sband
  unfold famTb famT3 famT4 famT5 famTbM famTcM famTbR famTcR
  obtain ⟨⟨o1, o2, o3, o4, o5⟩, ⟨p1, p2, p3⟩, ⟨q1, q2, q3⟩, i1, i2, i3, i4, i5, i6, i7, i8,
    i9, i10, i11, i12, i13⟩ := radar_gate_times c_b₂ c_21 c_2a c_fast c_τ c_δ c_δπ c_start
      c_η c_lev
  have hb₁0 : 0 < radarRateB k := c_b₂.trans_le c_21
  have ha0 : 0 < radarRateA k := by linarith only [c_2a, hb₁0]
  have ht₀ : radarRateA k * (radarRateB k * radarTau k M / radarRateA k)
      = radarRateB k * radarTau k M := mul_div_cancel₀ _ ha0.ne'
  have I := radar_gate_intervals (t₀ := radarRateB k * radarTau k M / radarRateA k)
    (w := 3 * wallDelta k) c_b₂ c_21 (by linarith only [c_2a, hb₁0]) c_τ ht₀ c_δ.le
    (by linarith only [c_δ]) (by linarith only [c_δπ, c_δ]) (o1.trans o2)
    ((o1.trans o2).trans (o3.trans o4)) q1 q2 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  obtain ⟨I1, I2, I3, I4, I5, I6, I7⟩ := I
  -- the carriers
  have hNpos : 0 < wallN k := by
    rw [wallN]
    positivity
  have hkN : k ≤ wallN k := by
    rw [wallN]
    calc k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
      _ ≤ 10 ^ 16 * k ^ 4 := Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨-, -, -, -, ⟨hμ0, hμ1⟩, ⟨hΔ0, hΔ12⟩⟩ := wall_values hk1 (t := 0) (t' := 0)
    (by rw [abs_zero]; linarith only [hK0]) (by rw [abs_zero]; linarith only [hK0])
  have hMz : (210000 : ℤ) * (wallN k : ℤ) ^ 2 * wallN k ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ wallN k := by exact_mod_cast hNpos
  have hnN : (0 : ℤ) ≤ (wallN k : ℤ) * wallN k := by positivity
  have hsq : (wallN k : ℤ) * wallN k ≤ (wallN k : ℤ) ^ 2 * wallN k := by
    nlinarith only [hn1, hnN]
  have hNle : (wallN k : ℤ) ≤ (wallN k : ℤ) * wallN k := by nlinarith only [hn1]
  have hlo : (0 : ℤ) < 600 * (wallN k : ℤ) * wallN k := by nlinarith only [hn1]
  have hhi : 2 * (600 * (wallN k : ℤ) * wallN k + wallN k) ≤ M := by
    linarith only [hMz, hsq, hNle, hnN]
  have hp₀ : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hWD : ∀ m ∈ Finset.Ico (600 * (wallN k : ℤ) * wallN k)
      (600 * (wallN k : ℤ) * wallN k + wallN k),
      |2 * Real.pi * m / ringLen (1200 * wallN k * wallN k) - 1 / 2|
        ≤ 1 / (600 * (wallN k : ℕ)) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * wallN k * wallN k : ℕ) : ℝ) := by
      exact_mod_cast (by positivity : 0 < 1200 * wallN k * wallN k)
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * wallN k * wallN k)
        = (m : ℝ) / ((1200 * wallN k * wallN k : ℕ) : ℝ) := by
      rw [ringLen]
      field_simp
    rw [e]
    exact flatWindow_width hNpos hNpos m hm
  have hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
      (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
      (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0 := by
    have hnorm := chainInner_icoWall (M := M) hNpos hNpos hμ0 hlo hhi hp₀ hWD
      (radarRateB k * radarTau k M / radarRateA k)
    intro h0
    rw [h0] at hnorm
    simp [chainInner] at hnorm
  -- the far wall
  have hφ : (0 : ℝ) + 2 * Real.pi * (ZMod.val (H : ZMod (M + 1))) / ((M + 1 : ℕ) : ℝ)
      = Real.pi := by
    have hHpos : 0 < H := by omega
    have hlt : H < M + 1 := by omega
    have hH' : (0 : ℝ) < H := by exact_mod_cast hHpos
    rw [ZMod.val_natCast_of_lt hlt, hH]
    push_cast
    field_simp
    ring
  -- sizes
  have hRB0 : 0 < ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) := by
    linarith only [hR1, hΔ0]
  have hRA : ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) = wallGap k :=
    ringRate_zero _ _ hΔ0.le
  have hδ1 : wallDelta k ≤ 1 := by linarith only [c_δπ, c_δ, Real.pi_lt_four]
  have hcos : Real.cos (wallDelta k) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
      (by linarith only [c_δπ, c_δ] : wallDelta k ≤ Real.pi) c_δ
    rw [Real.cos_zero] at h
    exact h
  have h24 : 1 / (24 * (k : ℝ)) ≤ 1 / 2400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX]
  have hLB : ∀ (μ t : ℝ), 0 < μ → 0 ≤ lightBudget (wallN k) (wallN k) μ t := by
    intro μ t hμ
    unfold lightBudget
    positivity
  have hτA0 : 0 ≤ Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) := by
    rw [hRA]
    exact div_nonneg Real.pi_pos.le (by linarith only [hΔ0])
  have hτAK : Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
      ≤ wallK k := by
    rw [hRA, div_le_iff₀ (by linarith only [hΔ0])]
    nlinarith only [hΔK, hX, Real.pi_lt_four]
  have ht₀0 : 0 ≤ radarRateB k * radarTau k M / radarRateA k :=
    div_nonneg (mul_nonneg hb₁0.le c_τ) ha0.le
  have hbud : ∀ s, 0 ≤ s → s ≤ 8 * wallK k →
      4 * lightBudget (wallN k) (wallN k) (wallMu k)
          (radarRateB k * radarTau k M / radarRateA k + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
      ∧ 4 * lightBudget (wallN k) (wallN k) 1
          (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))) + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
      ∧ 4 * lightBudget (wallN k) (wallN k) 1
          (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))) + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2 := by
    intro s hs0 hs
    have e : 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
        = 1 / (1000 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) := by
      field_simp
      ring
    rw [e]
    have b1 : |radarRateB k * radarTau k M / radarRateA k + s| ≤ 10 * wallK k := by
      rw [abs_of_nonneg (by linarith only [ht₀0, hs0])]
      linarith only [st₀, hs, hK0]
    have b2 : |-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))) + s|
        ≤ 10 * wallK k := by
      rw [abs_le]
      constructor <;> linarith only [hτA0, hτAK, hs0, hs, hK0]
    have b3 : |-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))
        + s| ≤ 10 * wallK k := by
      have h1 : 0 ≤ radarTau k M := c_τ
      have h2 : radarTau k M ≤ wallK k := sτ
      unfold radarTau at h1 h2
      rw [abs_le]
      constructor <;> linarith only [h1, h2, hs0, hs, hK0]
    have b0 : |(0 : ℝ)| ≤ 10 * wallK k := by rw [abs_zero]; linarith only [hK0]
    have v1 := (wall_values hk1 b1 b0).1
    have v2 := (wall_values hk1 b0 b2).1
    have v3 := (wall_values hk1 b0 b3).1
    have n1 := hLB 1 0 one_pos
    have n2 := hLB (wallMu k) 0 hμ0
    exact ⟨by linarith only [v1, n1], by linarith only [v2, n2], by linarith only [v3, n2]⟩
  -- the theorem of #423
  have t30 : 0 ≤ 6 * wallDelta k / (radarRateA k - radarRateB k) := o1.trans o2
  have t40 : 0 ≤ (2 * Real.pi - wallDelta k) / (radarRateA k + radarRateB' k) :=
    t30.trans (o3.trans o4)
  have tM0 : 0 ≤ radarTau k M + (Real.pi - 6 * wallDelta k) / radarRateB k := c_τ.trans q1
  have R := tri_wall_radar_lorentz (j := k) (n := wallN k) (N := wallN k) (M := M)
    (Δ := wallGap k) (μ := wallMu k) (p₀ := 1 / 2) (w := 3 * wallDelta k) (δ := wallDelta k)
    (ε := 1 / (500 * (k : ℝ))) (T := 8 * wallK k) (d := Real.pi * wallK k)
    (by omega) hkN hNpos hM hμ0 hμ1 hΔ0 hΔ12 hlo hhi hp₀ hWD
    (radarRateB k * radarTau k M / radarRateA k) (H : ZMod (M + 1)) hψ c_δ.le hcos
    (by linarith only [c_δ]) (by linarith only [c_δπ, c_δ]) (by positivity) hbud
    o1 o2 o3 o4 o5 s5 ((o4.trans o5).trans (s5.trans sHB)) I1 I2 I3
    ((sclB _ (by linarith only [o4, o5, s5, t30])).trans (by norm_num))
    ((sclB _ (by linarith only [s5, t40])).trans (by norm_num)) sband
    p1 p2 p3 sR ((p2.trans p3).trans (sR.trans sHA))
    (fun s h0 h1 => by rw [hφ]; exact I4 s h0 h1)
    (fun s h0 h1 => by rw [hφ]; exact I5 s h0 h1)
    (by
      have := sclA _ ((p2.trans p3).trans sR)
      linarith only [this, h24])
    ((sclA _ (by linarith only [sR, p1, p2])).trans (by norm_num))
    tM0 q2 q3 sM ((q2.trans q3).trans (sM.trans sHB)) ((q2.trans q3).trans (sM.trans sHA))
    (fun s h0 h1 => by rw [hφ]; exact I6 s h0 h1)
    (fun s h0 h1 => by rw [hφ]; exact I7 s h0 h1)
    (by
      have := sclB _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    ((sclB _ (by linarith only [sM, tM0, q2])).trans (by norm_num))
    (by
      have := sclA _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    ((sclA _ (by linarith only [sM, tM0, q2])).trans (by norm_num))
  obtain ⟨gA, gB, hΨA, hΨB, a1, a2, a3, a4, W⟩ := R
  refine ⟨hψ, gA, gB, hΨA, hΨB, a1, a2, a3, a4, ?_⟩
  -- the error
  have hv := vRel_half_one
  have hs : 89 / 100 ≤ Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hv.1, hv.2])
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := radar_error_pieces hK0 hX hKX hΔK ha1 ha2 hb1 hb2
    hb3 hb4 c_τ (by
      have h1 : radarTau k M * wallGap k
          = Real.pi * (wallGap k / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2)
            (wallGap k))) := by
        rw [radarTau]
        ring
      rw [h1]
      have h2 : wallGap k / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))
          ≤ 1 := by
        rw [div_le_one (by linarith only [hRB0])]
        linarith only [hR1]
      nlinarith only [h2, Real.pi_pos]) (radarRateB_mul_wallK hk1) (δ := wallDelta k) rfl
  -- the rate tolerance
  have hκ0 : 0 ≤ wallGap k
      + (ringLen (1200 * wallN k * wallN k) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6 := by
    have := hΔ0
    positivity
  have hκ : (wallGap k
      + (ringLen (1200 * wallN k * wallN k) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6)
        * (8 * wallK k) ≤ 8 * (k : ℝ) + 1 := by
    have hN1 : (1 : ℝ) ≤ wallN k := by exact_mod_cast hNpos
    have hKc : ((1200 * wallN k * wallN k : ℕ) : ℝ) = wallK k := by
      rw [wallK]
      push_cast
      ring
    have hKe : wallK k = 1200 * (wallN k : ℝ) * wallN k := rfl
    have hL : 210000 * (wallN k : ℝ) ^ 2 * wallN k ≤ ((M + 1 : ℕ) : ℝ) := by
      have : 210000 * wallN k ^ 2 * wallN k ≤ M + 1 := by omega
      exact_mod_cast this
    have hL0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    set x : ℝ := ringLen (1200 * wallN k * wallN k) / ((M + 1 : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := by
      rw [hx, ringLen]
      positivity
    have hxL : x * ((M + 1 : ℕ) : ℝ) = 2 * Real.pi * wallK k := by
      rw [hx, ringLen, hKc]
      field_simp
    have hxN : x * wallN k ≤ 1 / 25 := by
      have h1 : x * (210000 * (wallN k : ℝ) ^ 2 * wallN k) ≤ 2 * Real.pi * wallK k := by
        rw [← hxL]
        exact mul_le_mul_of_nonneg_left hL hx0
      have h2 : 2 * Real.pi * wallK k ≤ 8400 * ((wallN k : ℝ) * wallN k) := by
        rw [hKe]
        nlinarith only [Real.pi_lt_d2, mul_pos (lt_of_lt_of_le one_pos hN1)
          (lt_of_lt_of_le one_pos hN1)]
      have h3 : x * wallN k * (210000 * ((wallN k : ℝ) * wallN k))
          ≤ 1 / 25 * (210000 * ((wallN k : ℝ) * wallN k)) := by
        nlinarith only [h1, h2]
      exact le_of_mul_le_mul_right h3 (by nlinarith only [hN1])
    have hxN0 : 0 ≤ x * wallN k := mul_nonneg hx0 (by linarith only [hN1])
    have hsq2 : (x * wallN k) ^ 2 ≤ (1 / 25) ^ 2 := pow_le_pow_left₀ hxN0 hxN 2
    have e : (wallGap k + x ^ 2 * (1 / 2) ^ 3 / 6) * (8 * wallK k)
        = 8 * (wallGap k * wallK k) + 200 * (x * wallN k) ^ 2 := by
      rw [hKe]
      ring
    rw [e, hΔK]
    nlinarith only [hsq2]
  have hEr := radar_error_le (RA := ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
    (RB := ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))
    (TR := radarTR (Real.pi * wallK k))
    (TRet := radarTRet (Real.pi * wallK k) (vRel 1 1 (1 / 2)))
    (TM := radarTM (Real.pi * wallK k) (vRel 1 1 (1 / 2)))
    hK0 hX hKX hΔK hRA hR2 a1.le (by linarith only [a2, hRA]) a3.le
    (by linarith only [a4, hR2]) hκ0 hκ hv.2 hs o1 o2 o4 q2 p2
    (by linarith only [o4, o5, s5]) (by linarith only [q2, q3, sM]) g1 g2 g3 g4 g5 g6 g7 g8
  exact W.mono hEr.1 hEr.2

end Run

end CSD.RecordLayer

end
