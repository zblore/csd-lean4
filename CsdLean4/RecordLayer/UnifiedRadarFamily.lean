/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallIntervals
public import CsdLean4.RecordLayer.UnifiedWallValues
public import CsdLean4.RecordLayer.UnifiedEventTimes

/-!
# The family: the rates of the three carriers and the conditions of the gate times

**Category:** 7-SigmaLayer (the record layer). BACKLOG #425 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 8 of the research delivery
plan of 2026-11-16, first part. No new assumption.

The family of #415: `n = N = 10¹⁶ k⁴`, the ring of length `2π K` with `K = 1200 N²`, the gap
`Δ = k/K`, the messenger's rest energy `1/k`, the arcs' half-angle `δ = 1/(10⁵ k)`. This
module computes, for `k ≥ 100`, the angular rates of the messenger and of the moving clock's
two levels and the packet time at which that clock is prepared, and proves the six conditions
under which `radar_gate_times` (#424) gives the gate times.

* `radarRateA`, `radarRateB`, `radarRateB'`, `radarTau` — the three rates and the clock's
  preparation time;
* ★★ `radar_family_rates` — `K ≥ 10⁷ k²`, `Δ K = k`; the messenger's rate is within
  `[(1 − 2/k²)/K, 1/K]`, the first level's within `[(2/5)/K, (9/20)/K]`, the second level's
  within `Δ/K` below the first; the moving clock's rate is within `[Δ/2, Δ]`;
* `radar_six_of_bounds` — the six conditions from those bounds (real arithmetic);
* ★★★ `radar_family_gate_conditions` — the six conditions of `radar_gate_times` for the
  family, for every `k ≥ 100` and every number of sites;
* `famTE`, `famTb`, `famT3`, `famT4`, `famT5`, `famTR`, `famTbR`, `famTcR`, `famTM`,
  `famTbM`, `famTcM` — the eleven gate times of `radar_gate_times` for the family;
* `radar_sizes_of_bounds` — the sizes from the bounds (real arithmetic);
* ★★★ `radar_family_all_conditions` — the sizes of #423 for the family with gate weight
  `1/(500 k)` and swing index `k`: the last gate times and the two swing horizons against
  `8K`, the closing terms, and the band.

## Exact scope

* **Six conditions on rates, a start and a half-angle, and the sizes.** With #424 the six
  give gate times that satisfy the seven angle conditions of #423; the sizes are the swing
  horizons, the closing conditions and the band of #423 in a form from which each follows.
  The budget of #423 is `wall_values` (#415). The theorem of #423 is not applied here.
* **`k ≥ 100`**, chosen for round constants; not the least value for which they hold.
* **Nothing about the flow.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-184, UD-188, UD-193, UD-194, UD-195); `specs/unified-m6-feasibility.md`
(§3, the family); `RecordLayer/UnifiedWallIntervals.lean` (#424: `radar_gate_times`);
`RecordLayer/UnifiedWallValues.lean` (#415: `wallN`, `wallK`, `wallGap`, `wallDelta`,
`wallMu`, `wall_values`); `RecordLayer/UnifiedEmissionValues.lean` (#397: `vRel_half_light`,
`vRel_half_one`); `RecordLayer/UnifiedEventTimes.lean` (#418: `abs_vRel_level_sub_le`);
`RecordLayer/UnifiedClockPacketInstance.lean` (`half_le_levelClockRate`,
`levelClockRate_le_gap`).
-/

@[expose] public section

noncomputable section

open CSD.CV

namespace CSD.RecordLayer

/-- **The messenger's angular rate** for the family. -/
def radarRateA (k : ℕ) : ℝ :=
  2 * Real.pi / ringLen (1200 * wallN k * wallN k) * vRel 1 (wallMu k) (1 * (1 / 2))

/-- **The angular rate of the moving clock's first level.** -/
def radarRateB (k : ℕ) : ℝ :=
  2 * Real.pi / ringLen (1200 * wallN k * wallN k) * vRel 1 1 (1 * (1 / 2))

/-- **The angular rate of the moving clock's second level.** -/
def radarRateB' (k : ℕ) : ℝ :=
  2 * Real.pi / ringLen (1200 * wallN k * wallN k) * vRel 1 (1 + wallGap k) (1 * (1 / 2))

/-- **The packet time before `0` at which the moving clock is prepared**: a quarter turn. -/
def radarTau (k M : ℕ) : ℝ :=
  Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))

/-- The velocity at momentum `1/2` and rest energy `1` is at least `2/5`. -/
theorem two_fifths_le_vRel_half_one : 2 / 5 ≤ vRel 1 1 (1 / 2) := by
  have hE := dispE_pos (μ := 1) one_pos (1 / 2)
  have hE1 : dispE 1 (1 / 2) ≤ 5 / 4 := by
    rw [dispE, Real.sqrt_le_iff]
    constructor <;> norm_num
  rw [vRel, le_div_iff₀ hE]
  linarith only [hE1]

/-- A heavier level is slower at the same positive momentum. -/
theorem vRel_level_le {Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) : vRel 1 (1 + Δ) s ≤ vRel 1 1 s := by
  have hE := dispE_pos (μ := 1) one_pos s
  have hle : dispE 1 s ≤ dispE (1 + Δ) s := by
    rw [dispE, dispE]
    exact Real.sqrt_le_sqrt (by nlinarith only [hΔ])
  rw [vRel, vRel]
  exact div_le_div_of_nonneg_left (by linarith only [hs]) hE hle

/-- ★★ **The rates of the family.** For `k ≥ 100` and any number of sites. -/
theorem radar_family_rates {k : ℕ} (hk : 100 ≤ k) (M : ℕ) :
    0 < wallK k ∧ 10 ^ 7 * (k : ℝ) ^ 2 ≤ wallK k ∧ wallGap k * wallK k = k
      ∧ (1 - 2 / (k : ℝ) ^ 2) / wallK k ≤ radarRateA k ∧ radarRateA k ≤ 1 / wallK k
      ∧ 2 / 5 / wallK k ≤ radarRateB k ∧ radarRateB k ≤ 9 / 20 / wallK k
      ∧ radarRateB k - wallGap k / wallK k ≤ radarRateB' k ∧ radarRateB' k ≤ radarRateB k
      ∧ wallGap k / 2 ≤ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)
      ∧ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) ≤ wallGap k := by
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 : (0 : ℝ) < k := by linarith only [hX]
  have hNc : ((wallN k : ℕ) : ℝ) = 10 ^ 16 * (k : ℝ) ^ 4 := by
    rw [wallN]
    push_cast
    ring
  have hX2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith only [hX])
  have hX4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    have : (k : ℝ) ^ 4 = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by ring
    rw [this]
    nlinarith only [hX2]
  have hN1 : (1 : ℝ) ≤ wallN k := by rw [hNc]; nlinarith only [hX2, hX4]
  have hNX : 10 ^ 16 * (k : ℝ) ^ 2 ≤ wallN k := by rw [hNc]; nlinarith only [hX4]
  have hK0 : 0 < wallK k := by rw [wallK]; nlinarith only [hN1]
  have hKN : (wallN k : ℝ) ≤ wallK k := by rw [wallK]; nlinarith only [hN1]
  have hKX : 10 ^ 7 * (k : ℝ) ^ 2 ≤ wallK k := by nlinarith only [hKN, hNX, hX2]
  have hΔK : wallGap k * wallK k = k := by
    rw [wallGap]
    exact div_mul_cancel₀ _ hK0.ne'
  have hΔ0 : 0 < wallGap k := by rw [wallGap]; exact div_pos hX0 hK0
  have hKc : ((1200 * wallN k * wallN k : ℕ) : ℝ) = wallK k := by
    rw [wallK]
    push_cast
    ring
  have hpref : 2 * Real.pi / ringLen (1200 * wallN k * wallN k) = 1 / wallK k := by
    have hπ := Real.pi_pos
    rw [ringLen, hKc]
    field_simp
  have hKn : 0 < 1200 * wallN k * wallN k := by
    have : 0 < wallN k := by
      rw [wallN]
      positivity
    positivity
  have hμ0 : 0 < wallMu k := by rw [wallMu]; positivity
  have hμ : wallMu k ≤ 1 / 2 := by
    rw [wallMu, div_le_div_iff₀ hX0 (by norm_num)]
    linarith only [hX]
  obtain ⟨-, hu1, hu2⟩ := vRel_half_light hμ0 hμ
  have hμ2 : 2 * wallMu k ^ 2 = 2 / (k : ℝ) ^ 2 := by
    rw [wallMu, div_pow, one_pow, mul_one_div]
  rw [hμ2] at hu2
  have hv := vRel_half_one
  have hv' := two_fifths_le_vRel_half_one
  have hl1 := vRel_level_le hΔ0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hl2 := (abs_le.1 (abs_vRel_level_sub_le hΔ0.le (1 / 2))).1
  have hinv : 0 ≤ 1 / wallK k := by positivity
  refine ⟨hK0, hKX, hΔK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [radarRateA, hpref, one_mul]
    calc (1 - 2 / (k : ℝ) ^ 2) / wallK k = 1 / wallK k * (1 - 2 / (k : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu2 hinv
  · rw [radarRateA, hpref, one_mul]
    calc 1 / wallK k * vRel 1 (wallMu k) (1 / 2) ≤ 1 / wallK k * 1 :=
          mul_le_mul_of_nonneg_left hu1 hinv
      _ = 1 / wallK k := mul_one _
  · rw [radarRateB, hpref, one_mul]
    calc 2 / 5 / wallK k = 1 / wallK k * (2 / 5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv' hinv
  · rw [radarRateB, hpref, one_mul]
    calc 1 / wallK k * vRel 1 1 (1 / 2) ≤ 1 / wallK k * (9 / 20) :=
          mul_le_mul_of_nonneg_left hv.2 hinv
      _ = 9 / 20 / wallK k := by ring
  · rw [radarRateB, radarRateB', hpref, one_mul]
    calc 1 / wallK k * vRel 1 1 (1 / 2) - wallGap k / wallK k
        = 1 / wallK k * (vRel 1 1 (1 / 2) - wallGap k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hl2]) hinv
  · rw [radarRateB, radarRateB', hpref, one_mul]
    exact mul_le_mul_of_nonneg_left hl1 hinv
  · exact half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hKn M (by rw [abs_of_pos (by norm_num)]; norm_num))
  · exact levelClockRate_le_gap hΔ0.le _

/-- **The six conditions from bounds on the rates** (real arithmetic): the hypotheses of
`radar_gate_times` for rates within the stated bounds of `1/K`, a start
`π/(2Δ) ≤ τ ≤ π/Δ`, `Δ K = X ≥ 100`, `K ≥ 10⁷ X²` and `δ = 1/(10⁵ X)`. -/
theorem radar_six_of_bounds {K X a b₁ b₂ τ Δ : ℝ} (hK : 0 < K) (hX : 100 ≤ X)
    (hKX : 10 ^ 7 * X ^ 2 ≤ K) (hΔ : Δ * K = X) (ha1 : (1 - 2 / X ^ 2) / K ≤ a)
    (ha2 : a ≤ 1 / K) (hb1 : 2 / 5 / K ≤ b₁) (hb2 : b₁ ≤ 9 / 20 / K)
    (hb3 : b₁ - Δ / K ≤ b₂) (hb4 : b₂ ≤ b₁) (hτ0 : 0 ≤ τ) (hτ2 : τ * Δ ≤ Real.pi) :
    0 < b₂ ∧ b₂ ≤ b₁ ∧ 2 * b₁ ≤ a ∧ a ≤ 3 * b₁ + 4 * b₂ ∧ 0 ≤ τ ∧ 0 < 1 / (10 ^ 5 * X)
      ∧ 24 * (1 / (10 ^ 5 * X)) ≤ Real.pi
      ∧ 4 * (b₁ * τ) ≤ Real.pi - 24 * (1 / (10 ^ 5 * X))
      ∧ (b₁ - b₂) * τ ≤ 1 / (10 ^ 5 * X) / 2
      ∧ 2 * Real.pi * (b₁ - b₂) ≤ 1 / (10 ^ 5 * X) * b₂ := by
  have hX0 : 0 < X := by linarith only [hX]
  have hπ := Real.pi_gt_three
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hX2 : 10 ^ 4 ≤ X ^ 2 := by nlinarith only [hX]
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
  have hB4 : b₂ * K ≤ b₁ * K := mul_le_mul_of_nonneg_right hb4 hK.le
  have h2X : 2 / X ^ 2 ≤ 1 / 5000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX2]
  have hΔ0 : 0 < Δ := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, hΔ, hX0]
  -- the gap is tiny: `Δ ≤ 10⁻⁷ / X`
  have hΔs : Δ * (10 ^ 7 * X) ≤ 1 := by
    have h1 : Δ * (10 ^ 7 * X ^ 2) ≤ Δ * K := mul_le_mul_of_nonneg_left hKX hΔ0.le
    rw [hΔ] at h1
    have h2 : Δ * (10 ^ 7 * X) * X ≤ 1 * X := by nlinarith only [h1]
    exact le_of_mul_le_mul_right h2 hX0
  have hΔ9 : Δ ≤ 1 / 10 ^ 9 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith only [hΔs, mul_le_mul_of_nonneg_left hX hΔ0.le]
  have hδ0 : (0 : ℝ) < 1 / (10 ^ 5 * X) := by positivity
  have hδ1 : 1 / (10 ^ 5 * X) ≤ 1 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX]
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le (by positivity) hb1
  have hb₂K : 0 < b₂ * K := by linarith only [hB3, hB1, hΔ9]
  have hb₂0 : 0 < b₂ := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, hb₂K]
  -- the start: `b₁ τ ≤ 9π/(20 X)`
  have hbτ : b₁ * τ * X ≤ 9 / 20 * Real.pi := by
    have h1 : b₁ * τ * X = (b₁ * K) * (τ * Δ) := by rw [← hΔ]; ring
    rw [h1]
    exact mul_le_mul hB2 hτ2 (mul_nonneg hτ0 hΔ0.le) (by norm_num)
  have hbτ' : b₁ * τ ≤ 9 / 2000 * Real.pi := by
    have h0 : 0 ≤ b₁ * τ := mul_nonneg hb₁0.le hτ0
    nlinarith only [hbτ, mul_le_mul_of_nonneg_left hX h0]
  -- the levels' spread: `(b₁ − b₂) K ≤ Δ`
  have hsp : (b₁ - b₂) * K ≤ Δ := by linarith only [hB3]
  have hsp0 : 0 ≤ b₁ - b₂ := sub_nonneg.2 hb4
  refine ⟨hb₂0, hb4, ?_, ?_, hτ0, hδ0, by linarith only [hδ1, hπ], ?_, ?_, ?_⟩
  · exact le_of_mul_le_mul_right (by linarith only [hA1, hB2, h2X]) hK
  · exact le_of_mul_le_mul_right (by linarith only [hA2, hB1, hB3, hΔ9]) hK
  · linarith only [hbτ', hδ1, hπ]
  · -- `(b₁ − b₂) τ ≤ π / K ≤ δ / 2`
    have h1 : (b₁ - b₂) * τ * K ≤ Real.pi := by
      have e : (b₁ - b₂) * τ * K = (b₁ - b₂) * K * τ := by ring
      rw [e]
      calc (b₁ - b₂) * K * τ ≤ Δ * τ :=
            mul_le_mul_of_nonneg_right hsp hτ0
        _ = τ * Δ := mul_comm _ _
        _ ≤ Real.pi := hτ2
    have h2 : Real.pi ≤ 1 / (10 ^ 5 * X) / 2 * K := by
      have e : 1 / (10 ^ 5 * X) / 2 * K = K / (2 * 10 ^ 5 * X) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith only [hKX, mul_le_mul_of_nonneg_right hπ4.le hX0.le,
        mul_le_mul_of_nonneg_right hX hX0.le, sq_nonneg X]
    exact le_of_mul_le_mul_right (h1.trans h2) hK
  · -- `2π (b₁ − b₂) K ≤ 2π Δ ≤ δ b₂ K`
    have h1 : 2 * Real.pi * (b₁ - b₂) * K ≤ 2 * Real.pi * Δ := by
      have := mul_le_mul_of_nonneg_left hsp (by linarith only [hπ] : 0 ≤ 2 * Real.pi)
      linarith only [this]
    have h2 : 2 * Real.pi * Δ ≤ 1 / (10 ^ 5 * X) * (b₂ * K) := by
      have h3 : 1 / (10 ^ 5 * X) * (1 / 3) ≤ 1 / (10 ^ 5 * X) * (b₂ * K) :=
        mul_le_mul_of_nonneg_left (by linarith only [hB3, hB1, hΔ9]) hδ0.le
      have h4 : 2 * Real.pi * Δ ≤ 1 / (10 ^ 5 * X) * (1 / 3) := by
        have e : 1 / (10 ^ 5 * X) * (1 / 3) = 1 / (3 * 10 ^ 5 * X) := by
          field_simp
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith only [hΔs, mul_le_mul_of_nonneg_right hπ4.le (mul_nonneg hΔ0.le hX0.le)]
      exact h4.trans h3
    have h5 : 2 * Real.pi * (b₁ - b₂) * K ≤ 1 / (10 ^ 5 * X) * b₂ * K := by
      rw [mul_assoc (1 / (10 ^ 5 * X))]
      exact h1.trans h2
    exact le_of_mul_le_mul_right h5 hK

/-- ★★★ **The six conditions of the gate times, for the family.** For every `k ≥ 100` and
every number of sites, the rates `radarRateA`, `radarRateB`, `radarRateB'`, the preparation
time `radarTau` and the half-angle `wallDelta` satisfy the hypotheses of `radar_gate_times`
(#424). -/
theorem radar_family_gate_conditions {k : ℕ} (hk : 100 ≤ k) (M : ℕ) :
    0 < radarRateB' k ∧ radarRateB' k ≤ radarRateB k ∧ 2 * radarRateB k ≤ radarRateA k
      ∧ radarRateA k ≤ 3 * radarRateB k + 4 * radarRateB' k ∧ 0 ≤ radarTau k M
      ∧ 0 < wallDelta k ∧ 24 * wallDelta k ≤ Real.pi
      ∧ 4 * (radarRateB k * radarTau k M) ≤ Real.pi - 24 * wallDelta k
      ∧ (radarRateB k - radarRateB' k) * radarTau k M ≤ wallDelta k / 2
      ∧ 2 * Real.pi * (radarRateB k - radarRateB' k) ≤ wallDelta k * radarRateB' k := by
  obtain ⟨hK0, hKX, hΔK, ha1, ha2, hb1, hb2, hb3, hb4, hR1, hR2⟩ := radar_family_rates hk M
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hΔ0 : 0 < wallGap k := by
    rw [wallGap]
    exact div_pos (by linarith only [hX]) hK0
  have hR0 : 0 < ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) := by
    linarith only [hR1, hΔ0]
  have hτ0 : 0 ≤ radarTau k M := by
    rw [radarTau]
    exact div_nonneg Real.pi_pos.le (by linarith only [hR0])
  have hτ2 : radarTau k M * wallGap k ≤ Real.pi := by
    rw [radarTau, div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hR0])]
    nlinarith only [hR1, Real.pi_pos]
  unfold wallDelta
  exact radar_six_of_bounds hK0 hX hKX hΔK ha1 ha2 hb1 hb2 hb3 hb4 hτ0 hτ2

/-! ### The gate times of the family and the sizes -/

/-- **The emission ends.** -/
def famTE (k : ℕ) : ℝ := wallDelta k / (2 * (radarRateA k + radarRateB k))

/-- **The emission gate has closed.** -/
def famTb (k : ℕ) : ℝ := 6 * wallDelta k / (radarRateA k - radarRateB k)

/-- **The return gate begins to close.** -/
def famT3 (k : ℕ) : ℝ := (2 * Real.pi - 6 * wallDelta k) / (radarRateA k + radarRateB k)

/-- **The return window opens.** -/
def famT4 (k : ℕ) : ℝ := (2 * Real.pi - wallDelta k) / (radarRateA k + radarRateB' k)

/-- **The return window closes.** -/
def famT5 (k : ℕ) : ℝ :=
  (2 * Real.pi + wallDelta k / 2) / (radarRateA k + radarRateB k)

/-- **The relay gate begins to close.** -/
def famTR (k M : ℕ) : ℝ :=
  (Real.pi - 6 * wallDelta k - radarRateB k * radarTau k M) / radarRateA k

/-- **The relay window opens.** -/
def famTbR (k M : ℕ) : ℝ :=
  (Real.pi - wallDelta k - radarRateB k * radarTau k M) / radarRateA k

/-- **The relay window closes.** -/
def famTcR (k M : ℕ) : ℝ :=
  (Real.pi + wallDelta k - radarRateB k * radarTau k M) / radarRateA k

/-- **The meeting gate begins to close.** -/
def famTM (k M : ℕ) : ℝ := radarTau k M + (Real.pi - 6 * wallDelta k) / radarRateB k

/-- **The meeting window opens.** -/
def famTbM (k M : ℕ) : ℝ := radarTau k M + (Real.pi - wallDelta k) / radarRateB' k

/-- **The meeting window closes.** -/
def famTcM (k M : ℕ) : ℝ := radarTau k M + (Real.pi + wallDelta k) / radarRateB k

/-- **The sizes from bounds on the rates** (real arithmetic). Rates and start as in
`radar_six_of_bounds`, a clock rate `0 < R ≤ Δ`, a swing size `n ≥ 2 X²`, the half-angle
`δ = 1/(10⁵ X)` and the gate weight `ε = 1/(500 X)`: the last gate times are at most `8K`,
the start is at most `K`, the swing horizon `2π n/(X R)` is at least `8K`, a closing term
over any time up to `8K` is at most `16/2500`, and the band inequality of #420 holds for the
gate times of `radar_gate_times`. -/
theorem radar_sizes_of_bounds {K X a b₁ τ Δ R n : ℝ} (hK : 0 < K) (hX : 100 ≤ X)
    (hΔ : Δ * K = X) (ha1 : (1 - 2 / X ^ 2) / K ≤ a) (hb1 : 2 / 5 / K ≤ b₁)
    (hb2 : b₁ ≤ 9 / 20 / K) (hτ0 : 0 ≤ τ) (hτ2 : τ * Δ ≤ Real.pi) (hR0 : 0 < R)
    (hR : R ≤ Δ) (hn : 2 * X ^ 2 ≤ n) :
    (2 * Real.pi + 1 / (10 ^ 5 * X) / 2) / (a + b₁) ≤ 8 * K
      ∧ (Real.pi + 1 / (10 ^ 5 * X) - b₁ * τ) / a ≤ 8 * K
      ∧ τ + (Real.pi + 1 / (10 ^ 5 * X)) / b₁ ≤ 8 * K
      ∧ τ ≤ K ∧ b₁ * τ / a ≤ K
      ∧ 8 * K ≤ 2 * Real.pi * n / (X * R)
      ∧ (∀ x, x ≤ 8 * K → 2 * (R / 5) * (1 / (500 * X)) * x ≤ 16 / 2500)
      ∧ 1 / 4 * (1 - Real.cos (R * (1 / (10 ^ 5 * X) / (2 * (a + b₁))))) + 1 / (24 * X)
          + 2 * (R / 5) * (1 / (500 * X)) * (1 / (10 ^ 5 * X) / (2 * (a + b₁)))
          + 2 * (R / 5) * (6 * (1 / (10 ^ 5 * X)) / (a - b₁)
              - 1 / (10 ^ 5 * X) / (2 * (a + b₁)))
          + (1 / (24 * X) + 2 * (R / 5) * (1 / (500 * X))
              * ((2 * Real.pi - 6 * (1 / (10 ^ 5 * X))) / (a + b₁)
                - 6 * (1 / (10 ^ 5 * X)) / (a - b₁)))
        < 1 / 12 := by
  have hX0 : 0 < X := by linarith only [hX]
  have hπ := Real.pi_gt_three
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hX2 : 10 ^ 4 ≤ X ^ 2 := by nlinarith only [hX]
  have h2X : 2 / X ^ 2 ≤ 1 / 5000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX2]
  have hA1 : 1 - 2 / X ^ 2 ≤ a * K := (div_le_iff₀ hK).1 ha1
  have hB1 : 2 / 5 ≤ b₁ * K := (div_le_iff₀ hK).1 hb1
  have hB2 : b₁ * K ≤ 9 / 20 := by
    have := mul_le_mul_of_nonneg_right hb2 hK.le
    rwa [div_mul_cancel₀ _ hK.ne'] at this
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le (by positivity) hb1
  have ha0 : 0 < a := lt_of_lt_of_le (div_pos (by linarith only [h2X]) hK) ha1
  have hab : 0 < a - b₁ := by
    have : 0 < (a - b₁) * K := by linarith only [hA1, hB2, h2X]
    by_contra h
    rw [not_lt] at h
    nlinarith only [mul_nonneg (neg_nonneg.2 h) hK.le, this]
  have hp1 : 0 < a + b₁ := by linarith only [ha0, hb₁0]
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hR0 hR
  set δ : ℝ := 1 / (10 ^ 5 * X) with hδd
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 10 ^ 7 := by
    rw [hδd, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX]
  have hδX : δ * X = 1 / 10 ^ 5 := by
    rw [hδd]
    field_simp
  have hbτ0 : 0 ≤ b₁ * τ := mul_nonneg hb₁0.le hτ0
  -- the start: `τ X ≤ π K`
  have hτK : τ * X ≤ Real.pi * K := by
    rw [← hΔ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hτ2 hK.le
  have hτK' : τ ≤ 315 / 10000 * K := by
    have h1 : τ * 100 ≤ τ * X := mul_le_mul_of_nonneg_left hX hτ0
    have h2 : Real.pi * K ≤ 3.15 * K := mul_le_mul_of_nonneg_right hπu.le hK.le
    linarith only [h1, h2, hτK]
  -- the three end times
  have c1 : (2 * Real.pi + δ / 2) / (a + b₁) ≤ 8 * K := by
    rw [div_le_iff₀ hp1]
    linarith only [hA1, hB1, h2X, hπu, hδ1]
  have c2 : (Real.pi + δ - b₁ * τ) / a ≤ 8 * K := by
    rw [div_le_iff₀ ha0]
    linarith only [hA1, h2X, hπu, hδ1, hbτ0]
  have c3' : (Real.pi + δ) / b₁ ≤ 79 / 10 * K := by
    rw [div_le_iff₀ hb₁0]
    linarith only [hB1, hπu, hδ1]
  have c3 : τ + (Real.pi + δ) / b₁ ≤ 8 * K := by linarith only [c3', hτK', hK]
  have c4 : τ ≤ K := by linarith only [hτK', hK]
  have c5 : b₁ * τ / a ≤ K := by
    rw [div_le_iff₀ ha0]
    have h1 : b₁ * τ * K ≤ 9 / 20 * τ := by
      have := mul_le_mul_of_nonneg_right hB2 hτ0
      linarith only [this]
    have h2 : K * (1 / 2) ≤ K * (a * K) :=
      mul_le_mul_of_nonneg_left (by linarith only [hA1, h2X]) hK.le
    exact le_of_mul_le_mul_right (by linarith only [h1, h2, c4, hK]) hK
  -- the horizon
  have c6 : 8 * K ≤ 2 * Real.pi * n / (X * R) := by
    rw [le_div_iff₀ (mul_pos hX0 hR0)]
    have h1 : K * R ≤ X := by
      rw [← hΔ, mul_comm]
      exact mul_le_mul_of_nonneg_right hR hK.le
    have h2 : 8 * K * (X * R) = 8 * X * (K * R) := by ring
    rw [h2]
    have h3 : 8 * X * (K * R) ≤ 8 * X * X :=
      mul_le_mul_of_nonneg_left h1 (by linarith only [hX0])
    have hn0 : 0 ≤ n := by nlinarith only [hn, sq_nonneg X]
    have h4 := mul_le_mul_of_nonneg_right hπ.le hn0
    nlinarith only [h3, h4, hn]
  -- a closing term
  have c7 : ∀ x, x ≤ 8 * K → 2 * (R / 5) * (1 / (500 * X)) * x ≤ 16 / 2500 := by
    intro x hx
    have h1 : R * x ≤ 8 * X := by
      calc R * x ≤ R * (8 * K) := mul_le_mul_of_nonneg_left hx hR0.le
        _ ≤ Δ * (8 * K) := mul_le_mul_of_nonneg_right hR (by linarith only [hK])
        _ = 8 * X := by rw [← hΔ]; ring
    have e : 2 * (R / 5) * (1 / (500 * X)) * x = R * x * (2 / (2500 * X)) := by
      field_simp
      ring
    rw [e]
    calc R * x * (2 / (2500 * X)) ≤ 8 * X * (2 / (2500 * X)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 16 / 2500 := by
        field_simp
        norm_num
  -- the band
  have hKp : 1 ≤ (a + b₁) * K := by linarith only [hA1, hB1, h2X]
  have hKm : 1 / 2 ≤ (a - b₁) * K := by linarith only [hA1, hB2, h2X]
  have tE0 : 0 ≤ δ / (2 * (a + b₁)) := by positivity
  have tE1 : δ / (2 * (a + b₁)) ≤ δ * K / 2 := by
    rw [div_le_iff₀ (by linarith only [hp1])]
    nlinarith only [mul_le_mul_of_nonneg_left hKp hδ0.le]
  have tb0 : 0 ≤ 6 * δ / (a - b₁) := div_nonneg (by linarith only [hδ0]) hab.le
  have tb1 : 6 * δ / (a - b₁) ≤ 12 * (δ * K) := by
    rw [div_le_iff₀ hab]
    nlinarith only [mul_le_mul_of_nonneg_left hKm hδ0.le]
  have t31 : (2 * Real.pi - 6 * δ) / (a + b₁) ≤ 8 * K := by
    rw [div_le_iff₀ hp1]
    nlinarith only [mul_le_mul_of_nonneg_left hKp (by norm_num : (0 : ℝ) ≤ 8), hπu, hδ0]
  have hδK : δ * K ≤ K := by nlinarith only [hδ1, hK]
  -- the phase at the emission
  have y0 : 0 ≤ R * (δ / (2 * (a + b₁))) := mul_nonneg hR0.le tE0
  have y1 : R * (δ / (2 * (a + b₁))) ≤ 1 / 10 ^ 5 := by
    calc R * (δ / (2 * (a + b₁))) ≤ Δ * (δ * K / 2) :=
          mul_le_mul hR tE1 tE0 hΔ0.le
      _ = δ * X / 2 := by rw [← hΔ]; ring
      _ ≤ 1 / 10 ^ 5 := by rw [hδX]; norm_num
  have ycos : 1 / 4 * (1 - Real.cos (R * (δ / (2 * (a + b₁))))) ≤ 1 / 10 ^ 5 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := R * (δ / (2 * (a + b₁))))
    have hsq : (R * (δ / (2 * (a + b₁)))) ^ 2 ≤ 1 / 10 ^ 5 := by
      nlinarith only [y0, y1]
    linarith only [h, hsq]
  -- the closing of the emission gate
  have hgap : 2 * (R / 5) * (6 * δ / (a - b₁) - δ / (2 * (a + b₁))) ≤ 1 / 10 ^ 4 := by
    have h1 : R * (6 * δ / (a - b₁)) ≤ 12 / 10 ^ 5 := by
      calc R * (6 * δ / (a - b₁)) ≤ Δ * (12 * (δ * K)) := mul_le_mul hR tb1 tb0 hΔ0.le
        _ = 12 * (δ * X) := by rw [← hΔ]; ring
        _ = 12 / 10 ^ 5 := by rw [hδX]; ring
    linarith only [h1, y0]
  have hx1 := c7 (δ / (2 * (a + b₁))) (by linarith only [tE1, hδK, hK])
  have hx2 := c7 ((2 * Real.pi - 6 * δ) / (a + b₁) - 6 * δ / (a - b₁))
    (by linarith only [t31, tb0])
  have h24 : 1 / (24 * X) ≤ 1 / 2400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX]
  exact ⟨c1, c2, c3, c4, c5, c6, c7, by linarith only [ycos, hgap, hx1, hx2, h24]⟩

/-- ★★★ **The sizes, for the family.** For every `k ≥ 100` and every number of sites, with
the gate weight `1/(500 k)` and the swing index `j = k`: the last gate times are at most
`8K`; the clock's preparation time and the messenger's are at most `K`; the swing horizons of
both clocks are at least `8K`; a closing term of either clock over any time up to `8K` is at
most `16/2500`; and the band inequality of #420 holds. -/
theorem radar_family_all_conditions {k : ℕ} (hk : 100 ≤ k) (M : ℕ) :
    famT5 k ≤ 8 * wallK k ∧ famTcR k M ≤ 8 * wallK k ∧ famTcM k M ≤ 8 * wallK k
      ∧ radarTau k M ≤ wallK k ∧ radarRateB k * radarTau k M / radarRateA k ≤ wallK k
      ∧ 8 * wallK k ≤ 2 * Real.pi * (wallN k : ℕ)
          / (k * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))
      ∧ 8 * wallK k ≤ 2 * Real.pi * (wallN k : ℕ)
          / (k * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
      ∧ (∀ x, x ≤ 8 * wallK k →
          2 * (ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5)
            * (1 / (500 * (k : ℝ))) * x ≤ 16 / 2500)
      ∧ (∀ x, x ≤ 8 * wallK k →
          2 * (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) / 5)
            * (1 / (500 * (k : ℝ))) * x ≤ 16 / 2500)
      ∧ 1 / 4 * (1 - Real.cos
            (ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) * famTE k))
          + 1 / (24 * (k : ℝ))
          + 2 * (ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5)
            * (1 / (500 * (k : ℝ))) * famTE k
          + 2 * (ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5)
            * (famTb k - famTE k)
          + (1 / (24 * (k : ℝ))
            + 2 * (ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5)
              * (1 / (500 * (k : ℝ))) * (famT3 k - famTb k))
        < 1 / 12 := by
  obtain ⟨hK0, -, hΔK, ha1, -, hb1, hb2, -, -, hR1, hR2⟩ := radar_family_rates hk M
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hΔ0 : 0 < wallGap k := by
    rw [wallGap]
    exact div_pos (by linarith only [hX]) hK0
  have hR0 : 0 < ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) := by
    linarith only [hR1, hΔ0]
  have hτ0 : 0 ≤ radarTau k M := by
    rw [radarTau]
    exact div_nonneg Real.pi_pos.le (by linarith only [hR0])
  have hτ2 : radarTau k M * wallGap k ≤ Real.pi := by
    rw [radarTau, div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hR0])]
    nlinarith only [mul_le_mul_of_nonneg_left hR1 Real.pi_pos.le]
  have hX2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith only [hX])
  have hn : 2 * (k : ℝ) ^ 2 ≤ ((wallN k : ℕ) : ℝ) := by
    have hX4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
      have : (k : ℝ) ^ 4 = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by ring
      rw [this]
      nlinarith only [hX2]
    rw [wallN]
    push_cast
    nlinarith only [hX4, hX2]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := radar_sizes_of_bounds hK0 hX hΔK ha1 hb1 hb2
    hτ0 hτ2 hR0 hR2 hn
  obtain ⟨-, -, -, -, -, d6, d7, -⟩ := radar_sizes_of_bounds hK0 hX hΔK ha1 hb1 hb2
    hτ0 hτ2 hΔ0 le_rfl hn
  rw [ringRate_zero _ _ hΔ0.le]
  unfold famT5 famTcR famTcM famTE famTb famT3 wallDelta
  exact ⟨c1, c2, c3, c4, c5, c6, d6, c7, d7, c8⟩

end CSD.RecordLayer

end
