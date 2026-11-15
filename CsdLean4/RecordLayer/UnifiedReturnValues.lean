/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarReading
public import CsdLean4.RecordLayer.UnifiedEmissionValues

/-!
# Values for a run with a return: a lap of the ring with a quickly closing gate

**Category:** 7-SigmaLayer (the record layer). BACKLOG #403 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; items R5 and R6 of the list
under UD-164, for two carriers on the ring. No new assumption beyond UA-18.

The radar reading of #401 holds under inequalities between the parameters and under the
conditions of #400: a gate that closes within a small part of a tick, and a condition on the
clock's phase. The family of #397 does not meet them. This module exhibits values that do,
along a family, and so tests whether the pointer arrangement of UA-18 can give a return
reading at all.

* `lap_times`, `lap_angles` — the flow times and the predicted angles of a messenger that
  starts with the clock, leaves, and comes round the ring once;
* `lapBudget`, `lap_budget_le`, `lap_error_le` — the two packets' budgets over the lap, and
  the two error terms;
* `lapTb`, `lapT3`, `lapT4` — the first and last flow times at which the two are certified
  apart, and the flow time at which the messenger has come round;
* ★★★ `lap_radar_reading` — a flat messenger of rest energy `0 < μ ≤ 1/2` and the flat clock
  packet on one ring, the gate "within the angle `3δ`", both gates in one run, under seven
  scalar conditions: for some strength `0 < g ≤ R/5`, at every flow time of
  `[lapTb, lapT3]` the first pointer has a count `N_e` with `N_e ≤ 4`, and at `lapT4` the
  last pointer has a count `N_r` with `|2π N_r − R (lapT3 − lapTb)| ≤ 16π`, and
  `R (lapT3 − lapTb) ≥ (5/2) Δ K`, `K = 1200 n N`;
* `lapn`, `lapGap`, `lap_family_conditions`;
* ★★★ `lap_radar_family` — for every `k ≥ 1`, with `n = N = 10¹¹ k³`, gap `k/K`,
  `δ = ε = 1/(1000 k)`, `μ = 1/2`: the conclusions above with no condition but the size of
  the ring; the time away is at least `(5/2) k` in the clock's phase, and
  `|2π N_r − R (lapT3 − lapTb)| ≤ (21/k) · R (lapT3 − lapTb)`.

## Exact scope

* **The test is passed for two carriers on the ring, not on the arena of UA-18.** A lap of a
  ring stands in for the reflection at a wall; the clock moves at about `0.45`; there is no
  second observer. This discharges nothing of the list under UD-164 on the chain with two
  walls. What it shows is that the conditions of #400 can be met together with all the
  other inequalities, with an error that is a fixed number of ticks.
* **The emission is at the start.** The messenger starts where the clock's lower level is
  predicted to be and the gate begins to close at the flow time `0`, so the emission count
  is at most four ticks and the phase condition of #400 holds because `cos 0 = 1`. A run
  whose emission comes later in the clock's phase is not exhibited.
* **The return is read at one flow time**, `lapT4`, at which the predicted angles have come
  round by exactly `2π`. A window after it is not exhibited.
* **A slow clock.** The gate closes within a small part of a tick because the gap is
  `k/K`: the clock makes about `k` turns of phase in the time the messenger needs to go
  round the ring. The messenger has rest energy `1/2` in the family and travels at about
  `0.7`; its speed is not close to one here.
* **Counts of two pointers at two flow times**, as #401; the fibres where both profiles
  vanish and product starts only, as #393; for some strength, as #396.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-153, UD-154, UD-159, UD-160, UD-161, UD-162, UD-164, UD-165, UD-166);
`RecordLayer/UnifiedRadarReading.lean` (#401: `flat_clock_radar_reading`);
`RecordLayer/UnifiedStopBand.lean` (#400); `RecordLayer/UnifiedReturnReading.lean` (#399:
`ringReturnRun`, `packetAngleGap`); `RecordLayer/UnifiedEmissionValues.lean` (#397:
`emission_angles`, `flat_messenger_budget`, `emT0`, `vRel_half_light`, `vRel_half_one`,
`cos_le_cos_of_abs_le`, `cos_lt_cos_of_between`, `sq_div_five_le_one_sub_cos`);
`RecordLayer/UnifiedGateRegions.lean` (#395: `flatBudget`, `ringPacket_ne_zero`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The flow times and the predicted angles of a lap -/

/-- **The flow times of a lap.** With `d` the difference of the two velocities, `1/4 ≤ d ≤ 1`,
and `52 Δ ≤ δ ≤ 1/100`: the times `t_b = 6δ/((d/K)(1 − 4Δ))`,
`t₃ = (2π − 6δ)/((d/K)(1 + 4Δ))`, `t₄ = 2π/(d/K)` are ordered, `t_b ≤ 25 δ K`, `t₄ ≤ 26 K`,
`t₃ − t_b ≥ 5 K`, `t₄ − t₃ ≤ 26 δ K`, and they solve the three angle equations. -/
theorem lap_times {K d Δ δ : ℝ} (hK : 0 < K) (hd : 1 / 4 ≤ d) (hd1 : d ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hΔδ : 52 * Δ ≤ δ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 100) :
    0 ≤ 6 * δ / (d / K * (1 - 4 * Δ))
    ∧ 6 * δ / (d / K * (1 - 4 * Δ)) ≤ (2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ))
    ∧ (2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ)) ≤ 2 * Real.pi / (d / K)
    ∧ 6 * δ / (d / K * (1 - 4 * Δ)) ≤ 25 * δ * K
    ∧ 2 * Real.pi / (d / K) ≤ 26 * K
    ∧ 5 * K ≤ (2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ)) - 6 * δ / (d / K * (1 - 4 * Δ))
    ∧ 2 * Real.pi / (d / K) - (2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ)) ≤ 26 * δ * K
    ∧ d / K * (6 * δ / (d / K * (1 - 4 * Δ))) * (1 - 4 * Δ) = 6 * δ
    ∧ d / K * ((2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ))) * (1 + 4 * Δ)
        = 2 * Real.pi - 6 * δ
    ∧ d / K * (2 * Real.pi / (d / K)) = 2 * Real.pi := by
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hd0 : 0 < d := by linarith
  have hΔs : Δ ≤ 1 / 5200 := by linarith
  have hm : 0 < 1 - 4 * Δ := by linarith
  have hp : 0 < 1 + 4 * Δ := by linarith
  have hc : 6 / 25 ≤ d * (1 - 4 * Δ) := by nlinarith
  have hc1 : d * (1 - 4 * Δ) ≤ 1 := by nlinarith
  have hc0 : 0 < d * (1 - 4 * Δ) := by linarith
  have hc' : 1 / 4 ≤ d * (1 + 4 * Δ) := by nlinarith
  have hc'1 : d * (1 + 4 * Δ) ≤ 101 / 100 := by nlinarith
  have hc'0 : 0 < d * (1 + 4 * Δ) := by linarith
  have hc'd : d ≤ d * (1 + 4 * Δ) := by nlinarith
  have etb : 6 * δ / (d / K * (1 - 4 * Δ)) = 6 * δ * K / (d * (1 - 4 * Δ)) := by
    field_simp
  have et3 : (2 * Real.pi - 6 * δ) / (d / K * (1 + 4 * Δ))
      = (2 * Real.pi - 6 * δ) * K / (d * (1 + 4 * Δ)) := by
    field_simp
  have et4 : 2 * Real.pi / (d / K) = 2 * Real.pi * K / d := by
    field_simp
  have hδK : 0 < δ * K := mul_pos hδ0 hK
  have hπK : 0 < Real.pi * K := mul_pos Real.pi_pos hK
  -- the four bounds, in the cleared forms
  have b1 : 6 * δ * K / (d * (1 - 4 * Δ)) ≤ 25 * δ * K := by
    rw [div_le_iff₀ hc0]
    have := mul_le_mul_of_nonneg_left hc hδK.le
    linarith
  have b2 : 2 * Real.pi * K / d ≤ 26 * K := by
    rw [div_le_iff₀ hd0]
    have h1 := mul_le_mul_of_nonneg_left hd hK.le
    have h2 := mul_le_mul_of_nonneg_right hπu.le hK.le
    linarith
  have b3 : 53 / 10 * K ≤ (2 * Real.pi - 6 * δ) * K / (d * (1 + 4 * Δ)) := by
    rw [le_div_iff₀ hc'0]
    have h1 := mul_le_mul_of_nonneg_left hc'1 hK.le
    have h2 := mul_le_mul_of_nonneg_right hπ3.le hK.le
    have h3 := mul_le_mul_of_nonneg_right hδ hK.le
    linarith
  have b4 : (2 * Real.pi - 6 * δ) * K / (d * (1 + 4 * Δ)) ≤ 2 * Real.pi * K / d := by
    rw [div_le_div_iff₀ hc'0 hd0]
    have h1 := mul_le_mul_of_nonneg_left hc'd hπK.le
    have h2 : 0 ≤ δ * K * d := by positivity
    linarith
  have b5 : 2 * Real.pi * K / d - (2 * Real.pi - 6 * δ) * K / (d * (1 + 4 * Δ))
      ≤ 26 * δ * K := by
    have e : 2 * Real.pi * K / d - (2 * Real.pi - 6 * δ) * K / (d * (1 + 4 * Δ))
        = K * (8 * Real.pi * Δ + 6 * δ) / (d * (1 + 4 * Δ)) := by
      field_simp
      ring
    rw [e, div_le_iff₀ hc'0]
    have h1 := mul_le_mul_of_nonneg_left hc' hδK.le
    have h2 : Real.pi * Δ ≤ 3.15 * Δ := mul_le_mul_of_nonneg_right hπu.le hΔ0
    have h3 := mul_le_mul_of_nonneg_right h2 hK.le
    have h4 := mul_le_mul_of_nonneg_right hΔδ hK.le
    norm_num at h3
    linarith
  have hKδ : δ * K ≤ 1 / 100 * K := mul_le_mul_of_nonneg_right hδ hK.le
  rw [etb, et3, et4]
  refine ⟨by positivity, by linarith, b4, b1, b2, by linarith, b5, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp

/-- **The predicted angles of a lap.** For the messenger's and the two levels' predicted
angles of #397, with `Δ q/K ≤ δ/2` and `52 Δ ≤ δ`: at the flow time `0` both differences are
within `δ` of zero; on `[t_b, t₃]` both lie strictly between `5δ` and `2π − 5δ`; and at `t₄`
both are within `δ` of `2π`. -/
theorem lap_angles {K vm v0 v1 q t₀ Δ δ tb t3 t4 : ℝ} (hK : 0 < K)
    (ht0 : vm * t₀ = -(q * v0)) (hd : 1 / 4 ≤ vm - v0) (hv : |v1 - v0| ≤ Δ) (hq : 0 ≤ q)
    (hΔ0 : 0 ≤ Δ) (hΔδ : 52 * Δ ≤ δ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 100)
    (he : Δ * q / K ≤ δ / 2)
    (hutb : (vm - v0) / K * tb * (1 - 4 * Δ) = 6 * δ)
    (hut3 : (vm - v0) / K * t3 * (1 + 4 * Δ) = 2 * Real.pi - 6 * δ)
    (hut4 : (vm - v0) / K * t4 = 2 * Real.pi) (htb : 0 ≤ tb) (ht4 : 0 ≤ t4) :
    (|1 / K * vm * (t₀ + 0) - 1 / K * v0 * (-q + 0)| ≤ δ
      ∧ |1 / K * vm * (t₀ + 0) - 1 / K * v1 * (-q + 0)| ≤ δ)
    ∧ (∀ s, tb ≤ s → s ≤ t3 →
        (5 * δ < 1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s)
          ∧ 1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s) < 2 * Real.pi - 5 * δ)
        ∧ (5 * δ < 1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s)
          ∧ 1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s) < 2 * Real.pi - 5 * δ))
    ∧ (|1 / K * vm * (t₀ + t4) - 1 / K * v0 * (-q + t4) - 2 * Real.pi| ≤ δ
      ∧ |1 / K * vm * (t₀ + t4) - 1 / K * v1 * (-q + t4) - 2 * Real.pi| ≤ δ) := by
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hX0 : 0 ≤ (vm - v0) / K := div_nonneg (by linarith) hK.le
  have hΔs : Δ ≤ 1 / 5200 := by linarith
  have hm : 0 ≤ 1 - 4 * Δ := by linarith
  have hp : 0 ≤ 1 + 4 * Δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := emission_angles (v1 := v1) hK ht0 hd hv hq (le_refl (0 : ℝ))
    have h1b := abs_le.1 h1
    constructor
    · rw [h0, mul_zero, abs_zero]
      exact hδ0.le
    · rw [abs_le]
      constructor <;> linarith [h1b.1, h1b.2]
  · intro s hbs hs3
    have hs0 : 0 ≤ s := htb.trans hbs
    obtain ⟨h0, h1⟩ := emission_angles (v1 := v1) hK ht0 hd hv hq hs0
    have h1b := abs_le.1 h1
    have m1 : (vm - v0) / K * tb ≤ (vm - v0) / K * s := mul_le_mul_of_nonneg_left hbs hX0
    have m2 : (vm - v0) / K * s ≤ (vm - v0) / K * t3 := mul_le_mul_of_nonneg_left hs3 hX0
    have m3 := mul_le_mul_of_nonneg_right m1 hm
    have m4 := mul_le_mul_of_nonneg_right m2 hp
    have n1 : 0 ≤ Δ * ((vm - v0) / K * tb) := mul_nonneg hΔ0 (mul_nonneg hX0 htb)
    have n2 : 0 ≤ Δ * ((vm - v0) / K * s) := mul_nonneg hΔ0 (mul_nonneg hX0 hs0)
    have n3 : 0 ≤ Δ * ((vm - v0) / K * t3) :=
      mul_nonneg hΔ0 (mul_nonneg hX0 (hs0.trans hs3))
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [h0]
      linarith
    · rw [h0]
      linarith
    · linarith [h1b.1]
    · linarith [h1b.2]
  · obtain ⟨h0, h1⟩ := emission_angles (v1 := v1) hK ht0 hd hv hq ht4
    rw [hut4] at h0 h1
    have h1b := abs_le.1 h1
    have hπΔ : Real.pi * Δ ≤ 3.15 * Δ := mul_le_mul_of_nonneg_right hπu.le hΔ0
    norm_num at hπΔ
    constructor
    · rw [h0, sub_self, abs_zero]
      exact hδ0.le
    · rw [abs_le]
      constructor <;> linarith [h1b.1, h1b.2]

/-! ### The budgets over a lap -/

variable {n N M : ℕ}

/-- **The two packets' budget over a lap**, for packet times within `30 K` of zero. -/
def lapBudget (n N : ℕ) (μ : ℝ) : ℝ :=
  2 / N + 1 / (2 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2) + 2 / μ * (1 / (10 * n))

/-- **The two budgets over a lap are at most `lapBudget`**, for packet times within `30 K` of
zero, `K = 1200 n N`. -/
theorem lap_budget_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2) {t t' : ℝ}
    (ht1 : |t| ≤ 30 * (1200 * (n : ℝ) * N)) (ht2 : |t'| ≤ 30 * (1200 * (n : ℝ) * N)) :
    (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) 0)).re
        + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
            (ringLen (1200 * n * N) / (M + 1 : ℕ)))
      + flatBudget n N t' ≤ lapBudget n N μ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have mb := flat_messenger_budget hn hN hM hμ0 (by linarith) t
  have hc1 : 0 ≤ 1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)) := by positivity
  have hinvμ : 1 ≤ 1 / μ := by
    rw [le_div_iff₀ hμ0]
    linarith
  have hX : 30 * (1200 * (n : ℝ) * N) * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)))
      = 1 / (10 * n) := by
    field_simp
    norm_num
  have hX0 : (0 : ℝ) ≤ 1 / (10 * n) := by positivity
  have hf1 := mul_le_mul_of_nonneg_right ht2 hc1
  rw [hX] at hf1
  have hm1 : |t| * (1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))))
      ≤ 1 / μ * (1 / (10 * n)) := by
    have h := mul_le_mul_of_nonneg_right ht1
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / μ) hc1)
    rw [← hX]
    linarith [h]
  have hcc : 1 / (4 * (1200 * (n : ℝ) * N) ^ 2)
      ≤ 1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2) := by
    refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
    have hμ2 : μ ^ 2 ≤ 1 := by nlinarith
    have hp : (0 : ℝ) ≤ 4 * (1200 * (n : ℝ) * N) ^ 2 := by positivity
    nlinarith
  have e1 : 1 / (2 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2)
      = 2 * (1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2)) := by
    field_simp
    ring
  have e2 : 2 / μ * (1 / (10 * (n : ℝ))) = 2 * (1 / μ * (1 / (10 * n))) := by ring
  have hXμ : 1 / (10 * (n : ℝ)) ≤ 1 / μ * (1 / (10 * n)) :=
    le_mul_of_one_le_left hX0 hinvμ
  have e3 : (2 : ℝ) / N = 1 / N + 1 / N := by ring
  rw [lapBudget, e1, e2, e3, flatBudget]
  linarith

/-! ### The radar reading of a lap, under seven scalar conditions -/

/-- **The two error terms of a lap are small**: with a strength `0 ≤ g ≤ R/5`, a rate
`R ≤ Δ`, `t_b ≤ 25 δ K`, `t₄ − t₃ ≤ 26 δ K` and `Δ δ K ≤ 1/1000`. -/
theorem lap_error_le {g R Δ δ K tb t3 t4 : ℝ} (hg0 : 0 ≤ g) (hg5 : g ≤ R / 5)
    (hRhi : R ≤ Δ) (htb0 : 0 ≤ tb) (h34 : t3 ≤ t4) (htb25 : tb ≤ 25 * δ * K)
    (h43 : t4 - t3 ≤ 26 * δ * K) (hclose : Δ * δ * K ≤ 1 / 1000) :
    6 * g * (tb - 0) + 7 / 2 ≤ 4 ∧ 6 * g * ((tb - 0) + (t4 - t3)) + 7 ≤ 8 := by
  have h1 : g * (tb + (t4 - t3)) ≤ Δ / 5 * (25 * δ * K + 26 * δ * K) :=
    mul_le_mul (hg5.trans (by linarith)) (by linarith) (by linarith) (by linarith)
  have h0 : g * tb ≤ g * (tb + (t4 - t3)) :=
    mul_le_mul_of_nonneg_left (by linarith) hg0
  constructor <;> linarith

/-- **The first flow time at which the messenger is certified away from the clock.** -/
def lapTb (n N : ℕ) (μ Δ δ : ℝ) : ℝ :=
  6 * δ / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 - 4 * Δ))

/-- **The last flow time at which the messenger is certified away from the clock.** -/
def lapT3 (n N : ℕ) (μ Δ δ : ℝ) : ℝ :=
  (2 * Real.pi - 6 * δ)
    / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 + 4 * Δ))

/-- **The flow time at which the messenger has come round the ring** to the clock's lower
level. -/
def lapT4 (n N : ℕ) (μ : ℝ) : ℝ :=
  2 * Real.pi / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N))

/-- ★★★ **The radar reading of a lap, under seven scalar conditions.** The flat clock packet
of #392 with gap `Δ` and a flat messenger of rest energy `0 < μ ≤ 1/2` on the same ring and
window, the messenger starting where the clock's lower level is; both gates of "within the
angle `3δ`" in one run; `K = 1200 n N`. If `1 ≤ Δ K`, `8 ≤ δ K`, `52 Δ ≤ δ ≤ 1/100`,
`lapBudget ≤ ε δ²/5`, `Δ δ K ≤ 1/1000`, `Δ K ε ≤ 1/1000` and `18 Δ K ≤ n`, then for some
strength `0 < g ≤ R/5`: the three flow times are ordered, `R (lapT3 − lapTb) ≥ (5/2) Δ K`,
at every flow time of `[lapTb, lapT3]` the first pointer has a count `N_e` with
`2π N_e ≤ 8π`, and at `lapT4` the last pointer has a count `N_r` with
`|2π N_r − R (lapT3 − lapTb)| ≤ 16π`. -/
theorem lap_radar_reading (hn : 4 ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2) {a b : ℕ} (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 100) (hΔK : 1 ≤ Δ * (1200 * (n : ℝ) * N))
    (hres : 8 ≤ δ * (1200 * (n : ℝ) * N)) (hΔδ : 52 * Δ ≤ δ)
    (hB : lapBudget n N μ ≤ ε * (δ ^ 2 / 5))
    (hclose : Δ * δ * (1200 * (n : ℝ) * N) ≤ 1 / 1000)
    (hE : Δ * (1200 * (n : ℝ) * N) * ε ≤ 1 / 1000)
    (hH : 18 * (Δ * (1200 * (n : ℝ) * N)) ≤ n) :
    ∃ (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) (emT0 n N M Δ μ) ≠ 0) (g : ℝ)
        (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ 0 ≤ lapTb n N μ Δ δ ∧ lapTb n N μ Δ δ ≤ lapT3 n N μ Δ δ
      ∧ lapT3 n N μ Δ δ ≤ lapT4 n N μ
      ∧ 5 / 2 * (Δ * (1200 * (n : ℝ) * N))
          ≤ ringRate (1200 * n * N) M (1 / 2) Δ * (lapT3 n N μ Δ δ - lapTb n N μ Δ δ)
      ∧ ∀ s, lapTb n N μ Δ δ ≤ s → s ≤ lapT3 n N μ Δ δ →
          ∃ Ne Nr : ℕ,
            IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ readyArc 2}
                {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ displayArc}
                (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) (3 * δ) g
                  (chainRay _ hψ) (deviceRay _ hΨ)) s Ne
              ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
                  {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
                  (ringReturnRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) (3 * δ) g
                    (chainRay _ hψ) (deviceRay _ hΨ)) (lapT4 n N μ) Nr
              ∧ (Ne : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi * 4
              ∧ |(Nr : ℝ) * (2 * Real.pi)
                    - ringRate (1200 * n * N) M (1 / 2) Δ
                      * (lapT3 n N μ Δ δ - lapTb n N μ Δ δ)|
                  ≤ 2 * Real.pi * 8 := by
  have hπ := Real.pi_pos
  have hπl : 3 < Real.pi := Real.pi_gt_three
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < 1200 * n * N := by positivity
  have hKr : ((1200 * n * N : ℕ) : ℝ) = 1200 * n * N := by push_cast; ring
  have hK0 : (0 : ℝ) < 1200 * n * N := by positivity
  have hfac : 2 * Real.pi / ringLen (1200 * n * N) = 1 / (1200 * (n : ℝ) * N) := by
    rw [ringLen, hKr]
    field_simp
  have hWD : ∀ m ∈ flatWindow n N,
      |2 * Real.pi * m / ringLen (1200 * n * N) - 1 / 2| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      field_simp
    rw [e]
    exact flatWindow_width hnpos hN m hm
  have hP : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hD0 : (0 : ℝ) ≤ 1 / (600 * n) := by positivity
  have hψ := ringPacket_ne_zero (M := M) one_pos hμ0 (ringLen_pos hK) hP hD0
    (flatWindow_mem_range hnpos hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) (emT0 n N M Δ μ)
  have hΔs : Δ ≤ 1 / 5200 := by linarith
  have hΔ2 : Δ ≤ 1 / 2 := by linarith
  -- the clock's rate
  have hRlo : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hRhi : ringRate (1200 * n * N) M (1 / 2) Δ ≤ Δ := levelClockRate_le_gap hΔ0.le _
  have hT0 : emT0 n N M Δ μ = -(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)
      * (vRel 1 1 (1 / 2) / vRel 1 μ (1 / 2))) := rfl
  have hTb : lapTb n N μ Δ δ = 6 * δ
      / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 - 4 * Δ)) := rfl
  have hT3 : lapT3 n N μ Δ δ = (2 * Real.pi - 6 * δ)
      / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 + 4 * Δ)) := rfl
  have hT4 : lapT4 n N μ = 2 * Real.pi
      / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N)) := rfl
  -- the velocities
  obtain ⟨hvm7, hvm1, -⟩ := vRel_half_light hμ0 hμ
  obtain ⟨hv00, hv09⟩ := vRel_half_one
  have hv1 : |vRel 1 (1 + Δ) (1 / 2) - vRel 1 1 (1 / 2)| ≤ Δ := by
    have h := abs_vRel_sub_le (c := 1) zero_le_one one_pos (μ₀ := 1) (μ₁ := 1 + Δ)
      (by linarith) (1 / 2)
    have e : (1 : ℝ) * (1 + Δ - 1) / 1 = Δ := by ring
    rwa [e] at h
  generalize hRd : ringRate (1200 * n * N) M (1 / 2) Δ = R at *
  generalize hvmd : vRel 1 μ (1 / 2) = vm at *
  generalize hv0d : vRel 1 1 (1 / 2) = v0 at *
  generalize hv1d : vRel 1 (1 + Δ) (1 / 2) = v1 at *
  generalize ht0d : emT0 n N M Δ μ = t₀ at *
  generalize htbd : lapTb n N μ Δ δ = tb at *
  generalize ht3d : lapT3 n N μ Δ δ = t3 at *
  generalize ht4d : lapT4 n N μ = t4 at *
  have hR0 : 0 < R := by linarith
  have hd : 1 / 4 ≤ vm - v0 := by linarith
  have hd1 : vm - v0 ≤ 1 := by linarith
  have hvm0 : 0 < vm := by linarith
  have hq0 : 0 < Real.pi / (2 * R) := by positivity
  have hq4 : Real.pi / (2 * R) ≤ 4 / Δ := by
    have hπ4 : Real.pi ≤ 4 := by
      have h := Real.pi_lt_d2
      norm_num at h
      linarith
    have h1 := mul_le_mul_of_nonneg_right hπ4 hΔ0.le
    rw [div_le_div_iff₀ (by positivity) hΔ0]
    linarith
  have h4Δ : 4 / Δ ≤ 4 * (1200 * (n : ℝ) * N) := by
    rw [div_le_iff₀ hΔ0]
    linarith
  generalize hqd : Real.pi / (2 * R) = q at *
  generalize hKd : 1200 * (n : ℝ) * N = K at *
  have hΔq : Δ * q ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hq4 hΔ0.le
    have e : Δ * (4 / Δ) = 4 := by field_simp
    rwa [e] at h
  have he : Δ * q / K ≤ δ / 2 := by
    rw [div_le_iff₀ hK0]
    linarith
  have hvt0 : vm * t₀ = -(q * v0) := by
    rw [hT0]
    field_simp
  have hr0 : 0 ≤ v0 / vm := div_nonneg hv00.le hvm0.le
  have hr1 : v0 / vm ≤ 1 := (div_le_one hvm0).2 (by linarith)
  have ht0lo : -q ≤ t₀ := by
    have h := mul_le_mul_of_nonneg_left hr1 hq0.le
    rw [hT0]
    linarith
  have ht0hi : t₀ ≤ 0 := by
    have h := mul_nonneg hq0.le hr0
    rw [hT0]
    linarith
  -- the flow times
  obtain ⟨htb0, hb3, h34, htb25, ht426, h5K, h43, hutb, hut3, hut4⟩ :
      0 ≤ tb ∧ tb ≤ t3 ∧ t3 ≤ t4 ∧ tb ≤ 25 * δ * K ∧ t4 ≤ 26 * K ∧ 5 * K ≤ t3 - tb
      ∧ t4 - t3 ≤ 26 * δ * K
      ∧ (vm - v0) / K * tb * (1 - 4 * Δ) = 6 * δ
      ∧ (vm - v0) / K * t3 * (1 + 4 * Δ) = 2 * Real.pi - 6 * δ
      ∧ (vm - v0) / K * t4 = 2 * Real.pi := by
    rw [hTb, hT3, hT4]
    exact lap_times hK0 hd hd1 hΔ0.le hΔδ hδ0 hδ
  have ht30 : 0 ≤ t3 := htb0.trans hb3
  have ht40 : 0 ≤ t4 := ht30.trans h34
  have hBpos : 0 < lapBudget n N μ := by
    unfold lapBudget
    positivity
  have hε0 : 0 ≤ ε :=
    nonneg_of_mul_nonneg_left (hBpos.le.trans hB) (by positivity)
  -- the size of the reading
  have hY : 5 / 2 * (Δ * K) ≤ R * (t3 - tb) :=
    calc 5 / 2 * (Δ * K) = Δ / 2 * (5 * K) := by ring
      _ ≤ R * (t3 - tb) := mul_le_mul hRlo h5K (by positivity) hR0.le
  -- the horizon
  have ht3T : t3 ≤ 2 * Real.pi * n / (4 * R) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : t3 * R ≤ 26 * K * Δ := mul_le_mul (h34.trans ht426) hRhi hR0.le (by positivity)
    have h3 := mul_pos hn0 (sub_pos.2 hπl)
    linarith
  -- the three size conditions
  have hRtb : R * tb ≤ Δ * (25 * δ * K) := mul_le_mul hRhi htb25 htb0 hΔ0.le
  have hRt3 : R * (t3 - tb) ≤ Δ * (26 * K) :=
    mul_le_mul hRhi (by linarith) (by linarith) hΔ0.le
  have hS : 2 * (R / 5) * (ε * 0 + (tb - 0) + ε * (t3 - tb)) ≤ 1 / 48 := by
    have h2 := mul_le_mul_of_nonneg_left hRt3 hε0
    linarith
  have hphase : 1 / 6 < |Real.cos (R * 0)| := by
    rw [mul_zero, Real.cos_zero, abs_one]
    norm_num
  have hS4 : 2 * (R / 5) * ε * (t4 - t4) ≤ 1 / 6 := by
    rw [sub_self, mul_zero]
    norm_num
  -- the budgets
  have hbudget : ∀ s, 0 ≤ s → s ≤ t4 →
      (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
            (flatAmpN N) 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-q + s) ≤ ε * (1 - Real.cos δ) := by
    intro s hs0 hs
    have ht1 : |t₀ + s| ≤ 30 * (1200 * (n : ℝ) * N) := by
      rw [hKd, abs_le]
      constructor <;> linarith
    have ht2 : |-q + s| ≤ 30 * (1200 * (n : ℝ) * N) := by
      rw [hKd, abs_le]
      constructor <;> linarith
    have hcos := mul_le_mul_of_nonneg_left
      (sq_div_five_le_one_sub_cos (δ := δ) (by rw [abs_of_pos hδ0]; linarith)) hε0
    exact ((lap_budget_le hnpos hN hM hμ0 hμ ht1 ht2).trans hB).trans hcos
  -- the predicted angles
  obtain ⟨⟨a0, a1⟩, hmid, ⟨c0, c1⟩⟩ := lap_angles (v1 := v1) hK0 hvt0 hd hv1 hq0.le hΔ0.le
    hΔδ hδ0 hδ he hutb hut3 hut4 htb0 ht40
  have hnear0 : ∀ s, 0 ≤ s → s ≤ 0 →
      Real.cos (3 * δ - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v0 * (-q + s))
        ∧ Real.cos (3 * δ - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v1 * (-q + s)) := by
    intro s hs0 hs
    obtain rfl : s = 0 := le_antisymm hs hs0
    rw [hfac]
    exact ⟨cos_le_cos_of_abs_le (by linarith) (by linarith),
      cos_le_cos_of_abs_le (by linarith) (by linarith)⟩
  have hapart : ∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v0 * (-q + s))
          < Real.cos (3 * δ + 2 * δ)
        ∧ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v1 * (-q + s))
          < Real.cos (3 * δ + 2 * δ) := by
    intro s hbs hs
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩⟩ := hmid s hbs hs
    rw [hfac]
    exact ⟨cos_lt_cos_of_between (by linarith) (by linarith) (by linarith),
      cos_lt_cos_of_between (by linarith) (by linarith) (by linarith)⟩
  have hnear1 : ∀ s, t4 ≤ s → s ≤ t4 →
      Real.cos (3 * δ - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v0 * (-q + s))
        ∧ Real.cos (3 * δ - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v1 * (-q + s)) := by
    intro s hs4 hs
    obtain rfl : s = t4 := le_antisymm hs hs4
    rw [hfac]
    constructor
    · rw [← Real.cos_sub_two_pi (1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s))]
      exact cos_le_cos_of_abs_le (by linarith) (by linarith)
    · rw [← Real.cos_sub_two_pi (1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s))]
      exact cos_le_cos_of_abs_le (by linarith) (by linarith)
  have hw1 : 2 * δ ≤ 3 * δ := by linarith
  have hw2 : 3 * δ + 2 * δ ≤ Real.pi := by linarith
  have hfin : ∀ g : ℝ, 0 ≤ g → g ≤ R / 5 →
      6 * g * (tb - 0) + 7 / 2 ≤ 4 ∧ 6 * g * ((tb - 0) + (t4 - t3)) + 7 ≤ 8 :=
    fun g hg0 hg5 => lap_error_le hg0 hg5 hRhi htb0 h34 htb25 h43 hclose
  subst hKd hqd ht4d ht3d htbd ht0d hv1d hv0d hvmd hRd
  obtain ⟨g, hΨ, hg0, hg5, H⟩ :=
    flat_clock_radar_reading hn hN hM hΔ0 hΔ2 e₁ e₂ hμ0 hP hD0
      (flatWindow_mem_range hnpos hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) _ hψ
      (w := 3 * δ) (δ := δ) (ε := ε) hδ0 hw1 hw2 hε0 le_rfl htb0 hb3 h34 le_rfl ht3T hbudget
      hnear0 hapart hnear1 hS hphase hS4
  refine ⟨hψ, g, hΨ, hg0, hg5, htb0, hb3, h34, hY, fun s hs1 hs2 => ?_⟩
  obtain ⟨Ne, Nr, hNe, hNr, be, br, -, -⟩ := H s hs1 hs2 _ le_rfl le_rfl
  refine ⟨Ne, Nr, hNe, hNr, ?_, br.trans
    (mul_le_mul_of_nonneg_left (hfin g hg0.le hg5).2 (by positivity))⟩
  rw [mul_zero, sub_zero] at be
  exact (le_abs_self _).trans
    (be.trans (mul_le_mul_of_nonneg_left (hfin g hg0.le hg5).1 (by positivity)))

/-! ### A family -/

/-- The family's momentum-width index and number of modes: `10¹¹ k³`. -/
def lapn (k : ℕ) : ℕ := 10 ^ 11 * k ^ 3

/-- The family's level gap: `k/K`, `K = 1200 n N`. -/
def lapGap (k : ℕ) : ℝ := k / (1200 * (lapn k : ℝ) * lapn k)

/-- **The family meets the seven scalar conditions.** -/
theorem lap_family_conditions {k : ℕ} (hk : 0 < k) :
    0 < lapGap k
    ∧ 1 ≤ lapGap k * (1200 * (lapn k : ℝ) * lapn k)
    ∧ 8 ≤ 1 / (1000 * (k : ℝ)) * (1200 * (lapn k : ℝ) * lapn k)
    ∧ 52 * lapGap k ≤ 1 / (1000 * (k : ℝ))
    ∧ lapBudget (lapn k) (lapn k) (1 / 2)
        ≤ 1 / (1000 * (k : ℝ)) * ((1 / (1000 * (k : ℝ))) ^ 2 / 5)
    ∧ lapGap k * (1 / (1000 * (k : ℝ))) * (1200 * (lapn k : ℝ) * lapn k) ≤ 1 / 1000
    ∧ lapGap k * (1200 * (lapn k : ℝ) * lapn k) * (1 / (1000 * (k : ℝ))) ≤ 1 / 1000
    ∧ 18 * (lapGap k * (1200 * (lapn k : ℝ) * lapn k)) ≤ lapn k
    ∧ lapGap k * (1200 * (lapn k : ℝ) * lapn k) = k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hn : ((lapn k : ℕ) : ℝ) = 10 ^ 11 * (k : ℝ) ^ 3 := by
    rw [lapn]
    push_cast
    ring
  rw [lapBudget, lapGap, hn]
  generalize (k : ℝ) = X at *
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hk1
  have hX6 : 1 ≤ X ^ 6 := one_le_pow₀ hk1
  have hX36 : X ^ 3 ≤ X ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  have hX26 : X ^ 2 ≤ X ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  have hX13 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := pow_le_pow_right₀ hk1 (by norm_num)
  have hX312 : X ^ 3 ≤ X ^ 12 := pow_le_pow_right₀ hk1 (by norm_num)
  have hX5 : 1 ≤ X ^ 5 := one_le_pow₀ hk1
  have eK : X / (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3))
      * (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3)) = X := by
    field_simp
  refine ⟨by positivity, by rw [eK]; exact hk1, ?_, ?_, ?_, ?_, ?_, ?_, eK⟩
  · have e : 1 / (1000 * X) * (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3))
        = 12 * 10 ^ 21 * X ^ 5 := by
      field_simp
      ring
    rw [e]
    nlinarith
  · rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hk0 6]
  · have t1 : (2 : ℝ) / (10 ^ 11 * X ^ 3) = 2 / 10 ^ 11 * (1 / X ^ 3) := by
      field_simp
    have t2 : 1 / (2 * (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3)) ^ 2 * (1 / 2 : ℝ) ^ 2)
        ≤ 1 / 10 ^ 11 * (1 / X ^ 3) := by
      have e : 2 * (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3)) ^ 2 * (1 / 2 : ℝ) ^ 2
          = 72 * 10 ^ 48 * X ^ 12 := by ring
      have e2 : 1 / 10 ^ 11 * (1 / X ^ 3) = 1 / (10 ^ 11 * X ^ 3) := by
        field_simp
      rw [e, e2]
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    have t3 : 2 / (1 / 2 : ℝ) * (1 / (10 * (10 ^ 11 * X ^ 3)))
        = 4 / 10 ^ 12 * (1 / X ^ 3) := by
      field_simp
      norm_num
    have t4 : 1 / (1000 * X) * ((1 / (1000 * X)) ^ 2 / 5) = 1 / (5 * 10 ^ 9) * (1 / X ^ 3) := by
      field_simp
      norm_num
    have h5 : 0 ≤ 1 / X ^ 3 := by positivity
    rw [t1, t3, t4]
    nlinarith
  · have e : X / (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3)) * (1 / (1000 * X))
          * (1200 * (10 ^ 11 * X ^ 3) * (10 ^ 11 * X ^ 3)) = 1 / 1000 := by
      field_simp
    rw [e]
  · rw [eK]
    have e : X * (1 / (1000 * X)) = 1 / 1000 := by field_simp
    rw [e]
  · rw [eK]
    nlinarith

/-- ★★★ **A family of runs with a return and a quickly closing gate.** For every `k ≥ 1`, on
any ring with `M ≥ 210000 n² N` sites, `n = N = 10¹¹ k³`, gap `k/K`, a flat messenger of rest
energy `1/2` starting with the clock, the gate "within the angle `3/(1000 k)`", both gates in
one run: for some strength `g > 0` the time away is at least `(5/2) k` in the clock's phase,
at every flow time of `[lapTb, lapT3]` the first pointer has a count `N_e` with
`2π N_e ≤ 8π`, and at `lapT4` the last pointer has a count `N_r` with
`|2π N_r − R (lapT3 − lapTb)| ≤ (21/k) · R (lapT3 − lapTb)`. -/
theorem lap_radar_family (k : ℕ) (hk : 0 < k) {M : ℕ}
    (hM : 210000 * lapn k ^ 2 * lapn k ≤ M) {a b : ℕ}
    (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) :
    ∃ (hψ : ringPacket (L := M + 1) 1 (1 / 2) (ringLen (1200 * lapn k * lapn k))
          (flatWindow (lapn k) (lapn k)) (flatAmpN (lapn k))
          (emT0 (lapn k) (lapn k) M (lapGap k) (1 / 2)) ≠ 0) (g : ℝ)
        (hΨ : devicePacket (L := M + 1) (ringHop (1200 * lapn k * lapn k) M) 1 (1 + lapGap k)
          (flatWindow (lapn k) (lapn k)) (flatAmpN (lapn k))
          (-(Real.pi / (2 * ringRate (1200 * lapn k * lapn k) M (1 / 2) (lapGap k)))) ≠ 0),
      0 < g
      ∧ lapTb (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
          ≤ lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
      ∧ lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
          ≤ lapT4 (lapn k) (lapn k) (1 / 2)
      ∧ 5 / 2 * (k : ℝ) ≤ ringRate (1200 * lapn k * lapn k) M (1 / 2) (lapGap k)
          * (lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
            - lapTb (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k)))
      ∧ ∀ s, lapTb (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k)) ≤ s →
          s ≤ lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k)) →
          ∃ Ne Nr : ℕ,
            IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ readyArc 2}
                {x : EchoSigma (a * (b + 1) + b) | x.1.2 ∈ displayArc}
                (ringReturnRun e₁ e₂ (ringHop (1200 * lapn k * lapn k) M) (1 / 2) 1
                  (1 + lapGap k) (3 * (1 / (1000 * k))) g (chainRay _ hψ) (deviceRay _ hΨ))
                s Ne
              ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
                  {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
                  (ringReturnRun e₁ e₂ (ringHop (1200 * lapn k * lapn k) M) (1 / 2) 1
                    (1 + lapGap k) (3 * (1 / (1000 * k))) g (chainRay _ hψ) (deviceRay _ hΨ))
                  (lapT4 (lapn k) (lapn k) (1 / 2)) Nr
              ∧ (Ne : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi * 4
              ∧ |(Nr : ℝ) * (2 * Real.pi)
                    - ringRate (1200 * lapn k * lapn k) M (1 / 2) (lapGap k)
                      * (lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
                        - lapTb (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k)))|
                  ≤ 21 / k * (ringRate (1200 * lapn k * lapn k) M (1 / 2) (lapGap k)
                      * (lapT3 (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k))
                        - lapTb (lapn k) (lapn k) (1 / 2) (lapGap k) (1 / (1000 * k)))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, cK⟩ := lap_family_conditions hk
  have hn4 : 4 ≤ lapn k := by
    have h1 : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ hk
    rw [lapn]
    nlinarith
  have hn0 : 0 < lapn k := by omega
  have hδ0 : (0 : ℝ) < 1 / (1000 * (k : ℝ)) := by positivity
  have hδ : 1 / (1000 * (k : ℝ)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨hψ, g, hΨ, hg0, -, -, hb3, h34, hY, H⟩ := lap_radar_reading (M := M) hn4 hn0 hM c0
    (μ := 1 / 2) (by norm_num) le_rfl e₁ e₂ (δ := 1 / (1000 * (k : ℝ)))
    (ε := 1 / (1000 * (k : ℝ))) hδ0 hδ c1 c2 c3 c4 c5 c6 c7
  rw [cK] at hY
  refine ⟨hψ, g, hΨ, hg0, hb3, h34, hY, fun s hs1 hs2 => ?_⟩
  obtain ⟨Ne, Nr, hNe, hNr, be, br⟩ := H s hs1 hs2
  refine ⟨Ne, Nr, hNe, hNr, be, br.trans ?_⟩
  have h1 : 21 / (k : ℝ) * (5 / 2 * (k : ℝ)) = 105 / 2 := by field_simp; norm_num
  have h2 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 21 / (k : ℝ))
  rw [h1] at h2
  linarith

end CSD.RecordLayer

end
