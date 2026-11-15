/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedEmissionReading

/-!
# Values for the emission reading: a fast messenger and a family with a shrinking error

**Category:** 7-SigmaLayer (the record layer). BACKLOG #397 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, seventh brick: Remainder (c) of #396, values. No new assumption beyond UA-18.

#396 (`flat_clock_emission_reading`) reads a gated pointer under inequalities between real
numbers and shows no values meeting them. This module exhibits values: a messenger whose
velocity tends to `1`, and a family of runs along which the reading's relative error tends to
zero.

* `sq_div_five_le_one_sub_cos`, `cos_le_cos_of_abs_le`, `cos_lt_cos_of_between`;
* ★ `vRel_half_light` — at the momentum `1/2` a rest energy `0 < μ ≤ 1/2` gives a velocity
  between `7/10` and `1` and within `2μ²` of `1`; `vRel_half_one`;
* `emission_times`, `emission_angles`, `emission_angles_near`, `emission_angles_apart` — the kinematics of
  two packets on the ring, in real numbers: the flow times `t_a`, `t_b` and the differences
  of the predicted angles before `t_a` and on `[t_b, (3/2) t_b]`;
* `limitErr_le_inv_mul`, ★ `flat_messenger_budget` — the flat messenger's budget for a rest
  energy `0 < μ ≤ 1`: `1/N + 1/(4 K² μ²) + |t|/(μ · 360000 n² N)`;
* `emT0`, `emTa`, `emTb`, `emBudget`, `emission_budget_le`;
* ★★★ `light_messenger_emission_reading` — the reading of #396 for the flat clock packet and
  a light flat messenger, under four scalar conditions: `800 Δ N ≤ 1`, `1 ≤ 150 n N δ`,
  `emBudget ≤ ε δ²/5`, `1920 Δ n N ε < 1/24`. At every flow time of `[t_b, (3/2) t_b]` the
  count `N'` has `|2π N' − R t_a| ≤ 2π ((22 δ + 29 Δ) R t_a + 7/2)`, and `R t_a ≥ 300 Δ n N`;
* `emn`, `emN`, `emGap`, `emBudget_family_le`, `emission_family_error`;
* ★★★ `emission_reading_family` — for every `k ≥ 1`, with `n = 10⁷ k⁴`, `N = 2 · 10⁸ k³`,
  `Δ = k/(n N)`, the messenger's rest energy `1/(2k)` and the resolution `1/(10k)`: the
  messenger's velocity is within `1/(2k²)` of `1`, `R t_a ≥ 300 k`, and at every flow time
  of `[t_b, (3/2) t_b]` the gated pointer's count `N'` has `|2π N' − R t_a| ≤ (15/k) R t_a`.
  The only hypothesis left is the size of the ring.

## Exact scope

* **What the family shows.** The inequalities of #396 can be met, with a messenger whose
  velocity tends to `1` and with a relative error of the count that tends to zero. The count
  is at least about `47 k` ticks. This was the open question after #396; it is decided for
  the ring with two carriers and for nothing else.
* **The messenger's velocity is a property of its packet, not a recorded speed.**
  `vRel 1 μ (1/2)` is the continuum velocity at the reference momentum; it enters only
  through the predicted angles of #395, where the packet's weight is shown to be. No record
  holds a speed, and no hypothesis states one.
* **The count is compared with the flow time `t_a`** (UA-7), which is fixed by the two
  packets' velocities and the gate's width. Nothing is recorded at `t_a`. The reading is not
  yet that of an emission: on the ring the two start together and separate once.
* **The window is `[t_b, (3/2) t_b]`.** Nothing is said after it; on the ring the messenger
  comes round again.
* **The system grows with `k`.** The ring has more than `210000 n² N ≈ 4 · 10²⁷ k¹¹` sites,
  the clock's gap falls as `k⁻⁶` and the flow times grow as `k⁷`. The error `15/k` is bought
  with all of these, and the constants are not sharp. Each `k` is a different generator, not
  one system with different starts.
* **For some strength, one fibre, product starts**, as #396: the strength is tuned to the
  clock packet (UA-4); only the fibres where both profiles vanish; null sets.
* **A ring and two carriers; the gate's width is the angle `1`.** UA-18 has a chain with
  walls and three carriers. The values here will not carry over unchanged.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-18, UO-16, UD-150, UD-151, UD-152, UD-153, UD-154);
`RecordLayer/UnifiedEmissionReading.lean` (#396: `flat_clock_emission_reading`,
`ringGateRun`); `RecordLayer/UnifiedGateRegions.lean` (#395: `flatBudget`,
`ringPacket_ne_zero`); `RecordLayer/UnifiedClockPacketLocalised.lean` (#392:
`flat_packet_limitErr_le`, `flatWindow`, `flatAmpN`);
`RecordLayer/UnifiedClockPacketInstance.lean` (#391: `ringRate`, `half_le_levelClockRate`,
`levelClockRate_le_gap`); `RecordLayer/DiracArrival.lean` (#265:
`re_transPhase_ringPacket_ge`); `CV/DiracPacketLimit.lean` (#261: `limitErr`, `flat_sums`);
`CV/DiracClockChain.lean` (`vRel`, `dispE`, `abs_vRel_lt`); `CV/DiracDevice.lean`
(`abs_vRel_sub_le`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### Cosines -/

/-- `δ²/5 ≤ 1 − cos δ` for `|δ| ≤ π`. -/
theorem sq_div_five_le_one_sub_cos {δ : ℝ} (hδ : |δ| ≤ Real.pi) :
    δ ^ 2 / 5 ≤ 1 - Real.cos δ := by
  have h := Real.cos_le_one_sub_mul_cos_sq hδ
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ2 : Real.pi ^ 2 ≤ 10 := by
    norm_num at hπu
    nlinarith
  have h2 : 1 / 5 ≤ 2 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have h3 : 1 / 5 * δ ^ 2 ≤ 2 / Real.pi ^ 2 * δ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg δ)
  linarith

/-- An angle within `y ≤ π` of `0` has cosine at least `cos y`. -/
theorem cos_le_cos_of_abs_le {x y : ℝ} (h : |x| ≤ y) (hy : y ≤ Real.pi) :
    Real.cos y ≤ Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hy h

/-- An angle strictly between `a` and `2π − a` has cosine below `cos a`. -/
theorem cos_lt_cos_of_between {x a : ℝ} (ha : 0 ≤ a) (h1 : a < x)
    (h2 : x < 2 * Real.pi - a) : Real.cos x < Real.cos a := by
  by_cases hx : x ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi ha hx h1
  · rw [← Real.cos_two_pi_sub x]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi ha (by linarith) (by linarith)

/-! ### Velocities at the momentum `1/2` -/

/-- **A light messenger is fast**: for a rest energy `0 < μ ≤ 1/2` at the momentum `1/2` the
velocity is between `7/10` and `1`, and within `2μ²` of `1`. -/
theorem vRel_half_light {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2) :
    7 / 10 ≤ vRel 1 μ (1 / 2) ∧ vRel 1 μ (1 / 2) ≤ 1 ∧ 1 - 2 * μ ^ 2 ≤ vRel 1 μ (1 / 2) := by
  have hE := dispE_pos hμ0 (1 / 2)
  have hμ2 : μ ^ 2 ≤ 1 / 4 := by nlinarith
  have hE1 : dispE μ (1 / 2) ≤ 5 / 7 := by
    rw [dispE, Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hE2 : dispE μ (1 / 2) ≤ 1 / 2 + μ ^ 2 := by
    rw [dispE, Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg (μ ^ 2)]
  have hlt := (abs_lt.1 (abs_vRel_lt one_pos hμ0 (1 / 2))).2
  refine ⟨?_, hlt.le, ?_⟩
  · rw [vRel, le_div_iff₀ hE]
    linarith
  · rw [vRel, le_div_iff₀ hE]
    have h0 : 0 ≤ 1 - 2 * μ ^ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hE2 h0, sq_nonneg (μ ^ 2)]

/-- The clock's lower level at the momentum `1/2` moves at a velocity in `(0, 9/20]`. -/
theorem vRel_half_one : 0 < vRel 1 1 (1 / 2) ∧ vRel 1 1 (1 / 2) ≤ 9 / 20 := by
  have hE := dispE_pos (μ := 1) one_pos (1 / 2)
  have hE1 : 10 / 9 ≤ dispE 1 (1 / 2) := by
    rw [dispE]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  constructor
  · rw [vRel]
    positivity
  · rw [vRel, div_le_iff₀ hE]
    linarith

/-! ### Kinematics of the two packets -/

/-- **The two flow times.** With the relative angular velocity `d/K`, `1/4 ≤ d ≤ 1`: the last
flow time `t_a` at which the centres are within `1 − 3δ` with the margin `4Δ`, and the first
`t_b` at which they are `1 + 3δ` apart with that margin. -/
theorem emission_times {K d Δ δ : ℝ} (hK : 0 < K) (hd : 1 / 4 ≤ d) (hd1 : d ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1 / 16) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) :
    0 ≤ (1 - 3 * δ) / (d / K * (1 + 4 * Δ))
    ∧ (1 - 3 * δ) / (d / K * (1 + 4 * Δ)) ≤ (1 + 3 * δ) / (d / K * (1 - 4 * Δ))
    ∧ (1 - 3 * δ) / (d / K * (1 + 4 * Δ)) ≤ 4 * K
    ∧ (1 + 3 * δ) / (d / K * (1 - 4 * Δ)) ≤ 7 * K
    ∧ 14 / 25 * K ≤ (1 - 3 * δ) / (d / K * (1 + 4 * Δ))
    ∧ (1 + 3 * δ) / (d / K * (1 - 4 * Δ)) - (1 - 3 * δ) / (d / K * (1 + 4 * Δ))
        ≤ (18 * δ + 24 * Δ) * ((1 - 3 * δ) / (d / K * (1 + 4 * Δ)))
    ∧ d / K * ((1 - 3 * δ) / (d / K * (1 + 4 * Δ))) * (1 + 4 * Δ) = 1 - 3 * δ
    ∧ d / K * ((1 + 3 * δ) / (d / K * (1 - 4 * Δ))) * (1 - 4 * Δ) = 1 + 3 * δ := by
  have hd0 : 0 < d := by linarith
  have h1 : 0 < 1 + 4 * Δ := by linarith
  have h2 : 0 < 1 - 4 * Δ := by linarith
  set A := (1 - 3 * δ) / (1 + 4 * Δ) with hAd
  set B := (1 + 3 * δ) / (1 - 4 * Δ) with hBd
  set m := K / d with hmd
  have hm0 : 0 < m := div_pos hK hd0
  have hA1 : A * (1 + 4 * Δ) = 1 - 3 * δ := div_mul_cancel₀ _ h1.ne'
  have hB1 : B * (1 - 4 * Δ) = 1 + 3 * δ := div_mul_cancel₀ _ h2.ne'
  have hAlo : 14 / 25 ≤ A := by
    rw [hAd, le_div_iff₀ h1]
    linarith
  have hAhi : A ≤ 1 := by
    rw [hAd, div_le_one h1]
    linarith
  have hBhi : B ≤ 26 / 15 := by
    rw [hBd, div_le_iff₀ h2]
    linarith
  have hBlo : 1 ≤ B := by
    rw [hBd, one_le_div h2]
    linarith
  have hpoly : (1 + 3 * δ) * (1 + 4 * Δ)
      ≤ (1 + 18 * δ + 24 * Δ) * (1 - 3 * δ) * (1 - 4 * Δ) := by
    nlinarith [mul_nonneg hδ0 hΔ0, mul_nonneg hδ0 hδ0, mul_nonneg hΔ0 hΔ0,
      mul_nonneg hδ0 (sub_nonneg.2 hδ), mul_nonneg hΔ0 (sub_nonneg.2 hΔ),
      mul_nonneg hδ0 (sub_nonneg.2 hΔ), mul_nonneg hΔ0 (sub_nonneg.2 hδ),
      mul_nonneg (mul_nonneg hδ0 hΔ0) (sub_nonneg.2 hδ),
      mul_nonneg (mul_nonneg hδ0 hΔ0) (sub_nonneg.2 hΔ)]
  have hBA : B ≤ (1 + 18 * δ + 24 * Δ) * A := by
    have h12 : 0 < (1 - 4 * Δ) * (1 + 4 * Δ) := mul_pos h2 h1
    refine le_of_mul_le_mul_right ?_ h12
    have e1 : B * ((1 - 4 * Δ) * (1 + 4 * Δ)) = (1 + 3 * δ) * (1 + 4 * Δ) := by
      rw [← mul_assoc, hB1]
    have e2 : (1 + 18 * δ + 24 * Δ) * A * ((1 - 4 * Δ) * (1 + 4 * Δ))
        = (1 + 18 * δ + 24 * Δ) * (1 - 3 * δ) * (1 - 4 * Δ) := by
      rw [← hA1]
      ring
    rw [e1, e2]
    exact hpoly
  have hmlo : K ≤ m := by
    rw [hmd, le_div_iff₀ hd0]
    nlinarith
  have hmhi : m ≤ 4 * K := by
    rw [hmd, div_le_iff₀ hd0]
    nlinarith
  have eta : (1 - 3 * δ) / (d / K * (1 + 4 * Δ)) = A * m := by
    rw [hAd, hmd]
    field_simp
  have etb : (1 + 3 * δ) / (d / K * (1 - 4 * Δ)) = B * m := by
    rw [hBd, hmd]
    field_simp
  have hdm : d / K * m = 1 := by
    rw [hmd]
    field_simp
  have hA0 : 0 ≤ A := by linarith
  rw [eta, etb]
  refine ⟨mul_nonneg hA0 hm0.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  · calc A * m ≤ 1 * (4 * K) := mul_le_mul hAhi hmhi hm0.le zero_le_one
      _ = 4 * K := one_mul _
  · calc B * m ≤ 26 / 15 * (4 * K) := mul_le_mul hBhi hmhi hm0.le (by norm_num)
      _ ≤ 7 * K := by linarith
  · calc 14 / 25 * K ≤ A * K := mul_le_mul_of_nonneg_right hAlo hK.le
      _ ≤ A * m := mul_le_mul_of_nonneg_left hmlo hA0
  · have := mul_le_mul_of_nonneg_right hBA hm0.le
    nlinarith
  · calc d / K * (A * m) * (1 + 4 * Δ) = d / K * m * (A * (1 + 4 * Δ)) := by ring
      _ = 1 - 3 * δ := by rw [hdm, hA1, one_mul]
  · calc d / K * (B * m) * (1 - 4 * Δ) = d / K * m * (B * (1 - 4 * Δ)) := by ring
      _ = 1 + 3 * δ := by rw [hdm, hB1, one_mul]

/-- **The differences of the predicted angles.** The messenger starts where the clock's lower
level is (`v_m t₀ = −q v₀`). Its angle from the lower level is `(v_m − v₀) s/K`, and its
angle from the upper level differs from that by at most `4Δ` of it plus `Δ q/K`. -/
theorem emission_angles {K vm v0 v1 q t₀ Δ s : ℝ} (hK : 0 < K) (ht0 : vm * t₀ = -(q * v0))
    (hd : 1 / 4 ≤ vm - v0) (hv : |v1 - v0| ≤ Δ) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s) = (vm - v0) / K * s
    ∧ |1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s) - (vm - v0) / K * s|
        ≤ 4 * (Δ * ((vm - v0) / K * s)) + Δ * q / K := by
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hv
  have e0 : 1 / K * vm * (t₀ + s) = 1 / K * (vm * t₀) + 1 / K * vm * s := by ring
  constructor
  · rw [e0, ht0]
    ring
  · have e : 1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s) - (vm - v0) / K * s
        = (v0 - v1) * (s - q) / K := by
      rw [e0, ht0]
      ring
    have h1 : |v0 - v1| ≤ Δ := by rwa [abs_sub_comm]
    have h2 : |s - q| ≤ s + q := by
      rw [abs_le]
      constructor <;> linarith
    have h3 : |v0 - v1| * |s - q| ≤ Δ * (s + q) :=
      mul_le_mul h1 h2 (abs_nonneg _) hΔ0
    have e2 : (4 * (Δ * ((vm - v0) / K * s)) + Δ * q / K) * K
        = 4 * Δ * (vm - v0) * s + Δ * q := by
      field_simp
    rw [e, abs_div, abs_mul, abs_of_pos hK, div_le_iff₀ hK, e2]
    nlinarith [mul_nonneg (mul_nonneg hΔ0 hs) (by linarith : (0 : ℝ) ≤ 4 * (vm - v0) - 1)]

/-- **While the gate is open.** Up to `t_a` both differences of predicted angles are within
`1 − 2δ` of zero. -/
theorem emission_angles_near {K vm v0 v1 q t₀ Δ δ s ta : ℝ} (hK : 0 < K)
    (ht0 : vm * t₀ = -(q * v0)) (hd : 1 / 4 ≤ vm - v0) (hv : |v1 - v0| ≤ Δ) (hq : 0 ≤ q)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) (he : Δ * q / K ≤ δ / 2)
    (huta : (vm - v0) / K * ta * (1 + 4 * Δ) = 1 - 3 * δ) (hs0 : 0 ≤ s) (hs : s ≤ ta) :
    |1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s)| ≤ 1 - 2 * δ
    ∧ |1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s)| ≤ 1 - 2 * δ := by
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hv
  obtain ⟨h0eq, h1b⟩ := emission_angles (v1 := v1) (s := s) hK ht0 hd hv hq hs0
  have hu0 : 0 ≤ (vm - v0) / K := by
    have : 0 ≤ vm - v0 := by linarith
    positivity
  have hY0 : 0 ≤ (vm - v0) / K * s := mul_nonneg hu0 hs0
  have hY1 : (vm - v0) / K * s * (1 + 4 * Δ) ≤ 1 - 3 * δ := by
    rw [← huta]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hu0) (by linarith)
  have hZ0 : 0 ≤ Δ * ((vm - v0) / K * s) := mul_nonneg hΔ0 hY0
  have hY1' : (vm - v0) / K * s + 4 * (Δ * ((vm - v0) / K * s)) ≤ 1 - 3 * δ := by
    have e : (vm - v0) / K * s * (1 + 4 * Δ)
        = (vm - v0) / K * s + 4 * (Δ * ((vm - v0) / K * s)) := by ring
    linarith
  have h1b' := abs_le.1 h1b
  constructor
  · rw [h0eq, abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith [h1b'.1, h1b'.2]

/-- **While the gate is closed.** On `[t_b, (3/2) t_b]` both differences of predicted angles
are above `1 + 2δ` and below `4`. -/
theorem emission_angles_apart {K vm v0 v1 q t₀ Δ δ s tb : ℝ} (hK : 0 < K)
    (ht0 : vm * t₀ = -(q * v0)) (hd : 1 / 4 ≤ vm - v0) (hv : |v1 - v0| ≤ Δ) (hq : 0 ≤ q)
    (hΔ : Δ ≤ 1 / 16) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10) (he : Δ * q / K ≤ δ / 2)
    (hutb : (vm - v0) / K * tb * (1 - 4 * Δ) = 1 + 3 * δ) (htb : 0 ≤ tb) (hbs : tb ≤ s)
    (hs : s ≤ 3 / 2 * tb) :
    (1 + 2 * δ < 1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s)
      ∧ 1 / K * vm * (t₀ + s) - 1 / K * v0 * (-q + s) < 4)
    ∧ (1 + 2 * δ < 1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s)
      ∧ 1 / K * vm * (t₀ + s) - 1 / K * v1 * (-q + s) < 4) := by
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hv
  have hs0 : 0 ≤ s := htb.trans hbs
  obtain ⟨h0eq, h1b⟩ := emission_angles (v1 := v1) (s := s) hK ht0 hd hv hq hs0
  have hu0 : 0 ≤ (vm - v0) / K := by
    have : 0 ≤ vm - v0 := by linarith
    positivity
  have hY0 : 0 ≤ (vm - v0) / K * s := mul_nonneg hu0 hs0
  have e : (vm - v0) / K * s * (1 - 4 * Δ)
      = (vm - v0) / K * s - 4 * (Δ * ((vm - v0) / K * s)) := by ring
  have hYlo : 1 + 3 * δ ≤ (vm - v0) / K * s - 4 * (Δ * ((vm - v0) / K * s)) := by
    rw [← e, ← hutb]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbs hu0) (by linarith)
  have hYhi : (vm - v0) / K * s - 4 * (Δ * ((vm - v0) / K * s)) ≤ 3 / 2 * (1 + 3 * δ) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hu0)
      (by linarith : (0 : ℝ) ≤ 1 - 4 * Δ)
    have e' : (vm - v0) / K * (3 / 2 * tb) * (1 - 4 * Δ)
        = 3 / 2 * ((vm - v0) / K * tb * (1 - 4 * Δ)) := by ring
    rw [e', hutb, e] at h
    exact h
  have hZ0 : 0 ≤ Δ * ((vm - v0) / K * s) := mul_nonneg hΔ0 hY0
  have hZ1 : Δ * ((vm - v0) / K * s) ≤ 1 / 16 * ((vm - v0) / K * s) :=
    mul_le_mul_of_nonneg_right hΔ hY0
  have h1b' := abs_le.1 h1b
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h0eq]
    linarith
  · rw [h0eq]
    linarith
  · linarith [h1b'.1]
  · linarith [h1b'.2]

/-! ### The budget of a light flat messenger -/

/-- For a rest energy `0 < μ ≤ 1` the error rate is at most `1/μ` times the rate at rest
energy `1`. -/
theorem limitErr_le_inv_mul {μ ℓ D P a : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1) (hℓ : 0 < ℓ) :
    limitErr 1 μ ℓ D P a ≤ 1 / μ * limitErr 1 1 ℓ D P a := by
  have hπ := Real.pi_pos
  have h1 : 0 ≤ 1 / μ - 1 := by
    rw [sub_nonneg, le_div_iff₀ hμ0]
    linarith
  have key : 1 / μ * limitErr 1 1 ℓ D P a - limitErr 1 μ ℓ D P a
      = 2 * Real.pi / ℓ * (a ^ 2 * (P ^ 2 / 2)) * (1 / μ - 1) := by
    unfold limitErr
    field_simp
    ring
  have h2 : 0 ≤ 2 * Real.pi / ℓ * (a ^ 2 * (P ^ 2 / 2)) * (1 / μ - 1) := by positivity
  linarith

variable {n N M : ℕ}

/-- **The flat messenger's budget, for a light messenger.** For a rest energy `0 < μ ≤ 1`, at
every packet time: `1 − Re T(0) + |t| · limitErr ≤ 1/N + 1/(4 K² μ²) + |t|/(μ · 360000 n² N)`,
`K = 1200 n N`. -/
theorem flat_messenger_budget (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1) (t : ℝ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / N + 1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2)
        + |t| * (1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)))) := by
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK : 0 < 1200 * n * N := by positivity
  have hKr : ((1200 * n * N : ℕ) : ℝ) = 1200 * n * N := by push_cast; ring
  have hLen : ringLen (1200 * n * N) = 2 * Real.pi * (1200 * n * N) := by rw [ringLen, hKr]
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := M + 1) (flatWindow_mem_range hn hM)
  have hRe := re_transPhase_ringPacket_ge (L := M + 1) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) hμ0 (ringLen_pos hK) hW
    (fun _ => 1 / Real.sqrt N) (fun _ => by positivity)
  rw [flatWindow, (flat_sums (600 * (n : ℤ) * N) hN).2] at hRe
  have he : Real.pi * 1 / (ringLen (1200 * n * N) * μ) = 1 / (2 * (1200 * n * N) * μ) := by
    rw [hLen]
    field_simp
  rw [he] at hRe
  have hc : (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2
      = 1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2) := by
    field_simp
    ring
  rw [hc] at hRe
  have hc0 : 0 ≤ 1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2) := by positivity
  have hinvN0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hstart : 1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico (600 * (n : ℤ) * N) (600 * (n : ℤ) * N + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) 0)).re
      ≤ 1 / N + 1 / (4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2) := by
    nlinarith [mul_nonneg hc0 hinvN0]
  have hrate1 := (flat_packet_limitErr_le hn hN hM (μ := 1) le_rfl).2
  have hrate := limitErr_le_inv_mul (D := 1 / (600 * (n : ℝ))) (P := 1 / 2)
    (a := ringLen (1200 * n * N) / (M + 1 : ℕ)) hμ0 hμ (ringLen_pos hK)
  have hinvμ : 0 ≤ 1 / μ := by positivity
  have hrate' : limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
        (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))) :=
    hrate.trans (mul_le_mul_of_nonneg_left hrate1 hinvμ)
  have hdrift := mul_le_mul_of_nonneg_left hrate' (abs_nonneg t)
  unfold flatWindow flatAmpN
  linarith

/-! ### The reading under four scalar conditions -/

/-- **The messenger's packet time at the flow time `0`**: it starts where the clock's lower
level is predicted to be. -/
def emT0 (n N M : ℕ) (Δ μ : ℝ) : ℝ :=
  -(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)
    * (vRel 1 1 (1 / 2) / vRel 1 μ (1 / 2)))

/-- **The last flow time at which the gate is certified open.** -/
def emTa (n N : ℕ) (μ Δ δ : ℝ) : ℝ :=
  (1 - 3 * δ) / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 + 4 * Δ))

/-- **The first flow time at which the gate is certified closed.** -/
def emTb (n N : ℕ) (μ Δ δ : ℝ) : ℝ :=
  (1 + 3 * δ) / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 - 4 * Δ))

/-- **The two packets' budget over the whole run**, up to the flow time `(3/2) t_b`. -/
def emBudget (n N : ℕ) (Δ μ : ℝ) : ℝ :=
  2 / N + 1 / (2 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2)
    + 2 / μ * (1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n))

/-- **The two budgets over the run are at most `emBudget`**, for packet times within
`4/Δ + 11 K` of zero, `K = 1200 n N`. -/
theorem emission_budget_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2) {t t' : ℝ}
    (ht1 : |t| ≤ 4 / Δ + 11 * (1200 * (n : ℝ) * N))
    (ht2 : |t'| ≤ 4 / Δ + 11 * (1200 * (n : ℝ) * N)) :
    (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) 0)).re
        + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
            (ringLen (1200 * n * N) / (M + 1 : ℕ)))
      + flatBudget n N t' ≤ emBudget n N Δ μ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have mb := flat_messenger_budget hn hN hM hμ0 (by linarith) t
  have hc1 : 0 ≤ 1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)) := by positivity
  have hinvμ : 1 ≤ 1 / μ := by
    rw [le_div_iff₀ hμ0]
    linarith
  have hX : (4 / Δ + 11 * (1200 * (n : ℝ) * N))
        * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)))
      = 1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n) := by
    field_simp
    ring
  have hX0 : 0 ≤ 1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n) := by positivity
  have hf1 := mul_le_mul_of_nonneg_right ht2 hc1
  rw [hX] at hf1
  have hm1 : |t| * (1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))))
      ≤ 1 / μ * (1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n)) := by
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
  have e2 : 2 / μ * (1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n))
      = 2 * (1 / μ * (1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n))) := by ring
  have hXμ : 1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n)
      ≤ 1 / μ * (1 / (90000 * Δ * (n : ℝ) ^ 2 * N) + 11 / (300 * n)) :=
    le_mul_of_one_le_left hX0 hinvμ
  have e3 : (2 : ℝ) / N = 1 / N + 1 / N := by ring
  rw [emBudget, e1, e2, e3, flatBudget]
  linarith

/-- ★★★ **The emission reading for a light flat messenger, under four scalar conditions.** The
flat clock packet of #392 with gap `0 < Δ ≤ 1/16` and a flat messenger of rest energy
`0 < μ ≤ 1/2` on the same ring and window, the messenger starting where the clock's lower
level is; the gate "within the angle `1`"; a resolution `0 < δ ≤ 1/10`. If `800 Δ N ≤ 1`,
`1 ≤ 150 n N δ`, `emBudget ≤ ε δ²/5` and `1920 Δ n N ε < 1/24`, then for some strength
`0 < g ≤ R/5` the gated pointer has, at every flow time of `[t_b, (3/2) t_b]`, a count `N'`
with `|2π N' − R t_a| ≤ 2π ((22 δ + 29 Δ) R t_a + 7/2)`, and `R t_a ≥ 300 Δ n N`. -/
theorem light_messenger_emission_reading (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 16) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2) {a b : ℕ} (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1))
    {G₁ : Matrix ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2))
      ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2)) ℂ} (hG₁ : G₁.IsHermitian)
    {θ : KTorus} (hθ : trainF_periodic.lift θ.2 = 0) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 10) (hΔN : 800 * (Δ * N) ≤ 1) (hres : 1 ≤ 150 * n * N * δ)
    (hB : emBudget n N Δ μ ≤ ε * (δ ^ 2 / 5)) (hE : 1920 * Δ * n * N * ε < 1 / 24) :
    ∃ (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
          (flatAmpN N) (emT0 n N M Δ μ) ≠ 0) (g : ℝ)
        (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ 0 ≤ emTa n N μ Δ δ ∧ emTa n N μ Δ δ ≤ emTb n N μ Δ δ
      ∧ 300 * Δ * n * N ≤ ringRate (1200 * n * N) M (1 / 2) Δ * emTa n N μ Δ δ
      ∧ ∀ t, emTb n N μ Δ δ ≤ t → t ≤ 3 / 2 * emTb n N μ Δ δ →
          ∃ N' : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (ringGateRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) G₁ 1 g
                (chainRay _ hψ) (deviceRay _ hΨ) θ) t N'
            ∧ |(N' : ℝ) * (2 * Real.pi)
                  - ringRate (1200 * n * N) M (1 / 2) Δ * emTa n N μ Δ δ|
                ≤ 2 * Real.pi * ((22 * δ + 29 * Δ)
                    * (ringRate (1200 * n * N) M (1 / 2) Δ * emTa n N μ Δ δ) + 7 / 2) := by
  have hπ := Real.pi_pos
  have hπl : 3 < Real.pi := Real.pi_gt_three
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
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
    exact flatWindow_width hn hN m hm
  have hP : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hD0 : (0 : ℝ) ≤ 1 / (600 * n) := by positivity
  have hψ := ringPacket_ne_zero (M := M) one_pos hμ0 (ringLen_pos hK) hP hD0
    (flatWindow_mem_range hn hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) (emT0 n N M Δ μ)
  -- the clock's rate
  have hRlo : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hRhi : ringRate (1200 * n * N) M (1 / 2) Δ ≤ Δ := levelClockRate_le_gap hΔ0.le _
  have hT0 : emT0 n N M Δ μ = -(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)
      * (vRel 1 1 (1 / 2) / vRel 1 μ (1 / 2))) := rfl
  have hTa : emTa n N μ Δ δ = (1 - 3 * δ)
      / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 + 4 * Δ)) := rfl
  have hTb : emTb n N μ Δ δ = (1 + 3 * δ)
      / ((vRel 1 μ (1 / 2) - vRel 1 1 (1 / 2)) / (1200 * (n : ℝ) * N) * (1 - 4 * Δ)) := rfl
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
  generalize htad : emTa n N μ Δ δ = ta at *
  generalize htbd : emTb n N μ Δ δ = tb at *
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
  generalize hqd : Real.pi / (2 * R) = q at *
  have hΔq : Δ * q ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hq4 hΔ0.le
    have e : Δ * (4 / Δ) = 4 := by field_simp
    rwa [e] at h
  have he : Δ * q / (1200 * (n : ℝ) * N) ≤ δ / 2 := by
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
  obtain ⟨hta0, hab, hta4, htb7, htalo, hclose, huta, hutb⟩ :
      0 ≤ ta ∧ ta ≤ tb ∧ ta ≤ 4 * (1200 * (n : ℝ) * N) ∧ tb ≤ 7 * (1200 * (n : ℝ) * N)
      ∧ 14 / 25 * (1200 * (n : ℝ) * N) ≤ ta ∧ tb - ta ≤ (18 * δ + 24 * Δ) * ta
      ∧ (vm - v0) / (1200 * (n : ℝ) * N) * ta * (1 + 4 * Δ) = 1 - 3 * δ
      ∧ (vm - v0) / (1200 * (n : ℝ) * N) * tb * (1 - 4 * Δ) = 1 + 3 * δ := by
    rw [hTa, hTb]
    exact emission_times hK0 hd hd1 hΔ0.le hΔ hδ0.le hδ
  have htb0 : 0 ≤ tb := hta0.trans hab
  have hbc : tb ≤ 3 / 2 * tb := by linarith
  have hBpos : 0 < emBudget n N Δ μ := by
    unfold emBudget
    positivity
  have hε0 : 0 ≤ ε :=
    nonneg_of_mul_nonneg_left (hBpos.le.trans hB) (by positivity)
  have hΔnN : 0 ≤ Δ * n * N := by positivity
  have hRta : 300 * Δ * n * N ≤ R * ta :=
    calc 300 * Δ * n * N ≤ Δ / 2 * (14 / 25 * (1200 * (n : ℝ) * N)) := by linarith
      _ ≤ R * ta := mul_le_mul hRlo htalo (by positivity) hR0.le
  have htaT : ta ≤ 2 * Real.pi * n / R := by
    rw [le_div_iff₀ hR0]
    have h1 : ta * R ≤ 4 * (1200 * (n : ℝ) * N) * Δ :=
      mul_le_mul hta4 hRhi hR0.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hΔN hn0.le
    have h3 := mul_pos hn0 (sub_pos.2 hπl)
    linarith
  have hopenS : 2 * (R / 5) * ε * ta < 1 / 24 := by
    have h1 : R * ta ≤ Δ * (4 * (1200 * (n : ℝ) * N)) := mul_le_mul hRhi hta4 hta0 hΔ0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hε0
    linarith
  have hclosedS : 2 * (R / 5) * ε * (3 / 2 * tb - tb) ≤ 1 / 6 := by
    have h1 : R * tb ≤ Δ * (7 * (1200 * (n : ℝ) * N)) := mul_le_mul hRhi htb7 htb0 hΔ0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hε0
    have h3 : 0 ≤ ε * (Δ * n * N) := mul_nonneg hε0 hΔnN
    linarith
  -- the budgets
  have hbudget : ∀ s, 0 ≤ s → s ≤ 3 / 2 * tb →
      (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
            (flatAmpN N) 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-q + s) ≤ ε * (1 - Real.cos δ) := by
    intro s hs0 hs
    have hTs : 3 / 2 * tb ≤ 11 * (1200 * (n : ℝ) * N) := by linarith
    have ht1 : |t₀ + s| ≤ 4 / Δ + 11 * (1200 * (n : ℝ) * N) := by
      rw [abs_le]
      constructor <;> linarith
    have ht2 : |-q + s| ≤ 4 / Δ + 11 * (1200 * (n : ℝ) * N) := by
      rw [abs_le]
      constructor <;> linarith
    have hcos := mul_le_mul_of_nonneg_left
      (sq_div_five_le_one_sub_cos (δ := δ) (by rw [abs_of_pos hδ0]; linarith)) hε0
    exact ((emission_budget_le hn hN hM hΔ0 hμ0 hμ ht1 ht2).trans hB).trans hcos
  -- the predicted angles
  have hnear : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (1 - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v0 * (-q + s))
        ∧ Real.cos (1 - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v1 * (-q + s)) := by
    intro s hs0 hs
    obtain ⟨h0, h1⟩ := emission_angles_near (v1 := v1) hK0 hvt0 hd hv1 hq0.le hδ0.le hδ he huta
      hs0 hs
    rw [hfac]
    exact ⟨cos_le_cos_of_abs_le h0 (by linarith), cos_le_cos_of_abs_le h1 (by linarith)⟩
  have hapart : ∀ s, tb ≤ s → s ≤ 3 / 2 * tb →
      Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v0 * (-q + s))
          < Real.cos (1 + 2 * δ)
        ∧ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vm * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * v1 * (-q + s))
          < Real.cos (1 + 2 * δ) := by
    intro s hbs hs
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩⟩ := emission_angles_apart (v1 := v1) hK0 hvt0 hd hv1 hq0.le hΔ hδ0
      hδ he hutb htb0 hbs hs
    rw [hfac]
    exact ⟨cos_lt_cos_of_between (by linarith) h0 (by linarith),
      cos_lt_cos_of_between (by linarith) h1 (by linarith)⟩
  have hΔ2 : Δ ≤ 1 / 2 := by linarith
  have hw1 : 2 * δ ≤ 1 := by linarith
  have hw2 : 1 + 2 * δ ≤ Real.pi := by linarith
  have hfin : ∀ g : ℝ, g ≤ R / 5 →
      6 * g * (tb - ta) + 7 / 2 ≤ (22 * δ + 29 * Δ) * (R * ta) + 7 / 2 := by
    intro g hg5
    have hg' : g * (tb - ta) ≤ R / 5 * ((18 * δ + 24 * Δ) * ta) :=
      mul_le_mul hg5 hclose (sub_nonneg.2 hab) (by positivity)
    have hRt : 0 ≤ R * ta := mul_nonneg hR0.le hta0
    have h4 := mul_nonneg hδ0.le hRt
    have h5 := mul_nonneg hΔ0.le hRt
    linarith
  subst hqd htbd htad ht0d hv1d hv0d hvmd hRd
  obtain ⟨g, hΨ, hg0, hg5, Na, Nb, hNa, hNa', hNb, hNab, hNb', hwin⟩ :=
    flat_clock_emission_reading hn hN hM hΔ0 hΔ2 e₁ e₂ hμ0 hP hD0
      (flatWindow_mem_range hn hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) _ hψ hG₁ hθ
      (w := 1) (δ := δ) (ε := ε) hδ0 hw1 hw2 hε0 hta0 hab hbc htaT hbudget hnear hapart
      hopenS hclosedS
  refine ⟨hψ, g, hΨ, hg0, hg5, hta0, hab, hRta, fun t hbt htc => ?_⟩
  obtain ⟨N', hN', -, -, h3⟩ := hwin t hbt htc
  exact ⟨N', hN', h3.trans (mul_le_mul_of_nonneg_left (hfin g hg5) (by positivity))⟩

/-! ### A family along which the error shrinks -/

/-- The family's momentum-width index: `10⁷ k⁴`. -/
def emn (k : ℕ) : ℕ := 10 ^ 7 * k ^ 4

/-- The family's number of modes: `2 · 10⁸ k³`. -/
def emN (k : ℕ) : ℕ := 2 * 10 ^ 8 * k ^ 3

/-- The family's level gap: `k / (n N)`. -/
def emGap (k : ℕ) : ℝ := k / ((emn k : ℝ) * emN k)

/-- **The family's budget**: at most `(7/2)/(10⁸ k³)`. -/
theorem emBudget_family_le {k : ℕ} (hk : 0 < k) :
    emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) ≤ 7 / 2 * (1 / (10 ^ 8 * (k : ℝ) ^ 3)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hn : ((emn k : ℕ) : ℝ) = 10 ^ 7 * (k : ℝ) ^ 4 := by
    rw [emn]
    push_cast
    ring
  have hN : ((emN k : ℕ) : ℝ) = 2 * 10 ^ 8 * (k : ℝ) ^ 3 := by
    rw [emN]
    push_cast
    ring
  rw [emBudget, emGap, hn, hN]
  generalize (k : ℝ) = X at *
  have h3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hk1 (by norm_num)
  have h12 : X ^ 3 ≤ X ^ 12 := pow_le_pow_right₀ hk1 (by norm_num)
  have hX3 : 0 < X ^ 3 := by positivity
  have t1 : (2 : ℝ) / (2 * 10 ^ 8 * X ^ 3) = 1 / (10 ^ 8 * X ^ 3) := by
    field_simp
  have t2 : 1 / (2 * (1200 * (10 ^ 7 * X ^ 4) * (2 * 10 ^ 8 * X ^ 3)) ^ 2 * (1 / (2 * X)) ^ 2)
      ≤ 1 / (10 ^ 8 * X ^ 3) := by
    have e : 2 * (1200 * (10 ^ 7 * X ^ 4) * (2 * 10 ^ 8 * X ^ 3)) ^ 2 * (1 / (2 * X)) ^ 2
        = 288 * 10 ^ 34 * X ^ 12 := by
      field_simp
      ring
    rw [e]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have t3 : 2 / (1 / (2 * X))
        * (1 / (90000 * (X / (10 ^ 7 * X ^ 4 * (2 * 10 ^ 8 * X ^ 3))) * (10 ^ 7 * X ^ 4) ^ 2
              * (2 * 10 ^ 8 * X ^ 3))
          + 11 / (300 * (10 ^ 7 * X ^ 4)))
      ≤ 3 / 2 * (1 / (10 ^ 8 * X ^ 3)) := by
    have e : 2 / (1 / (2 * X))
          * (1 / (90000 * (X / (10 ^ 7 * X ^ 4 * (2 * 10 ^ 8 * X ^ 3))) * (10 ^ 7 * X ^ 4) ^ 2
                * (2 * 10 ^ 8 * X ^ 3))
            + 11 / (300 * (10 ^ 7 * X ^ 4)))
        = 4 / (9 * 10 ^ 11) * (1 / X ^ 4) + 44 / (3 * 10 ^ 9) * (1 / X ^ 3) := by
      field_simp
      ring
    have h4 : 1 / X ^ 4 ≤ 1 / X ^ 3 := one_div_le_one_div_of_le hX3 h3
    have h5 : 0 ≤ 1 / X ^ 3 := by positivity
    have e2 : 3 / 2 * (1 / (10 ^ 8 * X ^ 3)) = 3 / (2 * 10 ^ 8) * (1 / X ^ 3) := by
      field_simp
    rw [e, e2]
    nlinarith
  rw [t1]
  linarith

/-- The error of the family: with `Δ ≤ 1/(1000 X)`, a resolution `1/(10 X)` and a phase
`Y ≥ 300 X`, the bound of `light_messenger_emission_reading` is at most `(15/X) Y`. -/
theorem emission_family_error {X Δ Y : ℝ} (hX : 1 ≤ X)
    (hΔ : Δ ≤ 1 / (1000 * X)) (hY : 300 * X ≤ Y) :
    2 * Real.pi * ((22 * (1 / (10 * X)) + 29 * Δ) * Y + 7 / 2) ≤ 15 / X * Y := by
  have hX0 : 0 < X := by linarith
  have hπ := Real.pi_pos
  have hπu : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  norm_num at hπu
  have hY0 : 0 ≤ Y := by nlinarith
  have hW : 300 ≤ Y / X := by
    rw [le_div_iff₀ hX0]
    exact hY
  have e1 : 1 / (10 * X) * Y = Y / X / 10 := by
    field_simp
  have h2 : Δ * Y ≤ Y / X / 1000 := by
    have h := mul_le_mul_of_nonneg_right hΔ hY0
    have e : 1 / (1000 * X) * Y = Y / X / 1000 := by
      field_simp
    linarith
  have e3 : 15 / X * Y = 15 * (Y / X) := by
    field_simp
  have hin : (22 * (1 / (10 * X)) + 29 * Δ) * Y + 7 / 2 ≤ 2229 / 1000 * (Y / X) + 7 / 2 := by
    have e : (22 * (1 / (10 * X)) + 29 * Δ) * Y = 22 * (1 / (10 * X) * Y) + 29 * (Δ * Y) := by
      ring
    rw [e, e1]
    linarith
  have hin0 : 0 ≤ 2229 / 1000 * (Y / X) + 7 / 2 := by linarith
  have h3 := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have h4 := mul_le_mul_of_nonneg_right hπu hin0
  rw [e3]
  linarith

/-- ★★★ **A family of runs whose emission reading has a relative error at most `15/k`.** For
every `k ≥ 1`: the flat clock packet with `n = 10⁷ k⁴`, `N = 2 · 10⁸ k³` and gap
`Δ = k/(n N)`, and a flat messenger of rest energy `1/(2k)` on the same ring, whose velocity
is within `1/(2k²)` of `1`. For some strength of the coupling, the pointer gated by "within
the angle `1`" has, at every flow time of `[t_b, (3/2) t_b]`, a number of ticks `N'` with
`|2π N' − R t_a| ≤ (15/k) R t_a`, and `R t_a ≥ 300 k`. No hypothesis is left but the size of
the ring. -/
theorem emission_reading_family (k : ℕ) (hk : 0 < k) {M : ℕ}
    (hM : 210000 * emn k ^ 2 * emN k ≤ M) {a b : ℕ}
    (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1))
    {G₁ : Matrix ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2))
      ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2)) ℂ} (hG₁ : G₁.IsHermitian)
    {θ : KTorus} (hθ : trainF_periodic.lift θ.2 = 0) :
    1 - 1 / (2 * (k : ℝ) ^ 2) ≤ vRel 1 (1 / (2 * k)) (1 / 2)
    ∧ vRel 1 (1 / (2 * k)) (1 / 2) ≤ 1
    ∧ ∃ (hψ : ringPacket (L := M + 1) 1 (1 / (2 * k)) (ringLen (1200 * emn k * emN k))
          (flatWindow (emn k) (emN k)) (flatAmpN (emN k))
          (emT0 (emn k) (emN k) M (emGap k) (1 / (2 * k))) ≠ 0) (g : ℝ)
        (hΨ : devicePacket (L := M + 1) (ringHop (1200 * emn k * emN k) M) 1 (1 + emGap k)
          (flatWindow (emn k) (emN k)) (flatAmpN (emN k))
          (-(Real.pi / (2 * ringRate (1200 * emn k * emN k) M (1 / 2) (emGap k)))) ≠ 0),
      0 < g
      ∧ 0 ≤ emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))
      ∧ emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))
          ≤ emTb (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))
      ∧ 300 * (k : ℝ) ≤ ringRate (1200 * emn k * emN k) M (1 / 2) (emGap k)
          * emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))
      ∧ ∀ t, emTb (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k)) ≤ t →
          t ≤ 3 / 2 * emTb (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k)) →
          ∃ N' : ℕ, IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (ringGateRun e₁ e₂ (ringHop (1200 * emn k * emN k) M) (1 / (2 * k)) 1
                (1 + emGap k) G₁ 1 g (chainRay _ hψ) (deviceRay _ hΨ) θ) t N'
            ∧ |(N' : ℝ) * (2 * Real.pi)
                  - ringRate (1200 * emn k * emN k) M (1 / 2) (emGap k)
                    * emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))|
                ≤ 15 / k * (ringRate (1200 * emn k * emN k) M (1 / 2) (emGap k)
                    * emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hn : 0 < emn k := by
    rw [emn]
    positivity
  have hN : 0 < emN k := by
    rw [emN]
    positivity
  have hnr : ((emn k : ℕ) : ℝ) = 10 ^ 7 * (k : ℝ) ^ 4 := by
    rw [emn]
    push_cast
    ring
  have hNr : ((emN k : ℕ) : ℝ) = 2 * 10 ^ 8 * (k : ℝ) ^ 3 := by
    rw [emN]
    push_cast
    ring
  have hk6 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ hk1
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
  have hΔe : emGap k = 1 / (2 * 10 ^ 15 * (k : ℝ) ^ 6) := by
    rw [emGap, hnr, hNr]
    field_simp
  have hΔ0 : 0 < emGap k := by
    rw [hΔe]
    positivity
  have hΔX : emGap k ≤ 1 / (1000 * k) := by
    rw [hΔe]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h5 : (k : ℝ) ≤ (k : ℝ) ^ 6 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
    nlinarith
  have hΔ16 : emGap k ≤ 1 / 16 := by
    refine hΔX.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hΔnN : emGap k * (emn k : ℝ) * emN k = k := by
    rw [emGap]
    have h1 : (0 : ℝ) < emn k := by exact_mod_cast hn
    have h2 : (0 : ℝ) < emN k := by exact_mod_cast hN
    field_simp
  have hμ0 : (0 : ℝ) < 1 / (2 * k) := by positivity
  have hμ : (1 : ℝ) / (2 * k) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ0 : (0 : ℝ) < 1 / (10 * k) := by positivity
  have hδ : (1 : ℝ) / (10 * k) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hΔN : 800 * (emGap k * (emN k : ℝ)) ≤ 1 := by
    have e : emGap k * (emN k : ℝ) = 1 / (10 ^ 7 * (k : ℝ) ^ 3) := by
      rw [hΔe, hNr]
      field_simp
    rw [e, ← mul_div_assoc, mul_one, div_le_one (by positivity)]
    nlinarith
  have hres : 1 ≤ 150 * (emn k : ℝ) * emN k * (1 / (10 * k)) := by
    have e : 150 * (emn k : ℝ) * emN k * (1 / (10 * k)) = 3 * 10 ^ 16 * (k : ℝ) ^ 6 := by
      rw [hnr, hNr]
      field_simp
      ring
    rw [e]
    nlinarith
  have hBle := emBudget_family_le hk
  have hBpos : 0 < emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) := by
    unfold emBudget
    have h1 : (0 : ℝ) < emn k := by exact_mod_cast hn
    have h2 : (0 : ℝ) < emN k := by exact_mod_cast hN
    positivity
  have hfive : (5 : ℝ) / (1 / (10 * k)) ^ 2 = 500 * (k : ℝ) ^ 2 := by
    field_simp
    ring
  have hB : emBudget (emn k) (emN k) (emGap k) (1 / (2 * k))
      ≤ emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) * (5 / (1 / (10 * k)) ^ 2)
        * ((1 / (10 * k)) ^ 2 / 5) := by
    refine le_of_eq ?_
    field_simp
  have hE : 1920 * emGap k * (emn k : ℝ) * emN k
        * (emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) * (5 / (1 / (10 * k)) ^ 2))
      < 1 / 24 := by
    have e : 1920 * emGap k * (emn k : ℝ) * emN k
          * (emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) * (5 / (1 / (10 * k)) ^ 2))
        = 960000 * (k : ℝ) ^ 3 * emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) := by
      rw [hfive]
      calc 1920 * emGap k * (emn k : ℝ) * emN k
            * (emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) * (500 * (k : ℝ) ^ 2))
          = 1920 * (emGap k * (emn k : ℝ) * emN k)
            * (emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) * (500 * (k : ℝ) ^ 2)) := by
            ring
        _ = 960000 * (k : ℝ) ^ 3 * emBudget (emn k) (emN k) (emGap k) (1 / (2 * k)) := by
            rw [hΔnN]
            ring
    have h1 := mul_le_mul_of_nonneg_left hBle
      (by positivity : (0 : ℝ) ≤ 960000 * (k : ℝ) ^ 3)
    have e2 : 960000 * (k : ℝ) ^ 3 * (7 / 2 * (1 / (10 ^ 8 * (k : ℝ) ^ 3))) = 336 / 10000 := by
      field_simp
      norm_num
    rw [e]
    linarith
  obtain ⟨hv7, hv1, hv2⟩ := vRel_half_light hμ0 hμ
  obtain ⟨hψ, g, hΨ, hg0, -, hta0, hab, hRta, hwin⟩ :=
    light_messenger_emission_reading (M := M) hn hN hM hΔ0 hΔ16 hμ0 hμ e₁ e₂ hG₁ hθ hδ0 hδ
      hΔN hres hB hE
  have hRta' : 300 * (k : ℝ) ≤ ringRate (1200 * emn k * emN k) M (1 / 2) (emGap k)
      * emTa (emn k) (emN k) (1 / (2 * k)) (emGap k) (1 / (10 * k)) := by
    have e : 300 * emGap k * (emn k : ℝ) * emN k = 300 * (k : ℝ) := by
      rw [← hΔnN]
      ring
    rw [← e]
    exact hRta
  refine ⟨?_, hv1, hψ, g, hΨ, hg0, hta0, hab, hRta', fun t h1 h2 => ?_⟩
  · have e : 2 * ((1 : ℝ) / (2 * k)) ^ 2 = 1 / (2 * (k : ℝ) ^ 2) := by
      field_simp
    rw [← e]
    exact hv2
  · obtain ⟨N', hN', hb⟩ := hwin t h1 h2
    exact ⟨N', hN', hb.trans (emission_family_error hk1 hΔX hRta')⟩

end CSD.RecordLayer

end
