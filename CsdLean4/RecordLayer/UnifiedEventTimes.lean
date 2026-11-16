/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateTimes
public import CsdLean4.RecordLayer.UnifiedClockAtRest
public import CsdLean4.CV.DiracContinuum

/-!
# Event times of the radar run from the gates, and the clocks' rate relation

**Category:** 7-SigmaLayer (the record layer). BACKLOG #418 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 4 and 5 of the research
delivery plan of 2026-11-16. No new assumption.

The top-down statement (#402) has five timing hypotheses `|t − T| ≤ τ` and one rate
hypothesis `|R_B − √(1 − v²) R₀| ≤ κ R₀`. #412 defined the four times `T`; #406 proved the
rate hypothesis with the velocity taken at the lattice's momentum term. This module closes
both: the rate relation with the velocity of the packets, and the timing tolerances from
the intervals on which the gates are open.

* `abs_ringSigma_sub_le` — the lattice's momentum term is within `a² p³/6` of the momentum,
  `a` the lattice spacing;
* `sqrt_one_sub_vRel_sq`, `abs_inv_dispE_sub_le`, ★★★ `wall_observer_clock_rate_relation` —
  **the rate hypothesis of #402 with the packets' velocity**:
  `|R(p) − √(1 − v(p)²) R(0)| ≤ (Δ + a² p³/6) R(0)`, `v(p) = p/√(1 + p²)`;
* `abs_vRel_level_sub_le` — the clock's two levels differ in velocity by at most `Δ`;
* ★ `gate_closed_away_turn` — #414's "closed while away", for angles through a whole turn
  (the distance of the feasibility note is the whole chain);
* ★ `wall_gate_apart_before`, ★ `wall_gate_near_at` — a carrier coming to an observer who
  sits at a wall: apart until `(d − (w + 2δ))/u`, near within `(w − 2δ)/u` of `d/u`;
* ★★ `wall_packet_relay_time_bound`, ★★ `wall_packet_return_time_bound`,
  ★★ `wall_observer_meeting_time_bound` — a flow time within `ρ` of the crossing time is
  within `ρ + d(1 − u)/u`, `ρ + 2d(1 − u)/u`, `ρ` of `T_R`, `T_Ret`, `T_M`.

## Exact scope

* **The rate relation is complete as an inequality**: its velocity is now the relativistic
  velocity at the momentum `p` that the localisation theorems (#265) use for the packets'
  predicted positions. The error has two terms, the levels' relative gap and the lattice's.
* **The timing bounds are conditional on a gate window.** Each takes `|t − crossing| ≤ ρ`,
  which `gate_open_at_emission`, `gate_open_at_return`, `wall_gate_near_at` supply for
  carriers on straight lines. That the gated pointers' histories turn at such `t` is the
  history theorems' business (Task 6).
* **Straight motion at one speed per carrier.** The clock's two levels are to be treated one
  at a time; `abs_vRel_level_sub_le` bounds their difference and the intervals are not
  intersected here.
* **Angular units.** `u`, `v` are angular speeds and `d` an angle, or all three are scaled
  by the same factor; the lemmas are homogeneous. With the ring of length `2π K` the
  angular speed of a packet of velocity `v` is `v/K`.
* **No arena.** Real arithmetic, except the two rate lemmas, which are about `ringRate`.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-171, UD-181, UD-183, UD-188); `specs/unified-m6-feasibility.md`
(§4, §6 items 3 and 7); `RecordLayer/UnifiedGateTimes.lean` (#414: `gate_open_at_emission`,
`gate_open_at_return`); `RecordLayer/UnifiedRadarTimes.lean` (#412: `radarTR`, `radarTRet`,
`radarTM`, `crossRelay`, `crossReturn`, `abs_crossRelay_sub`, `abs_crossReturn_sub_le`);
`RecordLayer/UnifiedClockAtRest.lean` (#406: `abs_ringRate_sub_le`, `ringRate_zero`);
`RecordLayer/UnifiedEmissionValues.lean` (#397: `cos_lt_cos_of_between`,
`cos_le_cos_of_abs_le`); `CV/DiracContinuum.lean` (`abs_dispE_sub_le`);
`CV/DiracClockChain.lean` (`div_dispE_eq_sqrt`, `le_dispE`); `CV/DiracDevice.lean`
(`abs_vRel_sub_le`); `RecordLayer/UnifiedRadarSkeleton.lean` (#402: `hκ`, `hτR`, `hτRet`,
`hτMB`, `hτMA`).
-/

@[expose] public section

noncomputable section

open CSD.CV

namespace CSD.RecordLayer

/-! ### The clocks' rate relation, with the packets' velocity -/

/-- The lattice's momentum term is within `a² p³/6` of the momentum, `a = ℓ/L` the lattice
spacing. -/
theorem abs_ringSigma_sub_le {K : ℕ} (hK : 0 < K) (M : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    |ringSigma K M p - p| ≤ (ringLen K / (M + 1 : ℕ)) ^ 2 * p ^ 3 / 6 := by
  have hL := ringLen_pos hK
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  rcases hp.eq_or_lt with rfl | hp0
  · simp [ringSigma]
  have hx : 0 < ringLen K / (M + 1 : ℕ) * p := by positivity
  have h1 := Real.sin_gt_sub_cube hx
  have h2 := Real.sin_lt hx
  have hxp : ((M + 1 : ℕ) : ℝ) / ringLen K * (ringLen K / (M + 1 : ℕ) * p) = p := by
    field_simp
  have e : ringSigma K M p - p
      = ((M + 1 : ℕ) : ℝ) / ringLen K
        * (Real.sin (ringLen K / (M + 1 : ℕ) * p) - ringLen K / (M + 1 : ℕ) * p) := by
    rw [ringSigma, two_ringHop hK, mul_sub, hxp]
  have habs : |Real.sin (ringLen K / (M + 1 : ℕ) * p) - ringLen K / (M + 1 : ℕ) * p|
      ≤ (ringLen K / (M + 1 : ℕ) * p) ^ 3 / 6 := by
    rw [abs_le]
    constructor <;> linarith [pow_pos hx 3]
  rw [e, abs_mul, abs_of_pos (div_pos hM hL)]
  calc ((M + 1 : ℕ) : ℝ) / ringLen K
        * |Real.sin (ringLen K / (M + 1 : ℕ) * p) - ringLen K / (M + 1 : ℕ) * p|
      ≤ ((M + 1 : ℕ) : ℝ) / ringLen K * ((ringLen K / (M + 1 : ℕ) * p) ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left habs (div_pos hM hL).le
    _ = (ringLen K / (M + 1 : ℕ)) ^ 2 * p ^ 3 / 6 := by
        field_simp

/-- The dilation factor of the lower level at the momentum term `s`. -/
theorem sqrt_one_sub_vRel_sq (s : ℝ) : Real.sqrt (1 - vRel 1 1 s ^ 2) = 1 / dispE 1 s := by
  have h := div_dispE_eq_sqrt (c := 1) one_ne_zero one_pos s
  rw [div_one] at h
  exact h.symm

theorem abs_inv_dispE_sub_le (s t : ℝ) : |1 / dispE 1 s - 1 / dispE 1 t| ≤ |s - t| := by
  have hs := dispE_pos (μ := 1) one_pos s
  have ht := dispE_pos (μ := 1) one_pos t
  have hs1 := le_dispE 1 s
  have ht1 := le_dispE 1 t
  have h := abs_dispE_sub_le (μ := 1) one_pos t s
  have e : 1 / dispE 1 s - 1 / dispE 1 t = (dispE 1 t - dispE 1 s) / (dispE 1 s * dispE 1 t) := by
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hs ht), abs_sub_comm s t]
  refine (div_le_self (abs_nonneg _) ?_).trans h
  nlinarith

/-- ★★★ **The rate hypothesis of #402, with the packets' velocity.** The clock with levels
`1` and `1 + Δ` at reference momentum `p ≥ 0` on the ring, against the same clock at
reference momentum `0`: the rate is `√(1 − v²)` times the rest rate within
`(Δ + a² p³/6)` times the rest rate, `v = p/√(1 + p²)` the velocity at which the packet's
predicted position moves, `a` the lattice spacing. -/
theorem wall_observer_clock_rate_relation {K : ℕ} (hK : 0 < K) (M : ℕ) {Δ : ℝ} (hΔ : 0 < Δ)
    {p : ℝ} (hp : 0 ≤ p) :
    |ringRate K M p Δ - Real.sqrt (1 - vRel 1 1 p ^ 2) * ringRate K M 0 Δ|
      ≤ (Δ + (ringLen K / (M + 1 : ℕ)) ^ 2 * p ^ 3 / 6) * ringRate K M 0 Δ := by
  have h := abs_ringRate_sub_le K M hΔ p
  have h0 : ringRate K M 0 Δ = Δ := ringRate_zero K M hΔ.le
  have hσ := abs_ringSigma_sub_le hK M hp
  have hd := abs_inv_dispE_sub_le (ringSigma K M p) p
  rw [← sqrt_one_sub_vRel_sq, ← sqrt_one_sub_vRel_sq] at hd
  rw [h0] at h ⊢
  have e : ringRate K M p Δ - Real.sqrt (1 - vRel 1 1 p ^ 2) * Δ
      = (ringRate K M p Δ - Real.sqrt (1 - vRel 1 1 (ringSigma K M p) ^ 2) * Δ)
        + (Real.sqrt (1 - vRel 1 1 (ringSigma K M p) ^ 2)
            - Real.sqrt (1 - vRel 1 1 p ^ 2)) * Δ := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hΔ]
  have h3 := mul_le_mul_of_nonneg_right (hd.trans hσ) hΔ.le
  linarith

/-- The clock's two levels differ in velocity by at most the gap. -/
theorem abs_vRel_level_sub_le {Δ : ℝ} (hΔ : 0 ≤ Δ) (s : ℝ) :
    |vRel 1 (1 + Δ) s - vRel 1 1 s| ≤ Δ := by
  have h := abs_vRel_sub_le (c := 1) zero_le_one one_pos (by linarith : (1 : ℝ) ≤ 1 + Δ) s
  rw [add_sub_cancel_left, div_one, one_mul] at h
  exact h

/-! ### Gates through a whole turn, and at an observer who sits at a wall -/

/-- ★ **The gate is closed while the messenger is away, through a whole turn.** As
`gate_closed_away`, for a distance up to the whole chain: the two carriers are more than
`w + 2δ` apart both ways round while `(u − v) s` and `2d − (u + v) s` lie in
`(w + 2δ, 2π − (w + 2δ))`. -/
theorem gate_closed_away_turn {u v d w δ s : ℝ} (hwδ : 0 ≤ w + 2 * δ)
    (h1 : w + 2 * δ < (u - v) * s) (h1' : (u - v) * s < 2 * Real.pi - (w + 2 * δ))
    (h2 : w + 2 * δ < 2 * d - (u + v) * s)
    (h2' : 2 * d - (u + v) * s < 2 * Real.pi - (w + 2 * δ)) :
    Real.cos ((u * s - d) - (v * s - d)) < Real.cos (w + 2 * δ)
      ∧ Real.cos ((u * s - d) + (v * s - d)) < Real.cos (w + 2 * δ) := by
  constructor
  · rw [show (u * s - d) - (v * s - d) = (u - v) * s by ring]
    exact cos_lt_cos_of_between hwδ h1 h1'
  · rw [← Real.cos_neg, show -((u * s - d) + (v * s - d)) = 2 * d - (u + v) * s by ring]
    exact cos_lt_cos_of_between hwδ h2 h2'

/-- ★ **A carrier is apart from an observer at a wall until it arrives.** The carrier's
angle from the wall is `u s − d`, the observer's is `0`: they are more than `w + 2δ` apart
both ways round while `d − u s` lies in `(w + 2δ, 2π − (w + 2δ))`. -/
theorem wall_gate_apart_before {u d w δ s : ℝ} (hwδ : 0 ≤ w + 2 * δ)
    (h : w + 2 * δ < d - u * s) (h' : d - u * s < 2 * Real.pi - (w + 2 * δ)) :
    Real.cos ((u * s - d) - 0) < Real.cos (w + 2 * δ)
      ∧ Real.cos ((u * s - d) + 0) < Real.cos (w + 2 * δ) := by
  have key : Real.cos (u * s - d) < Real.cos (w + 2 * δ) := by
    rw [← Real.cos_neg, neg_sub]
    exact cos_lt_cos_of_between hwδ h h'
  rw [sub_zero, add_zero]
  exact ⟨key, key⟩

/-- ★ **A carrier is near an observer at a wall around its arrival**: within `w − 2δ` while
`|s − d/u| ≤ (w − 2δ)/u`. -/
theorem wall_gate_near_at {u d w δ s : ℝ} (hu : 0 < u) (hwπ : w - 2 * δ ≤ Real.pi)
    (h : |s - d / u| ≤ (w - 2 * δ) / u) :
    Real.cos (w - 2 * δ) ≤ Real.cos ((u * s - d) - 0) := by
  refine cos_le_cos_of_abs_le ?_ hwπ
  rw [sub_zero, show u * s - d = u * (s - d / u) by field_simp, abs_mul, abs_of_pos hu]
  calc u * |s - d / u| ≤ u * ((w - 2 * δ) / u) := mul_le_mul_of_nonneg_left h hu.le
    _ = w - 2 * δ := mul_div_cancel₀ _ hu.ne'

/-! ### The timing tolerances -/

/-- ★★ **The relay's flow time against `T_R`.** A flow time within `ρ` of the messenger's
arrival at the wall is within `ρ + d (1 − u)/u` of `T_R`. -/
theorem wall_packet_relay_time_bound {d u ρ t : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hd : 0 ≤ d)
    (h : |t - crossRelay d u| ≤ ρ) : |t - radarTR d| ≤ ρ + d * (1 - u) / u := by
  have h2 := abs_crossRelay_sub d hu hu1 hd
  calc |t - radarTR d| ≤ |t - crossRelay d u| + |crossRelay d u - radarTR d| :=
        abs_sub_le _ _ _
    _ ≤ ρ + d * (1 - u) / u := by rw [h2]; linarith

/-- ★★ **The return's flow time against `T_Ret`.** A flow time within `ρ` of the messenger's
return to the moving observer is within `ρ + 2d (1 − u)/u` of `T_Ret`. -/
theorem wall_packet_return_time_bound {d u v ρ t : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hv : 0 ≤ v) (hd : 0 ≤ d) (h : |t - crossReturn d u v| ≤ ρ) :
    |t - radarTRet d v| ≤ ρ + 2 * d * (1 - u) / u := by
  have h2 := abs_crossReturn_sub_le d hu hu1 hv hd
  calc |t - radarTRet d v| ≤ |t - crossReturn d u v| + |crossReturn d u v - radarTRet d v| :=
        abs_sub_le _ _ _
    _ ≤ ρ + 2 * d * (1 - u) / u := by linarith

/-- ★★ **The meeting's flow time against `T_M`.** The moving observer reaches the wall at
`d/v`, which is `T_M`: a flow time within `ρ` of it is within `ρ` of `T_M`. -/
theorem wall_observer_meeting_time_bound {d v ρ t : ℝ} (h : |t - d / v| ≤ ρ) :
    |t - radarTM d v| ≤ ρ := by
  rwa [radarTM]

end CSD.RecordLayer

end
