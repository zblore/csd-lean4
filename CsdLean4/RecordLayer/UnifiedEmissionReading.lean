/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateRegions

/-!
# The emission reading: a gated pointer's count for a messenger packet and a clock packet

**Category:** 7-SigmaLayer (the record layer). BACKLOG #396 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, sixth brick: Remainder (a) of #395, the reading assembled. No new assumption beyond
UA-18.

#394 reads a gated pointer under three hypotheses; #395 proves two of them for packets on a
ring. This module proves the third, the clock's swing with a margin, and applies #394: for a
messenger packet and the flat clock packet of #392 on one ring, with the pointer coupled to
"the messenger is within the angle `w` of the clock" times the clock's level swap, the pointer
has a number of ticks that is fixed, up to one, while the two are apart.

* `scaledTrainF`, `scaledTrainF_periodic`, `contDiff_scaledTrainF`, `scaledTrainF_lift_zero`,
  `scaledTrainF_deriv_lift_zero` — the profile `g · trainF`: the strength of the coupling
  carried by the profile;
* ★★ `clock_packet_shift_le` — under the hypotheses of #388 and a lower bound `κ` of its
  margin: the strength `g = R/(16 Im C₀)` is at most `R/(16κ)` and up to `T` the clock
  pointer's displacement is within `R ε (2T/ρ + 3/ρ² + π/(2R²))/(4κ)` of
  `(1/4)(1 − cos R t)`;
* ★★ `narrow_clock_packet_swing`, `flat_clock_swing` — for every window of #391, and for the
  flat window of #392: `g ≤ R/5` and the displacement is within `1/24` of the swing up to
  `T = 2π n/R`;
* `clockPointerShift_trainF_eq` — the clock pointer's displacement of #357 is the ungated
  displacement of #394 for the profile `g · trainF`;
* `outside_arcs_flat_clock_le` — a messenger packet and the flat clock packet stay in their
  arcs, up to the messenger's budget plus `flatBudget`;
* `ringGateRun` — the run: the flow of #393 with the last pointer coupled to the gate, from
  the product of a messenger ray and a clock ray;
* ★★★ `flat_clock_emission_reading` — the reading.

## The reading

Let `R` be the clock's rate and `q = π/(2R)`. Suppose that at every flow time up to `t_c` the
two budgets add up to at most `ε (1 − cos δ)`; that up to `t_a ≤ 2π n/R` the messenger's
predicted angle is within `w − 2δ` of both levels' predicted angles; that on `[t_b, t_c]` it
is more than `w + 2δ` from both; and that `2 (R/5) ε t_a < 1/24` and
`2 (R/5) ε (t_c − t_b) ≤ 1/6`. Then for some strength `0 < g ≤ R/5` the gated pointer has a
count `N_a` at `t_a` with `|2π N_a − R t_a| ≤ 2π`, a count `N_b` at `t_b` with
`N_a ≤ N_b ≤ N_a + 6 g (t_b − t_a) + 3/2`, and at every flow time of `[t_b, t_c]` a count `N`
that is `N_b` or `N_b + 1`, with `|2π N − R t_a| ≤ 2π (6 g (t_b − t_a) + 7/2)`.

## Exact scope

* **The conditions are inequalities between real numbers, and no values are exhibited.** They
  are stated in the parameters `n, N, Δ, w, δ, ε, t_a, t_b, t_c`, the messenger's budget and
  the predicted angles. No choice of the parameters is shown to meet them together. That is
  to be done once, for the messenger of M6 (step (6)); for a messenger slower than the clock
  it would be thrown away.
* **Any messenger packet; the flat clock packet.** The messenger is any ring packet of
  `dirac_packet_limit` on the clock's ring with speed `1` in its energy: its own window, rest
  energy and budget. Its speed is not assumed; its predicted angular velocity is
  `vRel 1 μ p₀` over the ring's radius. No messenger is exhibited here.
* **The count is compared with the flow time `t_a`**, the last flow time at which the gate
  is certified open (UA-7). No event is recorded at `t_a` and no record holds it. The term
  `6 g (t_b − t_a)` is the closing of the gate; with `g ≤ R/5` it is at most `6/5` of the
  clock's phase over the closing.
* **Not yet the reading at an emission.** On this ring the messenger and the clock start
  together and separate once. Which event closes the gate, and that it is the messenger's
  departure from an observer, is the content of the next bricks (the wall and the return).
* **Counts of passages**, as #394: the record write of a tick is #358's up to `t_a` and is
  not restated; nothing is said after `t_c`.
* **Only the fibres where both profiles vanish, and only product starts**, as #393: the
  pointer starts at `1/12` on the fibre `0`, the clock packet is prepared a quarter turn
  early. Null sets.
* **For some strength.** The strength `g = R/(16 Im C₀)` is tuned to the clock packet (UA-4),
  as in #391; the statement records `0 < g ≤ R/5`.
* **A ring and two carriers.** UA-18 has a chain with walls and three carriers. The first
  pointer's observable `G₁` is any Hermitian matrix and plays no part.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-18, UO-16, UD-137, UD-138, UD-141, UD-148, UD-149, UD-150, UD-151, UD-152);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringNear`, `ringArc`, `ringGate_not_le`,
`ringGate_le`, `one_sub_sum_arenaObs_ringArc_ringPacket_le`,
`one_sub_sum_arenaObs_ringArc_devicePacket_le`, `flatBudget`, `flat_packet_budget_time`);
`RecordLayer/UnifiedGatedReading.lean` (#394: `coincFlow_gated_reading`,
`abs_arenaObs_siteSel_mul_levelSwap_le`); `RecordLayer/UnifiedCoincidenceFlow.lean` (#393:
`coincFlow`); `RecordLayer/UnifiedClockPacket.lean` (#388: `clock_packet_ticks`,
`abs_clockPointerShift_packet_sub_swing_le`, `packetSwingErr`);
`RecordLayer/UnifiedClockPacketInstance.lean` (#391: `narrow_clock_packet_ticks`, `ringRate`,
`ringHop`, `ringLen`); `RecordLayer/UnifiedClockPacketLocalised.lean` (#392: `flatWindow`,
`flatAmpN`); `RecordLayer/UnifiedDiracClockTicks.lean` (#358: `clock_tick_device`,
`clockSwingAmp`, `IsTickCount`); `RecordLayer/UnifiedDiracClock.lean` (#357:
`clockPointerShift`, `levelSwap`, `clockRead_of_lift_eq_zero`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The profile that carries the strength -/

/-- **The profile `g · trainF`**: the strength of the coupling carried by the profile. -/
def scaledTrainF (g : ℝ) : ℝ → ℝ := fun x => g * trainF x

theorem scaledTrainF_periodic (g : ℝ) : Function.Periodic (scaledTrainF g) 1 := fun x =>
  congrArg (fun y => g * y) (trainF_periodic x)

theorem contDiff_scaledTrainF (g : ℝ) : ContDiff ℝ ∞ (scaledTrainF g) :=
  contDiff_const.mul contDiff_trainF

/-- The scaled profile vanishes on the fibre `0`. -/
theorem scaledTrainF_lift_zero (g : ℝ) :
    (scaledTrainF_periodic g).lift (0 : AddCircle (1 : ℝ)) = 0 := by
  show (scaledTrainF_periodic g).lift (((0 : ℝ) : AddCircle (1 : ℝ))) = 0
  rw [Function.Periodic.lift_coe]
  simp [scaledTrainF, trainF]

/-- Its derivative on the fibre `0` is `−g`. -/
theorem scaledTrainF_deriv_lift_zero (g : ℝ) :
    (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g := by
  show (scaledTrainF_periodic g).deriv_periodic.lift (((0 : ℝ) : AddCircle (1 : ℝ))) = -g
  have h := (hasDerivAt_trainF 0).const_mul g
  rw [Function.Periodic.lift_coe, show scaledTrainF g = fun x => g * trainF x from rfl, h.deriv]
  simp

/-! ### The clock's swing, with a margin -/

section Swing

variable {M : ℕ}

/-- ★★ **The clock pointer's displacement against the swing, with the margin explicit.** Under
the hypotheses of `clock_packet_ticks` (#388), with `κ > 0` a lower bound of its margin
`(1 − ((μ₁ − μ₀)/μ₀)²)/2 − (π/(2R)) ε`: the strength `g = R/(16 Im C₀)` is positive and at
most `R/(16κ)`, and up to `T` the pointer's displacement is within
`R ε (2T/ρ + 3/ρ² + π/(2R²))/(4κ)` of `(1/4)(1 − cos R t)`. -/
theorem clock_packet_shift_le {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D ∨ |2 * Real.pi * m / ℓ + p₀| ≤ D)
    (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {J σ R ε : ℝ} (hJ : J = scaledHop c (ℓ / (M + 1 : ℕ)))
    (hσ : σ = 2 * J * Real.sin (ℓ / (M + 1 : ℕ) * p₀)) (hR : R = levelClockRate μ₀ μ₁ σ)
    (hε : ε = deviceDrift c μ₀ μ₁ D p₀) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hρm : ∀ m ∈ W, ρ ≤ modeRate M J μ₀ μ₁ m) {g : ℝ}
    (hg : g = R / (16 * (deviceCoherence
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).im))
    {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : κ ≤ (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε) {T : ℝ} (hT : 0 ≤ T) :
    ∃ hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))) ≠ 0,
      0 < g ∧ g ≤ R / (16 * κ)
      ∧ ∀ t, 0 ≤ t → t ≤ T →
        |clockPointerShift J μ₀ μ₁ g trainF_periodic (0 : AddCircle (1 : ℝ))
              (deviceRay _ hΨ) t - 1 / 4 * (1 - Real.cos (R * t))|
          ≤ R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) / (4 * κ) := by
  have hπ := Real.pi_pos
  have h1 : 0 < μ₁ := h0.trans h01
  have hR0 : 0 < R := hρ.trans_le hρR
  have hD := (noWrap_distinct_of_window (L := M + 1) hWin).2
  have hdev := clock_tick_device (M := M) trainF_periodic contDiff_trainF hc h0 h01 hℓ hWin hWD
    β hβ (0 : ℝ)
  simp only [← hJ, ← hσ, ← hR, ← hε] at hdev
  obtain ⟨hΨ, hre, him, -⟩ := hdev
  set C₀ := deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R)))) with hC₀
  have hκim : κ ≤ C₀.im := hκ.trans him
  have him0 : 0 < C₀.im := hκ0.trans_le hκim
  have hn1 : (deviceNorm
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re = 1 := by
    rw [deviceNorm_devicePacket h0 h1 hD, hβ]
    simp
  have hg0 : 0 < g := by rw [hg]; positivity
  have hε0 : 0 ≤ ε := by
    have := (abs_nonneg _).trans hre
    have h2 : 0 < Real.pi / (2 * R) := by positivity
    exact nonneg_of_mul_nonneg_right this h2
  have hsum : ∑ m ∈ W, ‖modeCoh M J μ₀ μ₁ β (-(Real.pi / (2 * R))) m‖
      * |modeRate M J μ₀ μ₁ m - R| ≤ ε := by
    rw [hε, hR, hσ, hJ]
    exact sum_norm_modeCoh_mul_le hc h0 h01.le hℓ hWD β hβ _
  have hfac : 0 ≤ 2 * T / ρ + 3 / ρ ^ 2 := by positivity
  have hfac' : 0 ≤ 2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2) := by positivity
  refine ⟨hΨ, hg0, ?_, fun t ht htT => ?_⟩
  · rw [hg]
    exact div_le_div_of_nonneg_left hR0.le (by positivity) (by linarith)
  · have hA : (1 / 4 : ℝ) = clockSwingAmp g trainF_periodic (0 : AddCircle (1 : ℝ)) R
        (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re C₀ := by
      rw [clockSwingAmp, hn1, trainF_deriv_lift_zero, hg]
      field_simp
      ring
    have hδeq : packetSwingErr g trainF_periodic (0 : AddCircle (1 : ℝ)) R
        (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re ρ C₀ ε T
        = R / (4 * C₀.im) * (ε * (2 * T / ρ + 3 / ρ ^ 2) + |C₀.re| / R) := by
      rw [packetSwingErr, hn1, trainF_deriv_lift_zero, mul_neg_one, abs_neg,
        abs_of_pos hg0, hg]
      field_simp
      ring
    have hsw := abs_clockPointerShift_packet_sub_swing_le g trainF_periodic trainF_lift_zero hD
      β (-(Real.pi / (2 * R))) hΨ hρ hρR hρm hsum ht htT
    rw [← hA, hδeq] at hsw
    refine hsw.trans ?_
    have hreR : |C₀.re| / R ≤ ε * (Real.pi / (2 * R ^ 2)) := by
      rw [div_le_iff₀ hR0]
      calc |C₀.re| ≤ Real.pi / (2 * R) * ε := hre
        _ = ε * (Real.pi / (2 * R ^ 2)) * R := by field_simp
    have hb : ε * (2 * T / ρ + 3 / ρ ^ 2) + |C₀.re| / R
        ≤ ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) := by
      rw [mul_add]
      linarith
    have hpos : 0 < R / (4 * C₀.im) := by positivity
    have hX : 0 ≤ R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) := by positivity
    calc R / (4 * C₀.im) * (ε * (2 * T / ρ + 3 / ρ ^ 2) + |C₀.re| / R)
        ≤ R / (4 * C₀.im) * (ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2))) :=
          mul_le_mul_of_nonneg_left hb hpos.le
      _ = R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) / (4 * C₀.im) := by ring
      _ ≤ R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2)) / (4 * κ) :=
          div_le_div_of_nonneg_left hX (by positivity) (by linarith)

/-- ★★ **Every narrow clock packet swings with a margin.** For the clock of
`narrow_clock_packet_ticks` (#391): for some strength `0 < g ≤ R/5`, up to `T = 2π n/R` the
clock pointer's displacement is within `1/24` of `(1/4)(1 − cos R t)`. -/
theorem narrow_clock_packet_swing {n K : ℕ} (hn : 0 < n) (hK : 0 < K) {p₀ : ℝ}
    (hp0 : 0 ≤ p₀) (hp1 : p₀ ≤ 9 / 10)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |(m : ℝ) / K - p₀| ≤ 1 / (600 * n) ∨ |(m : ℝ) / K + p₀| ≤ 1 / (600 * n))
    (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop K M) 1 (1 + Δ) W β
          (-(Real.pi / (2 * ringRate K M p₀ Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate K M p₀ Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / ringRate K M p₀ Δ →
        |clockPointerShift (ringHop K M) 1 (1 + Δ) g trainF_periodic (0 : AddCircle (1 : ℝ))
              (deviceRay _ hΨ) t - 1 / 4 * (1 - Real.cos (ringRate K M p₀ Δ * t))|
          ≤ 1 / 24 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hσsq : ringSigma K M p₀ ^ 2 ≤ 3 :=
    ringSigma_sq_le hK M (by rw [abs_of_nonneg hp0]; linarith)
  have hRlo : Δ / 2 ≤ ringRate K M p₀ Δ := half_le_levelClockRate hΔ0.le hσsq
  have hRhi : ringRate K M p₀ Δ ≤ Δ := levelClockRate_le_gap hΔ0.le _
  have hR0 : 0 < ringRate K M p₀ Δ := by linarith
  set R := ringRate K M p₀ Δ with hRd
  have hWD' : ∀ m ∈ W, |2 * Real.pi * m / ringLen K - p₀| ≤ 1 / (600 * n)
      ∨ |2 * Real.pi * m / ringLen K + p₀| ≤ 1 / (600 * n) := by
    intro m hm
    have e : 2 * Real.pi * (m : ℝ) / ringLen K = (m : ℝ) / K := by
      rw [ringLen]
      field_simp
    rw [e]
    exact hWD m hm
  have hD1 : (1 : ℝ) / (600 * n) ≤ 1 / 600 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hD0 : (0 : ℝ) < 1 / (600 * n) := by positivity
  have hρm : ∀ m ∈ W, Δ / 2 ≤ modeRate M (ringHop K M) 1 (1 + Δ) m := by
    intro m hm
    have hm1 : |(m : ℝ) / K| ≤ 1 := by
      rcases hWD m hm with h | h
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
    rw [modeRate, two_ringHop_mul_sin_angleZ hK]
    exact half_le_levelClockRate hΔ0.le (ringSigma_sq_le hK M hm1)
  set u := 1 / (600 * (n : ℝ)) * (2 * p₀ + 1 / (600 * n)) / 4 with hud
  have hεeq : deviceDrift 1 1 (1 + Δ) (1 / (600 * n)) p₀ = Δ * u := by
    rw [hud, deviceDrift, abs_of_nonneg hp0]
    ring
  have hu0 : 0 ≤ u := by
    rw [hud]
    positivity
  have hun : u * n ≤ 1 / 800 := by
    have hb : 2 * p₀ + 1 / (600 * n) ≤ 3 := by linarith
    have hDn : 1 / (600 * (n : ℝ)) * n = 1 / 600 := by field_simp
    calc u * n = 1 / (600 * n) * n * (2 * p₀ + 1 / (600 * n)) / 4 := by
          rw [hud]; ring
      _ = 1 / 600 * (2 * p₀ + 1 / (600 * n)) / 4 := by rw [hDn]
      _ ≤ 1 / 600 * 3 / 4 := by linarith
      _ = 1 / 800 := by norm_num
  have hule : u ≤ 1 / 800 := by nlinarith
  have hinv : Real.pi / (2 * R) * Δ ≤ Real.pi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : Real.pi / (2 * R) * (Δ * u) ≤ 1 / 100 := by
    calc Real.pi / (2 * R) * (Δ * u) = Real.pi / (2 * R) * Δ * u := by ring
      _ ≤ Real.pi * (1 / 800) := mul_le_mul hinv hule hu0 hπ.le
      _ ≤ 1 / 100 := by linarith
  have hΔe : ((1 + Δ - 1) / 1 : ℝ) = Δ := by ring
  have hΔsq : Δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hκ : (9 / 25 : ℝ) ≤ (1 - ((1 + Δ - 1) / 1) ^ 2) / 2 - Real.pi / (2 * R) * (Δ * u) := by
    rw [hΔe]
    linarith
  set T := 2 * Real.pi * n / R with hTd
  have hT0 : 0 ≤ T := by positivity
  have hX : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
      ≤ 3 / 50 := by
    have e : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
        = 8 * Real.pi * (u * n) + 12 * (R / Δ) * u + Real.pi / (2 * R) * (Δ * u) := by
      rw [hTd]
      field_simp
      ring
    have hrΔ : R / Δ ≤ 1 := (div_le_one hΔ0).2 hRhi
    have hrΔ0 : 0 ≤ R / Δ := by positivity
    have t1 : 8 * Real.pi * (u * n) ≤ 8 * 3.15 * (1 / 800) :=
      mul_le_mul (by linarith) hun (mul_nonneg hu0 hn'.le) (by norm_num)
    have t2 : 12 * (R / Δ) * u ≤ 12 * 1 * (1 / 800) :=
      mul_le_mul (by linarith) hule hu0 (by norm_num)
    rw [e]
    norm_num at t1 t2
    linarith
  obtain ⟨hΨ, hg0, hgle, hsw⟩ := clock_packet_shift_le (M := M) (c := 1) (μ₀ := 1)
    (μ₁ := 1 + Δ) (ℓ := ringLen K) (D := 1 / (600 * n)) (p₀ := p₀) one_pos one_pos
    (by linarith) (ringLen_pos hK) hWin hWD' β hβ (J := ringHop K M)
    (σ := ringSigma K M p₀) (R := R) (ε := Δ * u) rfl rfl rfl hεeq.symm (ρ := Δ / 2)
    (by positivity) hRlo hρm rfl (κ := 9 / 25) (by norm_num) hκ hT0
  refine ⟨_, hΨ, hg0, ?_, fun t ht htT => (hsw t ht htT).trans ?_⟩
  · have e : R / (16 * (9 / 25)) = R * (25 / 144) := by ring
    rw [e] at hgle
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    linarith

/-- **The flat clock packet swings with a margin**: the instance of
`narrow_clock_packet_swing` on the flat window of #392. -/
theorem flat_clock_swing {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ →
        |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
              (0 : AddCircle (1 : ℝ)) (deviceRay _ hΨ) t
            - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * t))|
          ≤ 1 / 24 :=
  narrow_clock_packet_swing (lo := 0) hn (by positivity) (by norm_num) (by norm_num)
    (flatWindow_mem_range hn hM) (fun m hm => Or.inl (flatWindow_width hn hN m hm))
    (flatAmpN N) (sum_norm_flatAmpN n hN) hΔ0 hΔ

/-- **The clock pointer's displacement of #357 is the ungated displacement of #394** for the
profile `g · trainF` on the fibre `0`. -/
theorem clockPointerShift_trainF_eq (J μ₀ μ₁ g : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) :
    clockPointerShift J μ₀ μ₁ g trainF_periodic (0 : AddCircle (1 : ℝ)) p t
      = -2 * (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))
        * ∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s) p) := by
  rw [clockPointerShift, scaledTrainF_deriv_lift_zero, trainF_deriv_lift_zero]
  simp only [clockRead_of_lift_eq_zero J μ₀ μ₁ g trainF_periodic trainF_lift_zero, clockFreeRead]
  ring

end Swing

/-! ### A messenger packet and the flat clock packet in their arcs -/

section Reading

variable {n N M : ℕ}

/-- **A messenger packet and the flat clock packet stay in their arcs.** For any messenger
packet of `dirac_packet_limit` on the clock's ring and the flat clock packet of #392, at
every flow time `s`: the two weights outside the arcs about the predicted angles, times
`1 − cos δ`, add up to at most the messenger's budget plus `flatBudget`. -/
theorem outside_arcs_flat_clock_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) {μ P D p₀ : ℝ} (hμ : 0 < μ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ t₁ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ) (flatWindow n N)
      (flatAmpN N) t₁ ≠ 0) (δ s : ℝ) :
    ((1 - ∑ k ∈ ringArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)) δ,
          arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
            (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ)))
        + (1 - ∑ k ∈ ringArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2) * (t₁ + s)) δ
            ∪ ringArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2) * (t₁ + s)) δ,
          arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))))
        * (1 - Real.cos δ)
      ≤ (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) D P
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (t₁ + s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have hWD' : ∀ m ∈ flatWindow n N,
      |2 * Real.pi * m / ringLen (1200 * n * N) - 1 / 2| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      have := Real.pi_pos
      field_simp
    rw [e]
    exact flatWindow_width hn hN m hm
  have hP : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hD0' : (0 : ℝ) ≤ 1 / (600 * n) := by positivity
  have hm := one_sub_sum_arenaObs_ringArc_ringPacket_le (M := M) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) one_pos hμ (ringLen_pos hK) hp₀ hD0 hWin hWD β hβ t₀ hψ δ s
  have hc := one_sub_sum_arenaObs_ringArc_devicePacket_le (M := M) (c := 1) (μ₀ := 1)
    (μ₁ := 1 + Δ) (ℓ := ringLen (1200 * n * N)) (P := 1 / 2) (D := 1 / (600 * n))
    (p₀ := 1 / 2) one_pos one_pos (by linarith) (ringLen_pos hK) hP hD0'
    (flatWindow_mem_range hn hM) hWD' (flatAmpN N) (sum_norm_flatAmpN n hN) t₁ hΨ δ s
  simp only [one_mul] at hm hc
  have b0 := flat_packet_budget_time hn hN hM (μ := 1) le_rfl (t₁ + s)
  have b1 := flat_packet_budget_time hn hN hM (μ := 1 + Δ) (by linarith) (t₁ + s)
  unfold ringHop
  rw [add_mul]
  linarith

/-- **The run**: the flow of #393 with its last pointer, of profile `g · trainF`, coupled to
"the messenger is within the angle `w` of the clock" times the clock's level swap, from the
product of a messenger ray `p` and a clock ray `q`, the last pointer at the angle `1/12` on
the fibre `0`. -/
noncomputable def ringGateRun {a b : ℕ} (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) (J μ μ₀ μ₁ : ℝ)
    (G₁ : Matrix ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2))
      ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2)) ℂ) (w g : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (θ : KTorus) (t : ℝ) : EchoSigma (a * (b + 1) + b) :=
  coincFlow e₁ e₂ (diracHam (L := M + 1) J μ) (deviceHam (L := M + 1) J μ₀ μ₁) G₁
    (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
      (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
      (levelSwap (ZMod (M + 1) × Fin 2)))
    trainF_periodic (scaledTrainF_periodic g) contDiff_trainF (contDiff_scaledTrainF g) t
    ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ),
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

/-- ★★★ **The emission reading.** A messenger packet and the flat clock packet of #392 on one
ring; the last pointer coupled to "within the angle `w`" times the clock's level swap; `R` the
clock's rate. Suppose that at every flow time up to `t_c` the two budgets add up to at most
`ε (1 − cos δ)`; that up to `t_a ≤ 2π n/R` the messenger's predicted angle is within `w − 2δ`
of both levels' predicted angles, and on `[t_b, t_c]` more than `w + 2δ` from both; and that
`2 (R/5) ε t_a < 1/24` and `2 (R/5) ε (t_c − t_b) ≤ 1/6`. Then for some strength
`0 < g ≤ R/5` the pointer has a count `N_a` at `t_a` with `|2π N_a − R t_a| ≤ 2π`, a count
`N_b` at `t_b` with `N_a ≤ N_b ≤ N_a + 6 g (t_b − t_a) + 3/2`, and at every flow time of
`[t_b, t_c]` a count `N` that is `N_b` or `N_b + 1`, with
`|2π N − R t_a| ≤ 2π (6 g (t_b − t_a) + 7/2)`. -/
theorem flat_clock_emission_reading (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {a b : ℕ}
    (e₁ : ZMod (M + 1) × Fin 2 ≃ Fin (a + 1))
    (e₂ : (ZMod (M + 1) × Fin 2) × Fin 2 ≃ Fin (b + 1)) {μ P D p₀ : ℝ} (hμ : 0 < μ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₀ : ℝ)
    (hψ : ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β t₀ ≠ 0)
    {G₁ : Matrix ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2))
      ((ZMod (M + 1) × Fin 2) × ((ZMod (M + 1) × Fin 2) × Fin 2)) ℂ} (hG₁ : G₁.IsHermitian)
    {θ : KTorus} (hθ : trainF_periodic.lift θ.2 = 0) {w δ ε ta tb tc : ℝ} (hδ : 0 < δ)
    (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb)
    (hbc : tb ≤ tc) (htaT : ta ≤ 2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ)
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      (1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) W β 0)).re
          + |t₀ + s| * limitErr 1 μ (ringLen (1200 * n * N)) D P
              (ringLen (1200 * n * N) / (M + 1 : ℕ)))
        + flatBudget n N (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
      ≤ ε * (1 - Real.cos δ))
    (hnear : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (w - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2)
              * (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
        ∧ Real.cos (w - 2 * δ)
          ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2)
              * (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)))
    (hapart : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2)
              * (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ p₀ * (t₀ + s)
            - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2)
              * (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ))
    (hopenSmall : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * ta < 1 / 24)
    (hclosedSmall : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (tc - tb) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ ∃ Na Nb : ℕ,
        IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
            {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
            (ringGateRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) G₁ w g
              (chainRay _ hψ) (deviceRay _ hΨ) θ) ta Na
          ∧ |(Na : ℝ) * (2 * Real.pi) - ringRate (1200 * n * N) M (1 / 2) Δ * ta|
              ≤ 2 * Real.pi
          ∧ IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
              {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
              (ringGateRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) G₁ w g
                (chainRay _ hψ) (deviceRay _ hΨ) θ) tb Nb
          ∧ Na ≤ Nb
          ∧ (Nb : ℝ) ≤ Na + 6 * g * (tb - ta) + 3 / 2
          ∧ ∀ t, tb ≤ t → t ≤ tc →
              ∃ N', IsTickCount {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ readyArc 2}
                  {x : EchoSigma (a * (b + 1) + b) | x.2 ∈ displayArc}
                  (ringGateRun e₁ e₂ (ringHop (1200 * n * N) M) μ 1 (1 + Δ) G₁ w g
                    (chainRay _ hψ) (deviceRay _ hΨ) θ) t N'
                ∧ Nb ≤ N' ∧ N' ≤ Nb + 1
                ∧ |(N' : ℝ) * (2 * Real.pi) - ringRate (1200 * n * N) M (1 / 2) Δ * ta|
                    ≤ 2 * Real.pi * (6 * g * (tb - ta) + 7 / 2) := by
  have hπ := Real.pi_pos
  have hK : 0 < 1200 * n * N := by positivity
  have hR : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hR0 : 0 < ringRate (1200 * n * N) M (1 / 2) Δ := by linarith
  obtain ⟨g, hΨ, hg0, hg5, hsw⟩ := flat_clock_swing (M := M) hn hN hM hΔ0 hΔ
  set R := ringRate (1200 * n * N) M (1 / 2) Δ with hRd
  have hcos : 0 < 1 - Real.cos δ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith : δ ≤ Real.pi) hδ
    rw [Real.cos_zero] at h
    linarith
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hzabs : |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| = g := by
    rw [hz, abs_neg, abs_of_pos hg0]
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hgε : 2 * g * ε * ta ≤ 2 * (R / 5) * ε * ta := by
    have : 0 ≤ ε * ta := mul_nonneg hε hta
    nlinarith
  have hgε' : 2 * g * ε * (tc - tb) ≤ 2 * (R / 5) * ε * (tc - tb) := by
    have : 0 ≤ ε * (tc - tb) := mul_nonneg hε (sub_nonneg.2 hbc)
    nlinarith
  have key_open : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ ringNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε :=
    fun s hs0 hs => le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (ringGate_not_le hδ.le hw (by linarith) (hnear s hs0 hs).1 (hnear s hs0 hs).2 _ _)
        hcos.le).trans
        ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
          (hbudget s hs0 (hs.trans (hab.trans hbc))))) hcos
  have key_closed : ∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε :=
    fun s hbs hs => le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (ringGate_le hδ.le (by linarith) hwπ (hapart s hbs hs).1 (hapart s hbs hs).2 _ _)
        hcos.le).trans
        ((outside_arcs_flat_clock_le hn hN hM hΔ0 hμ hp₀ hD0 hWin hWD β hβ t₀ _ hψ hΨ δ s).trans
          (hbudget s (hta.trans (hab.trans hbs)) hs))) hcos
  have hYs : ∀ i j : (ZMod (M + 1) × Fin 2) × Fin 2, i.1.1 ≠ j.1.1 →
      levelSwap (ZMod (M + 1) × Fin 2) i j = 0 := fun i j hij => by
    simp only [levelSwap, Matrix.of_apply]
    split_ifs with h
    · exact absurd (by rw [h.1]) hij
    · rfl
  obtain ⟨Na, Nb, hNa, hNa', hNb, hNab, hNb', hwin⟩ := coincFlow_gated_reading e₁ e₂
    (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (ringNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hG₁
    (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) hYs
    (fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q)
    trainF_periodic (scaledTrainF_periodic g) contDiff_trainF (contDiff_scaledTrainF g)
    (chainRay _ hψ) (deviceRay _ hΨ) (θ := θ)
    (ψ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) hθ
    (scaledTrainF_lift_zero g) (R := R) (A := 1 / 4) (δ₀ := 1 / 24) (ε := ε) (ta := ta)
    (tb := tb) (tc := tc) hR0 (by norm_num) (by norm_num) hε hta hab hbc
    (fun t ht0 hta' => by
      have h := hsw t ht0 (hta'.trans htaT)
      rw [clockPointerShift_trainF_eq] at h
      exact h)
    key_open key_closed
    (by
      show 2 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * ε
        * (tc - tb) ≤ 1 / 6
      rw [hzabs]
      linarith)
    (by
      show 1 / 24 + 2 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))|
        * ε * ta < rep (((1 / 12 : ℝ) : CircleFibre))
      rw [hzabs, hrep]
      linarith)
    (by
      show rep (((1 / 12 : ℝ) : CircleFibre)) + (1 / 24
        + 2 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * ε * ta)
        ≤ 1 / 6
      rw [hzabs, hrep]
      linarith)
    (by
      show 1 / 3 < rep (((1 / 12 : ℝ) : CircleFibre)) + 2 * (1 / 4) - (1 / 24
        + 2 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * ε * ta)
      rw [hzabs, hrep]
      linarith)
    (by
      show rep (((1 / 12 : ℝ) : CircleFibre)) + 2 * (1 / 4) + (1 / 24
        + 2 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * ε * ta)
        ≤ 5 / 6
      rw [hzabs, hrep]
      linarith)
  change (Nb : ℝ) ≤ Na + 6 * |(scaledTrainF_periodic g).deriv_periodic.lift
    (0 : AddCircle (1 : ℝ))| * (tb - ta) + 3 / 2 at hNb'
  rw [hzabs] at hNb'
  refine ⟨g, hΨ, hg0, hg5, Na, Nb, hNa, hNa', hNb, hNab, hNb', fun t hbt htc => ?_⟩
  obtain ⟨N', hN', h1, h2, h3⟩ := hwin t hbt htc
  change |(N' : ℝ) * (2 * Real.pi) - R * ta| ≤ 2 * Real.pi
    * (6 * |(scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ))| * (tb - ta)
      + 7 / 2) at h3
  rw [hzabs] at h3
  exact ⟨N', hN', h1, h2, h3⟩

end Reading

end CSD.RecordLayer

end
