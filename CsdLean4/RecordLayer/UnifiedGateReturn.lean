/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateCount
public import CsdLean4.RecordLayer.UnifiedFineReturn

/-!
# The gated pointer on the return leg: its swing comes back shifted by the clock's phase

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #380 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #379.

#379 bounded the gated pointer's displacement on three intervals of one round trip. Here the
three bounds are joined, with the two gaps, for the one-mode clock of #358. While the messenger
is away the gated pointer's displacement changes at a bounded rate, and after the return its
advance is close to the advance of the pointer of #357 on the clock's own arena. The clock's
phase has moved on in between. So on the return leg the gated pointer's displacement is

  `(1/4)(1 − cos R t) + (1/4)(cos R T_b − cos R T_a)`

up to a stated error, with `T_a` the last flow time before the first gap and `T_b` the first
flow time after the second: the swing of #377, shifted by a quarter of the difference of the
cosines of the clock's phase at return and at departure.

* `roundOut`, `roundBack`, `roundEnd` (the flow times of the predicted angles `π/2 − δ`,
  `3π/2 + δ`, `5π/2 − δ`), `gatePhaseShift`, `gateReturnErr`, `fineEta_nonneg`;
* `abs_gateClockShift_train_sub_le'` — the gated pointer's displacement changes by at most
  `2|g_c| (b − a)` between two flow times;
* ★ `abs_gateClockShift_return_sub_le` — **the gated pointer's displacement on the return leg
  is within `gateReturnErr` of the swing shifted by `gatePhaseShift`**;
* ★ `gateClock_return_not_ready` — **an obstruction for this coupling**: when the shift is
  between `1/12` and `5/12`, with the error as margin, the gated pointer is never in its ready
  arc on the return leg, so no tick begins there;
* ★ `isSwing_gateClock_return` — **when the shift and the error are together below `1/12`,
  the gated pointer is a swing again on the return leg**, read from a whole turn of the clock
  after the return; `gateClock_tickCount_return` — it has a tick count there, and the count
  times the period is within one period of the time since that turn.

## Exact scope

* **The gated pointer of UA-17 is not a tick counter across an absence.** Its rate is the
  product of the messenger's occupancy and the clock's reading, so an absence leaves it with an
  offset fixed by the clock's phases at departure and at return. Whether it ticks on the return
  leg depends on those two phases. `gateClock_return_not_ready` and `isSwing_gateClock_return`
  are the two cases; the cases in between are not treated. This is a statement about the
  product coupling of UA-17 (c) with the drift law of UA-5. It is not a statement about `Σ`,
  and another coupling may behave otherwise.
* **No radar time from the gated counts.** Where the gated pointer ticks, it counts turns of
  the clock while the messenger is present. The time the messenger is away is not held by it.
* **The hypotheses are not shown to be jointly satisfiable for either case.** The error
  `gateReturnErr` contains the two gaps, `2|g_c| · 5000 n² δ`, and the three intervals,
  `2|g_c| fineEta n δ · t` with `t` of order `n²`, so it is of order `|g_c| (n/δ² + n² δ)`.
  That it can be made smaller than `1/12` together with a shift in the stated range, for some
  clock, index and margin, is a calculation and not in Lean; it needs a clock whose rate falls
  with `n`. With the lower bounds of #378 for many ticks before departure it asks for
  `δ ≪ 1/K` and `n ≫ K/δ²` (the same calculation).
* **The arena and its limits are those of #376, #377 and #379**: a fibre where the gated
  pointer's profile vanishes and a product start (null sets by calculations not in Lean), the
  round fibres of #379, the one-point clock start of #358. The gate is the messenger's
  occupancy, not a record. The ticks are `IsSwing` and `IsTickCount` statements about a readout
  history, not `ActualOccurrence`s.
* **The return swing is read from a chosen flow time.** `isSwing_gateClock_return` is about
  the history `t ↦ flow (t + 2πj/R)` for a whole number `j` of turns with `2πj/R` on the return
  leg. That flow time is not given by a record.
* **Flow times throughout (UA-7).** No distance, no speed, no second observer.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-12, UA-17, UO-14, UO-16, UD-113, UD-119, UD-120, UD-121);
`RecordLayer/UnifiedFineReturn.lean` (#379: `round_gateClock_before`, `round_gateClock_away`,
`round_gateClock_back`, `roundFibres`, `fineEta`); `RecordLayer/UnifiedGateTicks.lean` (#377:
`gateTrainStart`, `gateClockFlow_train_thd`, `clockPointerShift_train`,
`isSwing_thd_of_abs_shift_sub_le`); `RecordLayer/UnifiedCompositeCarrier.lean` (#376:
`gateClockShift`, `abs_gateShift_sub_le_of_le`); `RecordLayer/UnifiedDiracClockTicks.lean`
(#358: `IsSwing`, `IsTickCount`); `RecordLayer/UnifiedCountAtWrite.lean`
(`IsSwing.abs_tickTime_sub_le`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The flow times of one round trip, the shift and the error -/

/-- The flow time at which the predicted angle is `π/2 − δ`: the end of the first interval. -/
noncomputable def roundOut (n : ℕ) (δ : ℝ) : ℝ := 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)

/-- The flow time at which the predicted angle is `3π/2 + δ`: the start of the return leg. -/
noncomputable def roundBack (n : ℕ) (δ : ℝ) : ℝ := 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ)

/-- The flow time at which the predicted angle is `5π/2 − δ`: the end of the return leg. -/
noncomputable def roundEnd (n : ℕ) (δ : ℝ) : ℝ := 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)

/-- **The shift of the return swing**: a quarter of the difference of the cosines of the
clock's phase at the start of the return leg and at the end of the first interval. -/
noncomputable def gatePhaseShift (R : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  1 / 4 * (Real.cos (R * roundBack n δ) - Real.cos (R * roundOut n δ))

/-- **The error on the return leg** at the flow time `t`: the three intervals at the rate
`2|g_c| fineEta n δ` and the two gaps at the rate `2|g_c|`. -/
noncomputable def gateReturnErr (gc : ℝ) (n : ℕ) (δ t : ℝ) : ℝ :=
  2 * |gc| * (fineEta n δ * t + 5000 * (n : ℝ) ^ 2 * δ)

theorem fineEta_nonneg (n : ℕ) {δ : ℝ} (hcos : Real.cos δ < 1) : 0 ≤ fineEta n δ := by
  have h : 0 < 1 - Real.cos δ := by linarith
  unfold fineEta
  positivity

section Return

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}

/-- The gated pointer's displacement changes by at most `2|g_c| (b − a)` between two flow
times, for the profile `trainF` on the fibre `χ₂ = 0`: its largest rate. -/
theorem abs_gateClockShift_train_sub_le' (gc : ℝ) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2))
    (J μ : ℝ) (A B : Finset (ZMod (M + 1))) {a b : ℝ} (hab : a ≤ b) :
    |gateClockShift J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh trainF_periodic φ χ
          (0 : AddCircle (1 : ℝ)) p q b
        - gateClockShift J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh trainF_periodic φ χ
          (0 : AddCircle (1 : ℝ)) p q a|
      ≤ 2 * |gc| * (b - a) := by
  have h := abs_gateShift_sub_le_of_le (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh trainF_periodic φ χ (0 : AddCircle (1 : ℝ)) p q
    (fun r => arenaObs_regionProj_nonneg A r) (abs_nonneg gc) (norm_clockB_le gc) hab
    (η := 1) (fun u _ => arenaObs_regionProj_le_one A _)
  rw [trainF_deriv_lift_zero, abs_neg, abs_one, mul_one, one_mul] at h
  exact h

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {gc : ℝ}
  (hg : gc = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **The gated pointer's displacement on the return leg is the swing of #377 shifted by
`gatePhaseShift`, within `gateReturnErr`.** The messenger starts on the fine packet of index
`n`, the clock on the one-mode start of #358, the two region pointers on a round fibre, the
gated pointer's profile is `trainF` on the fibre `χ₂ = 0`, and `0 ≤ δ ≤ π/2`. At every flow
time `t` of the return leg, `roundBack n δ ≤ t ≤ roundEnd n δ`. -/
theorem abs_gateClockShift_return_sub_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) {t : ℝ} (ht0 : roundBack n δ ≤ t) (ht : t ≤ roundEnd n δ) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁
          gc hf hh trainF_periodic φ χ (0 : AddCircle (1 : ℝ))
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
          (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
            (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t
        - (1 / 4 * (1 - Real.cos (R * t)) + gatePhaseShift R n δ)|
      ≤ gateReturnErr gc n δ t := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) 2
  have hη := fineEta_nonneg n hcos
  unfold roundBack at ht0
  unfold roundEnd at ht
  unfold gatePhaseShift gateReturnErr roundOut roundBack
  have hTa0 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ) :=
    mul_nonneg (by positivity) (by linarith)
  have hTb0 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) := by positivity
  have ht00 : 0 ≤ t := hTb0.trans ht0
  have hgapa : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have haway : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hgapb : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- before the messenger leaves
  have h1 := round_gateClock_before g₁ g₂ Jc μ₀ μ₁ gc hf hh trainF_periodic hn hL hx
    trainF_lift_zero
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) hδ0 hcos hTa0 le_rfl
  rw [idxPointerShift_clock, clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg hTa0,
    trainF_deriv_lift_zero, abs_neg, abs_one, mul_one] at h1
  -- the first gap
  have h2 := abs_gateClockShift_train_sub_le' (Mc := Mc) g₁ g₂ hf hh Jc (μ₀ := μ₀) (μ₁ := μ₁) gc
    φ χ (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) (fineHop n (M + 1)) 3
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) hgapa
  -- while the messenger is away
  have h3 := round_gateClock_away g₁ g₂ Jc μ₀ μ₁ gc hf hh trainF_periodic hn hL hx
    (0 : AddCircle (1 : ℝ))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) hδ0 hcos le_rfl haway le_rfl
  rw [trainF_deriv_lift_zero, abs_neg, abs_one, mul_one] at h3
  -- the second gap
  have h4 := abs_gateClockShift_train_sub_le' (Mc := Mc) g₁ g₂ hf hh Jc (μ₀ := μ₀) (μ₁ := μ₁) gc
    φ χ (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) (fineHop n (M + 1)) 3
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) hgapb
  -- after the messenger is back
  have h5 := round_gateClock_back g₁ g₂ Jc μ₀ μ₁ gc hf hh trainF_periodic hn hL hx
    trainF_lift_zero
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) hδ0 hcos le_rfl ht0 ht
  rw [idxPointerShift_clock, idxPointerShift_clock,
    clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg ht00,
    clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg hTb0,
    trainF_deriv_lift_zero, abs_neg, abs_one, mul_one] at h5
  have hpos : 0 ≤ |gc| * (fineEta n δ * ((n : ℝ) ^ 2 * δ)) :=
    mul_nonneg (abs_nonneg gc) (mul_nonneg hη (mul_nonneg hr2.le hδ0))
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨h3a, h3b⟩ := abs_le.1 h3
  obtain ⟨h4a, h4b⟩ := abs_le.1 h4
  obtain ⟨h5a, h5b⟩ := abs_le.1 h5
  rw [abs_le]
  constructor <;> linarith

/-- ★ **An obstruction for the product coupling: a shifted return swing never rests.** With
the start of `gateTrainStart` on a round fibre, if the shift is above `1/12` and at most `5/12`
by more than the error at the end of the return leg, then at no flow time of the return leg is
the gated pointer in its ready arc. No tick begins there, whatever the clock does. -/
theorem gateClock_return_not_ready (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hlo : 1 / 12 + gateReturnErr gc n δ (roundEnd n δ) < gatePhaseShift R n δ)
    (hhi : gatePhaseShift R n δ + gateReturnErr gc n δ (roundEnd n δ) ≤ 5 / 12) {t : ℝ}
    (ht0 : roundBack n δ ≤ t) (ht : t ≤ roundEnd n δ) :
    gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁
        gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)
      ∉ triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) := by
  have hη := fineEta_nonneg n hcos
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have key := abs_le.1 (abs_gateClockShift_return_sub_le g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ
    hRe hg hx hδ0 hδ hcos ht0 ht)
  have hmono : gateReturnErr gc n δ t ≤ gateReturnErr gc n δ (roundEnd n δ) := by
    unfold gateReturnErr
    have h1 := mul_le_mul_of_nonneg_left ht hη
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity : (0 : ℝ) ≤ 2 * |gc|)
  have hc1 := Real.cos_le_one (R * t)
  have hc2 := Real.neg_one_le_cos (R * t)
  intro hmem
  have hmem' : (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
      (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
      (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)).2 ∈ readyArc 2 := hmem
  rw [gateClockFlow_train_thd g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc θ ψ t] at hmem'
  have hmem'' : rep (pshift (gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
      (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic θ.2 ψ.2 (0 : AddCircle (1 : ℝ))
      (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
      (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
        (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t)
      ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))).1
      ∈ Ioc (0 : ℝ) (shearWidth 2) := hmem'
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by
    show 0 < rep (((1 / 12 : ℝ) : CircleFibre)) + _
    rw [hrep]
    linarith [key.1], by
    show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ 1
    rw [hrep]
    linarith [key.2]⟩] at hmem''
  have h3 : rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ 1 / 6 := hmem''.2
  rw [hrep] at h3
  linarith [key.1]

/-- ★ **When the clock's phases match, the gated pointer is a swing again on the return
leg.** With the start of `gateTrainStart` on a round fibre, let `j` be a whole number of turns
of the clock with `2πj/R` on the return leg, and `T ≥ 0` with `2πj/R + T` still on it. If
`ε = |gatePhaseShift| + gateReturnErr` at the end of the return leg is below `1/12`, the
history read from the flow time `2πj/R` is a swing at the rate `R` up to `T`, with thresholds
`±4ε`. -/
theorem isSwing_gateClock_return (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hε : |gatePhaseShift R n δ| + gateReturnErr gc n δ (roundEnd n δ) < 1 / 12) (j : ℕ)
    (hj : roundBack n δ ≤ 2 * Real.pi * j / R) {T : ℝ}
    (hT : 2 * Real.pi * j / R + T ≤ roundEnd n δ) :
    IsSwing (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF
        (t + 2 * Real.pi * j / R) (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ))
      R (4 * (|gatePhaseShift R n δ| + gateReturnErr gc n δ (roundEnd n δ)))
      (-(4 * (|gatePhaseShift R n δ| + gateReturnErr gc n δ (roundEnd n δ)))) T := by
  have hη := fineEta_nonneg n hcos
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = |gatePhaseShift R n δ| + gateReturnErr gc n δ (roundEnd n δ) :=
    ⟨_, rfl⟩
  rw [← hεdef] at hε ⊢
  have herr0 : 0 ≤ gateReturnErr gc n δ (roundEnd n δ) := by
    unfold gateReturnErr roundEnd
    have : (0 : ℝ) ≤ 5 * Real.pi / 2 - δ := by linarith [Real.pi_pos]
    positivity
  have hε0 : 0 ≤ ε := by
    rw [hεdef]
    exact add_nonneg (abs_nonneg _) herr0
  have hmono : ∀ t, t ≤ roundEnd n δ →
      gateReturnErr gc n δ t ≤ gateReturnErr gc n δ (roundEnd n δ) := fun t ht => by
    unfold gateReturnErr
    have h1 := mul_le_mul_of_nonneg_left ht hη
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity : (0 : ℝ) ≤ 2 * |gc|)
  have hsw := isSwing_thd_of_abs_shift_sub_le (A := 1 / 4) (δ := ε) (T := T) hR (by norm_num) hε0
    (fun t _ _ => gateClockFlow_train_thd (R := R) g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc
      θ ψ (t + 2 * Real.pi * j / R))
    (fun t ht0 htT => by
      have hta : roundBack n δ ≤ t + 2 * Real.pi * j / R := by linarith
      have htb : t + 2 * Real.pi * j / R ≤ roundEnd n δ := by linarith
      have key := abs_gateClockShift_return_sub_le g₁ g₂ hf hh hn hL Jc h0 h01 h10
        m hβ hRe hg hx hδ0 hδ hcos hta htb
      have hm := hmono _ htb
      have hcosj : Real.cos (R * (t + 2 * Real.pi * j / R)) = Real.cos (R * t) := by
        have e : R * (t + 2 * Real.pi * j / R) = R * t + j * (2 * Real.pi) := by
          field_simp
        rw [e, Real.cos_add_nat_mul_two_pi]
      rw [hcosj] at key
      have e : ∀ G F s : ℝ, G - F = (G - (F + s)) + s := fun G F s => by ring
      rw [hεdef, e _ _ (gatePhaseShift R n δ)]
      exact (abs_add_le _ _).trans
        ((add_le_add (key.trans hm) le_rfl).trans_eq (add_comm _ _)))
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)); rw [hrep]; exact hε)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ _; rw [hrep]; linarith)
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)) + _ - _; rw [hrep]; linarith)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ + _ ≤ _; rw [hrep]; linarith)
  have e₁ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) - ε) / (1 / 4) = 4 * ε := by
    rw [hrep]
    ring
  have e₂ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) + ε) / (1 / 4)
      = -(4 * ε) := by
    rw [hrep]
    ring
  rw [e₁, e₂] at hsw
  exact hsw

/-- **A tick count on the return leg.** Under the hypotheses of `isSwing_gateClock_return`
the history read from the flow time `2πj/R` has a tick count `N` at `T`, and
`|N · 2π/R − T| ≤ 2π/R`. The count may be zero. -/
theorem gateClock_tickCount_return (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hε : |gatePhaseShift R n δ| + gateReturnErr gc n δ (roundEnd n δ) < 1 / 12) (j : ℕ)
    (hj : roundBack n δ ≤ 2 * Real.pi * j / R) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : 2 * Real.pi * j / R + T ≤ roundEnd n δ) :
    ∃ N : ℕ, IsTickCount (triThdReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (triThdDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
        (fun t => gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
          (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF
          (t + 2 * Real.pi * j / R) (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)) T N
      ∧ |(N : ℝ) * (2 * Real.pi / R) - T| ≤ 2 * Real.pi / R := by
  have hsw := isSwing_gateClock_return g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hx
    hδ0 hδ hcos hε j hj hT
  obtain ⟨N, hN⟩ := hsw.exists_tickCount hT0
  exact ⟨N, hN, hsw.abs_tickTime_sub_le hT0 hN⟩

end Return

end CSD.RecordLayer

end
