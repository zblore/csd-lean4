/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRoundTrip

/-!
# Two records and two counts in one run: one written during the absence, one on the return leg

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #383 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #382, by the
second pointer already on the arena, and part of Remainder (a) of #381.

#382 has one record, written on the return leg, from a prepared start. The arena already
carries a second region pointer, coupled to the far half of the messenger's ring. With its
strength in a stated window its readout is written during the interval of #379 on which the
far half's occupancy is high. So one run has two records, in order, and the clock's own
pointer of #381 has a count at a flow time by which each is complete. Both writes are
thresholds of accumulated occupancy; neither certifies an arrival or a return.

* `roundAway`, `roundAwayEnd` (the flow times of the predicted angles `π/2 + δ` and
  `3π/2 − δ`), `farOcc`, `continuous_farOcc`, `farOcc_nonneg`, `farOcc_le_one`;
* `farUpper`, `farLower`, `integral_farOcc_le`, `le_integral_farOcc` — on a round fibre the
  accumulated far-half occupancy is at most `farUpper n δ` when the absence begins and at
  least `farLower n δ` when it ends; `two_farUpper_le_farLower`;
* `echoSiteShown_twoCount_iff` — the second pointer's readout along the run of #381;
* ★ `arrival_and_return_records_with_counts` — **two records and two counts**: there are flow
  times `τ_a ≤ τ_r`, the first in the absence and the second on the return leg, such that the
  far pointer's readout is an `IsRecordWrite` whose write interval ends at `τ_a`, the near
  pointer's readout is an `IsRecordWrite` whose write interval ends at `τ_r`, the clock's own
  pointer has counts `N_a` and `N_r` at the two, and
  `|(N_r − N_a) · 2π/R − (τ_r − τ_a)| ≤ 4π/R`.

## Exact scope

* **Two records of one run, and the clock's counts at the flow times of their writes.** The
  difference of the counts, times the period, is within two periods of `τ_r − τ_a`. That time
  content is the clock's alone: the bound holds for any two non-negative flow times (#366).
  The records contribute where `τ_a` and `τ_r` lie. No hypothesis relates the period `2π/R` to
  `τ_r − τ_a`, and both counts may be zero. `τ_a` and `τ_r` are the ends of the stated write
  intervals, not the instants the readouts turn; each readout displays through its window
  after its `τ`.
* **Neither write certifies a transit or a return.** Both are thresholds of accumulated
  occupancy, as in #367. A carrier with suitable constant occupancies would give readouts with
  the same clauses (a calculation, not in Lean; not exhibited on this arena). What shows the
  round trip is the occupancy statement of #379, which is not a record.
* **The two times are located only within their intervals**: `τ_a` between the flow times of
  the predicted angles `π/2 + δ` and `3π/2 − δ`, `τ_r` between those of `3π/2 + δ` and
  `5π/2 − δ`. So `τ_r − τ_a` is known only to lie between `2500 n² δ` and
  `1250 n² (2π − 2δ)`. It is not a half round-trip time read to within the margin.
* **The counts are read at flow times** (UA-7). No record reads a count and no degree of
  freedom holds a pair (UO-14 (b)).
* **Not a radar time.** There is no emission record: the start is prepared. The two records
  are an arrival at the far half and a return, both read on the one messenger's ring. There is
  no reflector, no distance, and no second observer.
* **Four rate conditions are hypotheses.** `two_roundUpper_le_roundLower` and
  `two_farUpper_le_farLower` show each pair compatible for `δ ≤ π/48` and
  `fineEta n δ ≤ 1/48`; that some `n` gives the latter, and that rates in the two windows then
  exist, is not stated in Lean. The margin must be positive (`cos δ < 1`).
* **The arena and its limits are those of #381 and #382**: both clock pointers' profiles vanish
  on the fibre and the start is a product ray (null sets by calculations not in Lean); the
  round fibres of #379; one clock start; the gated pointer is present with a free strength, is
  not shown to tick and plays no part. The writes are `IsRecordWrite`s of readout histories, not
  `ActualOccurrence`s.
* **Earlier.** #360 and #366 have a clock's count at a position write, with the flow time shown
  to be the switching instant; #369 a clock and two detectors with counts at two readout switches
  in one run. #367 has a departure and an arrival record in one run, and #372 a separate clock's
  counts at both, on other arenas and for the crossing packet. What is new here is the pair
  (arrival, return) on the free round trip, with the clock a tensor factor of the same carrier.
  Nothing here is evidence about Lorentz kinematics.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-4, UA-5, UA-7, UA-8, UA-12, UA-13, UA-15, UA-17, UO-14, UO-16, UD-92, UD-94, UD-104,
UD-118, UD-123, UD-126, UD-127, UD-128); `RecordLayer/UnifiedRoundTrip.lean` (#382:
`nearOcc`, `roundUpper`, `roundLower`, `integral_nearOcc_le`, `le_integral_nearOcc`,
`echoFstShown_twoCount_iff`, `integral_le_of_forall_le`, `le_integral_of_forall_le`);
`RecordLayer/UnifiedTwoCounts.lean` (#381: `gateFreeClockFlow`, `twoCountStart`,
`isSwing_free_twoCount`); `RecordLayer/UnifiedFineReturn.lean` (#379);
`RecordLayer/UnifiedDepartureArrival.lean` (#367: `echoSiteShown_regionTwoFlow_iff`);
`RecordLayer/UnifiedArrivalRecord.lean` (#365: `isRecordWrite_of_integral_crossing`);
`RecordLayer/UnifiedCountAtWrite.lean` (#366: `IsSwing.abs_tickTime_sub_sub_le`);
`RecordLayer/UnifiedClockMessenger.lean` (#372).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-- The flow time at which the predicted angle is `π/2 + δ`: the start of the absence. -/
noncomputable def roundAway (n : ℕ) (δ : ℝ) : ℝ := 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)

/-- The flow time at which the predicted angle is `3π/2 − δ`: the end of the absence. -/
noncomputable def roundAwayEnd (n : ℕ) (δ : ℝ) : ℝ :=
  1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)

/-! ### The accumulated far-half occupancy -/

section Far

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)

/-- **The coupled carrier's occupancy of the far half** of the messenger's ring, on the fibre
`(φ, χ)` of the two region pointers, at the flow time `s`. -/
noncomputable def farOcc (φ χ : AddCircle (1 : ℝ)) (s : ℝ) : ℝ :=
  arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ s)

theorem continuous_farOcc (φ χ : AddCircle (1 : ℝ)) :
    Continuous (farOcc g₁ g₂ hf hh hn hL φ χ) :=
  (continuous_arenaObs _).comp ((continuous_idxTwoCarrierU _ _ _ hf hh φ χ).arenaKick
    continuous_const)

theorem farOcc_nonneg (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    0 ≤ farOcc g₁ g₂ hf hh hn hL φ χ s :=
  arenaObs_regionProj_nonneg _ _

theorem farOcc_le_one (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    farOcc g₁ g₂ hf hh hn hL φ χ s ≤ 1 :=
  arenaObs_regionProj_le_one _ _

/-- The bound on the accumulated far-half occupancy when the absence begins. -/
noncomputable def farUpper (n : ℕ) (δ : ℝ) : ℝ :=
  1250 * (n : ℝ) ^ 2 * (fineEta n δ * (Real.pi / 2 - δ) + 2 * δ)

/-- The bound on the accumulated far-half occupancy when the absence ends. -/
noncomputable def farLower (n : ℕ) (δ : ℝ) : ℝ :=
  (1 - fineEta n δ) * (1250 * (n : ℝ) ^ 2 * (Real.pi - 2 * δ))

/-- **When the absence begins the far half has accumulated at most `farUpper n δ`**: the
fraction `fineEta n δ` of the first presence and all of the first gap. -/
theorem integral_farOcc_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) :
    (∫ s in (0 : ℝ)..roundAway n δ, farOcc g₁ g₂ hf hh hn hL φ χ s) ≤ farUpper n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hF := continuous_farOcc g₁ g₂ hf hh hn hL φ χ
  have hi : ∀ a b : ℝ, IntervalIntegrable (farOcc g₁ g₂ hf hh hn hL φ χ) volume a b :=
    fun a b => hF.intervalIntegrable a b
  have h0a : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ) :=
    mul_nonneg hr2.le (by linarith)
  have hab : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have h1 := integral_le_of_forall_le hF h0a (c := fineEta n δ) fun s hs =>
    fineCarrier_far_le_before g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
  have h2 := integral_le_of_forall_le hF hab (c := 1)
    fun s _ => farOcc_le_one g₁ g₂ hf hh hn hL φ χ s
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)) (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)))
  unfold roundAway farUpper
  rw [← e]
  nlinarith

/-- **When the absence ends the far half has accumulated at least `farLower n δ`**: the
fraction `1 − fineEta n δ` of the absence. -/
theorem le_integral_farOcc {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) :
    farLower n δ ≤ ∫ s in (0 : ℝ)..roundAwayEnd n δ, farOcc g₁ g₂ hf hh hn hL φ χ s := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hF := continuous_farOcc g₁ g₂ hf hh hn hL φ χ
  have hi : ∀ a b : ℝ, IntervalIntegrable (farOcc g₁ g₂ hf hh hn hL φ χ) volume a b :=
    fun a b => hF.intervalIntegrable a b
  have h0a : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) := by positivity
  have hab : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..(1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)),
      farOcc g₁ g₂ hf hh hn hL φ χ s :=
    intervalIntegral.integral_nonneg h0a fun s _ => farOcc_nonneg g₁ g₂ hf hh hn hL φ χ s
  have h2 := le_integral_of_forall_le hF hab (c := 1 - fineEta n δ) fun s hs => by
    have := fineCarrier_near_le_away g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
    show 1 - fineEta n δ ≤ arenaObs _ _
    linarith
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)) (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)))
  unfold roundAwayEnd farLower
  rw [← e]
  nlinarith

omit hn in
/-- The two far bounds are a factor two apart for a small margin and a small `fineEta`. -/
theorem two_farUpper_le_farLower (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 48)
    (hη : fineEta n δ ≤ 1 / 48) :
    2 * farUpper n δ ≤ farLower n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 := by positivity
  unfold farUpper farLower
  have h1 : fineEta n δ * (Real.pi / 2 - δ) ≤ 1 / 48 * (Real.pi / 2) := by
    have := mul_le_mul hη (by linarith : Real.pi / 2 - δ ≤ Real.pi / 2) (by linarith)
      (by norm_num)
    linarith
  have h2 : (47 / 48 : ℝ) * (Real.pi - Real.pi / 24)
      ≤ (1 - fineEta n δ) * (Real.pi - 2 * δ) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 2 * (fineEta n δ * (Real.pi / 2 - δ) + 2 * δ)
      ≤ (1 - fineEta n δ) * (Real.pi - 2 * δ) := by
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hr2
  nlinarith

end Far

/-! ### The two records and the two counts -/

section Records

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}

/-- **The second pointer's readout along the run of #381**, in terms of the accumulated
far-half occupancy. -/
theorem echoSiteShown_twoCount_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc g₀ : ℝ)
    (θ ψ : KTorus) (t : ℝ) :
    echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
          Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
          contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1 = true
      ↔ pshift (rateAt g₂ 1 hh ψ.2
          * ∫ s in (0 : ℝ)..t, farOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) ψ ∈ displayArc := by
  rw [gateFreeClockFlow_twoCount_fst g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc g₀ θ ψ t]
  have hp := gateClockFlow_snd_pointer (Mc := Mc) (fineHop n (M + 1)) 3 g₁ g₂
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch
    contDiff_trainF t (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) θ ψ
    (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) trainF_lift_zero
  have hiff := echoSiteShown_regionTwoFlow_iff (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) hf hh hc hch
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) θ ψ t
  rw [echoSiteShown_eq_true_iff] at hiff ⊢
  have hmem : (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)).1
        ∈ echoSiteDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)
        ∈ echoSiteDisplay (2 * M + 1) := by
    show (_ : KTorus) ∈ displayArc ↔ (_ : KTorus) ∈ displayArc
    rw [gateTrainStart, hp]
  rw [hmem]
  exact hiff

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **Two records and two counts in one run.** On the composite carrier with four pointers,
from `twoCountStart` with both region pointers ready, on a round fibre, with `0 < δ ≤ π/2`
(in Lean `0 ≤ δ`, `δ ≤ π/2`, `cos δ < 1`), both rates positive: if
the far pointer's rate `κ₂` has `κ₂ · farUpper n δ ≤ 1/6` and `1/3 ≤ κ₂ · farLower n δ`, and
the near pointer's rate `κ₁` has `κ₁ · roundUpper n δ ≤ 1/6` and `1/3 ≤ κ₁ · roundLower n δ`,
there are flow times `τ_a ≤ τ_r` and numbers `N_a`, `N_r` such that

* `roundAway n δ ≤ τ_a ≤ roundAwayEnd n δ` and `roundBack n δ ≤ τ_r ≤ roundEnd n δ`;
* the far pointer's readout history is an `IsRecordWrite` of `true` from the start with write
  interval `[roundAway n δ, τ_a]`, and the near pointer's with `[roundBack n δ, τ_r]`;
* the clock's own pointer has exactly `N_a` ticks by `τ_a` and `N_r` by `τ_r`;
* `|(N_r − N_a) · 2π/R − (τ_r − τ_a)| ≤ 4π/R`.

The times are flow times (UA-7). Both writes are thresholds of accumulated occupancy and
certify neither an arrival nor a return; the counts may be zero. -/
theorem arrival_and_return_records_with_counts (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (gc : ℝ) {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2) (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6)
    (hhi₁ : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ)
    (hκ₂ : 0 < rateAt g₂ 1 hh ψ.2) (hlo₂ : rateAt g₂ 1 hh ψ.2 * farUpper n δ ≤ 1 / 6)
    (hhi₂ : 1 / 3 ≤ rateAt g₂ 1 hh ψ.2 * farLower n δ) :
    ∃ (τa τr : ℝ) (Na Nr : ℕ), roundAway n δ ≤ τa ∧ τa ≤ roundAwayEnd n δ
      ∧ roundBack n δ ≤ τr ∧ τr ≤ roundEnd n δ ∧ τa ≤ τr
      ∧ IsRecordWrite
          (fun t => echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
              (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
              contDiff_trainF contDiff_trainF t
              (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1)
          0 (roundAway n δ) τa (1 / (3 * rateAt g₂ 1 hh ψ.2)) true
      ∧ IsRecordWrite
          (fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
              (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
              contDiff_trainF contDiff_trainF t
              (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1)
          0 (roundBack n δ) τr (1 / (3 * rateAt g₁ 1 hf θ.2)) true
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
            (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
            contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) τa Na
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
            (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
            contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) τr Nr
      ∧ |((Nr : ℝ) - Na) * (2 * Real.pi / R) - (τr - τa)| ≤ 4 * Real.pi / R := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  -- the return record of #382
  obtain ⟨τr, Nr, hr1, hr2', hwr, hNr, -⟩ := return_record_with_count g₁ g₂ hf hh hn hL Jc h0
    h01 h10 m hβ hRe hg hc hch gc hθ hx hδ0 hδ hcos hκ₁ hlo₁ hhi₁
  -- the arrival record
  have hTa0 : 0 ≤ roundAway n δ := by
    unfold roundAway
    positivity
  have hTae : roundAway n δ ≤ roundAwayEnd n δ := by
    unfold roundAway roundAwayEnd
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hTeb : roundAwayEnd n δ ≤ roundBack n δ := by
    unfold roundAwayEnd roundBack
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hU := mul_le_mul_of_nonneg_left
    (integral_farOcc_le g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₂.le
  have hLo := mul_le_mul_of_nonneg_left
    (le_integral_farOcc g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₂.le
  obtain ⟨τa, ha1, ha2, hwa⟩ := isRecordWrite_of_integral_crossing
    (continuous_farOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun s => farOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 s)
    (fun s => farOcc_le_one g₁ g₂ hf hh hn hL θ.2 ψ.2 s) hκ₂ hTa0 hTae (hU.trans hlo₂)
    (hhi₂.trans hLo) hψ
    (hist := fun t => echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
        Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
        contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1)
    (fun t => echoSiteShown_twoCount_iff g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc g₀ θ ψ t)
  have hτa0 : 0 ≤ τa := hTa0.trans ha1
  have hτr0 : 0 ≤ τr := (hτa0.trans (ha2.trans hTeb)).trans hr1
  have hswa := isSwing_free_twoCount g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch gc θ ψ
    τa
  have hswr := isSwing_free_twoCount g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch gc θ ψ
    τr
  obtain ⟨Na, hNa⟩ := hswa.exists_tickCount hτa0
  exact ⟨τa, τr, Na, Nr, ha1, ha2, hr1, hr2', (ha2.trans hTeb).trans hr1, hwa, hwr, hNa, hNr,
    hswa.abs_tickTime_sub_sub_le hswr hτa0 hτr0 hNa hNr⟩

end Records

end CSD.RecordLayer

end
