/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTwoCounts

/-!
# A return record, with the running clock's count at it

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #382 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainders (a) and (b) of #381.

On the composite carrier with its four pointers (UA-17 with (e)) the first pointer is coupled
to the near half of the messenger's ring. It advances by its rate times the messenger's
accumulated occupancy of the near half. The messenger of #379 is in the near half, leaves,
and comes back. If the pointer's rate is small enough that the first presence does not carry
it out of its ready arc, and large enough that the first presence and the return together
carry it into its displayed arc, its readout is written on the return leg: a record that the
messenger is back. The clock's own pointer of #381 runs throughout, so it has a count at that
write.

* `integral_le_of_forall_le`, `le_integral_of_forall_le`;
* `nearOcc`, `continuous_nearOcc`, `nearOcc_nonneg`, `nearOcc_le_one`, `nearOcc_eq`;
* `roundUpper`, `roundLower`, ★ `integral_nearOcc_le`, `le_integral_nearOcc` — on a round
  fibre the accumulated near-half occupancy is at most `roundUpper n δ` at the start of the
  return leg and at least `roundLower n δ` at its end;
* `two_roundUpper_le_roundLower` — for `δ ≤ π/48` and `fineEta n δ ≤ 1/48` the two bounds are a
  factor two apart, so a rate between them exists;
* `echoFstShown_twoCount_iff` — the first pointer's readout along the run of #381;
* ★ `return_record_with_count` — **a return record and the clock's count at it**: there is a
  flow time `τ` on the return leg such that the first pointer's readout is an `IsRecordWrite`
  of `true` with write interval `[roundBack n δ, τ]`, the clock's own pointer has a tick count
  `N` at `τ`, and `|N · 2π/R − τ| ≤ 2π/R`.

## Exact scope

* **One record, at the return, and a prepared start.** The messenger starts in the near half
  by preparation; nothing records an emission. The first pointer here is the return record,
  not the departure record of #367: its strength is chosen so that it does not write during
  the first presence. So the reading is "the clock's count at the return record, counted from
  the prepared start", not a difference of two records.
* **The write is located only within the return leg.** `τ` lies between the flow times of the
  predicted angles `3π/2 + δ` and `5π/2 − δ`. With the two arcs of #358 the pointer must go
  from at most `1/6` to `1/3`, which takes at least as much accumulated occupancy as the first
  presence gave, so the write interval is long. The count locates `τ` within one period; it
  does not sharpen where `τ` is.
* **The write does not certify a return.** It is a threshold of accumulated occupancy, as in
  #367. A carrier whose near-half occupancy is a suitable constant would give a readout with
  the same two clauses (a calculation, not in Lean). What shows the round trip is the
  occupancy statement of #379, which is not a record.
* **The clock's count is read at the flow time `τ`** (UA-7), and the time content is the
  clock's alone: `|N · 2π/R − τ| ≤ 2π/R` holds at every non-negative flow time (#366). The
  record contributes only that `τ` lies on the return leg. The record does not read the count
  and no degree of freedom holds the pair (UO-14 (b)); by the generic statement of #374 the
  pointers are cyclic coordinates, so nothing of the present form ties the count to a
  pointer's angle.
* **The gated pointer is present and plays no part.** Its strength `g_c` is free and it is not
  shown to tick.
* **The two rate conditions are hypotheses.** `two_roundUpper_le_roundLower` shows they are
  compatible when `δ ≤ π/48` and `fineEta n δ ≤ 1/48`; that some `n` gives `fineEta n δ ≤ 1/48`
  is not stated in Lean. The round fibres must also hold, and they
  constrain the first pointer's strength through `g₁ f(θ₂)`; for `trainF` at `θ₂ = 0` that
  term vanishes.
* **The arena and its limits are those of #381**: both clock pointers' profiles vanish on the
  fibre and the start is a product ray (null sets by calculations not in Lean); one clock
  start. The first pointer's write is driven by an occupancy, an expectation; it is a record in
  the sense of `IsRecordWrite` of a readout history, not an `ActualOccurrence`.
* **The round-trip time is the ring's.** The messenger comes back because the ring closes. The
  flow time of the return is fixed by the ring's length and the packet's velocity (UA-8). No
  distance is measured, there is no reflector and no second observer, and nothing here is
  evidence about Lorentz kinematics.
* **Earlier readings.** #372 has a separate clock's counts at a departure write and an arrival
  write, on the uncoupled product arena. #200 and #202 (echo arena), #270 (reflection, stated
  detector law) and #274 and #278 (relay, stated hybrid law) have emission and return records
  with a clock reading. What is new here is the place: the write is on the return leg of the
  free round trip of #379, and the clock is a tensor factor of the same composite carrier. It
  has one record, not two.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-4, UA-5, UA-7, UA-8, UA-12, UA-13, UA-15, UA-17, UO-14, UO-16, UD-118, UD-123, UD-125,
UD-126); `RecordLayer/UnifiedTwoCounts.lean` (#381: `gateFreeClockFlow`, `twoCountStart`,
`isSwing_free_twoCount`); `RecordLayer/UnifiedFineReturn.lean` (#379: `roundFibres`,
`fineEta`, `fineCarrier_far_le_before`, `fineCarrier_near_le_away`,
`fineCarrier_far_le_back`); `RecordLayer/UnifiedGateReturn.lean` (#380: `roundOut`,
`roundBack`, `roundEnd`); `RecordLayer/UnifiedArrivalRecord.lean`
(`isRecordWrite_of_integral_crossing`); `RecordLayer/UnifiedDepartureArrival.lean` (#367:
`echoFstShown_regionTwoFlow_iff`); `RecordLayer/UnifiedCompositeCarrier.lean` (#376:
`gateClockFlow_fst_pointer`); `RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Two bounds for an integral -/

theorem integral_le_of_forall_le {F : ℝ → ℝ} (hF : Continuous F) {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, F s ≤ c) : (∫ s in a..b, F s) ≤ c * (b - a) := by
  refine (intervalIntegral.integral_mono_on hab (hF.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b) h).trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

theorem le_integral_of_forall_le {F : ℝ → ℝ} (hF : Continuous F) {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, c ≤ F s) : c * (b - a) ≤ ∫ s in a..b, F s := by
  refine Eq.trans_le ?_ (intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable a b) (hF.intervalIntegrable a b) h)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-! ### The accumulated near-half occupancy through one round trip -/

section Near

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)

/-- **The coupled carrier's occupancy of the near half** of the messenger's ring, on the fibre
`(φ, χ)` of the two region pointers, at the flow time `s`. -/
noncomputable def nearOcc (φ χ : AddCircle (1 : ℝ)) (s : ℝ) : ℝ :=
  arenaObs (regionProj (farHalf (M + 1))ᶜ) (fineCarrier g₁ g₂ hf hh hn hL φ χ s)

theorem continuous_nearOcc (φ χ : AddCircle (1 : ℝ)) :
    Continuous (nearOcc g₁ g₂ hf hh hn hL φ χ) :=
  (continuous_arenaObs _).comp ((continuous_idxTwoCarrierU _ _ _ hf hh φ χ).arenaKick
    continuous_const)

theorem nearOcc_nonneg (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    0 ≤ nearOcc g₁ g₂ hf hh hn hL φ χ s :=
  arenaObs_regionProj_nonneg _ _

theorem nearOcc_le_one (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    nearOcc g₁ g₂ hf hh hn hL φ χ s ≤ 1 :=
  arenaObs_regionProj_le_one _ _

theorem nearOcc_eq (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    nearOcc g₁ g₂ hf hh hn hL φ χ s
      = 1 - arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ s) :=
  arenaObs_regionProj_compl _ _

/-- The bound on the accumulated near-half occupancy at the start of the return leg. -/
noncomputable def roundUpper (n : ℕ) (δ : ℝ) : ℝ :=
  1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + 3 * δ + fineEta n δ * (Real.pi - 2 * δ))

/-- The bound on the accumulated near-half occupancy at the end of the return leg. -/
noncomputable def roundLower (n : ℕ) (δ : ℝ) : ℝ :=
  (1 - fineEta n δ) * (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - 3 * δ))

/-- ★ **By the start of the return leg the near half has accumulated at most
`roundUpper n δ`**: all of the time up to the end of the first gap, the fraction `fineEta n δ`
of the absence, and all of the second gap. -/
theorem integral_nearOcc_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) :
    (∫ s in (0 : ℝ)..roundBack n δ, nearOcc g₁ g₂ hf hh hn hL φ χ s) ≤ roundUpper n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hF := continuous_nearOcc g₁ g₂ hf hh hn hL φ χ
  have hi : ∀ a b : ℝ, IntervalIntegrable (nearOcc g₁ g₂ hf hh hn hL φ χ) volume a b :=
    fun a b => hF.intervalIntegrable a b
  have h0a : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) := by positivity
  have hab : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hbc : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have h1 := integral_le_of_forall_le hF h0a (c := 1)
    fun s _ => nearOcc_le_one g₁ g₂ hf hh hn hL φ χ s
  have h2 := integral_le_of_forall_le hF hab (c := fineEta n δ) fun s hs => by
    rw [nearOcc_eq]
    exact fineCarrier_near_le_away g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
  have h3 := integral_le_of_forall_le hF hbc (c := 1)
    fun s _ => nearOcc_le_one g₁ g₂ hf hh hn hL φ χ s
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)) (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)))
  have e' := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)) (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ)))
  unfold roundBack roundUpper
  rw [← e', ← e]
  nlinarith

/-- **By the end of the return leg the near half has accumulated at least `roundLower n δ`**:
the fraction `1 − fineEta n δ` of the first presence and of the return leg. -/
theorem le_integral_nearOcc {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) :
    roundLower n δ ≤ ∫ s in (0 : ℝ)..roundEnd n δ, nearOcc g₁ g₂ hf hh hn hL φ χ s := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hF := continuous_nearOcc g₁ g₂ hf hh hn hL φ χ
  have hi : ∀ a b : ℝ, IntervalIntegrable (nearOcc g₁ g₂ hf hh hn hL φ χ) volume a b :=
    fun a b => hF.intervalIntegrable a b
  have h0a : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ) :=
    mul_nonneg hr2.le (by linarith)
  have hab : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hbc : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ)
      ≤ 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have h1 := le_integral_of_forall_le hF h0a (c := 1 - fineEta n δ) fun s hs => by
    rw [nearOcc_eq]
    have := fineCarrier_far_le_before g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
    linarith
  have h2 : 0 ≤ ∫ s in (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ))..(1250 * (n : ℝ) ^ 2
      * (3 * Real.pi / 2 + δ)), nearOcc g₁ g₂ hf hh hn hL φ χ s :=
    intervalIntegral.integral_nonneg hab fun s _ => nearOcc_nonneg g₁ g₂ hf hh hn hL φ χ s
  have h3 := le_integral_of_forall_le hF hbc (c := 1 - fineEta n δ) fun s hs => by
    rw [nearOcc_eq]
    have := fineCarrier_far_le_back g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
    linarith
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)) (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ)))
  have e' := intervalIntegral.integral_add_adjacent_intervals (hi 0 _) (hi
    (1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ)) (1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)))
  unfold roundEnd roundLower
  rw [← e', ← e]
  nlinarith

omit hn in
/-- **The two bounds are a factor two apart for a small margin and a small `fineEta`**, so a
rate `κ` with `κ · roundUpper ≤ 1/6` and `1/3 ≤ κ · roundLower` exists. -/
theorem two_roundUpper_le_roundLower (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 48)
    (hη : fineEta n δ ≤ 1 / 48) :
    2 * roundUpper n δ ≤ roundLower n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 := by positivity
  unfold roundUpper roundLower
  have h1 : fineEta n δ * (Real.pi - 2 * δ) ≤ 1 / 48 * Real.pi := by
    have := mul_le_mul hη (by linarith : Real.pi - 2 * δ ≤ Real.pi) (by linarith) (by norm_num)
    linarith
  have h2 : (47 / 48 : ℝ) * (3 * Real.pi / 2 - Real.pi / 16)
      ≤ (1 - fineEta n δ) * (3 * Real.pi / 2 - 3 * δ) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 2 * (Real.pi / 2 + 3 * δ + fineEta n δ * (Real.pi - 2 * δ))
      ≤ (1 - fineEta n δ) * (3 * Real.pi / 2 - 3 * δ) := by
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hr2
  nlinarith

end Near

/-! ### The return record and the clock's count at it -/

section Return

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
  (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ}
  (hβ : β m ≠ 0) {R : ℝ}

/-- **The first pointer's readout along the run of #381**, in terms of the accumulated
near-half occupancy. -/
theorem echoFstShown_twoCount_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc g₀ : ℝ)
    (θ ψ : KTorus) (t : ℝ) :
    echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
          Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
          contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1 = true
      ↔ pshift (rateAt g₁ 1 hf θ.2
          * ∫ s in (0 : ℝ)..t, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) θ ∈ displayArc := by
  rw [gateFreeClockFlow_twoCount_fst g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc g₀ θ ψ t]
  have hp := gateClockFlow_fst_pointer (Mc := Mc) (fineHop n (M + 1)) 3 g₁ g₂
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch
    contDiff_trainF t (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
    (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) θ ψ
    (χ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) trainF_lift_zero
  have hiff := echoFstShown_regionTwoFlow_iff (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) hf hh hc hch
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) θ ψ t
  rw [echoFstShown_eq_true_iff] at hiff ⊢
  have hmem : (gateClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (gateTrainStart hn hL Jc h0 h01 m hβ R θ ψ)).1
        ∈ echoFstDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)
        ∈ echoFstDisplay (2 * M + 1) := by
    show (_ : KTorus) ∈ displayArc ↔ (_ : KTorus) ∈ displayArc
    rw [gateTrainStart, hp]
  rw [hmem]
  exact hiff

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **A return record, with the running clock's count at it.** On the composite carrier with
four pointers, from `twoCountStart` with the first pointer ready, on a round fibre of the two
region pointers, with `0 ≤ δ ≤ π/2`: if the first pointer's rate `κ` satisfies
`κ · roundUpper n δ ≤ 1/6` and `1/3 ≤ κ · roundLower n δ`, there are a flow time `τ` on the
return leg and a number `N` such that

* the first pointer's readout history is an `IsRecordWrite` of `true` from the start, with
  write interval `[roundBack n δ, τ]` and window `1/(3κ)`: it does not display before the
  return leg begins and displays through the window after `τ`;
* the clock's own pointer has exactly `N` ticks by `τ`;
* `|N · 2π/R − τ| ≤ 2π/R`.

The times are flow times (UA-7). -/
theorem return_record_with_count (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (gc : ℝ)
    {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ : 0 < rateAt g₁ 1 hf θ.2)
    (hlo : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6)
    (hhi : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ) :
    ∃ (τ : ℝ) (N : ℕ), roundBack n δ ≤ τ ∧ τ ≤ roundEnd n δ
      ∧ IsRecordWrite
          (fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
              (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
              contDiff_trainF contDiff_trainF t
              (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1)
          0 (roundBack n δ) τ (1 / (3 * rateAt g₁ 1 hf θ.2)) true
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (fun t => gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
            (farHalf (M + 1)) Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch
            contDiff_trainF contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)) τ N
      ∧ |(N : ℝ) * (2 * Real.pi / R) - τ| ≤ 2 * Real.pi / R := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hTb0 : 0 ≤ roundBack n δ := by
    unfold roundBack
    positivity
  have hTbc : roundBack n δ ≤ roundEnd n δ := by
    unfold roundBack roundEnd
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hU := mul_le_mul_of_nonneg_left
    (integral_nearOcc_le g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ.le
  have hLo := mul_le_mul_of_nonneg_left
    (le_integral_nearOcc g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ.le
  obtain ⟨τ, hτ1, hτ2, hw⟩ := isRecordWrite_of_integral_crossing
    (continuous_nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun s => nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 s)
    (fun s => nearOcc_le_one g₁ g₂ hf hh hn hL θ.2 ψ.2 s) hκ hTb0 hTbc (hU.trans hlo)
    (hhi.trans hLo) hθ
    (hist := fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      (gateFreeClockFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1))
        Jc μ₀ μ₁ gc g₀ hf hh trainF_periodic trainF_periodic hc hch contDiff_trainF
        contDiff_trainF t (twoCountStart hn hL Jc h0 h01 m hβ R θ ψ)).1.1)
    (fun t => echoFstShown_twoCount_iff g₁ g₂ hf hh hn hL Jc h0 h01 m hβ hc hch gc g₀ θ ψ t)
  have hτ0 : 0 ≤ τ := hTb0.trans hτ1
  have hsw := isSwing_free_twoCount g₁ g₂ hf hh hn hL Jc h0 h01 h10 m hβ hRe hg hc hch gc θ ψ τ
  obtain ⟨N, hN⟩ := hsw.exists_tickCount hτ0
  exact ⟨τ, N, hτ1, hτ2, hw, hN, hsw.abs_tickTime_sub_le hτ0 hN⟩

end Return

end CSD.RecordLayer

end
