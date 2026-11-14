/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReadoutRise

/-!
# One start that meets every hypothesis of the three records and of the dip

**Category:** 7-SigmaLayer (the record layer). BACKLOG #387 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16. No new assumption.

#382 to #386 each carried the caveat that the rate windows, the round-fibre bound and (for
#385 and #386) the rate condition and the tightened window are hypotheses, and that no start
was shown in Lean to meet them together. This module exhibits one.

**The instance.** All three region pointers have the profile `trainF` and start at
`dipAngle`: moving angle `1/30`, conserved angle `0`. On that fibre the profile vanishes and
its derivative is `−1`, so the rate of a pointer of strength `g` is `2g`
(`rateAt_trainF_dipAngle`) and the pair `(0, 0)` is a round fibre for every strength (#379).
The strengths are `g₁ = 1/(6 · roundLower)`, `g₂ = 1/(6 · farLower)` and
`g₃ = 1/(6 (1 − fineEta) roundOut)`. For a margin `0 < δ ≤ π/96` and a packet index with
`fineEta n δ ≤ 1/96` they satisfy every rate hypothesis of #384 (at `T₁ = 0`), #385 and #386
(`dipInstance_windows`). At `δ = π/96` every `n ≥ 73744` is such an index
(`fineEta_le_of_le`).

* `one_sub_cos_pi_div_ninetySix`, `fineEta_le_of_le` — a packet index exists;
* `dipAngle`, `dipAngle_snd`, `rep_dipAngle`, `dipAngle_mem_readyArc`,
  `rateAt_trainF_dipAngle`;
* ★ `dipInstance_windows` — the windows, the tightened window and the rate condition together;
* ★ `dipInstance_three_records` — the conclusion of `three_records_with_counts` (#384);
* ★ `dipInstance_readouts_certify_dip` — the conclusion of `threeRecord_readouts_certify_dip`
  (#386) for every `F` that reproduces the stated readouts;
* ★ `dipInstance_nearOcc_dip`, ★ `exists_nearOcc_dip` — the run's own near-half occupancy has
  the dip; the second has no hypothesis left.

## Exact scope

* **Satisfiability, nothing more.** The conclusions are those of #384, #385 and #386, word for
  word, with their limits: three threshold writes that certify no departure, arrival or
  return; counts read at flow times that may all be zero; a drop, a rise and a dip of means
  over stated intervals of flow time; premises that are readouts at flow times (UA-7), held by
  no record; no reflector, no second observer, no radar time. What is added is that the
  hypotheses are not contradictory.
* **One start, a null set.** The three pointers start at one point: angle `1/30`, fibres
  `0`. The start is a product ray on the fine packet and one clock start. That the hypotheses
  hold on a set of starts of positive measure is not stated in Lean. The windows are met
  with equality at their lower ends (`κ · bound = 1/3`), so this instance is at the edge of
  each window, not inside it.
* **On this fibre no region pointer acts back on the messenger.** With `trainF` and the
  conserved angles `0` all three profiles vanish, so the messenger moves as the free packet
  on the ring and each pointer is turned by it without turning it. The round-fibre bound
  holds trivially. Nothing here exercises the back-reaction that #379 bounds.
* **The strengths are tuned to the ring's schedule.** Each is the reciprocal of an occupancy
  bound of #382 to #384, which depends on `n` and `δ`. They are apparatus input (UA-4), chosen
  with the round trip's timing known in flow time.
* **The numbers are not physical.** The index bound `73744` comes from `1 − cos(π/96) ≥
  1/4608` and is not sharp. With `640000 n³ ≤ M + 1` it gives a ring of more than `2 · 10²⁰`
  sites (a calculation). No scale is attached to any of it.
* **What is left as a hypothesis** in the three instance theorems: the margin and the index
  bound, the ring's length, and the clock's parameters (`0 < μ₀ < μ₁ < 2μ₀`, a non-zero
  amplitude, and the definitions of its rate and of its pointer's strength).
  `dipInstance_readouts_certify_dip` keeps the three premises about `F`: they are what the
  certificate is about. `exists_nearOcc_dip` has no hypothesis; it is a statement about the
  coupled carrier's occupancy and involves no pointer and no clock.
* **The clock plays no part**, as in #385 and #386. No term couples it to the messenger in the
  variant of #384.
* **Earlier.** #379 has `zero_mem_roundFibres_trainF`; #382 and #383 the factor-two room
  lemmas; #386 the factor `5/2`. Nothing here is evidence about Lorentz kinematics.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-17, UO-16, UD-130, UD-132, UD-134, UD-135, UD-136);
`RecordLayer/UnifiedReadoutRise.lean` (#386: `threeRecord_readouts_certify_dip`,
`threeRecord_nearOcc_dip`, `five_halves_roundUpper_le_roundLower`);
`RecordLayer/UnifiedThreeRecords.lean` (#384: `three_records_with_counts`);
`RecordLayer/UnifiedArrivalReturn.lean` (#383: `two_farUpper_le_farLower`);
`RecordLayer/UnifiedFineReturn.lean` (#379: `fineEta`, `zero_mem_roundFibres_trainF`);
`RecordLayer/DiracPointerHamiltonian.lean` (`trainF_lift_zero`, `trainF_deriv_lift_zero`);
`RecordLayer/CircleFibre.lean` (`rep_coe_of_mem_Ioc`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The packet index -/

/-- The margin `π/96` is far enough from zero: `1/4608 ≤ 1 − cos (π/96)`. -/
theorem one_sub_cos_pi_div_ninetySix : 1 / 4608 ≤ 1 - Real.cos (Real.pi / 96) := by
  have hπ := Real.pi_pos
  have h := Real.cos_le_one_sub_mul_cos_sq (x := Real.pi / 96)
    (by rw [abs_of_pos (by positivity)]; linarith)
  have e : 2 / Real.pi ^ 2 * (Real.pi / 96) ^ 2 = 1 / 4608 := by
    field_simp
    norm_num
  linarith

/-- **A packet index exists.** For every `n ≥ 73744` the leak bound at the margin `π/96` is
at most `1/96`. -/
theorem fineEta_le_of_le {n : ℕ} (hn : 73744 ≤ n) : fineEta n (Real.pi / 96) ≤ 1 / 96 := by
  have hc := one_sub_cos_pi_div_ninetySix
  have hn' : (73744 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (1 - Real.cos (Real.pi / 96)) ≤ 4608 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : 1 / (6 * (n : ℝ)) ≤ 1 / (6 * 73744) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (1 - Real.cos (Real.pi / 96)) :=
    div_nonneg zero_le_one (by linarith)
  unfold fineEta
  calc 1 / (6 * (n : ℝ)) * (1 + 1 / (1 - Real.cos (Real.pi / 96)))
      ≤ 1 / (6 * 73744) * (1 + 4608) :=
        mul_le_mul h2 (by linarith) (by linarith) (by norm_num)
    _ = 1 / 96 := by norm_num

/-! ### The start angle and the rates -/

/-- **The start of each region pointer in the instance**: moving angle `1/30`, on the fibre
`0`. -/
noncomputable def dipAngle : KTorus := ((((1 / 30 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))

theorem dipAngle_snd : dipAngle.2 = 0 := rfl

theorem rep_dipAngle : rep dipAngle.1 = 1 / 30 :=
  rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩

theorem dipAngle_mem_readyArc : dipAngle ∈ readyArc 2 := by
  show rep dipAngle.1 ∈ Ioc (0 : ℝ) (shearWidth 2)
  rw [rep_dipAngle, shearWidth_two]
  constructor <;> norm_num

/-- With the profile `trainF` the rate on the fibre `0` is twice the strength. -/
theorem rateAt_trainF_dipAngle (g : ℝ) : rateAt g 1 trainF_periodic dipAngle.2 = 2 * g := by
  rw [dipAngle_snd, rateAt, trainF_deriv_lift_zero]
  ring

/-- ★ **The rate windows, the tightened window and the rate condition hold together.** For
a margin `0 < δ ≤ π/96` and a packet index with `fineEta n δ ≤ 1/96`, the three strengths
`1/(6 · roundLower)`, `1/(6 · farLower)` and `1/(6 (1 − fineEta) roundOut)` with the profile
`trainF` and the three pointers at `dipAngle` satisfy every rate hypothesis of
`three_records_with_counts` (#384, at `T₁ = 0`), of `threeRecord_readouts_certify_drop` (#385)
and of `threeRecord_readouts_certify_rise` (#386). -/
theorem dipInstance_windows {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ Real.pi / 96) (hη : fineEta n δ ≤ 1 / 96) {g₁ g₂ g₃ : ℝ}
    (hg₁ : g₁ = 1 / (6 * roundLower n δ)) (hg₂ : g₂ = 1 / (6 * farLower n δ))
    (hg₃ : g₃ = 1 / (6 * ((1 - fineEta n δ) * roundOut n δ))) :
    Real.cos δ < 1
      ∧ 0 < rateAt g₁ 1 trainF_periodic dipAngle.2
      ∧ rateAt g₁ 1 trainF_periodic dipAngle.2 * roundUpper n δ ≤ 1 / 6 - rep dipAngle.1
      ∧ 1 / 3 ≤ rateAt g₁ 1 trainF_periodic dipAngle.2 * roundLower n δ
      ∧ 0 < rateAt g₂ 1 trainF_periodic dipAngle.2
      ∧ rateAt g₂ 1 trainF_periodic dipAngle.2 * farUpper n δ ≤ 1 / 6
      ∧ 1 / 3 ≤ rateAt g₂ 1 trainF_periodic dipAngle.2 * farLower n δ
      ∧ 0 < rateAt g₃ 1 trainF_periodic dipAngle.2
      ∧ 1 / 3 ≤ rateAt g₃ 1 trainF_periodic dipAngle.2
          * ((1 - fineEta n δ) * roundOut n δ)
      ∧ (1 / 3 - rep dipAngle.1) / rateAt g₁ 1 trainF_periodic dipAngle.2 * roundOut n δ
          ≤ (1 / 3 - rep dipAngle.1) / rateAt g₃ 1 trainF_periodic dipAngle.2
            * roundBack n δ := by
  have hπ := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by positivity
  have hcos : Real.cos δ < 1 := by
    have h := Real.cos_le_one_sub_mul_cos_sq (x := δ) (by rw [abs_of_pos hδ0]; linarith)
    have : 0 < 2 / Real.pi ^ 2 * δ ^ 2 := by positivity
    linarith
  have hη1 : 0 < 1 - fineEta n δ := by linarith
  have hRO : 0 < roundOut n δ := by
    unfold roundOut
    exact mul_pos hr (by linarith)
  have hE : 0 < (1 - fineEta n δ) * roundOut n δ := mul_pos hη1 hRO
  have hRL : 0 < roundLower n δ := by
    unfold roundLower
    exact mul_pos hη1 (mul_pos hr (by linarith))
  have hFL : 0 < farLower n δ := by
    unfold farLower
    exact mul_pos hη1 (mul_pos hr (by linarith))
  have h52 := five_halves_roundUpper_le_roundLower n hδ0.le hδ hη
  have h2 := two_farUpper_le_farLower n hδ0.le (by linarith) (by linarith : fineEta n δ ≤ 1 / 48)
  have hLB : roundLower n δ ≤ (1 - fineEta n δ) * roundBack n δ := by
    unfold roundLower roundBack
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hr.le) hη1.le
  have key : ∀ x : ℝ, 2 * (1 / (6 * x)) = 1 / (3 * x) := fun x => by ring
  have e₁ : rateAt g₁ 1 trainF_periodic dipAngle.2 = 1 / (3 * roundLower n δ) := by
    rw [rateAt_trainF_dipAngle, hg₁, key]
  have e₂ : rateAt g₂ 1 trainF_periodic dipAngle.2 = 1 / (3 * farLower n δ) := by
    rw [rateAt_trainF_dipAngle, hg₂, key]
  have e₃ : rateAt g₃ 1 trainF_periodic dipAngle.2
      = 1 / (3 * ((1 - fineEta n δ) * roundOut n δ)) := by
    rw [rateAt_trainF_dipAngle, hg₃, key]
  rw [e₁, e₂, e₃, rep_dipAngle]
  refine ⟨hcos, by positivity, ?_, ?_, by positivity, ?_, ?_, by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_div_eq_mul_div, div_one, div_div_eq_mul_div, div_one]
    have h9 : roundLower n δ * roundOut n δ
        ≤ (1 - fineEta n δ) * roundBack n δ * roundOut n δ :=
      mul_le_mul_of_nonneg_right hLB hRO.le
    nlinarith

/-! ### The instance -/

section Instance

variable {M Mc : ℕ} {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1) (Jc : ℝ) {μ₀ μ₁ : ℝ}
  (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
  (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
  {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ Real.pi / 96) (hη : fineEta n δ ≤ 1 / 96) {g₁ g₂ g₃ : ℝ}
  (hg₁ : g₁ = 1 / (6 * roundLower n δ)) (hg₂ : g₂ = 1 / (6 * farLower n δ))
  (hg₃ : g₃ = 1 / (6 * ((1 - fineEta n δ) * roundOut n δ)))

include h10 hRe hg hδ0 hδ hη hg₁ hg₂ hg₃

/-- ★ **The three records and three counts with no rate hypothesis left.** For the three
strengths of `dipInstance_windows`, the profile `trainF` on all three region pointers and the
three pointers started at `dipAngle`, the conclusion of `three_records_with_counts` (#384)
holds with `T₁ = 0`: three `IsRecordWrite`s in order, the clock's tick counts at the ends of
their write intervals, the two count bounds and the midpoint clause. The remaining hypotheses
are the margin, the packet index, the ring's length and the clock's parameters. -/
theorem dipInstance_three_records :
    ∃ (τd τa τr : ℝ) (Nd Na Nr : ℕ), 0 ≤ τd ∧ τd ≤ roundOut n δ
      ∧ roundAway n δ ≤ τa ∧ τa ≤ roundAwayEnd n δ
      ∧ roundBack n δ ≤ τr ∧ τr ≤ roundEnd n δ ∧ τd ≤ τa ∧ τa ≤ τr
      ∧ IsRecordWrite
          (fun t => triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
              Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
              dipAngle dipAngle t).1)
          0 0 τd (1 / (3 * rateAt g₃ 1 trainF_periodic dipAngle.2)) true
      ∧ IsRecordWrite
          (fun t => echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
              Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
              dipAngle dipAngle t).1.1)
          0 (roundAway n δ) τa (1 / (3 * rateAt g₂ 1 trainF_periodic dipAngle.2)) true
      ∧ IsRecordWrite
          (fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
              Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
              dipAngle dipAngle t).1.1)
          0 (roundBack n δ) τr (1 / (3 * rateAt g₁ 1 trainF_periodic dipAngle.2)) true
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
            Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
            dipAngle dipAngle)
          τd Nd
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
            Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
            dipAngle dipAngle)
          τa Na
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
            Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
            dipAngle dipAngle)
          τr Nr
      ∧ |((Na : ℝ) - Nd) * (2 * Real.pi / R) - (τa - τd)| ≤ 4 * Real.pi / R
      ∧ |((Nr : ℝ) - Nd) * (2 * Real.pi / R) - (τr - τd)| ≤ 4 * Real.pi / R
      ∧ roundAway n δ ≤ (τd + τr) / 2 ∧ (τd + τr) / 2 ≤ roundAwayEnd n δ
      ∧ |((Nd : ℝ) + Nr) / 2 * (2 * Real.pi / R) - (τd + τr) / 2| ≤ 2 * Real.pi / R := by
  have hπ := Real.pi_pos
  obtain ⟨hcos, hκ₁, hlo₁, hhi₁, hκ₂, hlo₂, hhi₂, hκ₃, hhi₃, -⟩ :=
    dipInstance_windows hn hδ0 hδ hη hg₁ hg₂ hg₃
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hRO : 0 ≤ roundOut n δ := by
    unfold roundOut
    exact mul_nonneg (by positivity) (by linarith)
  rw [rep_dipAngle] at hlo₁
  exact three_records_with_counts g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn
    hL Jc h0 h01 h10 m hβ hRe hg contDiff_trainF contDiff_trainF contDiff_trainF
    dipAngle_mem_readyArc dipAngle_mem_readyArc dipAngle_mem_readyArc trainF_lift_zero
    (zero_mem_roundFibres_trainF g₁ g₂ n) hδ0.le (by linarith) hcos hκ₁ (by linarith) hhi₁ hκ₂
    hlo₂ hhi₂ hκ₃ le_rfl hRO (by rw [mul_zero]; norm_num) hhi₃

/-- ★ **The dip certificate with no rate hypothesis left.** For the three strengths of
`dipInstance_windows`, the profile `trainF` on all three region pointers and the three
pointers started at `dipAngle`: every continuous non-negative `F` that reproduces the third
and the first readout histories of the three-record run, and the first pointer's ready arc
at `roundBack n δ`, has a mean over `[roundOut, roundBack]` strictly less than its mean over
`[0, roundOut]` and strictly less than its mean over `[roundBack, roundEnd]`, and is neither
non-decreasing nor non-increasing. The remaining hypotheses are the margin, the packet index
(`fineEta_le_of_le` at `δ = π/96`), the ring's length and the clock's parameters. -/
theorem dipInstance_readouts_certify_dip {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ s, 0 ≤ F s)
    (hFf : ∀ t, 0 ≤ t → t ≤ roundBack n δ →
      (triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL Jc
          h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle dipAngle
          dipAngle t).1 = true
      ↔ pshift (rateAt g₃ 1 trainF_periodic dipAngle.2 * ∫ s in (0 : ℝ)..t, F s) dipAngle
          ∈ displayArc))
    (hFs : ∀ t, 0 ≤ t → t ≤ roundEnd n δ →
      (echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL Jc
          h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle dipAngle
          dipAngle t).1.1 = true
      ↔ pshift (rateAt g₁ 1 trainF_periodic dipAngle.2 * ∫ s in (0 : ℝ)..t, F s) dipAngle
          ∈ displayArc))
    (hFr : (threeRecordRun Mc g₁ g₂ g₃ trainF_periodic trainF_periodic trainF_periodic hn hL
          Jc h0 h01 m hβ g₀ contDiff_trainF contDiff_trainF contDiff_trainF R dipAngle
          dipAngle dipAngle (roundBack n δ)).1.1
        ∈ echoFstReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ pshift (rateAt g₁ 1 trainF_periodic dipAngle.2
          * ∫ s in (0 : ℝ)..roundBack n δ, F s) dipAngle ∈ readyArc 2) :
    roundOut n δ * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in (0 : ℝ)..roundOut n δ, F s
      ∧ (roundEnd n δ - roundBack n δ) * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in roundBack n δ..roundEnd n δ, F s
      ∧ ¬ Monotone F ∧ ¬ Antitone F := by
  have hπ := Real.pi_pos
  obtain ⟨hcos, hκ₁, hlo₁, hhi₁, hκ₂, hlo₂, hhi₂, hκ₃, hhi₃, H⟩ :=
    dipInstance_windows hn hδ0 hδ hη hg₁ hg₂ hg₃
  exact threeRecord_readouts_certify_dip g₁ g₂ g₃ trainF_periodic trainF_periodic
    trainF_periodic hn hL Jc h0 h01 h10 m hβ hRe hg contDiff_trainF contDiff_trainF
    contDiff_trainF dipAngle_mem_readyArc dipAngle_mem_readyArc dipAngle_mem_readyArc
    trainF_lift_zero (zero_mem_roundFibres_trainF g₁ g₂ n) hδ0.le (by linarith) hcos hκ₁ hlo₁
    hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ hhi₃ H hF hF0 hFf hFs hFr

include h0 h01 hβ in
/-- ★ **The run's own near-half occupancy has the dip, with no rate hypothesis left.** For
the strengths of `dipInstance_windows`, the near-half occupancy of the coupled carrier on the
fibre `(0, 0)` satisfies both inequalities of the dip and is neither non-decreasing nor
non-increasing. -/
theorem dipInstance_nearOcc_dip :
    roundOut n δ * ∫ s in roundOut n δ..roundBack n δ,
          nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
        < (roundBack n δ - roundOut n δ) * ∫ s in (0 : ℝ)..roundOut n δ,
          nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
      ∧ (roundEnd n δ - roundBack n δ) * ∫ s in roundOut n δ..roundBack n δ,
          nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
        < (roundBack n δ - roundOut n δ) * ∫ s in roundBack n δ..roundEnd n δ,
          nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
      ∧ ¬ Monotone (nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2)
      ∧ ¬ Antitone
          (nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2) := by
  have hπ := Real.pi_pos
  obtain ⟨hcos, hκ₁, hlo₁, hhi₁, hκ₂, hlo₂, hhi₂, hκ₃, hhi₃, H⟩ :=
    dipInstance_windows hn hδ0 hδ hη hg₁ hg₂ hg₃
  exact threeRecord_nearOcc_dip (Mc := Mc) g₁ g₂ g₃ trainF_periodic trainF_periodic
    trainF_periodic hn hL Jc h0 h01 h10 m hβ hRe hg contDiff_trainF contDiff_trainF
    contDiff_trainF dipAngle_mem_readyArc dipAngle_mem_readyArc dipAngle_mem_readyArc
    trainF_lift_zero (zero_mem_roundFibres_trainF g₁ g₂ n) hδ0.le (by linarith) hcos hκ₁ hlo₁
    hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ hhi₃ H

end Instance

/-- ★ **The dip exists, with no hypothesis left.** There are a ring, a packet index and two
strengths for which the coupled carrier's near-half occupancy on the fibre `(0, 0)` has the
dip at the margin `π/96`. The witness is the packet index `73744`, a ring of
`640000 · 73744³ + 1` sites and the strengths of `dipInstance_windows`. -/
theorem exists_nearOcc_dip :
    ∃ (M n : ℕ) (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1) (g₁ g₂ : ℝ),
      roundOut n (Real.pi / 96) * ∫ s in roundOut n (Real.pi / 96)..roundBack n (Real.pi / 96),
            nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
          < (roundBack n (Real.pi / 96) - roundOut n (Real.pi / 96))
            * ∫ s in (0 : ℝ)..roundOut n (Real.pi / 96),
              nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
        ∧ (roundEnd n (Real.pi / 96) - roundBack n (Real.pi / 96))
            * ∫ s in roundOut n (Real.pi / 96)..roundBack n (Real.pi / 96),
              nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
          < (roundBack n (Real.pi / 96) - roundOut n (Real.pi / 96))
            * ∫ s in roundBack n (Real.pi / 96)..roundEnd n (Real.pi / 96),
              nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2 s
        ∧ ¬ Monotone (nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2)
        ∧ ¬ Antitone (nearOcc g₁ g₂ trainF_periodic trainF_periodic hn hL dipAngle.2 dipAngle.2) := by
  have hn : 0 < 73744 := by norm_num
  have hπ := Real.pi_pos
  exact ⟨640000 * 73744 ^ 3, 73744, hn, Nat.le_succ _, _, _,
    dipInstance_nearOcc_dip (Mc := 0) hn (Nat.le_succ _) (0 : ℝ) (μ₀ := 1) (μ₁ := 3 / 2)
      one_pos (by norm_num) (by norm_num) (0 : ℤ) (β := fun _ => 1) one_ne_zero rfl rfl
      (by positivity) le_rfl (fineEta_le_of_le le_rfl) rfl rfl rfl⟩

end CSD.RecordLayer

end
