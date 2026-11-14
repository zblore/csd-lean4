/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReadoutCertificate

/-!
# Readouts that certify a rise of the occupancy that drives them

**Category:** 7-SigmaLayer (the record layer). BACKLOG #386 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #385.
No new dynamical assumption; one more readout on the arcs of UA-4 (the first region pointer's
ready arc at the flow time `roundBack`), recorded there.

#385 read a drop of the near-half occupancy from two readouts and said nothing about the
return leg. This module reads the rise. It needs one pointer only, read on two arcs: under a
tightened rate window the first pointer of #384's run is still in its ready arc when the
return leg begins, and it displays by the end of that leg.

**The generic statement** (`rise_of_ready_then_display`). A ready pointer is turned by
`κ ∫₀ᵗ F` for one continuous non-negative `F`. If its readout does not display at any flow
time before `T_b`, the pointer is in the ready arc at `T_b`, and the readout displays at some
flow time up to `T_e`, then `∫₀^{T_b} F < ∫_{T_b}^{T_e} F`: `F` accumulates more after `T_b`
than in all the time before it. If `[T_b, T_e]` is no longer than `[T_o, T_b]`, the mean of
`F` over `[T_b, T_e]` is strictly greater than its mean over `[T_o, T_b]`
(`mean_rise_of_integral_lt`), and `F` is not non-increasing (`not_antitone_of_rise`).

**In the run of #384** (`threeRecord_readouts_certify_rise`): with the first pointer's first
window tightened to `κ₁ · roundUpper ≤ 1/6 − a_θ`, every continuous non-negative `F` that
reproduces the first readout history on `[0, roundEnd]`, and the first pointer's ready arc at
`roundBack`, accumulates more over `[roundBack, roundEnd]` than over `[0, roundBack]`, and has
a greater mean over `[roundBack, roundEnd]` than over `[roundOut, roundBack]`. With the drop
of #385 and its rate condition (`threeRecord_readouts_certify_dip`): the mean over
`[roundOut, roundBack]` is strictly less than the mean before it and the mean after it. The
run's own near-half occupancy is one such `F` (`threeRecord_nearOcc_dip`).

* ★ `rise_of_ready_then_display`, `mean_rise_of_integral_lt`, `not_antitone_of_rise`;
* `five_halves_roundUpper_le_roundLower` — room for the tightened window;
* `echoFstReady_regionTwoFlow_iff`, `echoFstReady_threeRecord_iff` — the first pointer's
  ready arc along the flows;
* ★ `threeRecord_readouts_certify_rise`, ★ `threeRecord_readouts_certify_dip`,
  `threeRecord_nearOcc_dip`.

## Exact scope

* **A rise of a mean, not a return.** The conclusions compare accumulated values and means of
  `F` over stated intervals of flow time. They have no direction, path or speed, they do not
  say when the rise happens within `[roundBack, roundEnd]`, and they do not say that what the
  pointer registers on the return leg is what was there before. The dip is a statement about
  three means. It is not a departure and a return, and no radar time is formed from it.
* **One pointer, read on two arcs.** Each single display history still certifies nothing, as
  stated since #365. The rise uses one more premise about the same pointer: that it is in the
  ready arc at the one flow time `T_b`. The threshold writes (`IsRecordWrite`) of the region
  pointers have read only the displayed arc after the start. Tick records have read a ready
  arc at later flow times since #358 (`HasTicks`), but not this pointer's. Reading the first
  region pointer's ready arc at `roundBack` is a further apparatus input on the arcs of UA-4,
  recorded there. "Does not display before `T_b`" is used only to exclude a full turn.
* **The premises are readouts at flow times** (UA-7): a display history over an interval and
  an arc membership at one flow time. No record holds them, and no degree of freedom holds
  the conclusion.
* **The form of the drive is assumed**, as in #385: the pointer is turned by the accumulated
  value of one function at a known rate from a known start angle. The theorems do not
  identify `F` with an occupancy. In the run the coupled carrier's near-half occupancy is one
  such `F` (`threeRecord_nearOcc_dip`); for it the rise also follows from the occupancy
  bounds of #382 for a small margin and a small `fineEta`, by a calculation not stated in
  Lean.
* **No rate condition between pointers for the rise, but a tighter window.** The rise needs
  `κ₁ · roundUpper ≤ 1/6 − a_θ` in place of #384's `κ₁ · roundUpper ≤ 1/6`: the first pointer
  must still be ready when the return leg begins. With `1/3 ≤ κ₁ · roundLower` this asks
  `roundLower / roundUpper ≥ 2/(1 − 6 a_θ)`. `five_halves_roundUpper_le_roundLower` gives the
  ratio `5/2` for `δ ≤ π/96` and `fineEta n δ ≤ 1/96`, which is enough for `a_θ ≤ 1/30` (a
  calculation, not in Lean). The ratio is below `3` for every `n > 0` and `δ > 0`, so the two
  conditions cannot both hold for a start angle `a_θ ≥ 1/18`: on that part of the ready arc
  `(0, 1/6]` the run theorems here are vacuous (a calculation, not in Lean). The comparison
  of means also uses that the return leg is no longer than `[roundOut, roundBack]`, which
  holds in the run for `δ ≥ 0`.
* **The dip needs the rate condition of #385**, a hypothesis that the rate windows of #384 do
  not imply. The tightened window works against it: with equal start angles `a` the corner
  most favourable to the rate condition is `2 · roundUpper ≤ (1 − fineEta)(1 − 6a) · roundBack`,
  which `two_roundUpper_le_roundBack` (#385) does not cover (a calculation, not in Lean).
  That rates and start angles meeting all the conditions exist is not stated in this module.
  `threeRecord_nearOcc_dip` shows the class of functions is not empty when they are met; it
  does not show that they can be met.
* **The run is that of #384**, with its limits: no term couples the messenger and the clock in
  that variant, the third and fourth profiles vanish on their fibres, the start is a product
  ray (null sets by calculations not in Lean), the round fibres of #379. The clock plays no
  part in this module, and the far pointer and the third pointer play none in the rise;
  their hypotheses are carried only because the writes are taken from
  `three_records_with_counts`. The margin is `0 < δ < π/2`.
* **Not instantiated elsewhere.** That the generic statement applies off the null sets is
  expected, not stated in Lean.
* **Earlier.** #385 has the drop, from two pointers. #373 has a transit certificate in
  accumulated occupancies, with no pointer in it. `echoFstReady` is #364's set, used there
  for the start only. Nothing here is evidence about Lorentz kinematics.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-13, UA-17, UO-16, UD-126, UD-130, UD-131, UD-132, UD-133, UD-134);
`RecordLayer/UnifiedReadoutCertificate.lean` (#385: `threeRecord_readouts_certify_drop`,
`lt_of_pshift_mem_displayArc`, `le_of_forall_pshift_notMem_displayArc`);
`RecordLayer/UnifiedThreeRecords.lean` (#384: `three_records_with_counts`,
`threeRecordRun_fst_pointer`, `echoFstShown_threeRecord_iff`);
`RecordLayer/UnifiedRoundTrip.lean` (#382: `integral_nearOcc_le`, `roundUpper`, `roundLower`);
`RecordLayer/UnifiedDepartureArrival.lean` (#367: `regionTwoFlow_apply`);
`RecordLayer/UnifiedTwoSiteRecords.lean` (#364: `echoFstReady`);
`RecordLayer/UnifiedDiracClockTicks.lean` (`pshift_mem_readyArc_iff`);
`RecordLayer/UnifiedTransitCertificate.lean` (#373).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### One pointer, read on two arcs -/

/-- ★ **A pointer still ready at one flow time and displayed by a later one certifies a
rise.** Let a ready pointer be turned by `κ ∫₀ᵗ F` for one continuous non-negative `F`. If its
readout does not display at any flow time before `T_b`, the pointer is still in the ready arc
at `T_b`, and the readout displays at some flow time up to `T_e`, then `F` accumulates strictly
more over `[T_b, T_e]` than over `[0, T_b]`: `∫₀^{T_b} F < ∫_{T_b}^{T_e} F`. The rate `κ` is
positive. The ready arc at `T_b` is a second readout of the same pointer, an apparatus input
(UA-4). -/
theorem rise_of_ready_then_display {F : ℝ → ℝ} (hF : Continuous F) (h0 : ∀ s, 0 ≤ F s)
    {κ : ℝ} (hκ : 0 < κ) {q : KTorus} (hq : q ∈ readyArc 2) {hist : ℝ → Bool}
    {Tb t₁ Te : ℝ}
    (hh : ∀ t, 0 ≤ t → t ≤ Te →
      (hist t = true ↔ pshift (κ * ∫ s in (0 : ℝ)..t, F s) q ∈ displayArc))
    (hTb : 0 ≤ Tb) (hTbe : Tb ≤ Te) (ht₁0 : 0 ≤ t₁) (ht₁ : t₁ ≤ Te)
    (hnot : ∀ t, 0 ≤ t → t < Tb → hist t ≠ true)
    (hready : pshift (κ * ∫ s in (0 : ℝ)..Tb, F s) q ∈ readyArc 2)
    (hshown : hist t₁ = true) :
    (∫ s in (0 : ℝ)..Tb, F s) < ∫ s in Tb..Te, F s := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have hnn : ∀ {a b : ℝ}, a ≤ b → 0 ≤ ∫ s in a..b, F s := fun hab =>
    intervalIntegral.integral_nonneg hab fun u _ => h0 u
  -- no display before `T_b`, so no wrap by then
  have h2 : κ * ∫ s in (0 : ℝ)..Tb, F s ≤ 1 / 3 - rep q.1 :=
    le_of_forall_pshift_notMem_displayArc hq (I := fun t => κ * ∫ s in (0 : ℝ)..t, F s)
      hTb (continuous_const.mul (intervalIntegral.continuous_primitive hi 0)).continuousOn
      (by simp) (fun t ht0 htT hd => hnot t ht0 htT ((hh t ht0 (htT.le.trans hTbe)).2 hd))
  have hb0 := mul_nonneg hκ.le (hnn hTb)
  have h3 : rep q.1 + κ * ∫ s in (0 : ℝ)..Tb, F s ≤ 1 / 6 :=
    (pshift_mem_readyArc_iff (by linarith [hr.1]) (by linarith)).1 hready
  have h1 := lt_of_pshift_mem_displayArc hq (mul_nonneg hκ.le (hnn ht₁0))
    ((hh t₁ ht₁0 ht₁).1 hshown)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ Te)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 Tb) (hi Tb Te)
  have h4 := mul_nonneg hκ.le (hnn ht₁)
  have h5 : κ * (∫ s in (0 : ℝ)..Tb, F s) < κ * ∫ s in Tb..Te, F s := by
    have a1 : κ * (∫ s in (0 : ℝ)..Te, F s)
        = κ * (∫ s in (0 : ℝ)..Tb, F s) + κ * ∫ s in Tb..Te, F s := by
      rw [← e2]
      ring
    have a2 : κ * (∫ s in (0 : ℝ)..Te, F s)
        = κ * (∫ s in (0 : ℝ)..t₁, F s) + κ * ∫ s in t₁..Te, F s := by
      rw [← e1]
      ring
    linarith [hr.1]
  exact lt_of_mul_lt_mul_left h5 hκ.le

/-- **From accumulated values to means.** If `F ≥ 0` accumulates more over `[T_b, T_e]` than
over `[0, T_b]`, and `[T_b, T_e]` is no longer than `[T_o, T_b]`, then the mean of `F` over
`[T_b, T_e]` is strictly greater than its mean over `[T_o, T_b]`:
`(T_e − T_b) ∫_{T_o}^{T_b} F < (T_b − T_o) ∫_{T_b}^{T_e} F`. -/
theorem mean_rise_of_integral_lt {F : ℝ → ℝ} (hF : Continuous F) (h0 : ∀ s, 0 ≤ F s)
    {To Tb Te : ℝ} (hTo : 0 ≤ To) (hTob : To < Tb) (hlen : Te - Tb ≤ Tb - To)
    (h : (∫ s in (0 : ℝ)..Tb, F s) < ∫ s in Tb..Te, F s) :
    (Te - Tb) * ∫ s in To..Tb, F s < (Tb - To) * ∫ s in Tb..Te, F s := by
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have hnn : ∀ {a b : ℝ}, a ≤ b → 0 ≤ ∫ s in a..b, F s := fun hab =>
    intervalIntegral.integral_nonneg hab fun u _ => h0 u
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 To) (hi To Tb)
  have hA0 := hnn hTob.le
  have h00 := hnn hTo
  have hA : (∫ s in To..Tb, F s) < ∫ s in Tb..Te, F s := by linarith
  have h1 := mul_le_mul_of_nonneg_right hlen hA0
  have h2 := mul_lt_mul_of_pos_left hA (sub_pos.2 hTob)
  linarith

/-- **A function whose mean rises is not non-increasing**; in particular it is not constant. -/
theorem not_antitone_of_rise {F : ℝ → ℝ} (hF : Continuous F) {To Tb Te : ℝ} (hTob : To ≤ Tb)
    (hTbe : Tb ≤ Te)
    (h : (Te - Tb) * ∫ s in To..Tb, F s < (Tb - To) * ∫ s in Tb..Te, F s) : ¬ Antitone F := by
  intro hm
  have a := le_integral_of_forall_le hF hTob (c := F Tb) fun s hs => hm hs.2
  have b := integral_le_of_forall_le hF hTbe (c := F Tb) fun s hs => hm hs.1
  have a' := mul_le_mul_of_nonneg_left a (sub_nonneg.2 hTbe)
  have b' := mul_le_mul_of_nonneg_left b (sub_nonneg.2 hTob)
  nlinarith

/-- The rate window of the near-half pointer leaves room for a positive start angle: for a
small margin and a small `fineEta`, `roundLower` is at least `5/2` of `roundUpper`. For
`n > 0` a rate `κ` with `κ · roundUpper ≤ 1/6 − a` and `1/3 ≤ κ · roundLower` then exists for
every start angle `a ≤ 1/30` (a calculation, not stated here; at `n = 0` both bounds are
zero and no rate exists). -/
theorem five_halves_roundUpper_le_roundLower (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 96) (hη : fineEta n δ ≤ 1 / 96) :
    5 / 2 * roundUpper n δ ≤ roundLower n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 := by positivity
  unfold roundUpper roundLower
  have h1 : fineEta n δ * (Real.pi - 2 * δ) ≤ 1 / 96 * Real.pi := by
    have := mul_le_mul hη (by linarith : Real.pi - 2 * δ ≤ Real.pi) (by linarith) (by norm_num)
    linarith
  have h2 : (95 / 96 : ℝ) * (3 * Real.pi / 2 - Real.pi / 32)
      ≤ (1 - fineEta n δ) * (3 * Real.pi / 2 - 3 * δ) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 5 / 2 * (Real.pi / 2 + 3 * δ + fineEta n δ * (Real.pi - 2 * δ))
      ≤ (1 - fineEta n δ) * (3 * Real.pi / 2 - 3 * δ) := by
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hr2
  nlinarith

/-! ### The first pointer's ready arc along the flows -/

section Ready

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The first pointer's ready arc along `regionTwoFlow` (#367), in terms of the accumulated
weight on the first region. -/
theorem echoFstReady_regionTwoFlow_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) (t : ℝ) :
    regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t ((idxArenaEquiv (diracIdx M) p, θ), ψ)
        ∈ echoFstReady (2 * M + 1)
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p)) θ ∈ readyArc 2 := by
  have e : idxTwoShiftFst (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
        (regionProj_smul_isHermitian g₂ B) hf hh θ.2 ψ.2 p t
      = rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p) :=
    (idxTwoShiftFst_ofReal_smul g₁ (diracHam_isHermitian J μ) (regionProj_isHermitian A)
      (regionProj_smul_isHermitian g₂ B) hf hh θ.2 ψ.2 p t).trans (by rw [rateAt, div_one])
  rw [regionTwoFlow_apply, ← e]
  rfl

end Ready

section RunReady

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ g₃ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) {n : ℕ} (hn : 0 < n)
  (hL : 640000 * n ^ 3 ≤ M + 1) (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
  (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}

/-- **The first pointer's ready arc along the three-record run** (#384), in terms of the
accumulated near-half occupancy. -/
theorem echoFstReady_threeRecord_iff (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).1.1
        ∈ echoFstReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ pshift (rateAt g₁ 1 hf θ.2
          * ∫ s in (0 : ℝ)..t, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) θ ∈ readyArc 2 := by
  have hp := threeRecordRun_fst_pointer (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01
    m hβ g₀ hc hch hck θ ψ hzk t
  have hiff := echoFstReady_regionTwoFlow_iff (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) hf hh hc hch
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) θ ψ t
  have hmem : (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
        t).1.1 ∈ echoFstReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)
        ∈ echoFstReady (2 * M + 1) := by
    show (_ : KTorus) ∈ readyArc 2 ↔ (_ : KTorus) ∈ readyArc 2
    rw [hp]
  rw [hmem]
  exact hiff

end RunReady

/-! ### The certificates in the three-record run -/

section Run

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ g₃ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) {n : ℕ} (hn : 0 < n)
  (hL : 640000 * n ^ 3 ≤ M + 1) (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
  (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
  (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **The near-half pointer of the three-record run, read on two arcs, certifies a rise.**
In the run of #384, under its hypotheses with `T₁ = 0`, `0 < δ < π/2` (in Lean `0 ≤ δ`,
`δ < π/2`, `cos δ < 1`) and the first pointer's first window tightened to
`κ₁ · roundUpper n δ ≤ 1/6 − a_θ`: every continuous non-negative `F` such that the first
readout displays exactly where `pshift (κ₁ ∫₀ᵗ F) θ` is in the displayed arc, and the first
pointer is in the ready arc at `roundBack n δ` exactly if `pshift (κ₁ ∫₀^{roundBack} F) θ` is,
satisfies

* `∫₀^{roundBack} F < ∫_{roundBack}^{roundEnd} F`;
* `(roundEnd − roundBack) ∫_{roundOut}^{roundBack} F
    < (roundBack − roundOut) ∫_{roundBack}^{roundEnd} F`;
* `F` is not non-increasing.

The times are flow times (UA-7). A rise of a mean, not a return. The ready arc at
`roundBack n δ` is a second readout of the first pointer, an apparatus input (UA-4). The
hypotheses on the far pointer, the third pointer and the clock are carried only to take the
write from `three_records_with_counts`. That the hypotheses hold together for some start is
not stated here. -/
theorem threeRecord_readouts_certify_rise (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2)
    (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6 - rep θ.1)
    (hhi₁ : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ)
    (hκ₂ : 0 < rateAt g₂ 1 hh ψ.2) (hlo₂ : rateAt g₂ 1 hh ψ.2 * farUpper n δ ≤ 1 / 6)
    (hhi₂ : 1 / 3 ≤ rateAt g₂ 1 hh ψ.2 * farLower n δ)
    (hκ₃ : 0 < rateAt g₃ 1 hk χ.2)
    (hhi₃ : 1 / 3 ≤ rateAt g₃ 1 hk χ.2 * ((1 - fineEta n δ) * roundOut n δ))
    {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ s, 0 ≤ F s)
    (hFs : ∀ t, 0 ≤ t → t ≤ roundEnd n δ →
      (echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1.1 = true
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, F s) θ ∈ displayArc))
    (hFr : (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          (roundBack n δ)).1.1 ∈ echoFstReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..roundBack n δ, F s) θ ∈ readyArc 2) :
    (∫ s in (0 : ℝ)..roundBack n δ, F s) < ∫ s in roundBack n δ..roundEnd n δ, F s
      ∧ (roundEnd n δ - roundBack n δ) * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in roundBack n δ..roundEnd n δ, F s
      ∧ ¬ Antitone F := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hr : rep θ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  have hTo : 0 < roundOut n δ := by
    unfold roundOut
    exact mul_pos hr2 (by linarith)
  have hTob : roundOut n δ < roundBack n δ := by
    unfold roundOut roundBack
    exact mul_lt_mul_of_pos_left (by linarith) hr2
  have hTbe : roundBack n δ ≤ roundEnd n δ := by
    unfold roundBack roundEnd
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hlen : roundEnd n δ - roundBack n δ ≤ roundBack n δ - roundOut n δ := by
    unfold roundEnd roundBack roundOut
    nlinarith [mul_nonneg hr2.le hδ0]
  have hTb0 : 0 ≤ roundBack n δ := hTo.le.trans hTob.le
  obtain ⟨τd, τa, τr, Nd, Na, Nr, -, -, -, -, hr1, hr2', -, -, -, -, hwr, -⟩ :=
    three_records_with_counts g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hck hθ
      hψ hχ hzk hx hδ0 hδ.le hcos hκ₁ (by linarith [hr.1]) hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ le_rfl
      hTo.le (by rw [mul_zero]; norm_num) hhi₃
  -- the run's first pointer is still ready at the start of the return leg
  have hup := integral_nearOcc_le g₁ g₂ hf hh hn hL hx hδ0 hδ.le hcos
  have hlow : 0 ≤ ∫ s in (0 : ℝ)..roundBack n δ, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s :=
    intervalIntegral.integral_nonneg hTb0 fun u _ => nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 u
  have hx1 := mul_le_mul_of_nonneg_left hup hκ₁.le
  have hx0 := mul_nonneg hκ₁.le hlow
  have hrun := (echoFstReady_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0
    h01 m hβ g₀ hc hch hck θ ψ hzk (roundBack n δ)).2
    ((pshift_mem_readyArc_iff (by linarith [hr.1]) (by linarith)).2 (by linarith))
  have hrise := rise_of_ready_then_display hF hF0 hκ₁ hθ hFs hTb0 hTbe (hTb0.trans hr1) hr2'
    (fun t ht0 ht => hwr.before t ht0 ht) (hFr.1 hrun)
    (hwr.holds τr le_rfl (le_add_of_nonneg_right hwr.window_nonneg))
  have hmean := mean_rise_of_integral_lt hF hF0 hTo.le hTob hlen hrise
  exact ⟨hrise, hmean, not_antitone_of_rise hF hTob.le hTbe hmean⟩

/-- ★ **The readouts of the three-record run certify a dip.** Under the hypotheses of
`threeRecord_readouts_certify_drop` (#385) and of `threeRecord_readouts_certify_rise`
together: every continuous non-negative `F` that reproduces the third and the first readout
histories, and the first pointer's ready arc at `roundBack n δ`, has a mean over
`[roundOut, roundBack]` strictly less than its mean over `[0, roundOut]` and strictly less
than its mean over `[roundBack, roundEnd]`. It is neither non-decreasing nor non-increasing.
The times are flow times (UA-7). A dip of a mean, not a departure and a return. The ready
arc at `roundBack n δ` is an apparatus input (UA-4). That the hypotheses hold together for
some start is not stated here. -/
theorem threeRecord_readouts_certify_dip (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2)
    (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6 - rep θ.1)
    (hhi₁ : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ)
    (hκ₂ : 0 < rateAt g₂ 1 hh ψ.2) (hlo₂ : rateAt g₂ 1 hh ψ.2 * farUpper n δ ≤ 1 / 6)
    (hhi₂ : 1 / 3 ≤ rateAt g₂ 1 hh ψ.2 * farLower n δ)
    (hκ₃ : 0 < rateAt g₃ 1 hk χ.2)
    (hhi₃ : 1 / 3 ≤ rateAt g₃ 1 hk χ.2 * ((1 - fineEta n δ) * roundOut n δ))
    (H : (1 / 3 - rep θ.1) / rateAt g₁ 1 hf θ.2 * roundOut n δ
      ≤ (1 / 3 - rep χ.1) / rateAt g₃ 1 hk χ.2 * roundBack n δ)
    {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ s, 0 ≤ F s)
    (hFf : ∀ t, 0 ≤ t → t ≤ roundBack n δ →
      (triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1 = true
      ↔ pshift (rateAt g₃ 1 hk χ.2 * ∫ s in (0 : ℝ)..t, F s) χ ∈ displayArc))
    (hFs : ∀ t, 0 ≤ t → t ≤ roundEnd n δ →
      (echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1.1 = true
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, F s) θ ∈ displayArc))
    (hFr : (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          (roundBack n δ)).1.1 ∈ echoFstReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..roundBack n δ, F s) θ ∈ readyArc 2) :
    roundOut n δ * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in (0 : ℝ)..roundOut n δ, F s
      ∧ (roundEnd n δ - roundBack n δ) * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in roundBack n δ..roundEnd n δ, F s
      ∧ ¬ Monotone F ∧ ¬ Antitone F := by
  have hr : rep θ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  have hTbe : roundBack n δ ≤ roundEnd n δ := by
    have hπ := Real.pi_pos
    unfold roundBack roundEnd
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨hdrop, hmono⟩ := threeRecord_readouts_certify_drop g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01
    h10 m hβ hRe hg hc hch hck hθ hψ hχ hzk hx hδ0 hδ hcos hκ₁ (by linarith [hr.1]) hhi₁ hκ₂
    hlo₂ hhi₂ hκ₃ hhi₃ H hF hF0 hFf (fun t a b => hFs t a (b.trans hTbe))
  obtain ⟨-, hrise, hanti⟩ := threeRecord_readouts_certify_rise g₁ g₂ g₃ hf hh hk hn hL Jc h0
    h01 h10 m hβ hRe hg hc hch hck hθ hψ hχ hzk hx hδ0 hδ hcos hκ₁ hlo₁ hhi₁ hκ₂ hlo₂ hhi₂ hκ₃
    hhi₃ hF hF0 hFs hFr
  exact ⟨hdrop, hrise, hmono, hanti⟩

include h0 h01 hβ in
/-- **The run's own near-half occupancy is one such function.** Under the same hypotheses the
coupled carrier's near-half occupancy `nearOcc` on the fibre `(θ₂, ψ₂)` satisfies both
inequalities of the dip and is neither non-decreasing nor non-increasing. So the class of
functions in `threeRecord_readouts_certify_dip` is not empty. -/
theorem threeRecord_nearOcc_dip (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2)
    (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6 - rep θ.1)
    (hhi₁ : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ)
    (hκ₂ : 0 < rateAt g₂ 1 hh ψ.2) (hlo₂ : rateAt g₂ 1 hh ψ.2 * farUpper n δ ≤ 1 / 6)
    (hhi₂ : 1 / 3 ≤ rateAt g₂ 1 hh ψ.2 * farLower n δ)
    (hκ₃ : 0 < rateAt g₃ 1 hk χ.2)
    (hhi₃ : 1 / 3 ≤ rateAt g₃ 1 hk χ.2 * ((1 - fineEta n δ) * roundOut n δ))
    (H : (1 / 3 - rep θ.1) / rateAt g₁ 1 hf θ.2 * roundOut n δ
      ≤ (1 / 3 - rep χ.1) / rateAt g₃ 1 hk χ.2 * roundBack n δ) :
    roundOut n δ * ∫ s in roundOut n δ..roundBack n δ, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s
        < (roundBack n δ - roundOut n δ)
          * ∫ s in (0 : ℝ)..roundOut n δ, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s
      ∧ (roundEnd n δ - roundBack n δ)
          * ∫ s in roundOut n δ..roundBack n δ, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s
        < (roundBack n δ - roundOut n δ)
          * ∫ s in roundBack n δ..roundEnd n δ, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s
      ∧ ¬ Monotone (nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
      ∧ ¬ Antitone (nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2) :=
  threeRecord_readouts_certify_dip g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 h10 m hβ hRe hg hc hch
    hck hθ hψ hχ hzk hx hδ0 hδ hcos hκ₁ hlo₁ hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ hhi₃ H
    (continuous_nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2) (nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun t _ _ => triThdShown_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc
      h0 h01 m hβ g₀ hc hch hck θ ψ hzk t)
    (fun t _ _ => echoFstShown_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc
      h0 h01 m hβ g₀ hc hch hck θ ψ hzk t)
    (echoFstReady_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ
      g₀ hc hch hck θ ψ hzk (roundBack n δ))

end Run

end CSD.RecordLayer

end
