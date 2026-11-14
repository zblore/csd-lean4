/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedThreeRecords

/-!
# Two readouts that certify a drop of the occupancy that drives them

**Category:** 7-SigmaLayer (the record layer). BACKLOG #385 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; part of Remainder (b) of #384.
No new assumption.

Every write since #365 is a threshold of accumulated occupancy, and each scope has said that a
carrier whose occupancy is a suitable constant would give a readout with the same clauses. That
is true of one readout. This module shows it is not true of two readouts taken together, when the
two pointers are driven by the same function at known rates from known start angles and those
rates and angles satisfy a rate condition. Where the condition fails the caveat stands (a
calculation, not in Lean).

**The generic statement** (`drop_of_two_readouts`). Two ready pointers are turned by
`κ_f ∫₀ᵗ F` and `κ_s ∫₀ᵗ F` for one continuous non-negative `F`. If the fast readout displays
at some flow time up to `T_o`, the slow readout does not display at any flow time before
`T_b`, and `(1/3 − a_s)/κ_s · T_o ≤ (1/3 − a_f)/κ_f · T_b`, then
`T_o ∫_{T_o}^{T_b} F < (T_b − T_o) ∫₀^{T_o} F`: the mean of `F` over `[T_o, T_b]` is strictly
less than its mean over `[0, T_o]`. So `F` is not non-decreasing, and in particular not
constant (`not_monotone_of_drop`).

**In the run of #384** (`threeRecord_readouts_certify_drop`): under the rate condition, every
continuous non-negative `F` that reproduces the third and the first readout histories of that run
at the flow times in `[0, roundBack]`, through pointers of those rates and start angles, has a
smaller mean over `[roundOut, roundBack]` than over `[0, roundOut]`. The run's own near-half
occupancy is one such `F` (`threeRecord_nearOcc_drop`).

* `lt_of_pshift_mem_displayArc`, `le_of_forall_pshift_notMem_displayArc` — what a display, and
  the absence of one, say about the displacement behind a ready pointer;
* ★ `drop_of_two_readouts`, `not_monotone_of_drop`;
* `two_roundUpper_le_roundBack` — the rate condition at its most favourable corner, a
  corollary of `two_roundUpper_le_roundLower` (#382);
* ★ `threeRecord_readouts_certify_drop`, `threeRecord_nearOcc_drop`.

## Exact scope

* **A drop of a mean, not a departure.** The conclusion compares two means of `F`. It has no
  direction, path or speed, and it does not say when the drop happens within `[0, T_b]`. It
  says nothing about a return: no statement here shows the mean rising again.
* **The premises are readout histories over intervals of flow time** (UA-7). "The slow
  readout does not display at any flow time before `T_b`" is a statement about every flow
  time of an interval. No record holds it, and no degree of freedom holds the conclusion.
* **The form of the drive is assumed.** Both pointers are turned by the accumulated value of one
  function, at known rates, from known start angles in the ready arc, read on the arcs of UA-4.
  The theorem does not identify `F` with an occupancy. In the run, the coupled carrier's
  near-half occupancy is one such `F` (`threeRecord_nearOcc_drop`). For it the drop also follows
  from the occupancy bounds of #382 and #384 (built on #379) without the rate condition, for a
  small margin and a small `fineEta`, by a calculation not stated in Lean. What is new is that
  the drop follows from the two readout histories, the rates, the start angles and the rate
  condition, for every continuous non-negative `F` that reproduces both histories on
  `[0, T_b]`. In particular no constant `F` reproduces them.
* **Two readouts, taken together.** Each single write still certifies nothing, as stated since
  #365. The certificate needs two pointers on the same region with different thresholds
  `(1/3 − a)/κ`.
* **The rate condition is a hypothesis**, and the rate windows of #384 do not imply it: it bounds
  the third rate from above, and with `T₁ = 0` those windows bound it only from below. With equal
  start angles, the third rate at the least value its window allows and the first rate at the
  greatest (the corner most favourable to the condition; elsewhere it is stronger, and it fails
  for a large third rate), it reads `2 · roundUpper ≤ (1 − fineEta) · roundBack`. That is weaker
  than the compatibility `2 · roundUpper ≤ roundLower` of the first pointer's window (#382), and
  `two_roundUpper_le_roundBack` has it for `δ ≤ π/48` and `fineEta n δ ≤ 1/48` as a corollary of
  that. That rates and start angles meeting all the conditions exist is otherwise not stated in
  Lean.
* **The run is that of #384**, with its limits: no term couples the messenger and the clock in
  that variant, the third and fourth profiles vanish on their fibres, the start is a product
  ray (null sets by calculations not in Lean), the round fibres of #379. The clock plays no
  part in this module; its hypotheses are carried only because the writes are taken from
  `three_records_with_counts`. The margin is `0 < δ < π/2`.
* **Not instantiated elsewhere.** On every fibre a pointer of the present coupling form is
  turned by its rate times an accumulated expectation along the orbit, so the generic
  statement is expected to apply off the null sets too. That is not stated in Lean.
* **Earlier.** #373 has a transit certificate in accumulated occupancies, with no pointer in
  it. #365, #367, #382, #383 and #384 have threshold writes that certify nothing singly.
  Nothing here is evidence about Lorentz kinematics.
* **Later.** #386 (`RecordLayer/UnifiedReadoutRise.lean`): the first pointer, read on its
  ready arc at the start of the return leg and on its displayed arc after, certifies a rise;
  with the drop here, a dip of the mean.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-13, UA-17, UO-16, UD-89, UD-105, UD-118, UD-126, UD-129, UD-130, UD-131,
UD-132); `RecordLayer/UnifiedThreeRecords.lean` (#384: `three_records_with_counts`,
`threeRecordRun`); `RecordLayer/UnifiedRoundTrip.lean` (#382: `roundUpper`,
`integral_le_of_forall_le`, `le_integral_of_forall_le`); `RecordLayer/UnifiedGateReturn.lean`
(#380: `roundOut`, `roundBack`); `RecordLayer/UnifiedDiracClockTicks.lean`
(`pshift_mem_displayArc_iff`); `RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`);
`RecordLayer/UnifiedTransitCertificate.lean` (#373).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### What a readout says about the displacement behind it -/

/-- **A ready pointer that displays after a non-negative turn has turned past the edge of the
displayed arc**: the turn exceeds `1/3` minus the start angle. -/
theorem lt_of_pshift_mem_displayArc {q : KTorus} (hq : q ∈ readyArc 2) {x : ℝ} (hx : 0 ≤ x)
    (h : pshift x q ∈ displayArc) : 1 / 3 - rep q.1 < x := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  by_contra hc
  push Not at hc
  have := (pshift_mem_displayArc_iff (q := q) (a := x) (by linarith [hr.1]) (by linarith)).1 h
  linarith

/-- **A ready pointer that never displays up to a flow time has not turned past the edge of
the displayed arc by then**, when its displacement is continuous and starts at zero. -/
theorem le_of_forall_pshift_notMem_displayArc {q : KTorus} (hq : q ∈ readyArc 2) {I : ℝ → ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hI : ContinuousOn I (Icc 0 T)) (hI0 : I 0 = 0)
    (h : ∀ t, 0 ≤ t → t < T → pshift (I t) q ∉ displayArc) : I T ≤ 1 / 3 - rep q.1 := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  by_contra hc
  push Not at hc
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ((I T - (1 / 3 - rep q.1)) / 2) (1 / 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ (I T - (1 / 3 - rep q.1)) / 2 := hε ▸ min_le_left _ _
  have hε2 : ε ≤ 1 / 2 := hε ▸ min_le_right _ _
  obtain ⟨t, ht, hIt⟩ := intermediate_value_Icc hT hI
    (show 1 / 3 - rep q.1 + ε ∈ Icc (I 0) (I T) from
      ⟨by rw [hI0]; linarith [hr.2], by linarith⟩)
  have htT : t < T := by
    rcases ht.2.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [h'] at hIt
      linarith
  refine h t ht.1 htT ?_
  rw [hIt]
  exact (pshift_mem_displayArc_iff (by linarith [hr.1]) (by linarith)).2 (by linarith)

/-! ### Two pointers driven by one occupancy -/

/-- ★ **Two readouts certify a drop.** Let two ready pointers be turned by one continuous
non-negative function `F`, the fast one by `κ_f ∫₀ᵗ F` and the slow one by `κ_s ∫₀ᵗ F`. If the
fast readout displays at some flow time up to `T_o`, the slow readout does not display at any
flow time before `T_b ≥ T_o`, and the rates and start angles satisfy
`(1/3 − a_s)/κ_s · T_o ≤ (1/3 − a_f)/κ_f · T_b`, then the mean of `F` over `[T_o, T_b]` is
strictly less than its mean over `[0, T_o]`:
`T_o ∫_{T_o}^{T_b} F < (T_b − T_o) ∫₀^{T_o} F`. The histories are asked to match the pointers
only at the flow times in `[0, T_b]`. -/
theorem drop_of_two_readouts {F : ℝ → ℝ} (hF : Continuous F) (h0 : ∀ s, 0 ≤ F s)
    {κf κs : ℝ} (hκf : 0 < κf) (hκs : 0 < κs) {qf qs : KTorus} (hqf : qf ∈ readyArc 2)
    (hqs : qs ∈ readyArc 2) {histf hists : ℝ → Bool} {t₀ To Tb : ℝ}
    (hhf : ∀ t, 0 ≤ t → t ≤ Tb →
      (histf t = true ↔ pshift (κf * ∫ s in (0 : ℝ)..t, F s) qf ∈ displayArc))
    (hhs : ∀ t, 0 ≤ t → t ≤ Tb →
      (hists t = true ↔ pshift (κs * ∫ s in (0 : ℝ)..t, F s) qs ∈ displayArc))
    (ht₀ : 0 ≤ t₀) (ht₀o : t₀ ≤ To) (hTo : 0 < To) (hTob : To ≤ Tb)
    (hshown : histf t₀ = true) (hnot : ∀ t, 0 ≤ t → t < Tb → hists t ≠ true)
    (H : (1 / 3 - rep qs.1) / κs * To ≤ (1 / 3 - rep qf.1) / κf * Tb) :
    To * ∫ s in To..Tb, F s < (Tb - To) * ∫ s in (0 : ℝ)..To, F s := by
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have hnn : ∀ {a b : ℝ}, a ≤ b → 0 ≤ ∫ s in a..b, F s := fun hab =>
    intervalIntegral.integral_nonneg hab fun u _ => h0 u
  have hTb : 0 < Tb := hTo.trans_le hTob
  -- the fast pointer
  have h1 := lt_of_pshift_mem_displayArc hqf (mul_nonneg hκf.le (hnn ht₀))
    ((hhf t₀ ht₀ (ht₀o.trans hTob)).1 hshown)
  have h1' : (1 / 3 - rep qf.1) / κf < ∫ s in (0 : ℝ)..To, F s := by
    have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 t₀) (hi t₀ To)
    have h3 := mul_nonneg hκf.le (hnn ht₀o)
    rw [div_lt_iff₀ hκf, ← e]
    nlinarith
  -- the slow pointer
  have h2 : κs * ∫ s in (0 : ℝ)..Tb, F s ≤ 1 / 3 - rep qs.1 :=
    le_of_forall_pshift_notMem_displayArc hqs (I := fun t => κs * ∫ s in (0 : ℝ)..t, F s)
      hTb.le (continuous_const.mul (intervalIntegral.continuous_primitive hi 0)).continuousOn
      (by simp) (fun t ht0 htT hd => hnot t ht0 htT ((hhs t ht0 htT.le).2 hd))
  have h2' : (∫ s in (0 : ℝ)..Tb, F s) ≤ (1 / 3 - rep qs.1) / κs := by
    rw [le_div_iff₀ hκs]
    linarith
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 To) (hi To Tb)
  rw [← e] at h2'
  have h4 := mul_le_mul_of_nonneg_left h2' hTo.le
  have h5 := mul_lt_mul_of_pos_right h1' hTb
  nlinarith

/-- **A function whose mean drops is not non-decreasing**; in particular it is not constant. -/
theorem not_monotone_of_drop {F : ℝ → ℝ} (hF : Continuous F) {To Tb : ℝ} (hTo : 0 ≤ To)
    (hTob : To ≤ Tb)
    (h : To * ∫ s in To..Tb, F s < (Tb - To) * ∫ s in (0 : ℝ)..To, F s) : ¬ Monotone F := by
  intro hm
  have a := integral_le_of_forall_le hF hTo (c := F To) fun s hs => hm hs.2
  have b := le_integral_of_forall_le hF hTob (c := F To) fun s hs => hm hs.1
  have a' := mul_le_mul_of_nonneg_left a (sub_nonneg.2 hTob)
  have b' := mul_le_mul_of_nonneg_left b hTo
  nlinarith

/-- The rate condition of the certificate at its most favourable corner of the rate windows of
#384: for a small margin and a small `fineEta`, twice `roundUpper` is at most the fraction
`1 − fineEta` of the flow time at which the return leg begins. A corollary of
`two_roundUpper_le_roundLower` (#382). -/
theorem two_roundUpper_le_roundBack (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 48)
    (hη : fineEta n δ ≤ 1 / 48) :
    2 * roundUpper n δ ≤ (1 - fineEta n δ) * roundBack n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) ≤ 1250 * (n : ℝ) ^ 2 := by positivity
  refine (two_roundUpper_le_roundLower n hδ0 hδ hη).trans ?_
  unfold roundLower roundBack
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hr2) (by linarith)

/-! ### The certificate in the three-record run -/

section Run

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ g₃ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) {n : ℕ} (hn : 0 < n)
  (hL : 640000 * n ^ 3 ≤ M + 1) (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
  (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
  (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- ★ **The two near-half readouts of the three-record run certify a drop.** In the run of #384,
under its hypotheses with `T₁ = 0` and `0 < δ < π/2` (in Lean `0 ≤ δ`, `δ < π/2`, `cos δ < 1`),
and with the rate condition `(1/3 − a_θ)/κ₁ · roundOut n δ ≤ (1/3 − a_χ)/κ₃ · roundBack n δ`:
every continuous non-negative `F` such that the third readout displays exactly where `pshift (κ₃
∫₀ᵗ F) χ` is in the displayed arc and the first readout exactly where `pshift (κ₁ ∫₀ᵗ F) θ` is,
at the flow times in `[0, roundBack n δ]`, satisfies
`roundOut ∫_{roundOut}^{roundBack} F < (roundBack − roundOut) ∫₀^{roundOut} F`, and is
not non-decreasing. The times are flow times (UA-7). A drop of a mean, not a departure; nothing
is said about a return. -/
theorem threeRecord_readouts_certify_drop (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2) (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6)
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
    (hFs : ∀ t, 0 ≤ t → t ≤ roundBack n δ →
      (echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1.1 = true
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, F s) θ ∈ displayArc)) :
    roundOut n δ * ∫ s in roundOut n δ..roundBack n δ, F s
        < (roundBack n δ - roundOut n δ) * ∫ s in (0 : ℝ)..roundOut n δ, F s
      ∧ ¬ Monotone F := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hTo : 0 < roundOut n δ := by
    unfold roundOut
    exact mul_pos hr2 (by linarith)
  have hTob : roundOut n δ ≤ roundBack n δ := by
    unfold roundOut roundBack
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  obtain ⟨τd, τa, τr, Nd, Na, Nr, hd1, hd2, -, -, -, -, -, -, hwd, -, hwr, -⟩ :=
    three_records_with_counts g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 h10 m hβ hRe hg hc hch hck hθ
      hψ hχ hzk hx hδ0 hδ.le hcos hκ₁ hlo₁ hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ le_rfl hTo.le
      (by rw [mul_zero]; norm_num) hhi₃
  have hdrop := drop_of_two_readouts hF hF0 hκ₃ hκ₁ hχ hθ hFf hFs hd1 hd2 hTo hTob
    (hwd.holds τd le_rfl (le_add_of_nonneg_right hwd.window_nonneg))
    (fun t ht0 ht => hwr.before t ht0 ht) H
  exact ⟨hdrop, not_monotone_of_drop hF hTo.le hTob hdrop⟩

include h0 h01 hβ in
/-- **The run's own near-half occupancy is one such function.** Under the same hypotheses the
coupled carrier's near-half occupancy `nearOcc` on the fibre `(θ₂, ψ₂)` satisfies the drop
inequality and is not non-decreasing. So the class of functions in
`threeRecord_readouts_certify_drop` is not empty. -/
theorem threeRecord_nearOcc_drop (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2) (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6)
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
      ∧ ¬ Monotone (nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2) :=
  threeRecord_readouts_certify_drop g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 h10 m hβ hRe hg hc hch
    hck hθ hψ hχ hzk hx hδ0 hδ hcos hκ₁ hlo₁ hhi₁ hκ₂ hlo₂ hhi₂ hκ₃ hhi₃ H
    (continuous_nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2) (nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun t _ _ => triThdShown_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc
      h0 h01 m hβ g₀ hc hch hck θ ψ hzk t)
    (fun t _ _ => echoFstShown_threeRecord_iff (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc
      h0 h01 m hβ g₀ hc hch hck θ ψ hzk t)

end Run

end CSD.RecordLayer

end
