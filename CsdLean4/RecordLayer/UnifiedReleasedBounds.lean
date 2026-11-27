/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedRecord

/-!
# Sharper bounds for the released return: what an instance needs

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (γ5)
of the task plans, first part).

The bounds of UD-274, UD-276 and UD-277 use the clock's crude upper bound `κ(u) ≤ c u` and the
detector's crude upper bound `ρ t`. With those, the three threshold inequalities of UD-277
ask the return carrier to dwell on the detector for more than half of the whole run, counted
from the flow time `0`; no carrier in the corpus does (see the scope). Here the same
quantities are bounded with the stage in which nothing happens taken out:

* `windowClock_le_of_shut`, ★★ `returnClock_le_of_obs_le` — **while the event's occupancy is
  small the clock is `0`, so later it is at most `c (u − s₁)`**;
* ★★ `returnDetectorShift_le_of_clock` — the detector's displacement in two stages: at most
  `ρ (ε t₁ + (t − t₁))` when the clock is at most `τ₁` up to `t₁`;
* ★★ `le_returnDetectorShift_of_clock` — at least `ρ q' (t − u₂)` when the clock is in
  `[τ₂, τ₃]` on `[u₂, t]`;
* ★★★ `released_detector_records_of_shift` — **the detector's two counts from three
  inequalities on its displacement**: at most `1/6` at `t₁`, between `1/3` and `2/3` at `t`.

## Honest scope

⚠️ **No instance here.** These are the statements an instance composes. By hand, for the
flat packet and the box of UD-245 as both carriers (misses the box up to `M/4`, inside from
`M` to `2M`, tail `1/10`): the hypotheses of UD-277 are not met by the windows proved there
(they force a dwell window `[τ₂, τ₃]` with `τ₃ > 2 τ₂`), and those of UD-278 are not either,
since the event's pointer would have to display within `2M` and also stay inside the window
for the return carrier's whole transit. With the bounds here the two-count history of
the detector can be met when the return carrier's transit in flow time is at least about
`127 M`, with the event's pointer as a slow gate that is not itself read. None of this
arithmetic is in Lean.

⚠️ **The clock's bounds are hypotheses** of the two displacement statements; they are
supplied by `returnClock_le_of_obs_le`, `returnClock_nonneg` and `le_returnClock_of_dwell`.

⚠️ **On the fibres where the detector's profile vanishes**, a null set. **The constant `c`.**
**Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-26, UD-245, UD-274, UD-276, UD-277, UD-279; §9.4);
`specs/unified-records-spacetime-task-plans.md` (§9, route (γ5));
`RecordLayer/UnifiedReleasedClock.lean` (`releasedClock_eq_zero_of_obs_le`,
`le_releasedClock_of_dwell`); `RecordLayer/UnifiedReleasedArrival.lean` (`returnClock`,
`returnDetectorShift_eq`); `RecordLayer/UnifiedReleasedRecord.lean`
(`released_detector_isTickCount`, `released_detector_arrival_records`);
`RecordLayer/TorusArrival.lean` (`integral_le_of_arrival`, `le_integral_of_dwell`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Projectivization Matrix.UnitaryGroup MeasureTheory
open NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The clock after a stage in which the window is shut -/

/-- A window at most `1` that is shut along the displacement up to `s₁` gives a clock of at
most `c (u − s₁)` at `u ≥ s₁`. -/
theorem windowClock_le_of_shut {b s : ℝ → ℝ} (hb : Continuous b) (hs : Continuous s)
    (hb1 : ∀ x, b x ≤ 1) {c : ℝ} (hc : 0 ≤ c) (a₀ : ℝ) {s₁ u : ℝ} (h1 : 0 ≤ s₁)
    (h1u : s₁ ≤ u) (hz : ∀ v, 0 ≤ v → v ≤ s₁ → b (a₀ + s v) = 0) :
    c * ∫ v in (0 : ℝ)..u, b (a₀ + s v) ≤ c * (u - s₁) := by
  have hcont : Continuous fun v : ℝ => b (a₀ + s v) := hb.comp (continuous_const.add hs)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 s₁) (hcont.intervalIntegrable (μ := volume) s₁ u)
  have hA : ∫ v in (0 : ℝ)..s₁, b (a₀ + s v) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => by
      rw [Set.uIcc_of_le h1] at hv
      exact hz v hv.1 hv.2, intervalIntegral.integral_zero]
  have hB := intervalIntegral.integral_mono_on h1u (hcont.intervalIntegrable s₁ u)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun v _ => hb1 _
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hB
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← hsplit, hA]
  linarith

section Clock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ha P : Matrix ι ι ℂ} {f b : ℝ → ℝ}

/-- ★★ **The clock does not start before the event's occupancy does.** On a fibre with rate
`κ = −2 f'(φ) ≥ 0`, a continuous window at most `1` and shut on `[a₀, a₀ + δ]`, `c ≥ 0`: if
the occupancy that drives the event's pointer is between `0` and `ε` up to `s₁`, with
`κ ε s₁ ≤ δ`, the clock at `u ≥ s₁` is at most `c (u − s₁)`. -/
theorem returnClock_le_of_obs_le (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hbc : Continuous b) (hb1 : ∀ x, b x ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) {a₀ δ : ℝ} (hbz : ∀ x, a₀ ≤ x → x ≤ a₀ + δ → b x = 0)
    {pa : GenArena ι} {s₁ u ε : ℝ} (h1 : 0 ≤ s₁) (h1u : s₁ ≤ u)
    (h0 : ∀ s, 0 ≤ s → s ≤ s₁ →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hε : ∀ s, 0 ≤ s → s ≤ s₁ →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ ε)
    (hδ : -2 * hf.deriv_periodic.lift φ * (ε * s₁) ≤ δ) :
    returnClock hHa hP hf b c pa a₀ φ u ≤ c * (u - s₁) := by
  have hε0 : 0 ≤ ε := (h0 0 le_rfl h1).trans (hε 0 le_rfl h1)
  refine windowClock_le_of_shut (s := fun v => idxPointerShift hHa hP hf φ pa v) hbc
    (continuous_idxPointerShift hHa hP hf φ pa) hb1 hc a₀ h1 h1u fun v hv0 hv1 => ?_
  show b (a₀ + idxPointerShift hHa hP hf φ pa v) = 0
  have hlo := le_idxPointerShift_of_le hHa hP hf hκ (q := 0) hv0
    (fun s hs hsv => h0 s hs (hsv.trans hv1))
  have hup := idxPointerShift_le_of_obs_le hHa hP hf hκ hv0
    (fun s hs hsv => hε s hs (hsv.trans hv1))
  have hmono : -2 * hf.deriv_periodic.lift φ * (ε * v)
      ≤ -2 * hf.deriv_periodic.lift φ * (ε * s₁) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv1 hε0) hκ
  rw [mul_zero, zero_mul] at hlo
  exact hbz _ (by linarith) (by linarith)

end Clock

/-! ### The detector's displacement from bounds on the clock -/

section Shift

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ}

/-- ★★ **The detector's displacement in two stages.** With a rate `ρ ≥ 0` and `⟨Q⟩ ≤ 1` at
every ray: if the clock stays in `[0, τ₁]` up to `t₁ ≤ t`, and the return carrier's free
occupancy of `Q` is at most `ε` at its own times in `[0, τ₁]`, the displacement at `t` is at
most `ρ (ε t₁ + (t − t₁))`. -/
theorem returnDetectorShift_le_of_clock (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (c : ℝ) {Q : Matrix κ κ ℂ} (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1)
    (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) {t₁ t τ₁ ε : ℝ}
    (h1 : 0 ≤ t₁) (h1t : t₁ ≤ t)
    (hck : ∀ u, 0 ≤ u → u ≤ t₁ → 0 ≤ returnClock hHa hP hf b c pa a₀ φ u
      ∧ returnClock hHa hP hf b c pa a₀ φ u ≤ τ₁)
    (hε : ∀ τ, 0 ≤ τ → τ ≤ τ₁ → arenaObs Q (arenaKick (idxFreeU hHR τ) r) ≤ ε) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
      ≤ -2 * hh.deriv_periodic.lift χ₂ * (ε * t₁ + (t - t₁)) := by
  rw [returnDetectorShift_eq]
  exact mul_le_mul_of_nonneg_left (integral_le_of_arrival
    (continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ) h1 h1t
    (fun u hu0 hu1 => hε _ (hck u hu0 hu1).1 (hck u hu0 hu1).2) fun _ _ _ => hQ1 _) hρ

/-- ★★ **The detector's displacement while the clock is in the dwell window.** With a rate
`ρ ≥ 0` and `⟨Q⟩ ≥ 0` at every ray: if the clock is in `[τ₂, τ₃]` at every flow time in
`[u₂, t]`, and the return carrier's free occupancy of `Q` is at least `q'` at its own times
in `[τ₂, τ₃]`, the displacement at `t` is at least `ρ q' (t − u₂)`. -/
theorem le_returnDetectorShift_of_clock (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (c : ℝ) {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) {u₂ t τ₂ τ₃ q' : ℝ}
    (h2 : 0 ≤ u₂) (h2t : u₂ ≤ t)
    (hck : ∀ u, u₂ ≤ u → u ≤ t → τ₂ ≤ returnClock hHa hP hf b c pa a₀ φ u
      ∧ returnClock hHa hP hf b c pa a₀ φ u ≤ τ₃)
    (hq' : ∀ τ, τ₂ ≤ τ → τ ≤ τ₃ → q' ≤ arenaObs Q (arenaKick (idxFreeU hHR τ) r)) :
    -2 * hh.deriv_periodic.lift χ₂ * (q' * (t - u₂))
      ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t := by
  rw [returnDetectorShift_eq]
  exact mul_le_mul_of_nonneg_left (le_integral_of_dwell
    (continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ) h2 h2t
    (fun _ _ _ => hQ0 _) fun u hu2 hut => hq' _ (hck u hu2 hut).1 (hck u hu2 hut).2) hρ

end Shift

/-! ### The detector's counts from its displacement -/

section Record

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The detector's two counts from three inequalities on its displacement.** On a
fibre where the detector's profile vanishes and its rate is `ρ = −2 h'(χ₂) ≥ 0`, from a
ready detector pointer and a product ray, with `⟨Q⟩ ≥ 0` at every ray: if the displacement is
at most `1/6` at `t₁` and between `1/3` and `2/3` at `t`, the start of the run is in the
compatible region of "the detector has counted `0` at `t₁`" and "the detector has counted
`1` at `t`". -/
theorem released_detector_records_of_shift (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) (c : ℝ) {Q : Matrix κ κ ℂ}
    (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) {χ : KTorus} (hχ : χ ∈ readyArc 2) (h0 : hh.lift χ.2 = 0)
    (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2) {t₁ t : ℝ} (ht₁ : 0 ≤ t₁) (ht : 0 ≤ t)
    (hearly : returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t₁ ≤ 1 / 6)
    (hlate : 1 / 3 ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t)
    (hmax : returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t ≤ 2 / 3) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r p₀).semantics
        [TickReadout.startFact true t₁ 0, TickReadout.startFact true t 1] := by
  have hr : rep χ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hχ
  rw [shearWidth_two] at hr
  have hbc : Continuous b := hcb.continuous
  have c0 := released_detector_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0
    ht₁ (monotoneOn_returnDetectorShift hHa hP hHR hf hh hbc c hQ0 pa r a₀ φ hρ t₁)
  rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  have c1 := released_detector_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0
    ht (monotoneOn_returnDetectorShift hHa hP hHR hf hh hbc c hQ0 pa r a₀ φ hρ t)
  rw [card_tickIndices_eq_one_of_ready hr.1 hr.2 (by linarith [hr.1])
    (by linarith [hr.2])] at c1
  refine (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r
    p₀).mem_compatibleSet_startFacts [(true, t₁, 0), (true, t, 1)] _ fun r' hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  exacts [c0, c1]

end Record

end CSD.RecordLayer

end
