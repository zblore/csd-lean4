/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracPointerThreshold

/-!
# The record the pointer holds

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #353 — milestone **M2, part C** of the
author's programme "From `Σ` to physical spacetime" (2026-11-09): the last two of the four
statements M2 keeps apart, *a definite outcome being selected* and *the persistence and readability
of that outcome*, and the milestone's acceptance: a generated record is a theorem about the
Hamiltonian flow, not a record process added to it.

`RecordLayer/DiracPointerWrite.lean` (#351) bounded the displacement of the pointer of
`Σ_* = ℂℙ^{2M+1} × T²` and `RecordLayer/DiracPointerThreshold.lean` (#352) proved when that
displacement crosses the threshold at one time. This module proves that the readout then *holds*
its value over an interval, and packages the write as an `ActualOccurrence` of
`RecordLayer/RecordOccurrence.lean` whose `evolve` field is `diracPointerFlow`.

The step from one time to an interval is monotonicity. On a fibre with rate `κ = −2 g f'(θ₂) ≥ 0`
the pointer's displacement is `κ` times an integral of an occupancy, which is nonnegative, so the
pointer does not turn back. Three values of the displacement then fix the readout history on three
intervals: at most `1/6` at `τ₀` (not displayed up to `τ₀`), at least `1/3` at `τ₁` and at most
`2/3` at `τ₂` (displayed throughout `[τ₁, τ₂]`).

## A turn of the pointer, and a generic fact about writes

* `pshift_notMem_displayArc_of_le` — a ready pointer turned forward by at most `1/6` is not
  displayed; `pshift_one` — a full turn brings the pointer back;
* `diracDisplayed_eq_false_of_ready` — a ready pointer reads `false`;
* `not_isRecordWrite_of_forall_ne` — a history that does not show `v` up to `T` has no write of `v`
  completed by `T`.

## The pointer does not turn back

* `continuous_diracPointerShift`; ★★ `diracPointerShift_mono` — **on a fibre with `κ ≥ 0` the
  displacement is monotone in time**, for every carrier.

## The flow as a two-time evolution

* `continuous_diracPointerFlow`, `measurable_diracPointerFlow`;
* `diracPointerEvolve` — the flow over the elapsed time; `diracPointerEvolve_self`,
  `diracPointerEvolve_comp`, `diracPointerEvolve_shift`, `measurable_diracPointerEvolve`.

## Persistence, and the record

* ★★ `diracPointerFlow_displayed_of_mono`, `diracPointerFlow_not_displayed_of_mono` — **the readout
  on an interval**, from the displacement at its ends;
* ★★★ `isRecordWrite_diracPointerFlow` — **the readout history of the flow writes `true`**, with
  write interval `[τ₀, τ₁]` and window `τ₂ − τ₁`, for any carrier, given the three values;
* ★★★ `diracPointerRecord` — **that write as an `ActualOccurrence`** whose `evolve` is
  `diracPointerEvolve` (`diracPointerRecord_evolve`, `_readout`, `_prep`, `_window`).

## Where there is no record

* ★★ `not_isRecordWrite_of_mem_slowFibres` — **on a slow fibre of horizon `T` no record is
  completed by `T`**, whatever the carrier;
* ★★ `not_isRecordWrite_of_rateAt_eq_zero` — **on a fibre where `f'(θ₂) = 0` no record is written
  at any time**; every `C¹` profile has one (`exists_rateAt_eq_zero`).

## The pointer coming back

* `diracPointerFlow_snd_of_shift_eq_one`; ★★ `exists_diracPointerFlow_snd_eq` — **once the
  displacement has reached a full turn there was an earlier time at which the pointer pair was
  exactly its ready value** (intermediate value theorem).

## The record fibres: a carrier on the detector's site

* `recordFibres` — `8 (‖H_D‖ + |g f(θ₂)|) < 3 κ`; `isOpen_recordFibres`,
  `rateAt_pos_of_mem_recordFibres`, `norm_diracPointerH_lt_of_mem_recordFibres`;
* ★★ `third_le_diracPointerShift_siteRay` — the signal has turned the pointer by `1/3` at
  `1/(2κ)`; `diracPointerShift_div_rateAt_le` — any carrier by at most `c` at `c/κ`;
* ★★★ `isRecordWrite_siteRay` — **on a record fibre the carrier on the detector's site writes
  `true`**: not displayed before `1/(6κ)`, displayed throughout `[1/(2κ), 2/(3κ)]`;
  `siteRayRecord` — the occurrence (`siteRayRecord_evolve`, `_prep`, `_window`,
  `siteRayRecord_window_pos`);
* ★★★ `diracPointerFlow_not_displayed_of_mem_recordFibres`, `not_isRecordWrite_siteRay_of_ne` —
  **the carrier on another site reads `false` throughout `[0, 2/(3κ)]`** and completes no write of
  `true` in that time;
* ★★ `zero_mem_recordFibres_trainF`, ★★★ `volume_recordFibres_trainF_pos`,
  `exists_volume_recordFibres_pos` — **for the profile `trainF` and any coupling with
  `4 ‖H_D‖ < 3 g` the record fibres have positive measure.**

## The two-mode packet on the fibre `θ₂ = 0`

* `rateAt_trainF_zero`; `diracPointerShift_twoMode_zero_le`, `le_diracPointerShift_twoMode_zero`;
* ★★★ `isRecordWrite_twoMode`, `twoModeRecord` — **for `0 < g ≤ 29/12` the two-mode packet writes
  `true`** with write interval `[(29 − 12g)/(29g), (58 + 12g)/(29g)]` and window
  `(58 − 24g)/(29g)` (`twoModeRecord_evolve`, `twoModeRecord_window`);
* ★★★ `twoMode_record_erased` — **the record does not last**: at some time after the window and no
  later than `7/g` the pointer pair is exactly its ready value and the readout is `false`.

## The milestone

* ★★★ `diracPointer_record` — **M2 on a record fibre**: the displacement, the threshold held over
  an interval, the two carriers told apart, the write of nonzero window along the flow, and the
  fibres on which there is no record by a given time.

## Honest scope

* **Exact versus approximate.** Monotonicity, the two interval statements and
  `isRecordWrite_diracPointerFlow` are exact, given the three displacement values. The times of
  the record on a record fibre come from the first-order bound `‖H‖ t²` of #352 and are not sharp.
  The times of the two-mode record come from the closed form with `|sin| ≤ 1` and are not sharp
  either.
* **An interval with stated ends, never permanence.** The window is where the proof ends. For the
  carrier on the detector's site nothing is proved after `2/(3κ)`, in either direction. For the
  two-mode packet the record is proved to have gone by `7/g` (`twoMode_record_erased`).
* **"Selected" means fixed by the ontic initial point.** The flow is deterministic. The readout
  history is a function of the carrier's ray and the angles, and two carriers are compared: on the
  detector's site (`true` through the window) and on another site (`false` through it). No
  probability is stated, no Born weight appears, and a carrier with weight on both sites is
  without a statement here. That question is milestone M3.
* **Not universal.** On a slow fibre no record is completed by `T`, and those have positive measure
  for every `C¹` profile and every `T` (`volume_slowFibres_pos`). On a fibre with `f'(θ₂) = 0`
  there is never one. Fibres with a negative rate carry no statement: the monotonicity is used with
  `κ ≥ 0`. The measure of `recordFibres` is shown positive and not computed.
* **The carrier on the detector's site does not arrive.** It starts there. The two-mode packet has
  weight on every site at every time, and its record is proved on the single fibre `θ₂ = 0`, a null
  set of fibres. A packet with no weight at the detector that travels to it is not treated.
* **The conserved angle.** `θ₂` is conserved, so the pointer does not act back on the carrier
  beyond the static site potential `g f(θ₂) P_j`. That is the model of #349.
* **What is a definition and what is derived.** The readout, the ready set, the value `true`, the
  site label and the `evolve` field of the occurrences are definitions. That `evolve` is the flow
  of #349 is the check asked of this milestone, and it holds by `rfl`. What is derived is the
  `isWrite` field: the readout history of that flow is not `true` before the write and is `true`
  through the window.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  coupling `−2 g f(θ₂) ⟨P_j⟩` (UA-5) and the Dirac propagation law (UA-8) are the definitions every
  statement here is about. The two arcs, the site, the profile, the coupling, the carrier's initial
  ray and the fibre `θ₂` a statement holds on are preparation input (UA-4). Haar measure on the
  `θ₂` circle is used only to say that a set of fibres is not null. Nothing here is a statement
  about Born weights, clocks or spacetime.

References: `specs/BACKLOG.md` #353, #352, #351, #349, #350, #191, #194; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-4, UO-5; UD-40 to UD-44);
`RecordLayer/DiracPointerThreshold.lean` (`diracReady`, `diracDisplayed`, `diracPointerFlow_snd`,
`diracPointerFlow_displayed`, `diracPointerFlow_not_displayed`, `diracPointerShift_eq_rateAt`,
`le_diracPointerShift_siteRay`, `diracPointerFlow_siteRay_of_ne_not_displayed`, `slowFibres`,
`diracPointerFlow_not_displayed_of_mem_slowFibres`, `volume_slowFibres_pos`);
`RecordLayer/DiracPointerWrite.lean` (`diracOccupancy_nonneg`, `continuous_diracOccupancy`,
`diracPointerShift_twoMode_zero`, `twoModeRay`); `RecordLayer/DiracPointerHamiltonian.lean`
(`diracPointerFlow`, `diracPointerFlow_zero`, `diracPointerFlow_add`,
`hasDerivAt_diracPointerShift`, `siteRay`); `RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`,
`ActualOccurrence`); `RecordLayer/ActivatedWrite.lean` (`activatedRegister`,
`readyArc_disjoint_displayArc`, `exists_rateAt_eq_zero`); `RecordLayer/DiracDetector.lean`
(`siteFin`); `Mathlib/Geometry/Manifold/HamiltonianFlowVolume.lean`
(`DifferentialForm.IsSymplectic.continuous_hamiltonianFlow`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A turn of the pointer, and a generic fact about writes -/

/-- A ready pointer turned forward by at most a sixth of a turn is not in the displayed arc. -/
theorem pshift_notMem_displayArc_of_le {q : KTorus} (hq : q ∈ readyArc 2) {a : ℝ} (h₀ : 0 ≤ a)
    (h₁ : a ≤ 1 / 6) : pshift a q ∉ displayArc := by
  intro hd
  change rep (pshift a q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hd hr
  rw [rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩] at hd
  linarith [hd.1, hr.2]

/-- A full turn brings the pointer back. -/
theorem pshift_one (q : KTorus) : pshift 1 q = q := by
  show (q.1 + ((1 : ℝ) : AddCircle (1 : ℝ)), q.2) = q
  rw [AddCircle.coe_period, add_zero]

/-- A ready pointer reads `false`: the ready arc and the displayed arc do not meet. -/
theorem diracDisplayed_eq_false_of_ready {M : ℕ} {x : KSigma (2 * M + 1 + 1)}
    (hx : x ∈ diracReady M) : diracDisplayed M x = false :=
  diracDisplayed_eq_false_iff.2 fun hd =>
    Set.disjoint_left.1 readyArc_disjoint_displayArc (show x.2 ∈ readyArc 2 from hx) hd

/-- A history that does not show `v` at any time up to `T` has no write of `v` completed by `T`. -/
theorem not_isRecordWrite_of_forall_ne {Ω : Type*} {h : ℝ → Ω} {t₀ τ₀ τ₁ w T : ℝ} {v : Ω}
    (hT : τ₁ ≤ T) (hne : ∀ t, t₀ ≤ t → t ≤ T → h t ≠ v) : ¬ IsRecordWrite h t₀ τ₀ τ₁ w v :=
  fun hw => hne τ₁ (hw.start_le.trans hw.interval) hT
    (hw.holds τ₁ le_rfl (le_add_of_nonneg_right hw.window_nonneg))

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-! ### The pointer does not turn back -/

theorem continuous_diracPointerShift (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    Continuous fun t => diracPointerShift J μ g j hf φ p t :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_diracPointerShift J μ g j hf φ p t).continuousAt

/-- ★★ **On a fibre with a nonnegative rate the displacement is monotone in time**, for every
carrier: it is the rate times an integral of an occupancy, which is nonnegative. -/
theorem diracPointerShift_mono {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ rateAt g 1 hf φ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {s t : ℝ} (hst : s ≤ t) :
    diracPointerShift J μ g j hf φ p s ≤ diracPointerShift J μ g j hf φ p t := by
  rw [diracPointerShift_eq_rateAt, diracPointerShift_eq_rateAt]
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have hi : ∀ a b : ℝ,
      IntervalIntegrable (fun u => diracOccupancy J μ g j hf φ p u) volume a b :=
    fun a b => (continuous_diracOccupancy J μ g j hf φ p).intervalIntegrable a b
  have h := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)
  have hn : 0 ≤ ∫ u in s..t, diracOccupancy J μ g j hf φ p u :=
    intervalIntegral.integral_nonneg hst fun u _ => diracOccupancy_nonneg J μ g j hf φ p u
  linarith

/-! ### The flow as a two-time evolution -/

theorem continuous_diracPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Continuous (diracPointerFlow J μ g j hf hc t) :=
  (arenaForm_isSymplectic (2 * M + 1)).continuous_hamiltonianFlow
    (contMDiff_diracPointerEnergy J μ g j hf hc) t

theorem measurable_diracPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measurable (diracPointerFlow J μ g j hf hc t) :=
  (continuous_diracPointerFlow J μ g j hf hc t).measurable

/-- **The two-time propagator** of the joint dynamics: autonomous, so only the elapsed time
enters. It is `diracPointerFlow` and nothing else. -/
noncomputable def diracPointerEvolve (hc : ContDiff ℝ ∞ f) (s t : ℝ) :
    KSigma (2 * M + 1 + 1) → KSigma (2 * M + 1 + 1) :=
  diracPointerFlow J μ g j hf hc (t - s)

theorem diracPointerEvolve_self (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    diracPointerEvolve J μ g j hf hc t t = id := by
  funext x
  rw [diracPointerEvolve, sub_self, diracPointerFlow_zero]
  rfl

/-- **The two-time law.** -/
theorem diracPointerEvolve_comp (hc : ContDiff ℝ ∞ f) (s t u : ℝ) :
    diracPointerEvolve J μ g j hf hc t u ∘ diracPointerEvolve J μ g j hf hc s t
      = diracPointerEvolve J μ g j hf hc s u := by
  funext x
  show diracPointerFlow J μ g j hf hc (u - t) (diracPointerFlow J μ g j hf hc (t - s) x)
    = diracPointerFlow J μ g j hf hc (u - s) x
  rw [← diracPointerFlow_add, sub_add_sub_cancel]

/-- **Autonomy**: shifting both times leaves the propagator unchanged. -/
theorem diracPointerEvolve_shift (hc : ContDiff ℝ ∞ f) (s t a : ℝ) :
    diracPointerEvolve J μ g j hf hc (s + a) (t + a) = diracPointerEvolve J μ g j hf hc s t := by
  rw [diracPointerEvolve, diracPointerEvolve, add_sub_add_right_eq_sub]

theorem measurable_diracPointerEvolve (hc : ContDiff ℝ ∞ f) (s t : ℝ) :
    Measurable (diracPointerEvolve J μ g j hf hc s t) :=
  measurable_diracPointerFlow J μ g j hf hc (t - s)

/-! ### Persistence: the readout on an interval -/

/-- ★★ **The readout holds over an interval.** On a fibre with rate `κ ≥ 0`, from a ready pointer:
if the displacement is at least `1/3` at `τ₁` and at most `2/3` at `τ₂`, the flow is in the
displayed region throughout `[τ₁, τ₂]`. -/
theorem diracPointerFlow_displayed_of_mono (hc : ContDiff ℝ ∞ f) {q : KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 ≤ rateAt g 1 hf q.2) (p : GenArena (ZMod (M + 1) × Fin 2))
    {τ₁ τ₂ t : ℝ} (h₁ : 1 / 3 ≤ diracPointerShift J μ g j hf q.2 p τ₁)
    (h₂ : diracPointerShift J μ g j hf q.2 p τ₂ ≤ 2 / 3) (ht₁ : τ₁ ≤ t) (ht₂ : t ≤ τ₂) :
    diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) = true :=
  diracPointerFlow_displayed J μ g j hf hc hq p
    (h₁.trans (diracPointerShift_mono J μ g j hf hκ p ht₁))
    ((diracPointerShift_mono J μ g j hf hκ p ht₂).trans h₂)

/-- ★★ **Before the write.** On a fibre with rate `κ ≥ 0`, from a ready pointer: if the
displacement is at most `1/6` at `τ₀`, the flow is outside the displayed region throughout
`[0, τ₀]`. -/
theorem diracPointerFlow_not_displayed_of_mono (hc : ContDiff ℝ ∞ f) {q : KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 ≤ rateAt g 1 hf q.2) (p : GenArena (ZMod (M + 1) × Fin 2))
    {τ₀ t : ℝ} (h₀ : diracPointerShift J μ g j hf q.2 p τ₀ ≤ 1 / 6) (ht0 : 0 ≤ t)
    (ht : t ≤ τ₀) :
    diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) = false := by
  rw [diracDisplayed_eq_false_iff, diracPointerFlow_snd]
  exact pshift_notMem_displayArc_of_le hq (diracPointerShift_nonneg J μ g j hf hκ p ht0)
    ((diracPointerShift_mono J μ g j hf hκ p ht).trans h₀)

/-- ★★★ **The readout history of the Hamiltonian flow writes `true`.** On a fibre with rate
`κ ≥ 0`, from a ready pointer and any carrier: if the displacement is at most `1/6` at `τ₀`, at
least `1/3` at `τ₁` and at most `2/3` at `τ₂`, the history is not `true` on `[0, τ₀)` and is `true`
on `[τ₁, τ₂]`. -/
theorem isRecordWrite_diracPointerFlow (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 ≤ rateAt g 1 hf q.2) (p : GenArena (ZMod (M + 1) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : diracPointerShift J μ g j hf q.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ diracPointerShift J μ g j hf q.2 p τ₁)
    (h₂ : diracPointerShift J μ g j hf q.2 p τ₂ ≤ 2 / 3) :
    IsRecordWrite
      (fun t => diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)))
      0 τ₀ τ₁ (τ₂ - τ₁) true where
  start_le := hτ₀
  interval := hτ₁
  window_nonneg := sub_nonneg.2 hτ₂
  before := fun t ht0 ht => by
    show diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) ≠ true
    rw [diracPointerFlow_not_displayed_of_mono J μ g j hf hc hq hκ p h₀ ht0 ht.le]
    exact Bool.false_ne_true
  holds := fun t ht₁ ht₂ =>
    diracPointerFlow_displayed_of_mono J μ g j hf hc hq hκ p h₁ h₂ ht₁ (by linarith)

/-- ★★★ **The write as an actual occurrence on the shared arena.** Its `evolve` is the Hamiltonian
flow `diracPointerFlow` over the elapsed time, its readout and ready set are those of
`DiracPointerThreshold.lean`, its preparation is the carrier `p` with a ready pointer, and its
`isWrite` field is `isRecordWrite_diracPointerFlow`. The three displacement values are hypotheses
here; the instances below discharge them from the flow. -/
noncomputable def diracPointerRecord (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 ≤ rateAt g 1 hf q.2) (p : GenArena (ZMod (M + 1) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
    (h₀ : diracPointerShift J μ g j hf q.2 p τ₀ ≤ 1 / 6)
    (h₁ : 1 / 3 ≤ diracPointerShift J μ g j hf q.2 p τ₁)
    (h₂ : diracPointerShift J μ g j hf q.2 p τ₂ ≤ 2 / 3) :
    ActualOccurrence (KSigma (2 * M + 1 + 1)) Bool (M + 1) where
  evolve := diracPointerEvolve J μ g j hf hc
  evolve_self := diracPointerEvolve_self J μ g j hf hc
  evolve_comp := diracPointerEvolve_comp J μ g j hf hc
  measurable_evolve := measurable_diracPointerEvolve J μ g j hf hc
  readout := diracDisplayed M
  measurable_readout := measurable_diracDisplayed M
  ready := diracReady M
  measurableSet_ready := measurableSet_diracReady M
  prep := (diracArenaEquiv M p, q)
  prep_mem := hq
  site := {siteFin j}
  start := 0
  value := true
  writeStart := τ₀
  writeEnd := τ₁
  window := τ₂ - τ₁
  isWrite :=
    { start_le := hτ₀
      interval := hτ₁
      window_nonneg := sub_nonneg.2 hτ₂
      before := fun t ht0 ht => by
        show diracDisplayed M
          (diracPointerFlow J μ g j hf hc (t - 0) (diracArenaEquiv M p, q)) ≠ true
        rw [sub_zero]
        exact (isRecordWrite_diracPointerFlow J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).before
          t ht0 ht
      holds := fun t ht₁ ht₂ => by
        show diracDisplayed M
          (diracPointerFlow J μ g j hf hc (t - 0) (diracArenaEquiv M p, q)) = true
        rw [sub_zero]
        exact (isRecordWrite_diracPointerFlow J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).holds
          t ht₁ ht₂ }

section RecordFields

variable (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
  (hκ : 0 ≤ rateAt g 1 hf q.2) (p : GenArena (ZMod (M + 1) × Fin 2)) {τ₀ τ₁ τ₂ : ℝ}
  (hτ₀ : 0 ≤ τ₀) (hτ₁ : τ₀ ≤ τ₁) (hτ₂ : τ₁ ≤ τ₂)
  (h₀ : diracPointerShift J μ g j hf q.2 p τ₀ ≤ 1 / 6)
  (h₁ : 1 / 3 ≤ diracPointerShift J μ g j hf q.2 p τ₁)
  (h₂ : diracPointerShift J μ g j hf q.2 p τ₂ ≤ 2 / 3)

/-- **The occurrence's evolution is the Hamiltonian flow of #349**, by definition: no record
process is added to the dynamics. -/
theorem diracPointerRecord_evolve :
    (diracPointerRecord J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).evolve
      = diracPointerEvolve J μ g j hf hc := rfl

theorem diracPointerRecord_readout :
    (diracPointerRecord J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).readout
      = diracDisplayed M := rfl

theorem diracPointerRecord_prep :
    (diracPointerRecord J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).prep
      = (diracArenaEquiv M p, q) := rfl

theorem diracPointerRecord_window :
    (diracPointerRecord J μ g j hf hc hq hκ p hτ₀ hτ₁ hτ₂ h₀ h₁ h₂).window = τ₂ - τ₁ := rfl

end RecordFields

/-! ### Where there is no record -/

/-- ★★ **On a slow fibre of horizon `T` no record is completed by `T`, whatever the carrier.** -/
theorem not_isRecordWrite_of_mem_slowFibres (hc : ContDiff ℝ ∞ f) {T : ℝ} {q : KTorus}
    (hq : q ∈ readyArc 2) (hφ : q.2 ∈ slowFibres g hf T) (p : GenArena (ZMod (M + 1) × Fin 2))
    {τ₀ τ₁ w : ℝ} (hτ₁ : τ₁ ≤ T) :
    ¬ IsRecordWrite
      (fun t => diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)))
      0 τ₀ τ₁ w true :=
  not_isRecordWrite_of_forall_ne hτ₁ fun t ht0 htT => by
    show diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) ≠ true
    rw [diracPointerFlow_not_displayed_of_mem_slowFibres J μ g j hf hc hq hφ p ht0 htT]
    exact Bool.false_ne_true

/-- ★★ **On a fibre where the rate vanishes no record is written at any time**, whatever the
carrier: the pointer does not move. -/
theorem not_isRecordWrite_of_rateAt_eq_zero (hc : ContDiff ℝ ∞ f) {q : KTorus}
    (hq : q ∈ readyArc 2) (hφ : rateAt g 1 hf q.2 = 0) (p : GenArena (ZMod (M + 1) × Fin 2))
    {τ₀ τ₁ w : ℝ} :
    ¬ IsRecordWrite
      (fun t => diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)))
      0 τ₀ τ₁ w true :=
  not_isRecordWrite_of_forall_ne le_rfl fun t _ _ => by
    show diracDisplayed M (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)) ≠ true
    rw [diracPointerFlow_not_displayed J μ g j hf hc hq p (by
      rw [diracPointerShift_eq_rateAt, hφ, zero_mul, abs_zero]
      norm_num)]
    exact Bool.false_ne_true

/-! ### The pointer coming back -/

/-- At a time when the displacement is exactly one turn the pointer pair is its starting value. -/
theorem diracPointerFlow_snd_of_shift_eq_one (hc : ContDiff ℝ ∞ f)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : KTorus) {t : ℝ}
    (h : diracPointerShift J μ g j hf q.2 p t = 1) :
    (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)).2 = q := by
  rw [diracPointerFlow_snd, h, pshift_one]

/-- ★★ **Once the displacement has reached a full turn, the pointer has been back.** If the
displacement at `t ≥ 0` is at least `1`, there is a time in `[0, t]` at which it is exactly `1` and
the pointer pair of the flow is exactly its starting value. -/
theorem exists_diracPointerFlow_snd_eq (hc : ContDiff ℝ ∞ f)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : KTorus) {t : ℝ} (ht : 0 ≤ t)
    (h : 1 ≤ diracPointerShift J μ g j hf q.2 p t) :
    ∃ s ∈ Icc (0 : ℝ) t, diracPointerShift J μ g j hf q.2 p s = 1
      ∧ (diracPointerFlow J μ g j hf hc s (diracArenaEquiv M p, q)).2 = q := by
  have hmem : (1 : ℝ) ∈ Icc (diracPointerShift J μ g j hf q.2 p 0)
      (diracPointerShift J μ g j hf q.2 p t) := by
    rw [diracPointerShift_zero]
    exact ⟨zero_le_one, h⟩
  obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc ht
    (continuous_diracPointerShift J μ g j hf q.2 p).continuousOn hmem
  exact ⟨s, hs, hs1, diracPointerFlow_snd_of_shift_eq_one J μ g j hf hc p q hs1⟩

/-! ### The record fibres: a carrier on the detector's site -/

variable (M) in
/-- **The record fibres**: the angles `θ₂` at which the rate `κ = −2 g f'` dominates the carrier's
Hamiltonian, `8 (‖H_D‖ + |g f(θ₂)|) < 3 κ`. On them the write of the carrier on the detector's site
is complete, and held, before the carrier has moved. -/
def recordFibres : Set (AddCircle (1 : ℝ)) :=
  {φ | 8 * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) < 3 * rateAt g 1 hf φ}

theorem isOpen_recordFibres (hf1 : ContDiff ℝ 1 f) : IsOpen (recordFibres M J μ g hf) := by
  have hκ := continuous_rateAt g 1 hf hf1
  have hh : Continuous fun φ : AddCircle (1 : ℝ) =>
      ‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ| :=
    continuous_const.add (continuous_const.mul (continuous_periodicLift hf hf1.continuous)).abs
  exact isOpen_lt (continuous_const.mul hh) (continuous_const.mul hκ)

theorem rateAt_pos_of_mem_recordFibres {φ : AddCircle (1 : ℝ)}
    (hφ : φ ∈ recordFibres M J μ g hf) : 0 < rateAt g 1 hf φ := by
  have h : 8 * (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) < 3 * rateAt g 1 hf φ := hφ
  have h1 : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  have h2 := abs_nonneg (g * hf.lift φ)
  linarith

theorem norm_diracPointerH_lt_of_mem_recordFibres {φ : AddCircle (1 : ℝ)}
    (hφ : φ ∈ recordFibres M J μ g hf) :
    8 * ‖diracPointerH J μ g j hf φ‖ < 3 * rateAt g 1 hf φ :=
  lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (norm_diracPointerH_le J μ g j hf φ) (by norm_num)) hφ

/-- ★★ **The signal has crossed by `1/(2κ)`**: on a record fibre the carrier on the detector's
site has turned the pointer by at least a third of a turn. -/
theorem third_le_diracPointerShift_siteRay {φ : AddCircle (1 : ℝ)}
    (hφ : φ ∈ recordFibres M J μ g hf) :
    1 / 3 ≤ diracPointerShift J μ g j hf φ (siteRay j) (1 / (2 * rateAt g 1 hf φ)) := by
  have hκ := rateAt_pos_of_mem_recordFibres J μ g hf hφ
  have hH := norm_diracPointerH_lt_of_mem_recordFibres J μ g j hf hφ
  refine le_trans ?_ (le_diracPointerShift_siteRay J μ g j hf hκ.le
    (one_div_nonneg.2 (mul_nonneg zero_le_two hκ.le)))
  have hκ0 : rateAt g 1 hf φ ≠ 0 := hκ.ne'
  have e : rateAt g 1 hf φ * (1 / (2 * rateAt g 1 hf φ)
        - ‖diracPointerH J μ g j hf φ‖ * (1 / (2 * rateAt g 1 hf φ)) ^ 2)
      = 1 / 2 - ‖diracPointerH J μ g j hf φ‖ / (4 * rateAt g 1 hf φ) := by
    field_simp
    ring
  have hb : ‖diracPointerH J μ g j hf φ‖ / (4 * rateAt g 1 hf φ) ≤ 3 / 32 := by
    rw [div_le_iff₀ (mul_pos four_pos hκ)]
    linarith
  rw [e]
  linarith

/-- The displacement at `c/κ` is at most `c`, for any carrier. -/
theorem diracPointerShift_div_rateAt_le {φ : AddCircle (1 : ℝ)} (hκ : 0 < rateAt g 1 hf φ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) {c : ℝ} (hc0 : 0 ≤ c) :
    diracPointerShift J μ g j hf φ p (c / rateAt g 1 hf φ) ≤ c :=
  (diracPointerShift_le_rateAt_mul J μ g j hf hκ.le p (div_nonneg hc0 hκ.le)).trans_eq
    (mul_div_cancel₀ c hκ.ne')

/-- ★★★ **On a record fibre the carrier on the detector's site writes `true`**, along the
Hamiltonian flow: the readout is not `true` before `1/(6κ)` and is `true` throughout
`[1/(2κ), 2/(3κ)]`. The window `2/(3κ) − 1/(2κ)` is `1/(6κ)`. -/
theorem isRecordWrite_siteRay (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) :
    IsRecordWrite
      (fun t => diracDisplayed M
        (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay j), q)))
      0 (1 / 6 / rateAt g 1 hf q.2) (1 / (2 * rateAt g 1 hf q.2))
      (2 / 3 / rateAt g 1 hf q.2 - 1 / (2 * rateAt g 1 hf q.2)) true := by
  have hκ := rateAt_pos_of_mem_recordFibres J μ g hf hφ
  have e : 1 / (2 * rateAt g 1 hf q.2) = 1 / 2 / rateAt g 1 hf q.2 := by
    rw [div_div]
  refine isRecordWrite_diracPointerFlow J μ g j hf hc hq hκ.le (siteRay j)
    (div_nonneg (by norm_num) hκ.le) ?_ ?_
    (diracPointerShift_div_rateAt_le J μ g j hf hκ _ (by norm_num))
    (third_le_diracPointerShift_siteRay J μ g j hf hφ)
    (diracPointerShift_div_rateAt_le J μ g j hf hκ _ (by norm_num))
  · rw [e]
    exact div_le_div_of_nonneg_right (by norm_num) hκ.le
  · rw [e]
    exact div_le_div_of_nonneg_right (by norm_num) hκ.le

/-- ★★★ **The record of the carrier on the detector's site**, as an actual occurrence on the
shared arena whose evolution is the Hamiltonian flow. -/
noncomputable def siteRayRecord (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) :
    ActualOccurrence (KSigma (2 * M + 1 + 1)) Bool (M + 1) :=
  diracPointerRecord J μ g j hf hc hq (rateAt_pos_of_mem_recordFibres J μ g hf hφ).le (siteRay j)
    (isRecordWrite_siteRay J μ g j hf hc hq hφ).start_le
    (isRecordWrite_siteRay J μ g j hf hc hq hφ).interval
    (sub_nonneg.1 (isRecordWrite_siteRay J μ g j hf hc hq hφ).window_nonneg)
    (diracPointerShift_div_rateAt_le J μ g j hf (rateAt_pos_of_mem_recordFibres J μ g hf hφ) _
      (by norm_num))
    (third_le_diracPointerShift_siteRay J μ g j hf hφ)
    (diracPointerShift_div_rateAt_le J μ g j hf (rateAt_pos_of_mem_recordFibres J μ g hf hφ) _
      (by norm_num))

theorem siteRayRecord_evolve (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) :
    (siteRayRecord J μ g j hf hc hq hφ).evolve = diracPointerEvolve J μ g j hf hc := rfl

theorem siteRayRecord_prep (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) :
    (siteRayRecord J μ g j hf hc hq hφ).prep = (diracArenaEquiv M (siteRay j), q) := rfl

/-- The retention window of the record is `1/(6κ)`. -/
theorem siteRayRecord_window (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) :
    (siteRayRecord J μ g j hf hc hq hφ).window = 1 / 6 / rateAt g 1 hf q.2 := by
  show 2 / 3 / rateAt g 1 hf q.2 - 1 / (2 * rateAt g 1 hf q.2) = 1 / 6 / rateAt g 1 hf q.2
  rw [show 1 / (2 * rateAt g 1 hf q.2) = 1 / 2 / rateAt g 1 hf q.2 by rw [div_div], ← sub_div]
  norm_num

/-- ★★ **The retention window is not zero.** -/
theorem siteRayRecord_window_pos (hc : ContDiff ℝ ∞ f) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) : 0 < (siteRayRecord J μ g j hf hc hq hφ).window := by
  rw [siteRayRecord_window]
  exact div_pos (by norm_num) (rateAt_pos_of_mem_recordFibres J μ g hf hφ)

/-- ★★★ **On a record fibre the carrier on another site reads `false`** from the start to the end
of the other carrier's window, `[0, 2/(3κ)]`. -/
theorem diracPointerFlow_not_displayed_of_mem_recordFibres (hc : ContDiff ℝ ∞ f)
    {k : ZMod (M + 1)} (hk : j ≠ k) {q : KTorus} (hq : q ∈ readyArc 2)
    (hφ : q.2 ∈ recordFibres M J μ g hf) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 2 / 3 / rateAt g 1 hf q.2) :
    diracDisplayed M
      (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)) = false := by
  have hκ := rateAt_pos_of_mem_recordFibres J μ g hf hφ
  have hH := norm_diracPointerH_lt_of_mem_recordFibres J μ g j hf hφ
  refine diracPointerFlow_siteRay_of_ne_not_displayed J μ g j hf hc hk hq ?_ ht0 ht
  rw [abs_of_pos hκ]
  have hκ0 : rateAt g 1 hf q.2 ≠ 0 := hκ.ne'
  have e : rateAt g 1 hf q.2
        * (‖diracPointerH J μ g j hf q.2‖ * (2 / 3 / rateAt g 1 hf q.2) ^ 2)
      = 4 * ‖diracPointerH J μ g j hf q.2‖ / (9 * rateAt g 1 hf q.2) := by
    field_simp
    ring
  rw [e, div_lt_iff₀ (mul_pos (by norm_num) hκ)]
  linarith

/-- ★★ **The carrier on another site completes no write of `true`** by the end of the other
carrier's window. -/
theorem not_isRecordWrite_siteRay_of_ne (hc : ContDiff ℝ ∞ f) {k : ZMod (M + 1)} (hk : j ≠ k)
    {q : KTorus} (hq : q ∈ readyArc 2) (hφ : q.2 ∈ recordFibres M J μ g hf) {τ₀ τ₁ w : ℝ}
    (hτ₁ : τ₁ ≤ 2 / 3 / rateAt g 1 hf q.2) :
    ¬ IsRecordWrite
      (fun t => diracDisplayed M
        (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)))
      0 τ₀ τ₁ w true :=
  not_isRecordWrite_of_forall_ne hτ₁ fun t ht0 ht => by
    show diracDisplayed M
      (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)) ≠ true
    rw [diracPointerFlow_not_displayed_of_mem_recordFibres J μ g j hf hc hk hq hφ ht0 ht]
    exact Bool.false_ne_true

/-! ### The milestone -/

/-- ★★★ **M2 on a record fibre: a record generated by the Hamiltonian flow.** For a smooth profile,
a ready pointer, a fibre `θ₂` in `recordFibres` with rate `κ`, and a site `k` other than the
detector's site `j`, the four statements of the milestone and its exception:

1. *displacement* — the carrier on site `j` has turned the pointer by at least `1/3` at `1/(2κ)`
   and by at most `2/3` at `2/(3κ)`;
2. *threshold, held* — its readout is `true` throughout `[1/(2κ), 2/(3κ)]`;
3. *the outcome is fixed by the carrier* — the readout of the carrier on site `k` is `false`
   throughout `[0, 2/(3κ)]`;
4. *the record* — the readout history of `diracPointerFlow` is a write of `true` with a window that
   is not zero;
5. *not universal* — for every horizon `T` the slow fibres have positive measure, and on them no
   record is completed by `T`, whatever the carrier. -/
theorem diracPointer_record (hc : ContDiff ℝ ∞ f) {k : ZMod (M + 1)} (hk : j ≠ k) {q : KTorus}
    (hq : q ∈ readyArc 2) (hφ : q.2 ∈ recordFibres M J μ g hf) :
    (1 / 3 ≤ diracPointerShift J μ g j hf q.2 (siteRay j) (1 / (2 * rateAt g 1 hf q.2))
        ∧ diracPointerShift J μ g j hf q.2 (siteRay j) (2 / 3 / rateAt g 1 hf q.2) ≤ 2 / 3)
      ∧ (∀ t, 1 / (2 * rateAt g 1 hf q.2) ≤ t → t ≤ 2 / 3 / rateAt g 1 hf q.2 →
          diracDisplayed M
            (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay j), q)) = true)
      ∧ (∀ t, 0 ≤ t → t ≤ 2 / 3 / rateAt g 1 hf q.2 →
          diracDisplayed M
            (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay k), q)) = false)
      ∧ (IsRecordWrite
            (fun t => diracDisplayed M
              (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M (siteRay j), q)))
            0 (1 / 6 / rateAt g 1 hf q.2) (1 / (2 * rateAt g 1 hf q.2))
            (2 / 3 / rateAt g 1 hf q.2 - 1 / (2 * rateAt g 1 hf q.2)) true
          ∧ 0 < 2 / 3 / rateAt g 1 hf q.2 - 1 / (2 * rateAt g 1 hf q.2))
      ∧ ∀ T : ℝ, 0 < volume (slowFibres g hf T)
          ∧ ∀ (q' : KTorus) (p : GenArena (ZMod (M + 1) × Fin 2)) (τ₀ τ₁ w : ℝ),
              q' ∈ readyArc 2 → q'.2 ∈ slowFibres g hf T → τ₁ ≤ T →
              ¬ IsRecordWrite
                (fun t => diracDisplayed M
                  (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q')))
                0 τ₀ τ₁ w true := by
  have hκ := rateAt_pos_of_mem_recordFibres J μ g hf hφ
  have h₁ := third_le_diracPointerShift_siteRay J μ g j hf hφ
  have h₂ := diracPointerShift_div_rateAt_le J μ g j hf hκ (siteRay j)
    (c := 2 / 3) (by norm_num)
  have hw := siteRayRecord_window_pos J μ g j hf hc hq hφ
  refine ⟨⟨h₁, h₂⟩, fun t ht₁ ht₂ =>
      diracPointerFlow_displayed_of_mono J μ g j hf hc hq hκ.le _ h₁ h₂ ht₁ ht₂,
    fun t ht0 ht =>
      diracPointerFlow_not_displayed_of_mem_recordFibres J μ g j hf hc hk hq hφ ht0 ht,
    ⟨isRecordWrite_siteRay J μ g j hf hc hq hφ, hw⟩, fun T =>
      ⟨volume_slowFibres_pos g hf (hc.of_le (by simp)) T, fun q' p τ₀ τ₁ w hq' hs hτ₁ =>
        not_isRecordWrite_of_mem_slowFibres J μ g j hf hc hq' hs p hτ₁⟩⟩

end Arena

/-! ### The record fibres are not empty: the profile `trainF` -/

section Check

variable (M : ℕ) (J μ : ℝ)

/-- On the fibre `θ₂ = 0` of the profile `trainF` the pointer's rate is `2g`. -/
theorem rateAt_trainF_zero (g : ℝ) :
    rateAt g 1 trainF_periodic (0 : AddCircle (1 : ℝ)) = 2 * g := by
  rw [rateAt_one, trainF_deriv_lift_zero]
  ring

/-- **The fibre `θ₂ = 0` of the profile `trainF` is a record fibre** for every coupling with
`4 ‖H_D‖ < 3 g`. -/
theorem zero_mem_recordFibres_trainF {g : ℝ} (hg : 4 * ‖diracHam (L := M + 1) J μ‖ < 3 * g) :
    (0 : AddCircle (1 : ℝ)) ∈ recordFibres M J μ g trainF_periodic := by
  show 8 * (‖diracHam (L := M + 1) J μ‖ + |g * trainF_periodic.lift (0 : AddCircle (1 : ℝ))|)
    < 3 * rateAt g 1 trainF_periodic (0 : AddCircle (1 : ℝ))
  rw [rateAt_trainF_zero, trainF_lift_zero, mul_zero, abs_zero, add_zero]
  linarith

/-- ★★★ **The record fibres have positive measure** for the profile `trainF`: they are open and
contain `θ₂ = 0`. -/
theorem volume_recordFibres_trainF_pos {g : ℝ}
    (hg : 4 * ‖diracHam (L := M + 1) J μ‖ < 3 * g) :
    0 < volume (recordFibres M J μ g trainF_periodic) :=
  (isOpen_recordFibres J μ g trainF_periodic (contDiff_trainF.of_le (by simp))).measure_pos
    volume ⟨0, zero_mem_recordFibres_trainF M J μ hg⟩

/-- ★★ **For every ring and every `J`, `μ` there is a coupling** at which the record fibres have
positive measure. -/
theorem exists_volume_recordFibres_pos :
    ∃ g : ℝ, 0 < volume (recordFibres M J μ g trainF_periodic) :=
  ⟨2 * ‖diracHam (L := M + 1) J μ‖ + 1, volume_recordFibres_trainF_pos M J μ
    (by linarith [norm_nonneg (diracHam (L := M + 1) J μ)])⟩

end Check

/-! ### The two-mode packet on the fibre `θ₂ = 0` -/

section TwoMode

/-- The closed form of #351 with `sin ≤ 1`. -/
theorem diracPointerShift_twoMode_zero_le {g : ℝ} (hg : 0 ≤ g) (t : ℝ) :
    diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay t
      ≤ g * (116 * t + 48) / 696 := by
  rw [diracPointerShift_twoMode_zero]
  have h : g * (116 * t + 48 * Real.sin (2 * t)) ≤ g * (116 * t + 48) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.sin_le_one (2 * t)]) hg
  linarith

/-- The closed form of #351 with `−1 ≤ sin`. -/
theorem le_diracPointerShift_twoMode_zero {g : ℝ} (hg : 0 ≤ g) (t : ℝ) :
    g * (116 * t - 48) / 696
      ≤ diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay t := by
  rw [diracPointerShift_twoMode_zero]
  have h : g * (116 * t - 48) ≤ g * (116 * t + 48 * Real.sin (2 * t)) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_sin (2 * t)]) hg
  linarith

/-- ★★★ **The two-mode packet writes `true`**, on the fibre `θ₂ = 0` of the profile `trainF`, for
every coupling `0 < g ≤ 29/12` and every ready pointer: along the Hamiltonian flow the readout is
not `true` before `(29 − 12g)/(29g)` and is `true` throughout
`[(58 + 12g)/(29g), (116 − 12g)/(29g)]`. -/
theorem isRecordWrite_twoMode {g : ℝ} (hg : 0 < g) (hg' : g ≤ 29 / 12) {θ : AddCircle (1 : ℝ)}
    (hθ : ((θ, 0) : KTorus) ∈ readyArc 2) :
    IsRecordWrite
      (fun t => diracDisplayed 11
        (diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF t
          (diracArenaEquiv 11 twoModeRay, ((θ, 0) : KTorus))))
      0 ((29 - 12 * g) / (29 * g)) ((58 + 12 * g) / (29 * g))
      ((116 - 12 * g) / (29 * g) - (58 + 12 * g) / (29 * g)) true := by
  have hg0 : g ≠ 0 := hg.ne'
  have h29 : (0 : ℝ) ≤ 29 * g := by positivity
  have hκ : 0 ≤ rateAt g 1 trainF_periodic ((θ, 0) : KTorus).2 := by
    show 0 ≤ rateAt g 1 trainF_periodic (0 : AddCircle (1 : ℝ))
    rw [rateAt_trainF_zero]
    linarith
  refine isRecordWrite_diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF hθ hκ
    twoModeRay (div_nonneg (by linarith) h29)
    (div_le_div_of_nonneg_right (by linarith) h29)
    (div_le_div_of_nonneg_right (by linarith) h29) ?_ ?_ ?_
  · refine (diracPointerShift_twoMode_zero_le hg.le _).trans_eq ?_
    field_simp
    ring
  · refine Eq.trans_le ?_ (le_diracPointerShift_twoMode_zero hg.le _)
    field_simp
    ring
  · refine (diracPointerShift_twoMode_zero_le hg.le _).trans_eq ?_
    field_simp
    ring

/-- ★★★ **The two-mode record as an actual occurrence** on the shared arena, its evolution the
Hamiltonian flow. -/
noncomputable def twoModeRecord {g : ℝ} (hg : 0 < g) (hg' : g ≤ 29 / 12)
    {θ : AddCircle (1 : ℝ)} (hθ : ((θ, 0) : KTorus) ∈ readyArc 2) :
    ActualOccurrence (KSigma (2 * 11 + 1 + 1)) Bool (11 + 1) :=
  diracPointerRecord (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF hθ
    (show 0 ≤ rateAt g 1 trainF_periodic (0 : AddCircle (1 : ℝ)) by
      rw [rateAt_trainF_zero]
      linarith)
    twoModeRay (isRecordWrite_twoMode hg hg' hθ).start_le (isRecordWrite_twoMode hg hg' hθ).interval
    (sub_nonneg.1 (isRecordWrite_twoMode hg hg' hθ).window_nonneg)
    (by
      have hg0 : g ≠ 0 := hg.ne'
      refine (diracPointerShift_twoMode_zero_le hg.le _).trans_eq ?_
      field_simp
      ring)
    (by
      have hg0 : g ≠ 0 := hg.ne'
      refine Eq.trans_le ?_ (le_diracPointerShift_twoMode_zero hg.le _)
      field_simp
      ring)
    (by
      have hg0 : g ≠ 0 := hg.ne'
      refine (diracPointerShift_twoMode_zero_le hg.le _).trans_eq ?_
      field_simp
      ring)

theorem twoModeRecord_evolve {g : ℝ} (hg : 0 < g) (hg' : g ≤ 29 / 12) {θ : AddCircle (1 : ℝ)}
    (hθ : ((θ, 0) : KTorus) ∈ readyArc 2) :
    (twoModeRecord hg hg' hθ).evolve
      = diracPointerEvolve (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF := rfl

/-- The retention window of the two-mode record is `(58 − 24g)/(29g)`: positive for `g < 29/12`. -/
theorem twoModeRecord_window {g : ℝ} (hg : 0 < g) (hg' : g ≤ 29 / 12) {θ : AddCircle (1 : ℝ)}
    (hθ : ((θ, 0) : KTorus) ∈ readyArc 2) :
    (twoModeRecord hg hg' hθ).window = (58 - 24 * g) / (29 * g) := by
  show (116 - 12 * g) / (29 * g) - (58 + 12 * g) / (29 * g) = (58 - 24 * g) / (29 * g)
  rw [← sub_div]
  congr 1
  ring

/-- ★★★ **The two-mode record does not last.** At some time after the end of the window and no
later than `7/g` the pointer pair of the flow is exactly its ready value, and the readout is
`false`: the pointer has gone once round. Retention is an interval, not permanence. -/
theorem twoMode_record_erased {g : ℝ} (hg : 0 < g) (hg' : g ≤ 29 / 12) {θ : AddCircle (1 : ℝ)}
    (hθ : ((θ, 0) : KTorus) ∈ readyArc 2) :
    ∃ s : ℝ, (116 - 12 * g) / (29 * g) < s ∧ s ≤ 7 / g
      ∧ (diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF s
          (diracArenaEquiv 11 twoModeRay, ((θ, 0) : KTorus))).2 = (θ, 0)
      ∧ diracDisplayed 11 (diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF s
          (diracArenaEquiv 11 twoModeRay, ((θ, 0) : KTorus))) = false := by
  have hg0 : g ≠ 0 := hg.ne'
  have hκ : 0 ≤ rateAt g 1 trainF_periodic (0 : AddCircle (1 : ℝ)) := by
    rw [rateAt_trainF_zero]
    linarith
  have h7 : 1 ≤ diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay (7 / g) := by
    refine le_trans ?_ (le_diracPointerShift_twoMode_zero hg.le _)
    have e : g * (116 * (7 / g) - 48) / 696 = (812 - 48 * g) / 696 := by
      field_simp
      ring
    rw [e]
    linarith
  obtain ⟨s, hs, hs1, hsq⟩ := exists_diracPointerFlow_snd_eq (M := 11) 4 3 g 0 trainF_periodic
    contDiff_trainF twoModeRay ((θ, 0) : KTorus) (div_nonneg (by norm_num) hg.le) h7
  have hs1' : diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay s = 1 := hs1
  refine ⟨s, ?_, hs.2, hsq, ?_⟩
  · by_contra hle
    have hmono := diracPointerShift_mono (M := 11) 4 3 g 0 trainF_periodic hκ twoModeRay
      (not_lt.mp hle)
    have hend : diracPointerShift (M := 11) 4 3 g 0 trainF_periodic 0 twoModeRay
        ((116 - 12 * g) / (29 * g)) ≤ 2 / 3 := by
      refine (diracPointerShift_twoMode_zero_le hg.le _).trans_eq ?_
      field_simp
      ring
    linarith
  · refine diracDisplayed_eq_false_of_ready ?_
    show (diracPointerFlow (M := 11) 4 3 g 0 trainF_periodic contDiff_trainF s
      (diracArenaEquiv 11 twoModeRay, ((θ, 0) : KTorus))).2 ∈ readyArc 2
    rw [hsq]
    exact hθ

end TwoMode

end CSD.RecordLayer

end
