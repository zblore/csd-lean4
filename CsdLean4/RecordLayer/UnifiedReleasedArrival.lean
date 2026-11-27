/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedDetector
public import CsdLean4.RecordLayer.UnifiedCompositeCarrier

/-!
# The detector's displacement on the released return carrier: small early, large late

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4, R2 and R3;
route (γ3b) of the task plans).

`RecordLayer/UnifiedReleasedDetector.lean` gives the detector's displacement as its rate
times the accumulated occupancy of `Q` by the return carrier, read at the clock that the
event's pointer sets. Here that displacement is bounded from the two quantum calculations it
is made of, each used as it stands:

* the return carrier's free occupancy `w(τ) = ⟨Q⟩ at exp(−iτH_R) r`, as a function of its own
  time `τ`;
* the occupancy that drives the event's pointer, which fixes the clock (UD-274).

* `returnClock`, `continuous_returnClock`, `returnClock_nonneg`, `returnClock_le`,
  `le_returnClock_of_dwell` — the clock, named, with the bounds of UD-274;
* `returnDetectorShift_eq`, `returnDetectorShift_nonneg` — the displacement as the rate times
  the accumulated occupancy, and its sign;
* ★★ `returnDetectorShift_le_of_early` — **while `c t ≤ τ₁` and `w ≤ ε` on `[0, τ₁]`, the
  displacement is at most `ρ ε t`**, whatever the event's pointer does;
* ★★★ `le_returnDetectorShift_of_dwell` — **after a meeting, the displacement is at least
  `ρ q' (t − u₂)`**: the event's occupancy turns its pointer into the window by `t₀`, the
  clock passes `τ₂` by `u₂`, and `w ≥ q'` on `[τ₂, τ₃]`.

## Honest scope

⚠️ **Both occupancy bounds are hypotheses.** No return carrier is substituted for which
`w ≤ ε` on `[0, τ₁]` and `w ≥ q'` on `[τ₂, τ₃]` hold, and no earlier carrier for which the
event's occupancy bounds hold. An instance is owed.

⚠️ **Bounds for a displacement, not a count.** No readout is put on the detector's torus.

⚠️ **The early bound uses only `κ(t) ≤ c t`**, so it bounds the displacement whether or not
there was a meeting; the sharper control with no meeting is
`hamiltonianFlow_released_detector_idle`.

⚠️ **The late bound loses the time `u₂ − t₂`**: the reading time of the event's pointer and
the travel time `τ₂ / c` at the clock's full rate. Neither is located, only bounded.

⚠️ **`⟨Q⟩ ≥ 0` at every ray** is asked of `Q` (a projection has it). **On the fibres where
the detector's profile vanishes**, as in UD-275. **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-26, UD-274, UD-275, UD-276; §9.4); `specs/unified-records-spacetime-task-plans.md` (§9,
route (γ3b)); `RecordLayer/UnifiedReleasedDetector.lean` (`returnDetectorShift`,
`hamiltonianFlow_released_detector`); `RecordLayer/UnifiedReleasedClock.lean`
(`le_releasedClock_of_dwell`, `releasedClock_le`); `RecordLayer/TorusArrival.lean`
(`le_integral_of_dwell`, `continuous_idxPointerShift`);
`RecordLayer/UnifiedCompositeCarrier.lean` (`continuous_arenaObs_idxFreeU`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The clock, named -/

section Clock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ha P : Matrix ι ι ℂ} {f b : ℝ → ℝ}

/-- **The clock of the released return carrier**: `c ∫₀ᵘ b(a₀ + Δ(v)) dv`, `Δ` the
displacement of the event's pointer. -/
noncomputable def returnClock (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (b : ℝ → ℝ) (c : ℝ) (pa : GenArena ι) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (u : ℝ) : ℝ :=
  c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v)

/-- The clock is continuous in the flow time. -/
theorem continuous_returnClock (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (hbc : Continuous b) (c : ℝ) (pa : GenArena ι) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) : Continuous fun u : ℝ => returnClock hHa hP hf b c pa a₀ φ u := by
  unfold returnClock
  exact continuous_const.mul (intervalIntegral.continuous_primitive (μ := volume)
    (fun x y => (hbc.comp (continuous_const.add
      (continuous_idxPointerShift hHa hP hf φ pa))).intervalIntegrable x y) 0)

/-- A non-negative window and `c ≥ 0`: the clock does not run backwards from `0`. -/
theorem returnClock_nonneg (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (hb0 : ∀ x, 0 ≤ b x) {c : ℝ} (hc : 0 ≤ c) (pa : GenArena ι)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ returnClock hHa hP hf b c pa a₀ φ u :=
  mul_nonneg hc (intervalIntegral.integral_nonneg hu fun _ _ => hb0 _)

/-- A window at most `1`: the clock is at most `c u`. -/
theorem returnClock_le (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (hbc : Continuous b) (hb1 : ∀ x, b x ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (pa : GenArena ι) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    returnClock hHa hP hf b c pa a₀ φ u ≤ c * u :=
  releasedClock_le hHa hP hf φ hbc hb1 hc a₀ pa hu

/-- `le_releasedClock_of_dwell` for the named clock. -/
theorem le_returnClock_of_dwell (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hbc : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    {c : ℝ} (hc : 0 ≤ c) {a₀ lo hi : ℝ} (hb1 : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1)
    {pa : GenArena ι} {t₂ t₀ t q : ℝ} (h2 : 0 ≤ t₂) (h20 : t₂ ≤ t₀) (h0t : t₀ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hq : ∀ s, t₂ ≤ s → s ≤ t₀ →
      q ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hlo : lo ≤ -2 * hf.deriv_periodic.lift φ * (q * (t₀ - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift φ * t ≤ hi) :
    c * (t - t₀) ≤ returnClock hHa hP hf b c pa a₀ φ t :=
  le_releasedClock_of_dwell hHa hP hf hκ hbc hb0 hc hb1 h2 h20 h0t h0 hone hq hlo hhi

end Clock

/-! ### The detector's displacement -/

section Shift

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ}

/-- The return carrier's occupancy of `Q`, read at the clock, is continuous in the flow
time. -/
theorem continuous_arenaObs_returnClock (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hbc : Continuous b) (c : ℝ)
    (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) :
    Continuous fun u : ℝ =>
      arenaObs Q (arenaKick (idxFreeU hHR (returnClock hHa hP hf b c pa a₀ φ u)) r) :=
  (continuous_arenaObs_idxFreeU hHR Q r).comp (continuous_returnClock hHa hP hf hbc c pa a₀ φ)

/-- **The displacement is the detector's rate `−2 h'(χ₂)` times the accumulated occupancy.** -/
theorem returnDetectorShift_eq (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (b : ℝ → ℝ) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ)
    (φ χ₂ : AddCircle (1 : ℝ)) (t : ℝ) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
      = -2 * hh.deriv_periodic.lift χ₂ * ∫ u in (0 : ℝ)..t,
          arenaObs Q (arenaKick (idxFreeU hHR (returnClock hHa hP hf b c pa a₀ φ u)) r) := by
  unfold returnDetectorShift returnClock
  rw [intervalIntegral.integral_const_mul]
  ring

/-- With a rate `ρ ≥ 0` and `⟨Q⟩ ≥ 0` at every ray, the detector's pointer does not turn
back. -/
theorem returnDetectorShift_nonneg (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (b : ℝ → ℝ) (c : ℝ) {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t := by
  rw [returnDetectorShift_eq]
  exact mul_nonneg hρ (intervalIntegral.integral_nonneg ht fun _ _ => hQ0 _)

/-- ★★ **Early: a small displacement.** The window is continuous with values in `[0, 1]`,
`c ≥ 0`, the detector's rate is `ρ = −2 h'(χ₂) ≥ 0`. If the return carrier's free occupancy
of `Q` is at most `ε` at its own times in `[0, τ₁]`, and `c t ≤ τ₁`, the detector's
displacement at `t` is at most `ρ ε t`. Nothing is asked of the event's pointer. -/
theorem returnDetectorShift_le_of_early (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) {t τ₁ ε : ℝ}
    (ht : 0 ≤ t) (hτ : c * t ≤ τ₁)
    (hε : ∀ τ, 0 ≤ τ → τ ≤ τ₁ → arenaObs Q (arenaKick (idxFreeU hHR τ) r) ≤ ε) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
      ≤ -2 * hh.deriv_periodic.lift χ₂ * (ε * t) := by
  rw [returnDetectorShift_eq]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  have a := intervalIntegral.integral_mono_on ht
    ((continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := ε)) fun u hu =>
      hε _ (returnClock_nonneg hHa hP hf hb0 hc pa a₀ φ hu.1)
        ((returnClock_le hHa hP hf hbc hb1 hc pa a₀ φ hu.1).trans
          ((mul_le_mul_of_nonneg_left hu.2 hc).trans hτ))
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at a
  linarith

/-- ★★★ **Late, after a meeting: a large displacement.** The event's pointer has rate
`κ = −2 f'(φ) ≥ 0`; the window is continuous with values in `[0, 1]` and is `1` on
`[a₀ + lo, a₀ + hi]`; `c ≥ 0`; the detector's rate is `ρ = −2 h'(χ₂) ≥ 0` and `⟨Q⟩ ≥ 0` at
every ray. Suppose the event's occupancy is in `[0, 1]` up to `t` and at least `q` on
`[t₂, t₀]`, with `lo ≤ κ q (t₀ − t₂)` and `κ t ≤ hi` (so the clock runs from `t₀`); and the return
carrier's free occupancy of `Q` is at least `q'` at its own times in `[τ₂, τ₃]`, with
`τ₂ ≤ c (u₂ − t₀)` and `c t ≤ τ₃`. Then the detector's displacement at `t` is at least
`ρ q' (t − u₂)`. -/
theorem le_returnDetectorShift_of_dwell (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hbc : Continuous b)
    (hb0 : ∀ x, 0 ≤ b x) (hble : ∀ x, b x ≤ 1) {c : ℝ} (hc : 0 ≤ c) {a₀ lo hi : ℝ}
    (hb1 : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1) {Q : Matrix κ κ ℂ}
    (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p) {pa : GenArena ι} (r : GenArena κ)
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂)
    {t₂ t₀ u₂ t q q' τ₂ τ₃ : ℝ} (h2 : 0 ≤ t₂) (h20 : t₂ ≤ t₀) (h0u : t₀ ≤ u₂) (hut : u₂ ≤ t)
    (h0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hq : ∀ s, t₂ ≤ s → s ≤ t₀ →
      q ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hlo : lo ≤ -2 * hf.deriv_periodic.lift φ * (q * (t₀ - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift φ * t ≤ hi)
    (hτ₂ : τ₂ ≤ c * (u₂ - t₀)) (hτ₃ : c * t ≤ τ₃)
    (hq' : ∀ τ, τ₂ ≤ τ → τ ≤ τ₃ → q' ≤ arenaObs Q (arenaKick (idxFreeU hHR τ) r)) :
    -2 * hh.deriv_periodic.lift χ₂ * (q' * (t - u₂))
      ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t := by
  have hu₂ : 0 ≤ u₂ := (h2.trans h20).trans h0u
  rw [returnDetectorShift_eq]
  refine mul_le_mul_of_nonneg_left (le_integral_of_dwell
    (continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ) hu₂ hut
    (fun _ _ _ => hQ0 _) fun u huu hu => hq' _ ?_ ?_) hρ
  · have hclock := le_returnClock_of_dwell hHa hP hf hκ hbc hb0 hc hb1 (pa := pa) h2 h20
      (h0u.trans huu) (fun s hs hsu => h0 s hs (hsu.trans hu))
      (fun s hs hsu => hone s hs (hsu.trans hu)) hq hlo
      ((mul_le_mul_of_nonneg_left hu hκ).trans hhi)
    have hmono : c * (u₂ - t₀) ≤ c * (u - t₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    linarith
  · exact (returnClock_le hHa hP hf hbc hble hc pa a₀ φ (hu₂.trans huu)).trans
      ((mul_le_mul_of_nonneg_left hu hc).trans hτ₃)

end Shift

end CSD.RecordLayer

end
