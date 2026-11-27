/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedRecord

/-!
# The meeting's record and the arrival's record in one history

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4, R1 to R3;
route (γ4) of the task plans).

`RecordLayer/UnifiedReleasedRecord.lean` reads the detector's pointer. Here the event's
pointer is read along the same flow, in the same readout, and the two pairs of counts are
put in one record history:

* ★★ `released_event_isTickCount` — the count of the event's pointer along the released flow;
* ★★★ `released_event_records` — "the event's pointer has counted `0` at `s₁`" and "it has
  counted `1` at `tₑ`" are a record history of the run's start;
* ★★★ `released_meeting_arrival_records` — **one history of the start holds four facts: the
  event's pointer `0` at `s₁` and `1` at `tₑ`, the detector `0` at `t₁` and `1` at `t`.**

Nothing orders `tₑ` and `t₁`: the statement covers `tₑ ≤ t₁`, in which the meeting is on
record while the detector still reads `0`.

## Honest scope

⚠️ **All occupancy bounds and all threshold inequalities are hypotheses.** For the event's
pointer: `κ εₑ s₁ ≤ 1/6`, `1/3 ≤ κ q (tₑ − t₂)`, `κ tₑ ≤ 2/3`; for the detector those of
UD-277. No carriers are shown to meet them together. An instance is owed.

⚠️ **Four counts from the start, not two times.** Neither the meeting nor the arrival is
located in time; the interval between them is not a recorded quantity here.

⚠️ **The event's pointer starts ready**: `(a₀, φ) ∈ readyArc 2`. The window `b` is a profile
of the real number `a₀ + Δ`, as in UD-274.

⚠️ **On the fibres where the detector's profile vanishes**, a null set. **The constant `c`**
still stands for the profile of the pointer that carries the release. **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-13, UA-20,
UA-22, UO-26, UD-242, UD-277, UD-278; §9.4);
`specs/unified-records-spacetime-task-plans.md` (§9, route (γ4));
`RecordLayer/UnifiedReleasedRecord.lean` (`releasedDetectorReadout`, `stepPointer`,
`released_detector_arrival_records`); `RecordLayer/UnifiedReleasedDetector.lean`
(`hamiltonianFlow_released_detector`); `RecordLayer/TorusArrival.lean`
(`monotoneOn_idxPointerShift`, `le_idxPointerShift_of_dwell`,
`graphDetector_arrival_records`); `RecordLayer/TickCountLaw.lean` (`isTickCount_pointer`);
`SigmaLayer/RecordedFact.lean` (`mem_compatibleSet`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Projectivization Matrix.UnitaryGroup MeasureTheory
open NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

/-- ★★ **The count of the event's pointer along the released flow.** On a fibre where the
detector's profile vanishes and the event pointer's rate is `κ = −2 f'(φ) ≥ 0`, from a
product ray: with a non-negative occupancy up to `T`, the count of the event's pointer at
`T` is the number of turns of `tickIndices` for its displacement at `T`. -/
theorem released_event_isTickCount (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (c : ℝ) (Q : Matrix κ κ ℂ) {pa : GenArena ι} (r : GenArena κ)
    (a₀ : ℝ) {φ : AddCircle (1 : ℝ)} (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (χ : KTorus)
    (h0 : hh.lift χ.2 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hp0 : ∀ s, 0 ≤ s → s ≤ T →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa)) :
    IsTickCount {x : KSigma (N + 1) × KTorus | stepPointer false x ∈ readyArc 2}
      {x : KSigma (N + 1) × KTorus | stepPointer false x ∈ displayArc}
      (fun s => (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_stepEnergy
          (contMDiff_add_const_smul
            (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
              (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
            (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
              ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c)
          (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞)
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))) hh hch) s
        ((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ)) T
      (tickIndices (1 / 6) (1 / 3) (rep (a₀ : AddCircle (1 : ℝ)))
        (idxPointerShift hHa hP hf φ pa T)).card :=
  isTickCount_pointer (π := stepPointer (N := N) false) (q := ((a₀ : AddCircle (1 : ℝ)), φ))
    (D := fun t => idxPointerShift hHa hP hf φ pa t) hT
    (continuous_idxPointerShift hHa hP hf φ pa).continuousOn
    (monotoneOn_idxPointerShift hHa hP hf hκ hp0) (idxPointerShift_zero hHa hP hf φ pa)
    fun t _ _ => by
      rw [hamiltonianFlow_released_detector e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ
        h0 t]
      rfl

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The meeting is recorded, in the readout that holds the detector.** On a fibre
where the detector's profile vanishes and the event pointer's rate is `κ = −2 f'(φ) ≥ 0`,
from a ready event pointer and a product ray: if the occupancy that drives the event's
pointer is in `[0, 1]` up to `tₑ`, at most `εₑ` up to `s₁ ≤ tₑ` and at least `q` from
`t₂ ≤ tₑ`, with `κ εₑ s₁ ≤ 1/6`, `1/3 ≤ κ q (tₑ − t₂)` and `κ tₑ ≤ 2/3`, then the start of the
run is in the compatible region of "the event's pointer has counted `0` at `s₁`" and "it has
counted `1` at `tₑ`". -/
theorem released_event_records (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) (c : ℝ) (Q : Matrix κ κ ℂ) {pa : GenArena ι}
    (r : GenArena κ) {a₀ : ℝ} {φ : AddCircle (1 : ℝ)}
    (hθ : (((a₀ : AddCircle (1 : ℝ)), φ) : KTorus) ∈ readyArc 2)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (χ : KTorus) (h0 : hh.lift χ.2 = 0)
    {s₁ t₂ tₑ εₑ q : ℝ} (hs₁ : 0 ≤ s₁) (hs : s₁ ≤ tₑ) (h2 : 0 ≤ t₂) (h2e : t₂ ≤ tₑ)
    (hp0 : ∀ s, 0 ≤ s → s ≤ tₑ →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hone : ∀ s, 0 ≤ s → s ≤ tₑ →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hεₑ : ∀ s, 0 ≤ s → s ≤ s₁ →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ εₑ)
    (hq : ∀ s, t₂ ≤ s → s ≤ tₑ →
      q ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hbe : -2 * hf.deriv_periodic.lift φ * (εₑ * s₁) ≤ 1 / 6)
    (hle : 1 / 3 ≤ -2 * hf.deriv_periodic.lift φ * (q * (tₑ - t₂)))
    (hme : -2 * hf.deriv_periodic.lift φ * tₑ ≤ 2 / 3) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r p₀).semantics
        [TickReadout.startFact false s₁ 0, TickReadout.startFact false tₑ 1] := by
  have hte : 0 ≤ tₑ := h2.trans h2e
  have hr : rep (a₀ : AddCircle (1 : ℝ)) ∈ Ioc (0 : ℝ) (shearWidth 2) := hθ
  rw [shearWidth_two] at hr
  have c0 := released_event_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q r a₀ hκ χ h0 hs₁
    (fun s hs0 hss => hp0 s hs0 (hss.trans hs))
  have hup1 := idxPointerShift_le_of_obs_le hHa hP hf hκ hs₁ hεₑ
  rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  have c1 := released_event_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q r a₀ hκ χ h0 hte
    hp0
  have hlow := le_idxPointerShift_of_dwell hHa hP hf hκ h2 h2e hp0 hq
  have hup := idxPointerShift_le_of_le_one hHa hP hf hκ hte hone
  rw [card_tickIndices_eq_one_of_ready hr.1 hr.2 (by linarith [hr.1])
    (by linarith [hr.2])] at c1
  refine (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r
    p₀).mem_compatibleSet_startFacts [(false, s₁, 0), (false, tₑ, 1)] _ fun r' hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  exacts [c0, c1]

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The meeting's record and the arrival's record are one history.** Under the
hypotheses of `released_event_records` (for `s₁`, `tₑ ≤ t`) and of
`released_detector_arrival_records` (for `t₁`, `t`), the start of the run is in the
compatible region of the four facts: the event's pointer has counted `0` at `s₁` and `1` at
`tₑ`; the detector has counted `0` at `t₁` and `1` at `t`. -/
theorem released_meeting_arrival_records (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hb0 : ∀ x, 0 ≤ b x) (hble : ∀ x, b x ≤ 1)
    {c : ℝ} (hc0 : 0 ≤ c) {a₀ lo hi : ℝ} (hb1 : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1)
    (hθ : (((a₀ : AddCircle (1 : ℝ)), φ) : KTorus) ∈ readyArc 2)
    {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1) {pa : GenArena ι} (r : GenArena κ)
    {χ : KTorus} (hχ : χ ∈ readyArc 2) (h0 : hh.lift χ.2 = 0)
    (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2)
    {s₁ tₑ εₑ t₁ τ₁ ε t₂ t₀ u₂ t q q' τ₂ τ₃ : ℝ} (hs₁ : 0 ≤ s₁) (hs : s₁ ≤ tₑ)
    (h2e : t₂ ≤ tₑ) (het : tₑ ≤ t)
    (hεₑ : ∀ s, 0 ≤ s → s ≤ s₁ →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ εₑ)
    (hbe : -2 * hf.deriv_periodic.lift φ * (εₑ * s₁) ≤ 1 / 6)
    (hle : 1 / 3 ≤ -2 * hf.deriv_periodic.lift φ * (q * (tₑ - t₂)))
    (hme : -2 * hf.deriv_periodic.lift φ * tₑ ≤ 2 / 3)
    (ht₁ : 0 ≤ t₁) (hτ₁ : c * t₁ ≤ τ₁)
    (hε : ∀ τ, 0 ≤ τ → τ ≤ τ₁ → arenaObs Q (arenaKick (idxFreeU hHR τ) r) ≤ ε)
    (h2 : 0 ≤ t₂) (h20 : t₂ ≤ t₀) (h0u : t₀ ≤ u₂) (hut : u₂ ≤ t) (hq0 : 0 ≤ q)
    (hp0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hq : ∀ s, t₂ ≤ s → s ≤ t →
      q ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hlo : lo ≤ -2 * hf.deriv_periodic.lift φ * (q * (t₀ - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift φ * t ≤ hi)
    (hτ₂ : τ₂ ≤ c * (u₂ - t₀)) (hτ₃ : c * t ≤ τ₃)
    (hq' : ∀ τ, τ₂ ≤ τ → τ ≤ τ₃ → q' ≤ arenaObs Q (arenaKick (idxFreeU hHR τ) r))
    (hbefore : -2 * hh.deriv_periodic.lift χ.2 * (ε * t₁) ≤ 1 / 6)
    (hlate : 1 / 3 ≤ -2 * hh.deriv_periodic.lift χ.2 * (q' * (t - u₂)))
    (hmax : -2 * hh.deriv_periodic.lift χ.2 * t ≤ 2 / 3) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r p₀).semantics
        [TickReadout.startFact false s₁ 0, TickReadout.startFact false tₑ 1,
          TickReadout.startFact true t₁ 0, TickReadout.startFact true t 1] := by
  have hE := (mem_compatibleSet _ _ _).1 (released_event_records e hHa hP hHR hf hb hh hc hcb
    hch p₀ c Q r hθ hκ χ h0 hs₁ hs h2 h2e (fun s hs0 hse => hp0 s hs0 (hse.trans het))
    (fun s hs0 hse => hone s hs0 (hse.trans het)) hεₑ
    (fun s hs2 hse => hq s hs2 (hse.trans het)) hbe hle hme)
  have hD := (mem_compatibleSet _ _ _).1 (released_detector_arrival_records e hHa hP hHR hf hb
    hh hc hcb hch p₀ hκ hb0 hble hc0 hb1 hQ0 hQ1 r hχ h0 hρ ht₁ hτ₁ hε h2 h20 h0u hut hq0 hp0
    hone hq hlo hhi hτ₂ hτ₃ hq' hbefore hlate hmax)
  rw [mem_compatibleSet]
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact hE _ (by simp)
  · exact hE _ (by simp)
  · exact hD _ (by simp)
  · exact hD _ (by simp)

end CSD.RecordLayer

end
