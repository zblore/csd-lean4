/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedBounds
public import CsdLean4.RecordLayer.ArcWindow
public import CsdLean4.RecordLayer.PacketOccupancy

/-!
# The released return: an instance with numbers

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (γ5d)
of the task plans).

UD-276 to UD-279 give the detector's counts on the released return from bounds on the clock
and on occupancies, all hypotheses. Here the hypotheses are reduced to the two carriers' free
occupancies and to inequalities between numbers, and then met.

* `released_detector_record_zero_of_shift` — one fact, count `0`, from a displacement of at
  most `1/6`;
* ★★★ `released_detector_records_of_occupancy` — **the arrival record from free
  occupancies.** The event carrier's occupancy is at most `ε` up to `s₁` and at least `q` on
  `[s₂, s₃]`; the return carrier's free occupancy of the detector is at most `ε'` on
  `[0, τ₁]` and at least `q'` on `[τ₂, τ₃]`; a window shut on `[a₀, a₀ + δ]` and open on
  `[a₀ + lo, a₀ + hi]`; nine inequalities between the numbers. Then the detector counts `0`
  at `t₁` and `1` at `t`;
* ★★★ `released_detector_idle_record_of_occupancy` — **the control.** If the event's
  occupancy is `0` up to `t` the detector counts `0` at `t`, when the return carrier starts
  with at most `ε'` on the detector and `ρ ε' t ≤ 1/6`;
* ★★★ `released_arrival_instance` — **an instance.** Both carriers are the flat packet of
  UD-245 on its torus (`L = 8M`, `M ≥ 4·10⁶`), each with the region `arrivalBox`; the window
  is `gateWindow (1/6) (1/16000) (9/4000) (4/5)`; `c = 1/160`; the event pointer's rate is
  `1/(400M)` and the detector's `2/(853M)`. The detector counts `0` at the flow time `40M`
  and `1` at `320M`;
* ★★★ `released_idle_instance` — **its control.** The same arena with the event pointer's
  coupling removed (`P = 0`): the detector counts `0` at `320M`.

## Honest scope

⚠️ **The event here is one carrier reaching a region**, the arrival of UD-245. It is not the
meeting of two carriers of UD-261.

⚠️ **The event's pointer is a gate and is not read.** Its displacement at `320M` is at most
`4/5` of a turn and its count is not stated. The four-fact history of UD-278 is not
instantiated.

⚠️ **One fibre.** The event pointer's second angle and the detector's are `0`, where both
profiles vanish: a null set. The carriers start in a product ray.

⚠️ **The delay is set by supplied numbers**: the constant `c`, the two rates and the window.
No time is located (R5 of §9.4) and no speed is derived (UO-32). The margins are narrow:
`1/3 ≤ 1422/4265` and `568/853 ≤ 2/3`.

⚠️ **The control changes the energy** (`P = 0`), as the control of UD-261 does. All times
are flow times (UA-7).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-26, UO-32, UD-245, UD-276 to UD-282; §9.4); `specs/unified-records-spacetime-task-plans.md`
(§9, route (γ5d)); `RecordLayer/UnifiedReleasedBounds.lean` (`returnClock_le_of_obs_le`,
`returnDetectorShift_le_of_clock`, `le_returnDetectorShift_of_clock`,
`released_detector_records_of_shift`); `RecordLayer/UnifiedReleasedArrival.lean`
(`le_returnClock_of_dwell`); `RecordLayer/ArcWindow.lean` (`gateWindow`);
`RecordLayer/PacketOccupancy.lean` (`arenaObs_arrivalBox_le`, `le_arenaObs_arrivalBox`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Projectivization Matrix.UnitaryGroup MeasureTheory
open NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### From free occupancies to the detector's counts -/

section Occupancy

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

set_option synthInstance.maxSize 1024 in
/-- A detector displacement of at most `1/6` at `t` gives the recorded count `0` at `t`. -/
theorem released_detector_record_zero_of_shift (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hcf : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) (c : ℝ) {Q : Matrix κ κ ℂ}
    (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) {χ : KTorus} (hχ : χ ∈ readyArc 2) (h0 : hh.lift χ.2 = 0)
    (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2) {t : ℝ} (ht : 0 ≤ t)
    (hearly : returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t ≤ 1 / 6) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hcf hcb hch c Q r p₀).semantics
        [TickReadout.startFact true t 0] := by
  have hr : rep χ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hχ
  rw [shearWidth_two] at hr
  have c0 := released_detector_isTickCount e hHa hP hHR hf hb hh hcf hcb hch c Q pa r a₀ φ χ h0
    ht (monotoneOn_returnDetectorShift hHa hP hHR hf hh hcb.continuous c hQ0 pa r a₀ φ hρ t)
  rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  refine (releasedDetectorReadout e Ha P HR hf hb hh hcf hcb hch c Q r
    p₀).mem_compatibleSet_startFacts [(true, t, 0)] _ fun r' hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl
  exact c0

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The arrival record of the released return, from the two carriers' free
occupancies.** On fibres with rates `κ₀ = −2 f'(φ) ≥ 0` and `ρ = −2 h'(χ₂) ≥ 0`, the
detector's profile vanishing, from a ready detector pointer and a product ray. The window
has values in `[0, 1]`, is `0` on `[a₀, a₀ + δ]` and `1` on `[a₀ + lo, a₀ + hi]`; `c ≥ 0`.
The occupancy driving the event's pointer is in `[0, 1]` up to `t`, at most `ε` up to `s₁`
and at least `q` on `[s₂, s₃]`, with `κ₀ ε s₁ ≤ δ`, `lo ≤ κ₀ q (s₃ − s₂)`, `κ₀ t ≤ hi`. The
return carrier's free occupancy of `Q` (in `[0, 1]` at every ray) is at most `ε'` at its own
times in `[0, τ₁]` and at least `q'` in `[τ₂, τ₃]`, with `c t₁ ≤ τ₁`, `τ₂ ≤ c (u₂ − s₃)`,
`c (t − s₁) ≤ τ₃`. If `ρ ε' t₁ ≤ 1/6`, `1/3 ≤ ρ q' (t − u₂)` and
`ρ (ε' t₁ + (t − t₁)) ≤ 2/3`, the start of the run is in the compatible region of "the
detector has counted `0` at `t₁`" and "the detector has counted `1` at `t`". -/
theorem released_detector_records_of_occupancy (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hcf : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) {c : ℝ} (hc0 : 0 ≤ c) {Q : Matrix κ κ ℂ}
    (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p) (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1)
    (pa : GenArena ι) (r : GenArena κ) {a₀ δ lo hi : ℝ} (hb0 : ∀ x, 0 ≤ b x)
    (hb1 : ∀ x, b x ≤ 1) (hbz : ∀ x, a₀ ≤ x → x ≤ a₀ + δ → b x = 0)
    (hbo : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {χ : KTorus} (hχ : χ ∈ readyArc 2)
    (h0 : hh.lift χ.2 = 0) (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2)
    {s₁ s₂ s₃ t₁ u₂ t τ₁ τ₂ τ₃ ε q ε' q' : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hs₂₃ : s₂ ≤ s₃) (hs₃u : s₃ ≤ u₂) (hs₁u : s₁ ≤ u₂) (ht₁ : 0 ≤ t₁) (ht₁t : t₁ ≤ t)
    (hu₂t : u₂ ≤ t)
    (hP0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hP1 : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hPε : ∀ s, 0 ≤ s → s ≤ s₁ →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ ε)
    (hPq : ∀ s, s₂ ≤ s → s ≤ s₃ →
      q ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hδ : -2 * hf.deriv_periodic.lift φ * (ε * s₁) ≤ δ)
    (hlo : lo ≤ -2 * hf.deriv_periodic.lift φ * (q * (s₃ - s₂)))
    (hhi : -2 * hf.deriv_periodic.lift φ * t ≤ hi)
    (hQε : ∀ τ, 0 ≤ τ → τ ≤ τ₁ → arenaObs Q (arenaKick (idxFreeU hHR τ) r) ≤ ε')
    (hQq : ∀ τ, τ₂ ≤ τ → τ ≤ τ₃ → q' ≤ arenaObs Q (arenaKick (idxFreeU hHR τ) r))
    (hτ₁ : c * t₁ ≤ τ₁) (hτ₂ : τ₂ ≤ c * (u₂ - s₃)) (hτ₃ : c * (t - s₁) ≤ τ₃)
    (hearly : -2 * hh.deriv_periodic.lift χ.2 * (ε' * t₁) ≤ 1 / 6)
    (hlate : 1 / 3 ≤ -2 * hh.deriv_periodic.lift χ.2 * (q' * (t - u₂)))
    (hmax : -2 * hh.deriv_periodic.lift χ.2 * (ε' * t₁ + (t - t₁)) ≤ 2 / 3) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hcf hcb hch c Q r p₀).semantics
        [TickReadout.startFact true t₁ 0, TickReadout.startFact true t 1] := by
  have hbc : Continuous b := hcb.continuous
  have ht : 0 ≤ t := ht₁.trans ht₁t
  have hu₂ : 0 ≤ u₂ := hs₁.trans hs₁u
  have hck1 : ∀ u, 0 ≤ u → u ≤ t₁ → 0 ≤ returnClock hHa hP hf b c pa a₀ φ u
      ∧ returnClock hHa hP hf b c pa a₀ φ u ≤ τ₁ := fun u hu0 hu1 =>
    ⟨returnClock_nonneg hHa hP hf hb0 hc0 pa a₀ φ hu0,
      (returnClock_le hHa hP hf hbc hb1 hc0 pa a₀ φ hu0).trans
        ((mul_le_mul_of_nonneg_left hu1 hc0).trans hτ₁)⟩
  have e1 := returnDetectorShift_le_of_clock hHa hP hHR hf hh hbc c hQ1 pa r a₀ φ hρ ht₁
    le_rfl hck1 hQε
  rw [sub_self, add_zero] at e1
  have e2 := returnDetectorShift_le_of_clock hHa hP hHR hf hh hbc c hQ1 pa r a₀ φ hρ ht₁
    ht₁t hck1 hQε
  have hck2 : ∀ u, u₂ ≤ u → u ≤ t → τ₂ ≤ returnClock hHa hP hf b c pa a₀ φ u
      ∧ returnClock hHa hP hf b c pa a₀ φ u ≤ τ₃ := fun u hu2 hut => by
    constructor
    · refine hτ₂.trans ((mul_le_mul_of_nonneg_left (by linarith) hc0).trans
        (le_returnClock_of_dwell hHa hP hf hκ hbc hb0 hc0 hbo hs₂ hs₂₃ (hs₃u.trans hu2)
          (fun s hs hsu => hP0 s hs (hsu.trans hut))
          (fun s hs hsu => hP1 s hs (hsu.trans hut)) hPq hlo
          ((mul_le_mul_of_nonneg_left hut hκ).trans hhi)))
    · refine (returnClock_le_of_obs_le hHa hP hf hκ hbc hb1 hc0 hbz hs₁ (hs₁u.trans hu2)
        (fun s hs hss => hP0 s hs (hss.trans (hs₁u.trans hu₂t))) hPε hδ).trans
        ((mul_le_mul_of_nonneg_left (by linarith) hc0).trans hτ₃)
  have e3 := le_returnDetectorShift_of_clock hHa hP hHR hf hh hbc c hQ0 pa r a₀ φ hρ hu₂
    hu₂t hck2 hQq
  exact released_detector_records_of_shift e hHa hP hHR hf hb hh hcf hcb hch p₀ c hQ0 pa r a₀
    φ hχ h0 hρ ht₁ ht (e1.trans hearly) (hlate.trans e3) (e2.trans hmax)

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The control, with a return carrier that is not exactly off the detector.** With a
window in `[0, 1]` that vanishes at `a₀`, `c ≥ 0` and rates `κ₀, ρ ≥ 0`: if the occupancy
driving the event's pointer is `0` up to `t`, the return carrier's occupancy of `Q` at its
start is at most `ε'`, and `ρ ε' t ≤ 1/6`, the start of the run is in the compatible region
of "the detector has counted `0` at `t`". -/
theorem released_detector_idle_record_of_occupancy (hHa : Ha.IsHermitian)
    (hP : P.IsHermitian) (hHR : HR.IsHermitian) (hf : Function.Periodic f 1)
    (hb : Function.Periodic b 1) (hh : Function.Periodic h 1) (hcf : ContDiff ℝ ∞ f)
    (hcb : ContDiff ℝ ∞ b) (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) {c : ℝ} (hc0 : 0 ≤ c)
    {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1) (pa : GenArena ι) (r : GenArena κ) {a₀ : ℝ}
    (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1) (hba : b a₀ = 0) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) {χ : KTorus} (hχ : χ ∈ readyArc 2)
    (h0 : hh.lift χ.2 = 0) (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2) {t ε' : ℝ}
    (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) = 0)
    (hQε : arenaObs Q (arenaKick (idxFreeU hHR 0) r) ≤ ε')
    (hearly : -2 * hh.deriv_periodic.lift χ.2 * (ε' * t) ≤ 1 / 6) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hcf hcb hch c Q r p₀).semantics
        [TickReadout.startFact true t 0] := by
  have hbc : Continuous b := hcb.continuous
  have hbz : ∀ x, a₀ ≤ x → x ≤ a₀ + 0 → b x = 0 := fun x h1 h2 => by
    have hx : x = a₀ := by linarith
    rw [hx]
    exact hba
  have hck : ∀ u, 0 ≤ u → u ≤ t → 0 ≤ returnClock hHa hP hf b c pa a₀ φ u
      ∧ returnClock hHa hP hf b c pa a₀ φ u ≤ 0 := fun u hu0 hut => by
    refine ⟨returnClock_nonneg hHa hP hf hb0 hc0 pa a₀ φ hu0, ?_⟩
    have hle := returnClock_le_of_obs_le hHa hP hf hκ hbc hb1 hc0 hbz (ε := 0) hu0 le_rfl
      (fun s hs hsu => (hz s hs (hsu.trans hut)).ge)
      (fun s hs hsu => (hz s hs (hsu.trans hut)).le) (by simp)
    rwa [sub_self, mul_zero] at hle
  have e1 := returnDetectorShift_le_of_clock hHa hP hHR hf hh hbc c hQ1 pa r a₀ φ hρ ht
    le_rfl hck (ε := ε') fun τ h0' h1' => by
      have hτ : τ = 0 := le_antisymm h1' h0'
      rw [hτ]
      exact hQε
  rw [sub_self, add_zero] at e1
  exact released_detector_record_zero_of_shift e hHa hP hHR hf hb hh hcf hcb hch p₀ c hQ0 pa r
    a₀ φ hχ h0 hρ ht (e1.trans hearly)

end Occupancy

/-! ### The numbers -/

section Instance

variable {L : ℕ} [NeZero L] {N : ℕ}

/-- The event pointer's rate: for the profile `(1/(800M)) · trainF` on the fibre `0` it is
`1/(400M)`. -/
theorem releasedGateRate_scaledTrainF (M : ℕ) :
    -2 * (scaledTrainF_periodic (1 / (800 * (M : ℝ)))).deriv_periodic.lift
        (0 : AddCircle (1 : ℝ)) = 1 / (400 * M) := by
  rw [scaledTrainF_deriv_lift_zero]
  ring

/-- The detector's rate: for the profile `(1/(853M)) · trainF` on the fibre `0` it is
`2/(853M)`. -/
theorem releasedDetectorRate_scaledTrainF (M : ℕ) :
    -2 * (scaledTrainF_periodic (1 / (853 * (M : ℝ)))).deriv_periodic.lift
        (0 : AddCircle (1 : ℝ)) = 2 / (853 * M) := by
  rw [scaledTrainF_deriv_lift_zero]
  ring

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The released return, with numbers.** Two copies of the torus of UD-245: two
dimensions, `L = 8M` sites per axis with `M ≥ 4·10⁶`, `J = 2`, `μ = 1`, `σ_x`, `σ_y` with
`σ_z`. Each carrier is the flat packet of `400` momenta per axis starting at `(M, 0)`, and
each is read on the region `arrivalBox`. The event's pointer has the profile
`(1/(800M)) · trainF` and starts at the angle `1/6` on the fibre `0`; the window is
`gateWindow (1/6) (1/16000) (9/4000) (4/5)`; `c = 1/160`. The detector's pointer has the
profile `(1/(853M)) · trainF` and starts at `(1/6, 0)`. Then the start of the run is in the
compatible region of "the detector has counted `0` at the flow time `40M`" and "the detector
has counted `1` at `320M`". -/
theorem released_arrival_instance {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (e : ((Fin 2 → ZMod L) × Fin 2) × ((Fin 2 → ZMod L) × Fin 2) ≃ Fin (N + 1))
    (p₀ : CPN (N + 1)) :
    (((idxArenaEquiv e (prodRay (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))),
        ((((1 / 6 : ℝ) : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))), arrivalFibre) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (scaledTrainF_periodic (1 / (800 * (M : ℝ))))
          (gateWindow_periodic (1 / 6) (1 / 16000) (9 / 4000) (4 / 5))
          (scaledTrainF_periodic (1 / (853 * (M : ℝ))))
          (contDiff_scaledTrainF (1 / (800 * (M : ℝ))))
          (contDiff_gateWindow (1 / 6) (1 / 16000) (9 / 4000) (4 / 5))
          (contDiff_scaledTrainF (1 / (853 * (M : ℝ)))) (1 / 160)
          (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)) p₀).semantics
        [TickReadout.startFact true (40 * (M : ℝ)) 0,
          TickReadout.startFact true (320 * (M : ℝ)) 1] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hH := latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1
  have hPh : (siteSetProj (Prod.fst : (Fin 2 → ZMod L) × Fin 2 → Fin 2 → ZMod L)
      (arrivalBox L : Set (Fin 2 → ZMod L))).IsHermitian := siteSetProj_isHermitian _ _
  have hκe := releasedGateRate_scaledTrainF M
  have hρe : -2 * (scaledTrainF_periodic (1 / (853 * (M : ℝ)))).deriv_periodic.lift
      arrivalFibre.2 = 2 / (853 * M) := releasedDetectorRate_scaledTrainF M
  have hfree : ∀ s : ℝ, idxCarrierU hH hPh (scaledTrainF_periodic (1 / (800 * (M : ℝ))))
      (0 : AddCircle (1 : ℝ)) s = idxFreeU hH s :=
    idxCarrierU_of_lift_eq_zero hH hPh _ (scaledTrainF_lift_zero _)
  have k1 : 1 / (400 * (M : ℝ)) * (1 / 10 * (M / 4)) = 1 / 16000 := by
    field_simp
    ring
  have k2 : 1 / (400 * (M : ℝ)) * (9 / 10 * (2 * M - M)) = 9 / 4000 := by
    field_simp
    ring
  have k3 : 1 / (400 * (M : ℝ)) * (320 * M) = 4 / 5 := by
    field_simp
    ring
  have r1 : 2 / (853 * (M : ℝ)) * (1 / 10 * (40 * M)) = 8 / 853 := by
    field_simp
    ring
  have r2 : 2 / (853 * (M : ℝ)) * (9 / 10 * (320 * M - 162 * M)) = 1422 / 4265 := by
    field_simp
    ring
  have r3 : 2 / (853 * (M : ℝ)) * (1 / 10 * (40 * M) + (320 * M - 40 * M)) = 568 / 853 := by
    field_simp
    ring
  refine released_detector_records_of_occupancy e hH hPh hH _ _ _ _ _ _ p₀
    (c := 1 / 160) (by norm_num) (arenaObs_siteSetProj_nonneg _ _)
    (arenaObs_siteSetProj_le_one _ _) _ _ (a₀ := 1 / 6) (δ := 1 / 16000) (lo := 9 / 4000)
    (hi := 4 / 5) (gateWindow_nonneg _ _ _ _) (gateWindow_le_one _ _ _ _)
    (fun x h1 h2 => gateWindow_eq_zero (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h1 h2)
    (fun x h1 h2 => gateWindow_eq_one (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h1 h2)
    (by rw [hκe]; positivity) arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _)
    (by rw [hρe]; positivity)
    (s₁ := (M : ℝ) / 4) (s₂ := (M : ℝ)) (s₃ := 2 * (M : ℝ)) (t₁ := 40 * (M : ℝ))
    (u₂ := 162 * (M : ℝ)) (t := 320 * (M : ℝ)) (τ₁ := (M : ℝ) / 4) (τ₂ := (M : ℝ))
    (τ₃ := 2 * (M : ℝ)) (ε := 1 / 10) (q := 9 / 10) (ε' := 1 / 10) (q' := 9 / 10)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (fun s _ _ => arenaObs_siteSetProj_nonneg _ _ _)
    (fun s _ _ => arenaObs_siteSetProj_le_one _ _ _)
    (fun s hs hs1 => by rw [hfree]; exact arenaObs_arrivalBox_le hL hM hs hs1)
    (fun s hs hs1 => by rw [hfree]; exact le_arenaObs_arrivalBox hL hM hs hs1)
    (by rw [hκe, k1]) (by rw [hκe, k2]) (by rw [hκe, k3])
    (fun τ hτ hτ1 => arenaObs_arrivalBox_le hL hM hτ hτ1)
    (fun τ hτ hτ1 => le_arenaObs_arrivalBox hL hM hτ hτ1)
    (by linarith) (by linarith) (by linarith)
    (by rw [hρe, r1]; norm_num) (by rw [hρe, r2]; norm_num) (by rw [hρe, r3]; norm_num)

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The control of `released_arrival_instance`.** The same carriers, window, constant
and profiles, with the event pointer coupled to nothing (`P = 0`). Then the start of the run
is in the compatible region of "the detector has counted `0` at the flow time `320M`". -/
theorem released_idle_instance {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (e : ((Fin 2 → ZMod L) × Fin 2) × ((Fin 2 → ZMod L) × Fin 2) ≃ Fin (N + 1))
    (p₀ : CPN (N + 1)) :
    (((idxArenaEquiv e (prodRay (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))),
        ((((1 / 6 : ℝ) : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))), arrivalFibre) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (0 : Matrix ((Fin 2 → ZMod L) × Fin 2) ((Fin 2 → ZMod L) × Fin 2) ℂ)
          (latticeDiracHam (L := L) (fun i : Fin 2 => pauli i.castSucc) (pauli 2) 2 1)
          (scaledTrainF_periodic (1 / (800 * (M : ℝ))))
          (gateWindow_periodic (1 / 6) (1 / 16000) (9 / 4000) (4 / 5))
          (scaledTrainF_periodic (1 / (853 * (M : ℝ))))
          (contDiff_scaledTrainF (1 / (800 * (M : ℝ))))
          (contDiff_gateWindow (1 / 6) (1 / 16000) (9 / 4000) (4 / 5))
          (contDiff_scaledTrainF (1 / (853 * (M : ℝ)))) (1 / 160)
          (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM)) p₀).semantics
        [TickReadout.startFact true (320 * (M : ℝ)) 0] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hH := latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1
  have hκe := releasedGateRate_scaledTrainF M
  have hρe : -2 * (scaledTrainF_periodic (1 / (853 * (M : ℝ)))).deriv_periodic.lift
      arrivalFibre.2 = 2 / (853 * M) := releasedDetectorRate_scaledTrainF M
  have r1 : 2 / (853 * (M : ℝ)) * (1 / 10 * (320 * M)) = 64 / 853 := by
    field_simp
    ring
  refine released_detector_idle_record_of_occupancy e hH Matrix.isHermitian_zero hH _ _ _ _ _
    _ p₀ (c := 1 / 160) (by norm_num) (arenaObs_siteSetProj_nonneg _ _)
    (arenaObs_siteSetProj_le_one _ _) _ _ (a₀ := 1 / 6) (gateWindow_nonneg _ _ _ _)
    (gateWindow_le_one _ _ _ _)
    (gateWindow_eq_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
      (by norm_num))
    (by rw [hκe]; positivity) arrivalFibre_mem_readyArc (scaledTrainF_lift_zero _)
    (by rw [hρe]; positivity) (t := 320 * (M : ℝ)) (ε' := 1 / 10) (by linarith)
    (fun s _ _ => arenaObs_zero' _)
    (arenaObs_arrivalBox_le hL hM le_rfl (by positivity))
    (by rw [hρe, r1]; norm_num)

end Instance

end CSD.RecordLayer

end
