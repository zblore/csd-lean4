/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedArrival
public import CsdLean4.RecordLayer.TorusArrival

/-!
# The arrival of the released return carrier as a record, with its control

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4, R1 to R4;
route (γ3c) of the task plans).

The arena of `RecordLayer/UnifiedReleasedDetector.lean` (the earlier carriers, the event's
pointer, the released return carrier, a detector on it) is given a tick readout, and the
bounds of `RecordLayer/UnifiedReleasedArrival.lean` become counts of the detector's pointer:

* `stepArenaDynamics`, `stepPointer`, `stepArenaReadout` — the one-pointer arena with one more
  pointer as a dynamics with `μ_FS ⊗ vol ⊗ vol`, and the tick readout of its two pointers;
* `returnDetectorShift_zero`, `continuous_returnDetectorShift`,
  `monotoneOn_returnDetectorShift`, `returnDetectorShift_le`,
  `returnDetectorShift_eq_zero_of_obs_eq_zero`;
* `releasedDetectorReadout`, ★★ `released_detector_isTickCount` — the count of the detector's
  pointer along the released flow;
* ★★★ `released_detector_arrival_records` — **"the detector has counted `0` at `t₁`" and "the
  detector has counted `1` at `t`" are a record history of the run's start**, after a
  meeting;
* ★★★ `released_detector_idle_record` — **no meeting: "the detector has counted `0` at `t`"
  is a recorded fact of the run's start**, for every `t` up to which the event's occupancy
  is `0`.

## Honest scope

⚠️ **The occupancy bounds are hypotheses**, those of UD-274 and UD-276, and the three
threshold inequalities `ρ ε t₁ ≤ 1/6`, `1/3 ≤ ρ q' (t − u₂)`, `ρ t ≤ 2/3` are not shown to be
met by any carriers. An instance is owed.

⚠️ **The event's pointer is in the readout but its count is not read here.** The history
holds the detector's two counts only; the meeting's own record in the same history is not
stated.

⚠️ **Counts from the start, not a time of arrival.** Between `t₁` and `t` nothing is said.

⚠️ **On the fibres where the detector's profile vanishes**, a null set. **The constant `c`**
still stands for the profile of the pointer that carries the release. **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-13, UA-20,
UA-22, UO-26, UD-242, UD-275, UD-276, UD-277; §9.4);
`specs/unified-records-spacetime-task-plans.md` (§9, route (γ3c));
`RecordLayer/UnifiedReleasedDetector.lean` (`hamiltonianFlow_released_detector`);
`RecordLayer/UnifiedReleasedArrival.lean` (`returnDetectorShift_le_of_early`,
`le_returnDetectorShift_of_dwell`); `RecordLayer/TorusArrival.lean` (`arenaDynamics`,
`arenaReadout`, `card_tickIndices_eq_zero_of_ready`, `graphDetector_arrival_records`);
`RecordLayer/TickCountLaw.lean` (`isTickCount_pointer`); `LF4/PointerStep.lean`
(`map_hamiltonianFlow_stepEnergy`); `RecordLayer/UnifiedRecordHistoryBridge.lean`
(`TickReadout`, `mem_compatibleSet_startFacts`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Projectivization Matrix.UnitaryGroup MeasureTheory
open NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The arena with one more pointer as a dynamics with a tick readout -/

section Arena

variable {N : ℕ} {h : ℝ → ℝ}

set_option synthInstance.maxSize 1024 in
/-- **The one-pointer arena with one more pointer as a `ConstraintDynamics`**: the flow of a
step energy, with the measure `μ_FS ⊗ vol ⊗ vol`. -/
def stepArenaDynamics {H G : KSigma (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ G) (hh : Function.Periodic h 1)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) :
    ConstraintDynamics (KSigma (N + 1) × KTorus) where
  muL := ⟨(kMuL p₀).prod (volume : Measure KTorus), inferInstance⟩
  flow := (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
    (contMDiff_stepEnergy hH hG hh hch)
  measurable_flow t := ((stepForm_isSymplectic (arenaForm_isSymplectic N)).continuous_hamiltonianFlow
    (contMDiff_stepEnergy hH hG hh hch) t).measurable
  flow_zero x :=
    integralFlow_zero ((stepForm_isSymplectic
      (arenaForm_isSymplectic N)).contMDiff_hamiltonianVectorField_tangent
        (contMDiff_stepEnergy hH hG hh hch)) x
  flow_add s t x :=
    integralFlow_add ((stepForm_isSymplectic
      (arenaForm_isSymplectic N)).contMDiff_hamiltonianVectorField_tangent
        (contMDiff_stepEnergy hH hG hh hch)) s t x
  flow_preserves t :=
    ⟨((stepForm_isSymplectic (arenaForm_isSymplectic N)).continuous_hamiltonianFlow
        (contMDiff_stepEnergy hH hG hh hch) t).measurable,
      map_hamiltonianFlow_stepEnergy (arenaForm_isSymplectic N) hH hG hh hch (kMuL p₀) t
        fun _ => kMuL_map_hamiltonianFlow N p₀ _ t⟩

/-- **The two pointers**: `false` the arena's own, `true` the one the step adds. -/
def stepPointer (i : Bool) (x : KSigma (N + 1) × KTorus) : KTorus :=
  bif i then x.2 else x.1.2

theorem continuous_stepPointer : ∀ i : Bool, Continuous (stepPointer (N := N) i)
  | false => continuous_snd.comp continuous_fst
  | true => continuous_snd

set_option synthInstance.maxSize 1024 in
/-- **The tick readout of the two pointers**: each rests when its first angle is in
`readyArc 2` and displays when it is in `displayArc`. -/
def stepArenaReadout {H G : KSigma (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ G) (hh : Function.Periodic h 1)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) :
    TickReadout (stepArenaDynamics hH hG hh hch p₀) Bool where
  rest i := stepPointer i ⁻¹' readyArc 2
  disp i := stepPointer i ⁻¹' displayArc
  continuous_flow :=
    continuous_integralFlow ((stepForm_isSymplectic
      (arenaForm_isSymplectic N)).contMDiff_hamiltonianVectorField_tangent
        (contMDiff_stepEnergy hH hG hh hch))
  rest_sigmaClosed i := isSigmaClosed_readyArc.preimage (continuous_stepPointer i)
  disp_sigmaClosed i := isSigmaClosed_displayArc.preimage (continuous_stepPointer i)
  disjoint _ := readyArc_disjoint_displayArc.preimage _

end Arena

/-! ### The detector's displacement as a function of the flow time -/

section Shift

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ}

/-- At the flow time `0` the detector's pointer has not moved. -/
theorem returnDetectorShift_zero (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (b : ℝ → ℝ) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ)
    (φ χ₂ : AddCircle (1 : ℝ)) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ 0 = 0 := by
  unfold returnDetectorShift
  rw [intervalIntegral.integral_same, mul_zero]

/-- The detector's displacement is continuous in the flow time. -/
theorem continuous_returnDetectorShift (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ)
    (a₀ : ℝ) (φ χ₂ : AddCircle (1 : ℝ)) :
    Continuous fun t : ℝ => returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t := by
  have he : (fun t : ℝ => returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t)
      = fun t => -2 * hh.deriv_periodic.lift χ₂ * ∫ u in (0 : ℝ)..t,
          arenaObs Q (arenaKick (idxFreeU hHR (returnClock hHa hP hf b c pa a₀ φ u)) r) :=
    funext fun t => returnDetectorShift_eq hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
  rw [he]
  exact continuous_const.mul (intervalIntegral.continuous_primitive (μ := volume)
    (fun x y => (continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀
      φ).intervalIntegrable x y) 0)

/-- With a rate `ρ ≥ 0` and `⟨Q⟩ ≥ 0` at every ray, the detector's pointer never turns
back. -/
theorem monotoneOn_returnDetectorShift (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (c : ℝ) {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) (T : ℝ) :
    MonotoneOn (fun t : ℝ => returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t)
      (Icc 0 T) := by
  intro s _ t _ hst
  have hc := continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s t)
  have hnn : 0 ≤ ∫ u in s..t,
      arenaObs Q (arenaKick (idxFreeU hHR (returnClock hHa hP hf b c pa a₀ φ u)) r) :=
    intervalIntegral.integral_nonneg hst fun _ _ => hQ0 _
  show returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ s
    ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
  rw [returnDetectorShift_eq, returnDetectorShift_eq]
  exact mul_le_mul_of_nonneg_left (by linarith) hρ

/-- With a rate `ρ ≥ 0` and `⟨Q⟩ ≤ 1` at every ray, the displacement is at most `ρ t`. -/
theorem returnDetectorShift_le (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hbc : Continuous b) (c : ℝ) {Q : Matrix κ κ ℂ} (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1)
    (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    {χ₂ : AddCircle (1 : ℝ)} (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ₂) {t : ℝ} (ht : 0 ≤ t) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t
      ≤ -2 * hh.deriv_periodic.lift χ₂ * t := by
  rw [returnDetectorShift_eq]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  have a := intervalIntegral.integral_mono_on ht
    ((continuous_arenaObs_returnClock hHa hP hHR hf hbc c Q pa r a₀ φ).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun _ _ => hQ1 _
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at a
  exact a

/-- **No meeting: the detector's pointer has not moved.** On any fibre, with the window shut
at the event pointer's start and `⟨Q⟩ = 0` at the prepared ray: if the event's occupancy is
`0` up to `t`, the detector's displacement at `t` is `0`. -/
theorem returnDetectorShift_eq_zero_of_obs_eq_zero (hHa : Ha.IsHermitian)
    (hP : P.IsHermitian) (hHR : HR.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (c : ℝ) {Q : Matrix κ κ ℂ} (pa : GenArena ι)
    {r : GenArena κ} (hQr : arenaObs Q r = 0) {a₀ : ℝ} (hba : b a₀ = 0)
    (φ χ₂ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) = 0) :
    returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ₂ t = 0 := by
  unfold returnDetectorShift
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
    rw [Set.uIcc_of_le ht] at hu
    show -2 * arenaObs Q (arenaKick (idxFreeU hHR
      (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r) = 0
    rw [releasedClock_eq_zero_of_obs_eq_zero hHa hP hf φ c hba hu.1
      (fun s hs hsu => hz s hs (hsu.trans hu.2)), idxFreeU_zero, arenaKick_one, hQr,
      mul_zero], intervalIntegral.integral_zero, mul_zero]

end Shift

/-! ### The detector's counts -/

section Record

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

/-- **The tick readout of the arena with the event's pointer, the released return carrier and
the detector**: pointer `false` is the event's, pointer `true` the detector's. -/
def releasedDetectorReadout (Ha P : Matrix ι ι ℂ) (HR : Matrix κ κ ℂ)
    (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) (hh : Function.Periodic h 1)
    (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b) (hch : ContDiff ℝ ∞ h) (c : ℝ)
    (Q : Matrix κ κ ℂ) (r : GenArena κ) (p₀ : CPN (N + 1)) :
    TickReadout (stepArenaDynamics
      (contMDiff_add_const_smul
        (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
          (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
        (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
          ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c)
      (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞)
        (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))) hh hch p₀) Bool :=
  stepArenaReadout _ _ hh hch p₀

/-- ★★ **The count of the detector's pointer along the released flow.** On a fibre where the
detector's profile vanishes, from a product ray: if the detector's displacement does not
decrease on `[0, T]`, its count at `T` is the number of turns of `tickIndices` for the
displacement at `T`. -/
theorem released_detector_isTickCount (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (χ : KTorus) (h0 : hh.lift χ.2 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hm : MonotoneOn
      (fun t : ℝ => returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t) (Icc 0 T)) :
    IsTickCount {x : KSigma (N + 1) × KTorus | stepPointer true x ∈ readyArc 2}
      {x : KSigma (N + 1) × KTorus | stepPointer true x ∈ displayArc}
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
      (tickIndices (1 / 6) (1 / 3) (rep χ.1)
        (returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 T)).card :=
  isTickCount_pointer (π := stepPointer (N := N) true) (q := χ)
    (D := fun t => returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t) hT
    (continuous_returnDetectorShift hHa hP hHR hf hh hcb.continuous c Q pa r a₀ φ
      χ.2).continuousOn
    hm (returnDetectorShift_zero hHa hP hHR hf hh b c Q pa r a₀ φ χ.2)
    fun t _ _ => by
      rw [hamiltonianFlow_released_detector e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ
        h0 t]
      rfl

set_option synthInstance.maxSize 1024 in
/-- ★★★ **The arrival is recorded.** On a fibre where the detector's profile vanishes and its
rate is `ρ = −2 h'(χ₂) ≥ 0`, from a ready detector pointer and a product ray, with
`0 ≤ ⟨Q⟩ ≤ 1` at every ray, a window with values in `[0, 1]` and `c ≥ 0`. Under the
hypotheses of `returnDetectorShift_le_of_early` at `t₁` and of
`le_returnDetectorShift_of_dwell` at `t`, with `ρ ε t₁ ≤ 1/6`, `1/3 ≤ ρ q' (t − u₂)` and
`ρ t ≤ 2/3`: the start of the run is in the compatible region of the two facts "the detector
has counted `0` at `t₁`" and "the detector has counted `1` at `t`". -/
theorem released_detector_arrival_records (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) {φ : AddCircle (1 : ℝ)}
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift φ) (hb0 : ∀ x, 0 ≤ b x) (hble : ∀ x, b x ≤ 1)
    {c : ℝ} (hc0 : 0 ≤ c) {a₀ lo hi : ℝ} (hb1 : ∀ x, a₀ + lo ≤ x → x ≤ a₀ + hi → b x = 1)
    {Q : Matrix κ κ ℂ} (hQ0 : ∀ p : GenArena κ, 0 ≤ arenaObs Q p)
    (hQ1 : ∀ p : GenArena κ, arenaObs Q p ≤ 1) {pa : GenArena ι} (r : GenArena κ)
    {χ : KTorus} (hχ : χ ∈ readyArc 2) (h0 : hh.lift χ.2 = 0)
    (hρ : 0 ≤ -2 * hh.deriv_periodic.lift χ.2)
    {t₁ τ₁ ε t₂ t₀ u₂ t q q' τ₂ τ₃ : ℝ} (ht₁ : 0 ≤ t₁) (hτ₁ : c * t₁ ≤ τ₁)
    (hε : ∀ τ, 0 ≤ τ → τ ≤ τ₁ → arenaObs Q (arenaKick (idxFreeU hHR τ) r) ≤ ε)
    (h2 : 0 ≤ t₂) (h20 : t₂ ≤ t₀) (h0u : t₀ ≤ u₂) (hut : u₂ ≤ t)
    (hp0 : ∀ s, 0 ≤ s → s ≤ t →
      0 ≤ arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa))
    (hone : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) ≤ 1)
    (hq : ∀ s, t₂ ≤ s → s ≤ t₀ →
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
        [TickReadout.startFact true t₁ 0, TickReadout.startFact true t 1] := by
  have ht : 0 ≤ t := ((h2.trans h20).trans h0u).trans hut
  have hr : rep χ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hχ
  rw [shearWidth_two] at hr
  have hbc : Continuous b := hcb.continuous
  have c0 := released_detector_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0
    ht₁ (monotoneOn_returnDetectorShift hHa hP hHR hf hh hbc c hQ0 pa r a₀ φ hρ t₁)
  have hup1 := returnDetectorShift_le_of_early hHa hP hHR hf hh hbc hb0 hble hc0 Q pa r a₀ φ
    hρ ht₁ hτ₁ hε
  rw [card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  have c1 := released_detector_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0
    ht (monotoneOn_returnDetectorShift hHa hP hHR hf hh hbc c hQ0 pa r a₀ φ hρ t)
  have hlow := le_returnDetectorShift_of_dwell hHa hP hHR hf hh hκ hbc hb0 hble hc0 hb1 hQ0 r
    hρ h2 h20 h0u hut hp0 hone hq hlo hhi hτ₂ hτ₃ hq'
  have hup := returnDetectorShift_le hHa hP hHR hf hh hbc c hQ1 pa r a₀ φ hρ ht
  rw [card_tickIndices_eq_one_of_ready hr.1 hr.2 (by linarith [hr.1])
    (by linarith [hr.2])] at c1
  refine (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r
    p₀).mem_compatibleSet_startFacts [(true, t₁, 0), (true, t, 1)] _ fun r' hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  exacts [c0, c1]

set_option synthInstance.maxSize 1024 in
/-- ★★★ **No meeting, no arrival, as a record.** On a fibre where the detector's profile
vanishes and on any fibre of the event's pointer, from a ready detector pointer, with the
window shut at the event pointer's start and the return carrier prepared with `⟨Q⟩ = 0`: if
the event's occupancy is `0` up to `t`, then "the detector has counted `0` at `t`" is a
recorded fact of the run's start. -/
theorem released_detector_idle_record (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (p₀ : CPN (N + 1)) (c : ℝ) {Q : Matrix κ κ ℂ} (pa : GenArena ι)
    {r : GenArena κ} (hQr : arenaObs Q r = 0) {a₀ : ℝ} (hba : b a₀ = 0)
    (φ : AddCircle (1 : ℝ)) {χ : KTorus} (hχ : χ ∈ readyArc 2) (h0 : hh.lift χ.2 = 0) {t : ℝ}
    (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) = 0) :
    (((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ) :
        KSigma (N + 1) × KTorus)
      ∈ compatibleSet (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r p₀).semantics
        [TickReadout.startFact true t 0] := by
  have hzero : ∀ u, 0 ≤ u → u ≤ t →
      returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 u = 0 := fun u hu hut =>
    returnDetectorShift_eq_zero_of_obs_eq_zero hHa hP hHR hf hh c pa hQr hba φ χ.2 hu
      fun s hs hsu => hz s hs (hsu.trans hut)
  have hr : rep χ.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hχ
  rw [shearWidth_two] at hr
  have c0 := released_detector_isTickCount e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0
    ht (fun a ha b' hb' _ => by
      show returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 a
        ≤ returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 b'
      rw [hzero a ha.1 ha.2, hzero b' hb'.1 hb'.2])
  rw [hzero t ht le_rfl, card_tickIndices_eq_zero_of_ready hr.1 (by linarith [hr.2])] at c0
  refine (releasedDetectorReadout e Ha P HR hf hb hh hc hcb hch c Q r
    p₀).mem_compatibleSet_startFacts [(true, t, 0)] _ fun r' hr' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hr']
  exact c0

end Record

end CSD.RecordLayer

end
