/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedClock

/-!
# A detector on the released return carrier

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4, R1 and R4;
route (γ3) of the task plans, first part).

One more pointer is added to the arena of `RecordLayer/UnifiedReleasedReturn.lean` by the
step of `LF4/PointerStep.lean`: a detector coupled, through a profile `h` of its own
conserved angle, to an observable `Q` of the return carrier. On a fibre where `h` vanishes
the carriers and the event's pointer run as before, and the detector's moving angle advances
by

  `h'(χ₂) ∫₀ᵗ (−2⟨Q⟩ at exp(−iκ(u)H_R) r) du`,

`κ` the clock that the event's pointer sets. So the detector accumulates the return
carrier's occupancy of `Q` **read at the released clock**.

* `hamiltonianFlow_stepEnergy_arena_of_lift_eq_zero` — the step over the one-pointer arena
  on a fibre where the new profile vanishes, for any two smooth functions;
* `returnDetectorShift` — the detector's displacement;
* ★★★ `hamiltonianFlow_released_detector` — **the flow of the arena with the event's pointer,
  the released return carrier and the detector, from a product ray**;
* ★★★ `hamiltonianFlow_released_detector_idle` — **no meeting, no arrival**: with the
  event's occupancy `0` up to `t`, the window shut at the event pointer's start, and the
  return carrier prepared with `⟨Q⟩ = 0`, the detector's pointer is at `t` where it started.

## Honest scope

⚠️ **On the fibres where the detector's profile vanishes**, a null set of its conserved
angles. Off them the detector acts back on the return carrier and nothing is given.

⚠️ **The constant `c`** still stands for the profile of the pointer that carries the
release (UA-20, UA-22 (c)); that pointer is not a torus of this arena.

⚠️ **A displacement, not yet a count.** No readout is put on the detector's torus here, so
"the detector has counted `0`" is not yet a recorded fact. The displacement is an integral
of an occupancy; that it reaches a threshold after a meeting is not shown.

⚠️ **`⟨Q⟩ = 0` at the prepared ray** is a hypothesis of the control: the return carrier is
prepared off the detector.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-13, UA-20,
UA-22, UO-26, UD-273, UD-274, UD-275; §9.4); `specs/unified-records-spacetime-task-plans.md`
(§9, route (γ3)); `LF4/PointerStep.lean` (`stepEnergy`, `hamiltonianFlow_stepEnergy`,
`hamiltonianFlow_congr`); `LF4/ControlledStep.lean`
(`hamiltonianFlow_controlledEnergy_of_lift_eq_zero`, the same argument for one energy);
`RecordLayer/UnifiedReleasedReturn.lean` (`hamiltonianFlow_released_return`);
`RecordLayer/UnifiedReleasedClock.lean` (`hamiltonianFlow_released_return_idle`,
`releasedClock_eq_zero_of_obs_eq_zero`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The step on a fibre where the new profile vanishes -/

section Step

variable {N : ℕ} {h : ℝ → ℝ}

/-- **One more pointer on the one-pointer arena, on a fibre where its profile vanishes.** The
arena runs by its own flow of `H`, and the new pointer's moving angle advances by `h'(χ₂)`
times the accumulated `G` along that orbit. -/
theorem hamiltonianFlow_stepEnergy_arena_of_lift_eq_zero {H G : KSigma (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ G) (hh : Function.Periodic h 1)
    (hch : ContDiff ℝ ∞ h) (t : ℝ) (s : KSigma (N + 1)) (χ : KTorus)
    (h0 : hh.lift χ.2 = 0) :
    (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_stepEnergy hH hG hh hch) t (s, χ)
      = ((arenaForm_isSymplectic N).hamiltonianFlow hH t s,
          (χ.1 + ((hh.deriv_periodic.lift χ.2 * ∫ u in (0 : ℝ)..t,
              G ((arenaForm_isSymplectic N).hamiltonianFlow hH u s) : ℝ) :
            AddCircle (1 : ℝ)), χ.2)) := by
  have hbase : ∀ u : ℝ, (arenaForm_isSymplectic N).hamiltonianFlow
      (contMDiff_add_const_smul hH hG (hh.lift χ.2)) u s
      = (arenaForm_isSymplectic N).hamiltonianFlow hH u s := fun u =>
    congrFun (congrFun (hamiltonianFlow_congr (arenaForm_isSymplectic N)
      (by rw [h0, zero_smul, add_zero]) _ hH) u) s
  rw [hamiltonianFlow_stepEnergy (arenaForm_isSymplectic N) hH hG hh hch t s χ, hbase t]
  simp only [hbase]

end Step

/-! ### The detector on the return carrier -/

section Detector

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b h : ℝ → ℝ} {N : ℕ}

/-- **The detector's displacement**: `h'(χ₂)` times the accumulated `−2⟨Q⟩` of the return
carrier, read at the released clock. -/
noncomputable def returnDetectorShift (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (b : ℝ → ℝ) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (χ₂ : AddCircle (1 : ℝ)) (t : ℝ) : ℝ :=
  hh.deriv_periodic.lift χ₂ * ∫ u in (0 : ℝ)..t,
    -2 * arenaObs Q (arenaKick (idxFreeU hHR
      (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r)

variable (e : ι × κ ≃ Fin (N + 1))

/-- ★★★ **The arena with the event's pointer, the released return carrier and a detector on
it.** The detector is coupled through the profile `h` of its conserved angle to the
observable `Q` of the return carrier. On a fibre where `h` vanishes, from a product ray: the
earlier carriers, the event's pointer and the return carrier run as in
`hamiltonianFlow_released_return`, and the detector's moving angle advances by
`returnDetectorShift`. -/
theorem hamiltonianFlow_released_detector (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) (r : GenArena κ)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (χ : KTorus) (h0 : hh.lift χ.2 = 0) (t : ℝ) :
    (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_stepEnergy
          (contMDiff_add_const_smul
            (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
              (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
            (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
              ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c)
          (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞)
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))) hh hch) t
        ((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ)
      = ((idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa)
            (arenaKick (idxFreeU hHR
              (c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hHa hP hf φ pa u))) r)),
          (((a₀ + idxPointerShift hHa hP hf φ pa t : ℝ) : AddCircle (1 : ℝ)), φ)),
        (χ.1 + ((returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t : ℝ) :
          AddCircle (1 : ℝ)), χ.2)) := by
  have hbase := fun u : ℝ =>
    hamiltonianFlow_released_return e hHa hP hHR hf hb hc hcb c pa r a₀ φ u
  have hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞
      (coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
          (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf
        + c • controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
          ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb) :=
    contMDiff_add_const_smul (contMDiff_coupledEnergy _ _ hf hc)
      (contMDiff_controlObs _ hb hcb) c
  have hG : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞
      (sectorEnergy (schrodingerHamiltonian
        (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))) :=
    contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) _)
  refine (hamiltonianFlow_stepEnergy_arena_of_lift_eq_zero hH hG hh hch t _ χ h0).trans ?_
  rw [hbase t]
  simp only [hbase]
  have hint : (∫ u in (0 : ℝ)..t, sectorEnergy (schrodingerHamiltonian
        (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))
      ((idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ u) pa)
          (arenaKick (idxFreeU hHR
            (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r)),
        (((a₀ + idxPointerShift hHa hP hf φ pa u : ℝ) : AddCircle (1 : ℝ)), φ)) :
        KSigma (N + 1)))
      = ∫ u in (0 : ℝ)..t, -2 * arenaObs Q (arenaKick (idxFreeU hHR
          (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r) :=
    intervalIntegral.integral_congr fun u _ => by
      show schrodingerHamiltonian (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q))
          (idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ u) pa)
            (arenaKick (idxFreeU hHR
              (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r)))
        = -2 * arenaObs Q (arenaKick (idxFreeU hHR
            (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r)
      rw [schrodingerHamiltonian_reindex, arenaObs_one_kronecker]
  rw [hint]
  rfl

/-- ★★★ **No meeting, no arrival.** On a fibre where the detector's profile vanishes and on
any fibre of the event's pointer, with the window shut at that pointer's start and the
return carrier prepared with `⟨Q⟩ = 0`: if the observable that the event's pointer reads has
expectation `0` along the earlier carriers' orbit up to `t`, then at `t` the return carrier
is where it was prepared and the detector's pointer is where it started. -/
theorem hamiltonianFlow_released_detector_idle (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b)
    (hch : ContDiff ℝ ∞ h) (c : ℝ) (Q : Matrix κ κ ℂ) (pa : GenArena ι) {r : GenArena κ}
    (hQr : arenaObs Q r = 0) {a₀ : ℝ} (hba : b a₀ = 0) (φ : AddCircle (1 : ℝ)) (χ : KTorus)
    (h0 : hh.lift χ.2 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s, 0 ≤ s → s ≤ t →
      arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa) = 0) :
    (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_stepEnergy
          (contMDiff_add_const_smul
            (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
              (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
            (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
              ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c)
          (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞)
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ Q)))) hh hch) t
        ((idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ)), χ)
      = ((idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa) r),
          ((a₀ : AddCircle (1 : ℝ)), φ)), χ) := by
  have hshift : returnDetectorShift hHa hP hHR hf hh b c Q pa r a₀ φ χ.2 t = 0 := by
    unfold returnDetectorShift
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
      rw [Set.uIcc_of_le ht] at hu
      show -2 * arenaObs Q (arenaKick (idxFreeU hHR
        (c * ∫ v in (0 : ℝ)..u, b (a₀ + idxPointerShift hHa hP hf φ pa v))) r) = 0
      rw [releasedClock_eq_zero_of_obs_eq_zero hHa hP hf φ c hba hu.1
        (fun s hs hsu => hz s hs (hsu.trans hu.2)), idxFreeU_zero, arenaKick_one, hQr,
        mul_zero], intervalIntegral.integral_zero, mul_zero]
  rw [hamiltonianFlow_released_detector e hHa hP hHR hf hb hh hc hcb hch c Q pa r a₀ φ χ h0 t,
    hshift, releasedClock_eq_zero_of_obs_eq_zero hHa hP hf φ c hba ht hz, idxFreeU_zero,
    arenaKick_one, idxPointerShift_eq_zero_of_obs_eq_zero hHa hP hf φ ht hz, add_zero,
    AddCircle.coe_zero, add_zero]

end Detector

end CSD.RecordLayer

end
