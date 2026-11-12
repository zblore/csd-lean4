/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedDepartureArrival

/-!
# A transit, certified by the two pointers' displacements

**Category:** 7-SigmaLayer (the record layer). BACKLOG #373 — the author's programme "From `Σ` to
physical spacetime", obligation UO-16; Remainder (b) of #372 and the Remainder of #365 and #367.

`RecordLayer/UnifiedArrivalRecord.lean` (#365) and `RecordLayer/UnifiedDepartureArrival.lean`
(#367) write a departure record and an arrival record along one orbit. Each is a threshold
crossing of accumulated weight, and a carrier that does not move, with a constant weight in each
half of the ring, satisfies the same conclusions. So those records do not certify a transit. This
module adds a statement, on the same run, that no such carrier satisfies.

**The accumulated occupancy** `crossAccum C φ χ t` is `∫₀ᵗ ⟨P_C⟩` along the carrier of
`regionTwoFlow` started on the crossing packet, on the fibre `(φ, χ)`. The near pointer's moving
angle at the flow time `t` is its start plus `κ₁` times the accumulated occupancy of the near
half, and the far pointer's is its start plus `κ₂` times that of the far half
(`regionTwoFlow_cross_pointers`). So the accumulated occupancies are the two pointers'
displacements over their rates.

**The certificate** (`cross_transit_certificate`). With `T₁ = 625π/3`, `T₂ = 3125π/3`,
`T₃ = 4375π/3`, on the transit fibres:

* over `[0, T₁]` the far half accumulates at most `(1/3) T₁` and the near half at least
  `(2/3) T₁`;
* over `[T₂, T₃]` the far half accumulates at least `(2/3)(T₃ − T₂)` and the near half at most
  `(1/3)(T₃ − T₂)`.

The mean occupancy of the far half is at most `1/3` before `T₁` and at least `2/3` after `T₂`,
and the near half's the other way round. The predicted arrival `625π` is between `T₁` and `T₂`.

**No carrier at rest does this.** A function `F t = w t`, which is the accumulated occupancy of
a carrier whose occupancy of the region is the constant `w` (`integral_arenaObs_of_const`),
cannot have `F T₁ ≤ (1/3) T₁` and `(2/3)(T₃ − T₂) ≤ F T₃ − F T₂` (`not_transit_of_linear`). In
particular the far half's occupancy along this run is not constant
(`cross_far_occupancy_not_constant`).

**The transit fibres** (`transitFibres`): both rates positive and
`92500 π (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`. No condition relates the rates to the transit time. The
set is open, and for both profiles `trainF` and any positive strengths it contains `(0, 0)` and
has positive Haar measure (`volume_transitFibres_trainF_pos`).

## Exact scope

* **Displacements, not readouts.** The certificate is about the lifted displacement of each
  pointer: a real number, the rate times the accumulated occupancy. The pointer's angle is that
  number modulo one turn, and for the strengths of #367 the far pointer turns more than once by
  `T₃`. No readout region, no threshold and no `IsRecordWrite` is in this module. A pointer read
  in arcs fine enough to recover the displacement is not built here.
* **Four flow times.** The displacements are compared at `0`, `T₁`, `T₂`, `T₃`, which are values
  of the flow parameter (UA-7). No record holds them.
* **What is excluded** is a carrier whose occupancy of the far half is constant in time. A
  carrier that moves in some other way and gives the same four numbers is not excluded. "Transit"
  here means: the occupancy went from mostly near to mostly far between `T₁` and `T₂`.
* **The time is located only to `[T₁, T₂]`**, a factor of five. That is the resolution of the
  packet estimate of `dirac_arrival`: at most a quarter of the weight in the far half up to `T₁`
  and at least three quarters from `T₂`. The write times of #365 and #367 are not located any
  better by this module.
* **Back-reaction is bounded, not removed**: the detectors move each accumulated occupancy by at
  most `(|g₁ f| + |g₂ h|) t²`, and the fibre condition makes that a twelfth of the interval.
* **Positive measure is Haar measure on the pair of conserved angles.** The carrier is one ray,
  so no measure of start points is stated.
* **Definite facts, not statistics.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-8, UA-13, UO-16, UD-93, UD-94, UD-105);
`RecordLayer/UnifiedDepartureArrival.lean` (`regionTwoFlow`, `regionTwoFlow_apply`,
`abs_integral_regionProj_two_sub_free_le`, `arenaObs_nearHalf_free_crossPacket`,
`continuous_regionWeight_crossPacket`, `integral_regionWeight_crossPacket_le`,
`regionTwoFlow_departure_arrival`); `RecordLayer/UnifiedArrivalRecord.lean`
(`arenaObs_farHalf_free_crossPacket`, `crossPacket_ne_zero`, `regionProj`);
`RecordLayer/DiracArrival.lean` (`dirac_arrival`, `regionWeight_cross_far`,
`regionWeight_cross_near`, `crossPacket`, `farHalf`); `RecordLayer/UnifiedTwoPointer.lean`
(`idxTwoShiftFst_ofReal_smul`, `idxTwoShiftSnd_ofReal_smul`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A carrier at rest -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A carrier whose expectation of `D` is the constant `w` accumulates `w t`. -/
theorem integral_arenaObs_of_const {U : ℝ → Matrix.unitaryGroup ι ℂ} {D : Matrix ι ι ℂ}
    {p : GenArena ι} {w : ℝ} (hw : ∀ s, arenaObs D (arenaKick (U s) p) = w) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p)) = w * t := by
  simp only [hw]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

/-- ★★ **No constant occupancy passes the certificate.** A function `F t = w t` cannot be at
most `(1/3) T₁` at `T₁` and gain at least `(2/3)(T₃ − T₂)` over `[T₂, T₃]`. -/
theorem not_transit_of_linear {F : ℝ → ℝ} {w T₁ T₂ T₃ : ℝ} (hF : ∀ t, F t = w * t)
    (hT₁ : 0 < T₁) (h23 : T₂ < T₃) :
    ¬ (F T₁ ≤ 1 / 3 * T₁ ∧ 2 / 3 * (T₃ - T₂) ≤ F T₃ - F T₂) := by
  rintro ⟨h1, h2⟩
  rw [hF] at h1
  rw [hF, hF] at h2
  have hw₁ : w ≤ 1 / 3 := le_of_mul_le_mul_right h1 hT₁
  have hd : 0 < T₃ - T₂ := sub_pos.2 h23
  have h3 := mul_le_mul_of_nonneg_right hw₁ hd.le
  have e : w * T₃ - w * T₂ = w * (T₃ - T₂) := by ring
  rw [e] at h2
  linarith

end Generic

/-! ### The transit fibres -/

section Fibres

variable {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **The transit fibres**: the pairs of conserved angles `(θ₂, ψ₂)` at which both rates are
positive and the back-reaction of the two detectors is small,
`92500 π (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`. -/
def transitFibres : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 0 < rateAt g₁ 1 hf x.1 ∧ 0 < rateAt g₂ 1 hh x.2
    ∧ 92500 * Real.pi * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) < 1}

/-- The transit fibres are open. -/
theorem isOpen_transitFibres (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (transitFibres g₁ g₂ hf hh) := by
  have hκ₁ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₁ 1 hf x.1 :=
    (continuous_rateAt g₁ 1 hf hf1).comp continuous_fst
  have hκ₂ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₂ 1 hh x.2 :=
    (continuous_rateAt g₂ 1 hh hh1).comp continuous_snd
  have hb : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      92500 * Real.pi * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) :=
    continuous_const.mul ((continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs.add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs)
  exact (isOpen_lt continuous_const hκ₁).inter
    ((isOpen_lt continuous_const hκ₂).inter (isOpen_lt hb continuous_const))

/-- **For both profiles `trainF` and any positive strengths the pair `(0, 0)` is a transit
fibre.** -/
theorem zero_mem_transitFibres_trainF {g₁ g₂ : ℝ} (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ transitFibres g₁ g₂ trainF_periodic trainF_periodic := by
  show _ ∧ _ ∧ _
  rw [rateAt_trainF_zero, rateAt_trainF_zero, trainF_lift_zero]
  simp only [mul_zero, abs_zero, add_zero]
  exact ⟨by positivity, by positivity, by norm_num⟩

/-- ★★ **The transit fibres have positive measure** for both profiles `trainF` and any positive
strengths. -/
theorem volume_transitFibres_trainF_pos {g₁ g₂ : ℝ} (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    0 < volume (transitFibres g₁ g₂ trainF_periodic trainF_periodic) :=
  (isOpen_transitFibres g₁ g₂ trainF_periodic trainF_periodic
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_transitFibres_trainF hg₁ hg₂⟩

end Fibres

/-! ### The accumulated occupancies of the two halves -/

section Run

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hL : 640000 ≤ M + 1)

/-- **The accumulated occupancy of the region `C`** along the carrier of `regionTwoFlow` started
on the crossing packet, on the fibre `(φ, χ)`: `∫₀ᵗ ⟨P_C⟩`. -/
noncomputable def crossAccum (C : Finset (ZMod (M + 1))) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, arenaObs (regionProj C)
    (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
      (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
      (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh φ χ s)
      (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)))

/-- ★★ **The two pointers' angles are their starts plus the rates times the accumulated
occupancies** of the near half and of the far half. -/
theorem regionTwoFlow_cross_pointers (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (θ ψ : KTorus) (t : ℝ) :
    (regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh hc hch
        t ((idxArenaEquiv (diracIdx M)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ)).1.2.1
        = θ.1 + ((rateAt g₁ 1 hf θ.2
            * crossAccum g₁ g₂ hf hh hL (farHalf (M + 1))ᶜ θ.2 ψ.2 t : ℝ) : AddCircle (1 : ℝ))
      ∧ (regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
        hc hch t ((idxArenaEquiv (diracIdx M)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ)).2.1
        = ψ.1 + ((rateAt g₂ 1 hh ψ.2
            * crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) θ.2 ψ.2 t : ℝ) : AddCircle (1 : ℝ)) := by
  have e₁ := (idxTwoShiftFst_ofReal_smul g₁
    (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
    (regionProj_isHermitian (farHalf (M + 1))ᶜ)
    (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2
    (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)) t)
  have e₂ := (idxTwoShiftSnd_ofReal_smul g₂
    (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
    (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
    (regionProj_isHermitian (farHalf (M + 1))) hf hh θ.2 ψ.2
    (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)) t)
  rw [regionTwoFlow_apply]
  refine ⟨?_, ?_⟩
  · show θ.1 + _ = _
    rw [crossAccum, rateAt, div_one]
    exact congrArg (fun r : ℝ => θ.1 + ((r : ℝ) : AddCircle (1 : ℝ))) e₁
  · show ψ.1 + _ = _
    rw [crossAccum, rateAt, div_one]
    exact congrArg (fun r : ℝ => ψ.1 + ((r : ℝ) : AddCircle (1 : ℝ))) e₂

include hL in
/-- ★ **The crossing packet's weight in the far half, late**: over `[3125π/3, 4375π/3]` it
integrates to at least three quarters of the interval. -/
theorem le_integral_regionWeight_crossPacket_late :
    3 / 4 * (4375 * Real.pi / 3 - 3125 * Real.pi / 3)
      ≤ ∫ s in (3125 * Real.pi / 3)..(4375 * Real.pi / 3),
          regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
  have hπ := Real.pi_pos
  have hle : 3125 * Real.pi / 3 ≤ 4375 * Real.pi / 3 := by linarith
  have h := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (3 / 4 : ℝ)) volume
      (3125 * Real.pi / 3) (4375 * Real.pi / 3))
    ((continuous_regionWeight_crossPacket hL).intervalIntegrable _ _)
    (fun s hs => regionWeight_cross_near hL hs.1 hs.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- ★ **The far half's accumulated occupancy is within the back-reaction of the free
packet's.** -/
theorem abs_crossAccum_far_sub_le (φ χ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) φ χ t
        - ∫ s in (0 : ℝ)..t, regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))|
      ≤ (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) * t ^ 2 := by
  have h := abs_integral_regionProj_two_sub_free_le (crossHop (M + 1)) 3 g₁ g₂
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh (farHalf (M + 1)) φ χ
    (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)) ht
  simp only [arenaObs_farHalf_free_crossPacket hL] at h
  rw [crossAccum]
  exact h

/-- ★ **The near half's accumulated occupancy is within the back-reaction of the time less the
free packet's far weight.** -/
theorem abs_crossAccum_near_sub_le (φ χ : AddCircle (1 : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |crossAccum g₁ g₂ hf hh hL (farHalf (M + 1))ᶜ φ χ t
        - (t - ∫ s in (0 : ℝ)..t, regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)))|
      ≤ (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) * t ^ 2 := by
  have h := abs_integral_regionProj_two_sub_free_le (crossHop (M + 1)) 3 g₁ g₂
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh (farHalf (M + 1))ᶜ φ χ
    (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)) ht
  simp only [arenaObs_nearHalf_free_crossPacket hL] at h
  have e : (∫ s in (0 : ℝ)..t,
      (1 - regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))))
      = t - ∫ s in (0 : ℝ)..t, regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((continuous_regionWeight_crossPacket hL).intervalIntegrable 0 t),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [e] at h
  rw [crossAccum]
  exact h

/-! ### The certificate -/

/-- ★★★ **A transit, certified.** On a transit fibre, along the carrier of `regionTwoFlow`
started on the crossing packet: over `[0, 625π/3]` the far half accumulates at most a third of
the interval and the near half at least two thirds; over `[3125π/3, 4375π/3]` the far half
accumulates at least two thirds of the interval and the near half at most a third. The times are
flow times (UA-7). -/
theorem cross_transit_certificate {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ transitFibres g₁ g₂ hf hh) :
    crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) φ χ (625 * Real.pi / 3)
        ≤ 1 / 3 * (625 * Real.pi / 3)
      ∧ 2 / 3 * (625 * Real.pi / 3)
        ≤ crossAccum g₁ g₂ hf hh hL (farHalf (M + 1))ᶜ φ χ (625 * Real.pi / 3)
      ∧ 2 / 3 * (4375 * Real.pi / 3 - 3125 * Real.pi / 3)
        ≤ crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) φ χ (4375 * Real.pi / 3)
          - crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) φ χ (3125 * Real.pi / 3)
      ∧ crossAccum g₁ g₂ hf hh hL (farHalf (M + 1))ᶜ φ χ (4375 * Real.pi / 3)
          - crossAccum g₁ g₂ hf hh hL (farHalf (M + 1))ᶜ φ χ (3125 * Real.pi / 3)
        ≤ 1 / 3 * (4375 * Real.pi / 3 - 3125 * Real.pi / 3) := by
  obtain ⟨-, -, hb⟩ := hx
  have hb' : 92500 * Real.pi * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) < 1 := hb
  have hπ := Real.pi_pos
  set b := |g₁ * hf.lift φ| + |g₂ * hh.lift χ| with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hT₁ : (0 : ℝ) ≤ 625 * Real.pi / 3 := by positivity
  have hT₂ : (0 : ℝ) ≤ 3125 * Real.pi / 3 := by positivity
  have hT₃ : (0 : ℝ) ≤ 4375 * Real.pi / 3 := by positivity
  -- the back-reaction at the three times
  have hπb : 0 ≤ Real.pi * b := by positivity
  have r₁ : b * (625 * Real.pi / 3) ^ 2 ≤ 625 * Real.pi / 36 := by
    have e : b * (625 * Real.pi / 3) ^ 2 = 625 * Real.pi / 36 * (2500 * (Real.pi * b)) := by ring
    have e' : 92500 * Real.pi * b = 92500 * (Real.pi * b) := by ring
    have h1 : 2500 * (Real.pi * b) ≤ 1 := by
      rw [e'] at hb'
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 625 * Real.pi / 36)
    rw [e]
    linarith
  have r₂₃ : b * (3125 * Real.pi / 3) ^ 2 + b * (4375 * Real.pi / 3) ^ 2 ≤ 625 * Real.pi / 18 := by
    have e : b * (3125 * Real.pi / 3) ^ 2 + b * (4375 * Real.pi / 3) ^ 2
        = 625 * Real.pi / 18 * (92500 * Real.pi * b) := by ring
    have h2 := mul_le_mul_of_nonneg_left hb'.le (by positivity : (0 : ℝ) ≤ 625 * Real.pi / 18)
    rw [e]
    linarith
  -- the free packet
  have hW := continuous_regionWeight_crossPacket hL
  have hearly := integral_regionWeight_crossPacket_le hL
  have hlate := le_integral_regionWeight_crossPacket_late hL
  have hsplit := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hW.intervalIntegrable 0 (4375 * Real.pi / 3)) (hW.intervalIntegrable 0 (3125 * Real.pi / 3))
  -- coupled against free
  have f₁ := abs_le.1 (abs_crossAccum_far_sub_le g₁ g₂ hf hh hL φ χ hT₁)
  have f₂ := abs_le.1 (abs_crossAccum_far_sub_le g₁ g₂ hf hh hL φ χ hT₂)
  have f₃ := abs_le.1 (abs_crossAccum_far_sub_le g₁ g₂ hf hh hL φ χ hT₃)
  have n₁ := abs_le.1 (abs_crossAccum_near_sub_le g₁ g₂ hf hh hL φ χ hT₁)
  have n₂ := abs_le.1 (abs_crossAccum_near_sub_le g₁ g₂ hf hh hL φ χ hT₂)
  have n₃ := abs_le.1 (abs_crossAccum_near_sub_le g₁ g₂ hf hh hL φ χ hT₃)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- ★★★ **The far half's occupancy along this run is not constant.** On a transit fibre no real
`w` is the occupancy of the far half at every flow time. With `not_transit_of_linear`: a carrier
at rest in the two halves does not pass `cross_transit_certificate`. -/
theorem cross_far_occupancy_not_constant {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ transitFibres g₁ g₂ hf hh) :
    ¬ ∃ w : ℝ, ∀ s, arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
          (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh φ χ s)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL))) = w := by
  rintro ⟨w, hw⟩
  obtain ⟨h1, -, h3, -⟩ := cross_transit_certificate g₁ g₂ hf hh hL hx
  have hπ := Real.pi_pos
  exact not_transit_of_linear
    (F := crossAccum g₁ g₂ hf hh hL (farHalf (M + 1)) φ χ) (w := w)
    (fun t => integral_arenaObs_of_const hw t) (by positivity : (0 : ℝ) < 625 * Real.pi / 3)
    (by linarith : 3125 * Real.pi / 3 < 4375 * Real.pi / 3) ⟨h1, h3⟩

end Run

end CSD.RecordLayer

end
