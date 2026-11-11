/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCausalOrder

/-!
# A position record that singles out its site

**Category:** 7-SigmaLayer (the record layer). BACKLOG #363 — the author's programme "From `Σ` to
physical spacetime", milestone M4, condition (d2) of obligation UO-14 and Remainder (b) of #360.
In the exact instance of `RecordLayer/UnifiedClockSiteRecords.lean` the carrier is one momentum
mode. It occupies every site equally, so the position record is written at the same times
wherever the detector is placed. This module takes a carrier that sits mostly on one site and
shows that the record is written when the detector is at that site, and is not displayed at any
flow time up to the end of that record's window when the detector is placed anywhere else.

**The carrier over a short time.** On the arena of the clock's pointer and a site detector the
device moves by `exp (−i t H)` with `H = clockSiteH`, both couplings in it. The propagator is
within `|t| ‖H‖` of the identity (`norm_clockSiteCarrierU_sub_one_le`). So the occupancy of the
detector's site stays within `2 |s| ‖H‖` of its starting value `q`
(`abs_clockSiteOccupancy_sub_le`), the accumulated occupancy within `‖H‖ t²` of `t q`
(`abs_integral_clockSiteOccupancy_sub_mul_le`), and the site pointer's displacement within
`|κ| ‖H‖ t²` of `κ t q`, `κ` the rate on its fibre (`abs_clockSiteShiftSnd_sub_init_le`). And
`‖H‖ ≤ ‖H_dev‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|` (`norm_clockSiteH_le`).

**The record fibres** (`siteRecordFibres`): the pairs of conserved angles `(θ₂, ψ₂)` at which
the rate `κ` is positive and `16 (‖H_dev‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 3 κ`. The set does not
depend on the detector's site. It is open (`isOpen_siteRecordFibres`). For the detector profile
`trainF` and a strength `g₂` with `16 (‖H_dev‖ + |g₁ f(φ₀)|) < 6 g₂` at one angle `φ₀` it
contains `(φ₀, 0)` and has positive measure (`mem_siteRecordFibres_trainF`,
`volume_siteRecordFibres_trainF_pos`), and such a strength exists for every device, every clock
coupling and every continuous clock profile (`exists_volume_siteRecordFibres_pos`).

**On a record fibre, from a ready site pointer:**

* a carrier with at least `7/8` of its occupancy on the detector's site writes: the readout
  history is an `IsRecordWrite` of `true` with write interval `[1/(6κ), 1/(2κ)]` and window
  `1/(6κ)` (`isRecordWrite_clockSiteFlow_site_of_occupancy`,
  `clockSiteFlow_site_shown_of_occupancy`);
* a carrier with at most `1/8` of its occupancy on the detector's site is not displayed at any
  time up to `2/(3κ)`, the end of that window (`clockSiteFlow_site_not_shown_of_occupancy`).

**The record singles out its site.** The occupancies of the sites sum to one, so a carrier with
at least `7/8` on a site `x` has at most `1/8` on every other
(`arenaObs_deviceSiteProj_le_one_sub`). For such a carrier, and a detector placed at any site
`k`: the readout at the flow time `1/(2κ)` is `true` exactly when `k = x`
(`clockSiteFlow_site_shown_iff`). The carrier on one site is an example
(`deviceSiteRay`, `arenaObs_deviceSiteProj_deviceSiteRay`).

## Exact scope

* **One detector in each run.** The arena has one site detector. "A detector at another site"
  is another arena, with the same device, clock and pointers and the site projector moved. The
  two readouts compared in `clockSiteFlow_site_shown_iff` are of two flows, not of one run. A
  run with two site detectors is the arena of `diracTwoPointerFlow`, which has no readout
  (#361 Remainder (c)).
* **A fast detector.** The condition `16 ‖H‖ < 3 κ` makes the write complete at `1/(2κ)`, a
  time short against `1/‖H‖`. By then the occupancy of the detector's site has changed by at
  most `3/16`, and by at most `1/4` at the end of the window. Nothing here follows a moving
  packet, and nothing is said for a detector slower than the carrier.
* **Up to the end of the window.** The carrier off the detector's site is not displayed up to
  `2/(3κ)`. Nothing is said after that time, for either placement of the detector.
* **The carrier is a class, not a packet.** The statements hold for every ray with at least
  `7/8` (or at most `1/8`) of its occupancy on the site. The class is not confined to rays on
  one site, but the only member exhibited is `deviceSiteRay`. No particular packet is evolved.
* **Positive measure for the write only.** The record fibres have positive Haar measure in
  `(θ₂, ψ₂)`, for the detector profile `trainF` and a strong enough detector. So for carriers
  in the class the position write no longer needs the null set of #360. The clock pointer's
  conserved angle `θ₂` is in the fibre condition; only its moving angle is free. The clock's
  swing is not treated here: on these fibres its four inequalities of #358 stay hypotheses, and
  the tick record with them (#360 Remainder (a)).
* **A definite fact, not a statistic.** The record is that the accumulated occupancy of the
  detector's site crossed the threshold along the one trajectory. Carriers with occupancy
  between `1/8` and `7/8` are not covered. No weight of quantum mechanics is derived.
* **All times are flow times** (UA-7). The thresholds `7/8`, `1/8` and the factor `16` are
  sufficient, not sharp. The readout and the ready arc are apparatus input (UA-4).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UA-13, UO-14 (d2), UD-84, UD-85); `RecordLayer/UnifiedClockSiteRecords.lean`
(`isRecordWrite_clockSiteFlow_site`, `clockSiteShiftSnd_mono`, `clockSiteShiftSnd_le`,
`sum_arenaObs_deviceSiteProj`, `echoSiteShown`); `RecordLayer/UnifiedTwoPointer.lean`
(`clockSiteH`, `clockSiteCarrierU`, `clockSiteFlow`); `RecordLayer/UnifiedCausalOrder.lean`
(`clockSiteH_isHermitian`); `RecordLayer/DiracPointerThreshold.lean`
(`writeFibres`, the one-pointer statement this follows); `RecordLayer/DiracPointerWrite.lean`
(`abs_arenaObs_arenaKick_sub_le`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

section ShortTime

variable {M : ℕ} {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ) (k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-! ### The device over a short time -/

/-- **The coupled propagator is within `|t| ‖H‖` of the identity.** -/
theorem norm_clockSiteCarrierU_sub_one_le (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ t).val - 1‖
      ≤ |t| * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ := by
  have h := Matrix.norm_exp_smul_neg_I_sub_le (clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ) 0
    (clockSiteH_isHermitian J μ₀ μ₁ g₁ g₂ k hf hh φ χ) Matrix.isHermitian_zero t
  rw [smul_zero, smul_zero, NormedSpace.exp_zero, sub_zero] at h
  rwa [clockSiteCarrierU_val]

/-- The device's Hamiltonian is no larger than the free device's plus the two couplings. -/
theorem norm_clockSiteH_le (φ χ : AddCircle (1 : ℝ)) :
    ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖
      ≤ ‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift φ| + |g₂ * hh.lift χ| := by
  rw [clockSiteH]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) norm_levelSwap_le
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_deviceSiteProj_le k)

/-- ★ **The occupancy of the detector's site stays within `2 |s| ‖H‖` of its starting value.** -/
theorem abs_clockSiteOccupancy_sub_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (s : ℝ) :
    |arenaObs (deviceSiteProj k) (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p)
        - arenaObs (deviceSiteProj k) p|
      ≤ 2 * |s| * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ := by
  have h1 : arenaObs (deviceSiteProj k) p
      = arenaObs (deviceSiteProj k) (arenaKick (1 : Matrix.unitaryGroup _ ℂ) p) := by
    rw [arenaObs_kick_conj]
    simp
  rw [h1]
  refine (abs_arenaObs_arenaKick_sub_le _ _ (deviceSiteProj k) p).trans ?_
  have hU := norm_clockSiteCarrierU_sub_one_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ s
  have hone : ((1 : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ)).val = 1 := rfl
  rw [hone]
  have hn := norm_deviceSiteProj_le k
  have h0 : 0 ≤ ‖(clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s).val - 1‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hn h0]

/-- ★★ **The accumulated occupancy is within `‖H‖ t²` of `t` times the starting occupancy.** -/
theorem abs_integral_clockSiteOccupancy_sub_mul_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs (deviceSiteProj k)
          (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p))
        - t * arenaObs (deviceSiteProj k) p|
      ≤ ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ * t ^ 2 := by
  have hocc := continuous_clockSiteOccupancy J μ₀ μ₁ g₁ g₂ k hf hh φ χ p
  have hconst : (∫ _ in (0 : ℝ)..t, arenaObs (deviceSiteProj k) p)
      = t * arenaObs (deviceSiteProj k) p := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← hconst, ← intervalIntegral.integral_sub (hocc.intervalIntegrable 0 t)
    intervalIntegrable_const]
  have hc : Continuous fun s : ℝ => 2 * s * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ := by
    fun_prop
  have hab : Continuous fun s : ℝ =>
      |arenaObs (deviceSiteProj k) (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p)
        - arenaObs (deviceSiteProj k) p| := (hocc.sub continuous_const).abs
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht (hab.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := abs_clockSiteOccupancy_sub_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ p s
    rwa [abs_of_nonneg hs.1] at h
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring

/-- ★★ **The site pointer's displacement is within `|κ| ‖H‖ t²` of `κ t q`**, `κ` the rate on
its fibre and `q` the carrier's starting occupancy of the detector's site. -/
theorem abs_clockSiteShiftSnd_sub_init_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t
        - rateAt g₂ 1 hh χ * (t * arenaObs (deviceSiteProj k) p)|
      ≤ |rateAt g₂ 1 hh χ| * (‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ * t ^ 2) := by
  rw [clockSiteShiftSnd_eq_rateAt, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_clockSiteOccupancy_sub_mul_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ p ht) (abs_nonneg _)

end ShortTime

/-! ### The record fibres -/

section Fibres

variable (M : ℕ) {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **The record fibres**: the pairs of conserved angles `(θ₂, ψ₂)` at which the site pointer's
rate `κ` is positive and `16 (‖H_dev‖ + |g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 3 κ`. The set does not depend
on the detector's site. -/
def siteRecordFibres : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 0 < rateAt g₂ 1 hh x.2
    ∧ 16 * (‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|)
        < 3 * rateAt g₂ 1 hh x.2}

/-- The record fibres are open. -/
theorem isOpen_siteRecordFibres (hf0 : Continuous f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) := by
  have hκ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₂ 1 hh x.2 :=
    (continuous_rateAt g₂ 1 hh hh1).comp continuous_snd
  have hF : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => |g₁ * hf.lift x.1| :=
    (continuous_const.mul ((continuous_periodicLift hf hf0).comp continuous_fst)).abs
  have hH : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => |g₂ * hh.lift x.2| :=
    (continuous_const.mul
      ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs
  exact (isOpen_lt continuous_const hκ).inter
    (isOpen_lt (continuous_const.mul ((continuous_const.add hF).add hH))
      (continuous_const.mul hκ))

variable {M}

/-- On a record fibre the rate is positive and `16 ‖H‖ ≤ 3 κ`, for a detector at any site. -/
theorem siteRecordFibres_bounds {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) (k : ZMod (M + 1)) :
    0 < rateAt g₂ 1 hh χ
      ∧ 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ ≤ 3 * rateAt g₂ 1 hh χ := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨h1, (mul_le_mul_of_nonneg_left (norm_clockSiteH_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ)
    (by norm_num)).trans h2.le⟩

variable (M)

/-- **For the detector profile `trainF` the pair `(φ₀, 0)` is a record fibre** once
`16 (‖H_dev‖ + |g₁ f(φ₀)|) < 6 g₂`. -/
theorem mem_siteRecordFibres_trainF (φ₀ : AddCircle (1 : ℝ))
    (hg : 16 * (‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift φ₀|) < 6 * g₂) :
    (φ₀, (0 : AddCircle (1 : ℝ))) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf trainF_periodic := by
  have h0 : 0 ≤ ‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift φ₀| := by positivity
  show _ ∧ _
  rw [rateAt_trainF_zero, trainF_lift_zero, mul_zero, abs_zero, add_zero]
  exact ⟨by linarith, by linarith⟩

/-- ★★ **The record fibres have positive measure** for the detector profile `trainF`, a
continuous clock profile and a strong enough detector. -/
theorem volume_siteRecordFibres_trainF_pos (hf0 : Continuous f) (φ₀ : AddCircle (1 : ℝ))
    (hg : 16 * (‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift φ₀|) < 6 * g₂) :
    0 < volume (siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf trainF_periodic) :=
  (isOpen_siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf trainF_periodic hf0
    (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(φ₀, 0), mem_siteRecordFibres_trainF M J μ₀ μ₁ g₁ g₂ hf φ₀ hg⟩

/-- ★ **For every device, every clock coupling and every continuous clock profile there is a
detector strength** at which the record fibres have positive measure. -/
theorem exists_volume_siteRecordFibres_pos (hf0 : Continuous f) :
    ∃ g₂ : ℝ, 0 < volume (siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf trainF_periodic) :=
  ⟨(16 * (‖deviceHam (L := M + 1) J μ₀ μ₁‖ + |g₁ * hf.lift 0|) + 1) / 6,
    volume_siteRecordFibres_trainF_pos M J μ₀ μ₁ g₁ _ hf hf0 0 (by
      rw [mul_div_cancel₀ _ (by norm_num : (6 : ℝ) ≠ 0)]
      linarith)⟩

end Fibres

/-! ### The write, and its absence -/

section Record

variable {M : ℕ} {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ) (k : ZMod (M + 1))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- The displacement at `1/(2κ)` of a carrier with occupancy at least `7/8`. -/
theorem third_le_clockSiteShiftSnd {φ χ : AddCircle (1 : ℝ)} {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh χ) (hκ : 0 < κ)
    (hN : 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ ≤ 3 * κ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hq : 7 / 8 ≤ arenaObs (deviceSiteProj k) p) :
    1 / 3 ≤ clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p (1 / (2 * κ)) := by
  have ht : (0 : ℝ) ≤ 1 / (2 * κ) := by positivity
  have key := (abs_le.1
    (abs_clockSiteShiftSnd_sub_init_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ p ht)).1
  rw [← hκe, abs_of_pos hκ] at key
  have hNκ : ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ / κ ≤ 3 / 16 := by
    rw [div_le_iff₀ hκ]
    linarith
  have e1 : κ * (1 / (2 * κ) * arenaObs (deviceSiteProj k) p)
      = arenaObs (deviceSiteProj k) p / 2 := by
    field_simp
  have e2 : κ * (‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ * (1 / (2 * κ)) ^ 2)
      = ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ / κ / 4 := by
    field_simp
    ring
  rw [e1, e2] at key
  linarith

/-- The displacement up to `2/(3κ)` of a carrier with occupancy at most `1/8`. -/
theorem clockSiteShiftSnd_le_sixth {φ χ : AddCircle (1 : ℝ)} {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh χ) (hκ : 0 < κ)
    (hN : 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ ≤ 3 * κ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hq : arenaObs (deviceSiteProj k) p ≤ 1 / 8) {t : ℝ} (ht : t ≤ 2 / (3 * κ)) :
    clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t ≤ 1 / 6 := by
  have hκ0 : 0 ≤ rateAt g₂ 1 hh χ := by rw [← hκe]; exact hκ.le
  have ht2 : (0 : ℝ) ≤ 2 / (3 * κ) := by positivity
  refine (clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh φ hκ0 p ht).trans ?_
  have key := (abs_le.1
    (abs_clockSiteShiftSnd_sub_init_le J μ₀ μ₁ g₁ g₂ k hf hh φ χ p ht2)).2
  rw [← hκe, abs_of_pos hκ] at key
  have hNκ : ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ / κ ≤ 3 / 16 := by
    rw [div_le_iff₀ hκ]
    linarith
  have e1 : κ * (2 / (3 * κ) * arenaObs (deviceSiteProj k) p)
      = 2 * arenaObs (deviceSiteProj k) p / 3 := by
    field_simp
  have e2 : κ * (‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ * (2 / (3 * κ)) ^ 2)
      = 4 * (‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ‖ / κ) / 9 := by
    field_simp
    ring
  rw [e1, e2] at key
  linarith

/-- ★★★ **A carrier mostly on the detector's site writes the position record.** On a record
fibre, from a ready site pointer, for a carrier with at least `7/8` of its occupancy on the
detector's site and any moving angle of the clock's pointer: the readout history along
`clockSiteFlow` is an `IsRecordWrite` of `true` from time `0`, with write interval
`[1/(6κ), 1/(2κ)]` and window `1/(6κ)`, `κ` the site pointer's rate. The times are flow times
(UA-7). -/
theorem isRecordWrite_clockSiteFlow_site_of_occupancy (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) {θ ψ : KTorus} (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh ψ.2) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hq : 7 / 8 ≤ arenaObs (deviceSiteProj k) p) :
    IsRecordWrite
      (fun t => echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)))
      0 (1 / (6 * κ)) (1 / (2 * κ)) (1 / (6 * κ)) true := by
  obtain ⟨hκ', hN'⟩ := siteRecordFibres_bounds J μ₀ μ₁ g₁ g₂ hf hh hx k
  have hκ : 0 < κ := by rw [hκe]; exact hκ'
  have hN : 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ ≤ 3 * κ := by rw [hκe]; exact hN'
  have hκ0 : 0 ≤ rateAt g₂ 1 hh ψ.2 := hκ'.le
  have hκne : κ ≠ 0 := hκ.ne'
  have u₀ := clockSiteShiftSnd_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ0 p
    (t := 1 / (6 * κ)) (by positivity)
  have u₂ := clockSiteShiftSnd_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ0 p
    (t := 2 / (3 * κ)) (by positivity)
  rw [← hκe] at u₀ u₂
  have v₀ : κ * (1 / (6 * κ)) = 1 / 6 := by field_simp
  have v₂ : κ * (2 / (3 * κ)) = 2 / 3 := by field_simp
  rw [v₀] at u₀
  rw [v₂] at u₂
  have key := isRecordWrite_clockSiteFlow_site J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ θ hκ0 p
    (τ₀ := 1 / (6 * κ)) (τ₁ := 1 / (2 * κ)) (τ₂ := 2 / (3 * κ)) (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    u₀ (third_le_clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh hκe hκ hN p hq) u₂
  have e : 2 / (3 * κ) - 1 / (2 * κ) = 1 / (6 * κ) := by
    field_simp
    ring
  rw [e] at key
  exact key

/-- ★★ **The readout of such a carrier shows `true` through the window**: at every flow time
in `[1/(2κ), 2/(3κ)]`. -/
theorem clockSiteFlow_site_shown_of_occupancy (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh ψ.2) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hq : 7 / 8 ≤ arenaObs (deviceSiteProj k) p) {t : ℝ} (ht₁ : 1 / (2 * κ) ≤ t)
    (ht₂ : t ≤ 2 / (3 * κ)) :
    echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) = true := by
  obtain ⟨hκ', hN'⟩ := siteRecordFibres_bounds J μ₀ μ₁ g₁ g₂ hf hh hx k
  have hκ : 0 < κ := by rw [hκe]; exact hκ'
  have hN : 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ ≤ 3 * κ := by rw [hκe]; exact hN'
  have hκ0 : 0 ≤ rateAt g₂ 1 hh ψ.2 := hκ'.le
  have ht0 : 0 ≤ t := le_trans (by positivity) ht₁
  rw [echoSiteShown_eq_true_iff]
  show (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2
    ∈ displayArc
  rw [clockSiteFlow_site_pointer]
  refine pshift_mem_displayArc hψ
    ((third_le_clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh hκe hκ hN p hq).trans
      (clockSiteShiftSnd_mono J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ0 p ht₁)) ?_
  have u := (clockSiteShiftSnd_le J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ0 p ht0).trans
    (mul_le_mul_of_nonneg_left ht₂ hκ0)
  rw [← hκe] at u
  have v₂ : κ * (2 / (3 * κ)) = 2 / 3 := by
    have hκne : κ ≠ 0 := hκ.ne'
    field_simp
  rwa [v₂] at u

/-- ★★★ **A carrier mostly off the detector's site is not displayed.** On a record fibre, from
a ready site pointer, for a carrier with at most `1/8` of its occupancy on the detector's site:
the readout does not show `true` at any flow time up to `2/(3κ)`, the end of the window in which
a carrier on the site is displayed. -/
theorem clockSiteFlow_site_not_shown_of_occupancy (hc : ContDiff ℝ ∞ f)
    (hch : ContDiff ℝ ∞ h) {θ ψ : KTorus} (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh ψ.2) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    (hq : arenaObs (deviceSiteProj k) p ≤ 1 / 8) {t : ℝ} (ht0 : 0 ≤ t)
    (ht₂ : t ≤ 2 / (3 * κ)) :
    ¬ echoSiteShown (4 * M + 3)
      (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)) = true := by
  obtain ⟨hκ', hN'⟩ := siteRecordFibres_bounds J μ₀ μ₁ g₁ g₂ hf hh hx k
  have hκ : 0 < κ := by rw [hκe]; exact hκ'
  have hN : 16 * ‖clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2‖ ≤ 3 * κ := by rw [hκe]; exact hN'
  have hκ0 : 0 ≤ rateAt g₂ 1 hh ψ.2 := hκ'.le
  rw [echoSiteShown_eq_true_iff]
  show (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)).2
    ∉ displayArc
  rw [clockSiteFlow_site_pointer]
  exact pshift_notMem_displayArc_of_le hψ
    (clockSiteShiftSnd_nonneg J μ₀ μ₁ g₁ g₂ k hf hh θ.2 hκ0 p ht0)
    (clockSiteShiftSnd_le_sixth J μ₀ μ₁ g₁ g₂ k hf hh hκe hκ hN p hq ht₂)

/-! ### The record singles out its site -/

/-- The occupancies of two different sites sum to at most one. -/
theorem arenaObs_deviceSiteProj_le_one_sub {k x : ZMod (M + 1)} (hkx : k ≠ x)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (deviceSiteProj k) p ≤ 1 - arenaObs (deviceSiteProj x) p := by
  have hsum := sum_arenaObs_deviceSiteProj p
  have hle := Finset.add_le_sum (f := fun y : ZMod (M + 1) => arenaObs (deviceSiteProj y) p)
    (fun y _ => arenaObs_deviceSiteProj_nonneg y p) (Finset.mem_univ k) (Finset.mem_univ x) hkx
  rw [hsum] at hle
  linarith

/-- **The device on one site**: the ray of the basis vector at site `x`, lower spinor component,
lower level. -/
noncomputable def deviceSiteRay (x : ZMod (M + 1)) :
    GenArena ((ZMod (M + 1) × Fin 2) × Fin 2) :=
  Projectivization.mk ℂ (EuclideanSpace.single ((x, 0), 0) (1 : ℂ)) (fun h => by
    simpa using congrArg
      (fun v : EuclideanSpace ℂ ((ZMod (M + 1) × Fin 2) × Fin 2) => v ((x, 0), 0)) h)

/-- The device on site `x` occupies site `x`. -/
theorem arenaObs_deviceSiteProj_deviceSiteRay (x : ZMod (M + 1)) :
    arenaObs (deviceSiteProj x) (deviceSiteRay x) = 1 := by
  rw [deviceSiteRay, arenaObs_deviceSiteProj]
  simp [momentMap_mk, Fin.sum_univ_two]

/-- ★★★ **The position record singles out its site.** Take a carrier with at least `7/8` of its
occupancy on a site `x`, a record fibre and a ready site pointer. Place the detector at any site
`k`. The readout at the flow time `1/(2κ)` is `true` exactly when `k = x`. The two cases are
readouts of two flows, one for each placement of the detector, and not of one run. -/
theorem clockSiteFlow_site_shown_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ siteRecordFibres M J μ₀ μ₁ g₁ g₂ hf hh) {κ : ℝ}
    (hκe : κ = rateAt g₂ 1 hh ψ.2) (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2))
    {x : ZMod (M + 1)} (hq : 7 / 8 ≤ arenaObs (deviceSiteProj x) p) :
    echoSiteShown (4 * M + 3)
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (1 / (2 * κ))
          ((clockArenaEquiv M p, θ), ψ)) = true ↔ k = x := by
  have hκ : 0 < κ := by
    rw [hκe]
    exact (siteRecordFibres_bounds J μ₀ μ₁ g₁ g₂ hf hh hx k).1
  have hle : 1 / (2 * κ) ≤ 2 / (3 * κ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  constructor
  · intro hshown
    by_contra hkx
    have hqk : arenaObs (deviceSiteProj k) p ≤ 1 / 8 := by
      have := arenaObs_deviceSiteProj_le_one_sub hkx p
      linarith
    exact clockSiteFlow_site_not_shown_of_occupancy J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ hx hκe p
      hqk (by positivity) hle hshown
  · rintro rfl
    exact clockSiteFlow_site_shown_of_occupancy J μ₀ μ₁ g₁ g₂ k hf hh hc hch hψ hx hκe p hq
      le_rfl hle

end Record

end CSD.RecordLayer

end
