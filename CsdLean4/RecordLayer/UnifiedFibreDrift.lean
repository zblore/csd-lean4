/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedFibreRun
public import CsdLean4.RecordLayer.UnifiedCompositeCarrier

/-!
# The drift of a pointer's displacement when the carrier's matrix changes

**Category:** 7-SigmaLayer (the record layer). BACKLOG #428 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), third part. No new assumption beyond
UA-18.

Off the fibres where the profiles vanish the carrier moves by the free flow of another
constant matrix (`pentaRun_fibre`) and each pointer is turned with another strength. This
module bounds what that does to a pointer's displacement.

* `idxCarrierU_const_eq` — the free propagator of `H'` is the coupled propagator of `H` with
  the difference and a constant profile;
* ★ `abs_arenaObs_idxFreeU_sub_le` — an expectation along the free orbit of `H'` is within
  `2 ‖C‖ |s| ‖H' − H‖` of the one along the free orbit of `H`;
* ★★ `freeShift_drift` — the displacement with matrix `H'` and strength `z'` drifts from the
  one with `H` and `z` at a rate at most `4 |z'| ‖G‖ T ‖H' − H‖ + 2 |z' − z| ‖G‖` up to `T`;
* `freeShift_zero` — a displacement starts at `0`.

## Exact scope

* **Bounds in the operator norm**, with the factor `T`: the rate is small only when
  `‖H' − H‖` is small against `1/T`. Nothing is said about how small it is for a given set
  of pointer angles.
* **One pointer.** Nothing about histories or counts.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-109, UD-197, UD-198); `RecordLayer/UnifiedFibreRun.lean` (#428:
`pentaRun_fibre`); `RecordLayer/UnifiedRadarStability.lean` (#427: `IsGatedHistory.of_drift`,
whose drift hypothesis this is); `RecordLayer/UnifiedDiracClock.lean`
(`abs_arenaObs_idxCarrierU_sub_le`, `idxFreeU`); `RecordLayer/UnifiedCausalArrival.lean`
(`abs_arenaObs_le`); `RecordLayer/UnifiedCompositeCarrier.lean`
(`continuous_arenaObs_idxFreeU`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

section Drift

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {H H' : Matrix ν ν ℂ}

/-- The constant profile `1`. -/
theorem periodic_const_one : Function.Periodic (fun _ : ℝ => (1 : ℝ)) 1 := fun _ => rfl

/-- The free propagator of `H'` is the coupled propagator of `H` with the difference `H' − H`
and the constant profile `1`. -/
theorem idxCarrierU_const_eq (hH : H.IsHermitian) (hH' : H'.IsHermitian) (s : ℝ) :
    idxCarrierU hH (hH'.sub hH) periodic_const_one (0 : AddCircle (1 : ℝ)) s
      = idxFreeU hH' s := by
  apply Subtype.ext
  rw [idxCarrierU_val, idxFreeU_val, idxCoupledH]
  have h1 : periodic_const_one.lift (0 : AddCircle (1 : ℝ)) = 1 := by
    show periodic_const_one.lift (((0 : ℝ) : AddCircle (1 : ℝ))) = 1
    rw [Function.Periodic.lift_coe]
  rw [h1]
  simp

variable [Nonempty ν]

/-- ★ **An expectation along the free orbit of another matrix.** -/
theorem abs_arenaObs_idxFreeU_sub_le (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (C : Matrix ν ν ℂ) (p : GenArena ν) (s : ℝ) :
    |arenaObs C (arenaKick (idxFreeU hH' s) p) - arenaObs C (arenaKick (idxFreeU hH s) p)|
      ≤ 2 * ‖C‖ * (|s| * ‖H' - H‖) := by
  have h := abs_arenaObs_idxCarrierU_sub_le hH (hH'.sub hH) periodic_const_one
    (0 : AddCircle (1 : ℝ)) C p s
  have h1 : periodic_const_one.lift (0 : AddCircle (1 : ℝ)) = 1 := by
    show periodic_const_one.lift (((0 : ℝ) : AddCircle (1 : ℝ))) = 1
    rw [Function.Periodic.lift_coe]
  rw [idxCarrierU_const_eq hH hH', h1, abs_one, one_mul] at h
  exact h

omit [Nonempty ν] in
/-- A displacement starts at `0`. -/
theorem freeShift_zero (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ) (p : GenArena ν) :
    freeShift hH G z p 0 = 0 := by
  rw [freeShift, intervalIntegral.integral_same, mul_zero]

/-- ★★ **The drift of a displacement.** Up to the flow time `T`, the displacement of a
pointer with observable `G` along the free orbit of `H'` with strength `z'` drifts from the
one along the free orbit of `H` with strength `z` at a rate at most
`4 |z'| ‖G‖ T ‖H' − H‖ + 2 |z' − z| ‖G‖`. -/
theorem freeShift_drift (hH : H.IsHermitian) (hH' : H'.IsHermitian) (G : Matrix ν ν ℂ)
    (z z' : ℝ) (p : GenArena ν) {T s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    |(freeShift hH' G z' p t - freeShift hH G z p t)
        - (freeShift hH' G z' p s - freeShift hH G z p s)|
      ≤ (4 * |z'| * ‖G‖ * T * ‖H' - H‖ + 2 * |z' - z| * ‖G‖) * (t - s) := by
  have hc' := continuous_arenaObs_idxFreeU hH' G p
  have hc := continuous_arenaObs_idxFreeU hH G p
  have hT : 0 ≤ T := hs.trans (hst.trans ht)
  have hG : 0 ≤ ‖G‖ := norm_nonneg _
  have hE : 0 ≤ ‖H' - H‖ := norm_nonneg _
  -- the increments
  have e' : freeShift hH' G z' p t - freeShift hH' G z' p s
      = -2 * z' * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH' u) p) := by
    rw [freeShift, freeShift, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc'.intervalIntegrable _ _)
        (hc'.intervalIntegrable _ _)]
  have e : freeShift hH G z p t - freeShift hH G z p s
      = -2 * z * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p) := by
    rw [freeShift, freeShift, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have split : (freeShift hH' G z' p t - freeShift hH G z p t)
        - (freeShift hH' G z' p s - freeShift hH G z p s)
      = -2 * z' * (∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH' u) p)
            - arenaObs G (arenaKick (idxFreeU hH u) p)))
        - 2 * (z' - z) * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p) := by
    rw [intervalIntegral.integral_sub (hc'.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    linear_combination e' - e
  -- the two integrals
  have b1 : |∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH' u) p)
      - arenaObs G (arenaKick (idxFreeU hH u) p))| ≤ 2 * ‖G‖ * (T * ‖H' - H‖) * (t - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := 2 * ‖G‖ * (T * ‖H' - H‖))
      (f := fun u => arenaObs G (arenaKick (idxFreeU hH' u) p)
        - arenaObs G (arenaKick (idxFreeU hH u) p)) (fun u hu => by
        rw [Set.uIoc_of_le hst] at hu
        have hu0 : 0 ≤ u := hs.trans hu.1.le
        rw [Real.norm_eq_abs]
        refine (abs_arenaObs_idxFreeU_sub_le hH hH' G p u).trans ?_
        rw [abs_of_nonneg hu0]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hu.2.trans ht) hE) (by positivity))
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at h
  have b2 : |∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p)| ≤ ‖G‖ * (t - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := ‖G‖) (f := fun u => arenaObs G (arenaKick (idxFreeU hH u) p)) (fun u _ => by
        rw [Real.norm_eq_abs]
        exact abs_arenaObs_le G _)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at h
  rw [split]
  calc |-2 * z' * (∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH' u) p)
            - arenaObs G (arenaKick (idxFreeU hH u) p)))
        - 2 * (z' - z) * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p)|
      ≤ |-2 * z' * (∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH' u) p)
            - arenaObs G (arenaKick (idxFreeU hH u) p)))|
        + |2 * (z' - z) * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p)| :=
        abs_sub _ _
    _ ≤ 2 * |z'| * (2 * ‖G‖ * (T * ‖H' - H‖) * (t - s))
        + 2 * |z' - z| * (‖G‖ * (t - s)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_two]
        exact add_le_add (mul_le_mul_of_nonneg_left b1 (by positivity))
          (mul_le_mul_of_nonneg_left b2 (by positivity))
    _ = (4 * |z'| * ‖G‖ * T * ‖H' - H‖ + 2 * |z' - z| * ‖G‖) * (t - s) := by ring

end Drift

end CSD.RecordLayer

end
