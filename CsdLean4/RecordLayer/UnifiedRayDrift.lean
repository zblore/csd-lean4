/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedFibreDrift
public import CsdLean4.RecordLayer.UnifiedRadarStability

/-!
# The drift of a pointer's displacement when the carrier's ray changes

**Category:** 7-SigmaLayer. BACKLOG #438, first brick (Task 2 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (2)).

The five record events of `RecordLayer/UnifiedRecordHistoryBridge.lean` contain the run's
start for the family's carrier ray and an open set of pointer angles. One ray has
Fubini–Study measure zero, so that is not a set of positive measure in the arena. The open
set of angles came from `RecordLayer/UnifiedFibreDrift.lean`: a history survives a small
change of the carrier's matrix. Here the same for a small change of the carrier's **ray**. A
ray near `p` is written as `p` turned by a unitary `W` near the identity.

* ★★ `abs_arenaObs_kick_kick_sub_le` (after any unitary, the expectation of `G` from the
  turned ray is within `2 ‖G‖ ‖W − 1‖` of the one from the ray; no time in the bound);
* ★★ `freeShift_ray_drift` (the displacement from the turned ray drifts from the one from
  the ray at a rate at most `4 |z| ‖G‖ ‖W − 1‖`), `abs_freeShift_ray_sub_le`;
* ★★★ `IsGatedHistory.of_ray`, ★★★ `IsAwayHistory.of_ray` (**a history at a ray is a history
  at every turned ray**, with error enlarged by `lam · t` and speed by `lam`, for
  `lam ≥ 4 |z| ‖G‖ ‖W − 1‖`).

## Honest scope

⚠️ **No measure is computed and no preparation is built.** This is the stability of one
displacement's history. Still owed for UO-25 (2): the five histories of the family at every
turned ray, with their slack; the counts at each such ray from `penta_radar_lorentz_fibre`
(a turned ray is not a product of the three carriers' rays, so the three-carrier theorem
`tri_radar_lorentz_near` does not apply to it); that the turned rays have positive
Fubini–Study measure; the `HistoryPreparation`.

⚠️ **The rate does not grow with time, the error does.** The error is `lam · t`, so for a
run that ends at `T` the turned rays that keep the histories lie within a distance of order
`1/T` of the family's ray.

⚠️ **Along the free orbit only.** These are displacements on the fibre where the profiles
vanish. Joining them with the drift over the fibres is the next step, not done here.

References: `specs/BACKLOG.md` #438, ~~#436~~, ~~#427~~, ~~#428~~;
`specs/unified-record-spacetime-plan.md` (UO-25, UD-198, UD-200, UD-208, UD-213);
`RecordLayer/UnifiedFibreDrift.lean` (`freeShift_drift`, `freeShift_zero`);
`RecordLayer/UnifiedRadarStability.lean` (`IsGatedHistory.of_drift`, `IsAwayHistory.of_drift`);
`RecordLayer/UnifiedTriFibre.lean` (`IsGatedHistory.of_fibre`, `tri_radar_lorentz_near`);
`RecordLayer/UnifiedFibreRadar.lean` (`penta_radar_lorentz_fibre`);
`RecordLayer/UnifiedTwoSiteRecords.lean` (`abs_arenaObs_arenaKick_sub_self_le`);
`LF4/TypicalityForcing.lean` (`fsMeasure_pos_of_isOpen`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] {H G : Matrix ν ν ℂ}

/-- ★★ **An expectation along the orbit of a turned ray.** After any unitary `U`, the
expectation of `G` from the ray turned by `W` is within `2 ‖G‖ ‖W − 1‖` of the one from the
ray itself. The bound has no time in it. -/
theorem abs_arenaObs_kick_kick_sub_le (U W : Matrix.unitaryGroup ν ℂ) (G : Matrix ν ν ℂ)
    (p : GenArena ν) :
    |arenaObs G (arenaKick U (arenaKick W p)) - arenaObs G (arenaKick U p)|
      ≤ 2 * ‖G‖ * ‖W.val - 1‖ := by
  have hU : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.property
  have hG : ‖star U.val * G * U.val‖ ≤ ‖G‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [hU, mul_one]
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star, hU, one_mul]
  rw [arenaObs_kick_conj U G (arenaKick W p), arenaObs_kick_conj U G p]
  refine (abs_arenaObs_arenaKick_sub_self_le W _ p).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG (by norm_num))
    (norm_nonneg _)

/-- ★★ **The drift of a displacement when the ray is turned.** The displacement of a pointer
with observable `G` and strength `z` along the free orbit from the ray turned by `W` drifts
from the one from the ray itself at a rate at most `4 |z| ‖G‖ ‖W − 1‖`, at all times. -/
theorem freeShift_ray_drift (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ)
    (W : Matrix.unitaryGroup ν ℂ) (p : GenArena ν) {s t : ℝ} (hst : s ≤ t) :
    |(freeShift hH G z (arenaKick W p) t - freeShift hH G z p t)
        - (freeShift hH G z (arenaKick W p) s - freeShift hH G z p s)|
      ≤ 4 * |z| * ‖G‖ * ‖W.val - 1‖ * (t - s) := by
  have hc' := continuous_arenaObs_idxFreeU hH G (arenaKick W p)
  have hc := continuous_arenaObs_idxFreeU hH G p
  have e' : freeShift hH G z (arenaKick W p) t - freeShift hH G z (arenaKick W p) s
      = -2 * z * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) (arenaKick W p)) := by
    rw [freeShift, freeShift, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc'.intervalIntegrable _ _)
        (hc'.intervalIntegrable _ _)]
  have e : freeShift hH G z p t - freeShift hH G z p s
      = -2 * z * ∫ u in s..t, arenaObs G (arenaKick (idxFreeU hH u) p) := by
    rw [freeShift, freeShift, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have split : (freeShift hH G z (arenaKick W p) t - freeShift hH G z p t)
        - (freeShift hH G z (arenaKick W p) s - freeShift hH G z p s)
      = -2 * z * ∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH u) (arenaKick W p))
            - arenaObs G (arenaKick (idxFreeU hH u) p)) := by
    rw [intervalIntegral.integral_sub (hc'.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    linear_combination e' - e
  have b : |∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH u) (arenaKick W p))
      - arenaObs G (arenaKick (idxFreeU hH u) p))| ≤ 2 * ‖G‖ * ‖W.val - 1‖ * (t - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := 2 * ‖G‖ * ‖W.val - 1‖)
      (f := fun u => arenaObs G (arenaKick (idxFreeU hH u) (arenaKick W p))
        - arenaObs G (arenaKick (idxFreeU hH u) p)) (fun u _ => by
        rw [Real.norm_eq_abs]
        exact abs_arenaObs_kick_kick_sub_le (idxFreeU hH u) W G p)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at h
  rw [split, abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |z| * |∫ u in s..t, (arenaObs G (arenaKick (idxFreeU hH u) (arenaKick W p))
          - arenaObs G (arenaKick (idxFreeU hH u) p))|
      ≤ 2 * |z| * (2 * ‖G‖ * ‖W.val - 1‖ * (t - s)) :=
        mul_le_mul_of_nonneg_left b (by positivity)
    _ = 4 * |z| * ‖G‖ * ‖W.val - 1‖ * (t - s) := by ring

/-- The displacement from a turned ray moves, between two times, by at most what the
displacement from the ray moves, plus the drift. -/
theorem abs_freeShift_ray_sub_le (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ)
    (W : Matrix.unitaryGroup ν ℂ) (p : GenArena ν) {s t : ℝ} (hst : s ≤ t) :
    |freeShift hH G z (arenaKick W p) t - freeShift hH G z (arenaKick W p) s|
      ≤ |freeShift hH G z p t - freeShift hH G z p s|
        + 4 * |z| * ‖G‖ * ‖W.val - 1‖ * (t - s) := by
  have d := freeShift_ray_drift hH G z W p hst
  have e : freeShift hH G z (arenaKick W p) t - freeShift hH G z (arenaKick W p) s
      = ((freeShift hH G z (arenaKick W p) t - freeShift hH G z p t)
          - (freeShift hH G z (arenaKick W p) s - freeShift hH G z p s))
        + (freeShift hH G z p t - freeShift hH G z p s) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- ★★★ **A gated history at a turned ray.** If the displacement along the free orbit from
`p` has a gated history and moves by at most `c₀` while its gate is closed, then the
displacement from the ray turned by `W` has a gated history with error `δ + lam t_c` and
speed `v + lam`, for any `lam ≥ 4 |z| ‖G‖ ‖W − 1‖`, provided the error stays below `1/12`
and `c₀ + lam (t_c − t_b) ≤ 1/6`. -/
theorem IsGatedHistory.of_ray {R δ v ta tb tc c₀ lam z : ℝ} {p : GenArena ν}
    (hH : H.IsHermitian) (W : Matrix.unitaryGroup ν ℂ)
    (h : IsGatedHistory (freeShift hH G z p) R δ v ta tb tc)
    (hcl : ∀ s t, tb ≤ s → s ≤ t → t ≤ tc →
      |freeShift hH G z p t - freeShift hH G z p s| ≤ c₀)
    (hrate : 4 * |z| * ‖G‖ * ‖W.val - 1‖ ≤ lam)
    (hδ : δ + lam * tc < 1 / 12) (hc : c₀ + lam * (tc - tb) ≤ 1 / 6) :
    IsGatedHistory (freeShift hH G z (arenaKick W p)) R (δ + lam * tc) (v + lam) ta tb
      tc := by
  have hlam : 0 ≤ lam := le_trans (by positivity) hrate
  have r := h.of_drift (D' := freeShift hH G z (arenaKick W p)) (η₀ := 0) hcl hlam
    (fun s t _ hst _ => (freeShift_ray_drift hH G z W p hst).trans
      (mul_le_mul_of_nonneg_right hrate (sub_nonneg.2 hst)))
    (by rw [freeShift_zero, freeShift_zero, sub_zero, abs_zero])
    (by rw [add_zero]; exact hδ) hc
  simpa only [add_zero] using r

/-- ★★★ **An away history at a turned ray.** The same for an away history, which moves by at
most `c₁` while its gate is closed again: start error `η₀ + lam t₅`, error `η + lam t₅`,
speed `v + lam`, the same offset. The band for the enlarged error is a hypothesis. -/
theorem IsAwayHistory.of_ray {R c v η₀ η ta tb t3 t4 t5 c₁ lam z : ℝ} {p : GenArena ν}
    (hH : H.IsHermitian) (W : Matrix.unitaryGroup ν ℂ)
    (h : IsAwayHistory (freeShift hH G z p) R c v η₀ η ta tb t3 t4 t5)
    (hcl : ∀ a b, t4 ≤ a → a ≤ b → b ≤ t5 →
      |freeShift hH G z p b - freeShift hH G z p a| ≤ c₁)
    (hrate : 4 * |z| * ‖G‖ * ‖W.val - 1‖ ≤ lam)
    (hη₀ : η₀ + lam * t5 < 1 / 12) (hη : η + lam * t5 < 1 / 12)
    (hband : (-1 / 6 + (η + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c ≤ 1 / 6 - (η + lam * t5))
      ∨ (-1 / 2 + (η + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c < -1 / 6 - (η + lam * t5)))
    (hc : c₁ + lam * (t5 - t4) ≤ 1 / 6) :
    IsAwayHistory (freeShift hH G z (arenaKick W p)) R c (v + lam) (η₀ + lam * t5)
      (η + lam * t5) ta tb t3 t4 t5 := by
  have hlam : 0 ≤ lam := le_trans (by positivity) hrate
  have r := h.of_drift (D' := freeShift hH G z (arenaKick W p)) (ρ₀ := 0) hcl hlam
    (fun s t _ hst _ => (freeShift_ray_drift hH G z W p hst).trans
      (mul_le_mul_of_nonneg_right hrate (sub_nonneg.2 hst)))
    (by rw [freeShift_zero, freeShift_zero, sub_zero, abs_zero])
    (by rw [add_zero]; exact hη₀) (by rw [add_zero]; exact hη)
    (by simpa only [add_zero] using hband) hc
  simpa only [add_zero] using r

end CSD.RecordLayer

end
