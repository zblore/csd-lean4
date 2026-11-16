/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedFastMessenger

/-!
# When the wall gate is open: the flow times of the emission, the absence and the return

**Category:** 7-SigmaLayer (the record layer). BACKLOG #414 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R3 of the list under
UD-164, second part. No new assumption beyond UA-18.

#411 and #413 show the wall gate open and closed under conditions on predicted angles. On
the ring whose mirror-odd sector is the walled chain, a carrier that starts at the angle `−d`
and moves at the angular speed `u` has the predicted angle `u s − d`; it passes the wall at
`s = d/u` and its positive angles are the reflected leg. This module turns the angle
conditions into intervals of the flow time for two carriers that start together, and gives
the gate for the return, where the messenger is near the *mirror image* of the clock.

* `cos_lt_cos_of_lt_abs`;
* ★ `gate_open_at_emission` — the two angles are within `w − 2δ` while
  `(u − v) s ≤ w − 2δ`;
* ★ `gate_closed_away` — they are more than `w + 2δ` apart both ways round while
  `w + 2δ < (u − v) s` and `(u + v) s + (w + 2δ) < 2d`;
* `add_mul_sub_crossReturn`, ★ `gate_open_at_return` — the messenger is within `w − 2δ` of
  the clock's mirror image while `|s − 2d/(u + v)| ≤ (w − 2δ)/(u + v)`: the return of #412;
* `wallArc_neg`, ★★ `wallGate_not_le_mirror` — the wall gate for any rays when the
  messenger's angle is near the mirror image of the clock's;
* ★★★ `light_wall_gate_open_return` — the wall gate between the light messenger's wall state
  and a flat clock wall state is open while the messenger's predicted angle is within
  `w − 2δ` of the mirror images of both levels' predicted angles.

## Exact scope

* **Arithmetic of two carriers on straight lines**, with the conditions of #410 as its
  conclusions. It does not say at which flow time a gated pointer's count stops: that is the
  closing interval `[t_a, t_b]` of the history theorems, here
  `[(w − 2δ)/(u − v), (w + 2δ)/(u − v)]` for the emission.
* **One clock level at a time.** The clock's two levels have slightly different angular
  speeds; the lemmas are to be applied to each and the intervals intersected. That is not
  done.
* **Angles in half a turn.** The bounds ask `(u − v) s ≤ π` and `2d ≤ π`: the run stays in
  one half of the ring, away from the far wall.
* **Not joined to #412's tolerances.** `crossReturn` is the centre of the return interval;
  the distance of the interval's ends from `T_Ret` follows from `abs_crossReturn_sub_le` and
  the half-width `(w − 2δ)/(u + v)`, and is not stated as one bound.
* **The return gate is for a messenger and one clock, uncoupled orbits, angles**, as #413.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-178, UD-179, UD-181, UD-182, UD-183);
`RecordLayer/UnifiedFastMessenger.lean` (#413: `light_wall_gate_open`,
`one_sub_sum_arenaObs_wallArc_lightWall_le`, `lightBudget`);
`RecordLayer/UnifiedEmissionValues.lean` (#397: `cos_le_cos_of_abs_le`);
`RecordLayer/UnifiedWallGate.lean` (#410: `wallNear`, `wallArc`, `wallGate_not_le`);
`RecordLayer/UnifiedRadarTimes.lean` (#412: `crossReturn`, `abs_crossReturn_sub_le`);
`RecordLayer/UnifiedWallOrbits.lean` (#411: `one_sub_sum_arenaObs_wallArcs_icoDevice_le`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### From angles to flow times -/

theorem cos_lt_cos_of_lt_abs {θ a : ℝ} (ha : 0 ≤ a) (hθ : |θ| ≤ Real.pi) (h : a < |θ|) :
    Real.cos θ < Real.cos a := by
  rw [← Real.cos_abs θ]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi ha hθ h

/-- ★ **The gate is open at the emission.** Two carriers that start together at the angle
`−d` with angular speeds `v ≤ u` are within `w − 2δ` of each other while
`(u − v) s ≤ w − 2δ`. -/
theorem gate_open_at_emission {u v d w δ s : ℝ} (huv : v ≤ u) (hwπ : w - 2 * δ ≤ Real.pi)
    (hs0 : 0 ≤ s) (hs : (u - v) * s ≤ w - 2 * δ) :
    Real.cos (w - 2 * δ) ≤ Real.cos ((u * s - d) - (v * s - d)) := by
  refine cos_le_cos_of_abs_le ?_ hwπ
  rw [show (u * s - d) - (v * s - d) = (u - v) * s by ring,
    abs_of_nonneg (mul_nonneg (sub_nonneg.2 huv) hs0)]
  exact hs

/-- ★ **The gate is closed while the messenger is away.** The two carriers are more than
`w + 2δ` apart, and the messenger is more than `w + 2δ` from the other's mirror image, while
`w + 2δ < (u − v) s ≤ π` and `(u + v) s + (w + 2δ) < 2d ≤ π`. -/
theorem gate_closed_away {u v d w δ s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hwδ : 0 ≤ w + 2 * δ)
    (hs0 : 0 ≤ s) (h1 : w + 2 * δ < (u - v) * s) (h1π : (u - v) * s ≤ Real.pi)
    (h2 : (u + v) * s + (w + 2 * δ) < 2 * d) (h2π : 2 * d ≤ Real.pi) :
    Real.cos ((u * s - d) - (v * s - d)) < Real.cos (w + 2 * δ)
      ∧ Real.cos ((u * s - d) + (v * s - d)) < Real.cos (w + 2 * δ) := by
  have hpos : 0 ≤ (u - v) * s := by linarith
  have huvs : 0 ≤ (u + v) * s := mul_nonneg (add_nonneg hu hv) hs0
  constructor
  · refine cos_lt_cos_of_lt_abs hwδ ?_ ?_
    · rw [show (u * s - d) - (v * s - d) = (u - v) * s by ring, abs_of_nonneg hpos]
      exact h1π
    · rw [show (u * s - d) - (v * s - d) = (u - v) * s by ring, abs_of_nonneg hpos]
      exact h1
  · have hneg : (u * s - d) + (v * s - d) ≤ 0 := by linarith
    refine cos_lt_cos_of_lt_abs hwδ ?_ ?_
    · rw [abs_of_nonpos hneg]
      linarith
    · rw [abs_of_nonpos hneg]
      linarith

/-- The sum of the two angles is the angular speed of approach times the time from the
return of #412. -/
theorem add_mul_sub_crossReturn {u v : ℝ} (d s : ℝ) (huv : u + v ≠ 0) :
    (u * s - d) + (v * s - d) = (u + v) * (s - crossReturn d u v) := by
  rw [crossReturn, mul_sub, mul_div_cancel₀ _ huv]
  ring

/-- ★ **The gate is open at the return.** The messenger, reflected, is within `w − 2δ` of
the mirror image of the other carrier while `|s − 2d/(u + v)| ≤ (w − 2δ)/(u + v)`. -/
theorem gate_open_at_return {u v d w δ s : ℝ} (huv : 0 < u + v) (hwπ : w - 2 * δ ≤ Real.pi)
    (hs : |s - crossReturn d u v| ≤ (w - 2 * δ) / (u + v)) :
    Real.cos (w - 2 * δ) ≤ Real.cos ((u * s - d) + (v * s - d)) := by
  refine cos_le_cos_of_abs_le ?_ hwπ
  rw [add_mul_sub_crossReturn d s huv.ne', abs_mul, abs_of_pos huv]
  calc (u + v) * |s - crossReturn d u v|
      ≤ (u + v) * ((w - 2 * δ) / (u + v)) := mul_le_mul_of_nonneg_left hs huv.le
    _ = w - 2 * δ := mul_div_cancel₀ _ huv.ne'

/-! ### The wall gate at the return -/

section Mirror

theorem wallArc_neg (L : ℕ) [NeZero L] (x δ : ℝ) : wallArc L (-x) δ = wallArc L x δ := by
  rw [wallArc, wallArc, neg_neg, Finset.union_comm]

variable {M : ℕ}

/-- ★★ **Near the mirror image: little weight outside the relation.** As `wallGate_not_le`,
when the messenger's angle `x` is within `w − 2δ` of the mirror images `−y₀`, `−y₁` of the
clock's two angles. -/
theorem wallGate_not_le_mirror {w δ x y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w)
    (hwπ : w ≤ Real.pi) (h0 : Real.cos (w - 2 * δ) ≤ Real.cos (x + y₀))
    (h1 : Real.cos (w - 2 * δ) ≤ Real.cos (x + y₁))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        fun k k' => ¬ wallNear (M + 1) w k k') (prodRay p q)
      ≤ (1 - ∑ k ∈ wallArc (M + 1) x δ,
            arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k) p)
        + (1 - ∑ k ∈ wallArc (M + 1) y₀ δ ∪ wallArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  have h := wallGate_not_le (M := M) (y₀ := -y₀) (y₁ := -y₁) hδ hw hwπ
    (by rwa [sub_neg_eq_add]) (by rwa [sub_neg_eq_add]) p q
  rwa [wallArc_neg, wallArc_neg] at h

variable {n N : ℕ}

/-- ★★★ **The wall gate is open at the return.** A flat messenger wall state of rest energy
`0 < μ ≤ 1` and a flat clock wall state, at a flow time `s` with the clock's packet time
within `4π n/Δ`. If the messenger's predicted angle is within `w − 2δ` of the mirror images
of both levels' predicted angles: (weight outside `wallNear w`) `· (1 − cos δ)
≤ 4 · lightBudget n N μ (t₀ + s) + 4 (1/N + 1/(20000 Δ n N))`. -/
theorem light_wall_gate_open_return (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo lc : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M)
    (hlc : 0 < lc) (hhc : 2 * (lc + N) ≤ M) {p₀ q₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hq₀ : |q₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    (hWDc : ∀ m ∈ Finset.Ico lc (lc + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - q₀| ≤ 1 / (600 * n)) (t₀ t₁ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lc (lc + N) ∪ negWin (Finset.Ico lc (lc + N)))
      (oddExt (Finset.Ico lc (lc + N)) (flatAmpN N)) t₁ ≠ 0) {w δ s : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w) (hwπ : w ≤ Real.pi)
    (ht₁ : |t₁ + s| ≤ 4 * Real.pi * n / Δ)
    (h0 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          + 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * q₀) * (t₁ + s)))
    (h1 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          + 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * q₀) * (t₁ + s))) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
        * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N μ (t₀ + s) + 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hpos : 0 ≤ 1 - Real.cos δ := by linarith
  have g := mul_le_mul_of_nonneg_right (wallGate_not_le_mirror hδ0 hw hwπ h0 h1
    (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
    (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) hpos
  have a := one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀ hψ
    hδ s
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_le hn hN hM hΔ0 hΔ hlc hhc hq₀ hWDc t₁ hΨ
    hδ ht₁
  rw [add_mul] at g
  linarith

end Mirror

end CSD.RecordLayer

end
