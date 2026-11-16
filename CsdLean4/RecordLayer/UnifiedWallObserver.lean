/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallHistories
public import CsdLean4.RecordLayer.UnifiedEventTimes
public import CsdLean4.RecordLayer.UnifiedRingShift

/-!
# The moving observer's two radar histories on the walled chain

**Category:** 7-SigmaLayer (the record layer). BACKLOG #420 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Tasks 6 and 7 of the research
delivery plan of 2026-11-16, for the moving observer. No new assumption beyond UA-18.

`tri_radar_lorentz` (#405) asks for five histories. Two of them belong to the moving
observer `B` and the messenger: the emission pointer (gated by "the messenger is near `B`")
and the return pointer (gated by its complement). This module proves both for the wall
states: the light messenger of #413 and the moving clock of #409, with the clock's swing
of #411 and the gate bounds of #413, #414 and #415 put into the history theorems of #419.
The band of the return pointer, a hypothesis of #419, is derived from sizes: the emission
is at the start, so the emission pointer stops near `0`.

* `wallAngle` — the predicted angle of a packet at a packet time;
* ★★ `wall_observer_gate_weights` — the wall gate between the light messenger and the moving
  clock on three intervals: open, closed, open again;
* ★★★ `wall_observer_radar_histories` — for each strength `0 < g ≤ R/5` of the coupling:
  the emission displacement is a gated history with error `1/(24 j) + 2 g ε t_a`, and the
  return displacement is an away history whose offset is the emission displacement at
  `t_b`, with error `1/(24 j) + 2 g ε (t₃ − t_b)`. The band holds.

## Exact scope

* **The strength and the clock's swing bound are hypotheses** (since #423); the swing
  theorem of the clock provides a strength for which the bound holds.
* **Conditions on predicted angles over intervals are hypotheses** (`hnear`, `hapart`,
  `hback`), with the size conditions. #414 and #418 turn them into intervals of the flow
  time for straight motion; they are not discharged here, and no values are put in.
* **One strength for both pointers.** The two pointers are coupled to the same clock with
  the same strength `g`, the one the swing theorem provides.
* **The band is derived for an emission at the start**: the hypothesis `hband` bounds
  `(1/4)(1 − cos R t_a)` together with the errors by `1/12`, which needs `R t_a` small. A
  later emission is outside this theorem (decision (ii) of 2026-11-15 under UO-16).
* **The messenger and one clock**, on the fibres where the profiles vanish, from a product
  start. The other three histories (the relay and the two meeting pointers) involve the
  observer at rest and are not proved here.
* **Displacements, not counts.** The counts follow from `IsGatedHistory.exists_count` and
  `IsAwayHistory.exists_count` (#402) once the run is the five-pointer flow.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-163, UD-170, UD-180, UD-182, UD-183, UD-184, UD-189, UD-190);
`specs/unified-m6-feasibility.md` (§5); `RecordLayer/UnifiedWallHistories.lean` (#419:
`isGatedHistory_coincShift`, `isAwayHistory_coincShift`);
`RecordLayer/UnifiedFastMessenger.lean` (#413:
`one_sub_sum_arenaObs_wallArc_lightWall_le`, `lightBudget`);
`RecordLayer/UnifiedWallValues.lean` (#415:
`one_sub_sum_arenaObs_wallArcs_icoDevice_time_le`); `RecordLayer/UnifiedWallGate.lean`
(#410: `wallNear`, `wallGate_not_le`, `wallGate_le`); `RecordLayer/UnifiedGateTimes.lean`
(#414: `wallGate_not_le_mirror`); `RecordLayer/UnifiedWallOrbits.lean` (#411:
`wall_moving_clock_swing_fine`); `RecordLayer/UnifiedEmissionReading.lean` (#396:
`clockPointerShift_trainF_eq`, `scaledTrainF_deriv_lift_zero`, the ring's version of this
theorem); `RecordLayer/UnifiedGatedReading.lean` (#394:
`abs_arenaObs_siteSel_mul_levelSwap_le`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-- **The predicted angle of a packet** of rest energy `μ` and reference momentum `p` at the
packet time `t`, on the ring of length `2π · 1200 n N`. -/
def wallAngle (n N : ℕ) (μ p t : ℝ) : ℝ :=
  2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p) * t

section Observer

variable {n N M : ℕ}

/-- ★★ **The wall gate between the light messenger and the moving clock, on three
intervals.** If the gate's bound is at most `ε (1 − cos δ)` up to `t₅`, and the messenger's
predicted angle is within `w − 2δ` of both levels' mirror images on `[0, t_a]` (the clock
is prepared before the wall and moving into it), more than `w + 2δ` from
them and from their mirror images on `[t_b, t₃]`, and within `w − 2δ` of their mirror images
on `[t₄, t₅]`: the weight outside `wallNear w` is at most `ε` on the first and the third
interval, and the weight inside it is at most `ε` on the second. -/
theorem wall_observer_gate_weights (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ}
    (hΔ0 : 0 < Δ) {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M)
    {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ t₁ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
      t₁ ≠ 0) {w δ ε ta tb t3 t4 t5 : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (hta : 0 ≤ ta) (hab : ta ≤ tb) (hb3 : tb ≤ t3) (h34 : t3 ≤ t4) (h45 : t4 ≤ t5)
    (hbudget : ∀ s, 0 ≤ s → s ≤ t5 →
      4 * lightBudget n N μ (t₀ + s) + 4 * lightBudget n N 1 (t₁ + s)
        ≤ ε * (1 - Real.cos δ))
    (hnear : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2) (t₁ + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2) (t₁ + s)))
    (hapart : ∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (wallAngle n N μ p₀ (t₀ + s) - wallAngle n N 1 (1 / 2) (t₁ + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + wallAngle n N 1 (1 / 2) (t₁ + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) - wallAngle n N (1 + Δ) (1 / 2) (t₁ + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + wallAngle n N (1 + Δ) (1 / 2) (t₁ + s))
          < Real.cos (w + 2 * δ))
    (hback : ∀ s, t4 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2) (t₁ + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2) (t₁ + s))) :
    (∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε)
    ∧ (∀ s, tb ≤ s → s ≤ t3 →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε)
    ∧ (∀ s, t4 ≤ s → s ≤ t5 →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) ≤ ε) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  unfold wallAngle at hnear hapart hback
  have hcos : 0 < 1 - Real.cos δ := by linarith only [hδ]
  have hMz : (210000 : ℤ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hnN : (0 : ℤ) ≤ n * N := by positivity
  have hsq : (n : ℤ) * N ≤ n ^ 2 * N := by nlinarith only [hn1, hN1, hnN]
  have hNle : (N : ℤ) ≤ n * N := by nlinarith only [hn1, hN1]
  have hlc : (0 : ℤ) < 600 * (n : ℤ) * N := by nlinarith only [hn1, hN1]
  have hhc : 2 * (600 * (n : ℤ) * N + N) ≤ M := by linarith only [hMz, hsq, hNle, hnN]
  have hWDc : ∀ m ∈ Finset.Ico (600 * (n : ℤ) * N) (600 * (n : ℤ) * N + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - 1 / 2| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have hπ := Real.pi_pos
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      field_simp
    rw [e]
    exact flatWindow_width hn hN m hm
  have hout : ∀ s, 0 ≤ s → s ≤ t5 →
      ((1 - ∑ k ∈ wallArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)) δ,
          arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
            (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ)))
        + (1 - ∑ k ∈ wallArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * (1 / 2)) * (t₁ + s)) δ
            ∪ wallArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * (1 / 2))
                * (t₁ + s)) δ,
          arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))))
          * (1 - Real.cos δ)
        ≤ ε * (1 - Real.cos δ) := by
    intro s hs0 hs5
    have a := one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀
      hψ hδ s
    have b : (1 - ∑ k ∈ wallArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * (1 / 2)) * (t₁ + s)) δ
            ∪ wallArc (M + 1)
              (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * (1 / 2))
                * (t₁ + s)) δ,
          arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
          * (1 - Real.cos δ)
        ≤ 4 * lightBudget n N 1 (t₁ + s) :=
      one_sub_sum_arenaObs_wallArcs_icoDevice_time_le (lo := 600 * (n : ℤ) * N)
        (p₀ := 1 / 2) hn hN hM hΔ0 hlc hhc (by rw [abs_of_pos (by norm_num)]) hWDc t₁ hΨ hδ s
    have hb := hbudget s hs0 hs5
    rw [add_mul]
    linarith only [a, b, hb]
  refine ⟨fun s hs0 hs => ?_, fun s hbs hs => ?_, fun s h4s hs => ?_⟩
  · exact le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (wallGate_not_le_mirror hδ0 hw (by linarith only [hw, hwπ, hδ0]) (hnear s hs0 hs).1
          (hnear s hs0 hs).2 _ _) hcos.le).trans
        (hout s hs0 (hs.trans (hab.trans (hb3.trans (h34.trans h45)))))) hcos
  · exact le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (wallGate_le hδ0 (by linarith only [hw, hδ0]) hwπ (hapart s hbs hs).1
          (hapart s hbs hs).2.1 (hapart s hbs hs).2.2.1 (hapart s hbs hs).2.2.2 _ _)
        hcos.le).trans
        (hout s (hta.trans (hab.trans hbs)) (hs.trans (h34.trans h45)))) hcos
  · exact le_of_mul_le_mul_right
      ((mul_le_mul_of_nonneg_right
        (wallGate_not_le_mirror hδ0 hw (by linarith only [hw, hwπ, hδ0]) (hback s h4s hs).1
          (hback s h4s hs).2 _ _) hcos.le).trans
        (hout s (hta.trans (hab.trans (hb3.trans (h34.trans h4s)))) hs)) hcos

/-- ★★★ **The moving observer's emission and return histories on the walled chain.** A light
messenger wall state (rest energy `0 < μ ≤ 1`, `N` positive modes near `p₀`, packet time
`t₀`) and the moving clock's wall state (levels `1`, `1 + Δ`, momentum `1/2`, prepared a
quarter turn early). Suppose the gate's bound is at most `ε (1 − cos δ)` up to `t₅`; the
messenger's predicted angle is within `w − 2δ` of both levels' mirror images on `[0, t_a]`,
more than
`w + 2δ` from them and from their mirror images on `[t_b, t₃]`, and within `w − 2δ` of their
mirror images on `[t₄, t₅]`; and the sizes hold. Then for each strength `0 < g ≤ R/5` the
displacement of the pointer gated by `wallNear w` is a gated history, and the displacement
of the pointer gated by its complement is an away history with offset the first
displacement at `t_b`. -/
theorem wall_observer_radar_histories {j : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ}
    (hΔ0 : 0 < Δ) {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M)
    {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0) {w δ ε ta tb t3 t4 t5 : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε)
    (hta : 0 ≤ ta) (hab : ta ≤ tb) (hb3 : tb ≤ t3) (h34 : t3 ≤ t4) (h45 : t4 ≤ t5)
    (hT : t3 ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M (1 / 2) Δ))
    (hbudget : ∀ s, 0 ≤ s → s ≤ t5 →
      4 * lightBudget n N μ (t₀ + s)
          + 4 * lightBudget n N 1
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
        ≤ ε * (1 - Real.cos δ))
    (hnear : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)))
    (hapart : ∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (wallAngle n N μ p₀ (t₀ + s) - wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) - wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ))
    (hback : ∀ s, t4 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s)
          + wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)))
    (hcl3 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t3 - tb) ≤ 1 / 6)
    (hcl5 : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t5 - t4) ≤ 1 / 6)
    (hband : 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * ta))
        + 1 / (24 * (j : ℝ)) + 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * ta
        + 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * (tb - ta)
        + (1 / (24 * (j : ℝ)) + 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (t3 - tb))
      < 1 / 12) {g : ℝ} (hg0 : 0 < g)
    (hg5 : g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0)
    (hsw : ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M (1 / 2) Δ) →
      |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
            (0 : AddCircle (1 : ℝ))
            (deviceRay _ hΨ) t
          - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * t))|
        ≤ 1 / (24 * j)) :
    IsGatedHistory
          (coincShift (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g) (chainRay _ hψ) (deviceRay _ hΨ))
          (ringRate (1200 * n * N) M (1 / 2) Δ) (1 / (24 * (j : ℝ)) + 2 * g * ε * ta)
          (2 * g) ta tb t3
      ∧ IsAwayHistory
          (coincShift (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun k k' => ¬ wallNear (M + 1) w k k')
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g) (chainRay _ hψ) (deviceRay _ hΨ))
          (ringRate (1200 * n * N) M (1 / 2) Δ)
          (coincShift (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g) (chainRay _ hψ) (deviceRay _ hΨ) tb)
          (2 * g) (2 * g * ε * ta) (1 / (24 * (j : ℝ)) + 2 * g * ε * (t3 - tb))
          ta tb t3 t4 t5 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hK : 0 < 1200 * n * N := by positivity
  have hR : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hR0 : 0 < ringRate (1200 * n * N) M (1 / 2) Δ := by linarith
  set R := ringRate (1200 * n * N) M (1 / 2) Δ with hRd
  have hcos : 0 < 1 - Real.cos δ := by linarith only [hδ]
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hzabs : |(-g : ℝ)| = g := by rw [abs_neg, abs_of_pos hg0]
  have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
  obtain ⟨key_open, key_away, key_back⟩ := wall_observer_gate_weights hn hN hM hμ0 hμ1 hΔ0
    hlo hhi hp₀ hWD t₀ (-(Real.pi / (2 * R))) hψ hΨ hδ0 hδ hw hwπ hta hab hb3 h34 h45 hbudget
    hnear hapart hback
  -- the clock's own displacement
  have hclock : ∀ t, 0 ≤ t → t ≤ t3 →
      |-2 * -g * (∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
          - 1 / 4 * (1 - Real.cos (R * t))| ≤ 1 / (24 * (j : ℝ)) := by
    intro t ht0 ht3
    have h := hsw t ht0 (ht3.trans hT)
    rw [clockPointerShift_trainF_eq, hz] at h
    exact h
  -- sizes
  have hgG : g ≤ R / 5 := hg5
  have m1 : 2 * g * ε * ta ≤ 2 * (R / 5) * ε * ta := by
    have : 0 ≤ ε * ta := mul_nonneg hε hta
    nlinarith only [this, hgG]
  have m2 : 2 * g * ε * (t3 - tb) ≤ 2 * (R / 5) * ε * (t3 - tb) := by
    have : 0 ≤ ε * (t3 - tb) := mul_nonneg hε (sub_nonneg.2 hb3)
    nlinarith only [this, hgG]
  have m3 : 2 * g * ε * (t5 - t4) ≤ 2 * (R / 5) * ε * (t5 - t4) := by
    have : 0 ≤ ε * (t5 - t4) := mul_nonneg hε (sub_nonneg.2 h45)
    nlinarith only [this, hgG]
  have m4 : 2 * g * (tb - ta) ≤ 2 * (R / 5) * (tb - ta) := by
    have : 0 ≤ tb - ta := sub_nonneg.2 hab
    nlinarith only [this, hgG]
  have hcosR : 0 ≤ 1 / 4 * (1 - Real.cos (R * ta)) := by
    have := Real.cos_le_one (R * ta)
    linarith
  have hGa : 0 ≤ 2 * (R / 5) * ε * ta := by positivity
  have hG3 : 0 ≤ 2 * (R / 5) * ε * (t3 - tb) :=
    mul_nonneg (by positivity) (sub_nonneg.2 hb3)
  have hGab : 0 ≤ 2 * (R / 5) * (tb - ta) := mul_nonneg (by positivity) (sub_nonneg.2 hab)
  have hga : 0 ≤ 2 * g * ε * ta := by positivity
  have hg3 : 0 ≤ 2 * g * ε * (t3 - tb) := mul_nonneg (by positivity) (sub_nonneg.2 hb3)
  have hgab : 0 ≤ 2 * g * (tb - ta) := mul_nonneg (by positivity) (sub_nonneg.2 hab)
  have hY : ∀ s' (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)),
      |arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s'
          * levelSwap (ZMod (M + 1) × Fin 2)) q|
        ≤ arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s') q :=
    fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q
  -- the emission history
  have He := isGatedHistory_coincShift (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-g)
    (chainRay _ hψ) (deviceRay _ hΨ) (R := R) (δ₀ := 1 / (24 * (j : ℝ))) (ε := ε) (ta := ta)
    (tb := tb) (tc := t3) hR0 he0 hε hta hab hb3
    (fun t ht0 hta' => hclock t ht0 (hta'.trans (hab.trans hb3))) key_open key_away
    (by rw [hzabs]; linarith only [hcl3, m2])
    (by rw [hzabs]; linarith only [hband, m1, hcosR, hGab, hG3, he0])
  rw [hzabs] at He
  -- where the emission pointer stopped
  have hsa := He.swing ta hta le_rfl
  have hmid := He.mid ta tb le_rfl hab le_rfl
  rw [abs_le] at hsa hmid
  have Hr := isAwayHistory_coincShift (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-g)
    (chainRay _ hψ) (deviceRay _ hΨ) (R := R) (δ₀ := 1 / (24 * (j : ℝ))) (ε := ε) (ta := ta)
    (tb := tb) (t3 := t3) (t4 := t4) (t5 := t5) hR0 he0 hε hta hab hb3 h34 h45 hclock
    key_open key_away key_back
    (by rw [hzabs]; linarith only [hband, m1, hcosR, hGab, hG3, he0])
    (by rw [hzabs]; linarith only [hband, m2, hcosR, hGab, hGa, he0])
    (by rw [hzabs]; linarith only [hcl5, m3])
    (by
      rw [hzabs]
      left
      constructor <;>
        linarith only [hsa.1, hsa.2, hmid.1, hmid.2, hband, m1, m2, m4, hcosR, hga, hg3,
          hgab, he0])
  rw [hzabs] at Hr
  exact ⟨He, Hr⟩

end Observer

end CSD.RecordLayer

end
