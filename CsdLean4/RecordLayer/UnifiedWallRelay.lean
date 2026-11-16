/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallObserver

/-!
# The relay history: the messenger arrives at the observer at rest

**Category:** 7-SigmaLayer (the record layer). BACKLOG #421 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 6 of the research delivery
plan of 2026-11-16, the third of the five histories. No new assumption beyond UA-18.

The relay pointer of UA-18 (d) is coupled to the clock of the observer at rest, `A`, through
the gate "the messenger is *not* near `A`": it ticks from the start until the messenger
arrives. This module proves its history for the wall states: the light messenger of #413 and
the clock at rest of #408 translated to its place by #417.

* `gate_weight_le` — a gate's weight from two occupancy bounds and a budget;
* ★ `far_wall_clock_outside_wallArcs_le` — the translated clock's occupancy outside the
  double arc about its place;
* ★★ `wall_relay_gate_weights` — the weight inside `wallNear w` is at most `ε` while the
  messenger is away from `A`, and the weight outside it at most `ε` while it is there;
* ★★★ `wall_relay_history` — for some strength `0 < g ≤ R₀/5` the relay displacement is a
  gated history at the rest rate `R₀`, with error `1/(24 j) + 2 g ε t_a`.

## Exact scope

* **Conditions on predicted angles over two intervals are hypotheses**, with the sizes, as
  #420. `wall_gate_apart_before` and `wall_gate_near_at` (#418) give them for straight
  motion; they are not discharged here.
* **`A` is the clock at rest translated by any `h`.** The far wall is the half turn.
* **The messenger and one clock**, uncoupled orbits from a product start on the fibres where
  the profiles vanish; a displacement, not a count.
* **The relay window is short.** The gate is closed only while the messenger is beside `A`;
  the reading window `[t_b, t_c]` lies inside that passage.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-163, UD-170, UD-182, UD-187, UD-189, UD-190, UD-191);
`RecordLayer/UnifiedWallObserver.lean` (#420: `wallAngle`, the same for the moving
observer); `RecordLayer/UnifiedWallHistories.lean` (#419: `isGatedHistory_coincShift`,
`coincProj_not_not`); `RecordLayer/UnifiedRingShift.lean` (#417:
`far_wall_clock_swing_fine`, `far_wall_clock_outside_le`, `deviceShift`);
`RecordLayer/UnifiedFastMessenger.lean` (#413:
`one_sub_sum_arenaObs_wallArc_lightWall_le`); `RecordLayer/UnifiedWallGate.lean` (#410:
`wallGate_not_le`, `wallGate_le`); `RecordLayer/UnifiedEventTimes.lean` (#418:
`wall_gate_apart_before`, `wall_gate_near_at`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-- A gate's weight from two occupancy bounds and a budget. -/
theorem gate_weight_le {W A B a b ε c : ℝ} (hc : 0 < c) (hg : W ≤ A + B) (ha : A * c ≤ a)
    (hb : B * c ≤ b) (hab : a + b ≤ ε * c) : W ≤ ε := by
  refine le_of_mul_le_mul_right ?_ hc
  have h := mul_le_mul_of_nonneg_right hg hc.le
  rw [add_mul] at h
  linarith only [h, ha, hb, hab]

section Relay

variable {n N M : ℕ}

/-- ★ **The translated clock at rest stays in the double arc about its place.** -/
theorem far_wall_clock_outside_wallArcs_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (h : ZMod (M + 1)) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) t₁ ≠ 0)
    {δ : ℝ} (hδ : Real.cos δ < 1) (s : ℝ) :
    (1 - ∑ k ∈ wallArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ
          ∪ wallArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)))) * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N 1 (t₁ + s) := by
  have hcos : 0 ≤ 1 - Real.cos δ := by linarith only [hδ]
  have b := far_wall_clock_outside_le hn hN hM hΔ0 h t₁ hΨ hδ s
  have hsub : ringArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ
      ⊆ wallArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ
        ∪ wallArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ :=
    fun k hk => Finset.mem_union_left _ (mem_wallArc.2 (Or.inl hk))
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun k =>
    arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
      (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
        (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
        (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ))))
    (fun k _ _ => arenaObs_siteSel_nonneg _ k _)
  refine (mul_le_mul_of_nonneg_right ?_ hcos).trans b
  linarith only [hmono]

/-- ★★ **The wall gate between the light messenger and the observer at rest.** If the gate's
bound is at most `ε (1 − cos δ)` up to `t_c`, the messenger's predicted angle is more than
`w + 2δ` from `A`'s place and from its mirror image on `[0, t_a]`, and within `w − 2δ` of it
on `[t_b, t_c]`: the weight inside `wallNear w` is at most `ε` on the first interval and the
weight outside it at most `ε` on the second. -/
theorem wall_relay_gate_weights (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ} (hΔ0 : 0 < Δ) {lo : ℤ} (hlo : 0 < lo)
    (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ t₁ : ℝ)
    (h : ZMod (M + 1))
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) t₁ ≠ 0)
    {w δ ε ta tb tc : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      4 * lightBudget n N μ (t₀ + s) + 4 * lightBudget n N 1 (t₁ + s)
        ≤ ε * (1 - Real.cos δ))
    (hapart : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (wallAngle n N μ p₀ (t₀ + s) - (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)))
          < Real.cos (w + 2 * δ))
    (hnear : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (w - 2 * δ)
        ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s) - (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)))) :
    (∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)))) ≤ ε)
    ∧ (∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)))) ≤ ε) := by
  unfold wallAngle at hapart hnear
  have hcos : 0 < 1 - Real.cos δ := by linarith only [hδ]
  refine ⟨fun s hs0 hs => ?_, fun s hbs hs => ?_⟩
  · exact gate_weight_le hcos
      (wallGate_le hδ0 (by linarith only [hw, hδ0]) hwπ (hapart s hs0 hs).1 (hapart s hs0 hs).2
        (hapart s hs0 hs).1 (hapart s hs0 hs).2 _ _)
      (one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀ hψ hδ s)
      (far_wall_clock_outside_wallArcs_le hn hN hM hΔ0 h t₁ hΨ hδ s)
      (hbudget s hs0 (hs.trans (hab.trans hbc)))
  · exact gate_weight_le hcos
      (wallGate_not_le hδ0 hw (by linarith only [hw, hwπ, hδ0]) (hnear s hbs hs)
        (hnear s hbs hs) _ _)
      (one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀ hψ hδ s)
      (far_wall_clock_outside_wallArcs_le hn hN hM hΔ0 h t₁ hΨ hδ s)
      (hbudget s (hta.trans (hab.trans hbs)) hs)

/-- ★★★ **The relay history on the walled chain.** A light messenger wall state and the clock
at rest translated by `h`, prepared a quarter turn early. Under the hypotheses of
`wall_relay_gate_weights`, with `t_a ≤ 2π n/(j R₀)`, `1/(24 j) + 2 (R₀/5) ε t_a < 1/12` and
`2 (R₀/5) ε (t_c − t_b) ≤ 1/6`: for some strength `0 < g ≤ R₀/5` the displacement of the
pointer coupled to `A`'s clock through "the messenger is not near `A`" is a gated history at
the rest rate `R₀`, with error `1/(24 j) + 2 g ε t_a` and speed `2 g`. -/
theorem wall_relay_history {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M)
    {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ : ℝ)
    (h : ZMod (M + 1))
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0) {w δ ε ta tb tc : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1)
    (hw : 2 * δ ≤ w) (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε) (hta : 0 ≤ ta)
    (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hT : ta ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M 0 Δ))
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      4 * lightBudget n N μ (t₀ + s)
          + 4 * lightBudget n N 1 (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ)) + s)
        ≤ ε * (1 - Real.cos δ))
    (hapart : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos (wallAngle n N μ p₀ (t₀ + s) - (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos (wallAngle n N μ p₀ (t₀ + s) + (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)))
          < Real.cos (w + 2 * δ))
    (hnear : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (w - 2 * δ)
        ≤ Real.cos (wallAngle n N μ p₀ (t₀ + s) - (0 + 2 * Real.pi * h.val / (M + 1 : ℕ))))
    (hE : 1 / (24 * (j : ℝ)) + 2 * (ringRate (1200 * n * N) M 0 Δ / 5) * ε * ta < 1 / 12)
    (hcl : 2 * (ringRate (1200 * n * N) M 0 Δ / 5) * ε * (tc - tb) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M 0 Δ / 5
      ∧ IsGatedHistory
          (coincShift (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun k k' => ¬ wallNear (M + 1) w k k')
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g) (chainRay _ hψ)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)))
          (ringRate (1200 * n * N) M 0 Δ) (1 / (24 * (j : ℝ)) + 2 * g * ε * ta) (2 * g)
          ta tb tc := by
  have hn : 0 < n := hj.trans_le hjn
  have hR0 : 0 < ringRate (1200 * n * N) M 0 Δ := by
    rw [ringRate_zero _ _ hΔ0.le]
    exact hΔ0
  obtain ⟨g, hΨ, hg0, hg5, hsw⟩ := far_wall_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ h
  set R := ringRate (1200 * n * N) M 0 Δ with hRd
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hzabs : |(-g : ℝ)| = g := by rw [abs_neg, abs_of_pos hg0]
  have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
  obtain ⟨key_apart, key_near⟩ := wall_relay_gate_weights hn hN hM hμ0 hμ1 hΔ0 hlo hhi hp₀ hWD
    t₀ (-(Real.pi / (2 * R))) h hψ hΨ hδ0 hδ hw hwπ hta hab hbc hbudget hapart hnear
  have hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * -g * (∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
              (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ))))
          - 1 / 4 * (1 - Real.cos (R * t))| ≤ 1 / (24 * (j : ℝ)) := by
    intro t ht0 hta'
    have h1 := hsw t ht0 (hta'.trans hT)
    rw [clockPointerShift_trainF_eq, hz] at h1
    exact h1
  have m1 : 2 * g * ε * ta ≤ 2 * (R / 5) * ε * ta := by
    have : 0 ≤ ε * ta := mul_nonneg hε hta
    nlinarith only [this, hg5]
  have m2 : 2 * g * ε * (tc - tb) ≤ 2 * (R / 5) * ε * (tc - tb) := by
    have : 0 ≤ ε * (tc - tb) := mul_nonneg hε (sub_nonneg.2 hbc)
    nlinarith only [this, hg5]
  have hY : ∀ s' (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)),
      |arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s'
          * levelSwap (ZMod (M + 1) × Fin 2)) q|
        ≤ arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) s') q :=
    fun s' q => abs_arenaObs_siteSel_mul_levelSwap_le
      (fun x : ZMod (M + 1) × Fin 2 => x.1) s' q
  have H := isGatedHistory_coincShift (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')
    (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-g)
    (chainRay _ hψ) (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)) (R := R)
    (δ₀ := 1 / (24 * (j : ℝ))) (ε := ε) (ta := ta) (tb := tb) (tc := tc) hR0 he0 hε hta hab
    hbc hclock
    (fun s hs0 hs => by
      have h1 := key_apart s hs0 hs
      rw [← coincProj_not_not (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)] at h1
      exact h1)
    key_near (by rw [hzabs]; linarith only [hcl, m2]) (by rw [hzabs]; linarith only [hE, m1])
  rw [hzabs] at H
  exact ⟨g, hΨ, hg0, hg5, H⟩

end Relay

end CSD.RecordLayer

end
