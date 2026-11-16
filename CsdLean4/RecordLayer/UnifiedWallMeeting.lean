/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallRelay

/-!
# The meeting histories: the moving observer arrives at the observer at rest

**Category:** 7-SigmaLayer (the record layer). BACKLOG #422 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 6 of the research delivery
plan of 2026-11-16, the fourth and fifth of the five histories. No new assumption beyond
UA-18.

The two meeting pointers of UA-18 (d) are coupled, one to each observer's clock, through the
gate "the two observers are *not* near each other": each ticks from the start until the
observers meet. This module proves both histories for the wall states: the moving clock of
#409 and the clock at rest of #408 translated to its place.

* `arenaObs_coincProj_prodRay_swap` — exchanging the two carriers and reversing the relation
  leaves the coincidence weight unchanged;
* ★ `moving_clock_outside_le` — the moving clock's wall state outside its two double arcs;
* ★★ `wall_meeting_gate_weights` — the weight inside `wallNear w` between the two clocks is
  at most `ε` while they are apart, and the weight outside it at most `ε` while they are
  together;
* ★★★ `wall_meeting_history_moving` — the meeting pointer on the moving clock: a gated
  history at the moving rate, for some strength `0 < g ≤ R_B/5`;
* ★★★ `wall_meeting_history_rest` — the meeting pointer on the clock at rest: a gated history
  at the rest rate, for some strength `0 < g ≤ R₀/5`.

## Exact scope

* **Conditions on predicted angles over two intervals are hypotheses**, with the sizes, as
  #420 and #421.
* **Each history has its own strength.** The moving clock's two other pointers (#420) and
  this one are coupled to the same clock; that the three strengths can be taken equal is
  true (each is the strength the swing theorem provides for that clock and index `j`) but
  is not stated: each theorem asserts the existence of a strength.
* **The other clock's wall state must be non-zero** at its packet time; a hypothesis here,
  supplied by the other clock's swing theorem.
* **Two clocks, uncoupled orbits from a product start**, on the fibres where the profiles
  vanish; displacements, not counts.
* **The meeting window is short**: the two are together only while the moving one passes.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-163, UD-170, UD-185, UD-187, UD-189, UD-190, UD-191, UD-192);
`RecordLayer/UnifiedWallRelay.lean` (#421: `gate_weight_le`,
`far_wall_clock_outside_wallArcs_le`); `RecordLayer/UnifiedWallObserver.lean` (#420:
`wallAngle`); `RecordLayer/UnifiedWallValues.lean` (#415: `wallGate_clocks_not_le`,
`wallGate_clocks_le`, `one_sub_sum_arenaObs_wallArcs_icoDevice_time_le`);
`RecordLayer/UnifiedWallHistories.lean` (#419: `isGatedHistory_coincShift`,
`coincProj_not_not`); `RecordLayer/UnifiedWallOrbits.lean` (#411:
`wall_moving_clock_swing_fine`); `RecordLayer/UnifiedRingShift.lean` (#417:
`far_wall_clock_swing_fine`); `RecordLayer/UnifiedGatedReading.lean` (#394:
`arenaObs_coincProj_prodRay`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

section Swap

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]

/-- Exchanging the two carriers and reversing the relation leaves the coincidence weight
unchanged. -/
theorem arenaObs_coincProj_prodRay_swap (p : GenArena ι) (q : GenArena κ) :
    arenaObs (coincProj τ σ fun s s' => r s' s) (prodRay q p)
      = arenaObs (coincProj σ τ r) (prodRay p q) := by
  rw [arenaObs_coincProj_prodRay, arenaObs_coincProj_prodRay, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  split_ifs
  · exact mul_comm _ _
  · rfl

end Swap

section Meeting

variable {n N M : ℕ}

/-- ★ **The moving clock's wall state stays in its two double arcs.** The form of #415's
bound for the flat window of #392. -/
theorem moving_clock_outside_le (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
      t₁ ≠ 0) {δ : ℝ} (hδ : Real.cos δ < 1) (s : ℝ) :
    (1 - ∑ k ∈ wallArc (M + 1) (wallAngle n N 1 (1 / 2) (t₁ + s)) δ
          ∪ wallArc (M + 1) (wallAngle n N (1 + Δ) (1 / 2) (t₁ + s)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N 1 (t₁ + s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
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
  unfold wallAngle
  exact one_sub_sum_arenaObs_wallArcs_icoDevice_time_le (lo := 600 * (n : ℤ) * N)
    (p₀ := 1 / 2) hn hN hM hΔ0 hlc hhc (by rw [abs_of_pos (by norm_num)]) hWDc t₁ hΨ hδ s

/-- ★★ **The wall gate between the clock at rest and the moving clock.** If the gate's bound
is at most `ε (1 − cos δ)` up to `t_c`, the place of the clock at rest is more than `w + 2δ`
from both levels of the moving clock and from their mirror images on `[0, t_a]`, and within
`w − 2δ` of both on `[t_b, t_c]`: the weight inside `wallNear w` is at most `ε` on the first
interval and the weight outside it at most `ε` on the second. -/
theorem wall_meeting_gate_weights (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (h : ZMod (M + 1)) (tA tB : ℝ)
    (hΨA : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) tA ≠ 0)
    (hΨB : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
      tB ≠ 0) {w δ ε ta tb tc : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      4 * lightBudget n N 1 (tA + s) + 4 * lightBudget n N 1 (tB + s)
        ≤ ε * (1 - Real.cos δ))
    (hapart : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N 1 (1 / 2) (tB + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            + wallAngle n N 1 (1 / 2) (tB + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N (1 + Δ) (1 / 2) (tB + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            + wallAngle n N (1 + Δ) (1 / 2) (tB + s)) < Real.cos (w + 2 * δ))
    (hnear : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N 1 (1 / 2) (tB + s))
        ∧ Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N (1 + Δ) (1 / 2) (tB + s))) :
    (∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨB))) ≤ ε)
    ∧ (∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨB))) ≤ ε) := by
  have hcos : 0 < 1 - Real.cos δ := by linarith only [hδ]
  refine ⟨fun s hs0 hs => ?_, fun s hbs hs => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hapart s hs0 hs
    exact gate_weight_le hcos
      (wallGate_clocks_le hδ0 (by linarith only [hw, hδ0]) hwπ a1 a2 a3 a4 a1 a2 a3 a4 _ _)
      (far_wall_clock_outside_wallArcs_le hn hN hM hΔ0 h tA hΨA hδ s)
      (moving_clock_outside_le hn hN hM hΔ0 tB hΨB hδ s)
      (hbudget s hs0 (hs.trans (hab.trans hbc)))
  · obtain ⟨n1, n2⟩ := hnear s hbs hs
    exact gate_weight_le hcos
      (wallGate_clocks_not_le hδ0 hw (by linarith only [hw, hwπ, hδ0]) n1 n2 n1 n2 _ _)
      (far_wall_clock_outside_wallArcs_le hn hN hM hΔ0 h tA hΨA hδ s)
      (moving_clock_outside_le hn hN hM hΔ0 tB hΨB hδ s)
      (hbudget s (hta.trans (hab.trans hbs)) hs)

/-- ★★★ **The meeting history on the moving clock.** The clock at rest translated by `h`
(packet time `t_A`) and the moving clock prepared a quarter turn early. Under the hypotheses
of `wall_meeting_gate_weights`, with `t_a ≤ 2π n/(j R_B)`,
`1/(24 j) + 2 (R_B/5) ε t_a < 1/12` and `2 (R_B/5) ε (t_c − t_b) ≤ 1/6`: for some strength
`0 < g ≤ R_B/5` the displacement of the pointer coupled to the moving clock through "the two
are not near" is a gated history at the moving rate `R_B`. -/
theorem wall_meeting_history_moving {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    (h : ZMod (M + 1)) (tA : ℝ)
    (hΨA : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) tA ≠ 0)
    {w δ ε ta tb tc : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hT : ta ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M (1 / 2) Δ))
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      4 * lightBudget n N 1 (tA + s)
          + 4 * lightBudget n N 1
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)
        ≤ ε * (1 - Real.cos δ))
    (hapart : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) + wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) + wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
          < Real.cos (w + 2 * δ))
    (hnear : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N 1 (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s))
        ∧ Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N (1 + Δ) (1 / 2)
            (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ)) + s)))
    (hE : 1 / (24 * (j : ℝ)) + 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * ta
      < 1 / 12)
    (hcl : 2 * (ringRate (1200 * n * N) M (1 / 2) Δ / 5) * ε * (tc - tb) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨB : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ IsGatedHistory
          (coincShift
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun k k' => ¬ wallNear (M + 1) w k k')
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB))
          (ringRate (1200 * n * N) M (1 / 2) Δ) (1 / (24 * (j : ℝ)) + 2 * g * ε * ta)
          (2 * g) ta tb tc := by
  have hn : 0 < n := hj.trans_le hjn
  have hK : 0 < 1200 * n * N := by positivity
  have hR : Δ / 2 ≤ ringRate (1200 * n * N) M (1 / 2) Δ :=
    half_le_levelClockRate hΔ0.le
      (ringSigma_sq_le hK M (by rw [abs_of_pos (by norm_num)]; norm_num))
  have hR0 : 0 < ringRate (1200 * n * N) M (1 / 2) Δ := by linarith only [hR, hΔ0]
  obtain ⟨g, hΨB, hg0, hg5, hsw⟩ := wall_moving_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ
  set R := ringRate (1200 * n * N) M (1 / 2) Δ with hRd
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hzabs : |(-g : ℝ)| = g := by rw [abs_neg, abs_of_pos hg0]
  have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
  obtain ⟨key_apart, key_near⟩ := wall_meeting_gate_weights hn hN hM hΔ0 h tA
    (-(Real.pi / (2 * R))) hΨA hΨB hδ0 hδ hw hwπ hta hab hbc hbudget hapart hnear
  have hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * -g * (∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨB)))
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
  have H := isGatedHistory_coincShift
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k k')
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-g)
    (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (deviceRay _ hΨB) (R := R)
    (δ₀ := 1 / (24 * (j : ℝ))) (ε := ε) (ta := ta) (tb := tb) (tc := tc) hR0 he0 hε hta hab
    hbc hclock
    (fun s hs0 hs => by
      have h1 := key_apart s hs0 hs
      rw [← coincProj_not_not (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)] at h1
      exact h1)
    key_near (by rw [hzabs]; linarith only [hcl, m2]) (by rw [hzabs]; linarith only [hE, m1])
  rw [hzabs] at H
  exact ⟨g, hΨB, hg0, hg5, H⟩

/-- ★★★ **The meeting history on the clock at rest.** The moving clock (packet time `t_B`)
and the clock at rest translated by `h`, prepared a quarter turn early. Under the hypotheses
of `wall_meeting_gate_weights`, with `t_a ≤ 2π n/(j R₀)`,
`1/(24 j) + 2 (R₀/5) ε t_a < 1/12` and `2 (R₀/5) ε (t_c − t_b) ≤ 1/6`: for some strength
`0 < g ≤ R₀/5` the displacement of the pointer coupled to the clock at rest through "the two
are not near" is a gated history at the rest rate `R₀`. The moving clock is the first
carrier here and the relation is reversed, as `tri_radar_lorentz` (#405) has it. -/
theorem wall_meeting_history_rest {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    (h : ZMod (M + 1)) (tB : ℝ)
    (hΨB : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
      tB ≠ 0) {w δ ε ta tb tc : ℝ} (hδ0 : 0 ≤ δ) (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hT : ta ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M 0 Δ))
    (hbudget : ∀ s, 0 ≤ s → s ≤ tc →
      4 * lightBudget n N 1 (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ)) + s)
          + 4 * lightBudget n N 1 (tB + s)
        ≤ ε * (1 - Real.cos δ))
    (hapart : ∀ s, 0 ≤ s → s ≤ ta →
      Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) - wallAngle n N 1 (1 / 2) (tB + s))
          < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            + wallAngle n N 1 (1 / 2) (tB + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N (1 + Δ) (1 / 2) (tB + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            + wallAngle n N (1 + Δ) (1 / 2) (tB + s)) < Real.cos (w + 2 * δ))
    (hnear : ∀ s, tb ≤ s → s ≤ tc →
      Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N 1 (1 / 2) (tB + s))
        ∧ Real.cos (w - 2 * δ)
          ≤ Real.cos ((0 + 2 * Real.pi * h.val / (M + 1 : ℕ))
            - wallAngle n N (1 + Δ) (1 / 2) (tB + s)))
    (hE : 1 / (24 * (j : ℝ)) + 2 * (ringRate (1200 * n * N) M 0 Δ / 5) * ε * ta < 1 / 12)
    (hcl : 2 * (ringRate (1200 * n * N) M 0 Δ / 5) * ε * (tc - tb) ≤ 1 / 6) :
    ∃ (g : ℝ) (hΨA : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M 0 Δ / 5
      ∧ IsGatedHistory
          (coincShift
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
            (gateOp (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
              (fun k k' => ¬ wallNear (M + 1) w k' k)
              (levelSwap (ZMod (M + 1) × Fin 2))) (-g)
            (deviceRay _ hΨB) (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)))
          (ringRate (1200 * n * N) M 0 Δ) (1 / (24 * (j : ℝ)) + 2 * g * ε * ta) (2 * g)
          ta tb tc := by
  have hn : 0 < n := hj.trans_le hjn
  have hR0 : 0 < ringRate (1200 * n * N) M 0 Δ := by
    rw [ringRate_zero _ _ hΔ0.le]
    exact hΔ0
  obtain ⟨g, hΨA, hg0, hg5, hsw⟩ := far_wall_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ h
  set R := ringRate (1200 * n * N) M 0 Δ with hRd
  have hz : (scaledTrainF_periodic g).deriv_periodic.lift (0 : AddCircle (1 : ℝ)) = -g :=
    scaledTrainF_deriv_lift_zero g
  have hzabs : |(-g : ℝ)| = g := by rw [abs_neg, abs_of_pos hg0]
  have he0 : (0 : ℝ) ≤ 1 / (24 * (j : ℝ)) := by positivity
  obtain ⟨key_apart, key_near⟩ := wall_meeting_gate_weights hn hN hM hΔ0 h
    (-(Real.pi / (2 * R))) tB hΨA hΨB hδ0 hδ hw hwπ hta hab hbc hbudget hapart hnear
  have hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * -g * (∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
              (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
              (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA))))
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
  have H := isGatedHistory_coincShift
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
    (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (fun k k' => ¬ wallNear (M + 1) w k' k)
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
    (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)) hY (-g)
    (deviceRay _ hΨB) (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨA)) (R := R)
    (δ₀ := 1 / (24 * (j : ℝ))) (ε := ε) (ta := ta) (tb := tb) (tc := tc) hR0 he0 hε hta hab
    hbc hclock
    (fun s hs0 hs => by
      have h1 := key_apart s hs0 hs
      rw [← arenaObs_coincProj_prodRay_swap
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w),
        ← coincProj_not_not (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun s s' => wallNear (M + 1) w s' s)] at h1
      exact h1)
    (fun s hbs hs => by
      have h1 := key_near s hbs hs
      rw [← arenaObs_coincProj_prodRay_swap
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          (fun k k' => ¬ wallNear (M + 1) w k k')] at h1
      exact h1)
    (by rw [hzabs]; linarith only [hcl, m2]) (by rw [hzabs]; linarith only [hE, m1])
  rw [hzabs] at H
  exact ⟨g, hΨA, hg0, hg5, H⟩

end Meeting

end CSD.RecordLayer

end
