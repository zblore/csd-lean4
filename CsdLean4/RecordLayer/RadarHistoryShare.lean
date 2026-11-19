/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerCountCap
public import CsdLean4.RecordLayer.UnifiedRadarMacrostate

/-!
# The radar's record history holds a share of the starts, and its counts satisfy the bounds

**Category:** 7-SigmaLayer. BACKLOG #439, fifth brick (obligation UO-25 (3), Task 3 of the plan
`specs/unified-records-spacetime-task-plans.md` §1).

`RecordLayer/PointerCountCap.lean` finds, for any set of starts, a capped history whose
compatible region holds the fraction `1 / (B + 1)^5` of the set; it does not say that the
history's counts satisfy the comparisons of `RadarCountBounds`.
`RecordLayer/UnifiedRadarPreparation.lean` shows that every start of the radar's start set
has counts that do. This module joins the two: a count of one orbit at one time is unique,
so the counts of the pigeonhole history are the counts of any start in its region.

* ★★ `TickReadout.exists_history_measure_ge_of_forall` — for a set of starts of non-zero
  measure in which every start has counts with a property `Q`, and counts capped at `B`:
  there are counts at most `B` with `Q` whose history's compatible region holds at least
  `1 / (B + 1)^k` of the set;
* ★★★ `csd_radar_history_share` — for the radar family: a set of starts of positive
  `μ_FS ⊗ vol⁵` measure such that, for all reading times in the five windows and every cap
  `B ≥ 12 max(|g_A|, |g_B|) s` for the five times `s`, there are five counts at most `B`
  that satisfy `RadarCountBounds` and whose history's compatible region holds at least
  `1 / (B + 1)^5` of the set.

## Honest scope

⚠️ **The counts are still not named.** They are found by a pigeonhole argument and may
depend on the labelling, the reference point, the times and the cap.

⚠️ **A share of the start set, not a value.** The measure of the start set itself is
positive with no value (`pentaMuL_radarStartSet_pos`), and the cap is a speed bound, far
above the family's counts.

⚠️ **The reading times are assumed non-negative.** The five windows of the family are not
shown here to lie in `t ≥ 0`; that is a hypothesis on the times chosen.

⚠️ **No stability of the cell under the flow** and no register: conditioning on the history
is the normalised restriction of the measure.

References: `specs/BACKLOG.md` #439; `specs/unified-record-spacetime-plan.md` (UO-25, UD-219,
UD-225, UD-232, UD-237); `specs/unified-records-spacetime-task-plans.md` (§1);
`RecordLayer/PointerCountCap.lean` (`TickReadout.exists_history_measure_ge`, `wallCount_le`);
`RecordLayer/UnifiedRadarPreparation.lean` (`radarStartSet`, `RadarCountBounds`,
`WallRadarGeometry.mem_compatibleSet_ray`); `RecordLayer/UnifiedDiracClockTicks.lean`
(`IsTickCount.unique`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.SigmaLayer MeasureTheory Set CSD.CV CSD.LF4

namespace CSD.RecordLayer

section Cells

universe u w

variable {X : Type w} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {D : ConstraintDynamics X} {ι : Type u} (A : TickReadout D ι)

/-- ★★ **A capped history with a property holds a share of a set of starts.** For readings
whose counts are capped at `B` from every start, and a set `S` of starts of non-zero measure
in which every start has counts with the property `Q`: there are counts `c j ≤ B` with `Q`
such that the compatible region of their history holds at least `1 / (B + 1)^k` of the
measure of `S`. -/
theorem TickReadout.exists_history_measure_ge_of_forall {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ)
    (hcap : ∀ j x n, HasTicks (A.rest (ctx j).1) (A.disp (ctx j).1) (fun s => D.flow s x)
      (ctx j).2 n → n ≤ B) {S : Set X} (hS : (D.muL : Measure X) S ≠ 0)
    (Q : (Fin k → ℕ) → Prop)
    (hQ : ∀ x ∈ S, ∃ c' : Fin k → ℕ, Q c'
      ∧ ∀ j, x ∈ A.countEvent (ctx j).1 (ctx j).2 (c' j)) :
    ∃ c : Fin k → Fin (B + 1), Q (fun j => (c j : ℕ))
      ∧ (D.muL : Measure X) S
        ≤ ((B + 1 : ℕ) : ENNReal) ^ k * (D.muL : Measure X)
            (S ∩ compatibleSet A.semantics
              (List.ofFn fun j => TickReadout.startFact (ctx j).1 (ctx j).2 (c j))) := by
  obtain ⟨c, hc⟩ := A.exists_history_measure_ge ctx B hcap S
  refine ⟨c, ?_, hc⟩
  have hne : (S ∩ compatibleSet A.semantics
      (List.ofFn fun j => TickReadout.startFact (ctx j).1 (ctx j).2 (c j))).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    rw [hem, measure_empty, mul_zero] at hc
    exact hS (le_antisymm hc zero_le)
  obtain ⟨x, hxS, hx⟩ := hne
  obtain ⟨c', hQ', hc'⟩ := hQ x hxS
  rw [A.compatibleSet_eq_preimage_singleton ctx B] at hx
  have hfun : c' = fun j => (c j : ℕ) := by
    funext j
    have h1 : x ∈ A.countEvent (ctx j).1 (ctx j).2 (c j) :=
      (A.tickCode_eq_castSucc_iff B (ctx j).1 (ctx j).2 x (c j)).1 (congrFun hx j)
    exact IsTickCount.unique (hc' j) h1
  rw [← hfun]
  exact hQ'

end Cells

section Family

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The radar's record history holds a share of the starts, and its counts satisfy the
bounds.** For `k ≥ 100` and a ring with an even number `M + 1 = 2H` of sites,
`M ≥ 210000 N³`: there are strengths `g_A, g_B > 0` such that for every labelling and every
reference point of the measure there is a set `S` of starts of positive `μ_FS ⊗ vol⁵`
measure with the following property. For every choice of non-negative flow times in the five
reading windows and every cap `B` with `12 max(|g_A|, |g_B|) s ≤ B` for the five times `s`,
there are five counts at most `B` which satisfy the comparisons of `RadarCountBounds` within
`152 K/k` and `53 K/k`, and whose five-fact history has a compatible region holding at least
`1 / (B + 1)^5` of the measure of `S`. -/
theorem csd_radar_history_share {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ gA gB : ℝ, 0 < gA ∧ 0 < gB
      ∧ ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
          × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1)),
        ∃ S : Set (PentaSigma D), 0 < pentaMuL p₀ S ∧
        ∀ se, famTb k ≤ se → se ≤ famT3 k → ∀ sr, famT4 k ≤ sr → sr ≤ famT5 k →
        ∀ sμ, famTbM k M ≤ sμ → sμ ≤ famTcM k M → ∀ sρ, famTbR k M ≤ sρ → sρ ≤ famTcR k M →
        ∀ sm, famTbM k M ≤ sm → sm ≤ famTcM k M →
        (∀ j : Fin 5, 0 ≤ ![se, sr, sμ, sρ, sm] j) →
        ∀ B : ℕ, (∀ j : Fin 5, 12 * max |gA| |gB| * ![se, sr, sμ, sρ, sm] j ≤ B) →
        ∃ Ne Nr Nμ Nρ Nm : ℕ, Ne ≤ B ∧ Nr ≤ B ∧ Nμ ≤ B ∧ Nρ ≤ B ∧ Nm ≤ B
          ∧ RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
              (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
              (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
              (53 * (wallK k / k)) Ne Nr Nμ Nρ Nm
          ∧ pentaMuL p₀ S ≤ ((B + 1 : ℕ) : ENNReal) ^ 5 * pentaMuL p₀
              (S ∩ compatibleSet
                (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
                  gA gB e p₀).semantics (radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm)) := by
  obtain ⟨hψ, gA, gB, hΨA, hΨB, a1, -, a3, -, hall⟩ := radar_family_lorentz_ray hk hM hH
  refine ⟨gA, gB, a1, a3, ?_⟩
  intro D e p₀
  have hX0 : (0 : ℝ) < k := by
    have : (100 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this]
  have hv := vRel_half_one
  have habs : |vRel 1 1 (1 / 2)| < 1 := by
    rw [abs_of_pos hv.1]
    linarith only [hv.2]
  have hr : (0 : ℝ) < 1 / (12000 * (k : ℝ) ^ 2) := by positivity
  have hρ : (0 : ℝ) < 1 / (24000 * (k : ℝ) ^ 2) := by positivity
  have hpos := pentaMuL_radarStartSet_pos e p₀
    (prodRay (chainRay _ hψ) (prodRay (deviceRay (deviceShift (H : ZMod (M + 1)) _)
      (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB))) hr hρ
  refine ⟨_, hpos, ?_⟩
  intro se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10 hτ B hB
  obtain ⟨c, hQ, hc⟩ :=
    (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
      gA gB e p₀).exists_history_measure_ge_of_forall
      (fun j : Fin 5 => (j, ![se, sr, sμ, sρ, sm] j)) B
      (fun j x m h => by
        have h1 := wallCount_le (wallN k) (wallN k) M (wallMu k) (wallGap k)
          (3 * wallDelta k) gA gB e p₀ j x (hτ j) h
        exact_mod_cast h1.trans (hB j))
      (S := radarStartSet e
        (prodRay (chainRay _ hψ) (prodRay (deviceRay (deviceShift (H : ZMod (M + 1)) _)
          (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB)))
        (1 / (12000 * (k : ℝ) ^ 2)) (1 / (24000 * (k : ℝ) ^ 2)))
      hpos.ne'
      (fun c' => RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
        (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
        (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
        (53 * (wallK k / k)) (c' 0) (c' 1) (c' 2) (c' 3) (c' 4))
      (by
        rintro x ⟨W, hW, θ, ψ, χ, ξ, ζ, hθ, hψ', hχ, hξ, hζ, rfl⟩
        obtain ⟨Ne, Nr, Nμ, Nρ, Nm, hx, hb⟩ :=
          ((hall W hW.le θ ψ χ ξ ζ hθ hψ' hχ hξ hζ).geometry habs).mem_compatibleSet_ray e p₀
            h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
        refine ⟨![Ne, Nr, Nμ, Nρ, Nm], hb, fun j => ?_⟩
        have hlist : radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm
            = List.ofFn (fun j : Fin 5 => TickReadout.startFact j (![se, sr, sμ, sρ, sm] j)
                (![Ne, Nr, Nμ, Nρ, Nm] j)) := rfl
        rw [hlist, mem_compatibleSet] at hx
        rw [TickReadout.countEvent_eq_event]
        exact hx _ (List.mem_ofFn.2 ⟨j, rfl⟩))
  exact ⟨c 0, c 1, c 2, c 3, c 4, Nat.lt_succ_iff.1 (c 0).2, Nat.lt_succ_iff.1 (c 1).2,
    Nat.lt_succ_iff.1 (c 2).2, Nat.lt_succ_iff.1 (c 3).2, Nat.lt_succ_iff.1 (c 4).2, hQ, hc⟩

end Family

end CSD.RecordLayer

end
