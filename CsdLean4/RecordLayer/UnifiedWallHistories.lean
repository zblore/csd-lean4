/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarSkeleton
public import CsdLean4.RecordLayer.UnifiedGatedReading

/-!
# Histories of gate displacements, from where the carriers are

**Category:** 7-SigmaLayer (the record layer). BACKLOG #419 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 6 of the research delivery
plan of 2026-11-16, first part. No new assumption.

`tri_radar_lorentz` (#405) asks for five histories of two-carrier gate displacements
`coincShift (gateOp …)`: four gated (`IsGatedHistory`) and one away (`IsAwayHistory`). The
reading theorems #394 and #399 prove counts for the two-pointer flow, and what they prove
about the displacement is inside their proofs. This module states that part on its own:
both histories follow from where the two carriers are and from the clock's own reading.

* `coincProj_not_not` — a relation twice negated has the same coincidence projector;
* `arenaObs_coincProj_prodRay_le_one`, `arenaObs_coincProj_not_prodRay_le_one`;
* ★★★ `isGatedHistory_coincShift` — a pointer coupled to `gateOp r Y`: if the two carriers
  have weight at most `ε` outside `r` up to `t_a` and at most `ε` inside it on `[t_b, t_c]`,
  and the clock's own displacement is within `δ₀` of `(1/4)(1 − cos R t)` up to `t_a`, the
  gate displacement is a gated history with error `δ₀ + 2|z| ε t_a` and speed `2|z|`;
* ★★★ `isAwayHistory_coincShift` — a pointer coupled to the complementary gate: if the
  carriers are inside `r` up to `t_a`, outside it on `[t_b, t₃]` and inside it again on
  `[t₄, t₅]`, each up to `ε`, and the clock's own displacement is within `δ₀` of the swing
  up to `t₃`, the displacement is an away history, with offset the displacement of the
  `r`-gated pointer at `t_b`.

## Exact scope

* **Two carriers, any relation, any carriers.** No packet, wall or value. The hypotheses
  are those that #411, #413, #414 and #417 supply for wall states; they are not applied
  here, so no history of the walled chain is proved.
* **The band of the away history is a hypothesis.** It is a condition on where the
  `r`-gated pointer stopped (R5). #400 (`coincShift_stop_le`) bounds that stop; joining the
  two is Task 7.
* **Displacements along uncoupled orbits from a product ray**, on the fibres where the
  profiles vanish (#393).
* **The clock's own displacement is a hypothesis** (`hclock`): the swing theorems supply it
  for a clock packet with a stated strength and a quarter-turn preparation.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-145, UD-148, UD-157, UD-163, UD-170, UD-189);
`specs/unified-m6-feasibility.md` (§6, item 4); `RecordLayer/UnifiedRadarSkeleton.lean`
(#402: `IsGatedHistory`, `IsAwayHistory`); `RecordLayer/UnifiedGatedReading.lean` (#394:
`abs_coincShift_sub_le`, `abs_arenaObs_gateOp_prodRay_le`, `arenaObs_coincProj_add_not`,
`arenaObs_coincProj_prodRay_nonneg`, `coincFlow_gated_reading`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincShift`,
`coincShift_gateOp_add_not`); `RecordLayer/UnifiedReturnReading.lean` (#399:
`coincFlow_return_reading`); `RecordLayer/UnifiedTriCarrier.lean` (#405:
`tri_radar_lorentz`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

section Histories

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {Y : Matrix κ κ ℂ}

omit [Fintype ι] [Fintype κ] [Fintype S] [DecidableEq S] in
/-- A relation twice negated has the same coincidence projector. -/
theorem coincProj_not_not :
    coincProj σ τ (fun x y => ¬ ¬ r x y) = coincProj σ τ r := by
  ext p q
  simp only [coincProj, Matrix.diagonal_apply, not_not]

theorem arenaObs_coincProj_prodRay_le_one (p : GenArena ι) (q : GenArena κ) :
    arenaObs (coincProj σ τ r) (prodRay p q) ≤ 1 := by
  have h1 := arenaObs_coincProj_add_not σ τ r (prodRay p q)
  have h2 := arenaObs_coincProj_prodRay_nonneg σ τ (fun x y => ¬ r x y) p q
  linarith

theorem arenaObs_coincProj_not_prodRay_le_one (p : GenArena ι) (q : GenArena κ) :
    arenaObs (coincProj σ τ fun x y => ¬ r x y) (prodRay p q) ≤ 1 := by
  have h1 := arenaObs_coincProj_add_not σ τ r (prodRay p q)
  have h2 := arenaObs_coincProj_prodRay_nonneg σ τ r p q
  linarith

/-- ★★★ **A gated history, from where the carriers are.** On a product ray, for a pointer
coupled to `gateOp r Y` with profile derivative `z`: if up to `t_a` the two carriers have
weight at most `ε` outside the relation and the second carrier's own displacement is within
`δ₀` of `(1/4)(1 − cos R t)`, and on `[t_b, t_c]` they have weight at most `ε` inside the
relation with `2|z| ε (t_c − t_b) ≤ 1/6`, then the gate displacement is a gated history with
error `δ₀ + 2|z| ε t_a` and speed `2|z|`. -/
theorem isGatedHistory_coincShift (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (z : ℝ) (p : GenArena ι) (q : GenArena κ) {R δ₀ ε ta tb tc : ℝ} (hR : 0 < R)
    (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hbc : tb ≤ tc)
    (hclock : ∀ t, 0 ≤ t → t ≤ ta →
      |-2 * z * (∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q))
          - 1 / 4 * (1 - Real.cos (R * t))| ≤ δ₀)
    (hopen : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hclosed : ∀ s, tb ≤ s → s ≤ tc →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hsmall : 2 * |z| * ε * (tc - tb) ≤ 1 / 6)
    (hδ : δ₀ + 2 * |z| * ε * ta < 1 / 12) :
    IsGatedHistory (coincShift hA hC (gateOp σ τ r Y) z p q) R (δ₀ + 2 * |z| * ε * ta)
      (2 * |z|) ta tb tc := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  refine
    { rate_pos := hR
      err_nonneg := add_nonneg hδ₀ (by positivity)
      err_lt := hδ
      ta_nonneg := hta
      ta_le := hab
      tb_le := hbc
      swing := fun t ht0 htta => ?_
      mid := fun s t _ hst _ => ?_
      closed := fun s t hbs hst htc => ?_ }
  · have e := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
    have hnot := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
      (ε := ε) ht0 (fun u hu0 hut =>
        (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
          (hopen u hu0 (hut.trans htta)))
    have h0 : coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q 0 = 0 := by
      rw [coincShift, intervalIntegral.integral_same, mul_zero]
    rw [h0, sub_zero, sub_zero] at hnot
    have hcl := hclock t ht0 htta
    have hmono : 2 * |z| * ε * t ≤ 2 * |z| * ε * ta :=
      mul_le_mul_of_nonneg_left htta (by positivity)
    rw [abs_le] at hnot hcl ⊢
    constructor <;> linarith [hnot.1, hnot.2, hcl.1, hcl.2]
  · have h := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := 1) hst
      (fun u _ _ => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
        (arenaObs_coincProj_prodRay_le_one σ τ r _ _))
    linarith
  · have h := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := ε) hst
      (fun u hsu hut => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
        (hclosed u (hbs.trans hsu) (hut.trans htc)))
    have hmono : 2 * |z| * ε * (t - s) ≤ 2 * |z| * ε * (tc - tb) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- ★★★ **An away history, from where the carriers are.** On a product ray, for a pointer
coupled to the complementary gate `gateOp (¬r) Y` with profile derivative `z`: if the two
carriers have weight at most `ε` outside the relation up to `t_a` and again on `[t₄, t₅]`,
at most `ε` inside it on `[t_b, t₃]`, and the second carrier's own displacement is within
`δ₀` of `(1/4)(1 − cos R t)` up to `t₃`, then the displacement is an away history: it stays
within `2|z| ε t_a` of `0` up to `t_a`, follows the swing less the offset
`c = coincShift (gateOp r Y) z p q t_b` within `δ₀ + 2|z| ε (t₃ − t_b)` on `[t_b, t₃]`, and
moves by at most `1/6` on `[t₄, t₅]`. The band condition on `c` is a hypothesis. -/
theorem isAwayHistory_coincShift (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (hY : ∀ s' (q : GenArena κ), |arenaObs (siteSel τ s' * Y) q| ≤ arenaObs (siteSel τ s') q)
    (z : ℝ) (p : GenArena ι) (q : GenArena κ) {R δ₀ ε ta tb t3 t4 t5 : ℝ} (hR : 0 < R)
    (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hta : 0 ≤ ta) (hab : ta ≤ tb) (hb3 : tb ≤ t3)
    (h34 : t3 ≤ t4) (h45 : t4 ≤ t5)
    (hclock : ∀ t, 0 ≤ t → t ≤ t3 →
      |-2 * z * (∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q))
          - 1 / 4 * (1 - Real.cos (R * t))| ≤ δ₀)
    (hnear0 : ∀ s, 0 ≤ s → s ≤ ta →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (haway : ∀ s, tb ≤ s → s ≤ t3 →
      arenaObs (coincProj σ τ r)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hnear1 : ∀ s, t4 ≤ s → s ≤ t5 →
      arenaObs (coincProj σ τ fun x y => ¬ r x y)
        (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) ≤ ε)
    (hη₀ : 2 * |z| * ε * ta < 1 / 12) (hη : δ₀ + 2 * |z| * ε * (t3 - tb) < 1 / 12)
    (hsmall : 2 * |z| * ε * (t5 - t4) ≤ 1 / 6)
    (hband : (-1 / 6 + (δ₀ + 2 * |z| * ε * (t3 - tb))
          < 1 / 12 - coincShift hA hC (gateOp σ τ r Y) z p q tb
        ∧ 1 / 12 - coincShift hA hC (gateOp σ τ r Y) z p q tb
          ≤ 1 / 6 - (δ₀ + 2 * |z| * ε * (t3 - tb)))
      ∨ (-1 / 2 + (δ₀ + 2 * |z| * ε * (t3 - tb))
          < 1 / 12 - coincShift hA hC (gateOp σ τ r Y) z p q tb
        ∧ 1 / 12 - coincShift hA hC (gateOp σ τ r Y) z p q tb
          < -1 / 6 - (δ₀ + 2 * |z| * ε * (t3 - tb)))) :
    IsAwayHistory (coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q) R
      (coincShift hA hC (gateOp σ τ r Y) z p q tb) (2 * |z|) (2 * |z| * ε * ta)
      (δ₀ + 2 * |z| * ε * (t3 - tb)) ta tb t3 t4 t5 := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hspeed : ∀ a b, a ≤ b →
      |coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q b
          - coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q a|
        ≤ 2 * |z| * (b - a) := by
    intro a b hab'
    have h := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q (ε := 1)
      hab' (fun u _ _ =>
        (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
          (arenaObs_coincProj_not_prodRay_le_one σ τ r _ _))
    linarith
  refine
    { rate_pos := hR
      ta_nonneg := hta
      ta_le := hab
      tb_le := hb3
      t3_le := h34
      t4_le := h45
      start_lt := hη₀
      closed0 := fun t ht0 htta => ?_
      mid1 := fun a b _ hab' _ => hspeed a b hab'
      err_nonneg := add_nonneg hδ₀ (mul_nonneg (by positivity) (sub_nonneg.2 hb3))
      err_lt := hη
      swing := fun t hbt ht3 => ?_
      band := hband
      mid2 := fun a b _ hab' _ => hspeed a b hab'
      closed1 := fun a b h4a hab' hb5 => ?_ }
  · have hnot := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q
      (ε := ε) ht0 (fun u hu0 hut =>
        (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
          (hnear0 u hu0 (hut.trans htta)))
    have h0 : coincShift hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q 0 = 0 := by
      rw [coincShift, intervalIntegral.integral_same, mul_zero]
    rw [h0, sub_zero, sub_zero] at hnot
    have hmono : 2 * |z| * ε * t ≤ 2 * |z| * ε * ta :=
      mul_le_mul_of_nonneg_left htta (by positivity)
    linarith
  · have ht0 : 0 ≤ t := hta.trans (hab.trans hbt)
    have e := coincShift_gateOp_add_not σ τ r hA hC Y z p q t
    have hr := abs_coincShift_sub_le hA hC (gateOp σ τ r Y) z p q (ε := ε) hbt
      (fun u hsu hut => (abs_arenaObs_gateOp_prodRay_le σ τ r hY _ _).trans
        (haway u hsu (hut.trans ht3)))
    have hmono : 2 * |z| * ε * (t - tb) ≤ 2 * |z| * ε * (t3 - tb) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hcl := hclock t ht0 ht3
    rw [abs_le] at hr hcl ⊢
    constructor <;> linarith [hr.1, hr.2, hcl.1, hcl.2]
  · have h := abs_coincShift_sub_le hA hC (gateOp σ τ (fun x y => ¬ r x y) Y) z p q (ε := ε)
      hab' (fun u hsu hut =>
        (abs_arenaObs_gateOp_prodRay_le σ τ (fun x y => ¬ r x y) hY _ _).trans
          (hnear1 u (h4a.trans hsu) (hut.trans hb5)))
    have hmono : 2 * |z| * ε * (b - a) ≤ 2 * |z| * ε * (t5 - t4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

end Histories

end CSD.RecordLayer

end
