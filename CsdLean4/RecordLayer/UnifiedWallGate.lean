/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateRegions

/-!
# The coincidence relation of the walled chain, and its gate from arcs

**Category:** 7-SigmaLayer (the record layer). BACKLOG #410 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of items R1 and R2 of the list
under UD-164: the coincidence relation for carriers in the mirror-odd sector. No new
assumption beyond UA-18 (a), (c).

On the walled chain of UA-18 (a), taken as the mirror-odd sector of the ring, a carrier at
a place has half its weight at a ring site and half at the mirror site. The ring's relation
"within the angle `w`" (#395) between two such carriers then sees only half of a coincidence.
The chain's relation is "within `w` of the site or of its mirror image". This module defines
it and proves the two gate bounds of #395 for it.

* `cos_site_neg`, `neg_mem_ringArc` — the mirror site has the opposite angle;
* `wallNear` (within `w` of the site or of its mirror image), `wallArc` (the arc about an
  angle and the arc about the opposite angle), `mem_wallArc`;
* ★ `wallNear_of_mem_wallArc`, ★ `not_wallNear_of_mem_wallArc` — two such double arcs of
  half-angle `δ` hold only related pairs when their centres are within `w − 2δ`; they hold no
  related pair when the centres are more than `w + 2δ` apart both ways round;
* ★★ `wallGate_not_le`, ★★ `wallGate_le` — for any messenger ray and any clock ray: the weight
  outside (inside) the relation is at most the messenger's weight outside its double arc plus
  the clock's weight outside its two double arcs.

## Exact scope

* **The relation and two bounds, for any rays.** No packet, wall state, time or number is
  put in. The weights outside the double arcs are those bounded for wall states by #409
  (`regionWeight_icoWall_away_le`, `deviceRegionWeight_icoWall_away_le`); the bounds are not
  combined here, so no gate is shown open or closed for any state.
* **`wallNear` is symmetric under the mirror in its second argument only by construction**;
  that it is the relation of a chain of half the sites is a reading of UA-18 (a), not a
  theorem. It is diagonal in the site basis of the two carriers, a coincidence relation in
  the sense of UA-18 (c).
* **"Apart" is apart both ways round**: the centres must be more than `w + 2δ` from each
  other and from each other's mirror image. On the folded chain that is one condition.
* **A messenger and one clock.** A gate between two clocks takes the same lemma with the
  first carrier's site map changed; it is not stated.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-148, UD-149, UD-164, UD-170, UD-176, UD-178);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringNear`, `ringArc`, `mem_ringArc`,
`ringNear_of_mem_ringArc`, `not_ringNear_of_mem_ringArc`, `ringGate_not_le`, `ringGate_le`);
`RecordLayer/UnifiedGatedReading.lean` (#394: `arenaObs_coincProj_prodRay_le_of_disjoint`);
`RecordLayer/UnifiedCoincidence.lean` (#390: `coincProj`, `siteSel`);
`RecordLayer/UnifiedWallBudgets.lean` (#409: the weights of wall states outside such arcs).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

section Wall

variable (L : ℕ) [NeZero L]

variable {L} in
/-- **The mirror site has the opposite angle.** -/
theorem cos_site_neg (k : ZMod L) (x : ℝ) :
    Real.cos (2 * Real.pi * (-k).val / L - x) = Real.cos (2 * Real.pi * k.val / L + x) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  by_cases h : k = 0
  · subst h
    simp only [neg_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, zero_sub, zero_add,
      Real.cos_neg]
  · rw [ZMod.neg_val]
    simp only [h, ↓reduceIte]
    rw [Nat.cast_sub (ZMod.val_le k)]
    have e : 2 * Real.pi * ((L : ℝ) - k.val) / L - x
        = 2 * Real.pi - (2 * Real.pi * k.val / L + x) := by
      have hL' := hL.ne'
      field_simp
      ring
    rw [e, Real.cos_two_pi_sub]

variable {L} in
/-- The mirror site is in the arc about `x` exactly when the site is in the arc about `−x`. -/
theorem neg_mem_ringArc {x δ : ℝ} {k : ZMod L} :
    -k ∈ ringArc L x δ ↔ k ∈ ringArc L (-x) δ := by
  rw [mem_ringArc, mem_ringArc, cos_site_neg, sub_neg_eq_add]

/-- **Two sites of the walled chain within the angle `w` of each other**: the second site, or
its mirror image, is within `w` of the first. -/
def wallNear (w : ℝ) (k k' : ZMod L) : Prop := ringNear L w k k' ∨ ringNear L w k (-k')

noncomputable instance wallNear.instDecidableRel (w : ℝ) : DecidableRel (wallNear L w) :=
  fun _ _ => Classical.propDecidable _

/-- **The double arc** about the angle `x`: the arc of half-angle `δ` about `x` and the arc
about `−x`. -/
noncomputable def wallArc (x δ : ℝ) : Finset (ZMod L) := ringArc L x δ ∪ ringArc L (-x) δ

variable {L}

theorem mem_wallArc {x δ : ℝ} {k : ZMod L} :
    k ∈ wallArc L x δ ↔ k ∈ ringArc L x δ ∨ k ∈ ringArc L (-x) δ := by
  rw [wallArc, Finset.mem_union]

/-- ★ **Near double arcs hold only related pairs.** -/
theorem wallNear_of_mem_wallArc {w δ x y : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w)
    (hwπ : w ≤ Real.pi) (hxy : Real.cos (w - 2 * δ) ≤ Real.cos (x - y)) {k k' : ZMod L}
    (hk : k ∈ wallArc L x δ) (hk' : k' ∈ wallArc L y δ) : wallNear L w k k' := by
  have hxy' : Real.cos (w - 2 * δ) ≤ Real.cos (-x - -y) := by
    rw [show -x - -y = -(x - y) by ring, Real.cos_neg]
    exact hxy
  rcases mem_wallArc.1 hk with h | h <;> rcases mem_wallArc.1 hk' with h' | h'
  · exact Or.inl (ringNear_of_mem_ringArc hδ hw hwπ hxy h h')
  · exact Or.inr (ringNear_of_mem_ringArc hδ hw hwπ hxy h (neg_mem_ringArc.2 h'))
  · exact Or.inr (ringNear_of_mem_ringArc hδ hw hwπ hxy' h
      (neg_mem_ringArc.2 (by rwa [neg_neg])))
  · exact Or.inl (ringNear_of_mem_ringArc hδ hw hwπ hxy' h h')

/-- ★ **Double arcs apart both ways round hold no related pair.** -/
theorem not_wallNear_of_mem_wallArc {w δ x y : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) (hxy : Real.cos (x - y) < Real.cos (w + 2 * δ))
    (hxy2 : Real.cos (x + y) < Real.cos (w + 2 * δ)) {k k' : ZMod L}
    (hk : k ∈ wallArc L x δ) (hk' : k' ∈ wallArc L y δ) : ¬ wallNear L w k k' := by
  have a2 : Real.cos (x - -y) < Real.cos (w + 2 * δ) := by
    rw [sub_neg_eq_add]
    exact hxy2
  have a3 : Real.cos (-x - y) < Real.cos (w + 2 * δ) := by
    rw [show -x - y = -(x + y) by ring, Real.cos_neg]
    exact hxy2
  have a4 : Real.cos (-x - -y) < Real.cos (w + 2 * δ) := by
    rw [show -x - -y = -(x - y) by ring, Real.cos_neg]
    exact hxy
  rintro (hn | hn)
  · rcases mem_wallArc.1 hk with h | h <;> rcases mem_wallArc.1 hk' with h' | h'
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ hxy h h' hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a2 h h' hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a3 h h' hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a4 h h' hn
  · rcases mem_wallArc.1 hk with h | h <;> rcases mem_wallArc.1 hk' with h' | h'
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a2 h
        (neg_mem_ringArc.2 (by rwa [neg_neg])) hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ hxy h (neg_mem_ringArc.2 h') hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a4 h
        (neg_mem_ringArc.2 (by rwa [neg_neg])) hn
    · exact not_ringNear_of_mem_ringArc hδ hw hwπ a3 h (neg_mem_ringArc.2 h') hn

end Wall

/-! ### The gate of the walled chain, from arcs -/

section Gate

variable {M : ℕ}

/-- ★★ **Near double arcs: little weight outside the relation.** For any messenger ray and
any clock ray: if the messenger's angle `x` is within `w − 2δ` of the clock's two angles
`y₀`, `y₁`, the weight outside `wallNear` is at most the messenger's weight outside its
double arc plus the clock's weight outside its two double arcs. -/
theorem wallGate_not_le {w δ x y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w) (hwπ : w ≤ Real.pi)
    (h0 : Real.cos (w - 2 * δ) ≤ Real.cos (x - y₀))
    (h1 : Real.cos (w - 2 * δ) ≤ Real.cos (x - y₁))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        fun k k' => ¬ wallNear (M + 1) w k k') (prodRay p q)
      ≤ (1 - ∑ k ∈ wallArc (M + 1) x δ,
            arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k) p)
        + (1 - ∑ k ∈ wallArc (M + 1) y₀ δ ∪ wallArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' hn => hn ?_) p q
  rcases Finset.mem_union.1 hk' with h | h
  · exact wallNear_of_mem_wallArc hδ hw hwπ h0 hk h
  · exact wallNear_of_mem_wallArc hδ hw hwπ h1 hk h

/-- ★★ **Double arcs apart: little weight inside the relation.** For any messenger ray and
any clock ray: if the messenger's angle `x` is more than `w + 2δ` from the clock's two angles
and from their mirror images, the weight inside `wallNear` is at most the messenger's weight
outside its double arc plus the clock's weight outside its two double arcs. -/
theorem wallGate_le {w δ x y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (h0 : Real.cos (x - y₀) < Real.cos (w + 2 * δ))
    (h0' : Real.cos (x + y₀) < Real.cos (w + 2 * δ))
    (h1 : Real.cos (x - y₁) < Real.cos (w + 2 * δ))
    (h1' : Real.cos (x + y₁) < Real.cos (w + 2 * δ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)) (prodRay p q)
      ≤ (1 - ∑ k ∈ wallArc (M + 1) x δ,
            arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k) p)
        + (1 - ∑ k ∈ wallArc (M + 1) y₀ δ ∪ wallArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' => ?_) p q
  rcases Finset.mem_union.1 hk' with h | h
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h0 h0' hk h
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h1 h1' hk h

end Gate

end CSD.RecordLayer

end
