/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCoincidence
public import CsdLean4.CV.DiracPacketBoxD

/-!
# Two carriers in boxes that are not in contact have little coincidence weight

**Category:** 7-SigmaLayer. BACKLOG #437, part (the caused return, obligation UO-26, item
(2) of the plan `specs/unified-records-spacetime-task-plans.md` §9; the author's decision of
2026-11-18 under UO-17).

`RecordLayer/UnifiedTransponder.lean` bounds the launch of a transponder by the accumulated
norm of the coincidence projector on the free orbit. This module bounds that projector on a
product of two carriers by the weight each has outside a box, when the two boxes hold no
pair of sites in the gate's relation.

* `coincProj_mulVec_apply`;
* ★★★ `sum_norm_sq_coincProj_mulVec_prod_le` — for a product `ψ ⊗ φ` and sets of sites `A`,
  `B` with no pair in the relation `r`: the weight of the coincidence projector on the
  product is at most `(weight of ψ off A) ‖φ‖² + ‖ψ‖² (weight of φ off B)`;
* ★ `sum_ite_fst_eq_regionWeightD_compl` — on the torus the weight off a set of sites is
  `regionWeightD` of the complement;
* ★★ `sum_norm_sq_coincProj_mulVec_prodD_le` — the bound for two carriers on tori, in the
  box weights of `CV/DiracPacketBoxD.lean`.

## Honest scope

⚠️ **At one time, for one product vector.** That the free composite orbit of a product of
two packets is the product of the two packets' orbits is not stated here, so the bound is
not yet inserted under the integral of `transponder_launch_le_coincidence`. That theorem is
stated for matrices in the operator norm; this one is for a vector in the sum of squares.

⚠️ **An upper bound.** It says the coincidence weight is small while the boxes are apart.
It does not say a launch happens when they meet (items (3) to (5) of UO-26).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-224, UD-226, UD-236); `specs/unified-records-spacetime-task-plans.md` (§9);
`RecordLayer/UnifiedCoincidence.lean` (`coincProj`); `RecordLayer/UnifiedTransponder.lean`
(`transponder_launch_le_coincidence`); `CV/DiracPacketBoxD.lean` (`regionWeightD`,
`siteWeightD`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV Matrix

namespace CSD.RecordLayer

section Generic

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]

omit [DecidableEq S] in
/-- The coincidence projector acts on a vector entry by entry. -/
theorem coincProj_mulVec_apply (v : ι × κ → ℂ) (x : ι × κ) :
    (coincProj σ τ r *ᵥ v) x = (if r (σ x.1) (τ x.2) then 1 else 0) * v x := by
  rw [coincProj, Matrix.mulVec_diagonal]

/-- ★★★ **Two carriers in boxes that are not in contact have little coincidence weight.** For
a product `ψ ⊗ φ` and sets of sites `A`, `B` with no pair in the relation `r`, the weight of
the coincidence projector on the product is at most the weight of `ψ` off `A` times the norm
of `φ`, plus the norm of `ψ` times the weight of `φ` off `B`. -/
theorem sum_norm_sq_coincProj_mulVec_prod_le (ψ : ι → ℂ) (φ : κ → ℂ) {A B : Finset S}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) :
    ∑ x : ι × κ, ‖(coincProj σ τ r *ᵥ fun y : ι × κ => ψ y.1 * φ y.2) x‖ ^ 2
      ≤ (∑ p, if σ p ∈ A then 0 else ‖ψ p‖ ^ 2) * (∑ q, ‖φ q‖ ^ 2)
        + (∑ p, ‖ψ p‖ ^ 2) * (∑ q, if τ q ∈ B then 0 else ‖φ q‖ ^ 2) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [coincProj_mulVec_apply, norm_mul, norm_mul, mul_pow, mul_pow]
  have hψ : 0 ≤ ‖ψ p‖ ^ 2 := sq_nonneg _
  have hφ : 0 ≤ ‖φ q‖ ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ‖ψ p‖ ^ 2 * ‖φ q‖ ^ 2 := mul_nonneg hψ hφ
  by_cases hr : r (σ p) (τ q)
  · simp only [hr, ↓reduceIte, norm_one, one_pow, one_mul]
    by_cases hA : σ p ∈ A
    · have hB : τ q ∉ B := fun hB => hAB _ hA _ hB hr
      simp only [hA, hB, ↓reduceIte, zero_mul, zero_add, le_refl]
    · simp only [hA, ↓reduceIte]
      have : 0 ≤ ‖ψ p‖ ^ 2 * (if τ q ∈ B then 0 else ‖φ q‖ ^ 2) := by
        split_ifs
        · simp
        · exact hprod
      linarith
  · simp only [hr, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]
    refine add_nonneg (mul_nonneg ?_ hφ) (mul_nonneg hψ ?_) <;> split_ifs <;> simp

end Generic

section Torus

variable {ι₁ S₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype S₁] [DecidableEq S₁] {L : ℕ}
  [NeZero L]

omit [DecidableEq S₁] in
/-- ★ **On the torus the weight off a set of sites is the region weight of the
complement.** -/
theorem sum_ite_fst_eq_regionWeightD_compl (ψ : (ι₁ → ZMod L) × S₁ → ℂ)
    (A : Finset (ι₁ → ZMod L)) :
    (∑ p : (ι₁ → ZMod L) × S₁, if p.1 ∈ A then 0 else ‖ψ p‖ ^ 2) = regionWeightD ψ Aᶜ := by
  rw [Fintype.sum_prod_type, regionWeightD,
    ← Finset.sum_subset (Finset.subset_univ Aᶜ) (fun x _ hx => by
      have hxA : x ∈ A := by simpa using hx
      simp [hxA])]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxA : x ∉ A := by simpa using hx
  simp [hxA, siteWeightD]

/-- ★★ **Two carriers on tori whose boxes are not in contact.** For site sets `A`, `B` of the
two tori with no pair in the relation `r`, the coincidence weight of a product of two states
is at most `w_ψ(Aᶜ) ⟨φ, φ⟩ + ⟨ψ, ψ⟩ w_φ(Bᶜ)` in the box weights of the two carriers. -/
theorem sum_norm_sq_coincProj_mulVec_prodD_le
    (r : (ι₁ → ZMod L) → (ι₁ → ZMod L) → Prop) [DecidableRel r]
    (ψ φ : (ι₁ → ZMod L) × S₁ → ℂ) {A B : Finset (ι₁ → ZMod L)}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) :
    ∑ x : ((ι₁ → ZMod L) × S₁) × ((ι₁ → ZMod L) × S₁),
        ‖(coincProj Prod.fst Prod.fst r *ᵥ fun y => ψ y.1 * φ y.2) x‖ ^ 2
      ≤ regionWeightD ψ Aᶜ * (chainInnerD φ φ).re
        + (chainInnerD ψ ψ).re * regionWeightD φ Bᶜ := by
  have h := sum_norm_sq_coincProj_mulVec_prod_le
    (Prod.fst : (ι₁ → ZMod L) × S₁ → ι₁ → ZMod L)
    (Prod.fst : (ι₁ → ZMod L) × S₁ → ι₁ → ZMod L) r ψ φ hAB
  rwa [sum_ite_fst_eq_regionWeightD_compl, sum_ite_fst_eq_regionWeightD_compl,
    ← re_chainInnerD_self, ← re_chainInnerD_self] at h

end Torus

end CSD.RecordLayer

end
