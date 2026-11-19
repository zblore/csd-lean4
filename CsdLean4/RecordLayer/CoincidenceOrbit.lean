/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CoincidenceBoxes
public import CsdLean4.CV.ProductRay

/-!
# The free orbit of a product of two carriers, and its coincidence weight at every time

**Category:** 7-SigmaLayer. BACKLOG #437, part (the caused return, obligation UO-26, item
(2) of the plan `specs/unified-records-spacetime-task-plans.md` §9).

`RecordLayer/CoincidenceBoxes.lean` bounds the coincidence weight of a product of two
carriers at one time. This module shows that the free orbit of the composite, started on a
product, is the product of the two carriers' orbits, so the bound holds along the orbit with
the two carriers' own evolved states.

* ★★ `exp_compositeH_mulVec_prod` — `e^{−i s (A ⊗ 1 + 1 ⊗ C)} (ψ ⊗ φ)
  = (e^{−i s A} ψ) ⊗ (e^{−i s C} φ)`;
* ★★★ `sum_norm_sq_coincProj_freeOrbit_prod_le` — at every time `s`, for sets of sites `A`,
  `B` with no pair in the relation: the coincidence weight of the composite's free orbit of
  `ψ ⊗ φ` is at most (the weight of `ψ_s` off `A`) `‖φ_s‖²` + `‖ψ_s‖²` (the weight of `φ_s`
  off `B`), where `ψ_s`, `φ_s` are the two free orbits.

## Honest scope

⚠️ **A vector, not the operator norm.** `transponder_launch_le_coincidence` integrates the
operator norm of `P e^{−i s H₀} X` for a matrix `X`. This module bounds the sum of squares
of `P e^{−i s H₀} (ψ ⊗ φ)`. The passage between the two (a rank-one `X`) is not made.

⚠️ **The sets `A`, `B` are fixed in the statement.** They may be chosen at each time, but
the moving boxes of the two packets are not inserted here, so no bound in terms of the
packets' parameters is stated.

⚠️ **An upper bound.** No launch is shown when the boxes meet.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-226, UD-236, UD-240); `specs/unified-records-spacetime-task-plans.md` (§9);
`RecordLayer/CoincidenceBoxes.lean` (`sum_norm_sq_coincProj_mulVec_prod_le`);
`CV/ProductRay.lean` (`exp_smul_kronecker_add`); `RecordLayer/UnifiedCompositeCarrier.lean`
(`compositeH`); `RecordLayer/UnifiedTransponder.lean`
(`transponder_launch_le_coincidence`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV Matrix NormedSpace
open scoped Kronecker

namespace CSD.RecordLayer

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- ★★ **The free orbit of a product is the product of the orbits.** -/
theorem exp_compositeH_mulVec_prod (A₀ : Matrix ι ι ℂ) (C₀ : Matrix κ κ ℂ) (s : ℝ)
    (ψ : ι → ℂ) (φ : κ → ℂ) :
    exp (s • ((-Complex.I) • compositeH A₀ C₀)) *ᵥ (fun y : ι × κ => ψ y.1 * φ y.2)
      = fun y : ι × κ => (exp (s • ((-Complex.I) • A₀)) *ᵥ ψ) y.1
          * (exp (s • ((-Complex.I) • C₀)) *ᵥ φ) y.2 := by
  have h : (-Complex.I) • compositeH A₀ C₀
      = ((-Complex.I) • A₀) ⊗ₖ (1 : Matrix κ κ ℂ)
        + (1 : Matrix ι ι ℂ) ⊗ₖ ((-Complex.I) • C₀) := by
    rw [compositeH, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [h, exp_smul_kronecker_add]
  funext y
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- ★★★ **The coincidence weight along the free orbit of a product.** At every time `s`, for
sets of sites `A`, `B` with no pair in the relation `r`, the coincidence projector's weight
on the composite's free orbit of `ψ ⊗ φ` is at most the weight of the first carrier's orbit
off `A` times the norm of the second's, plus the norm of the first's times the weight of the
second's off `B`. -/
theorem sum_norm_sq_coincProj_freeOrbit_prod_le [DecidableEq S] (σ : ι → S) (τ : κ → S)
    (r : S → S → Prop) [DecidableRel r] (A₀ : Matrix ι ι ℂ) (C₀ : Matrix κ κ ℂ) (s : ℝ)
    (ψ : ι → ℂ) (φ : κ → ℂ) {A B : Finset S} (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) :
    ∑ x : ι × κ, ‖(coincProj σ τ r *ᵥ (exp (s • ((-Complex.I) • compositeH A₀ C₀))
        *ᵥ fun y : ι × κ => ψ y.1 * φ y.2)) x‖ ^ 2
      ≤ (∑ p, if σ p ∈ A then 0 else ‖(exp (s • ((-Complex.I) • A₀)) *ᵥ ψ) p‖ ^ 2)
          * (∑ q, ‖(exp (s • ((-Complex.I) • C₀)) *ᵥ φ) q‖ ^ 2)
        + (∑ p, ‖(exp (s • ((-Complex.I) • A₀)) *ᵥ ψ) p‖ ^ 2)
          * (∑ q, if τ q ∈ B then 0 else ‖(exp (s • ((-Complex.I) • C₀)) *ᵥ φ) q‖ ^ 2) := by
  rw [exp_compositeH_mulVec_prod]
  exact sum_norm_sq_coincProj_mulVec_prod_le σ τ r _ _ hAB

end CSD.RecordLayer

end
