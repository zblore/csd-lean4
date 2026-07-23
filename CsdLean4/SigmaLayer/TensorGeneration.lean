/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.TensorSector

/-!
# SigmaLayer/TensorGeneration: the tensor product resolved into the local observable algebras

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Bridge B6 posits that a composite system's projective sector is the tensor product with `dim = NA · NB`
(the "why ⊗" derivation P3, parked by standing instruction). This module RESOLVES a substantive part of
that posit into the underlying object: the tensor product carries **no observables beyond the local ones
and their products**. Concretely, the joint standard basis matrix is a product of local basis matrices,

  `single (i,k) (j,l) 1  =  aliceOp (single i j 1) * bobOp (single k l 1)`   (`single_prod`),

so the two commuting local subalgebras (`aliceOp` = `M_{NA} ⊗ I`, `bobOp` = `I ⊗ M_{NB}`) GENERATE the
entire joint observable algebra `M_{NA·NB}` (`joint_mem_span_local`). Combined with locality
(`aliceOp_bobOp_commute`, `SigmaLayer/TensorSector.lean`), this is the operational content of the tensor product:
the composite's observables are exactly the local observables and their products — nothing more. So B6
reduces from "posit `⊗`" to the weaker "posit that both subsystems carry full matrix observable algebras
that act and commute", from which the tensor structure (and the dimension `NA · NB`) is forced.

This does NOT derive WHY composition should be `⊗` from first principles (that would need a locality/
completeness reconstruction of the composite ontic space — the residual P3 / SO-1 direction); it shows
the `⊗` is not free structure OVER the local algebras.

References: `specs/future-work.md` (P3 / SL-T3); `SigmaLayer/TensorSector.lean` (`aliceOp`, `bobOp`,
`aliceOp_bobOp_commute`, `tensorIndexEquiv`).
-/

@[expose] public section

open Matrix
open CSD.Empirical.QM

namespace CSD.SigmaLayer

variable {m n : ℕ}

/-- **The joint basis matrix is a product of local basis matrices.** The `((i,k),(j,l))` standard basis
matrix of the joint space equals Alice's `(i,j)` basis operator times Bob's `(k,l)` basis operator:
`single (i,k) (j,l) 1 = (E_{ij} ⊗ I)(I ⊗ E_{kl}) = E_{ij} ⊗ E_{kl}`. The elementary joint observable is
built from local ones. -/
theorem single_prod (i j : Fin m) (k l : Fin n) :
    NoCommunication.aliceOp (single i j (1 : ℂ)) * NoCommunication.bobOp (single k l (1 : ℂ))
      = single (i, k) (j, l) (1 : ℂ) := by
  unfold NoCommunication.aliceOp NoCommunication.bobOp
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply, Prod.mk.injEq]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> by_cases h3 : k = c <;> by_cases h4 : l = d <;>
    simp_all

/-- `single p q c = c • single p q 1` (a matrix basis element is the scalar times the unit one). -/
theorem single_eq_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (i : ι) (j : κ) (c : ℂ) : single i j c = c • single i j (1 : ℂ) := by
  ext a b; simp only [Matrix.single, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split <;> simp

/-- **The commuting local subalgebras generate the entire joint observable algebra.** Every joint
operator `M : M_{NA·NB}` lies in the span of products `aliceOp U * bobOp Q` — it is a linear combination
of local Alice operators times local Bob operators. So the tensor product carries no observables beyond
the local ones and their products; the `⊗` structure is forced by locality + completeness of the local
algebras, not free structure over them (B6 reduced). -/
theorem joint_mem_span_local (M : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    M ∈ Submodule.span ℂ {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ |
      ∃ U Q, A = NoCommunication.aliceOp U * NoCommunication.bobOp Q} := by
  rw [matrix_eq_sum_single M]
  refine Submodule.sum_mem _ (fun p _ => Submodule.sum_mem _ (fun q _ => ?_))
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  rw [single_eq_smul, ← single_prod i j k l]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨single i j (1 : ℂ), single k l (1 : ℂ), rfl⟩)

end CSD.SigmaLayer
