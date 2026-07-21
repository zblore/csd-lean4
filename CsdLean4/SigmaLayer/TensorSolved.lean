import CsdLean4.SigmaLayer.TensorGeneration
import Mathlib.RingTheory.MatrixAlgebra

/-!
# FND/TensorSolved: why composition is the tensor product (P3, via local tomography)

**Category:** 7-SigmaLayer (the Choice A ontology layer).

`FND/TensorGeneration.lean` reduced B6 by showing the commuting local subalgebras GENERATE the joint
observable algebra. This module proves that the **standard tensor (Kronecker) model REALIZES the
composition principles**: it is a canonical linear (and — see `TensorReconstruction.lean` — algebra)
equivalence

  `M_{NA} ⊗[ℂ] M_{NB}  ≃  M_{NA·NB}`,   `U ⊗ₜ Q  ↦  aliceOp U · bobOp Q  =  U ⊗ₖ Q`

(`compositeTensorEquiv`, wiring `kroneckerLinearEquiv`), in which the two operational facts

* **locality** — the local algebras commute (`aliceOp_bobOp_commute`);
* **local tomography** — every joint observable is a combination of local products
  (`joint_mem_span_local`);

both hold. So the tensor product is a MODEL satisfying locality + local tomography with dimension
`NA · NB` (`composite_is_tensor_product`).

## Honest scope — SUFFICIENCY here, UNIQUENESS in `TensorReconstruction.lean`

This module proves SUFFICIENCY: the Kronecker composite satisfies the composition principles. It does NOT
by itself prove NECESSITY — that an ARBITRARY composite carrying commuting, generating local algebras must
BE the tensor product. That converse (the actual reconstruction, `local matrix algebras + locality +
generation ⟹ ⊗`, with the dimension corollary `dim = NA · NB` discharging B6) is the abstract theorem
`compositeAlgReconstruction` / `composite_dim_eq` in `FND/TensorReconstruction.lean`. Read together they
give the full statement; this file alone is the sufficiency half.

The operational content is the standard GPT reconstruction (Hardy; Chiribella–D'Ariano–Perinotti): "why
`⊗`" is answered by **local tomography** — the joint observables are spanned by local products. Local
tomography singles out the quantum tensor product among general composites (real-QM and other GPTs are NOT
locally tomographic and do NOT get `⊗`); it is here a PROVED property of the quantum local-algebra
structure (`joint_mem_span_local`). What is NOT derived (and cannot be, on pain of falsehood for
non-tomographic GPTs) is that the world must be locally tomographic.

References: `specs/future-work.md` (P3 / FND-P3r); `FND/TensorGeneration.lean` (`joint_mem_span_local`,
`single_prod`), `FND/TensorSector.lean` (`aliceOp`, `bobOp`, `aliceOp_bobOp_commute`).
-/

open Matrix TensorProduct
open scoped Kronecker
open CSD.Empirical.QM

namespace CSD.SigmaLayer

variable {m n : ℕ}

/-- The joint product of local operators is the Kronecker product:
`aliceOp U · bobOp Q = (U ⊗ I)(I ⊗ Q) = U ⊗ₖ Q`. -/
theorem aliceOp_mul_bobOp_eq_kronecker (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    NoCommunication.aliceOp U * NoCommunication.bobOp Q = U ⊗ₖ Q := by
  unfold NoCommunication.aliceOp NoCommunication.bobOp
  rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- **The composite observable equivalence.** The canonical linear isomorphism
`M_{NA} ⊗[ℂ] M_{NB} ≃ M_{NA·NB}` sending `U ⊗ₜ Q` to the joint product `aliceOp U · bobOp Q = U ⊗ₖ Q`
(`kroneckerLinearEquiv`). The composite observable algebra IS the tensor product of the local
ones. -/
noncomputable def compositeTensorEquiv (m n : ℕ) :
    Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ]
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  kroneckerLinearEquiv (Fin m) (Fin m) (Fin n) (Fin n) ℂ

/-- The composite equivalence sends `U ⊗ₜ Q` to the joint local product `aliceOp U · bobOp Q`. -/
theorem compositeTensorEquiv_apply (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    compositeTensorEquiv m n (U ⊗ₜ[ℂ] Q)
      = NoCommunication.aliceOp U * NoCommunication.bobOp Q := by
  rw [compositeTensorEquiv, kroneckerLinearEquiv_tmul, aliceOp_mul_bobOp_eq_kronecker]

/-- **The standard tensor model realizes the composition principles (P3 sufficiency).** Bundles, for the
Kronecker composite:

1. the map `M_{NA} ⊗ M_{NB} → M_{NA·NB}`, `U ⊗ₜ Q ↦ aliceOp U · bobOp Q`, is a BIJECTION (a linear
   isomorphism) — the tensor model carries exactly the local products, no more and no less;
2. its action is exactly the joint local product;
3. locality: the local algebras commute.

Together with local tomography (`joint_mem_span_local`) this shows the tensor product is a MODEL of
locality + generation with dimension `NA · NB`. It is the SUFFICIENCY half of "why `⊗`". The NECESSITY /
uniqueness half — that any composite with commuting, generating local algebras must BE this tensor product
— is `CSD.SigmaLayer.compositeAlgReconstruction` in `FND/TensorReconstruction.lean`; only the two together force
composition to be `⊗`. -/
theorem composite_is_tensor_product :
    Function.Bijective (compositeTensorEquiv m n)
    ∧ (∀ (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ),
        compositeTensorEquiv m n (U ⊗ₜ[ℂ] Q)
          = NoCommunication.aliceOp U * NoCommunication.bobOp Q)
    ∧ (∀ (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ),
        NoCommunication.aliceOp U * NoCommunication.bobOp Q
          = NoCommunication.bobOp Q * NoCommunication.aliceOp (n := n) U) :=
  ⟨(compositeTensorEquiv m n).bijective,
    fun U Q => compositeTensorEquiv_apply U Q,
    fun U Q => aliceOp_bobOp_commute U Q⟩

end CSD.SigmaLayer
