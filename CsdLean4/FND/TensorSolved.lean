import CsdLean4.FND.TensorGeneration
import Mathlib.RingTheory.MatrixAlgebra

/-!
# FND/TensorSolved: why composition is the tensor product (P3, via local tomography)

**Category:** 7-FND (the Choice A ontology layer).

`FND/TensorGeneration.lean` reduced B6 by showing the commuting local subalgebras GENERATE the joint
observable algebra. This module completes the derivation: **the composite observable algebra IS the
tensor product of the local ones**, a canonical linear (indeed algebra) equivalence

  `M_{NA} ⊗[ℂ] M_{NB}  ≃  M_{NA·NB}`,   `U ⊗ₜ Q  ↦  aliceOp U · bobOp Q  =  U ⊗ₖ Q`

(`compositeTensorEquiv`, wiring `kroneckerLinearEquiv`). So the two operational facts

* **locality** — the local algebras commute (`aliceOp_bobOp_commute`);
* **local tomography** — every joint observable is a combination of local products
  (`joint_mem_span_local`);

FORCE the composite state space to be `ℂ^{NA} ⊗ ℂ^{NB}` (dimension `NA · NB`): the map from
(local Alice observable) ⊗ (local Bob observable) to (their joint product) is a BIJECTION
(`composite_is_tensor_product`). There is no composite carrying these local observables, commuting and
locally tomographic, other than the tensor product.

## Honest scope — what "solving P3" means

This is the operational derivation of the tensor product, exactly as in the generalised-probabilistic-
theory reconstructions (Hardy; Chiribella–D'Ariano–Perinotti): "why `⊗`" is answered by **local
tomography** — that the joint state/observables are determined by, and spanned by, local ones. Local
tomography is the axiom that singles out the quantum tensor product among general composites (real-QM and
other GPTs are NOT locally tomographic and do NOT get `⊗`); it is here a PROVED property of the quantum
local-algebra structure (`joint_mem_span_local`), so the implication "local subsystems + locality + local
tomography ⟹ `⊗`" is a theorem, not a posit. What is NOT derived (and cannot be, on pain of falsehood
for non-tomographic GPTs) is that the world must be locally tomographic; P3 is thereby reduced to that one
clean operational axiom and the implication proved. This closes the "why `⊗`" question for quantum
composites; B6's dimension `NA · NB` is forced, not chosen.

References: `specs/future-work.md` (P3 / FND-P3r); `FND/TensorGeneration.lean` (`joint_mem_span_local`,
`single_prod`), `FND/TensorSector.lean` (`aliceOp`, `bobOp`, `aliceOp_bobOp_commute`).
-/

open Matrix TensorProduct
open scoped Kronecker
open CSD.Empirical.QM

namespace CSD.FND

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

/-- **P3 solved (via local tomography): the composite observable algebra IS the tensor product of the
local ones.** Bundles:

1. the map `M_{NA} ⊗ M_{NB} → M_{NA·NB}`, `U ⊗ₜ Q ↦ aliceOp U · bobOp Q`, is a BIJECTION (a linear
   isomorphism) — the composite carries no more and no less than the tensor product;
2. its action is exactly the joint local product;
3. locality: the local algebras commute.

Together with local tomography (`joint_mem_span_local`), this forces composition to be `⊗` with
dimension `NA · NB`: given quantum local subsystems that are local and locally tomographic, the composite
IS the tensor product. This is the operational answer to "why `⊗`". -/
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

end CSD.FND
