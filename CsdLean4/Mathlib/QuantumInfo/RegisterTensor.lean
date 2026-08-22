/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Register
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Splitting a qubit register into a Hilbert tensor product

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

A register of `a + b` qubits factors as the Hilbert tensor product of its first `a` and its last
`b` qubits:

  `QReg (a + b) ≃ₗᵢ[ℂ] QReg a ⊗[ℂ] QReg b`   (`regTensorEquiv`).

This is the identification recorded as missing in `MATHLIB-GAPS.md` (`specs/mathlib-gaps-plan.md`
MG-5). Mathlib carries the inner-product structure on `E ⊗[𝕜] F`
(`Analysis/InnerProductSpace/TensorProduct.lean`), but nothing connected it to the *concrete*
`EuclideanSpace`/`PiLp` model that `QReg` uses — so "apply this operator to those wires and the
identity elsewhere" could not even be stated.

The construction is two reindexings and an orthonormal basis:

* `regSplitEquiv` — the index bijection `(Fin (a+b) → Fin 2) ≃ (Fin a → Fin 2) × (Fin b → Fin 2)`,
  currying `Fin (a+b) ≃ Fin a ⊕ Fin b`;
* `splitReg` — the induced isometry onto the product-indexed Euclidean space;
* `prodTensorEquiv` — `EuclideanSpace ℂ (ι × κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ κ`
  from `OrthonormalBasis.tensorProduct`: both sides carry orthonormal bases indexed by `ι × κ`,
  so the isometry is the change of basis;
* ★★ `regTensorEquiv` — the composite, with `regTensorEquiv_basisState` confirming it is the
  expected map on computational basis states.

The payoff for consumers is `tensorFirst`: an operator on the first `a` qubits extended by the
identity on the remaining `b`, as an operator on `QReg (a + b)`, with `tensorFirst_basisState`
computing its action.

## Scope

Finite-dimensional and concrete throughout; no completion or topological tensor product is
involved (in finite dimensions the algebraic tensor product already carries the Hilbert
structure). The split is at a **prefix** of the wires; an arbitrary wire subset would compose
this with a permutation reindexing, which is not done here.

## References

`QuantumInfo/Register.lean` (`QReg`, `basisState`); `MATHLIB-GAPS.md` (the register
tensor-factorisation row this closes); `specs/mathlib-gaps-plan.md` (MG-5).
-/

@[expose] public section

open scoped TensorProduct

namespace QuantumInfo

/-! ### The product-index model is a tensor product -/

/-- **The concrete model of a Hilbert tensor product**: a Euclidean space on a product index is
the tensor product of the Euclidean spaces on the factors. Both sides carry orthonormal bases
indexed by `ι × κ` — the standard basis on the left, the tensor of the standard bases on the
right — so the isometry is the change of basis. -/
noncomputable def prodTensorEquiv (ι κ : Type*) [Fintype ι] [Fintype κ] :
    EuclideanSpace ℂ (ι × κ) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ ι) ⊗[ℂ] (EuclideanSpace ℂ κ) :=
  ((EuclideanSpace.basisFun ι ℂ).tensorProduct (EuclideanSpace.basisFun κ ℂ)).repr.symm

/-- On standard basis vectors the identification is the expected one. -/
lemma prodTensorEquiv_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) :
    prodTensorEquiv ι κ (EuclideanSpace.single (i, k) (1 : ℂ))
      = EuclideanSpace.single i (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single k (1 : ℂ) := by
  rw [prodTensorEquiv, OrthonormalBasis.repr_symm_single]
  simp

/-! ### Splitting the wire index -/

variable (a b : ℕ)

/-- The index bijection behind the register split: a bitstring on `a + b` wires is a pair of
bitstrings, on the first `a` and the last `b`. -/
def regSplitEquiv : (Fin (a + b) → Fin 2) ≃ ((Fin a → Fin 2) × (Fin b → Fin 2)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (Fin 2))

@[simp] lemma regSplitEquiv_apply (z : Fin (a + b) → Fin 2) :
    regSplitEquiv a b z
      = (fun i => z (Fin.castAdd b i), fun j => z (Fin.natAdd a j)) := by
  ext i <;> simp [regSplitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- **The register split**, as an isometry onto the product-indexed Euclidean space. -/
noncomputable def splitReg :
    QReg (a + b) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((Fin a → Fin 2) × (Fin b → Fin 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regSplitEquiv a b)

@[simp] lemma splitReg_basisState (z : Fin (a + b) → Fin 2) :
    splitReg a b (basisState z)
      = EuclideanSpace.single (regSplitEquiv a b z) (1 : ℂ) := by
  rw [splitReg, basisState]
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

/-! ### ★★ The register tensor factorisation -/

/-- ★★ **A register splits as a Hilbert tensor product of its wire blocks.** -/
noncomputable def regTensorEquiv : QReg (a + b) ≃ₗᵢ[ℂ] (QReg a) ⊗[ℂ] (QReg b) :=
  (splitReg a b).trans (prodTensorEquiv _ _)

/-- The factorisation acts as expected on computational basis states: a bitstring goes to the
tensor of its two blocks. -/
@[simp] lemma regTensorEquiv_basisState (z : Fin (a + b) → Fin 2) :
    regTensorEquiv a b (basisState z)
      = basisState (fun i => z (Fin.castAdd b i))
          ⊗ₜ[ℂ] basisState (fun j => z (Fin.natAdd a j)) := by
  rw [regTensorEquiv, LinearIsometryEquiv.trans_apply, splitReg_basisState,
    regSplitEquiv_apply, prodTensorEquiv_single]
  rfl

/-! ### Operators on a wire block, extended by the identity -/

variable {a b}

/-- **An operator on the first `a` wires, extended by the identity on the last `b`** — the
"local tensor factor" a register-level statement needs. -/
noncomputable def tensorFirst (A : QReg a →L[ℂ] QReg a) : QReg (a + b) →L[ℂ] QReg (a + b) :=
  LinearMap.toContinuousLinearMap
    (((regTensorEquiv a b).symm.toLinearEquiv.toLinearMap).comp
      ((LinearMap.rTensor (QReg b) (A : QReg a →ₗ[ℂ] QReg a)).comp
        ((regTensorEquiv a b).toLinearEquiv.toLinearMap)))

lemma tensorFirst_apply (A : QReg a →L[ℂ] QReg a) (v : QReg (a + b)) :
    tensorFirst A v
      = (regTensorEquiv a b).symm
          (LinearMap.rTensor (QReg b) (A : QReg a →ₗ[ℂ] QReg a) (regTensorEquiv a b v)) :=
  rfl

/-- **The action on computational basis states**: the operator hits the first block, the second
block rides along. This is the computation rule a hybrid-circuit argument consumes. -/
lemma tensorFirst_basisState (A : QReg a →L[ℂ] QReg a) (z : Fin (a + b) → Fin 2) :
    tensorFirst A (basisState z)
      = (regTensorEquiv a b).symm
          (A (basisState (fun i => z (Fin.castAdd b i)))
            ⊗ₜ[ℂ] basisState (fun j => z (Fin.natAdd a j))) := by
  rw [tensorFirst_apply, regTensorEquiv_basisState, LinearMap.rTensor_tmul]
  rfl

/-- The identity extends to the identity. -/
@[simp] lemma tensorFirst_one :
    tensorFirst (b := b) (ContinuousLinearMap.id ℂ (QReg a)) = ContinuousLinearMap.id ℂ _ := by
  ext v
  rw [tensorFirst_apply]
  simp

end QuantumInfo
