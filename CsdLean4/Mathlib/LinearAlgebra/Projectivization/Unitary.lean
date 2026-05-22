import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix unitary group action on projective Euclidean space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Builds on `Mathlib/LinearAlgebra/Projectivization/Topology.lean`'s
`instMulAction : MulAction (V ≃ₗ[K] V) (ℙ K V)` and Mathlib's
`Matrix.UnitaryGroup` to produce the natural action of the matrix
unitary group on the projective space of Euclidean space.

## Main definitions

- `Matrix.UnitaryGroup.toEuclideanLinearEquiv`: a unitary matrix
  gives a linear self-equivalence of `EuclideanSpace ℂ (Fin N)`.
  Companion to Mathlib's `Matrix.UnitaryGroup.toLinearEquiv` for the
  Euclidean (`PiLp 2`) version of the underlying vector space.
- `Matrix.UnitaryGroup.toEuclideanLinearEquivHom`: the monoid hom
  `unitaryGroup (Fin N) ℂ →* (EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N))`.

## Main instances

- `MulAction (Matrix.unitaryGroup (Fin N) ℂ) (ℙ ℂ (EuclideanSpace ℂ (Fin N)))`
  via `MulAction.compHom` applied to `toEuclideanLinearEquivHom`.
- `ContinuousConstSMul (Matrix.unitaryGroup (Fin N) ℂ) (ℙ ℂ (EuclideanSpace ℂ (Fin N)))`
  by routing through `Projectivization.mapEquiv_continuous_of_finiteDim`.

## What this unlocks

These instances are the substrate for the eventual SU(N)-invariant Borel
probability measure on `ℂℙ^{N-1}` and the associated uniqueness theorem,
which together discharge the `invariant_measure_uniqueness` axiom carried
by LF2.

## Provenance

Staged as upstream Mathlib material. All declarations are under
`namespace Matrix.UnitaryGroup` with no `CsdLean4`-namespace prefix.
The file is intended to land in
`Mathlib/LinearAlgebra/Projectivization/Unitary.lean` once usage stabilises.

## Tags

projectivization, unitary group, MulAction, complex projective space
-/

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-- A unitary matrix gives a linear self-equivalence of
`EuclideanSpace ℂ (Fin N)`. The inverse is the linear map induced by
the conjugate transpose. Euclidean (`PiLp 2`) companion to Mathlib's
`Matrix.UnitaryGroup.toLinearEquiv` (which is for `Fin N → ℂ`). -/
noncomputable def toEuclideanLinearEquiv (A : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  LinearEquiv.ofLinear
    (Matrix.toEuclideanLin (A.val : Matrix (Fin N) (Fin N) ℂ))
    (Matrix.toEuclideanLin (star A.val : Matrix (Fin N) (Fin N) ℂ))
    (by
      show Matrix.toEuclideanLin (A.val : Matrix (Fin N) (Fin N) ℂ) ∘ₗ
           Matrix.toEuclideanLin (star A.val : Matrix (Fin N) (Fin N) ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (A.val : Matrix (Fin N) (Fin N) ℂ) (star A.val),
          show (A.val : Matrix (Fin N) (Fin N) ℂ) * star A.val
                = (1 : Matrix (Fin N) (Fin N) ℂ) from Unitary.coe_mul_star_self A,
          Matrix.toLpLin_one 2])
    (by
      show Matrix.toEuclideanLin (star A.val : Matrix (Fin N) (Fin N) ℂ) ∘ₗ
           Matrix.toEuclideanLin (A.val : Matrix (Fin N) (Fin N) ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (star A.val : Matrix (Fin N) (Fin N) ℂ) A.val,
          show (star A.val : Matrix (Fin N) (Fin N) ℂ) * A.val
                = (1 : Matrix (Fin N) (Fin N) ℂ) from Unitary.coe_star_mul_self A,
          Matrix.toLpLin_one 2])

@[simp]
lemma toEuclideanLinearEquiv_apply (A : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    toEuclideanLinearEquiv A v
      = Matrix.toEuclideanLin (A.val : Matrix (Fin N) (Fin N) ℂ) v :=
  rfl

lemma toEuclideanLinearEquiv_one :
    toEuclideanLinearEquiv (1 : Matrix.unitaryGroup (Fin N) ℂ)
      = LinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin N)) := by
  apply LinearEquiv.toLinearMap_injective
  -- Goal: ↑(toEuclideanLinearEquiv 1) = ↑(LinearEquiv.refl ℂ ...)
  --      = LinearMap.id
  show Matrix.toEuclideanLin
        ((1 : Matrix.unitaryGroup (Fin N) ℂ).val : Matrix (Fin N) (Fin N) ℂ)
      = LinearMap.id
  rw [Matrix.UnitaryGroup.one_val]
  exact Matrix.toLpLin_one 2

lemma toEuclideanLinearEquiv_mul (A B : Matrix.unitaryGroup (Fin N) ℂ) :
    toEuclideanLinearEquiv (A * B)
      = toEuclideanLinearEquiv A * toEuclideanLinearEquiv B := by
  apply LinearEquiv.toLinearMap_injective
  -- LinearMap-level goal: toEuclideanLin (A*B).val = (toEuclideanLin A.val) ∘ₗ (toEuclideanLin B.val)
  -- The LinearEquiv * coerces to the LinearMap * = LinearMap.comp (= ∘ₗ).
  show Matrix.toEuclideanLin ((A * B).val : Matrix (Fin N) (Fin N) ℂ)
      = (Matrix.toEuclideanLin (A.val : Matrix (Fin N) (Fin N) ℂ)) ∘ₗ
        (Matrix.toEuclideanLin (B.val : Matrix (Fin N) (Fin N) ℂ))
  rw [Matrix.UnitaryGroup.mul_val, Matrix.toLpLin_mul_same]

/-- The monoid hom from the matrix unitary group to the LinearEquiv
group of `EuclideanSpace ℂ (Fin N)`. -/
noncomputable def toEuclideanLinearEquivHom :
    Matrix.unitaryGroup (Fin N) ℂ →*
      (EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N)) where
  toFun := toEuclideanLinearEquiv
  map_one' := toEuclideanLinearEquiv_one
  map_mul' := toEuclideanLinearEquiv_mul

/-! ## Action on projective space -/

/-- `Matrix.unitaryGroup (Fin N) ℂ` acts on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`
via the unitary action on the underlying Hilbert space, transported
through `Projectivization.instMulAction` via `MulAction.compHom`. -/
noncomputable instance instProjectivizationMulAction :
    MulAction (Matrix.unitaryGroup (Fin N) ℂ)
      (ℙ ℂ (EuclideanSpace ℂ (Fin N))) :=
  MulAction.compHom _ toEuclideanLinearEquivHom

/-- The action of each unitary on `ℂℙ^{N-1}` is continuous. -/
instance instProjectivizationContinuousConstSMul :
    ContinuousConstSMul (Matrix.unitaryGroup (Fin N) ℂ)
      (ℙ ℂ (EuclideanSpace ℂ (Fin N))) where
  continuous_const_smul U :=
    Projectivization.mapEquiv_continuous_of_finiteDim
      (toEuclideanLinearEquivHom U)

end Matrix.UnitaryGroup
