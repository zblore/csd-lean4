/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix unitary group action on projective Euclidean space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Builds on Mathlib's `Projectivization.instMulAction`
(`Mathlib/LinearAlgebra/Projectivization/Action.lean`,
here with `G := V ≃ₗ[K] V`; `mapEquiv_smul_eq` in `Projectivization/Topology.lean` reads it on
representatives) and Mathlib's `Matrix.UnitaryGroup` to produce the natural action of the matrix
unitary group on the projective space of Euclidean space.

## Main definitions

- `Matrix.UnitaryGroup.toEuclideanLinearEquiv`: a unitary matrix
  gives a linear self-equivalence of `EuclideanSpace ℂ ι`.
  Companion to Mathlib's `Matrix.UnitaryGroup.toLinearEquiv` for the
  Euclidean (`PiLp 2`) version of the underlying vector space.
- `Matrix.UnitaryGroup.toEuclideanLinearEquivHom`: the monoid hom
  `unitaryGroup ι ℂ →* (EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι)`.

## Main instances

- `MulAction (Matrix.unitaryGroup ι ℂ) (ℙ ℂ (EuclideanSpace ℂ ι))`
  via `MulAction.compHom` applied to `toEuclideanLinearEquivHom`.
- `ContinuousConstSMul (Matrix.unitaryGroup ι ℂ) (ℙ ℂ (EuclideanSpace ℂ ι))`
  by routing through `Projectivization.mapEquiv_continuous_of_finiteDim`.

## What this unlocks

These instances are the substrate for the U(N)-invariant Borel
probability measure on `ℂℙ^{N-1}` (`fsMeasure`) and the associated
uniqueness theorem (`fsMeasure_unique`). Together with the
finite-measure normalisation `invariant_measure_uniqueness_cpn`
(`FubiniStudyUnique.lean`), they provide the invariant-measure-uniqueness fact
for the `ℂℙ^{N-1}` / `U(N)` instantiation, consumed directly by the source
repository's concrete measure bridges, which therefore cite no axiom at that
site. (Historically this was the proved concrete realisation of an abstract
invariant-measure-uniqueness axiom of that repository; that axiom — together with the abstract
`measure_bridge` lemma it
served — was **removed 2026-06-04**, since nothing downstream used the abstract
statement. The concrete fact here is all that was ever load-bearing.)

## Provenance

Staged as upstream Mathlib material. All declarations are under
`namespace Matrix.UnitaryGroup` with no `CsdLean4`-namespace prefix.
The file is intended to land in
`Mathlib/LinearAlgebra/Projectivization/Unitary.lean` once usage stabilises.

## Tags

projectivization, unitary group, MulAction, complex projective space
-/

@[expose] public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A unitary matrix gives a linear self-equivalence of
`EuclideanSpace ℂ ι`. The inverse is the linear map induced by
the conjugate transpose. Euclidean (`PiLp 2`) companion to Mathlib's
`Matrix.UnitaryGroup.toLinearEquiv` (which is for `ι → ℂ`). -/
noncomputable def toEuclideanLinearEquiv (A : Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ))
    (Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ))
    (by
      show Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ) ∘ₗ
           Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (A.val : Matrix ι ι ℂ) (star A.val),
          show (A.val : Matrix ι ι ℂ) * star A.val
                = (1 : Matrix ι ι ℂ) from Unitary.coe_mul_star_self A,
          Matrix.toLpLin_one 2])
    (by
      show Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ) ∘ₗ
           Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (star A.val : Matrix ι ι ℂ) A.val,
          show (star A.val : Matrix ι ι ℂ) * A.val
                = (1 : Matrix ι ι ℂ) from Unitary.coe_star_mul_self A,
          Matrix.toLpLin_one 2])

@[simp]
lemma toEuclideanLinearEquiv_apply (A : Matrix.unitaryGroup ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    toEuclideanLinearEquiv A v
      = Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ) v :=
  rfl

lemma toEuclideanLinearEquiv_one :
    toEuclideanLinearEquiv (1 : Matrix.unitaryGroup ι ℂ)
      = LinearEquiv.refl ℂ (EuclideanSpace ℂ ι) := by
  apply LinearEquiv.toLinearMap_injective
  -- Goal: ↑(toEuclideanLinearEquiv 1) = ↑(LinearEquiv.refl ℂ ...)
  --      = LinearMap.id
  show Matrix.toEuclideanLin
        ((1 : Matrix.unitaryGroup ι ℂ).val : Matrix ι ι ℂ)
      = LinearMap.id
  rw [Matrix.UnitaryGroup.one_val]
  exact Matrix.toLpLin_one 2

lemma toEuclideanLinearEquiv_mul (A B : Matrix.unitaryGroup ι ℂ) :
    toEuclideanLinearEquiv (A * B)
      = toEuclideanLinearEquiv A * toEuclideanLinearEquiv B := by
  apply LinearEquiv.toLinearMap_injective
  -- LinearMap-level goal: toEuclideanLin (A*B).val = (toEuclideanLin A.val) ∘ₗ (toEuclideanLin
  -- B.val)
  -- The LinearEquiv * coerces to the LinearMap * = LinearMap.comp (= ∘ₗ).
  show Matrix.toEuclideanLin ((A * B).val : Matrix ι ι ℂ)
      = (Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ)) ∘ₗ
        (Matrix.toEuclideanLin (B.val : Matrix ι ι ℂ))
  rw [Matrix.UnitaryGroup.mul_val, Matrix.toLpLin_mul_same]

/-- The monoid hom from the matrix unitary group to the LinearEquiv
group of `EuclideanSpace ℂ ι`. -/
noncomputable def toEuclideanLinearEquivHom :
    Matrix.unitaryGroup ι ℂ →*
      (EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι) where
  toFun := toEuclideanLinearEquiv
  map_one' := toEuclideanLinearEquiv_one
  map_mul' := toEuclideanLinearEquiv_mul

/-! ## Action on projective space -/

/-- `Matrix.unitaryGroup ι ℂ` acts on `ℙ ℂ (EuclideanSpace ℂ ι)`
via the unitary action on the underlying Hilbert space, transported
through Mathlib's `Projectivization.instMulAction` (with `G := V ≃ₗ[ℂ] V`) via `MulAction.compHom`.
-/
noncomputable instance instProjectivizationMulAction :
    MulAction (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) :=
  MulAction.compHom _ toEuclideanLinearEquivHom

/-- The action of each unitary on `ℂℙ^{N-1}` is continuous. -/
instance instProjectivizationContinuousConstSMul :
    ContinuousConstSMul (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) where
  continuous_const_smul U :=
    Projectivization.mapEquiv_continuous_of_finiteDim
      (toEuclideanLinearEquivHom U)

end Matrix.UnitaryGroup
