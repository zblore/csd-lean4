import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import Mathlib.Topology.Instances.Matrix

/-!
# Joint continuity of the unitary action on complex projective space (Phase G1)

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Strengthens the `ContinuousConstSMul` instance from `Unitary.lean`
(continuity in the projective argument for fixed unitary) to the
full `ContinuousSMul` (joint continuity in both arguments).

## Argument

Use the open-quotient-map structure of
`Projectivization.mk' : V₀ → ℙ ℂ V` (where `V₀ := {v : V // v ≠ 0}`):

- `id × mk' : G × V₀ → G × ℙ ℂ V` is an open quotient map (via
  `IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'`).
- A function out of `G × ℙ ℂ V` is continuous iff its precomposition
  with `id × mk'` is.
- The precomposition `(U, ⟨v, hv⟩) ↦ U • mk' ⟨v, hv⟩ = mk' ⟨U.val.mulVec v, ...⟩`
  is continuous, via joint continuity of matrix-vector multiplication
  (`Continuous.matrix_mulVec`), `PiLp.continuous_toLp`, `continuous_mk'`,
  and subtype machinery.

## Main result

`Matrix.UnitaryGroup.instContinuousSMul_projectivization` —
`ContinuousSMul (Matrix.unitaryGroup (Fin N) ℂ) (ℙ ℂ (EuclideanSpace ℂ (Fin N)))`.

## What this unlocks

Joint continuity gives joint measurability (`Continuous.measurable`),
which is the prerequisite for the Fubini swap in Phase G4
(`fubiniStudyMeasure_unique`).

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`.

## Tags

projectivization, continuous group action, joint continuity
-/

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {N : ℕ} [NeZero N]

/-- Joint continuity of the unitary action on `ℂℙ^(N-1)`.

The action `(U, p) ↦ U • p` is jointly continuous on
`Matrix.unitaryGroup (Fin N) ℂ × ℙ ℂ (EuclideanSpace ℂ (Fin N))`. -/
instance instContinuousSMul_projectivization :
    ContinuousSMul (Matrix.unitaryGroup (Fin N) ℂ)
      (ℙ ℂ (EuclideanSpace ℂ (Fin N))) where
  continuous_smul := by
    -- Open-quotient structure: id × mk' is an open quotient on G × V₀.
    rw [← (IsOpenQuotientMap.id.prodMap
            Projectivization.isOpenQuotientMap_mk').continuous_comp_iff]
    -- After the rewrite, the goal is:
    --   Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --     Uv.1 • Projectivization.mk' ℂ Uv.2)
    -- which by definitional unfolding (compHom action + mapEquiv +
    -- Projectivization.map_mk) equals
    --   Continuous (fun Uv => mk' ⟨(toEuclideanLin Uv.1.val) Uv.2.1, ...⟩).
    -- Compose continuous_mk' with subtype_mk on the matrix-vector-mul
    -- composition (which is jointly continuous in (M, v)).
    refine Projectivization.continuous_mk'.comp ?_
    refine Continuous.subtype_mk ?_ _
    -- Goal: Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --   (toEuclideanLin Uv.1.val) Uv.2.1)
    -- This is the WithLp.toLp ∘ (M *ᵥ ofLp) composition.
    show Continuous (fun (Uv : Matrix.unitaryGroup (Fin N) ℂ
                          × {v : EuclideanSpace ℂ (Fin N) // v ≠ 0}) =>
        WithLp.toLp 2 ((Uv.1.val : Matrix (Fin N) (Fin N) ℂ)
            *ᵥ (Uv.2.val.ofLp : Fin N → ℂ)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · -- Continuous (fun Uv => Uv.1.val) — subtype_val ∘ fst
      exact continuous_subtype_val.comp continuous_fst
    · -- Continuous (fun Uv => Uv.2.val.ofLp) — ofLp ∘ subtype_val ∘ snd
      exact (PiLp.continuous_ofLp _ _).comp
              (continuous_subtype_val.comp continuous_snd)

end Matrix.UnitaryGroup
