import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import Mathlib.MeasureTheory.Measure.Haar.Unique
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

/-! ## Phase G2 — right-invariance of `unitaryHaarProb`

On a compact group, every Haar probability measure is both left- and
right-invariant. Mathlib gives left-invariance directly (via
`IsHaarMeasure`); we obtain right-invariance via Haar uniqueness:
the right-translate `Measure.map (· * g) unitaryHaarProb` is again a
Haar probability measure, hence equal to `unitaryHaarProb`.
-/

/-- `unitaryHaarProb` is right-invariant under group multiplication.

Proof: `Measure.map (· * g) unitaryHaarProb` is `IsHaarMeasure` (via
`isHaarMeasure_map_mul_right`, an instance) and `IsProbabilityMeasure`
(via `Measure.isProbabilityMeasure_map`, since `(· * g)` is measurable).
`unitaryHaarProb` itself is both. By Haar uniqueness on compact groups
(`isHaarMeasure_eq_of_isProbabilityMeasure`), the two measures coincide. -/
instance instIsMulRightInvariantUnitaryHaarProb (N : ℕ) :
    MeasureTheory.Measure.IsMulRightInvariant
      (unitaryHaarProb : MeasureTheory.Measure (Matrix.unitaryGroup (Fin N) ℂ)) where
  map_mul_right_eq_self g := by
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map (· * g)
          (unitaryHaarProb : MeasureTheory.Measure
            (Matrix.unitaryGroup (Fin N) ℂ))) :=
      MeasureTheory.Measure.isProbabilityMeasure_map
        (continuous_mul_const g).measurable.aemeasurable
    exact MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-! ## Phase G3 — Haar-orbit-indicator key lemma

The Haar-measure mass of the set of unitaries mapping a fixed point
`p` into a target Borel set `B` is independent of `p`. By transitivity
(Phase F), any two base points are related by some unitary `V`;
by right-invariance of Haar (Phase G2), the right-translation by `V`
preserves the measure. -/

/-- **Phase G3.** For any Borel set `B ⊆ ℙ ℂ V` and any two base points
`p₀, p`, the Haar mass of the set `{U | U • p ∈ B}` equals that of
`{U | U • p₀ ∈ B}`.

Proof: take `V_p` with `V_p • p₀ = p` (from `IsPretransitive`, which
auto-includes `[NeZero N]` from the section variable). Then
`{U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}` by `smul_smul`.
Right-invariance of Haar (Phase G2) discharges the measure equality. -/
lemma haar_orbit_indicator_eq
    {B : Set (ℙ ℂ (EuclideanSpace ℂ (Fin N)))} (hB : MeasurableSet B)
    (p₀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    unitaryHaarProb {U : Matrix.unitaryGroup (Fin N) ℂ | U • p ∈ B}
      = unitaryHaarProb {U : Matrix.unitaryGroup (Fin N) ℂ | U • p₀ ∈ B} := by
  -- Get a unitary V_p with V_p • p₀ = p via transitivity.
  obtain ⟨V_p, hV_p⟩ :=
    MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ) p₀ p
  -- Set equality: {U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}.
  have h_set_eq :
      {U : Matrix.unitaryGroup (Fin N) ℂ | U • p ∈ B}
        = (· * V_p) ⁻¹' {U | U • p₀ ∈ B} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [← hV_p, smul_smul]
  -- Measurability of the inner set (orbit map preimage of Borel).
  have h_S_meas :
      MeasurableSet {U : Matrix.unitaryGroup (Fin N) ℂ | U • p₀ ∈ B} :=
    orbit_map_measurable p₀ hB
  rw [h_set_eq, ← MeasureTheory.Measure.map_apply
        (continuous_mul_const V_p).measurable h_S_meas,
      MeasureTheory.map_mul_right_eq_self]

end Matrix.UnitaryGroup
