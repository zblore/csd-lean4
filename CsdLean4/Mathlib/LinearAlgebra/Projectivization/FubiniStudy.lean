/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
public import Mathlib.Topology.Instances.Matrix

/-!
# Fubini–Study measure on complex projective space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Constructs the SU(N)-invariant Borel probability measure on
`Projectivization ℂ (EuclideanSpace ℂ (Fin N))` by pushing the
probability-normalised Haar measure `unitaryHaarProb` (from
`UnitaryHaar.lean`) forward through the orbit map `U ↦ U • p₀`
for a fixed reference point `p₀`.

## Main definitions

- `Matrix.UnitaryGroup.orbitMap p₀` — the orbit map at `p₀`,
  `U ↦ U • p₀ : Matrix.unitaryGroup (Fin N) ℂ → ℙ ℂ (EuclideanSpace ℂ (Fin N))`.
- `fubiniStudyMeasure p₀` — `Measure.map (orbitMap p₀) unitaryHaarProb`.
  The SU(N)-invariant Borel probability measure on `ℂℙ^{N-1}`.
- `defaultPoint`, `defaultFubiniStudyMeasure` — canonical choice
  using `EuclideanSpace.single 0 1` as the reference (requires `[NeZero N]`).

## Main results

- `orbit_map_continuous` — continuity of the orbit map (Phase A).
- `orbit_map_measurable` — measurability corollary.
- `instIsProbabilityMeasureFubiniStudyMeasure` — pushforward is a probability measure.
- `fubiniStudyMeasure_smul_invariant` — SU(N)-invariance.

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`.

## Tags

projectivization, Fubini-Study, Haar measure, SU(N), invariant measure
-/

@[expose] public section

open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-! ## Phase A — orbit map continuity -/

/-- For any fixed vector `v`, the map `M ↦ Matrix.toEuclideanLin M v` is
continuous in `M`. Routes through `Continuous.matrix_mulVec` and
`PiLp.continuous_toLp`. -/
lemma toEuclideanLin_apply_continuous (v : EuclideanSpace ℂ (Fin N)) :
    Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => (Matrix.toEuclideanLin M) v) := by
  show Continuous (fun M : Matrix (Fin N) (Fin N) ℂ =>
      (WithLp.toLp 2 (M *ᵥ (WithLp.ofLp v))
        : EuclideanSpace ℂ (Fin N)))
  refine (PiLp.continuous_toLp _ _).comp ?_
  exact Continuous.matrix_mulVec continuous_id continuous_const

/-- A unitary matrix's `toEuclideanLin` action preserves non-zero.
Routes through `toEuclideanLinearEquiv`'s injectivity. -/
lemma toEuclideanLin_unitary_apply_ne_zero
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  exact (toEuclideanLinearEquiv U).injective (h.trans (LinearEquiv.map_zero _).symm)

/-- The orbit map at `p₀`, `U ↦ U • p₀`. -/
noncomputable def orbitMap (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Matrix.unitaryGroup (Fin N) ℂ → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun U => U • p₀

/-- **Phase A2.** The orbit map is continuous.

Decomposition: `U • p = mk' ⟨(toEuclideanLin U.val) p.rep, nonzero⟩`
via the compHom action on the Projectivization MulAction. The
non-zero proof routes through `toEuclideanLin_unitary_apply_ne_zero`. -/
lemma orbit_map_continuous (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Continuous (orbitMap p) := by
  -- Rewrite the orbit map as Projectivization.mk' of the matrix action on p.rep.
  have h_eq : orbitMap p = fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      Projectivization.mk' ℂ
        ⟨(Matrix.toEuclideanLin U.val) p.rep,
         toEuclideanLin_unitary_apply_ne_zero U p.rep_nonzero⟩ := by
    funext U
    show U • p = _
    conv_lhs => rw [← p.mk_rep]
    rfl
  rw [h_eq]
  refine Projectivization.continuous_mk'.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact (toEuclideanLin_apply_continuous p.rep).comp continuous_subtype_val

/-- **Phase A3.** The orbit map is measurable. -/
lemma orbit_map_measurable (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Measurable (orbitMap p) :=
  (orbit_map_continuous p).measurable

/-! ## Phase B — definition of Fubini–Study measure -/

/-- **Fubini–Study measure** at reference point `p₀`. Defined as the
pushforward of the probability-normalised Haar measure on the unitary
group under the orbit map `U ↦ U • p₀`. -/
noncomputable def fubiniStudyMeasure (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N))) :=
  Measure.map (orbitMap p₀) unitaryHaarProb

/-! ## Phase C — probability measure -/

/-- Pushforward of a probability measure by a measurable map is a
probability measure. -/
instance instIsProbabilityMeasureFubiniStudyMeasure
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    IsProbabilityMeasure (fubiniStudyMeasure p₀) := by
  unfold fubiniStudyMeasure
  exact Measure.isProbabilityMeasure_map (orbit_map_measurable p₀).aemeasurable

/-! ## Phase D — SU(N)-invariance -/

/-- Compatibility lemma: `(U' • ·) ∘ orbitMap p₀ = orbitMap p₀ ∘ (U' * ·)`.
The MulAction axiom `(U' * U) • p₀ = U' • (U • p₀)` makes the two
forms equal as functions. -/
lemma smul_comp_orbitMap (U' : Matrix.unitaryGroup (Fin N) ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (fun p => U' • p) ∘ orbitMap p₀ = orbitMap p₀ ∘ (fun U => U' * U) := by
  funext U
  show U' • (U • p₀) = (U' * U) • p₀
  exact smul_smul U' U p₀

/-- **SU(N)-invariance of the Fubini–Study measure.** For any unitary
`U'`, pushing forward `fubiniStudyMeasure p₀` by the action of `U'`
yields the same measure.

Proof via the chain:
1. unfold `fubiniStudyMeasure` to expose `(orbitMap p₀).map unitaryHaarProb`;
2. compose maps via `Measure.map_map` to push `U' • ·` through the orbit map;
3. use `smul_comp_orbitMap` to re-express the composition as
   `orbitMap p₀ ∘ (U' * ·)`;
4. push the multiplication-by-`U'` map back inside via `Measure.map_map`;
5. invoke `unitaryHaarProb`'s left-invariance (`IsMulLeftInvariant`,
   inherited from `unitaryHaarProb_isHaarMeasure`) to kill the
   inner pushforward. -/
theorem fubiniStudyMeasure_smul_invariant
    (U' : Matrix.unitaryGroup (Fin N) ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Measure.map (fun p => U' • p) (fubiniStudyMeasure p₀)
      = fubiniStudyMeasure p₀ := by
  unfold fubiniStudyMeasure
  rw [Measure.map_map (continuous_const_smul U').measurable
        (orbit_map_measurable p₀)]
  rw [smul_comp_orbitMap]
  rw [← Measure.map_map (orbit_map_measurable p₀)
        (measurable_const_mul U')]
  congr 1
  exact map_mul_left_eq_self unitaryHaarProb U'

end Matrix.UnitaryGroup
