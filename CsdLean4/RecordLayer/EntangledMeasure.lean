/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OnticComposite
public import CsdLean4.LF4.TypicalityForcing

/-!
# Q28 item 2: entangled rays carry positive Fubini–Study weight

**Category:** 7-SigmaLayer (Paper C A6, the measure tier; BACKLOG Q28,
`specs/c2-support-plan.md` item 2 — the C2-blocking item).

`OnticComposite.lean` delivers the topology: the Segre image (the product rays)
is closed, and entangled rays exist in every open neighbourhood of every
product ray. This module adds the measure conclusions the C2 argument runs on:

* `compositeFubiniStudy` — the Fubini–Study measure read on the composite
  index `Fin nA × Fin nB`: the pushforward of `fubiniStudyMeasure` along the
  canonical index reindexing (`finProdFinEquiv`, as a linear isometry of
  Euclidean spaces descended to rays). A probability measure; positive on
  nonempty opens (`compositeFubiniStudy_pos_of_isOpen`).
* ★★ `compositeFubiniStudy_entangled_pos_global` — **the entangled rays carry
  positive preparation weight**: the complement of the Segre image is open
  (2a) and nonempty (`segre_not_surjective`), hence has nonzero measure.
* ★★ `compositeFubiniStudy_entangled_pos` — **the local form C2's
  contradiction runs on**: every open neighbourhood of a product ray meets
  the entangled complement in a set of positive measure. A product-supported
  law assigns that set measure zero, so no product law reproduces the
  composite preparation weights — and the discrepancy set is defined without
  reference to any coordinatisation.

⚠️ Scope: the statements are TOPOLOGICAL-neighbourhood forms — `ℙ` carries no
metric in Mathlib or in this corpus, so "every ε-ball" is not statable today
(`MATHLIB-GAPS.md`, Fubini–Study metric row). The μ_FS-NULL strengthening
("almost every composite ray is entangled") is research-gated on Mathlib-scale
inputs (`MATHLIB-GAPS.md`, polynomial zero sets); the positive form here
carries the C2 argument.

## References

`specs/c2-support-plan.md` (Q28 scoping, item 2);
`RecordLayer/OnticComposite.lean` (`segre`, `segre_range_isClosed`,
`exists_entangled_mem_nhds`, `not_mem_range_segre`);
`LF4/TypicalityForcing.lean` (`fubiniStudyMeasure_pos_of_isOpen`);
`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`
(`fubiniStudyMeasure`); `specs/BACKLOG.md` (Q28); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### The index reindexing, descended to rays -/

/-- The canonical index reindexing `Fin nA × Fin nB ≃ Fin (nA * nB)` as a
linear isometry equivalence of Euclidean spaces. -/
noncomputable def tensorReindexL (nA nB : ℕ) :
    EuclideanSpace ℂ (Fin nA × Fin nB) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (nA * nB)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv

/-- Composite rays, read on the flat `Fin (nA * nB)` index. -/
noncomputable def rayReindex (nA nB : ℕ) :
    ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) →
      ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB))) :=
  Projectivization.map (tensorReindexL nA nB).toLinearEquiv.toLinearMap
    (tensorReindexL nA nB).injective

/-- Flat-index rays, read back on the composite `Fin nA × Fin nB` index. -/
noncomputable def rayReindexInv (nA nB : ℕ) :
    ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB))) →
      ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) :=
  Projectivization.map (tensorReindexL nA nB).symm.toLinearEquiv.toLinearMap
    (tensorReindexL nA nB).symm.injective

lemma rayReindex_continuous : Continuous (rayReindex nA nB) :=
  Projectivization.mapOfInjective_continuous _ _
    (tensorReindexL nA nB).continuous

lemma rayReindexInv_continuous : Continuous (rayReindexInv nA nB) :=
  Projectivization.mapOfInjective_continuous _ _
    (tensorReindexL nA nB).symm.continuous

/-- Reading a composite ray flat and back is the identity. -/
lemma rayReindexInv_rayReindex
    (x : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    rayReindexInv nA nB (rayReindex nA nB x) = x := by
  conv_lhs => rw [← x.mk_rep]
  rw [rayReindex, rayReindexInv, Projectivization.map_mk,
    Projectivization.map_mk]
  conv_rhs => rw [← x.mk_rep]
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  show (1 : ℂ) • x.rep
      = (tensorReindexL nA nB).symm.toLinearEquiv.toLinearMap
        ((tensorReindexL nA nB).toLinearEquiv.toLinearMap x.rep)
  simp

/-- The flat-to-composite reading is surjective. -/
lemma rayReindexInv_surjective :
    Function.Surjective (rayReindexInv nA nB) :=
  fun x => ⟨rayReindex nA nB x, rayReindexInv_rayReindex x⟩

/-! ### The composite Fubini–Study measure -/

/-- **The Fubini–Study measure on the composite index**: the pushforward of
`fubiniStudyMeasure` at `p₀` along the flat-to-composite ray reading. The
composite ray space is the flat `ℂℙ^{nA·nB−1}` up to the canonical index
bijection, and this is THE Fubini–Study measure carried across it. -/
noncomputable def compositeFubiniStudy
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB)))) :
    Measure (ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :=
  Measure.map (rayReindexInv nA nB) (fubiniStudyMeasure p₀)

instance instIsProbabilityMeasureCompositeFubiniStudy
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB)))) :
    IsProbabilityMeasure (compositeFubiniStudy (nA := nA) (nB := nB) p₀) := by
  unfold compositeFubiniStudy
  exact Measure.isProbabilityMeasure_map
    rayReindexInv_continuous.measurable.aemeasurable

/-- **The composite Fubini–Study measure has full support**: every nonempty
open set has positive measure. Transports
`fubiniStudyMeasure_pos_of_isOpen` along the reindexing (preimages of opens
are open by continuity, and nonempty by surjectivity). -/
theorem compositeFubiniStudy_pos_of_isOpen [NeZero nA] [NeZero nB]
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB))))
    {U : Set (ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)))}
    (hU : IsOpen U) (hne : U.Nonempty) :
    compositeFubiniStudy p₀ U ≠ 0 := by
  have : NeZero (nA * nB) := ⟨Nat.mul_ne_zero (NeZero.ne nA) (NeZero.ne nB)⟩
  rw [compositeFubiniStudy,
    Measure.map_apply rayReindexInv_continuous.measurable hU.measurableSet]
  exact CSD.LF4.fubiniStudyMeasure_pos_of_isOpen p₀
    (hU.preimage rayReindexInv_continuous)
    (hne.preimage rayReindexInv_surjective)

/-! ### The entangled rays carry positive weight (Q28 items 2c₀ and 2c) -/

/-- The Segre image is a measurable set (it is closed). -/
theorem measurableSet_range_segre :
    MeasurableSet (Set.range (segre (nA := nA) (nB := nB))) :=
  segre_range_isClosed.measurableSet

/-- ★★ **Entangled rays carry positive preparation weight** (the global form):
whenever both factors have dimension ≥ 2, the complement of the Segre image —
the entangled rays — has nonzero composite Fubini–Study measure. Open by
`segre_range_isClosed`, nonempty by `segre_not_surjective`. -/
theorem compositeFubiniStudy_entangled_pos_global
    (hA : 2 ≤ nA) (hB : 2 ≤ nB)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB)))) :
    compositeFubiniStudy p₀ (Set.range (segre (nA := nA) (nB := nB)))ᶜ ≠ 0 := by
  have : NeZero nA := ⟨by omega⟩
  have : NeZero nB := ⟨by omega⟩
  exact compositeFubiniStudy_pos_of_isOpen p₀
    segre_range_isClosed.isOpen_compl
    ⟨_, segre_not_surjective hA hB⟩

/-- ★★ **The local form C2's contradiction runs on**: every open neighbourhood
of a product ray meets the entangled complement in a set of positive composite
Fubini–Study measure. A product-supported law gives this set measure zero, so
no product law reproduces the composite preparation weights. -/
theorem compositeFubiniStudy_entangled_pos
    (hA : 2 ≤ nA) (hB : 2 ≤ nB)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (nA * nB))))
    {p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))}
    (hp : p ∈ Set.range (segre (nA := nA) (nB := nB)))
    {U : Set (ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)))}
    (hU : IsOpen U) (hpU : p ∈ U) :
    compositeFubiniStudy p₀
      (U \ Set.range (segre (nA := nA) (nB := nB))) ≠ 0 := by
  have : NeZero nA := ⟨by omega⟩
  have : NeZero nB := ⟨by omega⟩
  obtain ⟨q, hqU, hq⟩ := exists_entangled_mem_nhds hA hB hp hU hpU
  exact compositeFubiniStudy_pos_of_isOpen p₀
    (hU.sdiff segre_range_isClosed) ⟨q, hqU, hq⟩

end CSD.RecordLayer
