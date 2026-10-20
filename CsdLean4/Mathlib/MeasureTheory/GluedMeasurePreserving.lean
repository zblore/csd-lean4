/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Gluing measure-preserving pieces along a finite partition

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #137; consumed by `RecordLayer/SkewReroute.lean`.

A map defined piecewise — `f i` on the `i`-th cell `P i` of a finite exact partition — is
measure-preserving as soon as each piece pushes `μ.restrict (P i)` onto `μ.restrict (Q i)` for a
second exact partition `Q`. This is the "cut and move the pieces" principle behind interval and
rectangle exchanges: the preimage of a set splits along `P`, each part is computed by the piece's
transport law, and the parts reassemble along `Q`.

* `glueIdx hP x` — the cell of `x`; `glue hP f x = f (glueIdx hP x) x`;
* `glue_eq_of_mem` — on `P i` the glued map is `f i`;
* `preimage_glue` — `glue⁻¹ S = ⋃ i, f i ⁻¹' S ∩ P i`;
* ★★ `measurePreserving_glue` — **the gluing theorem**.

## Honest scope

The partitions are **exact** (every point in exactly one cell), not almost-everywhere: the
consumers have exact tilings, and the exact form keeps the pointwise statement `glue_eq_of_mem`
available for readout invariance, which an a.e. version would not give.

References: `specs/BACKLOG.md` #137.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {α ι : Type*} {P : ι → Set α}

/-- The cell of an exact partition that contains `x`. -/
noncomputable def glueIdx (hP : ∀ x, ∃! i, x ∈ P i) (x : α) : ι := (hP x).exists.choose

theorem mem_glueIdx (hP : ∀ x, ∃! i, x ∈ P i) (x : α) : x ∈ P (glueIdx hP x) :=
  (hP x).exists.choose_spec

theorem glueIdx_eq (hP : ∀ x, ∃! i, x ∈ P i) {x : α} {i : ι} (hx : x ∈ P i) :
    glueIdx hP x = i :=
  (hP x).unique (mem_glueIdx hP x) hx

/-- **The glued map**: `f i` on the cell `P i`. -/
noncomputable def glue (hP : ∀ x, ∃! i, x ∈ P i) (f : ι → α → α) (x : α) : α :=
  f (glueIdx hP x) x

theorem glue_eq_of_mem (hP : ∀ x, ∃! i, x ∈ P i) (f : ι → α → α) {x : α} {i : ι}
    (hx : x ∈ P i) : glue hP f x = f i x := by
  rw [glue, glueIdx_eq hP hx]

/-- Cells of an exact partition are pairwise disjoint. -/
theorem pairwise_disjoint_of_existsUnique (hP : ∀ x, ∃! i, x ∈ P i) :
    Pairwise (Function.onFun Disjoint P) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  rw [← glueIdx_eq hP hxi, glueIdx_eq hP hxj]

/-- The preimage of a set under the glued map splits along the partition. -/
theorem preimage_glue (hP : ∀ x, ∃! i, x ∈ P i) (f : ι → α → α) (S : Set α) :
    glue hP f ⁻¹' S = ⋃ i, (f i ⁻¹' S ∩ P i) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  constructor
  · intro hx
    exact ⟨glueIdx hP x, by rwa [glue] at hx, mem_glueIdx hP x⟩
  · rintro ⟨i, hfx, hxi⟩
    rwa [glue_eq_of_mem hP f hxi]

variable [MeasurableSpace α] [Fintype ι]

/-- The glued map is measurable when the pieces and the cells are. -/
theorem measurable_glue (hP : ∀ x, ∃! i, x ∈ P i) (hPm : ∀ i, MeasurableSet (P i))
    {f : ι → α → α} (hf : ∀ i, Measurable (f i)) : Measurable (glue hP f) := by
  intro S hS
  rw [preimage_glue]
  exact MeasurableSet.iUnion fun i => (hf i hS).inter (hPm i)

/-- ★★ **The gluing theorem.** If each piece `f i` pushes `μ.restrict (P i)` onto `μ.restrict (Q i)`,
for exact partitions `P` and `Q`, the glued map preserves `μ`. -/
theorem measurePreserving_glue (μ : Measure α) (hP : ∀ x, ∃! i, x ∈ P i)
    (hPm : ∀ i, MeasurableSet (P i)) {Q : ι → Set α} (hQ : ∀ y, ∃! i, y ∈ Q i)
    (hQm : ∀ i, MeasurableSet (Q i)) {f : ι → α → α} (hf : ∀ i, Measurable (f i))
    (hmap : ∀ i, (μ.restrict (P i)).map (f i) = μ.restrict (Q i)) :
    MeasurePreserving (glue hP f) μ μ := by
  refine ⟨measurable_glue hP hPm hf, ?_⟩
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (measurable_glue hP hPm hf) hS, preimage_glue]
  have hdisjP : Pairwise (Function.onFun Disjoint fun i => f i ⁻¹' S ∩ P i) := by
    intro i j hij
    exact (pairwise_disjoint_of_existsUnique hP hij).mono inter_subset_right inter_subset_right
  have hdisjQ : Pairwise (Function.onFun Disjoint fun i => S ∩ Q i) := by
    intro i j hij
    exact (pairwise_disjoint_of_existsUnique hQ hij).mono inter_subset_right inter_subset_right
  have hcover : (⋃ i, (S ∩ Q i)) = S := by
    ext y
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨glueIdx hQ y, h, mem_glueIdx hQ y⟩⟩
  calc μ (⋃ i, (f i ⁻¹' S ∩ P i))
      = ∑ i, μ (f i ⁻¹' S ∩ P i) := by
        rw [measure_iUnion hdisjP fun i => (hf i hS).inter (hPm i), tsum_fintype]
    _ = ∑ i, ((μ.restrict (P i)).map (f i)) S := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.map_apply (hf i) hS, Measure.restrict_apply (hf i hS)]
    _ = ∑ i, μ (S ∩ Q i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmap i, Measure.restrict_apply hS]
    _ = μ S := by
        conv_rhs => rw [← hcover]
        rw [measure_iUnion hdisjQ fun i => hS.inter (hQm i), tsum_fintype]

end MeasureTheory

end
