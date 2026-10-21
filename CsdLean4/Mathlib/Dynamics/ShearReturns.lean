/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapShears
public import CsdLean4.Mathlib.Dynamics.ReturnCriterion

/-!
# What returns under a shear: the torsion circles

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #181 (out of #19, #153, #177).

The `t`-th iterate of the horizontal shear `(x, y) ↦ (x + y, y)` is `(x, y) ↦ (x + t·y, y)`, so a
point returns after `t` strokes iff `t·y = 0`: the return set is the union of the `t` circles over
the `t`-torsion points of the read coordinate, infinite at every stroke. So a shear fails the return
criterion (#177) at **every** stroke, not merely at one — the `finite` clause never holds.

* `MeasureTheory.shearX_iterate`, `shearY_iterate` — the iterates in closed form;
* ★★ `MeasureTheory.shearX_iterate_fixed_iff`, `shearY_iterate_fixed_iff` — **a point returns
  iff its read coordinate is `t`-torsion**;
* ★ `MeasureTheory.infinite_fixedPoints_shearX_iterate`, `infinite_fixedPoints_shearY_iterate` —
  the return set at every stroke is infinite (it contains a whole circle);
* ★★ `MeasureTheory.not_hasReturnGrowth_shearX`, `not_hasReturnGrowth_shearY`.

## Honest scope

* The count of `t`-torsion points of the circle (`t` of them) is not used: only `t • y = 0` is,
  which is the definition of `t`-torsion.
* Both shears are elements of `SL₂(ℤ)` with trace `2`, so #179 already gives "no return growth"
  abstractly; this file says which configurations return, and that the failure is at every stroke.

References: `Mathlib/Dynamics/CatMapShears.lean` (#153, `shearX`, `shearY`,
`cat_eq_shearX_comp_shearY`), `Mathlib/Dynamics/ReturnCriterion.lean` (#177);
`specs/BACKLOG.md` #181, #19.
-/

@[expose] public section

open Function

namespace MeasureTheory

/-! ### The iterates -/

theorem shearX_iterate (t : ℕ) : shearX^[t] = fun p : Torus2 => (p.1 + t • p.2, p.2) := by
  induction t with
  | zero => funext p; simp
  | succ k ih =>
      funext p
      rw [iterate_succ_apply', ih]
      simp only [shearX, succ_nsmul]
      refine Prod.ext ?_ rfl
      simp only
      abel

theorem shearY_iterate (t : ℕ) : shearY^[t] = fun p : Torus2 => (p.1, p.2 + t • p.1) := by
  induction t with
  | zero => funext p; simp
  | succ k ih =>
      funext p
      rw [iterate_succ_apply', ih]
      simp only [shearY, succ_nsmul]
      refine Prod.ext rfl ?_
      simp only
      abel

/-! ### What returns: the torsion circles -/

/-- ★★ **A point returns under `t` horizontal shears iff its read coordinate is `t`-torsion.** -/
theorem shearX_iterate_fixed_iff (t : ℕ) (p : Torus2) : shearX^[t] p = p ↔ t • p.2 = 0 := by
  rw [shearX_iterate]
  simp only [Prod.ext_iff, and_true]
  exact add_eq_left

/-- ★★ **A point returns under `t` vertical shears iff its read coordinate is `t`-torsion.** -/
theorem shearY_iterate_fixed_iff (t : ℕ) (p : Torus2) : shearY^[t] p = p ↔ t • p.1 = 0 := by
  rw [shearY_iterate]
  simp only [Prod.ext_iff, true_and]
  exact add_eq_left

/-! ### The return sets are infinite at every stroke -/

/-- The circle `{(x, 0)}` lies in every return set of the horizontal shear. -/
theorem infinite_fixedPoints_shearX_iterate (t : ℕ) :
    Infinite {p : Torus2 // shearX^[t] p = p} := by
  have hmem : ∀ s : ℝ, shearX^[t] (((s : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ))))
      = ((s : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ))) := by
    intro s
    rw [shearX_iterate_fixed_iff]
    simp
  let f : Set.Ico (0 : ℝ) 1 → {p : Torus2 // shearX^[t] p = p} := fun s =>
    ⟨(((s : ℝ) : AddCircle (1 : ℝ)), 0), hmem s⟩
  have hf : Injective f := by
    intro s s' h
    have h1 := congrArg (fun q : {p : Torus2 // shearX^[t] p = p} => (q : Torus2).1) h
    simp only [f] at h1
    have hs : (s : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    have hs' : (s' : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    exact Subtype.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ico hs hs').1 h1)
  have : Infinite (Set.Ico (0 : ℝ) 1) := Set.Ico.infinite (by norm_num)
  exact Infinite.of_injective f hf

/-- The circle `{(0, y)}` lies in every return set of the vertical shear. -/
theorem infinite_fixedPoints_shearY_iterate (t : ℕ) :
    Infinite {p : Torus2 // shearY^[t] p = p} := by
  have hmem : ∀ s : ℝ, shearY^[t] (((0 : AddCircle (1 : ℝ)), (s : AddCircle (1 : ℝ))))
      = ((0 : AddCircle (1 : ℝ)), (s : AddCircle (1 : ℝ))) := by
    intro s
    rw [shearY_iterate_fixed_iff]
    simp
  let f : Set.Ico (0 : ℝ) 1 → {p : Torus2 // shearY^[t] p = p} := fun s =>
    ⟨(0, ((s : ℝ) : AddCircle (1 : ℝ))), hmem s⟩
  have hf : Injective f := by
    intro s s' h
    have h1 := congrArg (fun q : {p : Torus2 // shearY^[t] p = p} => (q : Torus2).2) h
    simp only [f] at h1
    have hs : (s : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    have hs' : (s' : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    exact Subtype.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ico hs hs').1 h1)
  have : Infinite (Set.Ico (0 : ℝ) 1) := Set.Ico.infinite (by norm_num)
  exact Infinite.of_injective f hf

/-- ★★ **A shear has no return growth**: its `finite` clause fails at every stroke. -/
theorem not_hasReturnGrowth_shearX (h : ℝ) : ¬ HasReturnGrowth shearX h := fun H =>
  @not_finite _ (infinite_fixedPoints_shearX_iterate 1) (H.finite 0)

theorem not_hasReturnGrowth_shearY (h : ℝ) : ¬ HasReturnGrowth shearY h := fun H =>
  @not_finite _ (infinite_fixedPoints_shearY_iterate 1) (H.finite 0)

end MeasureTheory

end
