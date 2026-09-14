/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyVolume
public import CsdLean4.Mathlib.Geometry.Manifold.FormInvariance

/-!
# The unitary action preserves the Fubini–Study form in charts

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).

`ProjectiveSpaceFubiniStudyVolume.lean` proves `fsVolume_map_smul` by feeding
`topFormMeasure_map_eq` the chart form of "`U` preserves `ω_FS^{∧n}`". This module states the same
fact for the 2-form itself, in the vocabulary of `FormInvariance.lean`, so that products of `ℂℙⁿ`
with other factors can inherit it:

* ★ `preservesLocalRep_fsForm_smul` — **`U^* ω_FS = ω_FS` in charts**: through two affine charts
  the action is `uTrans`, analytic where defined, and it pulls the model form back to itself
  (`fsModelForm_uTrans`).

References: `Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyVolume.lean`
(`fsVolume_map_smul`, `chartAt_smul_comp_symm`, `localRep_fsSection'`);
`Geometry/Manifold/Instances/ProjectiveSpaceUnitaryAction.lean` (`fsModelForm_uTrans`);
`Geometry/Manifold/FormInvariance.lean`; `specs/BACKLOG.md` (#29); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology Set MeasureTheory
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization

namespace Projectivization

open Kahler Matrix.UnitaryGroup DifferentialForm

variable {n : ℕ}

/-- ★ **The unitary action preserves the Fubini–Study form in charts.** -/
theorem preservesLocalRep_fsForm_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    PreservesLocalRep (fun x => fsForm (n := n) x) (fun p : ℙ ℂ (Ambient n) => U • p) := by
  intro x₀ z w _ hmem
  rw [chartAt_smul_comp_symm]
  have hne : toEuclideanLinearEquiv U (insertOne (idx x₀) w) (idx z) ≠ 0 :=
    (smul_symm_mem_source_iff U x₀ z w).1 hmem
  refine ⟨(((contDiffOn_uTrans U (idx x₀) (idx z)).contDiffAt
    ((isOpen_uDomain U (idx x₀) (idx z)).mem_nhds hne)).restrict_scalars ℝ).differentiableAt
    (by simp), ?_⟩
  have h1 : localRep (fun x => fsForm (n := n) x) z (uTrans U (idx x₀) (idx z) w)
      = fsModelForm (uTrans U (idx x₀) (idx z) w) := localRep_fsSection' z _
  have h2 : localRep (fun x => fsForm (n := n) x) x₀ w = fsModelForm w := localRep_fsSection' x₀ w
  rw [h1, h2]
  exact fsModelForm_uTrans U _ _ hne

end Projectivization

end
