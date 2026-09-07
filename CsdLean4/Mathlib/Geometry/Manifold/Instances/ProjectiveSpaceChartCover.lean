/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyForm

/-!
# The affine atlas of `ℂℙⁿ` as a finite chart cover

**Category:** 1-Mathlib-staging (CSD-free).

The non-vacuity witness for `ChartCover` (`TopFormMeasure.lean`, milestone M3 of
`specs/top-power-scoping.md`) on the corpus's own manifold: the `n + 1` affine charts of `ℂℙⁿ`
(`ProjectiveSpace.lean`) are the charts at the chart origins `origin i`
(`ProjectiveSpaceFubiniStudyForm.lean`), and every point has a non-vanishing coordinate, so they
cover.

* `Projectivization.affineChartCover n : ChartCover (Fin n → ℂ) (ℙ ℂ (Ambient n))`;
* `affineChartCover_m` — it has `n + 1` charts.

With it, `DifferentialForm.topFormMeasure volume e s (affineChartCover n)` is a measure on
`ℂℙⁿ` for every top-form family `s` — the object milestones M5–M7 evaluate on the wedge power
of the Fubini–Study form.

## Honest scope

⚠️ Only the cover. No top form on `ℂℙⁿ` is built here (the wedge of sections is M2), no measure is
evaluated, and nothing is said about the Fubini–Study measure.

References: `specs/top-power-scoping.md` (M3, and the ℂℙⁿ instance of the cover);
`Geometry/Manifold/TopFormMeasure.lean`; `Geometry/Manifold/Instances/ProjectiveSpace.lean`
(`chartAtIdx`, `idx`, `exists_ne_zero_coord`);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`origin`, `idx_origin`);
`specs/future-work.md`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-- The affine atlas of `ℂℙⁿ` as a finite chart cover: the charts at the `n + 1` chart origins. -/
noncomputable def affineChartCover (n : ℕ) : ChartCover (Fin n → ℂ) (ℙ ℂ (Ambient n)) where
  m := n + 1
  pt := fun i => origin i
  cover := fun x => by
    obtain ⟨i, hi⟩ := exists_ne_zero_coord x
    refine ⟨i, ?_⟩
    show x ∈ (chartAtIdx (idx (origin i))).source
    rw [idx_origin]
    exact hi

@[simp] theorem affineChartCover_m (n : ℕ) : (affineChartCover n).m = n + 1 := rfl

@[simp] theorem affineChartCover_pt (n : ℕ) (i : Fin (n + 1)) :
    (affineChartCover n).pt i = origin i := rfl

end Projectivization
