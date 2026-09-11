/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# `AddCircle T` is an analytic manifold, and so is the torus

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`,
beside `Sphere.lean`). Mathlib charts `Circle` (the unit complex numbers) and proves it an analytic
Lie group, but `AddCircle T = ℝ ⧸ ℤ • T` — the type the corpus's torus fibre is built on — has no
`ChartedSpace` at the pin, and `Mathlib/Geometry/Manifold/Instances/Quotient.lean` lists the
quotient `IsManifold` as its own TODO.

**Transport along a homeomorphism.** For `f : M ≃ₜ M'` and a charted space `M`, the atlas
`{ f.symm ≫ₕ e | e ∈ atlas M }` charts `M'`, and its transitions are exactly `M`'s:
`(f.symm ≫ₕ e).symm ≫ₕ (f.symm ≫ₕ e') = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' = e.symm ≫ₕ e'` on the nose
(`Homeomorph.symm_trans_self`). So every groupoid `M` has, `M'` has (`hasGroupoid_transport`), and in
particular `IsManifold I n M'` for every `I`, `n`. This is the general statement; nothing about the
circle is used until the last section.

* `Homeomorph.transportChartedSpace f` — the transported charted space (a `def`, not an instance:
  a type may already carry a charted space);
* ★ `Homeomorph.hasGroupoid_transport` / `isManifold_transport` — **the transported structure has
  every groupoid the source has**; transitions are the source's transitions, on the nose
  (`transport_transition`).
* `AddCircle.instChartedSpace`, ★ `AddCircle.instIsManifold` — **`AddCircle T` (`T ≠ 0`) is an
  analytic manifold**, transported from `Circle` along `AddCircle.homeomorphCircle`.
* ★ `AddCircle.instIsManifoldProd` — **the torus `AddCircle T × AddCircle T'` is an analytic
  manifold** (Mathlib's product instance, once each factor is one).

## Honest scope

⚠️ **`T ≠ 0` is a `Fact`.** The homeomorphism `AddCircle T ≃ₜ Circle` needs `T ≠ 0`; the instance
takes it as `[Fact (T ≠ 0)]`, which Mathlib's `AddCircle` API already uses for `T > 0`
(`Fact (0 < T)` gives it). The corpus's fibre is `AddCircle (1 : ℝ)`.

⚠️ **Not stated:** that `homeomorphCircle` itself is `C^ω` for the transported structure (it is the
identity in charts, a one-line `contMDiffAt_iff` argument) — nothing consumes it.

⚠️ **The transported atlas is not the "obvious" one.** A reader expecting charts `AddCircle T → ℝ`
from `QuotientAddGroup.mk` finds instead charts through `Circle ⊂ ℂ` into `EuclideanSpace ℝ (Fin 1)`
(the stereographic charts of the unit sphere in `ℂ`). The model is `𝓡 1`, not `𝓘(ℝ, ℝ)`. That is
what Mathlib's `Circle` has, and the transport inherits it; a direct `𝓘(ℝ, ℝ)` atlas would be a
second instance and is not built.

References: `specs/generator-layer-scoping.md` §11 (Q33); `specs/reconstruction-status.md` §2a (A3);
`Mathlib/Geometry/Manifold/Instances/Sphere.lean` (`Circle`'s instances);
`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (`AddCircle.homeomorphCircle`).
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

/-! ### Transport of a charted space and its groupoids along a homeomorphism -/

namespace Homeomorph

variable {H M M' : Type*} [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] (f : M ≃ₜ M')

/-- The charted space on `M'` transported from `M` along `f`: the charts are
`f.symm ≫ₕ e` for `e` a chart of `M`. -/
@[instance_reducible]
def transportChartedSpace : ChartedSpace H M' where
  atlas := {c | ∃ e ∈ atlas H M, c = f.symm.toOpenPartialHomeomorph.trans e}
  chartAt x := f.symm.toOpenPartialHomeomorph.trans (chartAt H (f.symm x))
  mem_chart_source x := by
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.univ_inter, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply]
    exact mem_chart_source H (f.symm x)
  chart_mem_atlas x := ⟨chartAt H (f.symm x), chart_mem_atlas H _, rfl⟩

omit [ChartedSpace H M] in
/-- The transitions of the transported atlas are the transitions of the source atlas, on the
nose: `f ≫ₕ f.symm` cancels. -/
theorem transport_transition (e e' : OpenPartialHomeomorph M H) :
    (f.symm.toOpenPartialHomeomorph.trans e).symm.trans (f.symm.toOpenPartialHomeomorph.trans e')
      = e.symm.trans e' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc f.symm.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_symm, Homeomorph.self_trans_symm, Homeomorph.refl_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.refl_trans]

/-- ★ **The transported structure has every groupoid the source has.** -/
theorem hasGroupoid_transport (G : StructureGroupoid H) [HasGroupoid M G] :
    @HasGroupoid H _ M' _ (f.transportChartedSpace) G := by
  let _ : ChartedSpace H M' := f.transportChartedSpace
  refine ⟨fun {c c'} hc hc' => ?_⟩
  obtain ⟨e, he, rfl⟩ := hc
  obtain ⟨e', he', rfl⟩ := hc'
  rw [transport_transition]
  exact HasGroupoid.compatible he he'

/-- ★ **A manifold structure transports along a homeomorphism.** -/
theorem isManifold_transport {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (f.transportChartedSpace) := by
  let _ : ChartedSpace H M' := f.transportChartedSpace
  exact { toHasGroupoid := f.hasGroupoid_transport (contDiffGroupoid n I) }

end Homeomorph

/-! ### `AddCircle T` -/

namespace AddCircle

variable {T : ℝ} [hT : Fact (T ≠ 0)]

/-- `AddCircle T` is charted by the stereographic charts of `Circle ⊂ ℂ`, through
`homeomorphCircle`. -/
instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle T) :=
  (homeomorphCircle hT.out).symm.transportChartedSpace

/-- ★ **`AddCircle T` is an analytic manifold.** -/
instance instIsManifold : IsManifold (𝓡 1) ω (AddCircle T) :=
  (homeomorphCircle hT.out).symm.isManifold_transport (𝓡 1) ω

end AddCircle

/-! ### The torus -/

namespace AddCircle

variable {T T' : ℝ} [Fact (T ≠ 0)] [Fact (T' ≠ 0)]

/-- ★ **The torus `AddCircle T × AddCircle T'` is an analytic manifold**, modelled on
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`. Mathlib's product instance, once each
factor has one. -/
instance instIsManifoldProd :
    IsManifold ((𝓡 1).prod (𝓡 1)) ω (AddCircle T × AddCircle T') :=
  inferInstance

end AddCircle

end
