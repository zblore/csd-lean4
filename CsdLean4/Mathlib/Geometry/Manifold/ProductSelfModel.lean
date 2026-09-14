/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ExteriorDerivative
public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# A product of manifolds, charted on the product normed space

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

Mathlib charts `M × N` on the type synonym `ModelProd E F` with the model `𝓘(ℝ, E).prod 𝓘(ℝ, F)`,
and deliberately keeps that apart from the normed space `E × F` with its self model `𝓘(ℝ, E × F)`
(`modelWithCornersSelf_prod` is the bridge, and its docstring says why it is kept separate). The
corpus's form layer (`DifferentialForm.lean` … `HamiltonianFlowVolume.lean`) is stated for self
models only, so to write a form on a product it needs the product charted on `E × F`.

This module supplies exactly that, by the same product charts:

* `Prod.instChartedSpaceSelf` — `ChartedSpace (E × F) (M × N)`, the chart at `(x, y)` being
  `(chartAt E x).prod (chartAt F y)` (`chartAt_prod`, definitional);
* `Prod.instIsManifoldSelf` — `IsManifold 𝓘(ℝ, E × F) n (M × N)` from the factors, through
  Mathlib's product instance and `modelWithCornersSelf_prod`;
* ★ `fderiv_chart_transition_prod` — **the derivative of a product chart transition is the product
  of the factors' derivatives** (`ContinuousLinearMap.prodMap`), which is what the
  local-representative machinery of `ExteriorDerivative.lean` reads on a product;
* `contMDiff_fst_self`, `contMDiff_snd_self`, `hasMFDerivAt_fst_self`, `hasMFDerivAt_snd_self`,
  `ContMDiff.prodMk_self`, `HasMFDerivAt.prodMk_self` — the projections and pairings are smooth,
  with the expected derivatives, for the self model (Mathlib's statements, read through the
  bridge);
* `ChartCover.prod` — a finite chart cover of each factor gives one of the product.

## Honest scope

⚠️ **Two charted-space instances on `M × N`**, keyed on the distinct model types
`ModelProd E F` and `E × F`. Instance search never confuses them; a lemma stated for one is not
automatically available for the other, which is why the transfer lemmas at the end exist.

⚠️ **`modelWithCornersSelf_prod` is a propositional equality between models over different
`H`s.** The instance proofs rewrite along it and finish with the factor instances; nothing here
depends on the identification being definitional.

References: `Mathlib/Geometry/Manifold/IsManifold/Basic.lean` (`modelWithCornersSelf_prod`,
`ModelProd`); `Geometry/Manifold/ExteriorDerivative.lean` (`tangent_symmL_eq_fderiv`,
`contDiffAt_chart_transition`); `Geometry/Manifold/ProductForm.lean` (the consumer);
`specs/BACKLOG.md` (`R-016′`).
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

namespace Prod

/-! ### The charted space and the manifold structure -/

/-- ★ **The product charted on the normed space `E × F`**, by the product charts. -/
instance instChartedSpaceSelf : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

theorem chartAt_prod (x : M) (y : N) :
    chartAt (E × F) (x, y) = (chartAt E x).prod (chartAt F y) := rfl

theorem chartAt_prod_apply (x : M) (y : N) (p : M × N) :
    chartAt (E × F) (x, y) p = (chartAt E x p.1, chartAt F y p.2) := rfl

theorem chartAt_prod_symm_apply (x : M) (y : N) (w : E × F) :
    (chartAt (E × F) (x, y)).symm w = ((chartAt E x).symm w.1, (chartAt F y).symm w.2) := rfl

theorem chartAt_prod_source (x : M) (y : N) :
    (chartAt (E × F) (x, y)).source = (chartAt E x).source ×ˢ (chartAt F y).source := rfl

theorem chartAt_prod_target (x : M) (y : N) :
    (chartAt (E × F) (x, y)).target = (chartAt E x).target ×ˢ (chartAt F y).target := rfl

/-- The chart transition on a product is the product of the chart transitions. -/
theorem chart_transition_prod (x x' : M) (y y' : N) :
    (chartAt (E × F) (x', y') ∘ (chartAt (E × F) (x, y)).symm)
      = Prod.map (chartAt E x' ∘ (chartAt E x).symm) (chartAt F y' ∘ (chartAt F y).symm) := rfl

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- ★ **The product of manifolds is a manifold over the product normed space.** -/
instance instIsManifoldSelf {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] [IsManifold 𝓘(ℝ, F) n N] :
    IsManifold 𝓘(ℝ, E × F) n (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact (inferInstance : IsManifold (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n (M × N))

/-! ### The derivative of a product transition -/

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- ★ **The derivative of a product chart transition is the product of the factors'
derivatives**, at every point where both factor transitions are defined. -/
theorem fderiv_chart_transition_prod (x x' : M) (y y' : N) {w : E × F}
    (hw₁ : w.1 ∈ (chartAt E x).target) (hx' : (chartAt E x).symm w.1 ∈ (chartAt E x').source)
    (hw₂ : w.2 ∈ (chartAt F y).target) (hy' : (chartAt F y).symm w.2 ∈ (chartAt F y').source) :
    fderiv ℝ (chartAt (E × F) (x', y') ∘ (chartAt (E × F) (x, y)).symm) w
      = (fderiv ℝ (chartAt E x' ∘ (chartAt E x).symm) w.1).prodMap
          (fderiv ℝ (chartAt F y' ∘ (chartAt F y).symm) w.2) := by
  rw [chart_transition_prod]
  have h₁ := (contDiffAt_chart_transition x x' hw₁ hx').differentiableAt (by simp)
  have h₂ := (contDiffAt_chart_transition y y' hw₂ hy').differentiableAt (by simp)
  exact (h₁.hasFDerivAt.prodMap w h₂.hasFDerivAt).fderiv

/-! ### Smoothness of the projections and of pairings, for the self model -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem contMDiff_fst_self {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E × F) 𝓘(ℝ, E) n (Prod.fst : M × N → M) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem contMDiff_snd_self {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E × F) 𝓘(ℝ, F) n (Prod.snd : M × N → N) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- The manifold derivative of the first projection, for the self model. -/
theorem hasMFDerivAt_fst_self (p : M × N) :
    HasMFDerivAt 𝓘(ℝ, E × F) 𝓘(ℝ, E) (Prod.fst : M × N → M) p
      (ContinuousLinearMap.fst ℝ E F) := by
  rw [modelWithCornersSelf_prod]
  exact hasMFDerivAt_fst (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) p

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- The manifold derivative of the second projection, for the self model. -/
theorem hasMFDerivAt_snd_self (p : M × N) :
    HasMFDerivAt 𝓘(ℝ, E × F) 𝓘(ℝ, F) (Prod.snd : M × N → N) p
      (ContinuousLinearMap.snd ℝ E F) := by
  rw [modelWithCornersSelf_prod]
  exact hasMFDerivAt_snd (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) p

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- Replace the derivative in a `HasMFDerivAt` by an equal one. Stated once so that the equality
is used at a site where the two continuous linear maps have syntactically the same type; at a use
site `exact h.congr_deriv h'` lets unification identify the instance paths. -/
theorem _root_.HasMFDerivAt.congr_deriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {f : P → M} {x : P}
    {df df' : TangentSpace 𝓘(ℝ, G) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (f x)}
    (h : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, E) f x df) (h' : df = df') :
    HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, E) f x df' :=
  h' ▸ h

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- The manifold derivative of a pairing, for the self model on the product. -/
theorem _root_.HasMFDerivAt.prodMk_self {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {f : P → M} {g : P → N} {x : P}
    {df : TangentSpace 𝓘(ℝ, G) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (f x)}
    (hf : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, E) f x df)
    {dg : TangentSpace 𝓘(ℝ, G) x →L[ℝ] TangentSpace 𝓘(ℝ, F) (g x)}
    (hg : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, F) g x dg) :
    HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, E × F) (fun y => (f y, g y)) x (df.prod dg) := by
  rw [modelWithCornersSelf_prod]
  exact hf.prodMk hg

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem _root_.ContMDiff.prodMk_self {n : WithTop ℕ∞} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    {f : P → M} {g : P → N} (hf : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) n f)
    (hg : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) n g) :
    ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E × F) n (fun p => (f p, g p)) := by
  rw [modelWithCornersSelf_prod]
  exact hf.prodMk hg

end Prod

/-! ### Chart covers of a product -/

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- A finite chart cover of each factor covers the product by the product charts. -/
def ChartCover.prod (c : ChartCover E M) (c' : ChartCover F N) : ChartCover (E × F) (M × N) where
  m := c.m * c'.m
  pt := fun k => (c.pt (finProdFinEquiv.symm k).1, c'.pt (finProdFinEquiv.symm k).2)
  cover := fun p => by
    obtain ⟨i, hi⟩ := c.cover p.1
    obtain ⟨j, hj⟩ := c'.cover p.2
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [Prod.chartAt_prod_source]
    exact Set.mem_prod.2 ⟨hi, hj⟩

end
