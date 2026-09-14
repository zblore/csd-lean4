/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ProductForm
public import CsdLean4.Mathlib.Geometry.Manifold.TranslationAtlasForm
public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure
public import CsdLean4.Mathlib.Geometry.Manifold.WedgeForm

/-!
# Maps that preserve a form in charts, and the top-form measures they preserve

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

`TopFormMeasure.lean`'s invariance theorem `topFormMeasure_map_eq` takes its hypothesis in chart
form: through any two charts, the map is differentiable and pulls the local representative of the
form back to itself. This module names that hypothesis and gives it the closure properties that
let a product manifold inherit it from its factors:

* `DifferentialForm.PreservesLocalRep s g` — **`g^* s = s`, read in charts**;
* `preservesLocalRep_id` — the identity preserves every family (the chart-change rule
  `localRep_transition`);
* `PreservesLocalRep.wedgePow` — a map preserving a 2-form preserves its iterated powers;
* ★ `PreservesLocalRep.map_topFormMeasure` — **a homeomorphism preserving a top form in charts
  preserves its measure** (`topFormMeasure_map_eq`, repackaged);
* ★ `PreservesLocalRep.prodMap` — **a product of chart-preserving maps preserves the product
  family `π₁^* α + π₂^* β`** on the product charted over `E × F`;
* `IsChartTranslation E g` — the chart expression of `g` has derivative the identity;
  `IsChartTranslation.prodMap`; `preservesLocalRep_constFamily` (on a translation atlas a chart
  translation preserves every constant family); ★ `AddCircle.isChartTranslation_addLeft`
  (**translation of the circle is a chart translation of the translation atlas**).

## Honest scope

⚠️ **Chart-level, not intrinsic.** `PreservesLocalRep` is the chart form of "`g` is a
symplectomorphism"; the pullback of a form along a map of manifolds is not built here, so no
bundle-level statement `g^* α = α` is made.

⚠️ **Self models only**, inherited from `ExteriorDerivative.lean`.

References: `Geometry/Manifold/TopFormMeasure.lean` (`topFormMeasure_map_eq`);
`Geometry/Manifold/ProductForm.lean` (`localRep_prodFamily`,
`prodSum_compContinuousLinearMap_prodMap`); `Geometry/Manifold/TranslationAtlasForm.lean`
(`localRep_constFamily`); `Geometry/Manifold/Instances/AddCircleTranslation.lean`
(`hasFDerivAt_transition`); `specs/BACKLOG.md` (#29); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology Set MeasureTheory
open scoped Manifold Bundle Topology ContDiff

namespace DifferentialForm

/-! ### The predicate -/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

/-- **`g` preserves the family `s` in charts** (`g^* s = s`, read through any two charts): where
the chart expression of `g` is defined it is differentiable, and the pullback of the local
representative of `s` along its derivative is the local representative of `s`. This is the
hypothesis `topFormMeasure_map_eq` reads. -/
def PreservesLocalRep (s : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x)
    (g : M → M) : Prop :=
  ∀ x₀ z : M, ∀ w ∈ (chartAt E x₀).target, g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
    DifferentiableAt ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w ∧
    (localRep s z ((chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)).compContinuousLinearMap
        (fderiv ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)
      = localRep s x₀ w

/-- The identity preserves every family: the chart-change rule for local representatives. -/
theorem preservesLocalRep_id
    (s : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) :
    PreservesLocalRep s id := by
  intro x₀ z w hw hmem
  simp only [Function.id_comp]
  exact ⟨(contDiffAt_chart_transition x₀ z hw hmem).differentiableAt (by simp),
    (localRep_transition s x₀ z hw hmem).symm⟩

/-- The iterated powers of a preserved 2-form are preserved. -/
theorem PreservesLocalRep.wedgePow {α : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin 2) ℝ} {g : M → M}
    (h : PreservesLocalRep (fun x => α x) g) (k : ℕ) :
    PreservesLocalRep (fun x => DifferentialForm.wedgePow α k x) g := by
  intro x₀ z w hw hmem
  obtain ⟨hd, hinv⟩ := h x₀ z w hw hmem
  refine ⟨hd, ?_⟩
  simp only [Function.comp_apply] at hinv ⊢
  rw [localRep_wedgePow α z ((chartAt E z).map_source hmem) k, localRep_wedgePow α x₀ hw k,
    ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, hinv]

/-- ★ **A homeomorphism preserving a top-form family in charts preserves its measure.** -/
theorem PreservesLocalRep.map_topFormMeasure [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace M] [BorelSpace M] [DecidableEq ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : Module.Basis ι ℝ E)
    {s : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M ℝ x}
    (c : ChartCover E M) (g : M ≃ₜ M) (h : PreservesLocalRep s g) :
    Measure.map g (topFormMeasure μ e s c) = topFormMeasure μ e s c :=
  topFormMeasure_map_eq μ e s c g (fun x₀ z w hw hmem => (h x₀ z w hw hmem).1)
    (fun x₀ z w hw hmem => (h x₀ z w hw hmem).2)

end Basic

/-! ### Products -/

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

/-- ★ **A product of chart-preserving maps preserves the product family** `π₁^* α + π₂^* β`, on
the product charted over `E × F`. -/
theorem PreservesLocalRep.prodMap
    {α : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x}
    {β : ∀ y : N, TangentSpace 𝓘(ℝ, F) y [⋀^ι]→L[ℝ] Bundle.Trivial N G y}
    {g₁ : M → M} {g₂ : N → N} (h₁ : PreservesLocalRep α g₁) (h₂ : PreservesLocalRep β g₂) :
    PreservesLocalRep (prodFamily α β) (Prod.map g₁ g₂) := by
  rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ w hw hmem
  rw [Prod.chartAt_prod_target] at hw
  rw [Prod.chartAt_prod_source] at hmem
  obtain ⟨hw₁, hw₂⟩ := Set.mem_prod.1 hw
  obtain ⟨hm₁, hm₂⟩ := Set.mem_prod.1 hmem
  obtain ⟨hd₁, hi₁⟩ := h₁ x₀ x₁ w.1 hw₁ hm₁
  obtain ⟨hd₂, hi₂⟩ := h₂ y₀ y₁ w.2 hw₂ hm₂
  have hT : (chartAt (E × F) (x₁, y₁) ∘ Prod.map g₁ g₂ ∘ (chartAt (E × F) (x₀, y₀)).symm)
      = Prod.map (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm)
          (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) := rfl
  rw [hT]
  have hD := hd₁.hasFDerivAt.prodMap w hd₂.hasFDerivAt
  refine ⟨hD.differentiableAt, ?_⟩
  rw [hD.fderiv]
  have hw' : Prod.map (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm)
      (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) w ∈ (chartAt (E × F) (x₁, y₁)).target := by
    rw [Prod.chartAt_prod_target]
    exact Set.mem_prod.2 ⟨(chartAt E x₁).map_source hm₁, (chartAt F y₁).map_source hm₂⟩
  rw [localRep_prodFamily α β x₁ y₁ hw', localRep_prodFamily α β x₀ y₀ hw,
    ContinuousAlternatingMap.prodSum_compContinuousLinearMap_prodMap]
  have e₁ : (localRep α x₁ (Prod.map (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm)
        (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) w).1).compContinuousLinearMap
        (fderiv ℝ (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm) w.1) = localRep α x₀ w.1 := hi₁
  have e₂ : (localRep β y₁ (Prod.map (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm)
        (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) w).2).compContinuousLinearMap
        (fderiv ℝ (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) w.2) = localRep β y₀ w.2 := hi₂
  rw [e₁, e₂]

end Prod

/-! ### Chart translations -/

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable (E) in
/-- **`g` is a translation in charts**: through any two charts, its chart expression has
derivative the identity wherever it is defined. -/
def IsChartTranslation (g : M → M) : Prop :=
  ∀ x₀ z : M, ∀ w ∈ (chartAt E x₀).target, g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
    HasFDerivAt (chartAt E z ∘ g ∘ (chartAt E x₀).symm) (ContinuousLinearMap.id ℝ E) w

/-- On a translation atlas, a chart translation preserves every constant family. -/
theorem preservesLocalRep_constFamily [IsManifold 𝓘(ℝ, E) ∞ M] [HasTranslationAtlas E M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*} [Fintype ι]
    (ξ : E [⋀^ι]→L[ℝ] G) {g : M → M} (hg : IsChartTranslation E g) :
    PreservesLocalRep (constFamily ξ) g := by
  intro x₀ z w hw hmem
  have h := hg x₀ z w hw hmem
  refine ⟨h.differentiableAt, ?_⟩
  simp only [Function.comp_apply]
  rw [h.fderiv, localRep_constFamily ξ z ((chartAt E z).map_source hmem),
    localRep_constFamily ξ x₀ hw]
  exact ContinuousAlternatingMap.ext fun _ => rfl

/-- The product of two chart translations is a chart translation, for the product charted over
`E × F`. -/
theorem IsChartTranslation.prodMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] {g₁ : M → M} {g₂ : N → N}
    (h₁ : IsChartTranslation E g₁) (h₂ : IsChartTranslation F g₂) :
    IsChartTranslation (E × F) (Prod.map g₁ g₂) := by
  rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ w hw hmem
  rw [Prod.chartAt_prod_target] at hw
  rw [Prod.chartAt_prod_source] at hmem
  obtain ⟨hw₁, hw₂⟩ := Set.mem_prod.1 hw
  obtain ⟨hm₁, hm₂⟩ := Set.mem_prod.1 hmem
  have hT : (chartAt (E × F) (x₁, y₁) ∘ Prod.map g₁ g₂ ∘ (chartAt (E × F) (x₀, y₀)).symm)
      = Prod.map (chartAt E x₁ ∘ g₁ ∘ (chartAt E x₀).symm)
          (chartAt F y₁ ∘ g₂ ∘ (chartAt F y₀).symm) := rfl
  rw [hT]
  refine ((h₁ x₀ x₁ w.1 hw₁ hm₁).prodMap w (h₂ y₀ y₁ w.2 hw₂ hm₂)).congr_fderiv ?_
  exact ContinuousLinearMap.ext fun _ => rfl

end Translation

end DifferentialForm

/-! ### Translation of the circle -/

namespace AddCircle

open DifferentialForm

variable {T : ℝ} [hT : Fact (0 < T)]

/-- ★ **Translation of the circle is a chart translation of the translation atlas**: read through
two translation charts, `x ↦ θ + x` is a translation of `ℝ` near every point. -/
theorem isChartTranslation_addLeft (θ : AddCircle T) :
    IsChartTranslation ℝ (fun x : AddCircle T => θ + x) := by
  intro x₀ z w _ hmem
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hne : ((t + w : ℝ) : AddCircle T) ≠ (cutPoint z : AddCircle T) := by
    rw [coe_add]
    exact hmem
  have h := (hasFDerivAt_transition (cutPoint z) hne).comp w ((hasFDerivAt_id w).const_add t)
  rw [ContinuousLinearMap.id_comp] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  show translationChart (cutPoint z) ((t : AddCircle T) + (y : AddCircle T))
    = translationChart (cutPoint z) ((t + y : ℝ) : AddCircle T)
  rw [coe_add]

end AddCircle

end
