/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ExteriorDerivative
public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.TopForm
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The measure of a top-degree form on a manifold

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`, where
no measure or integration on manifolds exists at the pin — `Riemannian/Basic.lean` imports measure
theory for path lengths only).

Milestone **M3** of `specs/top-power-scoping.md`: a form whose degree is a basis index type of
the model space has, in every chart, a density — the absolute value of its coefficient against
the basis — and those densities glue to a measure on the manifold.

* `DifferentialForm.chartDensity e s x₀ w` — `|coefficient of the local representative of s in
  the chart at x₀, at w|`, as an `ℝ≥0∞`;
* `DifferentialForm.chartMeasure μ e s x₀` — the density measure on the chart's target (against
  a Haar measure `μ` on the model), pushed to `M` by the chart; `chartMeasure_apply` reads it as
  an integral over the chart image;
* ★★ `DifferentialForm.chartMeasure_congr` — **chart-independence**: on a measurable set inside
  two chart domains the two chart measures agree. Change of variables along the chart transition
  (`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`), whose Jacobian is exactly the
  factor by which the coefficient of a top form transforms (`compContinuousLinearMap_apply_basis`
  through `localRep_transition`). This is the whole content of "a top form is a density";
* `ChartCover E M` — a finite cover of `M` by chart domains, **as data** (`m` base points), with
  the measurable partition `piece i` subordinate to it (`measurableSet_piece`,
  `pairwise_disjoint_piece`, `iUnion_piece`);
* ★★ `DifferentialForm.topFormMeasure μ e s c` — **the measure of a top form**: the chart
  measures glued along the partition;
* ★★ `topFormMeasure_apply_of_subset_source` — on a measurable set inside **any** chart domain
  (not only the cover's) the glued measure is that chart's measure; hence
  ★ `topFormMeasure_congr_cover` — the measure does not depend on the cover.

## Honest scope

⚠️ **A finite atlas given as data.** Compact manifolds have one, and `ℂℙⁿ`'s affine atlas is one
(`Instances/ProjectiveSpaceChartCover.lean`); nothing here handles an infinite atlas, and no
partition of unity is used — the gluing is along a measurable partition, which is why the
construction needs no paracompactness and no bump functions.

⚠️ **Densities, not integrals of forms.** The measure uses `|coefficient|`; no orientation is
chosen and none is needed. Integrating a form with its sign is not defined here.

⚠️ **No naturality yet.** That a diffeomorphism carries the measure of a pulled-back form to the
pushforward measure is milestone M5 and needs the pullback of forms (M4); it is not here.
Finiteness and non-vanishing of any particular measure are likewise consumer-side (M6).

⚠️ **`∞` and `𝓘(ℝ, E)` only**, inherited from `ExteriorDerivative.lean`; the model `E` is
finite-dimensional real, Borel, with an additive Haar measure supplied as an argument.

References: `specs/top-power-scoping.md` (M3); `Analysis/Normed/Module/Alternating/TopForm.lean`
(M1, the Jacobian rule); `Geometry/Manifold/ExteriorDerivative.lean` (`localRep`,
`localRep_transition`, `contDiffAt_chart_transition`);
`Mathlib/MeasureTheory/Function/Jacobian.lean`; `specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology Set MeasureTheory Function
open scoped Manifold Bundle Topology ContDiff ENNReal

noncomputable section

/-- A set on which `f` is continuous, intersected with the preimage of a measurable set, is
measurable. -/
theorem MeasurableSet.inter_preimage_of_continuousOn {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {s : Set X} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    {A : Set Y} (hA : MeasurableSet A) : MeasurableSet (s ∩ f ⁻¹' A) := by
  have hm : Measurable (fun x : s => f x) :=
    (hf.comp_continuous continuous_subtype_val Subtype.prop).measurable
  have h1 : MeasurableSet ((fun x : s => f x) ⁻¹' A) := hm hA
  have h2 : MeasurableSet (Subtype.val '' ((fun x : s => f x) ⁻¹' A)) :=
    (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 h1
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩
  · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
    exact ⟨hy, hfy⟩

/-! ### Finite chart covers and their measurable partitions -/

section ChartCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A finite cover of `M` by chart domains, as data: `m` base points whose charts cover `M`. -/
structure ChartCover (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Type*)
    [TopologicalSpace M] [ChartedSpace E M] where
  /-- The number of charts. -/
  m : ℕ
  /-- The base points of the charts. -/
  pt : Fin m → M
  /-- The chart domains cover `M`. -/
  cover : ∀ x : M, ∃ i, x ∈ (chartAt E (pt i)).source

namespace ChartCover

variable (c : ChartCover E M)

/-- The `i`-th piece of the measurable partition subordinate to the cover: the `i`-th chart
domain minus the earlier ones. -/
def piece (i : Fin c.m) : Set M :=
  (chartAt E (c.pt i)).source \ ⋃ j, ⋃ (_ : j < i), (chartAt E (c.pt j)).source

theorem piece_subset (i : Fin c.m) : c.piece i ⊆ (chartAt E (c.pt i)).source :=
  Set.sdiff_subset

theorem measurableSet_piece [MeasurableSpace M] [BorelSpace M] (i : Fin c.m) :
    MeasurableSet (c.piece i) :=
  (chartAt E (c.pt i)).open_source.measurableSet.diff
    (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      (chartAt E (c.pt j)).open_source.measurableSet)

theorem pairwise_disjoint_piece : Pairwise (Disjoint on c.piece) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Set.disjoint_left.2 fun x hxi hxj =>
      hxj.2 (Set.mem_iUnion₂.2 ⟨i, h, hxi.1⟩)
  · exact Set.disjoint_left.2 fun x hxi hxj =>
      hxi.2 (Set.mem_iUnion₂.2 ⟨j, h, hxj.1⟩)

theorem iUnion_piece : ⋃ i, c.piece i = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨i₀, hi₀⟩ := c.cover x
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun i => x ∈ (chartAt E (c.pt i)).source) id
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀⟩⟩
  refine Set.mem_iUnion.2 ⟨i, (Finset.mem_filter.1 hi).2, ?_⟩
  intro hx
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx
  have := hmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxj⟩)
  exact absurd (lt_of_lt_of_le hj this) (lt_irrefl _)

/-- A measurable set is the disjoint union of its traces on the pieces. -/
theorem iUnion_inter_piece (A : Set M) : ⋃ i, A ∩ c.piece i = A := by
  rw [← Set.inter_iUnion, c.iUnion_piece, Set.inter_univ]

end ChartCover

end ChartCover

/-! ### Chart densities and chart measures -/

section TopFormMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [μ.IsAddHaarMeasure] (e : Module.Basis ι ℝ E)

namespace DifferentialForm

variable (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M ℝ x)

/-- The density of a top-form family in the chart at `x₀`: the absolute value of the
coefficient of its local representative against the basis `e`. -/
def chartDensity (x₀ : M) (w : E) : ℝ≥0∞ := ENNReal.ofReal |localRep s x₀ w e|

/-- The chart measure: the density measure on the chart's target, pushed to `M` by the chart. -/
def chartMeasure (x₀ : M) : Measure M :=
  Measure.map (chartAt E x₀).symm
    ((μ.restrict (chartAt E x₀).target).withDensity (chartDensity e s x₀))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold (modelWithCornersSelf ℝ E) ∞ M] in
theorem measurableSet_target_inter_preimage (x₀ : M) {A : Set M} (hA : MeasurableSet A) :
    MeasurableSet ((chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' A) :=
  MeasurableSet.inter_preimage_of_continuousOn (chartAt E x₀).continuousOn_symm
    (chartAt E x₀).open_target.measurableSet hA

omit [DecidableEq ι] in
theorem chartMeasure_apply (x₀ : M) {A : Set M} (hA : MeasurableSet A) :
    chartMeasure μ e s x₀ A
      = ∫⁻ w in (chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' A, chartDensity e s x₀ w ∂μ := by
  have hT := (chartAt E x₀).open_target.measurableSet
  have hae : AEMeasurable (chartAt E x₀).symm
      ((μ.restrict (chartAt E x₀).target).withDensity (chartDensity e s x₀)) :=
    ((chartAt E x₀).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [chartMeasure, Measure.map_apply_of_aemeasurable hae hA, withDensity_apply' _ _,
    Measure.restrict_restrict' hT, Set.inter_comm]

/-- ★★ **Chart-independence.** On a measurable set inside two chart domains the two chart
measures agree: change of variables along the transition, whose Jacobian is exactly the factor
by which the coefficient of a top form transforms (`compContinuousLinearMap_apply_basis`). -/
theorem chartMeasure_congr (x₀ y : M) {A : Set M} (hA : MeasurableSet A)
    (hA₀ : A ⊆ (chartAt E x₀).source) (hAy : A ⊆ (chartAt E y).source) :
    chartMeasure μ e s x₀ A = chartMeasure μ e s y A := by
  rw [chartMeasure_apply μ e s x₀ hA, chartMeasure_apply μ e s y hA]
  have hS₀ := measurableSet_target_inter_preimage (E := E) x₀ hA
  have himg : (chartAt E y).target ∩ (chartAt E y).symm ⁻¹' A
      = (chartAt E y ∘ (chartAt E x₀).symm) ''
          ((chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' A) := by
    have h1 := (chartAt E y).image_eq_target_inter_inv_preimage hAy
    have h0 := (chartAt E x₀).image_eq_target_inter_inv_preimage hA₀
    calc (chartAt E y).target ∩ (chartAt E y).symm ⁻¹' A
        = chartAt E y '' A := h1.symm
      _ = chartAt E y '' ((chartAt E x₀).symm '' (chartAt E x₀ '' A)) := by
          congr 1
          exact ((chartAt E x₀).symm_image_image_of_subset_source hA₀).symm
      _ = (chartAt E y ∘ (chartAt E x₀).symm) '' (chartAt E x₀ '' A) :=
          (Set.image_comp _ _ _).symm
      _ = (chartAt E y ∘ (chartAt E x₀).symm) ''
            ((chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' A) := by rw [h0]
  rw [himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hS₀
    (f' := fun w => fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w) ?_ ?_]
  · apply setLIntegral_congr_fun hS₀
    intro w hw
    have hy : (chartAt E x₀).symm w ∈ (chartAt E y).source := hAy hw.2
    simp only [chartDensity, Function.comp_apply]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
      localRep_transition s x₀ y hw.1 hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply_basis]
  · intro w hw
    exact ((contDiffAt_chart_transition x₀ y hw.1 (hAy hw.2)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro w₁ hw₁ w₂ hw₂ h
    have h1 := (chartAt E y).injOn (hAy hw₁.2) (hAy hw₂.2) h
    exact (chartAt E x₀).symm.injOn hw₁.1 hw₂.1 h1

/-! ### The glued measure -/

/-- ★★ **The measure of a top form** on a manifold with a finite chart cover: the chart measures,
glued along the measurable partition subordinate to the cover. -/
def topFormMeasure (c : ChartCover E M) : Measure M :=
  Measure.sum fun i => (chartMeasure μ e s (c.pt i)).restrict (c.piece i)

/-- ★★ On a measurable set inside **any** chart domain the glued measure is that chart's
measure: the gluing did not depend on the ordering of the cover, and on chart domains the
measure is what it should be. -/
theorem topFormMeasure_apply_of_subset_source (c : ChartCover E M) (y : M) {A : Set M}
    (hA : MeasurableSet A) (hAy : A ⊆ (chartAt E y).source) :
    topFormMeasure μ e s c A = chartMeasure μ e s y A := by
  rw [topFormMeasure, Measure.sum_apply _ hA]
  simp_rw [Measure.restrict_apply hA]
  have hcongr : ∀ j, chartMeasure μ e s (c.pt j) (A ∩ c.piece j)
      = chartMeasure μ e s y (A ∩ c.piece j) := fun j =>
    chartMeasure_congr μ e s (c.pt j) y (hA.inter (c.measurableSet_piece j))
      (fun x hx => c.piece_subset j hx.2) (fun x hx => hAy hx.1)
  simp_rw [hcongr]
  rw [← measure_iUnion (fun j k hjk => (c.pairwise_disjoint_piece hjk).mono
      Set.inter_subset_right Set.inter_subset_right)
    (fun j => hA.inter (c.measurableSet_piece j)), c.iUnion_inter_piece]

/-- ★ **The measure does not depend on the cover.** -/
theorem topFormMeasure_congr_cover (c c' : ChartCover E M) :
    topFormMeasure μ e s c = topFormMeasure μ e s c' := by
  ext A hA
  have hdecomp : ∀ ν : Measure M, ν A = ∑' i, ν (A ∩ c'.piece i) := fun ν => by
    conv_lhs => rw [← c'.iUnion_inter_piece A]
    exact measure_iUnion (fun j k hjk => (c'.pairwise_disjoint_piece hjk).mono
      Set.inter_subset_right Set.inter_subset_right)
      (fun j => hA.inter (c'.measurableSet_piece j))
  rw [hdecomp, hdecomp (topFormMeasure μ e s c')]
  congr 1
  ext i
  rw [topFormMeasure_apply_of_subset_source μ e s c (c'.pt i) (hA.inter (c'.measurableSet_piece i))
      (fun x hx => c'.piece_subset i hx.2),
    topFormMeasure_apply_of_subset_source μ e s c' (c'.pt i) (hA.inter (c'.measurableSet_piece i))
      (fun x hx => c'.piece_subset i hx.2)]

end DifferentialForm

end TopFormMeasure
