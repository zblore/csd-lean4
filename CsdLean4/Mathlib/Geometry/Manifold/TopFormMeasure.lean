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

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`, where
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
  ★ `topFormMeasure_congr_cover` — the measure does not depend on the cover;
* ★ `chartMeasure_preimage_eq` and ★★ `topFormMeasure_map_eq` (milestone **M5**) —
  **invariance**: a homeomorphism whose chart expressions are smooth and pull the local
  representative at the target chart back to the local representative at the source chart
  preserves the measure. The proof is chart-independence with the chart transition replaced by
  the map's chart expression, summed over the double partition by the cover's pieces and their
  images;
* ★ `isLocallyFiniteMeasure_topFormMeasure`, ★ `isFiniteMeasure_topFormMeasure` (milestone
  **M6(a)**) — the measure of a smooth top form is locally finite (a compact ball inside a chart
  has finite measure, the density being continuous there), hence finite on a compact manifold;
* ★ `topFormMeasure_ne_zero_of_localRep_ne_zero` (milestone **M6(b)**, the generic half) — a
  smooth top form whose coefficient against the basis does not vanish at one chart point has
  **nonzero** measure: the density is continuous, so bounded below on a ball, and Haar measure
  gives balls positive measure (`ContinuousAlternatingMap.continuous_eval_const`: evaluation on
  a fixed family is Lipschitz).

## Honest scope

⚠️ **A finite atlas given as data.** Compact manifolds have one, and `ℂℙⁿ`'s affine atlas is one
(`Instances/ProjectiveSpaceChartCover.lean`); nothing here handles an infinite atlas, and no
partition of unity is used — the gluing is along a measurable partition, which is why the
construction needs no paracompactness and no bump functions.

⚠️ **Densities, not integrals of forms.** The measure uses `|coefficient|`; no orientation is
chosen and none is needed. Integrating a form with its sign is not defined here.

⚠️ **Invariance, not general naturality.** `topFormMeasure_map_eq` is stated for a map that
preserves the form in charts (the hypothesis is the chart form of "`g^* s = s`"); the general
statement `measureOf (g^* s) = map g⁻¹ (measureOf s)` would need the pullback of forms along
maps of manifolds, which is not built. Non-vanishing of a particular measure reduces to one chart
coefficient at one point (`topFormMeasure_ne_zero_of_localRep_ne_zero`); computing that
coefficient is consumer-side.

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

/-! ### Evaluation on a fixed family is continuous -/

section Eval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- Evaluating a continuous alternating map on a fixed family is Lipschitz (constant
`∏ i, ‖v i‖`, by `le_opNorm`), hence continuous. -/
theorem ContinuousAlternatingMap.continuous_eval_const (v : ι → E) :
    Continuous fun α : E [⋀^ι]→L[ℝ] ℝ => α v := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨∏ i, ‖v i‖, Finset.prod_nonneg fun _ _ => norm_nonneg _⟩) fun α β => ?_).continuous
  simp only [dist_eq_norm]
  rw [← ContinuousAlternatingMap.sub_apply, mul_comm]
  exact ContinuousAlternatingMap.le_opNorm _ _

end Eval

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

/-! ### Invariance under a form-preserving homeomorphism -/

/-- ★ **A chart measure under a form-preserving map.** If `g` is injective, smooth in the charts
at `x₀` and `z`, and its chart expression pulls the local representative at `z` back to the
local representative at `x₀`, then the chart measure at `x₀` of `g ⁻¹' A` is the chart measure
at `z` of `A`. -/
theorem chartMeasure_preimage_eq (g : M → M) (hg_inj : Function.Injective g)
    (hg_surj : Function.Surjective g) (x₀ z : M)
    (hG : ∀ w ∈ (chartAt E x₀).target, g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
      ContDiffAt ℝ ∞ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)
    (hinv : ∀ w ∈ (chartAt E x₀).target, g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
      (localRep s z ((chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)).compContinuousLinearMap
        (fderiv ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w) = localRep s x₀ w)
    {A : Set M} (hA : MeasurableSet A) (hgA : MeasurableSet (g ⁻¹' A))
    (hAz : A ⊆ (chartAt E z).source) (hA₀ : g ⁻¹' A ⊆ (chartAt E x₀).source) :
    chartMeasure μ e s x₀ (g ⁻¹' A) = chartMeasure μ e s z A := by
  rw [chartMeasure_apply μ e s x₀ hgA, chartMeasure_apply μ e s z hA]
  have hS₀ := measurableSet_target_inter_preimage (E := E) x₀ hgA
  have himg : (chartAt E z).target ∩ (chartAt E z).symm ⁻¹' A
      = (chartAt E z ∘ g ∘ (chartAt E x₀).symm) ''
          ((chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' (g ⁻¹' A)) := by
    have h1 := (chartAt E z).image_eq_target_inter_inv_preimage hAz
    have h0 := (chartAt E x₀).image_eq_target_inter_inv_preimage hA₀
    calc (chartAt E z).target ∩ (chartAt E z).symm ⁻¹' A
        = chartAt E z '' A := h1.symm
      _ = chartAt E z '' (g '' (g ⁻¹' A)) := by rw [Set.image_preimage_eq A hg_surj]
      _ = chartAt E z '' (g '' ((chartAt E x₀).symm '' (chartAt E x₀ '' (g ⁻¹' A)))) := by
          congr 2
          exact ((chartAt E x₀).symm_image_image_of_subset_source hA₀).symm
      _ = (chartAt E z ∘ g ∘ (chartAt E x₀).symm) '' (chartAt E x₀ '' (g ⁻¹' A)) := by
          rw [Set.image_comp, Set.image_comp]
      _ = (chartAt E z ∘ g ∘ (chartAt E x₀).symm) ''
            ((chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' (g ⁻¹' A)) := by rw [h0]
  rw [himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hS₀
    (f' := fun w => fderiv ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w) ?_ ?_]
  · apply setLIntegral_congr_fun hS₀
    intro w hw
    have hgw : g ((chartAt E x₀).symm w) ∈ (chartAt E z).source := hAz hw.2
    simp only [chartDensity]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, ← hinv w hw.1 hgw,
      ContinuousAlternatingMap.compContinuousLinearMap_apply_basis]
  · intro w hw
    exact ((hG w hw.1 (hAz hw.2)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro w₁ hw₁ w₂ hw₂ h
    have h1 := (chartAt E z).injOn (hAz hw₁.2) (hAz hw₂.2) h
    have h2 := hg_inj h1
    exact (chartAt E x₀).symm.injOn hw₁.1 hw₂.1 h2

/-- ★★ **Invariance of the measure of a top form** under a homeomorphism that preserves the
form in charts. -/
theorem topFormMeasure_map_eq (c : ChartCover E M) (g : M ≃ₜ M)
    (hG : ∀ x₀ z : M, ∀ w ∈ (chartAt E x₀).target,
      g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
      ContDiffAt ℝ ∞ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)
    (hinv : ∀ x₀ z : M, ∀ w ∈ (chartAt E x₀).target,
      g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
      (localRep s z ((chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)).compContinuousLinearMap
        (fderiv ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w) = localRep s x₀ w) :
    Measure.map g (topFormMeasure μ e s c) = topFormMeasure μ e s c := by
  ext A hA
  rw [Measure.map_apply g.measurable hA]
  -- the double partition: pieces of the cover and their images under g
  set P : Fin c.m × Fin c.m → Set M := fun p => A ∩ (c.piece p.2 ∩ g '' c.piece p.1) with hP
  have hPmeas : ∀ p, MeasurableSet (P p) := fun p =>
    hA.inter ((c.measurableSet_piece p.2).inter
      (g.measurableEmbedding.measurableSet_image.2 (c.measurableSet_piece p.1)))
  have hPdisj : Pairwise (Disjoint on P) := by
    intro p q hpq
    rcases ne_or_eq p.2 q.2 with h2 | h2
    · exact Set.disjoint_left.2 fun x hxp hxq =>
        Set.disjoint_left.1 (c.pairwise_disjoint_piece h2) hxp.2.1 hxq.2.1
    · have h1 : p.1 ≠ q.1 := fun h1 => hpq (Prod.ext h1 h2)
      exact Set.disjoint_left.2 fun x hxp hxq =>
        Set.disjoint_left.1
          ((Set.disjoint_image_iff g.injective).2 (c.pairwise_disjoint_piece h1)) hxp.2.2 hxq.2.2
  have hPunion : ⋃ p, P p = A := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      have hj : ∃ j, x ∈ c.piece j := Set.mem_iUnion.1 (by rw [c.iUnion_piece]; exact Set.mem_univ x)
      have hi : ∃ i, g.symm x ∈ c.piece i :=
        Set.mem_iUnion.1 (by rw [c.iUnion_piece]; exact Set.mem_univ _)
      obtain ⟨j, hj⟩ := hj
      obtain ⟨i, hi⟩ := hi
      exact Set.mem_iUnion.2 ⟨(i, j), hx, hj, ⟨g.symm x, hi, g.apply_symm_apply x⟩⟩
  -- each piece is handled by the chart pair (pt i, pt j)
  have hpiece : ∀ p : Fin c.m × Fin c.m,
      topFormMeasure μ e s c (g ⁻¹' P p) = topFormMeasure μ e s c (P p) := by
    intro p
    have hsub_z : P p ⊆ (chartAt E (c.pt p.2)).source := fun x hx => c.piece_subset _ hx.2.1
    have hsub_0 : g ⁻¹' P p ⊆ (chartAt E (c.pt p.1)).source := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hx.2.2
      have : y = x := g.injective hyx
      subst this
      exact c.piece_subset _ hy
    rw [topFormMeasure_apply_of_subset_source μ e s c (c.pt p.1) (g.measurable (hPmeas p)) hsub_0,
      topFormMeasure_apply_of_subset_source μ e s c (c.pt p.2) (hPmeas p) hsub_z]
    exact chartMeasure_preimage_eq μ e s g g.injective g.surjective (c.pt p.1) (c.pt p.2)
      (hG _ _) (hinv _ _) (hPmeas p) (g.measurable (hPmeas p)) hsub_z hsub_0
  calc topFormMeasure μ e s c (g ⁻¹' A)
      = topFormMeasure μ e s c (⋃ p, g ⁻¹' P p) := by rw [← Set.preimage_iUnion, hPunion]
    _ = ∑' p, topFormMeasure μ e s c (g ⁻¹' P p) :=
        measure_iUnion (fun p q hpq => (hPdisj hpq).preimage g) (fun p => g.measurable (hPmeas p))
    _ = ∑' p, topFormMeasure μ e s c (P p) := by simp_rw [hpiece]
    _ = topFormMeasure μ e s c (⋃ p, P p) := (measure_iUnion hPdisj hPmeas).symm
    _ = topFormMeasure μ e s c A := by rw [hPunion]

/-! ### Local finiteness, and positivity -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  in
theorem continuousOn_localRep
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] ℝ))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] ℝ) x (s x)))
    (x₀ : M) : ContinuousOn (localRep s x₀) (chartAt E x₀).target :=
  fun _ hw => (contDiffAt_localRep s hs x₀ hw).continuousAt.continuousWithinAt

/-- ★ **The measure of a smooth top form is locally finite**: a compact ball inside a chart has
finite measure because the density is continuous there. -/
theorem isLocallyFiniteMeasure_topFormMeasure
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] ℝ))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] ℝ) x (s x)))
    (c : ChartCover E M) : IsLocallyFiniteMeasure (topFormMeasure μ e s c) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target (chartAt E x x)
    (mem_chart_target E x)
  set K := Metric.closedBall (chartAt E x x) (r / 2) with hKdef
  have hK : K ⊆ (chartAt E x).target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hKc : IsCompact K := isCompact_closedBall _ _
  set V := (chartAt E x).source ∩ chartAt E x ⁻¹' K with hVdef
  refine ⟨V, ?_, ?_⟩
  · have hopen : IsOpen ((chartAt E x).source ∩ chartAt E x ⁻¹' Metric.ball (chartAt E x x) (r / 2)) :=
      (chartAt E x).continuousOn.isOpen_inter_preimage (chartAt E x).open_source Metric.isOpen_ball
    exact Filter.mem_of_superset
      (hopen.mem_nhds ⟨mem_chart_source E x, Metric.mem_ball_self (by linarith)⟩)
      (Set.inter_subset_inter_right _ (Set.preimage_mono Metric.ball_subset_closedBall))
  · have hVmeas : MeasurableSet V :=
      MeasurableSet.inter_preimage_of_continuousOn (chartAt E x).continuousOn
        (chartAt E x).open_source.measurableSet hKc.isClosed.measurableSet
    rw [topFormMeasure_apply_of_subset_source μ e s c x hVmeas Set.inter_subset_left,
      chartMeasure_apply μ e s x hVmeas]
    have hsub : (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' V ⊆ K := by
      rintro w ⟨hw, hwV⟩
      have := hwV.2
      rwa [Set.mem_preimage, (chartAt E x).right_inv hw] at this
    have hcont : ContinuousOn (fun w => localRep s x w e) K :=
      (ContinuousAlternatingMap.continuous_eval_const e).comp_continuousOn
        ((continuousOn_localRep s hs x).mono hK)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
    calc ∫⁻ w in (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' V, chartDensity e s x w ∂μ
        ≤ ∫⁻ w in K, chartDensity e s x w ∂μ := lintegral_mono_set hsub
      _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂μ := by
          refine setLIntegral_mono measurable_const fun w hw => ?_
          simp only [chartDensity]
          exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC w hw)
      _ = ENNReal.ofReal C * μ K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top

/-- ★ On a compact manifold, the measure of a smooth top form is finite. -/
theorem isFiniteMeasure_topFormMeasure [CompactSpace M]
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] ℝ))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] ℝ) x (s x)))
    (c : ChartCover E M) : IsFiniteMeasure (topFormMeasure μ e s c) := by
  have := isLocallyFiniteMeasure_topFormMeasure μ e s hs c
  infer_instance

/-- ★ **A smooth top form whose coefficient does not vanish at one chart point has nonzero
measure.** The density is continuous, so it is bounded below by a positive constant on a ball
around that point, and Haar measure gives balls positive measure. -/
theorem topFormMeasure_ne_zero_of_localRep_ne_zero
    (hs : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ (E [⋀^ι]→L[ℝ] ℝ))) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] ℝ) x (s x)))
    (c : ChartCover E M) (x₀ : M) {w₀ : E} (hw₀ : w₀ ∈ (chartAt E x₀).target)
    (hne : localRep s x₀ w₀ e ≠ 0) : topFormMeasure μ e s c ≠ 0 := by
  intro hzero
  have hsrc : topFormMeasure μ e s c (chartAt E x₀).source = 0 := by simp [hzero]
  rw [topFormMeasure_apply_of_subset_source μ e s c x₀ (chartAt E x₀).open_source.measurableSet
    subset_rfl, chartMeasure_apply μ e s x₀ (chartAt E x₀).open_source.measurableSet] at hsrc
  have hcont : ContinuousAt (fun w => |localRep s x₀ w e|) w₀ :=
    ((ContinuousAlternatingMap.continuous_eval_const e).continuousAt.comp
      (contDiffAt_localRep s hs x₀ hw₀).continuousAt).abs
  set c₀ : ℝ := |localRep s x₀ w₀ e| / 2 with hc₀
  have habs : 0 < |localRep s x₀ w₀ e| := abs_pos.2 hne
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hlow : ∀ᶠ w in 𝓝 w₀, c₀ < |localRep s x₀ w e| :=
    continuousAt_const.eventually_lt hcont (by rw [hc₀]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
    (hlow.and ((chartAt E x₀).open_target.mem_nhds hw₀))
  have hsub : Metric.ball w₀ r ⊆
      (chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' (chartAt E x₀).source :=
    fun w hw => ⟨(hball hw).2, (chartAt E x₀).map_target (hball hw).2⟩
  have hpos : 0 < ∫⁻ w in Metric.ball w₀ r, chartDensity e s x₀ w ∂μ := by
    calc (0 : ℝ≥0∞) < ENNReal.ofReal c₀ * μ (Metric.ball w₀ r) :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc₀pos).ne' (Metric.measure_ball_pos μ w₀ hr).ne'
      _ = ∫⁻ _ in Metric.ball w₀ r, ENNReal.ofReal c₀ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Metric.ball w₀ r, chartDensity e s x₀ w ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
            (Filter.Eventually.of_forall fun w hw => ?_))
          exact ENNReal.ofReal_le_ofReal (le_of_lt (hball hw).1)
  have := lintegral_mono_set (μ := μ) (f := chartDensity e s x₀) hsub
  rw [hsrc] at this
  exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl _)

end DifferentialForm

end TopFormMeasure
