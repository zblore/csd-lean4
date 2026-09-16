/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The Riemannian volume of a metric on a manifold, from chart Gram densities

**Category:** 1-Mathlib (measure theory on manifolds: the Riemannian volume measure of a
metric family, absent from Mathlib at the pin — `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`
has Riemannian *bundles*, no volume; G17 of the generator-layer plan §9).

A Riemannian metric `g` on a manifold `M` modelled on `E` has, in the chart at `x₀`, the Gram matrix
`G_{x₀}(w)ᵢⱼ = g (symmL (eᵢ)) (symmL (eⱼ))` against a basis `e` of `E` (the metric at the point under
`w`, read through the tangent trivialisation), and its Riemannian volume has the chart density
`√det G_{x₀}(w)`. This module builds the measure exactly as `TopFormMeasure.lean` builds the measure
of a top form — chart densities glued along the measurable partition of a `ChartCover` — with the
Gram density in place of the top-form coefficient.

* `RiemannianMetric.localRep g x₀ w u v` — the local representative of the metric family in the
  chart at `x₀`;
* `RiemannianMetric.gram e g x₀ w` — its Gram matrix against `e`;
* `RiemannianMetric.chartDensity e g x₀ w = ENNReal.ofReal √det` — the Riemannian chart density;
* `RiemannianMetric.chartMeasure μ e g x₀` — the density measure on the chart's target, pushed to
  `M` by the chart (`chartMeasure_apply`);
* ★★ `RiemannianMetric.riemannianVolume μ e g c` — **the Riemannian volume of `g`**, glued along
  the cover `c`;
* ★★ `RiemannianMetric.riemannianVolume_eq_smul_topFormMeasure` — **if in every chart of the cover
  the Gram density is `k` times the coefficient density of a top form, the Riemannian volume is `k`
  times the top-form measure.** This is the bridge the Kähler identity `vol_g = ω^{∧n}/n!` uses on
  `ℂℙⁿ` (`Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`);
* **Q30 / G17b (2026-09-11).** For a bilinear family (`IsBilinear g`, the four pointwise
  equations): `localRep_transition` (the local representative pulls back along the transition's
  derivative), ★ `chartDensity_transition` (**the Jacobian rule for Gram densities**,
  `√det G_{x₀} = |det Dφ| · √det G_y ∘ φ`, from the congruence `Aᵀ G A` and `det_transpose`),
  ★★ `chartMeasure_congr` (chart-independence, by change of variables), and ★★
  `riemannianVolume_congr_cover` — **the Riemannian volume is canonical**: it does not depend on
  the chart cover. The proofs are those of `TopFormMeasure.lean` with the Gram rule in place of
  the top-form coefficient rule.

## Honest scope

⚠️ **Chart-independence needs bilinearity, and asks for it.** The definitions take a bare family
`g` so that they ask nothing; `chartMeasure_congr` and `riemannianVolume_congr_cover` take
`IsBilinear g` (pointwise bilinearity, the four equations), which is what the Gram congruence
`Aᵀ G A` uses and all a metric has. No symmetry or positivity is asked; a family with a
non-positive Gram determinant has chart density `0` there and the theorems still hold.

⚠️ **`g` is a family, not a section.** No smoothness or symmetry of `g` is assumed by the
definitions; a non-positive Gram determinant gives density `0` (`Real.sqrt` of a negative is `0`).
The ℂℙⁿ instance supplies a genuine metric (`isBilinear_fsMetric`). Not stated: that an isometry
preserves `riemannianVolume` (the twin of `topFormMeasure_map_eq`; same route, no consumer).

**Provenance and references.** The generator-layer plan (G17); `Geometry/Manifold/TopFormMeasure.lean` (the
construction mirrored); `Instances/ProjectiveSpaceFubiniStudyRiemannian.lean` (the instance).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

section RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [μ.IsAddHaarMeasure] (e : Module.Basis ι ℝ E)

namespace RiemannianMetric

variable (g : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x →
  TangentSpace (modelWithCornersSelf ℝ E) x → ℝ)

/-- The local representative of a metric family in the chart at `x₀`: the metric at the point
under `w`, on tangent vectors read through the tangent trivialisation. Outside the chart's target it
is junk; every use is at a point of the target. -/
def localRep (x₀ : M) (w : E) (u v : E) : ℝ :=
  g ((chartAt E x₀).symm w)
    ((trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ
      ((chartAt E x₀).symm w) u)
    ((trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ
      ((chartAt E x₀).symm w) v)

/-- The Gram matrix of the local representative against the basis `e`. -/
def gram (x₀ : M) (w : E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => localRep g x₀ w (e i) (e j)

/-- The Riemannian chart density `√det G`. -/
def chartDensity (x₀ : M) (w : E) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (gram e g x₀ w).det)

/-- The Riemannian chart measure: the density measure on the chart's target, pushed to `M` by the
chart. -/
def chartMeasure (x₀ : M) : Measure M :=
  Measure.map (chartAt E x₀).symm
    ((μ.restrict (chartAt E x₀).target).withDensity (chartDensity e g x₀))

theorem chartMeasure_apply (x₀ : M) {A : Set M} (hA : MeasurableSet A) :
    chartMeasure μ e g x₀ A
      = ∫⁻ w in (chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' A, chartDensity e g x₀ w ∂μ := by
  have hT := (chartAt E x₀).open_target.measurableSet
  have hae : AEMeasurable (chartAt E x₀).symm
      ((μ.restrict (chartAt E x₀).target).withDensity (chartDensity e g x₀)) :=
    ((chartAt E x₀).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [chartMeasure, Measure.map_apply_of_aemeasurable hae hA, withDensity_apply' _ _,
    Measure.restrict_restrict' hT, Set.inter_comm]

/-- ★★ **The Riemannian volume of a metric family**, against a chart cover: the chart densities
`√det G` glued along the cover's measurable partition. -/
def riemannianVolume (c : ChartCover E M) : Measure M :=
  Measure.sum fun i => (chartMeasure μ e g (c.pt i)).restrict (c.piece i)

/-- ★★ **The Riemannian volume against a top-form measure.** If in every chart of the cover the
Gram density is `k` times the coefficient density of a top form `s` (on the chart's target), then
the Riemannian volume is `k` times the measure of `s`. -/
theorem riemannianVolume_eq_smul_topFormMeasure (c : ChartCover E M)
    (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M ℝ x)
    (k : ℝ≥0∞) (hk : k ≠ ⊤)
    (h : ∀ (i : Fin c.m), ∀ w ∈ (chartAt E (c.pt i)).target,
      chartDensity e g (c.pt i) w = k * DifferentialForm.chartDensity e s (c.pt i) w) :
    riemannianVolume μ e g c = k • DifferentialForm.topFormMeasure μ e s c := by
  ext A hA
  rw [riemannianVolume, DifferentialForm.topFormMeasure, Measure.smul_apply, Measure.sum_apply _ hA,
    Measure.sum_apply _ hA, smul_eq_mul, ← ENNReal.tsum_mul_left]
  congr 1
  funext i
  have hAi : MeasurableSet (A ∩ c.piece i) := hA.inter (c.measurableSet_piece i)
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, chartMeasure_apply μ e g _ hAi,
    DifferentialForm.chartMeasure_apply μ e s _ hAi, ← lintegral_const_mul' _ _ hk]
  refine setLIntegral_congr_fun
    (DifferentialForm.measurableSet_target_inter_preimage (E := E) (c.pt i) hAi) ?_
  intro w hw
  exact h i w hw.1


/-! ### Chart-independence (Q30 / G17b) -/

/-- **Bilinearity of a metric family**, pointwise: the four equations the Gram congruence needs.
`RiemannianMetric.localRep` takes a bare family so that the definitions ask nothing; the
chart-independence theorems ask for this. -/
structure IsBilinear : Prop where
  add_left : ∀ (x : M) (a b v : TangentSpace (modelWithCornersSelf ℝ E) x), g x (a + b) v = g x a v + g x b v
  smul_left : ∀ (x : M) (c : ℝ) (a v : TangentSpace (modelWithCornersSelf ℝ E) x), g x (c • a) v = c * g x a v
  add_right : ∀ (x : M) (v a b : TangentSpace (modelWithCornersSelf ℝ E) x), g x v (a + b) = g x v a + g x v b
  smul_right : ∀ (x : M) (c : ℝ) (v a : TangentSpace (modelWithCornersSelf ℝ E) x), g x v (c • a) = c * g x v a

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The local representative of a bilinear family is bilinear in its two slots (`symmL` is linear). -/
theorem localRep_add_left (hg : IsBilinear g) (x₀ : M) (w : E) (a b v : E) :
    localRep g x₀ w (a + b) v = localRep g x₀ w a v + localRep g x₀ w b v := by
  simp only [localRep, map_add]
  exact hg.add_left _ _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem localRep_smul_left (hg : IsBilinear g) (x₀ : M) (w : E) (c : ℝ) (a v : E) :
    localRep g x₀ w (c • a) v = c * localRep g x₀ w a v := by
  simp only [localRep, map_smul]
  exact hg.smul_left _ _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem localRep_add_right (hg : IsBilinear g) (x₀ : M) (w : E) (v a b : E) :
    localRep g x₀ w v (a + b) = localRep g x₀ w v a + localRep g x₀ w v b := by
  simp only [localRep, map_add]
  exact hg.add_right _ _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem localRep_smul_right (hg : IsBilinear g) (x₀ : M) (w : E) (c : ℝ) (v a : E) :
    localRep g x₀ w v (c • a) = c * localRep g x₀ w v a := by
  simp only [localRep, map_smul]
  exact hg.smul_right _ _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The local representative, as a real bilinear form on `E` (for a bilinear family). -/
def localRepBilin (hg : IsBilinear g) (x₀ : M) (w : E) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (localRep g x₀ w) (localRep_add_left g hg x₀ w) (localRep_smul_left g hg x₀ w)
    (localRep_add_right g hg x₀ w) (localRep_smul_right g hg x₀ w)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
@[simp] theorem localRepBilin_apply (hg : IsBilinear g) (x₀ : M) (w : E) (u v : E) :
    localRepBilin g hg x₀ w u v = localRep g x₀ w u v := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem gram_eq_toMatrix (hg : IsBilinear g) (x₀ : M) (w : E) :
    gram e g x₀ w = LinearMap.BilinForm.toMatrix e (localRepBilin g hg x₀ w) := by
  ext i j
  rw [gram, Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply, localRepBilin_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The local representative of a metric family transforms under a chart transition by pulling
back both slots along the transition's derivative: the metric analogue of
`DifferentialForm.localRep_transition`, from `tangent_symmL_eq_fderiv` at both charts and the chain
rule for the transition (`fderiv_chart_transition_comp`). -/
theorem localRep_transition (x₀ y : M) {w : E} (hw : w ∈ (chartAt E x₀).target)
    (hy : (chartAt E x₀).symm w ∈ (chartAt E y).source) (u v : E) :
    localRep g x₀ w u v
      = localRep g y (chartAt E y ((chartAt E x₀).symm w))
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w u)
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w v) := by
  have hz₀ : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have hwz : chartAt E x₀ ((chartAt E x₀).symm w) = w := (chartAt E x₀).right_inv hw
  have hyz : (chartAt E y).symm (chartAt E y ((chartAt E x₀).symm w)) = (chartAt E x₀).symm w :=
    (chartAt E y).left_inv hy
  simp only [localRep]
  rw [hyz]
  have hc := fderiv_chart_transition_comp x₀ y ((chartAt E x₀).symm w) hz₀ hy
  rw [hwz] at hc
  have h0 := tangent_symmL_eq_fderiv x₀ ((chartAt E x₀).symm w) hz₀
  have hy' := tangent_symmL_eq_fderiv y ((chartAt E x₀).symm w) hy
  rw [hwz] at h0
  have e0 : ∀ a : E,
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ ((chartAt E x₀).symm w) a
        = (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) y).symmL ℝ ((chartAt E x₀).symm w)
            (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w a) := fun a =>
    (congrArg (fun L => L a) h0).trans
      ((congrArg (fun L => L a) hc).trans
        (congrArg (fun L => L (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w a)) hy').symm)
  exact congrArg₂ (g _) (e0 u) (e0 v)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- ★ **The Jacobian rule for Gram densities**: under a chart transition `φ` the Gram matrix of a
bilinear family transforms by congruence, `G_{x₀}(w) = Aᵀ G_y(φ w) A` with `A` the matrix of
`Dφ_w`, so `√det G_{x₀}(w) = |det Dφ_w| · √det G_y(φ w)` — the exact analogue of
`compContinuousLinearMap_apply_basis` for top forms. -/
theorem chartDensity_transition (hg : IsBilinear g) (x₀ y : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) (hy : (chartAt E x₀).symm w ∈ (chartAt E y).source) :
    chartDensity e g x₀ w
      = ENNReal.ofReal |(fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w).det|
          * chartDensity e g y (chartAt E y ((chartAt E x₀).symm w)) := by
  set L := fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) w
  have hcomp : localRepBilin g hg x₀ w
      = LinearMap.BilinForm.comp (localRepBilin g hg y (chartAt E y ((chartAt E x₀).symm w)))
          (L : E →ₗ[ℝ] E) (L : E →ₗ[ℝ] E) := by
    apply LinearMap.ext; intro u; apply LinearMap.ext; intro v
    simp only [LinearMap.BilinForm.comp_apply, localRepBilin_apply, ContinuousLinearMap.coe_coe]
    exact localRep_transition g x₀ y hw hy u v
  have hdet : (gram e g x₀ w).det
      = (LinearMap.det (L : E →ₗ[ℝ] E)) ^ 2
          * (gram e g y (chartAt E y ((chartAt E x₀).symm w))).det := by
    rw [gram_eq_toMatrix e g hg, gram_eq_toMatrix e g hg, hcomp,
      LinearMap.BilinForm.toMatrix_comp e e _ (L : E →ₗ[ℝ] E) (L : E →ₗ[ℝ] E),
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
    ring
  rw [chartDensity, chartDensity, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- ★★ **Chart-independence.** On a measurable set inside two chart domains the two Riemannian
chart measures of a bilinear family agree: change of variables along the transition, whose
Jacobian is exactly the factor by which `√det G` transforms (`chartDensity_transition`). The proof
of `DifferentialForm.chartMeasure_congr` with the Gram rule in place of the top-form rule. -/
theorem chartMeasure_congr (hg : IsBilinear g) (x₀ y : M) {A : Set M} (hA : MeasurableSet A)
    (hA₀ : A ⊆ (chartAt E x₀).source) (hAy : A ⊆ (chartAt E y).source) :
    chartMeasure μ e g x₀ A = chartMeasure μ e g y A := by
  rw [chartMeasure_apply μ e g x₀ hA, chartMeasure_apply μ e g y hA]
  have hS₀ := DifferentialForm.measurableSet_target_inter_preimage (E := E) x₀ hA
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
    simp only [Function.comp_apply]
    exact chartDensity_transition e g hg x₀ y hw.1 hy
  · intro w hw
    exact ((contDiffAt_chart_transition x₀ y hw.1 (hAy hw.2)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro w₁ hw₁ w₂ hw₂ h
    have h1 := (chartAt E y).injOn (hAy hw₁.2) (hAy hw₂.2) h
    exact (chartAt E x₀).symm.injOn hw₁.1 hw₂.1 h1

/-- ★★ On a measurable set inside **any** chart domain the glued Riemannian volume is that
chart's measure (for a bilinear family). -/
theorem riemannianVolume_apply_of_subset_source (hg : IsBilinear g) (c : ChartCover E M) (y : M)
    {A : Set M} (hA : MeasurableSet A) (hAy : A ⊆ (chartAt E y).source) :
    riemannianVolume μ e g c A = chartMeasure μ e g y A := by
  rw [riemannianVolume, Measure.sum_apply _ hA]
  simp_rw [Measure.restrict_apply hA]
  have hcongr : ∀ j, chartMeasure μ e g (c.pt j) (A ∩ c.piece j)
      = chartMeasure μ e g y (A ∩ c.piece j) := fun j =>
    chartMeasure_congr μ e g hg (c.pt j) y (hA.inter (c.measurableSet_piece j))
      (fun x hx => c.piece_subset j hx.2) (fun x hx => hAy hx.1)
  simp_rw [hcongr]
  rw [← measure_iUnion (fun j k hjk => (c.pairwise_disjoint_piece hjk).mono
      Set.inter_subset_right Set.inter_subset_right)
    (fun j => hA.inter (c.measurableSet_piece j)), c.iUnion_inter_piece]

/-- ★★ **The Riemannian volume does not depend on the cover** (for a bilinear family):
`RiemannianMetric.riemannianVolume` is canonical. -/
theorem riemannianVolume_congr_cover (hg : IsBilinear g) (c c' : ChartCover E M) :
    riemannianVolume μ e g c = riemannianVolume μ e g c' := by
  ext A hA
  have hdecomp : ∀ ν : Measure M, ν A = ∑' i, ν (A ∩ c'.piece i) := fun ν => by
    conv_lhs => rw [← c'.iUnion_inter_piece A]
    exact measure_iUnion (fun j k hjk => (c'.pairwise_disjoint_piece hjk).mono
      Set.inter_subset_right Set.inter_subset_right)
      (fun j => hA.inter (c'.measurableSet_piece j))
  rw [hdecomp, hdecomp (riemannianVolume μ e g c')]
  congr 1
  ext i
  rw [riemannianVolume_apply_of_subset_source μ e g hg c (c'.pt i)
      (hA.inter (c'.measurableSet_piece i)) (fun x hx => c'.piece_subset i hx.2),
    riemannianVolume_apply_of_subset_source μ e g hg c' (c'.pt i)
      (hA.inter (c'.measurableSet_piece i)) (fun x hx => c'.piece_subset i hx.2)]

end RiemannianMetric

end RiemannianVolume

end
