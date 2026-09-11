/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure

/-!
# The Riemannian volume of a metric on a manifold, from chart Gram densities

**Category:** 1-Mathlib-staging (measure theory on manifolds: the Riemannian volume measure of a
metric family, absent from Mathlib at the pin — `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`
has Riemannian *bundles*, no volume; G17 of `specs/generator-layer-scoping.md` §9).

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
  `ℂℙⁿ` (`Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`).

## Honest scope

⚠️ **No chart-independence theorem here.** `TopFormMeasure.lean` proves its measure is independent of
the cover (`chartMeasure_congr`, by the Jacobian rule for top-form coefficients). The analogous fact
for Gram densities — `√det (DφᵀGDφ) = |det Dφ| √det G` along a transition — is true and is not
proved here: nothing consumes it, because on `ℂℙⁿ` the Riemannian volume is identified with a
top-form measure chart by chart, and independence is inherited from the top-form side. A consumer
needing `riemannianVolume` to be canonical for a metric that is *not* a top-form density must add
it (queued as G17b in the scoping note).

⚠️ **`g` is a family, not a section.** No smoothness or symmetry of `g` is assumed by the
definitions; a non-positive Gram determinant gives density `0` (`Real.sqrt` of a negative is `0`).
The ℂℙⁿ instance supplies a genuine metric.

References: `specs/generator-layer-scoping.md` (G17); `Geometry/Manifold/TopFormMeasure.lean` (the
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

end RiemannianMetric

end RiemannianVolume

end
