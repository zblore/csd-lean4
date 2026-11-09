/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceGeometricTensor
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannian
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The Fubini–Study metric as a Mathlib Riemannian metric

**TERM-SCOPE(Kahler)** — this module uses the restricted sense of "Kähler"; `specs/TERMS.md`
records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #338 (geometric QM, completion item 8a of 2026-11-08).

The corpus's Fubini–Study metric `fsMetric` (G17) is registered as a Mathlib
`ContMDiffRiemannianMetric` on the tangent bundle of `ℂℙⁿ`, so that Mathlib's Riemannian API —
the inner product on each tangent space, and the Levi-Civita connection of
`Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` — applies to `ℂℙⁿ`.

* `fsModelMetricCLM w` — the model metric as a continuous bilinear map;
  ★ `contDiff_fsModelMetricCLM`
  — smooth in the base point (from `contDiff_omega_fsModelForm`);
* ★ `fsModelMetric_self_ge` — **coercivity**: `g_w(u, u) ≥ 4 ‖u‖² / (1 + ‖w‖²)²` (Euclidean norms),
  from the Provost–Vallée form (`fsModelForm_qgt`) and Cauchy–Schwarz;
* `fsRiemannianMetric` — ★★ **the Fubini–Study metric as a `ContMDiffRiemannianMetric`** of class
  `C^∞`, with smoothness read through the tangent trivialisation of each chart
  (`fsForm_symmL_symmL`, `fsJ_symmL`);
* `fsMetric_eq_fsModelMetricCLM`, `fsMetric_symmL_symmL`, `isVonNBounded_fsModelMetric`,
  `norm_le_norm_toLpCLM`, `fsModelMetric_self`;
* `FubiniStudy.instRiemannianBundle`, `FubiniStudy.instIsContMDiffRiemannianBundle` (both
  scoped): the `RiemannianBundle` instance and its `IsContMDiffRiemannianBundle … ∞` instance;
  `inner_eq_fsMetric` — the inner product it puts on `T_xℂℙⁿ` is `fsMetric x` (by `rfl`);
* ★ `isLeviCivitaConnection_fs` — **Mathlib's Levi-Civita connection of `ℂℙⁿ` with the
  Fubini–Study metric is compatible with the metric and torsion-free.**

## Honest scope

⚠️ **The instances are scoped.** The `RiemannianBundle` instance and its smoothness instance live
in the scope `Projectivization.FubiniStudy` (open it to use Mathlib's Riemannian API on `ℂℙⁿ`), like
`fsENorm` of #330, because the tangent spaces of `ℂℙⁿ` carry no other norm and a global instance
would be a choice made for every user of `ℂℙⁿ`.

⚠️ **The Levi-Civita statement is Mathlib's.** `isLeviCivitaConnection_fs` is Mathlib's existence
theorem at this instance: its content is that the instances resolve on `ℂℙⁿ`. Christoffel symbols,
an explicit formula for `∇`, and the agreement of the instance's norm with #330's `fsENorm` (so
that Mathlib's `riemannianEDist` is `fsEDist`) are not stated.

⚠️ **Geodesics are elsewhere.** Mathlib has no covariant derivative along a curve; it is built in
`CovariantDerivativeAlongCurve.lean` (#339), and great circles are geodesics in
`ProjectiveSpaceGreatCircleGeodesic.lean` (#340).

## References

`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`,
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`;
`Instances/ProjectiveSpaceFubiniStudyRiemannian.lean` (G17, `fsMetric`, `fsModelMetric`),
`Instances/ProjectiveSpaceGeometricTensor.lean` (#327); `specs/BACKLOG.md` #338, #339, #340;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Bundle Kahler DifferentialForm

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- The model metric `g_w` as a continuous bilinear map. -/
def fsModelMetricCLM (w : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin n → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((Fin n → ℂ) →L[ℝ] ℝ)).toLinearMap ∘ₗ fsModelMetric w)

theorem fsModelMetricCLM_apply (w u v : Fin n → ℂ) :
    fsModelMetricCLM w u v = fsModelMetric w u v := rfl

/-- ★ The model metric is smooth in the base point. -/
theorem contDiff_fsModelMetricCLM : ContDiff ℝ ∞ (fsModelMetricCLM (n := n)) := by
  rw [contDiff_clm_apply_iff]
  intro u
  rw [contDiff_clm_apply_iff]
  intro v
  show ContDiff ℝ ∞ (fun w => fsModelForm w ![Complex.I • u, v])
  exact (ContinuousAlternatingMap.apply ℝ (Fin n → ℂ) ℝ ![Complex.I • u, v]).contDiff.comp
    (contDiff_omega_fsModelForm.of_le le_top)

/-- The model metric on the diagonal, written out: `g_w(u, u) = 4 (‖u‖² / N − |⟪u, w⟫|² / N²)`
with `N = 1 + ‖w‖²`. -/
theorem fsModelMetric_self (w u : Fin n → ℂ) :
    fsModelMetric w u u
      = 4 * (‖toLpCLM u‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2)
          - ‖inner ℂ (toLpCLM u) (toLpCLM w)‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2) ^ 2) := by
  have h := fsModelForm_qgt (0 : Fin (n + 1)) w u u
  have h0 : (fsModelForm w ![u, u] : ℝ) = 0 :=
    (fsModelForm w).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  rw [h0, inner_insertZeroCLM_insertZeroCLM, inner_insertZeroCLM_insertOne,
    inner_insertOne_insertZeroCLM, norm_sq_insertOne_toLpCLM] at h
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at h
  rw [← inner_conj_symm (toLpCLM w) (toLpCLM u), Complex.mul_conj', inner_self_eq_norm_sq_to_K]
    at h
  rw [fsModelMetric_apply]
  apply Complex.ofReal_injective
  rw [h]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one]
  rfl

/-- ★ **Coercivity of the model metric**: `g_w(u, u) ≥ 4 ‖u‖² / (1 + ‖w‖²)²`. -/
theorem fsModelMetric_self_ge (w u : Fin n → ℂ) :
    4 * ‖toLpCLM u‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2) ^ 2 ≤ fsModelMetric w u u := by
  rw [fsModelMetric_self]
  have hcs : ‖inner ℂ (toLpCLM u) (toLpCLM w)‖ ≤ ‖toLpCLM u‖ * ‖toLpCLM w‖ :=
    norm_inner_le_norm _ _
  have hN : (0 : ℝ) < 1 + ‖toLpCLM w‖ ^ 2 := by positivity
  have hsq : ‖inner ℂ (toLpCLM u) (toLpCLM w)‖ ^ 2 ≤ ‖toLpCLM u‖ ^ 2 * ‖toLpCLM w‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hcs 2
  rw [div_le_iff₀ (by positivity)]
  have e : 4 * (‖toLpCLM u‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2)
      - ‖inner ℂ (toLpCLM u) (toLpCLM w)‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2) ^ 2)
      * (1 + ‖toLpCLM w‖ ^ 2) ^ 2
      = 4 * (‖toLpCLM u‖ ^ 2 * (1 + ‖toLpCLM w‖ ^ 2) - ‖inner ℂ (toLpCLM u) (toLpCLM w)‖ ^ 2) := by
    field_simp
  rw [e]
  nlinarith [hsq]

/-- The sup norm of the model is at most the Euclidean norm. -/
theorem norm_le_norm_toLpCLM (u : Fin n → ℂ) : ‖u‖ ≤ ‖toLpCLM u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => by
    have h := PiLp.norm_apply_le (toLpCLM u) k
    exact h

/-- The Fubini–Study metric at `x` is the model metric at the chart coordinate of `x`. -/
theorem fsMetric_eq_fsModelMetricCLM (x : ℙ ℂ (Ambient n))
    (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    fsMetric x u v = fsModelMetricCLM (chartFun (idx x) x) u v := rfl

/-- The sublevel set `{g_w(v, v) < 1}` is bounded. -/
theorem isVonNBounded_fsModelMetric (w : Fin n → ℂ) :
    Bornology.IsVonNBounded ℝ {v : Fin n → ℂ | fsModelMetricCLM w v v < 1} := by
  refine (NormedSpace.isVonNBounded_ball ℝ (Fin n → ℂ) ((1 + ‖toLpCLM w‖ ^ 2) / 2 + 1)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, fsModelMetricCLM_apply] at hv
  have hge := fsModelMetric_self_ge w v
  have hN : (0 : ℝ) < 1 + ‖toLpCLM w‖ ^ 2 := by positivity
  have h2 : ‖toLpCLM v‖ ^ 2 < ((1 + ‖toLpCLM w‖ ^ 2) / 2) ^ 2 := by
    have : 4 * ‖toLpCLM v‖ ^ 2 / (1 + ‖toLpCLM w‖ ^ 2) ^ 2 < 1 := lt_of_le_of_lt hge hv
    rw [div_lt_one (by positivity)] at this
    nlinarith
  have h3 : ‖toLpCLM v‖ < (1 + ‖toLpCLM w‖ ^ 2) / 2 :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  rw [Metric.mem_ball, dist_zero_right]
  linarith [norm_le_norm_toLpCLM v]

/-- In the tangent trivialisation of the chart at `x₀`, the metric at `y` is the model metric at the
chart coordinate of `y`. -/
theorem fsMetric_symmL_symmL (x₀ y : ℙ ℂ (Ambient n)) (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source)
    (u v : Fin n → ℂ) :
    fsMetric y ((trivializationAt (Fin n → ℂ) (TangentSpace (𝓘(ℝ, Fin n → ℂ))) x₀).symmL ℝ y u)
        ((trivializationAt (Fin n → ℂ) (TangentSpace (𝓘(ℝ, Fin n → ℂ))) x₀).symmL ℝ y v)
      = fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y) u v := by
  have hw : chartAt (Fin n → ℂ) x₀ y ∈ (chartAt (Fin n → ℂ) x₀).target :=
    (chartAt (Fin n → ℂ) x₀).map_source hy
  have h := localRep_fsMetric x₀ hw u v
  rw [MetricFamily.localRep, (chartAt (Fin n → ℂ) x₀).left_inv hy] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- ★★ **The Fubini–Study metric as a smooth Mathlib Riemannian metric** on the tangent bundle of
`ℂℙⁿ`. -/
def fsRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : ℙ ℂ (Ambient n) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) where
  inner x := fsModelMetricCLM (chartFun (idx x) x)
  symm x v w := (fsForm_isAlmostKahler n).metric_comm x v w
  pos x v hv := (fsForm_isAlmostKahler n).metric_self_pos x hv
  isVonNBounded x := isVonNBounded_fsModelMetric _
  contMDiff := by
    intro x₀
    rw [contMDiffAt_section]
    refine ((contDiff_fsModelMetricCLM.contMDiff.contMDiffAt).comp x₀
      ((contMDiffOn_chart (n := ∞) (x := x₀)).contMDiffAt
        ((chartAt (Fin n → ℂ) x₀).open_source.mem_nhds
          (mem_chart_source _ x₀)))).congr_of_eventuallyEq ?_
    filter_upwards [(chartAt (Fin n → ℂ) x₀).open_source.mem_nhds (mem_chart_source _ x₀)]
      with y hy
    have hb : y ∈ (trivializationAt ((Fin n → ℂ) →L[ℝ] ℝ)
        (fun x : ℙ ℂ (Ambient n) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x →L[ℝ] ℝ) x₀).baseSet := by
      simpa using hy
    ext u v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
    rw [Trivialization.linearMapAt_def_of_mem _ hb]
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
    exact fsMetric_symmL_symmL x₀ y hy u v

namespace FubiniStudy

/-- **The Fubini–Study metric as a `RiemannianBundle` instance** on the tangent bundle of `ℂℙⁿ`
(scoped: open `Projectivization.FubiniStudy`). -/
scoped instance instRiemannianBundle :
    RiemannianBundle (fun x : ℙ ℂ (Ambient n) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :=
  ⟨fsRiemannianMetric.toRiemannianMetric⟩

/-- The instance is a `C^∞` Riemannian bundle (scoped with it). -/
scoped instance instIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : ℙ ℂ (Ambient n) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :=
  ⟨fsRiemannianMetric.inner, fsRiemannianMetric.contMDiff, fun _ _ _ => rfl⟩

end FubiniStudy

open FubiniStudy

open scoped RealInnerProductSpace in
/-- The inner product the instance puts on `T_xℂℙⁿ` is the Fubini–Study metric. -/
theorem inner_eq_fsMetric (x : ℙ ℂ (Ambient n)) (u v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) :
    ⟪u, v⟫ = fsMetric x u v := rfl

/-- ★ **Mathlib's Levi-Civita connection of `ℂℙⁿ` with the Fubini–Study metric is compatible
with the metric and torsion-free.** -/
theorem isLeviCivitaConnection_fs :
    (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ)
      (ℙ ℂ (Ambient n))).IsLeviCivitaConnection :=
  CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection _

end Projectivization
