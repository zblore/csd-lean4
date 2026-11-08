/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonJacobi
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianFlowVolume
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# The covariant derivative along a curve, and geodesics

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).
BACKLOG #339 (geometric QM, completion item 8b).

Mathlib's covariant derivatives act on vector fields. Here is the derivative of a vector field
*along a curve*, for any covariant derivative on the tangent bundle of a manifold modelled on a
finite-dimensional real normed space.

* `chartCov x₀` — the **flat connection of the chart at `x₀`**: differentiate the chart
  representative of a vector field and read the result back through the tangent trivialisation;
  `chartField_chartAt`, `differentiableAt_chartField`, `chartField_add_eventually`,
  `chartField_smul_eventually`; ★ `isCovariantDerivativeOn_chartCov` — it is a covariant
  derivative on the chart's source;
* `christoffel cov x₀` — **the Christoffel tensor** `cov − chartCov x₀` on the chart's source
  (Mathlib's `IsCovariantDerivativeOn.difference`);
* ★★ `covAlong cov γ V t` — **the covariant derivative along a curve**,
  `D_t V = (d/dt V_loc) + Γ(V, γ')` in the chart at `γ t`;
* ★★★ `covAlong_comp` — **`D_t (X ∘ γ) = ∇_{γ'} X`** for a vector field `X` differentiable along
  a differentiable curve: the definition is the right one;
* `IsGeodesic cov γ` — `D_t γ' = 0` for all `t`; ★★ `isGeodesic_of_isMIntegralCurve` — an integral
  curve of `X` with `∇_X X = 0` along it is a geodesic.

## Honest scope

⚠️ **Defined in the chart at the current point.** `covAlong` uses the chart at `γ t` at time `t`;
`covAlong_comp` identifies it with `∇_{γ'} X` whenever `V = X ∘ γ`, but chart independence for a
general field along `γ` (not a restriction) is not stated, nor are existence/uniqueness of
geodesics, parallel transport, or the exponential map.

## References

Mathlib's `Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean` (`difference`);
J. M. Lee, *Introduction to Riemannian Manifolds* (2nd ed., 2018), Thm. 4.24 (the covariant
derivative along a curve); `specs/BACKLOG.md` #339, #340; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Filter

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The flat connection of the chart at `x₀`**: `∇⁰_v σ = (dσ_loc)(v_loc)` read back through the
tangent trivialisation of the chart, with `σ_loc` the chart field of `σ`. A covariant derivative on
the chart's source (`isCovariantDerivativeOn_chartCov`). -/
def chartCov (x₀ : M) (σ : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (x : M) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x).comp
    ((fderiv ℝ (chartField σ x₀) (chartAt E x₀ x)).comp
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ x))

/-- The chart field at a point of the source reads the field through the trivialisation. -/
theorem chartField_chartAt (σ : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt E x₀).source) :
    chartField σ x₀ (chartAt E x₀ y)
      = (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ y (σ y) := by
  rw [chartField_eq_trivializationAt_snd, (chartAt E x₀).left_inv hy]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀) hy _).symm

/-- A section differentiable at a point of the chart's source has a chart field differentiable at
its chart coordinate. -/
theorem differentiableAt_chartField {σ : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {x₀ x : M}
    (hx : x ∈ (chartAt E x₀).source)
    (hσ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun y => TotalSpace.mk' E y (σ y)) x) :
    DifferentiableAt ℝ (chartField σ x₀) (chartAt E x₀ x) := by
  have hb : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hx
  have h1 := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).mdifferentiableAt_section_iff
    𝓘(ℝ, E) σ hb).1 hσ
  have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀).symm (chartAt E x₀ x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas E x₀) ((chartAt E x₀).map_source hx)
  have h1' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun b => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨b, σ b⟩).2)
      ((chartAt E x₀).symm (chartAt E x₀ x)) := by
    rw [(chartAt E x₀).left_inv hx]
    exact h1
  have h2 := h1'.comp (chartAt E x₀ x) hs
  have h3 : chartField σ x₀ = (fun b => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
      ⟨b, σ b⟩).2) ∘ (chartAt E x₀).symm :=
    funext fun w => chartField_eq_trivializationAt_snd σ x₀ w
  rw [h3]
  exact h2.differentiableAt

/-- The chart field of a sum, near the base point. -/
theorem chartField_add_eventually (σ σ' : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source) :
    chartField (σ + σ') x₀ =ᶠ[𝓝 (chartAt E x₀ x)] chartField σ x₀ + chartField σ' x₀ := by
  filter_upwards [(chartAt E x₀).open_target.mem_nhds ((chartAt E x₀).map_source hx)] with w hw
  have hy := (chartAt E x₀).map_target hw
  have hb : (chartAt E x₀).symm w ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hy
  rw [Pi.add_apply, chartField_eq_trivializationAt_snd, chartField_eq_trivializationAt_snd,
    chartField_eq_trivializationAt_snd,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
  exact map_add _ _ _

/-- The chart field of a scalar multiple, near the base point. -/
theorem chartField_smul_eventually (g : M → ℝ) (σ : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source) :
    chartField (g • σ) x₀ =ᶠ[𝓝 (chartAt E x₀ x)]
      fun w => g ((chartAt E x₀).symm w) • chartField σ x₀ w := by
  filter_upwards [(chartAt E x₀).open_target.mem_nhds ((chartAt E x₀).map_source hx)] with w hw
  have hy := (chartAt E x₀).map_target hw
  have hb : (chartAt E x₀).symm w ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hy
  rw [chartField_eq_trivializationAt_snd, chartField_eq_trivializationAt_snd,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
  exact map_smul _ _ _

/-- ★ **The flat connection of a chart is a covariant derivative on the chart's source.** -/
theorem isCovariantDerivativeOn_chartCov (x₀ : M) :
    IsCovariantDerivativeOn E (chartCov (E := E) x₀) (chartAt E x₀).source where
  add {σ σ' x} hσ hσ' hx := by
    have hd := differentiableAt_chartField hx hσ
    have hd' := differentiableAt_chartField hx hσ'
    ext v
    simp only [chartCov, ContinuousLinearMap.coe_comp, Function.comp_apply,
      (chartField_add_eventually σ σ' x₀ x hx).fderiv_eq, fderiv_add hd hd']
    simp
  leibniz {σ g x} hσ hg hx := by
    have hd := differentiableAt_chartField hx hσ
    have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀).symm (chartAt E x₀ x) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas E x₀) ((chartAt E x₀).map_source hx)
    have hxx : (chartAt E x₀).symm (chartAt E x₀ x) = x := (chartAt E x₀).left_inv hx
    have hg' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g ((chartAt E x₀).symm (chartAt E x₀ x)) := by
      rw [hxx]; exact hg
    have hgd : DifferentiableAt ℝ (g ∘ (chartAt E x₀).symm) (chartAt E x₀ x) :=
      (hg'.comp _ hs).differentiableAt
    have hb : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hx
    have hchain : ∀ v : TangentSpace 𝓘(ℝ, E) x,
        fderiv ℝ (g ∘ (chartAt E x₀).symm) (chartAt E x₀ x)
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ x v)
        = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x v := fun v => by
      rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
      exact DifferentialForm.fderiv_comp_chartAt_symm_trivializationAt_snd (k := g) x₀ hx hg v
    ext v
    simp only [chartCov, ContinuousLinearMap.coe_comp, Function.comp_apply,
      (chartField_smul_eventually g σ x₀ x hx).fderiv_eq]
    erw [fderiv_fun_smul hgd hd]
    simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, Function.comp_apply, hxx]
    rw [hchain v, chartField_chartAt σ x₀ hx,
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb]
    simp
    rfl

variable [FiniteDimensional ℝ E]

/-- **The Christoffel tensor of `cov` in the chart at `x₀`**: the difference `cov − chartCov x₀`
on the chart's source, a tensor (Mathlib's `IsCovariantDerivativeOn.difference`). -/
def christoffel (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  (cov.isCovariantDerivativeOn (s := (chartAt E x₀).source)).difference
    (isCovariantDerivativeOn_chartCov x₀) x

/-- ★★ **The covariant derivative along a curve**: for a vector field `V` along `γ`,
`D_t V = (d/dt V_loc) + Γ(V, γ')`, in the chart at `γ t` (`V_loc` the trivialised field). -/
def covAlong (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) (V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).symmL ℝ (γ t)
      (deriv (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t) ⟨γ s, V s⟩).2) t)
    + christoffel cov (γ t) (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))

/-- ★★★ **The derivative along a curve of a restricted vector field is the covariant derivative
along the velocity**: `D_t (X ∘ γ) = ∇_{γ'} X`. -/
theorem covAlong_comp (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hX : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (fun x => TotalSpace.mk' E x (X x)) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    covAlong cov γ (fun s => X (γ s)) t = cov X (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) := by
  have hx : γ t ∈ (chartAt E (γ t)).source := mem_chart_source E (γ t)
  have hb : γ t ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).baseSet := hx
  set v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) with hv
  -- the chart coordinate of the curve has derivative the trivialised velocity
  have hφ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E (γ t)) (γ t)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt ℝ (γ t)) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
    exact (mdifferentiableAt_atlas (chart_mem_atlas E (γ t)) hx).hasMFDerivAt
  have hφγ : HasDerivAt (fun s => chartAt E (γ t) (γ s))
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt ℝ (γ t) v) t := by
    have h : HasFDerivAt (fun s => chartAt E (γ t) (γ s))
        ((((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt ℝ (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) : ℝ →L[ℝ] E)) t :=
      hasMFDerivAt_iff_hasFDerivAt.1 (hφ.comp t hγ.hasMFDerivAt)
    exact h.hasDerivAt
  have hloc : (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t) ⟨γ s, X (γ s)⟩).2)
      =ᶠ[𝓝 t] (chartField X (γ t) ∘ fun s => chartAt E (γ t) (γ s)) := by
    have hcont : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt E (γ t)).source :=
      hγ.continuousAt.preimage_mem_nhds ((chartAt E (γ t)).open_source.mem_nhds hx)
    filter_upwards [hcont] with s hs
    rw [Function.comp_apply, chartField_chartAt X (γ t) hs]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hs _).symm
  have hd : HasDerivAt (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t) ⟨γ s, X (γ s)⟩).2)
      (fderiv ℝ (chartField X (γ t)) (chartAt E (γ t) (γ t))
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt ℝ (γ t) v)) t :=
    ((differentiableAt_chartField hx hX).hasFDerivAt.comp_hasDerivAt t hφγ).congr_of_eventuallyEq
      hloc
  rw [covAlong, christoffel, IsCovariantDerivativeOn.difference_apply _ _ hx hX, hd.deriv]
  show _ + (cov X (γ t) - chartCov (γ t) X (γ t)) v = _
  rw [FunLike.coe_sub, Pi.sub_apply]
  show chartCov (γ t) X (γ t) v + (cov X (γ t) v - chartCov (γ t) X (γ t) v) = _
  abel

/-- **A geodesic of `cov`**: a curve whose velocity is parallel along it, `D_t γ' = 0`. -/
def IsGeodesic (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) : Prop :=
  ∀ t, covAlong cov γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)) t = 0

/-- ★★ **An integral curve of a vector field `X` with `∇_X X = 0` along it is a geodesic.** -/
theorem isGeodesic_of_isMIntegralCurve
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ X)
    (hX : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (fun x => TotalSpace.mk' E x (X x))
      (γ t))
    (h : ∀ t, cov X (γ t) (X (γ t)) = 0) : IsGeodesic cov γ := by
  have hvel : (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)) = fun s => X (γ s) := by
    funext s
    have h1 := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, E) (γ s) =>
      L (1 : ℝ)) (hγ s).mfderiv
    exact h1.trans (one_smul ℝ (X (γ s)))
  intro t
  rw [hvel, covAlong_comp cov (hX t) (hγ t).mdifferentiableAt]
  have : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) = X (γ t) := congrFun hvel t
  rw [this]
  exact h t

end CovariantDerivative
