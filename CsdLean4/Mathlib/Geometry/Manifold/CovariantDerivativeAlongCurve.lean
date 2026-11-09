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
* `chartConstField x₀ c` — the vector field **constant `c` in the chart at `x₀`**:
  `chartCov_chartConstField` (its flat derivative vanishes), `christoffel_chartConstField`
  (`Γ(σ_c, u) = ∇_u σ_c`), ★ `mlieBracket_chartConstField` — **chart-constant fields commute**
  (by Mathlib's `mpullback_mlieBracket` through the inverse chart);
* `christoffel cov x₀` — **the Christoffel tensor** `cov − chartCov x₀` on the chart's source
  (Mathlib's `IsCovariantDerivativeOn.difference`);
* ★★ `covAlong cov γ V t` — **the covariant derivative along a curve**,
  `D_t V = (d/dt V_loc) + Γ(V, γ')` in the chart at `γ t`; `covAlongAt cov x₀` — the same formula
  in the chart at `x₀`, and `covAlongAt_comp`;
* ★★★ `covAlong_comp` — **`D_t (X ∘ γ) = ∇_{γ'} X`** for a vector field `X` differentiable along
  a differentiable curve: the definition is the right one;
* ★★ `covAlong_eq_covAlongAt` — **chart independence**: for a field along `γ` whose lift to `TM`
  is differentiable at `t`, every chart whose source contains `γ t` gives the same `D_t V`
  (`covAlongAt_eq_chartConst`: both are `∇_{γ'} σ_c + (V_loc)'` with `σ_c` chart-constant);
* `IsGeodesic cov γ` — the velocity `t ↦ (γ t, γ' t)` is differentiable in `TM` and
  `D_t γ' = 0` for all `t`; ★★ `isGeodesic_of_isMIntegralCurve` — an integral curve of a
  differentiable `X` with `∇_X X = 0` along it is a geodesic;
* `chartChristoffel cov x₀ w v u` — the Christoffel tensor in the coordinates of the chart at
  `x₀`; `chartSpray cov x₀ (w, v) = (v, -Γ_w(v, v))`; ★★★ `isGeodesic_iff_chartSpray` — **the
  geodesic equation in a chart**: a curve in the chart's source is a geodesic iff its chart
  coordinate `w` and some `v` solve `(w', v') = chartSpray (w, v)`.

## Honest scope

⚠️ **Chart independence needs a differentiable field.** `covAlong` uses the chart at `γ t`;
`covAlong_eq_covAlongAt` moves it to any chart containing `γ t` when the lift of `V` to `TM` is
differentiable at `t` (otherwise both sides are junk-`0` derivatives and are not compared).
Existence and uniqueness of geodesics, parallel transport and the exponential map are not stated.

⚠️ **One chart for all time.** `isGeodesic_iff_chartSpray` assumes `γ t` lies in the chart's
source for every `t ∈ ℝ`, as `IsGeodesic` quantifies over all of `ℝ`; a curve that leaves the
chart needs a time-restricted geodesic notion, not stated. Smoothness of `chartChristoffel` depends
on `cov` and is not stated here; for Fubini–Study it is in
`Instances/ProjectiveSpaceFubiniStudyGeodesicSpray.lean`.

⚠️ **Differentiability is part of `IsGeodesic`.** Mathlib's `mfderiv` and `deriv` are `0` where no
derivative exists, so `D_t γ' = 0` alone would hold for every nowhere-differentiable curve and at
the corner of a broken geodesic; the velocity lift is therefore required to be differentiable.

## References

Mathlib's `Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean` (`difference`);
J. M. Lee, *Introduction to Riemannian Manifolds* (2nd ed., 2018), Thm. 4.24 (the covariant
derivative along a curve), Ch. 4 (Christoffel symbols, the geodesic equation in coordinates);
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` (`mpullback_mlieBracket`);
`specs/BACKLOG.md` #339, #340, #343; `specs/future-work.md`.
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

/-- The vector field that is constant `c` in the chart at `x₀`. -/
def chartConstField (x₀ : M) (c : E) (y : M) : TangentSpace 𝓘(ℝ, E) y :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symm y c

/-- The chart-constant field reads `c` in the trivialisation of its chart. -/
theorem trivializationAt_chartConstField (x₀ : M) (c : E) {y : M}
    (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨y, chartConstField x₀ c y⟩).2 = c := by
  have hb : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hy
  rw [chartConstField, Trivialization.apply_mk_symm _ hb]

/-- The chart field of the chart-constant field is constant on the chart's target. -/
theorem chartField_chartConstField (x₀ : M) (c : E) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    chartField (chartConstField x₀ c) x₀ w = c := by
  rw [chartField_eq_trivializationAt_snd]
  exact trivializationAt_chartConstField x₀ c ((chartAt E x₀).map_target hw)

/-- The chart-constant field is differentiable on the chart's source. -/
theorem mdifferentiableAt_chartConstField (x₀ : M) (c : E) {y : M}
    (hy : y ∈ (chartAt E x₀).source) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x => TotalSpace.mk' E x (chartConstField x₀ c x)) y := by
  have hb : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := hy
  rw [(trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).mdifferentiableAt_section_iff
    𝓘(ℝ, E) _ hb]
  refine (mdifferentiableAt_const (c := c)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds hy] with z hz
  exact trivializationAt_chartConstField x₀ c hz

/-- The flat connection of the chart kills the chart-constant field. -/
theorem chartCov_chartConstField (x₀ : M) (c : E) {y : M} (hy : y ∈ (chartAt E x₀).source) :
    chartCov x₀ (chartConstField x₀ c) y = 0 := by
  have h : chartField (chartConstField x₀ c) x₀ =ᶠ[𝓝 (chartAt E x₀ y)] fun _ => c := by
    filter_upwards [(chartAt E x₀).open_target.mem_nhds ((chartAt E x₀).map_source hy)] with w hw
    exact chartField_chartConstField x₀ c hw
  ext v
  simp [chartCov, h.fderiv_eq]

/-- A field along a curve with differentiable lift to `TM` has differentiable components in every
chart containing the point. -/
theorem differentiableAt_trivializationAt_comp {γ : ℝ → M}
    {V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)} {t : ℝ} (x₀ : M)
    (hx : γ t ∈ (chartAt E x₀).source)
    (hV : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E).tangent (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    DifferentiableAt ℝ
      (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ s, V s⟩).2) t := by
  have hmem : TotalSpace.mk' E (γ t) (V t)
      ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).source :=
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).mem_source.2 hx
  have h := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).mdifferentiableAt_totalSpace_iff
    (IB := 𝓘(ℝ, E)) (fun s => TotalSpace.mk' E (γ s) (V s)) (x₀ := t) hmem).1 hV
  exact h.2.differentiableAt

/-- The components of a restricted field `X ∘ γ` in the chart at `x₀` differentiate by the chain
rule through the chart field of `X`. -/
theorem hasDerivAt_trivializationAt_comp {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}
    {t : ℝ} (x₀ : M) (hx : γ t ∈ (chartAt E x₀).source)
    (hX : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (fun x => TotalSpace.mk' E x (X x)) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    HasDerivAt (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ s, X (γ s)⟩).2)
      (fderiv ℝ (chartField X x₀) (chartAt E x₀ (γ t))
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)))) t := by
  have hφ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀) (γ t)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
    exact (mdifferentiableAt_atlas (chart_mem_atlas E x₀) hx).hasMFDerivAt
  have hφγ : HasDerivAt (fun s => chartAt E x₀ (γ s))
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))) t := by
    have h : HasFDerivAt (fun s => chartAt E x₀ (γ s))
        ((((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) : ℝ →L[ℝ] E)) t :=
      hasMFDerivAt_iff_hasFDerivAt.1 (hφ.comp t hγ.hasMFDerivAt)
    exact h.hasDerivAt
  have hloc : (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ s, X (γ s)⟩).2)
      =ᶠ[𝓝 t] (chartField X x₀ ∘ fun s => chartAt E x₀ (γ s)) := by
    have hcont : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt E x₀).source :=
      hγ.continuousAt.preimage_mem_nhds ((chartAt E x₀).open_source.mem_nhds hx)
    filter_upwards [hcont] with s hs
    rw [Function.comp_apply, chartField_chartAt X x₀ hs]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hs _).symm
  exact ((differentiableAt_chartField hx hX).hasFDerivAt.comp_hasDerivAt t
    hφγ).congr_of_eventuallyEq hloc

/-- The chart coordinate of a differentiable curve has derivative the trivialised velocity. -/
theorem hasDerivAt_chartAt_comp {γ : ℝ → M} {t : ℝ} (x₀ : M) (hx : γ t ∈ (chartAt E x₀).source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    HasDerivAt (fun s => chartAt E x₀ (γ s))
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
        ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩).2) t := by
  have hφ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀) (γ t)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
    exact (mdifferentiableAt_atlas (chart_mem_atlas E x₀) hx).hasMFDerivAt
  have h : HasFDerivAt (fun s => chartAt E x₀ (γ s))
      ((((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) : ℝ →L[ℝ] E)) t :=
    hasMFDerivAt_iff_hasFDerivAt.1 (hφ.comp t hγ.hasMFDerivAt)
  convert h.hasDerivAt using 1
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hx _).symm

/-- A curve whose chart coordinate is differentiable, inside the chart, is differentiable. -/
theorem mdifferentiableAt_of_chartAt_comp {γ : ℝ → M} {t : ℝ} (x₀ : M)
    (hγ : ∀ s, γ s ∈ (chartAt E x₀).source)
    (hw : DifferentiableAt ℝ (fun s => chartAt E x₀ (γ s)) t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := by
  have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀).symm (chartAt E x₀ (γ t)) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas E x₀) ((chartAt E x₀).map_source (hγ t))
  refine (hs.comp t hw.mdifferentiableAt).congr_of_eventuallyEq
    (Eventually.of_forall fun s => ?_)
  exact ((chartAt E x₀).left_inv (hγ s)).symm

/-- The derivative of the inverse chart is the inverse tangent trivialisation. -/
theorem mfderiv_extChartAt_symm_eq (x₀ : M) {w : E}
    (hw : w ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm w
      = (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ
          ((extChartAt 𝓘(ℝ, E) x₀).symm w) := by
  have hy : (extChartAt 𝓘(ℝ, E) x₀).symm w ∈ (chartAt E x₀).source := by
    have := (extChartAt 𝓘(ℝ, E) x₀).map_target hw
    rwa [extChartAt_source] at this
  rw [TangentBundle.symmL_trivializationAt hy, (extChartAt 𝓘(ℝ, E) x₀).right_inv hw]
  simp [mfderivWithin_univ]
  rfl

/-- Pulled back by the inverse chart, the chart-constant field is the constant field `c`. -/
theorem mpullback_chartConstField (x₀ : M) (c : E) {w : E}
    (hw : w ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
      (chartConstField x₀ c) w = c := by
  have hy : (extChartAt 𝓘(ℝ, E) x₀).symm w ∈ (chartAt E x₀).source := by
    have := (extChartAt 𝓘(ℝ, E) x₀).map_target hw
    rwa [extChartAt_source] at this
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm w).IsInvertible := by
    have := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀) hw
    simpa [mfderivWithin_univ] using this
  rw [VectorField.mpullback_apply]
  refine hinv.inverse_apply_eq.2 ?_
  rw [mfderiv_extChartAt_symm_eq x₀ hw]
  exact (Trivialization.symmL_apply (R := ℝ) _ hy c).symm

variable [FiniteDimensional ℝ E]

/-- **The Christoffel tensor of `cov` in the chart at `x₀`**: the difference `cov − chartCov x₀`
on the chart's source, a tensor (Mathlib's `IsCovariantDerivativeOn.difference`). -/
def christoffel (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  (cov.isCovariantDerivativeOn (s := (chartAt E x₀).source)).difference
    (isCovariantDerivativeOn_chartCov x₀) x

/-- On a chart-constant field the Christoffel tensor is the covariant derivative:
`Γ(σ_c, u) = ∇_u σ_c`. -/
theorem christoffel_chartConstField
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) (c : E) {y : M} (hy : y ∈ (chartAt E x₀).source) (u : TangentSpace 𝓘(ℝ, E) y) :
    christoffel cov x₀ y (chartConstField x₀ c y) u = cov (chartConstField x₀ c) y u := by
  rw [christoffel, IsCovariantDerivativeOn.difference_apply _ _ hy
    (mdifferentiableAt_chartConstField x₀ c hy)]
  show (cov (chartConstField x₀ c) y - chartCov x₀ (chartConstField x₀ c) y) u = _
  rw [chartCov_chartConstField x₀ c hy, sub_zero]

/-- ★ **Chart-constant fields commute**: the Lie bracket of two fields constant in the chart at
`x₀` vanishes on its source. -/
theorem mlieBracket_chartConstField (x₀ : M) (a b : E) {y : M}
    (hy : y ∈ (chartAt E x₀).source) :
    VectorField.mlieBracket 𝓘(ℝ, E) (chartConstField x₀ a) (chartConstField x₀ b) y = 0 := by
  have hy' : y ∈ (extChartAt 𝓘(ℝ, E) x₀).source := by rwa [extChartAt_source]
  set w := extChartAt 𝓘(ℝ, E) x₀ y with hwdef
  have hw : w ∈ (extChartAt 𝓘(ℝ, E) x₀).target := (extChartAt 𝓘(ℝ, E) x₀).map_source hy'
  have hfw : (extChartAt 𝓘(ℝ, E) x₀).symm w = y := (extChartAt 𝓘(ℝ, E) x₀).left_inv hy'
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) x₀).symm w :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀).mem_nhds hw)
  have hev : ∀ c, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
      (chartConstField x₀ c) =ᶠ[𝓝 w] fun _ => c := fun c => by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀).mem_nhds hw] with w' hw'
    exact mpullback_chartConstField x₀ c hw'
  have hfy := fun c => (show _ from by
    have h := mdifferentiableAt_chartConstField x₀ c hy
    rw [← hfw] at h
    exact h)
  have : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have key := VectorField.mpullback_mlieBracket (M := E) (M' := M) (E' := E) (H' := E)
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (f := (extChartAt 𝓘(ℝ, E) x₀).symm) (V := chartConstField x₀ a)
    (W := chartConstField x₀ b) (hfy a) (hfy b) hf (by simp)
  have h2 : VectorField.mlieBracket 𝓘(ℝ, E)
      (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (chartConstField x₀ a))
      (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (chartConstField x₀ b))
      w = 0 := by
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
    have h3 : ∀ P Q : E → E, P =ᶠ[𝓝 w] (fun _ => a) → Q =ᶠ[𝓝 w] (fun _ => b) →
        VectorField.lieBracketWithin ℝ P Q Set.univ w = 0 := by
      intro P Q hP hQ
      rw [VectorField.lieBracketWithin_univ, VectorField.lieBracket_eq]
      simp only
      rw [hP.fderiv_eq, hQ.fderiv_eq]
      simp
    exact h3 _ _ (hev a) (hev b)
  rw [h2, VectorField.mpullback_apply] at key
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm w).IsInvertible := by
    have := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀) hw
    simpa [mfderivWithin_univ] using this
  rw [hinv.inverse_apply_eq, map_zero] at key
  rw [← hfw]
  exact key

/-- ★★ **The covariant derivative along a curve**: for a vector field `V` along `γ`,
`D_t V = (d/dt V_loc) + Γ(V, γ')`, in the chart at `γ t` (`V_loc` the trivialised field). -/
def covAlong (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) (V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).symmL ℝ (γ t)
      (deriv (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t) ⟨γ s, V s⟩).2) t)
    + christoffel cov (γ t) (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))

/-- `covAlong` computed in the chart at `x₀`. -/
def covAlongAt (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) (γ : ℝ → M) (V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) :
    TangentSpace 𝓘(ℝ, E) (γ t) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ (γ t)
      (deriv (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ s, V s⟩).2) t)
    + christoffel cov x₀ (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))

/-- `covAlong` is `covAlongAt` in the chart at the current point (by definition). -/
theorem covAlong_eq_covAlongAt_self
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) (V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) :
    covAlong cov γ V t = covAlongAt cov (γ t) γ V t := rfl

/-- `D_t (X ∘ γ) = ∇_{γ'} X` in any chart whose source contains `γ t`. -/
theorem covAlongAt_comp (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ} (x₀ : M)
    (hx : γ t ∈ (chartAt E x₀).source)
    (hX : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (fun x => TotalSpace.mk' E x (X x)) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    covAlongAt cov x₀ γ (fun s => X (γ s)) t
      = cov X (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) := by
  set v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) with hv
  rw [covAlongAt, christoffel, IsCovariantDerivativeOn.difference_apply _ _ hx hX,
    (hasDerivAt_trivializationAt_comp x₀ hx hX hγ).deriv]
  show _ + (cov X (γ t) - chartCov x₀ X (γ t)) v = _
  rw [FunLike.coe_sub, Pi.sub_apply]
  show chartCov x₀ X (γ t) v + (cov X (γ t) v - chartCov x₀ X (γ t) v) = _
  abel

/-- ★★★ **The derivative along a curve of a restricted vector field is the covariant derivative
along the velocity**: `D_t (X ∘ γ) = ∇_{γ'} X`. -/
theorem covAlong_comp (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hX : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (fun x => TotalSpace.mk' E x (X x)) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    covAlong cov γ (fun s => X (γ s)) t = cov X (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) :=
  covAlongAt_comp cov (γ t) (mem_chart_source E (γ t)) hX hγ

/-- The covariant derivative along a curve in the chart at `x₁`, written through the chart at
`x₀`. -/
theorem covAlongAt_eq_chartConst
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {γ : ℝ → M} {V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)} {t : ℝ} (x₀ x₁ : M)
    (h₀ : γ t ∈ (chartAt E x₀).source) (h₁ : γ t ∈ (chartAt E x₁).source)
    (hV : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E).tangent (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    covAlongAt cov x₁ γ V t
      = cov (chartConstField x₀ ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ t, V t⟩).2))
          (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
        + (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ (γ t)
          (deriv (fun s => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ ⟨γ s, V s⟩).2) t) := by
  set e₀ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ with he₀
  set e₁ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₁ with he₁
  have hb₀ : γ t ∈ e₀.baseSet := h₀
  have hb₁ : γ t ∈ e₁.baseSet := h₁
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := ((mdifferentiableAt_totalSpace _ _).1 hV).1
  set c : E := (e₀ ⟨γ t, V t⟩).2 with hc
  set a : E := deriv (fun s => (e₀ ⟨γ s, V s⟩).2) t with ha
  set W₁ : ℝ → E := fun s => (e₁ ⟨γ s, chartConstField x₀ c (γ s)⟩).2 with hW₁
  set A₁ : ℝ → E := fun s => (e₁ ⟨γ s, chartConstField x₀ a (γ s)⟩).2 with hA₁
  have hdW : DifferentiableAt ℝ W₁ t :=
    differentiableAt_trivializationAt_comp x₁ h₁
      ((mdifferentiableAt_chartConstField x₀ c h₀).comp t hγ)
  have hdA : DifferentiableAt ℝ A₁ t :=
    differentiableAt_trivializationAt_comp x₁ h₁
      ((mdifferentiableAt_chartConstField x₀ a h₀).comp t hγ)
  have hdV₀ : HasDerivAt (fun s => (e₀ ⟨γ s, V s⟩).2) a t :=
    (differentiableAt_trivializationAt_comp x₀ h₀ hV).hasDerivAt
  have hVt : V t = chartConstField x₀ c (γ t) := (e₀.symm_apply_apply_mk hb₀ (V t)).symm
  -- the remainder, in both charts
  set R₀ : ℝ → E := fun s => (e₀ ⟨γ s, V s⟩).2 - c - (s - t) • a with hR₀
  set R₁ : ℝ → E := fun s => (e₁ ⟨γ s, V s⟩).2 - W₁ s - (s - t) • A₁ s with hR₁
  have hR₀d : HasDerivAt R₀ 0 t := by
    have := (hdV₀.sub_const c).sub (((hasDerivAt_id' t).sub_const t).smul_const a)
    convert this using 1
    simp
  have hR₀t : R₀ t = 0 := by simp [hR₀, hc]
  have hR₁t : R₁ t = 0 := by
    show (e₁ ⟨γ t, V t⟩).2 - (e₁ ⟨γ t, chartConstField x₀ c (γ t)⟩).2 - (t - t) • A₁ t = 0
    rw [← hVt]
    simp
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ e₀.baseSet ∩ e₁.baseSet :=
    hγ.continuousAt.preimage_mem_nhds
      ((e₀.open_baseSet.inter e₁.open_baseSet).mem_nhds ⟨hb₀, hb₁⟩)
  have hrel : ∀ᶠ s in 𝓝 t, R₁ s = e₀.coordChangeL ℝ e₁ (γ s) (R₀ s) := by
    filter_upwards [hev] with s hs
    have key : ∀ v : TangentSpace 𝓘(ℝ, E) (γ s),
        (e₁ ⟨γ s, v⟩).2 = e₀.coordChangeL ℝ e₁ (γ s) (e₀ ⟨γ s, v⟩).2 := fun v => by
      rw [e₀.coordChangeL_apply e₁ hs, e₀.symm_apply_apply_mk hs.1]
    have hc' : (e₀ ⟨γ s, chartConstField x₀ c (γ s)⟩).2 = c :=
      trivializationAt_chartConstField x₀ c hs.1
    have ha' : (e₀ ⟨γ s, chartConstField x₀ a (γ s)⟩).2 = a :=
      trivializationAt_chartConstField x₀ a hs.1
    simp only [hR₀, hR₁, hW₁, hA₁]
    rw [key (V s), key (chartConstField x₀ c (γ s)), key (chartConstField x₀ a (γ s)), hc', ha',
      map_sub, map_sub, map_smul]
  have hcont : ContinuousAt (fun s => (e₀.coordChangeL ℝ e₁ (γ s) : E →L[ℝ] E)) t :=
    ((continuousOn_coordChange (R := ℝ) e₀ e₁).continuousAt
      ((e₀.open_baseSet.inter e₁.open_baseSet).mem_nhds ⟨hb₀, hb₁⟩)).comp hγ.continuousAt
  have hbound := hcont.norm.eventually_lt continuousAt_const
    (lt_add_one ‖(e₀.coordChangeL ℝ e₁ (γ t) : E →L[ℝ] E)‖)
  have hO : R₁ =O[𝓝 t] R₀ := by
    refine Asymptotics.IsBigO.of_bound (‖(e₀.coordChangeL ℝ e₁ (γ t) : E →L[ℝ] E)‖ + 1) ?_
    filter_upwards [hrel, hbound] with s hs hb
    rw [hs]
    exact ((e₀.coordChangeL ℝ e₁ (γ s) : E →L[ℝ] E).le_opNorm (R₀ s)).trans
      (mul_le_mul_of_nonneg_right hb.le (norm_nonneg _))
  have hR₀o : R₀ =o[𝓝 t] fun s => s - t :=
    (hasDerivAt_iff_isLittleO.1 hR₀d).congr_left fun s => by simp [hR₀t]
  have hR₁d : HasDerivAt R₁ 0 t :=
    hasDerivAt_iff_isLittleO.2 ((hO.trans_isLittleO hR₀o).congr_left fun s => by simp [hR₁t])
  have hprod := ((hasDerivAt_id' t).sub_const t).smul hdA.hasDerivAt
  have hV₁ : HasDerivAt (fun s => (e₁ ⟨γ s, V s⟩).2)
      (0 + deriv W₁ t + ((t - t) • deriv A₁ t + (1 : ℝ) • A₁ t)) t := by
    have h := (hR₁d.add hdW.hasDerivAt).add hprod
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show (e₁ ⟨γ s, V s⟩).2 = R₁ s + W₁ s + (s - t) • A₁ s
    simp only [hR₁]
    abel
  have hWc := covAlongAt_comp cov (X := chartConstField x₀ c) x₁ h₁
    (mdifferentiableAt_chartConstField x₀ c h₀) hγ
  rw [covAlongAt] at hWc
  rw [covAlongAt, hV₁.deriv, hVt]
  simp only [← he₀, ← he₁] at hWc ⊢
  rw [← hW₁] at hWc
  have hA : e₁.symmL ℝ (γ t) (A₁ t) = e₀.symmL ℝ (γ t) a := by
    rw [Trivialization.symmL_apply _ hb₁, Trivialization.symmL_apply _ hb₀]
    exact e₁.symm_apply_apply_mk hb₁ _
  simp only [sub_self, zero_smul, one_smul, zero_add, map_add, hA]
  rw [← hWc]
  abel

/-- ★★ **Chart independence of the covariant derivative along a curve**: for a field along `γ`
whose lift to `TM` is differentiable at `t`, `covAlong` may be computed in any chart whose source
contains `γ t`. -/
theorem covAlong_eq_covAlongAt
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {γ : ℝ → M} {V : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t)} {t : ℝ} (x₀ : M)
    (h₀ : γ t ∈ (chartAt E x₀).source)
    (hV : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E).tangent (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    covAlong cov γ V t = covAlongAt cov x₀ γ V t := by
  rw [covAlong_eq_covAlongAt_self, covAlongAt_eq_chartConst cov x₀ (γ t) h₀
    (mem_chart_source E (γ t)) hV, covAlongAt_eq_chartConst cov x₀ x₀ h₀ h₀ hV]

/-- **A geodesic of `cov`**: a curve whose velocity is differentiable as a curve in the tangent
bundle (so `γ` and its velocity are genuinely differentiable, not junk-`0` derivatives) and is
parallel along it, `D_t γ' = 0`. -/
def IsGeodesic (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) : Prop :=
  ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E).tangent
      (fun s => TotalSpace.mk' E (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ))) t ∧
    covAlong cov γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)) t = 0

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
  have hlift : (fun s => TotalSpace.mk' E (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)))
      = fun s => TotalSpace.mk' E (γ s) (X (γ s)) := by
    funext s
    rw [congrFun hvel s]
  intro t
  refine ⟨?_, ?_⟩
  · rw [hlift]
    exact (hX t).comp t (hγ t).mdifferentiableAt
  rw [hvel, covAlong_comp cov (hX t) (hγ t).mdifferentiableAt]
  have : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) = X (γ t) := congrFun hvel t
  rw [this]
  exact h t

/-- **The Christoffel tensor in the coordinates of the chart at `x₀`**:
`Γ_w(v, u) = e(Γ(e⁻¹ v, e⁻¹ u))` at the point with coordinate `w`, `e` the tangent trivialisation
of the chart (`v` the field slot, `u` the direction). -/
def chartChristoffel (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) (w v u : E) : E :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ ((chartAt E x₀).symm w)
    (christoffel cov x₀ ((chartAt E x₀).symm w)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ ((chartAt E x₀).symm w) v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ ((chartAt E x₀).symm w) u))

/-- At the chart coordinate of `y`, `chartChristoffel` is the trivialised Christoffel tensor
at `y`. -/
theorem chartChristoffel_chartAt
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) {y : M} (hy : y ∈ (chartAt E x₀).source) (v u : E) :
    chartChristoffel cov x₀ (chartAt E x₀ y) v u
      = (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearMapAt ℝ y
          (christoffel cov x₀ y ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y v)
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y u)) := by
  unfold chartChristoffel
  rw [(chartAt E x₀).left_inv hy]

/-- **The geodesic spray of `cov` in the chart at `x₀`**: `(w, v) ↦ (v, -Γ_w(v, v))`. -/
def chartSpray (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) (p : E × E) : E × E :=
  (p.2, -chartChristoffel cov x₀ p.1 p.2 p.2)

/-- ★★★ **The geodesic equation in a chart**: a curve that stays in the source of the chart at
`x₀` is a geodesic iff its chart coordinate `w` and some `v` solve the first-order system
`(w', v') = (v, -Γ_w(v, v))`. -/
theorem isGeodesic_iff_chartSpray
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (x₀ : M) {γ : ℝ → M} (hγ : ∀ t, γ t ∈ (chartAt E x₀).source) :
    IsGeodesic cov γ ↔ ∃ v : ℝ → E, ∀ t,
      HasDerivAt (fun s => (chartAt E x₀ (γ s), v s))
        (chartSpray cov x₀ (chartAt E x₀ (γ t), v t)) t := by
  set e₀ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀ with he₀
  have hsymm : ∀ t, e₀.symmL ℝ (γ t) ((e₀ ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩).2)
      = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) := fun t => by
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ (hγ t)]
    exact e₀.symmL_continuousLinearMapAt (hγ t) _
  constructor
  · intro h
    have hγd : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := fun t =>
      ((mdifferentiableAt_totalSpace _ _).1 (h t).1).1
    refine ⟨fun s => (e₀ ⟨γ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)⟩).2, fun t => ?_⟩
    have hw := hasDerivAt_chartAt_comp x₀ (hγ t) (hγd t)
    have hv := (differentiableAt_trivializationAt_comp x₀ (hγ t) (h t).1).hasDerivAt
    have hcov := (h t).2
    rw [covAlong_eq_covAlongAt cov x₀ (hγ t) (h t).1, covAlongAt] at hcov
    have key : deriv (fun s => (e₀ ⟨γ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)⟩).2) t
        = -chartChristoffel cov x₀ (chartAt E x₀ (γ t))
            ((e₀ ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩).2)
            ((e₀ ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩).2) := by
      rw [chartChristoffel_chartAt cov x₀ (hγ t), hsymm t]
      have := congrArg (e₀.continuousLinearMapAt ℝ (γ t)) hcov
      rw [map_add, e₀.continuousLinearMapAt_symmL (hγ t), map_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [key] at hv
    exact hw.prodMk hv
  · rintro ⟨v, hv⟩ t
    have hfst : ∀ s, HasDerivAt (fun r => chartAt E x₀ (γ r)) (v s) s := fun s => by
      simpa [chartSpray, Function.comp_def] using
        (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s (hv s)
    have hsnd : ∀ s, HasDerivAt v (-chartChristoffel cov x₀ (chartAt E x₀ (γ s)) (v s) (v s)) s :=
      fun s => by
        simpa [chartSpray, Function.comp_def] using
          (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt s (hv s)
    have hγd : ∀ s, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s := fun s =>
      mdifferentiableAt_of_chartAt_comp x₀ hγ (hfst s).differentiableAt
    have hvel : (fun s => (e₀ ⟨γ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)⟩).2) = v := funext fun s =>
      (hasDerivAt_chartAt_comp x₀ (hγ s) (hγd s)).unique (hfst s)
    have hmem : TotalSpace.mk' E (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) ∈ e₀.source :=
      e₀.mem_source.2 (hγ t)
    have hlift : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E).tangent
        (fun s => TotalSpace.mk' E (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ))) t := by
      refine (e₀.mdifferentiableAt_totalSpace_iff (IB := 𝓘(ℝ, E))
        (fun s => TotalSpace.mk' E (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)))
        (x₀ := t) hmem).2 ⟨hγd t, ?_⟩
      show MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun s => (e₀ ⟨γ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s (1 : ℝ)⟩).2) t
      rw [hvel]
      exact (hsnd t).differentiableAt.mdifferentiableAt
    refine ⟨hlift, ?_⟩
    rw [covAlong_eq_covAlongAt cov x₀ (hγ t) hlift, covAlongAt, hvel, (hsnd t).deriv,
      chartChristoffel_chartAt cov x₀ (hγ t), ← congrFun hvel t, hsymm t, map_neg,
      e₀.symmL_continuousLinearMapAt (hγ t)]
    exact neg_add_cancel _

end CovariantDerivative
