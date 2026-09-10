/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.DifferentialForm
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudy
public import CsdLean4.Mathlib.Geometry.Manifold.ExteriorDerivative
public import CsdLean4.Mathlib.Geometry.Manifold.WedgeForm

/-!
# The Fubini–Study form as a global smooth 2-form on `ℂℙⁿ`

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

`DifferentialForm.lean` made "a smooth 2-form on `ℂℙⁿ`" a type and exhibited the zero form.
This module exhibits the one that matters: the Fubini–Study form, assembled from the chart
forms `fsChartForm = dd^c log(1 + ‖z‖²)` of `KahlerPotential.lean` using the chart invariance
`fsModelForm_transP` of `ProjectiveSpaceFubiniStudy.lean`.

* `fsSection` — the family: at `x`, the model form read in the chart the atlas chose at `x`
  (`TangentSpace 𝓘(ℝ, Fin n → ℂ) x` is `Fin n → ℂ` definitionally, so no transport is needed);
* ★ `localRep_fsSection` — the **local-representative identity**: in the trivialisation of the
  alternating bundle over the chart at `x₀`, the section reads as the model form in that chart
  at every `y` of the chart domain. This is where chart invariance is spent: the tangent
  coordinate change is the derivative of the chart transition (`extChartAt_trans_eq`,
  `VectorBundleCore.trivializationAt_symmL`), and the pullback of the form along it is the
  form (`fsModelForm_transP`);
* ★ `contMDiffAt_fsSection` / `contMDiff_fsSection` — smoothness, from the local
  representative and `contDiff_fsModelForm` (the model form is `C^∞`: `dd^c` of a `C^∞`
  potential, pulled back along a linear map);
* ★★ `fsForm` — **the Fubini–Study form as a `C^∞` global 2-form on `ℂℙⁿ`**, a term of
  `DifferentialForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)) ∞ (Fin 2) ℝ`;
* ★★ `contMDiff_omega_fsForm` / `fsFormAnalytic` — **the Fubini–Study form is analytic** (G12,
  2026-09-10): the same chain at `ω` — the potential is analytic (`contDiff_omega_fsPotential`),
  `dd^c` and the pullback are generic in the order (`contDiff_omega_fsChartForm`,
  `contDiff_omega_fsModelForm`), and the chart is analytic because the manifold is
  (`contMDiffAt_omega_fsSection`); `fsFormAnalytic` is the section as a term of the `ω` type;
* ★★ `fsForm_ne_zero` — it is **not the zero form** (`n ≥ 1`): at a chart origin it is `-4`
  times the flat fundamental form (`fsChartForm_zero`), which pairs `e` with `i • e` to `‖e‖²`;
* ★★★ `fsForm_mextDeriv` — **`d ω_FS = 0` on `ℂℙⁿ`**: the Fubini–Study form is closed at
  manifold level, for the exterior derivative `mextDeriv` of `ExteriorDerivative.lean` (step
  (2b)). Its local representative in every chart is the flat chart form `fsModelForm`
  (`localRep_fsSection`), whose flat `d` vanishes (`extDeriv_fsChartForm`, MG-4) — so the
  manifold statement is the flat one read through the chart, which is what `mextDeriv` is.

## Honest scope

⚠️ **Two orders, one section.** `fsForm` is the `C^∞` form the downstream predicates
(`IsSymplectic`, `IsAlmostKahler`, the Hamiltonian layer) are stated on, and `fsFormAnalytic` is the
same section as a term of the `ω` type (`fsFormAnalytic_apply`); nothing downstream is restated at
`ω`. Analyticity of the chart *transitions* is `instIsManifoldReal`; analyticity of the *section* is
`contMDiff_omega_fsForm`.

⚠️ **Real smooth, not holomorphic.** The section is over the real model `𝓘(ℝ, Fin n → ℂ)`; the
form is real-valued and `ℝ`-alternating, as a Kähler form is. No `(1,1)`-type statement is made
on the manifold.

⚠️ **Closed, but not non-degenerate and not a volume.** `d fsForm = 0` is `fsForm_mextDeriv`;
non-degeneracy at every point and the top-power identity `ωⁿ/n! = μ_FS` are not attempted.
`fsForm_ne_zero` is a non-vacuity certificate at one point, nothing more.

⚠️ **The chart chosen at `x` is `idx x`, a choice function.** `fsSection` is defined through
it; `localRep_fsSection` is what shows the value does not depend on the choice.

References: `Geometry/Manifold/DifferentialForm.lean` (the type; step (2a));
`specs/generator-layer-scoping.md` (G12, the analytic upgrade);
`Geometry/Manifold/ExteriorDerivative.lean` (`mextDeriv`, `d ∘ d = 0`; step (2b));
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudy.lean` (chart invariance);
`Geometry/Manifold/Instances/ProjectiveSpace.lean` (the atlas);
`Analysis/InnerProductSpace/KahlerPotential.lean` (`fsChartForm`, `fsChartForm_zero`);
`MATHLIB-GAPS.md` (Kahler / symplectic manifold API); `specs/BACKLOG.md` (XL, "Manifold
exterior calculus"); `specs/future-work.md`.
-/

@[expose] public section

open Bundle Projectivization Kahler Filter Topology
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ}

/-! ### The family -/

/-- The Fubini–Study form as a family over `ℂℙⁿ`: at `x`, the model form at `x`'s own chart
coordinate (`TangentSpace 𝓘(ℝ, Fin n → ℂ) x` is definitionally `Fin n → ℂ`). -/
noncomputable def fsSection (x : ℙ ℂ (Ambient n)) :
    TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x [⋀^Fin 2]→L[ℝ]
      Bundle.Trivial (ℙ ℂ (Ambient n)) ℝ x :=
  fsModelForm (chartFun (idx x) x)

/-- The chart transition between the charts at `x₀` and `y`, as `extChartAt` sees it, IS the
model transition `transP`. -/
lemma extChartAt_trans_eq (x₀ y : ℙ ℂ (Ambient n)) :
    (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) y ∘
        (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) x₀).symm)
      = transP (idx x₀) (idx y) := by
  funext w
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq]
  show chartFun (idx y) (chartInv (idx x₀) w) = coordRatio (idx y) (insertOne (idx x₀) w)
  rw [chartInv, chartFun_mk]

/-! ### The local representative -/

/-- ★ **The local-representative identity.** In the trivialisation of the alternating bundle
over the chart at `x₀`, the section reads as the model form in that chart, at every point of
the chart domain. Chart invariance (`fsModelForm_transP`) is spent exactly here. -/
theorem localRep_fsSection (x₀ y : ℙ ℂ (Ambient n))
    (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source) :
    (trivializationAt ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
        (fun p : ℙ ℂ (Ambient n) =>
          TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) p [⋀^Fin 2]→L[ℝ]
            Bundle.Trivial (ℙ ℂ (Ambient n)) ℝ p) x₀
      ⟨y, fsSection y⟩).2
      = fsModelForm (chartFun (idx x₀) y) := by
  have hy₀ : y.rep (idx x₀) ≠ 0 := hy
  have hinv : chartInv (idx x₀) (chartFun (idx x₀) y) = y := chartInv_chartFun (idx x₀) y hy₀
  -- the side condition of the invariance theorem: y lies in its own chart
  have hw : insertOne (idx x₀) (chartFun (idx x₀) y) (idx y) ≠ 0 := by
    rw [← mem_chartSource_mk (idx y) _ (insertOne_ne_zero _ _)]
    show chartInv (idx x₀) (chartFun (idx x₀) y) ∈ chartSource (idx y)
    rw [hinv]; exact idx_spec y
  -- y's own chart coordinate is the transition applied to its x₀-chart coordinate
  have hyw : chartFun (idx y) y = transP (idx x₀) (idx y) (chartFun (idx x₀) y) := by
    show chartFun (idx y) y = coordRatio (idx y) (insertOne (idx x₀) (chartFun (idx x₀) y))
    rw [← chartFun_mk (idx y) _ (insertOne_ne_zero _ _)]
    exact congrArg (chartFun (idx y)) hinv.symm
  -- the tangent coordinate change is the derivative of that transition
  have hsym : (trivializationAt (Fin n → ℂ)
        (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL ℝ y
      = fderiv ℝ (transP (idx x₀) (idx y)) (chartFun (idx x₀) y) := by
    have hy' : y ∈ (trivializationAt (Fin n → ℂ)
        (tangentBundleCore (modelWithCornersSelf ℝ (Fin n → ℂ)) (ℙ ℂ (Ambient n))).Fiber x₀).baseSet :=
      hy
    show (trivializationAt (Fin n → ℂ)
        (tangentBundleCore (modelWithCornersSelf ℝ (Fin n → ℂ)) (ℙ ℂ (Ambient n))).Fiber x₀).symmL ℝ y
      = _
    rw [VectorBundleCore.trivializationAt_symmL _ hy']
    show fderivWithin ℝ (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) y ∘
        (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) x₀).symm)
        (Set.range (modelWithCornersSelf ℝ (Fin n → ℂ)))
        (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) x₀ y) = _
    rw [extChartAt_trans_eq, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
    rfl
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp only [ContinuousAlternatingMap.inCoordinates]
  have hclm : (trivializationAt ℝ (Bundle.Trivial (ℙ ℂ (Ambient n)) ℝ) x₀).continuousLinearMapAt ℝ y
      = ContinuousLinearMap.id ℝ ℝ := by
    show (Bundle.Trivial.trivialization (ℙ ℂ (Ambient n)) ℝ).continuousLinearMapAt ℝ y = _
    simp
  rw [hclm]
  -- finish pointwise: the id-postcomposition is definitional, and the tangent coordinate change
  -- is applied to vectors, so the instance paths never need to be reconciled at the CLM level
  ext v
  have hS : ∀ u : Fin n → ℂ,
      (trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL ℝ y u
        = fderiv ℝ (transP (idx x₀) (idx y)) (chartFun (idx x₀) y) u :=
    fun u => congrArg (fun L => L u) hsym
  have hpt := congrArg (fun α : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ => α v)
    (fsModelForm_transP (idx x₀) (idx y) hw)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at hpt ⊢
  simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [fsSection, hyw]
  have hfun : (⇑((trivializationAt (Fin n → ℂ)
        (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL ℝ y) ∘ v)
      = (⇑(fderiv ℝ (transP (idx x₀) (idx y)) (chartFun (idx x₀) y)) ∘ v) :=
    funext fun k => hS (v k)
  exact (congrArg (fun g => (fsModelForm (transP (idx x₀) (idx y) (chartFun (idx x₀) y))) g)
    hfun).trans hpt

/-! ### Smoothness of the model form -/

/-- The chart form is the alternatization of the derivative of `d^c fsPotential` — `dd^c` of the
potential, in the shape the smoothness lemmas need. -/
theorem fsChartForm_eq_alternatizeUncurryFinCLM_fderiv :
    fsChartForm (E := EuclideanSpace ℂ (Fin n))
      = fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (fderiv ℝ (dcForm (fsPotential (E := EuclideanSpace ℂ (Fin n)))) x) := by
  funext x
  rw [fsChartForm, ddcForm, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

/-- The chart form is `C^∞`: `dd^c` of the `C^∞` potential, i.e. the alternatization of the
derivative of `d^c fsPotential`. -/
theorem contDiff_fsChartForm :
    ContDiff ℝ (⊤ : ℕ∞) (fsChartForm (E := EuclideanSpace ℂ (Fin n))) := by
  rw [fsChartForm_eq_alternatizeUncurryFinCLM_fderiv]
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (dcForm (fsPotential (E := EuclideanSpace ℂ (Fin n))))) :=
    (contDiff_dcForm contDiff_fsPotential).fderiv_right (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (EuclideanSpace ℂ (Fin n)) ℝ).contDiff.comp
    hfd

/-- The model form is `C^∞`: the chart form pulled back along the linear identification
`toLpCLM`. -/
theorem contDiff_fsModelForm : ContDiff ℝ (⊤ : ℕ∞) (fsModelForm (n := n)) := by
  have h : fsModelForm (n := n)
      = fun w => ContinuousAlternatingMap.compContinuousLinearMapCLM
          (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n)) (fsChartForm (toLpCLM w)) := by
    funext w; rfl
  rw [h]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n))).contDiff.comp
    (contDiff_fsChartForm.comp (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n)).contDiff)

/-! ### The global section -/

/-- ★ `fsSection` is a `C^∞` section at every point: in the chart at `x₀` it is the model form
composed with the chart (`localRep_fsSection`), and both are smooth. -/
theorem contMDiffAt_fsSection (x₀ : ℙ ℂ (Ambient n)) :
    ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ))) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) x (fsSection x)) x₀ := by
  rw [contMDiffAt_section]
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ)) ∞
      (chartFun (idx x₀)) x₀ :=
    contMDiffAt_extChartAt (n := ∞) (I := modelWithCornersSelf ℝ (Fin n → ℂ)) (x := x₀)
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun y => fsModelForm (chartFun (idx x₀) y)) x₀ :=
    (contDiff_fsModelForm.contMDiff.contMDiffAt (x := chartFun (idx x₀) x₀)).comp x₀ hchart
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (Fin n → ℂ) x₀).open_source.mem_nhds (mem_chart_source _ x₀)] with y hy
  exact localRep_fsSection x₀ y hy

/-- ★ `fsSection` is a `C^∞` section. -/
theorem contMDiff_fsSection :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ))) ∞
      (fun x : ℙ ℂ (Ambient n) =>
        TotalSpace.mk' ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) x (fsSection x)) :=
  fun x₀ => contMDiffAt_fsSection x₀

/-- ★★ **The Fubini–Study form as a `C^∞` global 2-form on `ℂℙⁿ`.** -/
noncomputable def fsForm :
    DifferentialForm (modelWithCornersSelf ℝ (Fin n → ℂ)) (ℙ ℂ (Ambient n)) ∞ (Fin 2) ℝ :=
  ⟨fsSection, contMDiff_fsSection⟩

@[simp] theorem fsForm_apply (x : ℙ ℂ (Ambient n)) : fsForm x = fsSection x := rfl

/-! ### ★ Analyticity: the section is `ω`, not merely `C^∞` (G12)

The manifold is analytic (`instIsManifoldReal`) and so is the potential
(`contDiff_omega_fsPotential`); every step of the `C^∞` chain above is generic in the order, so the
same chain at `ω` makes `fsForm` an analytic form. -/

/-- ★ The chart form is analytic: `dd^c` of the analytic potential. -/
theorem contDiff_omega_fsChartForm : ContDiff ℝ ω (fsChartForm (E := EuclideanSpace ℂ (Fin n))) := by
  rw [fsChartForm_eq_alternatizeUncurryFinCLM_fderiv]
  have hfd : ContDiff ℝ ω (fderiv ℝ (dcForm (fsPotential (E := EuclideanSpace ℂ (Fin n))))) :=
    (contDiff_omega_dcForm contDiff_omega_fsPotential).fderiv_right le_top
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (EuclideanSpace ℂ (Fin n)) ℝ).contDiff.comp
    hfd

/-- ★ The model form is analytic: the chart form pulled back along the linear identification. -/
theorem contDiff_omega_fsModelForm : ContDiff ℝ ω (fsModelForm (n := n)) := by
  have h : fsModelForm (n := n)
      = fun w => ContinuousAlternatingMap.compContinuousLinearMapCLM
          (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n)) (fsChartForm (toLpCLM w)) := by
    funext w; rfl
  rw [h]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n))).contDiff.comp
    (contDiff_omega_fsChartForm.comp
      (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n)).contDiff)

/-- ★ `fsSection` is an analytic section at every point: the proof of `contMDiffAt_fsSection`,
at `ω` (the chart is analytic because the manifold is). -/
theorem contMDiffAt_omega_fsSection (x₀ : ℙ ℂ (Ambient n)) :
    ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ))) ω
      (fun x => TotalSpace.mk' ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) x (fsSection x)) x₀ := by
  rw [contMDiffAt_section]
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ)) ω
      (chartFun (idx x₀)) x₀ :=
    contMDiffAt_extChartAt (n := ω) (I := modelWithCornersSelf ℝ (Fin n → ℂ)) (x := x₀)
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)) ω
      (fun y => fsModelForm (chartFun (idx x₀) y)) x₀ :=
    (contDiff_omega_fsModelForm.contMDiff.contMDiffAt (x := chartFun (idx x₀) x₀)).comp x₀ hchart
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (Fin n → ℂ) x₀).open_source.mem_nhds (mem_chart_source _ x₀)] with y hy
  exact localRep_fsSection x₀ y hy

/-- ★ `fsSection` is an analytic section. -/
theorem contMDiff_omega_fsSection :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ))) ω
      (fun x : ℙ ℂ (Ambient n) =>
        TotalSpace.mk' ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) x (fsSection x)) :=
  fun x₀ => contMDiffAt_omega_fsSection x₀

/-- ★★ **The Fubini–Study form is analytic**: the section of `fsForm` is `C^ω`, not merely `C^∞` —
the manifold is analytic and so is the potential. -/
theorem contMDiff_omega_fsForm :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ))) ω
      (fun x : ℙ ℂ (Ambient n) =>
        TotalSpace.mk' ((Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) x (fsForm x)) :=
  contMDiff_omega_fsSection

/-- ★★ **The Fubini–Study form as an analytic global 2-form on `ℂℙⁿ`**: the section of `fsForm`,
as a term of the `ω` type. -/
noncomputable def fsFormAnalytic :
    DifferentialForm (modelWithCornersSelf ℝ (Fin n → ℂ)) (ℙ ℂ (Ambient n)) ω (Fin 2) ℝ :=
  ⟨fsSection, contMDiff_omega_fsSection⟩

@[simp] theorem fsFormAnalytic_apply (x : ℙ ℂ (Ambient n)) : fsFormAnalytic x = fsForm x := rfl

/-! ### Non-vacuity -/

/-- The origin of the `i`-th affine chart, `[0 : … : 1 : … : 0]`. -/
noncomputable def origin (i : Fin (n + 1)) : ℙ ℂ (Ambient n) :=
  mk ℂ (insertOne i 0) (insertOne_ne_zero i 0)

/-- Any representative of the chart origin is a nonzero multiple of `insertOne i 0`. -/
lemma rep_origin (i : Fin (n + 1)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ k, (origin i).rep k = a * insertOne i 0 k := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff ℂ _ _ (rep_nonzero _) (insertOne_ne_zero i 0)).mp
    (mk_rep (origin i))
  refine ⟨a, a.ne_zero, fun k => ?_⟩
  rw [← ha]
  simp [Units.smul_def]

/-- The atlas has no choice at the chart origin: `i` is the only coordinate that does not vanish. -/
lemma idx_origin (i : Fin (n + 1)) : idx (origin i) = i := by
  obtain ⟨a, -, hk⟩ := rep_origin i
  by_contra h
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
  apply idx_spec (origin i)
  rw [hk, ← hj, insertOne_apply_succAbove]
  simp

lemma chartFun_idx_origin (i : Fin (n + 1)) : chartFun (idx (origin i)) (origin i) = 0 := by
  rw [idx_origin]
  obtain ⟨a, -, hk⟩ := rep_origin i
  funext j
  show (origin i).rep (i.succAbove j) / (origin i).rep i = 0
  rw [hk, insertOne_apply_succAbove]
  simp

/-- At a chart origin the section is the model form at `0`. -/
theorem fsSection_origin (i : Fin (n + 1)) : fsSection (origin i) = fsModelForm 0 := by
  rw [fsSection, chartFun_idx_origin]

/-- The model form at `0` is `-4` times the flat fundamental form (`fsChartForm_zero`). -/
theorem fsModelForm_zero_apply (v : Fin 2 → (Fin n → ℂ)) :
    fsModelForm 0 v = -4 * fundamentalForm (toLpCLM (v 0)) (toLpCLM (v 1)) := by
  simp [fsModelForm, fsChartForm_zero, fundamentalFormAlt_apply]

/-- ★★ **The Fubini–Study form is not the zero form** (for `n ≥ 1`): at a chart origin it pairs
a unit vector `e` with `i • e` to `-4 ‖e‖² ≠ 0`. -/
theorem fsForm_ne_zero (hn : 0 < n) : (fsForm (n := n)) ≠ 0 := by
  intro h
  set e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1 with he_def
  have he : e ≠ 0 := by
    intro h0
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v ⟨0, hn⟩) h0
    simp [he_def] at this
  -- evaluate both sides at the chart origin on the pair (e, i·e), read in the `Pi` model
  have h1 := congrArg (fun s : DifferentialForm (modelWithCornersSelf ℝ (Fin n → ℂ))
      (ℙ ℂ (Ambient n)) ∞ (Fin 2) ℝ =>
    s (origin 0) ![WithLp.ofLp e, WithLp.ofLp (Complex.I • e)]) h
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply] at h1
  have h1' : fsSection (origin 0) ![WithLp.ofLp e, WithLp.ofLp (Complex.I • e)] = 0 := h1
  have hpt := congrArg (fun α : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ =>
    α ![WithLp.ofLp e, WithLp.ofLp (Complex.I • e)]) (fsSection_origin (n := n) 0)
  have h0 : fsModelForm (n := n) 0 ![WithLp.ofLp e, WithLp.ofLp (Complex.I • e)] = 0 :=
    hpt.symm.trans h1'
  rw [fsModelForm_zero_apply] at h0
  have hc : ∀ u : EuclideanSpace ℂ (Fin n), toLpCLM (WithLp.ofLp u) = u := fun u => rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc] at h0
  have hpos : 0 < fundamentalForm e (Complex.I • e) :=
    fundamentalForm_complexStructure_self_pos he
  linarith

/-! ### Closedness: `d ω_FS = 0` on `ℂℙⁿ` -/

section Closed
open DifferentialForm

/-- The model form is closed on the flat model: the chart form is (`extDeriv_fsChartForm`), and
the model form is its pullback along the linear identification `toLpCLM`. -/
theorem extDeriv_fsModelForm (w : Fin n → ℂ) : extDeriv (fsModelForm (n := n)) w = 0 := by
  have h : fsModelForm (n := n)
      = fun w => (fsChartForm (toLpCLM w)).compContinuousLinearMap (fderiv ℝ toLpCLM w) := by
    funext w
    rw [fsModelForm, ContinuousLinearMap.fderiv]
  rw [h, extDeriv_pullback ((contDiff_fsChartForm (n := n)).differentiable (by simp) _)
    (ContinuousLinearMap.contDiff (n := ∞)
      (toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n))).contDiffAt
    minSmoothness_two_le_infty]
  rw [show extDeriv (fsChartForm (E := EuclideanSpace ℂ (Fin n))) (toLpCLM w) = 0 from
    congrFun extDeriv_fsChartForm _]
  ext v
  simp

/-- ★★★ **The Fubini–Study form is closed on `ℂℙⁿ`**, pointwise: in the chart at `x` its local
representative is the flat chart form, whose flat `d` is zero. -/
theorem mextDeriv_fsSection (x : ℙ ℂ (Ambient n)) : mextDeriv fsSection x = 0 := by
  show extDeriv (localRep fsSection x) (chartAt (Fin n → ℂ) x x) = 0
  have hev : localRep fsSection x =ᶠ[𝓝 (chartAt (Fin n → ℂ) x x)] fsModelForm := by
    filter_upwards [(chartAt (Fin n → ℂ) x).open_target.mem_nhds (mem_chart_target _ x)] with w hw
    have h := localRep_fsSection x ((chartAt (Fin n → ℂ) x).symm w)
      ((chartAt (Fin n → ℂ) x).map_target hw)
    show (trivializationAt _ _ x ⟨(chartAt (Fin n → ℂ) x).symm w, _⟩).2 = _
    rw [h]
    exact congrArg fsModelForm ((chartAt (Fin n → ℂ) x).right_inv hw)
  rw [hev.extDeriv_eq]
  exact extDeriv_fsModelForm _

/-- ★★★ **`d ω_FS = 0` on `ℂℙⁿ`.** -/
theorem fsForm_mextDeriv : (fsForm (n := n)).mextDeriv = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact mextDeriv_fsSection x

end Closed

/-! ### The top power -/

/-- **The top power of the Fubini–Study form**, a `2n`-form on `ℂℙⁿ`. -/
noncomputable def fsTopForm (n : ℕ) :
    DifferentialForm (modelWithCornersSelf ℝ (Fin n → ℂ)) (ℙ ℂ (Ambient n)) ∞ (Fin (2 * n)) ℝ :=
  DifferentialForm.wedgePow (fsForm (n := n)) n



end Projectivization
