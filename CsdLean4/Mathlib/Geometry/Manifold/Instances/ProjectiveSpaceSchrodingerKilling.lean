/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerHolomorphic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyVolume
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianLieDerivative
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonJacobi
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannianBundle

/-!
# The Schrödinger field is Killing, infinitesimally

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #341 (geometric QM, completion item 8c, first half; split from #340).

The flow of a Schrödinger field is an isometry of the Fubini–Study metric
(`fsMetric_hamiltonianFlow_schrodinger`). Here is the infinitesimal statement, in the form the
Koszul formula consumes. No flow is differentiated: in every affine chart

* the Lie derivative of the model form along the chart field vanishes (Q29,
  `flatLieDeriv_localHamiltonianVector_localRep_eq_zero`: the field is Hamiltonian), and
* the chart field's derivative commutes with `i·` (`isHolomorphicVectorField_schrodingerField`),

and the metric is `g(u, v) = ω(i u, v)` with `i·` constant in the chart, so the Lie derivative of
the metric is the Lie derivative of the form evaluated on `(i u, v)`.

* `localHamiltonianVector_schrodingerHamiltonian` — the local Hamiltonian vector is the chart
  field;
* ★★ `flatKilling_schrodingerChartField` — **the flat Killing equation**:
  `Dω(F)(i u, v) + ω(i DF u, v) + ω(i u, DF v) = 0` for the chart field `F` of `X_H`;
  `fderiv_fsModelMetricCLM_apply`; ★★ `flatKilling_metric_schrodingerChartField` — the same for
  the model metric, `Dg(F)(u, v) + g(DF u, v) + g(u, DF v) = 0`;
* `mpullback_extChartAt_symm_eq_chartField`, `fsMetric_eq_chartField` — the chart reads fields
  and the metric;
* ★★★ `mfderiv_fsMetric_schrodingerField` — **`d⟨X_H, Z⟩(X_H) = ⟨X_H, [X_H, Z]⟩`** for every `Z`
  differentiable at the point: the Killing identity `X⟨Y, Z⟩ = ⟨[X, Y], Z⟩ + ⟨Y, [X, Z]⟩` at `Y = X`,
  the form the Koszul formula of #342 consumes.

## Honest scope

⚠️ **The `Y = X` case.** The polarised identity for general `Y` follows the same way (the flat
equation holds for all `u, v`) but is not stated; #342 needs only `Y = X`.

## References

A. Ashtekar, T. A. Schilling, in *On Einstein's Path* (1999) 23, § 3 (Schrödinger fields are
Killing); `Instances/ProjectiveSpaceSchrodingerHolomorphic.lean` (KG-3′),
`Geometry/Manifold/HamiltonianLieDerivative.lean` (Q29); `specs/BACKLOG.md` #341, #342, #340;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Bundle Kahler DifferentialForm VectorField

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- The local Hamiltonian vector of `−2⟨H⟩` in the chart at `x₀` is the Schrödinger chart field. -/
theorem localHamiltonianVector_schrodingerHamiltonian {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n)) :
    localHamiltonianVector fsForm (schrodingerHamiltonian H) x₀
      = schrodingerChartField H (idx x₀) := by
  funext w
  rw [← chartField_hamiltonianVectorField fsForm (schrodingerHamiltonian H)
    (fsForm_isSymplectic n).nondegenerate (contMDiff_schrodingerHamiltonian H) x₀
    (Set.mem_univ w)]
  rw [← chartField_schrodingerField hH x₀ w, schrodingerField_eq_hamiltonianVectorField hH]
  rfl

/-- ★★ **The flat Killing equation for the Schrödinger chart field**:
`Dω(F)(i u, v) + ω(i DF u, v) + ω(i u, DF v) = 0`, with `ω` the model form and `F` the chart field
of `X_H` in the chart of `x₀`. -/
theorem flatKilling_schrodingerChartField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n)) (w u v : Fin n → ℂ) :
    fderiv ℝ fsModelForm w (schrodingerChartField H (idx x₀) w) ![Complex.I • u, v]
      + fsModelForm w ![Complex.I • fderiv ℝ (schrodingerChartField H (idx x₀)) w u, v]
      + fsModelForm w ![Complex.I • u, fderiv ℝ (schrodingerChartField H (idx x₀)) w v] = 0 := by
  have hq := flatLieDeriv_localHamiltonianVector_localRep_eq_zero fsForm
    (schrodingerHamiltonian H) (fsForm_isSymplectic n) (contMDiff_schrodingerHamiltonian H) x₀
    (Set.mem_univ w) ![Complex.I • u, v]
  have hΩ : localRep (fun x => fsForm (n := n) x) x₀ = fsModelForm :=
    funext (localRep_fsSection' x₀)
  have hhol := ((isHolomorphicVectorField_schrodingerField hH) x₀ w (Set.mem_univ w)).2 u
  rw [funext (chartField_schrodingerField hH x₀), modelJ_apply, modelJ_apply] at hhol
  rw [localHamiltonianVector_schrodingerHamiltonian hH, hΩ, flatLieDeriv,
    Fin.sum_univ_two] at hq
  have e0 : Function.update ![Complex.I • u, v] 0
      (fderiv ℝ (schrodingerChartField H (idx x₀)) w (![Complex.I • u, v] 0))
      = ![Complex.I • fderiv ℝ (schrodingerChartField H (idx x₀)) w u, v] := by
    funext i
    fin_cases i
    · simp [hhol]
    · rfl
  have e1 : Function.update ![Complex.I • u, v] 1
      (fderiv ℝ (schrodingerChartField H (idx x₀)) w (![Complex.I • u, v] 1))
      = ![Complex.I • u, fderiv ℝ (schrodingerChartField H (idx x₀)) w v] := by
    funext i
    fin_cases i
    · rfl
    · simp
  rw [e0, e1, ← add_assoc] at hq
  exact hq

set_option synthInstance.maxHeartbeats 200000 in
/-- The derivative of the model metric in the base point is the derivative of the model form on
`(i u, v)`. -/
theorem fderiv_fsModelMetricCLM_apply (w d u v : Fin n → ℂ) :
    fderiv ℝ fsModelMetricCLM w d u v = fderiv ℝ fsModelForm w d ![Complex.I • u, v] := by
  have hG : DifferentiableAt ℝ (fsModelMetricCLM (n := n)) w :=
    (contDiff_fsModelMetricCLM.differentiable (by simp)) w
  have hω : DifferentiableAt ℝ (fsModelForm (n := n)) w :=
    ((contDiff_omega_fsModelForm (n := n)).differentiable (by simp)) w
  have hGu : DifferentiableAt ℝ (fun w => fsModelMetricCLM (n := n) w u) w :=
    hG.clm_apply (differentiableAt_const u)
  have h1 : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u) w
      = (fsModelMetricCLM w).comp (fderiv ℝ (fun _ : Fin n → ℂ => u) w)
        + (fderiv ℝ fsModelMetricCLM w).flip u :=
    fderiv_clm_apply hG (differentiableAt_const u)
  have h2 : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u v) w
      = (fsModelMetricCLM w u).comp (fderiv ℝ (fun _ : Fin n → ℂ => v) w)
        + (fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u) w).flip v :=
    fderiv_clm_apply hGu (differentiableAt_const v)
  have h3 : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u v) w
      = (ContinuousAlternatingMap.apply ℝ (Fin n → ℂ) ℝ ![Complex.I • u, v]).comp
          (fderiv ℝ fsModelForm w) :=
    ((ContinuousAlternatingMap.apply ℝ (Fin n → ℂ) ℝ ![Complex.I • u, v]).hasFDerivAt.comp w
      hω.hasFDerivAt).fderiv
  have e1 : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u) w d
      = fderiv ℝ fsModelMetricCLM w d u := by
    rw [h1]
    simp
  have e2 : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u v) w d
      = fderiv ℝ (fun w => fsModelMetricCLM (n := n) w u) w d v := by
    rw [h2]
    simp
  have e3 := congrArg (fun L => L d) h3
  rw [← e1, ← e2]
  exact e3

/-- ★★ **The flat Killing equation, metric form**:
`Dg(F)(u, v) + g(DF u, v) + g(u, DF v) = 0` for the model metric `g` and the chart field `F` of
`X_H`. -/
theorem flatKilling_metric_schrodingerChartField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n)) (w u v : Fin n → ℂ) :
    fderiv ℝ fsModelMetricCLM w (schrodingerChartField H (idx x₀) w) u v
      + fsModelMetricCLM w (fderiv ℝ (schrodingerChartField H (idx x₀)) w u) v
      + fsModelMetricCLM w u (fderiv ℝ (schrodingerChartField H (idx x₀)) w v) = 0 := by
  rw [fderiv_fsModelMetricCLM_apply]
  exact flatKilling_schrodingerChartField hH x₀ w u v

/-- The pullback of a vector field along the inverse chart is its chart field. -/
theorem mpullback_extChartAt_symm_eq_chartField
    (V : ∀ x : ℙ ℂ (Ambient n), TangentSpace 𝓘(ℝ, Fin n → ℂ) x) (x₀ : ℙ ℂ (Ambient n))
    (w : Fin n → ℂ) :
    mpullback 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm V w
      = chartField V x₀ w := by
  have hw' : w ∈ (chartAt (Fin n → ℂ) x₀).target := Set.mem_univ w
  have hw : w ∈ (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).target := by simpa using hw'
  have hy : (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm w ∈ (chartAt (Fin n → ℂ) x₀).source := by
    have := (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).map_target hw
    rwa [extChartAt_source] at this
  have hb : (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm w
      ∈ (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀).baseSet := hy
  rw [mpullback_apply, inverse_mfderiv_extChartAt_symm x₀ hw,
    ← TangentBundle.continuousLinearMapAt_trivializationAt hy, chartField_eq_trivializationAt_snd]
  exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀) hb _

/-- The metric along two fields, read in the chart at `x₀`. -/
theorem fsMetric_eq_chartField (x₀ : ℙ ℂ (Ambient n))
    (V W : ∀ x : ℙ ℂ (Ambient n), TangentSpace 𝓘(ℝ, Fin n → ℂ) x) {y : ℙ ℂ (Ambient n)}
    (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source) :
    fsMetric y (V y) (W y)
      = fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y) (chartField V x₀ (chartAt (Fin n → ℂ) x₀ y))
          (chartField W x₀ (chartAt (Fin n → ℂ) x₀ y)) := by
  have hb : y ∈ (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀).baseSet := hy
  have hyw : (chartAt (Fin n → ℂ) x₀).symm (chartAt (Fin n → ℂ) x₀ y) = y :=
    (chartAt (Fin n → ℂ) x₀).left_inv hy
  have hcf : ∀ U : ∀ x : ℙ ℂ (Ambient n), TangentSpace 𝓘(ℝ, Fin n → ℂ) x,
      U y = (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀).symmL ℝ y
        (chartField U x₀ (chartAt (Fin n → ℂ) x₀ y)) := by
    intro U
    rw [chartField_eq_trivializationAt_snd, hyw,
      ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
    exact ((trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀)
      |>.symmL_continuousLinearMapAt hb _).symm
  rw [hcf V, hcf W]
  exact fsMetric_symmL_symmL x₀ y hy _ _

/-- ★★★ **The Schrödinger field is Killing**: `d⟨X_H, Z⟩(X_H) = ⟨X_H, [X_H, Z]⟩` for every vector
field `Z` differentiable at the point (the Killing identity `X⟨Y, Z⟩ = ⟨[X, Y], Z⟩ + ⟨Y, [X, Z]⟩` at
`Y = X`). -/
theorem mfderiv_fsMetric_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n))
    {Z : ∀ x : ℙ ℂ (Ambient n), TangentSpace 𝓘(ℝ, Fin n → ℂ) x}
    (hZ : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ).tangent
      (fun x => TotalSpace.mk' (Fin n → ℂ) x (Z x)) x₀) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (fun q => fsMetric q (schrodingerField H q) (Z q)) x₀
        (schrodingerField H x₀)
      = fsMetric x₀ (schrodingerField H x₀)
          (mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) Z x₀) := by
  set φ := chartAt (Fin n → ℂ) x₀ with hφ
  set F := schrodingerChartField H (idx x₀) with hFdef
  set Zt := chartField Z x₀ with hZt
  have hXF : chartField (schrodingerField H) x₀ = F := funext (chartField_schrodingerField hH x₀)
  have hsrc : φ.source ∈ nhds x₀ := φ.open_source.mem_nhds (mem_chart_source _ x₀)
  -- differentiability of the chart data
  have hFd : DifferentiableAt ℝ F (φ x₀) :=
    (differentiableAt_schrodingerChartField H (idx x₀) (φ x₀)).restrictScalars ℝ
  have hZd : DifferentiableAt ℝ Zt (φ x₀) := by
    have h1 := (mdifferentiableAt_section 𝓘(ℝ, Fin n → ℂ) Z).1 hZ
    have hs : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) φ.symm (φ x₀) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas _ x₀) (mem_chart_target _ x₀)
    have h2 := (by rw [φ.left_inv (mem_chart_source _ x₀)]; exact h1 :
      MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (fun b => (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀
          ⟨b, Z b⟩).2) (φ.symm (φ x₀))).comp (φ x₀) hs
    have h3 : Zt = (fun b => (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀
        ⟨b, Z b⟩).2) ∘ φ.symm := funext fun w => chartField_eq_trivializationAt_snd Z x₀ w
    rw [h3]
    exact h2.differentiableAt
  have hGd : DifferentiableAt ℝ (fsModelMetricCLM (n := n)) (φ x₀) :=
    (contDiff_fsModelMetricCLM.differentiable (by simp)) _
  set h : (Fin n → ℂ) → ℝ := fun w => fsModelMetricCLM w (F w) (Zt w) with hhdef
  have hcd : DifferentiableAt ℝ (fun w => fsModelMetricCLM (n := n) w (F w)) (φ x₀) :=
    hGd.clm_apply hFd
  have hhd : DifferentiableAt ℝ h (φ x₀) := hcd.clm_apply hZd
  -- the metric along the fields is `h` read through the chart
  have hloc : ∀ y ∈ φ.source, fsMetric y (schrodingerField H y) (Z y) = h (φ y) := by
    intro y hy
    rw [fsMetric_eq_chartField x₀ _ _ hy, hXF]
  have hf : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ)
      (fun q => fsMetric q (schrodingerField H q) (Z q)) x₀ := by
    have h1 : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (h ∘ φ) x₀ :=
      hhd.mdifferentiableAt.comp x₀ (mdifferentiableAt_atlas (chart_mem_atlas _ x₀)
        (mem_chart_source _ x₀))
    exact h1.congr_of_eventuallyEq (Filter.mem_of_superset hsrc fun y hy => hloc y hy)
  have hcomp : (fun q => fsMetric q (schrodingerField H q) (Z q)) ∘ φ.symm = h := by
    funext w
    have hwt : w ∈ φ.target := Set.mem_univ w
    have hw : φ.symm w ∈ φ.source := φ.map_target hwt
    show fsMetric (φ.symm w) _ _ = h w
    rw [hloc _ hw, φ.right_inv hwt]
  -- the left side, in the chart
  have hX0 : (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀
      ⟨x₀, schrodingerField H x₀⟩).2 = F (φ x₀) := by
    rw [← hXF, chartField_eq_trivializationAt_snd, φ.left_inv (mem_chart_source _ x₀)]
  have hL := fderiv_comp_chartAt_symm_trivializationAt_snd x₀ (mem_chart_source _ x₀) hf
    (schrodingerField H x₀)
  rw [hcomp, hX0] at hL
  rw [← hL]
  -- the bracket, in the chart
  have hrange : Set.range (𝓘(ℝ, Fin n → ℂ)) = Set.univ := by simp
  have hbr : mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) Z x₀
      = lieBracket ℝ F Zt (φ x₀) := by
    have hid : ∀ v : Fin n → ℂ,
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀)).inverse v = v := by
      intro v
      rw [ContinuousLinearMap.inverse_id]
      rfl
    rw [← mlieBracketWithin_univ, mlieBracketWithin_apply, mfderiv_extChartAt_self]
    refine (hid _).trans ?_
    simp only [hrange, mpullbackWithin_univ, Set.preimage_univ, Set.univ_inter]
    have e1 : flatField (mpullback 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm (schrodingerField H)) = F := by
      funext w
      rw [flatField, mpullback_extChartAt_symm_eq_chartField, hXF]
    have e2 : flatField (mpullback 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm Z) = Zt := by
      funext w
      rw [flatField, mpullback_extChartAt_symm_eq_chartField]
    have e3 := congrFun (lieBracketWithin_univ (𝕜 := ℝ)
      (V := flatField (mpullback 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm (schrodingerField H)))
      (W := flatField (mpullback 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀).symm Z))) (extChartAt 𝓘(ℝ, Fin n → ℂ) x₀ x₀)
    refine e3.trans ?_
    rw [e1, e2]
    rfl
  rw [hbr, fsMetric_eq_fsModelMetricCLM]
  show fderiv ℝ h (φ x₀) (F (φ x₀)) = fsModelMetricCLM (φ x₀) (F (φ x₀)) (lieBracket ℝ F Zt (φ x₀))
  -- the product rule, and the flat Killing equation
  have hc : fderiv ℝ (fun w => fsModelMetricCLM (n := n) w (F w)) (φ x₀)
      = (fsModelMetricCLM (φ x₀)).comp (fderiv ℝ F (φ x₀))
        + (fderiv ℝ fsModelMetricCLM (φ x₀)).flip (F (φ x₀)) := fderiv_clm_apply hGd hFd
  have hh : fderiv ℝ h (φ x₀)
      = (fsModelMetricCLM (φ x₀) (F (φ x₀))).comp (fderiv ℝ Zt (φ x₀))
        + (fderiv ℝ (fun w => fsModelMetricCLM (n := n) w (F w)) (φ x₀)).flip (Zt (φ x₀)) :=
    fderiv_clm_apply hcd hZd
  have hK := flatKilling_metric_schrodingerChartField hH x₀ (φ x₀) (F (φ x₀)) (Zt (φ x₀))
  rw [hh, hc, lieBracket_eq]
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub]
  rw [← hFdef] at hK
  linarith

end Projectivization
