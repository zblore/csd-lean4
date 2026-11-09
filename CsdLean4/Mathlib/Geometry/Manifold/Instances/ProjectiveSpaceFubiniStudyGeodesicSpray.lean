/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.CovariantDerivativeAlongCurve
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannianBundle

/-!
# The Fubini–Study geodesic spray

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #343, #344 (geometric QM: the local geodesic ODE of `ℂℙⁿ`, local existence and
uniqueness).

The geodesic equation of `ℂℙⁿ` with the Fubini–Study metric, as a first-order ODE in an affine
chart, with smooth right-hand side.

* `fsKoszul w u v` — the Koszul functional `z ↦ ½ (Dg(u)(v, z) + Dg(v)(z, u) − Dg(z)(u, v))` of the
  model metric `g = fsModelMetricCLM`; `fsModelMetricCLM_injective`,
  `isInvertible_fsModelMetricCLM` — `g_w : ℂⁿ → (ℂⁿ)*` is invertible (coercivity);
* `fsChristoffel w v u = g_w⁻¹ (fsKoszul w u v)` — **the Fubini–Study Christoffel symbols** in
  an affine chart; ★★ `contDiff_fsChristoffel` — **smooth** (`C^∞`) jointly in `(w, v, u)`;
* `fsGeodesicSpray (w, v) = (v, −Γ_w(v, v))`; ★★ `contDiff_fsGeodesicSpray` — **the spray is
  `C^∞`** on `ℂⁿ × ℂⁿ`;
* `mfderiv_inner_chartConstField` — the derivative of `⟨σ_a, σ_b⟩` along `σ_c` is `Dg(c)(a, b)`
  for chart-constant fields;
* ★★★ `chartChristoffel_leviCivita` — **the Christoffel symbols of Mathlib's Levi-Civita
  connection of `ℂℙⁿ`, in the chart at any `x₀`, are `fsChristoffel`** on the chart's target (Koszul
  formula with chart-constant fields, whose brackets vanish); ★★
  `contDiffOn_chartChristoffel_leviCivita` — they are `C^∞` there;
* ★★★ `isGeodesic_iff_fsGeodesicSpray` — **the local geodesic equation**: a curve that stays in
  the source of the chart at `x₀` is an `IsGeodesic` of the Levi-Civita connection iff its chart
  coordinate `w` and some `v : ℝ → ℂⁿ` solve `(w', v') = fsGeodesicSpray (w, v)`;
  `chartAt_target_eq_univ`, `chartSpray_leviCivita` (the chart spray is `fsGeodesicSpray` in every
  affine chart), ★★★ `isGeodesicOn_iff_fsGeodesicSpray` — the same on an open set of times;
* ★★★ `exists_isGeodesicOn_fs` — **local existence**: for every `x₀ ∈ ℂℙⁿ` and `v₀ ∈ T_{x₀}ℂℙⁿ`
  there are `ε > 0` and `γ` with `γ 0 = x₀`, `γ'(0) = v₀`, geodesic on `(-ε, ε)` (Mathlib's
  Picard–Lindelöf on the spray);
* ★★★ `eventuallyEq_of_isGeodesicOn_fs` — **local uniqueness**: two geodesics on an open set of
  times containing `t₀` with the same position and velocity at `t₀` agree near `t₀` (Mathlib's
  `ODE_solution_unique_of_eventually`, the spray being Lipschitz near the initial point).

## Honest scope

⚠️ **Local only.** Existence is on some `(-ε, ε)` with `ε` not estimated; uniqueness is near `t₀`
(`=ᶠ[𝓝 t₀]`), not on the whole common interval of two geodesics (that needs a connectedness
argument across charts). Maximal geodesics, completeness and the exponential map are not stated.

⚠️ **One chart per statement.** `isGeodesic_iff_fsGeodesicSpray` assumes `γ t` is in the chart's
source for every `t ∈ ℝ`; `isGeodesicOn_iff_fsGeodesicSpray` only on the open set `I`, which is
what the local existence and uniqueness theorems use.

⚠️ **The Christoffel symbols are `g⁻¹` of the Koszul form, not a closed formula.** No explicit
rational expression for `Γ_w` in terms of `w` (the Kähler form of the symbols) is derived.

⚠️ **One heartbeat override.** `mfderiv_inner_chartConstField` raises
`synthInstance.maxHeartbeats` to `200000` for the instances on iterated continuous linear maps
of `ℂⁿ` (the precedent of `ProjectiveSpaceSchrodingerKilling.lean`).

## References

J. M. Lee, *Introduction to Riemannian Manifolds* (2nd ed., 2018), Ch. 4 (Christoffel symbols,
the geodesic equation in coordinates) and Ch. 5 (the Koszul formula);
`CovariantDerivativeAlongCurve.lean` (#339: `isGeodesic_iff_chartSpray`,
`mlieBracket_chartConstField`), `Instances/ProjectiveSpaceFubiniStudyRiemannianBundle.lean` (#338:
`fsRiemannianMetric`, `fsMetric_symmL_symmL`); Mathlib's `leviCivitaConnection_apply_inner`;
Mathlib's `Analysis/ODE/ExistUnique.lean`; `specs/BACKLOG.md` #338, #339, #343, #344;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Filter

noncomputable section

namespace Projectivization

open CovariantDerivative FubiniStudy
open scoped LinearAlgebra.Projectivization

variable {n : ℕ}

/-- **The Koszul functional of the model metric** at `w`:
`z ↦ ½ (Dg(u)(v, z) + Dg(v)(z, u) − Dg(z)(u, v))`, `g = fsModelMetricCLM`. -/
def fsKoszul (w u v : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (fderiv ℝ fsModelMetricCLM w u v + (fderiv ℝ fsModelMetricCLM w v).flip u
    - (ContinuousLinearMap.apply ℝ ℝ v).comp
        ((ContinuousLinearMap.apply ℝ ((Fin n → ℂ) →L[ℝ] ℝ) u).comp
          (fderiv ℝ fsModelMetricCLM w)))

/-- The Koszul functional, evaluated. -/
theorem fsKoszul_apply (w u v z : Fin n → ℂ) :
    fsKoszul w u v z = (fderiv ℝ fsModelMetricCLM w u v z + fderiv ℝ fsModelMetricCLM w v z u
      - fderiv ℝ fsModelMetricCLM w z u v) / 2 := by
  simp [fsKoszul]
  ring

/-- The model metric is nondegenerate. -/
theorem fsModelMetricCLM_injective (w : Fin n → ℂ) : Function.Injective (fsModelMetricCLM w) := by
  intro u u' h
  rw [← sub_eq_zero]
  have hd : fsModelMetricCLM w (u - u') = 0 := by rw [map_sub, h, sub_self]
  have h0 : fsModelMetric w (u - u') (u - u') = 0 := by
    rw [← fsModelMetricCLM_apply, hd]
    rfl
  have hge := fsModelMetric_self_ge w (u - u')
  rw [h0] at hge
  have hN : (0 : ℝ) < (1 + ‖toLpCLM w‖ ^ 2) ^ 2 := by positivity
  have h4 : 4 * ‖toLpCLM (u - u')‖ ^ 2 ≤ 0 := by rwa [div_le_iff₀ hN, zero_mul] at hge
  have h5 : ‖toLpCLM (u - u')‖ = 0 := by nlinarith [norm_nonneg (toLpCLM (u - u'))]
  exact norm_le_zero_iff.1 ((norm_le_norm_toLpCLM (u - u')).trans h5.le)

/-- The model metric `g_w : ℂⁿ → (ℂⁿ)*` is invertible. -/
theorem isInvertible_fsModelMetricCLM (w : Fin n → ℂ) : (fsModelMetricCLM w).IsInvertible := by
  have hdim : Module.finrank ℝ (Fin n → ℂ) = Module.finrank ℝ ((Fin n → ℂ) →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap :
      ((Fin n → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((Fin n → ℂ) →L[ℝ] ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  let e := LinearMap.linearEquivOfInjective (fsModelMetricCLM w : (Fin n → ℂ) →ₗ[ℝ] _)
    (fsModelMetricCLM_injective w) hdim
  exact ⟨e.toContinuousLinearEquiv, by ext u; rfl⟩

/-- The inverse of the model metric is smooth in the base point. -/
theorem contDiff_inverse_fsModelMetricCLM :
    ContDiff ℝ ∞ (fun w : Fin n → ℂ => (fsModelMetricCLM w).inverse) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  obtain ⟨e, he⟩ := isInvertible_fsModelMetricCLM w
  have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞) e
  rw [he] at h
  exact h.comp w contDiff_fsModelMetricCLM.contDiffAt

/-- The derivative of the model metric is smooth, along smooth base points and directions. -/
theorem contDiff_fderiv_fsModelMetricCLM_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {g k : X → Fin n → ℂ} (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ fsModelMetricCLM (g x) (k x)) :=
  ContDiff.fderiv_apply (f := fun _ => fsModelMetricCLM)
    (contDiff_fsModelMetricCLM.comp contDiff_snd) hg hk (by simp)

/-- **The Christoffel symbols of the Fubini–Study metric in an affine chart**:
`Γ_w(v, u) = g_w⁻¹(K_w(u, v, ·))`, the Koszul formula with constant coordinate fields. -/
def fsChristoffel (w v u : Fin n → ℂ) : Fin n → ℂ :=
  (fsModelMetricCLM w).inverse (fsKoszul w u v)

/-- ★★ **The Fubini–Study Christoffel symbols are smooth**, jointly in the point and both slots. -/
theorem contDiff_fsChristoffel :
    ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) =>
      fsChristoffel p.1 p.2.1 p.2.2) := by
  have hK : ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) =>
      fsKoszul p.1 p.2.2 p.2.1) := by
    rw [contDiff_clm_apply_iff]
    intro z
    simp only [fsKoszul_apply]
    have hu : ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => p.2.2) :=
      contDiff_snd.comp contDiff_snd
    have hv : ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => p.2.1) :=
      contDiff_fst.comp contDiff_snd
    have hz : ContDiff ℝ ∞ (fun _ : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => z) :=
      contDiff_const
    have hw : ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => p.1) :=
      contDiff_fst
    have t1 := ((contDiff_fderiv_fsModelMetricCLM_apply hw hu).clm_apply hv).clm_apply hz
    have t2 := ((contDiff_fderiv_fsModelMetricCLM_apply hw hv).clm_apply hz).clm_apply hu
    have t3 := ((contDiff_fderiv_fsModelMetricCLM_apply hw hz).clm_apply hu).clm_apply hv
    exact ((t1.add t2).sub t3).div_const 2
  exact (contDiff_inverse_fsModelMetricCLM.comp contDiff_fst).clm_apply hK

/-- **The geodesic spray of the Fubini–Study metric in an affine chart**:
`(w, v) ↦ (v, −Γ_w(v, v))`. -/
def fsGeodesicSpray (p : (Fin n → ℂ) × (Fin n → ℂ)) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (p.2, -fsChristoffel p.1 p.2 p.2)

/-- ★★ **The Fubini–Study geodesic spray is smooth.** -/
theorem contDiff_fsGeodesicSpray : ContDiff ℝ ∞ (fsGeodesicSpray (n := n)) :=
  contDiff_snd.prodMk
    (contDiff_fsChristoffel.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_snd))).neg

set_option synthInstance.maxHeartbeats 200000 in
open scoped RealInnerProductSpace in
/-- The derivative of `⟨σ_a, σ_b⟩` along `σ_c`, for fields constant in the chart at `x₀`, is
`Dg(c)(a, b)`. -/
theorem mfderiv_inner_chartConstField (x₀ : ℙ ℂ (Ambient n)) {y : ℙ ℂ (Ambient n)}
    (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source) (a b c : Fin n → ℂ) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ)
        (fun x => ⟪chartConstField x₀ a x, chartConstField x₀ b x⟫) y (chartConstField x₀ c y)
      = fderiv ℝ fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y) c a b := by
  set e₀ := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀ with he₀
  set L : ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.apply ℝ _ a) with hL
  have hev : (fun x => ⟪chartConstField x₀ a x, chartConstField x₀ b x⟫)
      =ᶠ[𝓝 y] fun x => L (fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ x)) := by
    filter_upwards [(chartAt (Fin n → ℂ) x₀).open_source.mem_nhds hy] with x hx
    have hb : x ∈ e₀.baseSet := hx
    have h := fsMetric_symmL_symmL x₀ x hx a b
    rw [Trivialization.symmL_apply _ hb, Trivialization.symmL_apply _ hb] at h
    exact h
  have hφ : HasMFDerivAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (chartAt (Fin n → ℂ) x₀) y
      (e₀.continuousLinearMapAt ℝ y) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
    exact (mdifferentiableAt_atlas (chart_mem_atlas _ x₀) hy).hasMFDerivAt
  have hG : HasFDerivAt (fun w => L (fsModelMetricCLM w))
      (L.comp (fderiv ℝ fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y)))
      (chartAt (Fin n → ℂ) x₀ y) :=
    L.hasFDerivAt.comp _
      ((contDiff_fsModelMetricCLM.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h : HasMFDerivAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ)
      (fun x => L (fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ x))) y
      ((L.comp (fderiv ℝ fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y))).comp
        (e₀.continuousLinearMapAt ℝ y)) :=
    hG.hasMFDerivAt.comp y hφ
  rw [hev.mfderiv_eq, h.mfderiv]
  have hc : chartConstField x₀ c y = e₀.symmL ℝ y c := (Trivialization.symmL_apply _ hy c).symm
  rw [hc]
  show L (fderiv ℝ fsModelMetricCLM _ (e₀.continuousLinearMapAt ℝ y (e₀.symmL ℝ y c))) = _
  rw [e₀.continuousLinearMapAt_symmL hy]
  rfl

open scoped RealInnerProductSpace in
/-- ★★★ **The Christoffel symbols of the Levi-Civita connection of `ℂℙⁿ` in an affine chart are
the Fubini–Study `fsChristoffel`**, at every point of the chart. -/
theorem chartChristoffel_leviCivita (x₀ : ℙ ℂ (Ambient n)) {w : Fin n → ℂ}
    (hw : w ∈ (chartAt (Fin n → ℂ) x₀).target) (v u : Fin n → ℂ) :
    chartChristoffel (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) x₀ w v u
      = fsChristoffel w v u := by
  set y := (chartAt (Fin n → ℂ) x₀).symm w with hydef
  have hy : y ∈ (chartAt (Fin n → ℂ) x₀).source := (chartAt _ x₀).map_target hw
  have hwy : chartAt (Fin n → ℂ) x₀ y = w := (chartAt _ x₀).right_inv hw
  set e₀ := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀ with he₀
  have hb : y ∈ e₀.baseSet := hy
  have hσ : ∀ c, e₀.symmL ℝ y c = chartConstField x₀ c y := fun c =>
    Trivialization.symmL_apply _ hb c
  rw [← hwy]
  have hΓ : e₀.symmL ℝ y (chartChristoffel (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ)
      (ℙ ℂ (Ambient n))) x₀ (chartAt (Fin n → ℂ) x₀ y) v u)
      = leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)) (chartConstField x₀ v) y
          (chartConstField x₀ u y) := by
    rw [chartChristoffel_chartAt _ x₀ hy, e₀.symmL_continuousLinearMapAt hb, hσ, hσ,
      christoffel_chartConstField _ x₀ v hy]
  symm
  rw [fsChristoffel, (isInvertible_fsModelMetricCLM _).inverse_apply_eq]
  ext z
  rw [← fsMetric_symmL_symmL x₀ y hy, hΓ, hσ, fsKoszul_apply]
  rw [← inner_eq_fsMetric]
  rw [leviCivitaConnection_apply_inner 𝓘(ℝ, Fin n → ℂ)
    (mdifferentiableAt_chartConstField x₀ u hy) (mdifferentiableAt_chartConstField x₀ v hy)
    (mdifferentiableAt_chartConstField x₀ z hy)]
  beta_reduce
  rw [mlieBracket_chartConstField x₀ u z hy, mlieBracket_chartConstField x₀ v u hy,
    mlieBracket_chartConstField x₀ z v hy]
  erw [mfderiv_inner_chartConstField x₀ hy v z u, mfderiv_inner_chartConstField x₀ hy z u v,
    mfderiv_inner_chartConstField x₀ hy u v z]
  simp

/-- ★★ **The Levi-Civita Christoffel symbols of `ℂℙⁿ` are smooth on every affine chart.** -/
theorem contDiffOn_chartChristoffel_leviCivita (x₀ : ℙ ℂ (Ambient n)) :
    ContDiffOn ℝ ∞ (fun p : (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) =>
        chartChristoffel (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) x₀
          p.1 p.2.1 p.2.2)
      ((chartAt (Fin n → ℂ) x₀).target ×ˢ Set.univ) :=
  contDiff_fsChristoffel.contDiffOn.congr fun _ hp => chartChristoffel_leviCivita x₀ hp.1 _ _

/-- ★★★ **The Fubini–Study geodesic equation in an affine chart**: a curve in the source of the
chart at `x₀` is a geodesic of the Levi-Civita connection iff its chart coordinate `w` and some
`v` solve `(w', v') = fsGeodesicSpray (w, v) = (v, −Γ_w(v, v))`. -/
theorem isGeodesic_iff_fsGeodesicSpray (x₀ : ℙ ℂ (Ambient n)) {γ : ℝ → ℙ ℂ (Ambient n)}
    (hγ : ∀ t, γ t ∈ (chartAt (Fin n → ℂ) x₀).source) :
    IsGeodesic (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ ↔
      ∃ v : ℝ → Fin n → ℂ, ∀ t,
        HasDerivAt (fun s => (chartAt (Fin n → ℂ) x₀ (γ s), v s))
          (fsGeodesicSpray (chartAt (Fin n → ℂ) x₀ (γ t), v t)) t := by
  rw [isGeodesic_iff_chartSpray _ x₀ hγ]
  have h : ∀ t (v : Fin n → ℂ),
      chartSpray (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) x₀
        (chartAt (Fin n → ℂ) x₀ (γ t), v) = fsGeodesicSpray (chartAt (Fin n → ℂ) x₀ (γ t), v) :=
    fun t v => by
      simp only [chartSpray, fsGeodesicSpray]
      rw [chartChristoffel_leviCivita x₀ ((chartAt _ x₀).map_source (hγ t))]
  simp only [h]

/-- The affine charts of `ℂℙⁿ` are onto `ℂⁿ`. -/
theorem chartAt_target_eq_univ (x₀ : ℙ ℂ (Ambient n)) :
    (chartAt (Fin n → ℂ) x₀).target = Set.univ := rfl

/-- In every affine chart, the geodesic spray of the Levi-Civita connection is
`fsGeodesicSpray`. -/
theorem chartSpray_leviCivita (x₀ : ℙ ℂ (Ambient n)) :
    chartSpray (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) x₀ = fsGeodesicSpray := by
  funext p
  simp only [chartSpray, fsGeodesicSpray]
  rw [chartChristoffel_leviCivita x₀ (by rw [chartAt_target_eq_univ]; exact Set.mem_univ _)]

/-- ★★★ **The Fubini–Study geodesic equation on an open set of times**: a curve in the source of
the chart at `x₀` for `t ∈ I` (`I` open) is a geodesic on `I` iff its chart coordinate `w` and
some `v` solve `(w', v') = fsGeodesicSpray (w, v)` on `I`. -/
theorem isGeodesicOn_iff_fsGeodesicSpray (x₀ : ℙ ℂ (Ambient n)) {γ : ℝ → ℙ ℂ (Ambient n)}
    {I : Set ℝ} (hI : IsOpen I) (hγ : ∀ t ∈ I, γ t ∈ (chartAt (Fin n → ℂ) x₀).source) :
    IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ I ↔
      ∃ v : ℝ → Fin n → ℂ, ∀ t ∈ I,
        HasDerivAt (fun s => (chartAt (Fin n → ℂ) x₀ (γ s), v s))
          (fsGeodesicSpray (chartAt (Fin n → ℂ) x₀ (γ t), v t)) t := by
  rw [isGeodesicOn_iff_chartSpray _ x₀ hI hγ, chartSpray_leviCivita]

/-- ★★★ **Local existence of Fubini–Study geodesics**: through every point `x₀ ∈ ℂℙⁿ` with every
initial velocity `v₀ ∈ T_{x₀}ℂℙⁿ` there is a geodesic of the Levi-Civita connection on some
interval `(-ε, ε)` (Picard–Lindelöf on the smooth spray, in the chart at `x₀`). -/
theorem exists_isGeodesicOn_fs (x₀ : ℙ ℂ (Ambient n))
    (v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → ℙ ℂ (Ambient n), γ 0 = x₀ ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ) = v₀ ∧
      IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ
        (Set.Ioo (-ε) ε) := by
  set φ := chartAt (Fin n → ℂ) x₀ with hφ
  set e₀ := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀ with he₀
  set p₀ : (Fin n → ℂ) × (Fin n → ℂ) := (φ x₀, (e₀ ⟨x₀, v₀⟩).2) with hp₀
  have hC1 : ContDiffAt ℝ 1 (fsGeodesicSpray (n := n)) p₀ :=
    contDiff_fsGeodesicSpray.contDiffAt.of_le (by simp)
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hC1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hα
  set γ : ℝ → ℙ ℂ (Ambient n) := fun t => φ.symm (α t).1 with hγdef
  have htgt : ∀ t, (α t).1 ∈ φ.target := fun t => by
    rw [hφ, chartAt_target_eq_univ]; exact Set.mem_univ _
  have hsrc : ∀ t, γ t ∈ φ.source := fun t => φ.map_target (htgt t)
  have hw : ∀ t, φ (γ t) = (α t).1 := fun t => φ.right_inv (htgt t)
  have hfun : (fun s => (φ (γ s), (α s).2)) = α := funext fun s => by rw [hw s]
  have hgeo : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ
      (Set.Ioo (-ε) ε) := by
    rw [isGeodesicOn_iff_fsGeodesicSpray x₀ isOpen_Ioo fun t _ => hsrc t]
    refine ⟨fun t => (α t).2, fun t ht => ?_⟩
    rw [hfun, hw t]
    exact hα t ht
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hγ0 : γ 0 = x₀ := by
    show φ.symm (α 0).1 = x₀
    rw [hα0]
    exact φ.left_inv (mem_chart_source _ x₀)
  refine ⟨ε, hε, γ, hγ0, ?_, hgeo⟩
  -- the velocity at `0`, read in the chart at `x₀`
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 :=
    ((mdifferentiableAt_totalSpace _ _).1 (hgeo 0 h0mem).1).1
  have h1 := hasDerivAt_chartAt_comp x₀ (hsrc 0) hγd
  have h2 : HasDerivAt (fun s => φ (γ s)) (α 0).2 0 := by
    have := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt 0 (hα 0 h0mem)
    simp only [Function.comp_def, ContinuousLinearMap.coe_fst', fsGeodesicSpray] at this
    simpa only [hw] using this
  have hc : (e₀ ⟨γ 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ)⟩).2 = (e₀ ⟨x₀, v₀⟩).2 := by
    rw [h1.unique h2, hα0]
  have hb : γ 0 ∈ e₀.baseSet := hsrc 0
  rw [← e₀.symm_apply_apply_mk hb (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ)), hc, hγ0]
  exact e₀.symm_apply_apply_mk (mem_chart_source _ x₀) v₀

/-- ★★★ **Local uniqueness of Fubini–Study geodesics**: two geodesics on an open set of times
containing `t₀`, with the same position and velocity at `t₀`, agree near `t₀` (Picard–Lindelöf
uniqueness for the locally Lipschitz spray, in the chart at `γ₁ t₀`). -/
theorem eventuallyEq_of_isGeodesicOn_fs {γ₁ γ₂ : ℝ → ℙ ℂ (Ambient n)} {I : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (ht₀ : t₀ ∈ I)
    (h₁ : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ₁ I)
    (h₂ : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ₂ I)
    (hpos : γ₁ t₀ = γ₂ t₀)
    (hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t₀ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t₀ (1 : ℝ)) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  set x₀ := γ₁ t₀ with hx₀
  set φ := chartAt (Fin n → ℂ) x₀ with hφ
  set e₀ := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀ with he₀
  have hd₁ : ∀ t ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t := fun t ht =>
    ((mdifferentiableAt_totalSpace _ _).1 (h₁ t ht).1).1
  have hd₂ : ∀ t ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t := fun t ht =>
    ((mdifferentiableAt_totalSpace _ _).1 (h₂ t ht).1).1
  have hJ₁ : IsOpen (I ∩ γ₁ ⁻¹' φ.source) :=
    ContinuousOn.isOpen_inter_preimage (fun t ht => (hd₁ t ht).continuousAt.continuousWithinAt)
      hI φ.open_source
  have hJ₂ : IsOpen (I ∩ γ₂ ⁻¹' φ.source) :=
    ContinuousOn.isOpen_inter_preimage (fun t ht => (hd₂ t ht).continuousAt.continuousWithinAt)
      hI φ.open_source
  set J := (I ∩ γ₁ ⁻¹' φ.source) ∩ (I ∩ γ₂ ⁻¹' φ.source) with hJdef
  have hJ : IsOpen J := hJ₁.inter hJ₂
  have hsrc₀ : x₀ ∈ φ.source := mem_chart_source _ x₀
  have ht₀J : t₀ ∈ J := ⟨⟨ht₀, hsrc₀⟩, ⟨ht₀, by rw [Set.mem_preimage, ← hpos]; exact hsrc₀⟩⟩
  obtain ⟨v₁, hv₁⟩ := (isGeodesicOn_iff_fsGeodesicSpray x₀ hJ fun t ht => ht.1.2).1
    ((h₁.mono fun t ht => ht.1.1))
  obtain ⟨v₂, hv₂⟩ := (isGeodesicOn_iff_fsGeodesicSpray x₀ hJ fun t ht => ht.2.2).1
    ((h₂.mono fun t ht => ht.2.1))
  -- the two chart solutions start at the same point of `ℂⁿ × ℂⁿ`
  have hfst : ∀ (γ : ℝ → ℙ ℂ (Ambient n)) (v : ℝ → Fin n → ℂ),
      HasDerivAt (fun s => (φ (γ s), v s)) (fsGeodesicSpray (φ (γ t₀), v t₀)) t₀ →
      HasDerivAt (fun s => φ (γ s)) (v t₀) t₀ := fun γ v h => by
    have := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt t₀ h
    simpa [Function.comp_def, fsGeodesicSpray] using this
  have hv₁0 : v₁ t₀ = (e₀ ⟨γ₁ t₀, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t₀ (1 : ℝ)⟩).2 :=
    (hfst γ₁ v₁ (hv₁ t₀ ht₀J)).unique (hasDerivAt_chartAt_comp x₀ hsrc₀ (hd₁ t₀ ht₀))
  have hsrc₂ : γ₂ t₀ ∈ φ.source := ht₀J.2.2
  have hv₂0 : v₂ t₀ = (e₀ ⟨γ₂ t₀, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t₀ (1 : ℝ)⟩).2 :=
    (hfst γ₂ v₂ (hv₂ t₀ ht₀J)).unique (hasDerivAt_chartAt_comp x₀ hsrc₂ (hd₂ t₀ ht₀))
  have hinit : (φ (γ₁ t₀), v₁ t₀) = (φ (γ₂ t₀), v₂ t₀) := by
    rw [hv₁0, hv₂0, ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hsrc₀,
      ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hsrc₂, hvel]
    exact congrArg (fun y => (φ y, e₀.continuousLinearMapAt ℝ y
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t₀ (1 : ℝ) : Fin n → ℂ))) hpos
  -- the spray is Lipschitz near the common initial point
  set p₀ := (φ (γ₁ t₀), v₁ t₀) with hp₀
  obtain ⟨K, U, hU, hL⟩ :=
    (contDiff_fsGeodesicSpray.contDiffAt (x := p₀)).of_le (by simp) |>.exists_lipschitzOnWith
  have hev : ∀ (γ : ℝ → ℙ ℂ (Ambient n)) (v : ℝ → Fin n → ℂ),
      (∀ t ∈ J, HasDerivAt (fun s => (φ (γ s), v s)) (fsGeodesicSpray (φ (γ t), v t)) t) →
      (φ (γ t₀), v t₀) = p₀ →
      ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun s => (φ (γ s), v s))
        (fsGeodesicSpray (φ (γ t), v t)) t ∧ (φ (γ t), v t) ∈ U := fun γ v h h0 => by
    have hcont : ContinuousAt (fun s => (φ (γ s), v s)) t₀ := (h t₀ ht₀J).continuousAt
    have hU' : U ∈ 𝓝 ((fun s => (φ (γ s), v s)) t₀) := by
      show U ∈ 𝓝 (φ (γ t₀), v t₀)
      rw [h0]; exact hU
    filter_upwards [hJ.mem_nhds ht₀J, hcont.preimage_mem_nhds hU'] with t ht htU
    exact ⟨h t ht, htU⟩
  have heq := ODE_solution_unique_of_eventually (K := K) (s := fun _ => U)
    (v := fun _ => fsGeodesicSpray) (Eventually.of_forall fun _ => hL)
    (hev γ₁ v₁ hv₁ rfl) (hev γ₂ v₂ hv₂ hinit.symm) hinit
  filter_upwards [heq, hJ.mem_nhds ht₀J] with t h ht
  have h' := congrArg Prod.fst h
  simp only at h'
  rw [← φ.left_inv ht.1.2, ← φ.left_inv ht.2.2, h']

end Projectivization
