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
BACKLOG #343–#347 (geometric QM: the local geodesic ODE of `ℂℙⁿ`, local existence and
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
  `ODE_solution_unique_of_eventually`, the spray being Lipschitz near the initial point);
* ★★★ `eqOn_of_isGeodesicOn_fs` — **uniqueness on a whole interval**: two geodesics on an open
  preconnected `I` with the same position and velocity at one `t₀ ∈ I` agree on all of `I`, across
  any number of charts (the agreement set is open, and closed in `I` by continuity of positions
  and of chart velocities);
* `isGeodesicOn_congr_fs` — being a geodesic on an open set depends only on the curve there;
  `IsFSGeodesicData x₀ v₀ I η` (a geodesic on an open preconnected `I ∋ 0` with initial data
  `(x₀, v₀)`), `IsFSGeodesicData.eqOn`;
* ★★★ `exists_maximal_isGeodesicOn_fs` — **maximal geodesics**: for every `(x₀, v₀)` there is a
  geodesic on an open interval `J ∋ 0` containing every other such interval, agreeing with every
  geodesic with the same initial data (`J` is the union of all of them, the curve glued from them
  by uniqueness);
* `isGeodesicOn_of_chartSolution` — a solution of the spray in any affine chart is a geodesic with
  the corresponding initial data; `fsModelMetricCLM_comm`;
* ★★ `fsMetric_velocity_eq_of_isGeodesicOn` — **constant speed**: `g(γ', γ')` is constant along a
  geodesic on an open preconnected set (`d/dt g_w(v, v) = Dg(v)(v, v) − 2 g_w(Γ_w(v, v), v) = 0`);
* `exists_uniform_fsGeodesicSpray`, ★★ `exists_uniform_isGeodesicOn_fs` — **a uniform existence
  time** for all initial data of speed `g(v, v) ≤ C` (compactness of `ℂℙⁿ`, coercivity of the
  metric, finitely many Picard–Lindelöf balls per chart);
* `eq_univ_of_maximal_fs` — the maximal interval is `ℝ` (escape argument); ★★★
  `exists_isGeodesic_fs` — **`ℂℙⁿ` is geodesically complete**: every initial datum `(x₀, v₀)` has a
  geodesic defined on all of `ℝ` (an `IsGeodesic`), agreeing with every geodesic with the same
  data on an open interval containing `0`.

## Honest scope

⚠️ **Completeness by the escape argument, not Hopf–Rinow.** Geodesics exist for all time; no
metric-space completeness, distance-minimisation or Hopf–Rinow statement is made, and the
exponential map `exp_x(v) = γ_{x,v}(1)` is not defined. `ε` is never estimated.

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
Mathlib's `Analysis/ODE/ExistUnique.lean`; `specs/BACKLOG.md` #338, #339, #343–#347;
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

/-- **A chart solution of the spray is a geodesic**: if `α` solves `α' = fsGeodesicSpray α` on an
open `I ∋ t₀`, starting at the chart data of `(x, v)` in the chart at `x₁`, then
`t ↦ φ⁻¹ (α t).1` is a geodesic on `I` through `x` with velocity `v` at `t₀`. -/
theorem isGeodesicOn_of_chartSolution (x₁ : ℙ ℂ (Ambient n)) {x : ℙ ℂ (Ambient n)}
    (hx : x ∈ (chartAt (Fin n → ℂ) x₁).source) (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x)
    {I : Set ℝ} (hI : IsOpen I) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    {α : ℝ → (Fin n → ℂ) × (Fin n → ℂ)}
    (hα0 : α t₀ = (chartAt (Fin n → ℂ) x₁ x,
      (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₁ ⟨x, v⟩).2))
    (hα : ∀ t ∈ I, HasDerivAt α (fsGeodesicSpray (α t)) t) :
    (chartAt (Fin n → ℂ) x₁).symm (α t₀).1 = x ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) (fun t => (chartAt (Fin n → ℂ) x₁).symm (α t).1) t₀
        (1 : ℝ) = v ∧
      IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)))
        (fun t => (chartAt (Fin n → ℂ) x₁).symm (α t).1) I := by
  set φ := chartAt (Fin n → ℂ) x₁ with hφ
  set e₁ := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₁ with he₁
  set γ : ℝ → ℙ ℂ (Ambient n) := fun t => φ.symm (α t).1 with hγdef
  have htgt : ∀ t, (α t).1 ∈ φ.target := fun t => by
    rw [hφ, chartAt_target_eq_univ]; exact Set.mem_univ _
  have hsrc : ∀ t, γ t ∈ φ.source := fun t => φ.map_target (htgt t)
  have hw : ∀ t, φ (γ t) = (α t).1 := fun t => φ.right_inv (htgt t)
  have hfun : (fun s => (φ (γ s), (α s).2)) = α := funext fun s => by rw [hw s]
  have hgeo : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ I := by
    rw [isGeodesicOn_iff_fsGeodesicSpray x₁ hI fun t _ => hsrc t]
    refine ⟨fun t => (α t).2, fun t ht => ?_⟩
    rw [hfun, hw t]
    exact hα t ht
  have hγ0 : γ t₀ = x := by
    show φ.symm (α t₀).1 = x
    rw [hα0]
    exact φ.left_inv hx
  refine ⟨hγ0, ?_, hgeo⟩
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₀ :=
    ((mdifferentiableAt_totalSpace _ _).1 (hgeo t₀ ht₀).1).1
  have h1 := hasDerivAt_chartAt_comp x₁ (hsrc t₀) hγd
  have h2 : HasDerivAt (fun s => φ (γ s)) (α t₀).2 t₀ := by
    have := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt t₀ (hα t₀ ht₀)
    simp only [Function.comp_def, ContinuousLinearMap.coe_fst', fsGeodesicSpray] at this
    simpa only [hw] using this
  have hc : (e₁ ⟨γ t₀, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₀ (1 : ℝ)⟩).2 = (e₁ ⟨x, v⟩).2 := by
    rw [h1.unique h2, hα0]
  have hb : γ t₀ ∈ e₁.baseSet := hsrc t₀
  show mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₀ (1 : ℝ) = v
  rw [← e₁.symm_apply_apply_mk hb (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₀ (1 : ℝ)), hc, hγ0]
  exact e₁.symm_apply_apply_mk hx v

/-- ★★★ **Local existence of Fubini–Study geodesics**: through every point `x₀ ∈ ℂℙⁿ` with every
initial velocity `v₀ ∈ T_{x₀}ℂℙⁿ` there is a geodesic of the Levi-Civita connection on some
interval `(-ε, ε)` (Picard–Lindelöf on the smooth spray, in the chart at `x₀`). -/
theorem exists_isGeodesicOn_fs (x₀ : ℙ ℂ (Ambient n))
    (v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → ℙ ℂ (Ambient n), γ 0 = x₀ ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ) = v₀ ∧
      IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ
        (Set.Ioo (-ε) ε) := by
  have hC1 : ContDiffAt ℝ 1 (fsGeodesicSpray (n := n))
      (chartAt (Fin n → ℂ) x₀ x₀,
        (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₀ ⟨x₀, v₀⟩).2) :=
    contDiff_fsGeodesicSpray.contDiffAt.of_le (by simp)
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hC1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hα
  obtain ⟨h1, h2, h3⟩ := isGeodesicOn_of_chartSolution x₀ (mem_chart_source _ x₀) v₀ isOpen_Ioo
    ⟨by linarith, hε⟩ hα0 hα
  exact ⟨ε, hε, _, h1, h2, h3⟩

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

/-- ★★★ **Uniqueness of Fubini–Study geodesics on a whole interval**: two geodesics on an open
preconnected set of times `I` (an open interval) with the same position and velocity at one
`t₀ ∈ I` agree on all of `I`. Local uniqueness spreads by connectedness: the set where they agree
near `t` is open, and closed in `I` because positions and chart velocities are continuous. -/
theorem eqOn_of_isGeodesicOn_fs {γ₁ γ₂ : ℝ → ℙ ℂ (Ambient n)} {I : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (ht₀ : t₀ ∈ I)
    (h₁ : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ₁ I)
    (h₂ : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ₂ I)
    (hpos : γ₁ t₀ = γ₂ t₀)
    (hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t₀ (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t₀ (1 : ℝ)) :
    Set.EqOn γ₁ γ₂ I := by
  set u : Set ℝ := {t | γ₁ =ᶠ[𝓝 t] γ₂} with hu
  have hUo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : I ⊆ u := by
    refine hIc.subset_of_closure_inter_subset hUo
      ⟨t₀, ht₀, eventuallyEq_of_isGeodesicOn_fs hI ht₀ h₁ h₂ hpos hvel⟩ ?_
    rintro t ⟨htc, ht⟩
    have hne : (𝓝[u] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htc
    have hd₁ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t :=
      ((mdifferentiableAt_totalSpace _ _).1 (h₁ t ht).1).1
    have hd₂ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t :=
      ((mdifferentiableAt_totalSpace _ _).1 (h₂ t ht).1).1
    -- positions agree at `t`
    have hpt : γ₁ t = γ₂ t := by
      have l₁ : Tendsto γ₁ (𝓝[u] t) (𝓝 (γ₁ t)) := hd₁.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
      have l₂ : Tendsto γ₁ (𝓝[u] t) (𝓝 (γ₂ t)) :=
        (hd₂.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall fun s hs => (hs.self_of_nhds).symm)
      exact tendsto_nhds_unique l₁ l₂
    -- chart velocities agree at `t`
    set x := γ₁ t with hx
    set e := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x with he
    have hs₁ : γ₁ t ∈ (chartAt (Fin n → ℂ) x).source := mem_chart_source _ x
    have hs₂ : γ₂ t ∈ (chartAt (Fin n → ℂ) x).source := by rw [← hpt]; exact hs₁
    set f₁ := fun s => (e ⟨γ₁ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ s (1 : ℝ)⟩).2 with hf₁
    set f₂ := fun s => (e ⟨γ₂ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ s (1 : ℝ)⟩).2 with hf₂
    have hc₁ : ContinuousAt f₁ t :=
      (differentiableAt_trivializationAt_comp x hs₁ (h₁ t ht).1).continuousAt
    have hc₂ : ContinuousAt f₂ t :=
      (differentiableAt_trivializationAt_comp x hs₂ (h₂ t ht).1).continuousAt
    have heqf : ∀ s ∈ u, f₁ s = f₂ s := fun s hs => by
      have hp : γ₁ s = γ₂ s := hs.self_of_nhds
      have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ s (1 : ℝ)
          = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ s (1 : ℝ) := by
        rw [hs.mfderiv_eq]
        rfl
      show (e ⟨γ₁ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ s (1 : ℝ)⟩).2
        = (e ⟨γ₂ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ s (1 : ℝ)⟩).2
      rw [hv]
      exact congrArg (fun y => (e ⟨y, (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ s (1 : ℝ) :
        Fin n → ℂ)⟩).2) hp
    have hft : f₁ t = f₂ t := by
      have l₁ : Tendsto f₁ (𝓝[u] t) (𝓝 (f₁ t)) := hc₁.tendsto.mono_left nhdsWithin_le_nhds
      have l₂ : Tendsto f₁ (𝓝[u] t) (𝓝 (f₂ t)) :=
        (hc₂.tendsto.mono_left nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall fun s hs => (heqf s hs).symm)
      exact tendsto_nhds_unique l₁ l₂
    have hvt : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t (1 : ℝ)
        = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t (1 : ℝ) := by
      rw [← e.symm_apply_apply_mk hs₁ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₁ t (1 : ℝ)),
        ← e.symm_apply_apply_mk hs₂ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ₂ t (1 : ℝ))]
      exact (congrArg (fun y => (e.symm y (f₁ t) : Fin n → ℂ)) hpt).trans
        (congrArg (fun z => (e.symm (γ₂ t) z : Fin n → ℂ)) hft)
    exact eventuallyEq_of_isGeodesicOn_fs hI ht h₁ h₂ hpt hvt
  exact fun t ht => (hsub ht).self_of_nhds

/-- **Being a geodesic is local in time**: a curve that agrees with a geodesic on an open set of
times is a geodesic there (read through the chart equation, so only `ℂⁿ`-valued data move). -/
theorem isGeodesicOn_congr_fs {γ η : ℝ → ℙ ℂ (Ambient n)} {I : Set ℝ} (hI : IsOpen I)
    (h : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) η I)
    (heq : Set.EqOn γ η I) :
    IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ I := by
  intro t ht
  set φ := chartAt (Fin n → ℂ) (η t) with hφ
  have hd : ∀ s ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) η s := fun s hs =>
    ((mdifferentiableAt_totalSpace _ _).1 (h s hs).1).1
  have hK : IsOpen (I ∩ η ⁻¹' φ.source) :=
    ContinuousOn.isOpen_inter_preimage (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      hI φ.open_source
  have htK : t ∈ I ∩ η ⁻¹' φ.source := ⟨ht, show η t ∈ φ.source from mem_chart_source _ (η t)⟩
  obtain ⟨v, hv⟩ := (isGeodesicOn_iff_fsGeodesicSpray (η t) hK fun s hs => hs.2).1
    (h.mono Set.inter_subset_left)
  have hγ : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ
      (I ∩ η ⁻¹' φ.source) := by
    rw [isGeodesicOn_iff_fsGeodesicSpray (η t) hK fun s hs => by
      rw [heq hs.1]; exact hs.2]
    refine ⟨v, fun s hs => ?_⟩
    have hev : (fun r => (φ (γ r), v r)) =ᶠ[𝓝 s] fun r => (φ (η r), v r) :=
      Filter.mem_of_superset (hI.mem_nhds hs.1) fun r hr => by
        simp only [Set.mem_ofPred_eq, heq hr]
    rw [heq hs.1]
    exact (hv s hs).congr_of_eventuallyEq hev
  exact hγ t htK

/-- `IsFSGeodesicData x₀ v₀ I η`: `η` is a Fubini–Study geodesic on the open interval-like set `I`
(open, preconnected, containing `0`) with `η 0 = x₀` and `η'(0) = v₀`. -/
def IsFSGeodesicData (x₀ : ℙ ℂ (Ambient n)) (v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀)
    (I : Set ℝ) (η : ℝ → ℙ ℂ (Ambient n)) : Prop :=
  IsOpen I ∧ IsPreconnected I ∧ (0 : ℝ) ∈ I ∧ η 0 = x₀ ∧
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) η 0 (1 : ℝ) = v₀ ∧
    IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) η I

/-- Two geodesics with the same initial data agree where both are defined. -/
theorem IsFSGeodesicData.eqOn {x₀ : ℙ ℂ (Ambient n)} {v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀}
    {I I' : Set ℝ} {η η' : ℝ → ℙ ℂ (Ambient n)} (h : IsFSGeodesicData x₀ v₀ I η)
    (h' : IsFSGeodesicData x₀ v₀ I' η') : Set.EqOn η η' (I ∩ I') := by
  obtain ⟨hI, hIc, h0, hp, hv, hg⟩ := h
  obtain ⟨hI', hIc', h0', hp', hv', hg'⟩ := h'
  have hc : IsPreconnected (I ∩ I') :=
    (hIc.ordConnected.inter hIc'.ordConnected).isPreconnected
  exact eqOn_of_isGeodesicOn_fs (hI.inter hI') hc ⟨h0, h0'⟩ (hg.mono Set.inter_subset_left)
    (hg'.mono Set.inter_subset_right) (hp.trans hp'.symm) (hv.trans hv'.symm)

/-- ★★★ **Maximal Fubini–Study geodesics**: for every `x₀ ∈ ℂℙⁿ` and `v₀ ∈ T_{x₀}ℂℙⁿ` there is a
geodesic `γ` with `γ 0 = x₀`, `γ'(0) = v₀` on an open interval `J ∋ 0` such that every geodesic
with the same initial data on an open interval `I ∋ 0` has `I ⊆ J` and agrees with `γ` on `I`. -/
theorem exists_maximal_isGeodesicOn_fs (x₀ : ℙ ℂ (Ambient n))
    (v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀) :
    ∃ J : Set ℝ, ∃ γ : ℝ → ℙ ℂ (Ambient n), IsFSGeodesicData x₀ v₀ J γ ∧
      ∀ I η, IsFSGeodesicData x₀ v₀ I η → I ⊆ J ∧ Set.EqOn η γ I := by
  classical
  set c : Set (Set ℝ) := {I | ∃ η, IsFSGeodesicData x₀ v₀ I η} with hc
  set J := ⋃₀ c with hJ
  set γ : ℝ → ℙ ℂ (Ambient n) := fun t =>
    if h : ∃ p : Set ℝ × (ℝ → ℙ ℂ (Ambient n)), IsFSGeodesicData x₀ v₀ p.1 p.2 ∧ t ∈ p.1
    then h.choose.2 t else x₀ with hγ
  -- `γ` agrees with every geodesic with these initial data
  have hagree : ∀ I η, IsFSGeodesicData x₀ v₀ I η → Set.EqOn γ η I := by
    intro I η h t ht
    have hex : ∃ p : Set ℝ × (ℝ → ℙ ℂ (Ambient n)), IsFSGeodesicData x₀ v₀ p.1 p.2 ∧ t ∈ p.1 :=
      ⟨(I, η), h, ht⟩
    simp only [hγ, hex, ↓reduceDIte]
    exact hex.choose_spec.1.eqOn h ⟨hex.choose_spec.2, ht⟩
  -- a geodesic through `x₀` with velocity `v₀` exists
  obtain ⟨ε, hε, γ₀, hγ₀0, hγ₀v, hγ₀⟩ := exists_isGeodesicOn_fs x₀ v₀
  have h₀ : IsFSGeodesicData x₀ v₀ (Set.Ioo (-ε) ε) γ₀ :=
    ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ₀0, hγ₀v, hγ₀⟩
  have hJo : IsOpen J := isOpen_sUnion fun I ⟨_, h⟩ => h.1
  have hJc : IsPreconnected J :=
    isPreconnected_sUnion 0 c (fun I ⟨_, h⟩ => h.2.2.1) fun I ⟨_, h⟩ => h.2.1
  have hJ0 : (0 : ℝ) ∈ J := ⟨_, ⟨γ₀, h₀⟩, h₀.2.2.1⟩
  have hgeo : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ J := by
    rintro t ⟨I, ⟨η, h⟩, ht⟩
    exact isGeodesicOn_congr_fs h.1 h.2.2.2.2.2 (hagree I η h) t ht
  have hev : γ =ᶠ[𝓝 0] γ₀ :=
    Filter.mem_of_superset (h₀.1.mem_nhds h₀.2.2.1) fun t ht => hagree _ _ h₀ ht
  have hγ0 : γ 0 = x₀ := (hagree _ _ h₀ h₀.2.2.1).trans hγ₀0
  have hγv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ) = v₀ := by
    rw [hev.mfderiv_eq]
    exact hγ₀v
  refine ⟨J, γ, ⟨hJo, hJc, hJ0, hγ0, hγv, hgeo⟩, fun I η h => ⟨?_, ?_⟩⟩
  · exact Set.subset_sUnion_of_mem ⟨η, h⟩
  · exact fun t ht => (hagree I η h ht).symm

/-! ### Geodesic completeness -/

/-- The model metric is symmetric. -/
theorem fsModelMetricCLM_comm (x₀ : ℙ ℂ (Ambient n)) {y : ℙ ℂ (Ambient n)}
    (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source) (a b : Fin n → ℂ) :
    fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y) a b
      = fsModelMetricCLM (chartAt (Fin n → ℂ) x₀ y) b a := by
  rw [← fsMetric_symmL_symmL x₀ y hy, ← fsMetric_symmL_symmL x₀ y hy]
  exact (fsForm_isAlmostKahler n).metric_comm y _ _

set_option synthInstance.maxHeartbeats 200000 in
/-- ★★ **The speed of a Fubini–Study geodesic is constant**: `g(γ', γ')` takes the same value at
any two times of an open preconnected set on which `γ` is a geodesic. In a chart,
`d/dt g_w(v, v) = Dg(v)(v, v) − 2 g_w(Γ_w(v, v), v) = 0` by the Koszul formula. -/
theorem fsMetric_velocity_eq_of_isGeodesicOn {γ : ℝ → ℙ ℂ (Ambient n)} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J)
    (h : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ J)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    fsMetric (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ s (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ s (1 : ℝ))
      = fsMetric (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t (1 : ℝ)) := by
  set f : ℝ → ℝ := fun r => fsMetric (γ r) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ r (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ r (1 : ℝ)) with hf
  have hd : ∀ r ∈ J, HasDerivAt f 0 r := by
    intro r hr
    set x₁ := γ r with hx₁
    set φ := chartAt (Fin n → ℂ) x₁ with hφ
    set e := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x₁ with he
    have hdγ : ∀ q ∈ J, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ q := fun q hq =>
      ((mdifferentiableAt_totalSpace _ _).1 (h q hq).1).1
    have hK : IsOpen (J ∩ γ ⁻¹' φ.source) :=
      ContinuousOn.isOpen_inter_preimage
        (fun q hq => (hdγ q hq).continuousAt.continuousWithinAt) hJ φ.open_source
    have hrK : r ∈ J ∩ γ ⁻¹' φ.source := ⟨hr, show γ r ∈ φ.source from mem_chart_source _ _⟩
    obtain ⟨v, hv⟩ := (isGeodesicOn_iff_fsGeodesicSpray x₁ hK fun q hq => hq.2).1
      (h.mono Set.inter_subset_left)
    have hfst : ∀ q ∈ J ∩ γ ⁻¹' φ.source, HasDerivAt (fun p => φ (γ p)) (v q) q := fun q hq => by
      have := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivAt q (hv q hq)
      simpa [Function.comp_def, fsGeodesicSpray] using this
    have hsnd : HasDerivAt v (-fsChristoffel (φ (γ r)) (v r) (v r)) r := by
      have := (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivAt r (hv r hrK)
      simpa [Function.comp_def, fsGeodesicSpray] using this
    have hvel : ∀ q ∈ J ∩ γ ⁻¹' φ.source,
        v q = (e ⟨γ q, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ q (1 : ℝ)⟩).2 := fun q hq =>
      (hfst q hq).unique (hasDerivAt_chartAt_comp x₁ hq.2 (hdγ q hq.1))
    -- in the chart, `f = g_w(v, v)`
    set F : ℝ → ℝ := fun q => fsModelMetricCLM (φ (γ q)) (v q) (v q) with hF
    have hev : f =ᶠ[𝓝 r] F := by
      filter_upwards [hK.mem_nhds hrK] with q hq
      have hb : γ q ∈ e.baseSet := hq.2
      have hσ : e.symmL ℝ (γ q) (v q) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ q (1 : ℝ) := by
        rw [hvel q hq, ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb]
        exact e.symmL_continuousLinearMapAt hb _
      show fsMetric (γ q) _ _ = _
      rw [← hσ]
      exact fsMetric_symmL_symmL x₁ (γ q) hq.2 (v q) (v q)
    have hw : HasDerivAt (fun q => φ (γ q)) (v r) r := hfst r hrK
    have hG : HasDerivAt (fun q => fsModelMetricCLM (φ (γ q)))
        (fderiv ℝ fsModelMetricCLM (φ (γ r)) (v r)) r :=
      (contDiff_fsModelMetricCLM.differentiable (by simp)).differentiableAt.hasFDerivAt
        |>.comp_hasDerivAt r hw
    have hFd := (hG.clm_apply hsnd).clm_apply hsnd
    -- the derivative vanishes
    set w := φ (γ r) with hwdef
    set Γ := fsChristoffel w (v r) (v r) with hΓ
    have hinv := isInvertible_fsModelMetricCLM w
    have hKΓ : fsKoszul w (v r) (v r) = fsModelMetricCLM w Γ :=
      hinv.inverse_apply_eq.1 rfl
    have hKv : fsModelMetricCLM w Γ (v r)
        = fderiv ℝ fsModelMetricCLM w (v r) (v r) (v r) / 2 := by
      rw [← hKΓ, fsKoszul_apply]
      ring
    have hcomm : fsModelMetricCLM w (v r) Γ = fsModelMetricCLM w Γ (v r) :=
      fsModelMetricCLM_comm x₁ (mem_chart_source _ x₁) (v r) Γ
    refine (hFd.congr_deriv ?_).congr_of_eventuallyEq hev
    simp only [map_neg, FunLike.coe_neg, Pi.neg_apply, FunLike.coe_add, Pi.add_apply]
    rw [hcomm, hKv]
    ring
  exact hJ.is_const_of_deriv_eq_zero hJc
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

/-- **Uniform existence time for the spray on a ball**: solutions of `α' = fsGeodesicSpray α`
from every initial point of `closedBall 0 R` exist on one common interval `(-ε, ε)`. -/
theorem exists_uniform_fsGeodesicSpray (R : ℝ) :
    ∃ ε > (0 : ℝ), ∀ p ∈ Metric.closedBall (0 : (Fin n → ℂ) × (Fin n → ℂ)) R,
      ∃ α : ℝ → (Fin n → ℂ) × (Fin n → ℂ), α 0 = p ∧
        ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (fsGeodesicSpray (α t)) t := by
  have hC1 : ∀ q, ContDiffAt ℝ 1 (fsGeodesicSpray (n := n)) q := fun q =>
    contDiff_fsGeodesicSpray.contDiffAt.of_le (by simp)
  have hloc := fun q : (Fin n → ℂ) × (Fin n → ℂ) =>
    (hC1 q).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (0 : ℝ)
  choose r hr ε hε H using hloc
  obtain ⟨T, -, hcover⟩ :=
    (isCompact_closedBall (0 : (Fin n → ℂ) × (Fin n → ℂ)) R).elim_nhds_subcover
      (fun q => Metric.ball q (r q)) fun q _ => Metric.ball_mem_nhds q (hr q)
  by_cases hT : T.Nonempty
  · refine ⟨T.inf' hT ε, (Finset.lt_inf'_iff hT).2 fun i _ => hε i, fun p hp => ?_⟩
    obtain ⟨q, hqT, hpq⟩ := Set.mem_iUnion₂.1 (hcover hp)
    obtain ⟨α, hα0, hα⟩ := H q p (Metric.ball_subset_closedBall hpq)
    refine ⟨α, hα0, fun t ht => hα t ?_⟩
    have hle : T.inf' hT ε ≤ ε q := Finset.inf'_le ε hqT
    simp only [zero_sub, zero_add, Set.mem_Ioo] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  · refine ⟨1, one_pos, fun p hp => ?_⟩
    obtain ⟨q, hqT, -⟩ := Set.mem_iUnion₂.1 (hcover hp)
    exact absurd ⟨q, hqT⟩ hT

/-- ★★ **Uniform existence time for Fubini–Study geodesics of bounded speed**: there is `ε > 0`
such that for every `t₀`, every `x ∈ ℂℙⁿ` and every `v ∈ T_xℂℙⁿ` with `g(v, v) ≤ C` there is a
geodesic on `(t₀ − ε, t₀ + ε)` with `γ t₀ = x`, `γ'(t₀) = v` (compactness of `ℂℙⁿ`, coercivity
of the metric, finitely many Picard–Lindelöf balls in each chart). -/
theorem exists_uniform_isGeodesicOn_fs (C : ℝ) :
    ∃ ε > (0 : ℝ), ∀ (t₀ : ℝ) (x : ℙ ℂ (Ambient n)) (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      fsMetric x v v ≤ C → ∃ η : ℝ → ℙ ℂ (Ambient n), η t₀ = x ∧
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) η t₀ (1 : ℝ) = v ∧
        IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) η
          (Set.Ioo (t₀ - ε) (t₀ + ε)) := by
  -- the neighbourhood of `y` where the chart coordinate stays within `‖φ_y y‖ + 1`
  set U : ℙ ℂ (Ambient n) → Set (ℙ ℂ (Ambient n)) := fun y =>
    (chartAt (Fin n → ℂ) y).source ∩
      chartAt (Fin n → ℂ) y ⁻¹' Metric.ball 0 (‖chartAt (Fin n → ℂ) y y‖ + 1) with hU
  have hUn : ∀ y, U y ∈ 𝓝 y := fun y =>
    ((chartAt (Fin n → ℂ) y).continuousOn.isOpen_inter_preimage
      (chartAt (Fin n → ℂ) y).open_source Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source _ y, by simp⟩
  -- the coercivity bound on chart velocities
  set M := ‖(toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n))‖ with hM
  set B : ℝ → ℝ := fun ρ => (|C| + 1) * (1 + (M * ρ) ^ 2) with hB
  have hcoer : ∀ (y x : ℙ ℂ (Ambient n)) (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x),
      x ∈ U y → fsMetric x v v ≤ C →
      ‖(trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) y ⟨x, v⟩).2‖
        ≤ B (‖chartAt (Fin n → ℂ) y y‖ + 1) := by
    intro y x v hx hC
    set e := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) y
    set u := (e ⟨x, v⟩).2 with hu
    set w := chartAt (Fin n → ℂ) y x with hw
    set ρ := ‖chartAt (Fin n → ℂ) y y‖ + 1 with hρ
    have hb : x ∈ e.baseSet := hx.1
    have hmet : fsModelMetric w u u = fsMetric x v v := by
      rw [← fsModelMetricCLM_apply, ← fsMetric_symmL_symmL y x hx.1,
        Trivialization.symmL_apply _ hb, e.symm_apply_apply_mk hb]
    have hge := fsModelMetric_self_ge w u
    have hwρ : ‖w‖ ≤ ρ := (mem_ball_zero_iff.1 hx.2).le
    have hρ0 : 0 ≤ ρ := by positivity
    have hLw : ‖toLpCLM w‖ ≤ M * ρ :=
      (toLpCLM.le_opNorm w).trans (mul_le_mul_of_nonneg_left hwρ (norm_nonneg _))
    have hM0 : 0 ≤ M * ρ := mul_nonneg (norm_nonneg _) hρ0
    have hN : (1 + ‖toLpCLM w‖ ^ 2) ^ 2 ≤ (1 + (M * ρ) ^ 2) ^ 2 := by
      have : ‖toLpCLM w‖ ^ 2 ≤ (M * ρ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hLw 2
      have h1 : 0 ≤ 1 + ‖toLpCLM w‖ ^ 2 := by positivity
      exact pow_le_pow_left₀ h1 (by linarith) 2
    have hN0 : (0 : ℝ) < (1 + ‖toLpCLM w‖ ^ 2) ^ 2 := by positivity
    have h4 : 4 * ‖toLpCLM u‖ ^ 2 ≤ C * (1 + (M * ρ) ^ 2) ^ 2 := by
      have := (div_le_iff₀ hN0).1 (hge.trans (hmet.trans_le hC))
      have hC0 : 0 ≤ C := le_trans (by positivity) (hge.trans (hmet.trans_le hC))
      nlinarith
    have hu2 : ‖u‖ ^ 2 ≤ B ρ ^ 2 := by
      have hlp : ‖u‖ ^ 2 ≤ ‖toLpCLM u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_le_norm_toLpCLM u) 2
      have hC4 : ‖toLpCLM u‖ ^ 2 ≤ |C| * (1 + (M * ρ) ^ 2) ^ 2 := by
        nlinarith [le_abs_self C, sq_nonneg (1 + (M * ρ) ^ 2), sq_nonneg ‖toLpCLM u‖]
      have hCB : |C| * (1 + (M * ρ) ^ 2) ^ 2 ≤ ((|C| + 1) * (1 + (M * ρ) ^ 2)) ^ 2 := by
        nlinarith [abs_nonneg C, sq_nonneg (1 + (M * ρ) ^ 2)]
      show ‖u‖ ^ 2 ≤ ((|C| + 1) * (1 + (M * ρ) ^ 2)) ^ 2
      linarith
    have hB0 : 0 ≤ B ρ := by simp only [hB]; positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 hu2
  -- finitely many charts cover `ℂℙⁿ`
  obtain ⟨Y, -, hY⟩ := (isCompact_univ (X := ℙ ℂ (Ambient n))).elim_nhds_subcover U
    fun y _ => hUn y
  have hrad := fun y : ℙ ℂ (Ambient n) =>
    exists_uniform_fsGeodesicSpray (n := n)
      (max (‖chartAt (Fin n → ℂ) y y‖ + 1) (B (‖chartAt (Fin n → ℂ) y y‖ + 1)))
  choose ε hε H using hrad
  by_cases hYn : Y.Nonempty
  · refine ⟨Y.inf' hYn ε, (Finset.lt_inf'_iff hYn).2 fun i _ => hε i, ?_⟩
    intro t₀ x v hC
    obtain ⟨y, hyY, hxy⟩ := Set.mem_iUnion₂.1 (hY (Set.mem_univ x))
    set e := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) y
    set p : (Fin n → ℂ) × (Fin n → ℂ) := (chartAt (Fin n → ℂ) y x, (e ⟨x, v⟩).2) with hp
    have hpR : p ∈ Metric.closedBall (0 : (Fin n → ℂ) × (Fin n → ℂ))
        (max (‖chartAt (Fin n → ℂ) y y‖ + 1) (B (‖chartAt (Fin n → ℂ) y y‖ + 1))) := by
      rw [mem_closedBall_zero_iff, norm_prod_le_iff]
      exact ⟨(le_max_left _ _).trans' (mem_ball_zero_iff.1 hxy.2).le,
        (le_max_right _ _).trans' (hcoer y x v hxy hC)⟩
    obtain ⟨β, hβ0, hβ⟩ := H y p hpR
    have hle : Y.inf' hYn ε ≤ ε y := Finset.inf'_le ε hyY
    have hα : ∀ t ∈ Set.Ioo (t₀ - Y.inf' hYn ε) (t₀ + Y.inf' hYn ε),
        HasDerivAt (fun s => β (s - t₀)) (fsGeodesicSpray ((fun s => β (s - t₀)) t)) t := by
      intro t ht
      have ht' : t - t₀ ∈ Set.Ioo (-ε y) (ε y) := by
        simp only [Set.mem_Ioo] at ht ⊢
        constructor <;> linarith [ht.1, ht.2]
      exact (hβ (t - t₀) ht').comp_sub_const t t₀
    have ht₀ : t₀ ∈ Set.Ioo (t₀ - Y.inf' hYn ε) (t₀ + Y.inf' hYn ε) := by
      have := (Finset.lt_inf'_iff hYn).2 fun i _ => hε i
      constructor <;> linarith
    obtain ⟨h1, h2, h3⟩ := isGeodesicOn_of_chartSolution y hxy.1 v isOpen_Ioo ht₀
      (α := fun s => β (s - t₀)) (by show β (t₀ - t₀) = _; rw [sub_self, hβ0]) hα
    exact ⟨_, h1, h2, h3⟩
  · refine ⟨1, one_pos, fun t₀ x v _ => ?_⟩
    obtain ⟨y, hyY, -⟩ := Set.mem_iUnion₂.1 (hY (Set.mem_univ x))
    exact absurd ⟨y, hyY⟩ hYn

/-- **The maximal interval is all of `ℝ`**: a maximal Fubini–Study geodesic (every geodesic with
the same initial data lives inside its interval) is defined for all time. -/
theorem eq_univ_of_maximal_fs {x₀ : ℙ ℂ (Ambient n)} {v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀}
    {J : Set ℝ} {γ : ℝ → ℙ ℂ (Ambient n)} (hγ : IsFSGeodesicData x₀ v₀ J γ)
    (hmax : ∀ I η, IsFSGeodesicData x₀ v₀ I η → I ⊆ J) : J = Set.univ := by
  classical
  obtain ⟨hJ, hJc, hJ0, hγ0, hγv, hgeo⟩ := hγ
  set c := fsMetric x₀ v₀ v₀ with hc
  obtain ⟨ε, hε, H⟩ := exists_uniform_isGeodesicOn_fs (n := n) c
  -- every point of `J` carries an `ε`-neighbourhood inside `J`
  have hstep : ∀ t₁ ∈ J, Set.Ioo (t₁ - ε) (t₁ + ε) ⊆ J := by
    intro t₁ ht₁
    have hspeed : fsMetric (γ t₁) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₁ (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ t₁ (1 : ℝ)) ≤ c := by
      rw [fsMetric_velocity_eq_of_isGeodesicOn hJ hJc hgeo ht₁ hJ0, hc]
      rw [hγ0] at hγv ⊢
      rw [hγv]
    obtain ⟨η, hη0, hηv, hη⟩ := H t₁ (γ t₁) _ hspeed
    set I' := Set.Ioo (t₁ - ε) (t₁ + ε) with hI'
    have ht₁I' : t₁ ∈ I' := ⟨by linarith, by linarith⟩
    -- `γ` and `η` agree on `J ∩ I'`
    have hagree : Set.EqOn γ η (J ∩ I') :=
      eqOn_of_isGeodesicOn_fs (hJ.inter isOpen_Ioo)
        (hJc.ordConnected.inter (Set.ordConnected_Ioo)).isPreconnected ⟨ht₁, ht₁I'⟩
        (hgeo.mono Set.inter_subset_left) (hη.mono Set.inter_subset_right) hη0.symm hηv.symm
    set ζ : ℝ → ℙ ℂ (Ambient n) := fun t => if t ∈ J then γ t else η t with hζ
    have hζJ : Set.EqOn ζ γ J := fun t ht => by simp [hζ, ht]
    have hζI : Set.EqOn ζ η I' := fun t ht => by
      by_cases htJ : t ∈ J
      · simp [hζ, htJ, hagree ⟨htJ, ht⟩]
      · simp [hζ, htJ]
    have hζgeo : IsGeodesicOn (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) ζ
        (J ∪ I') := by
      rintro t (htJ | htI)
      · exact isGeodesicOn_congr_fs hJ hgeo hζJ t htJ
      · exact isGeodesicOn_congr_fs isOpen_Ioo hη hζI t htI
    have hev : ζ =ᶠ[𝓝 0] γ := Filter.mem_of_superset (hJ.mem_nhds hJ0) fun t ht => hζJ ht
    have hdata : IsFSGeodesicData x₀ v₀ (J ∪ I') ζ := by
      refine ⟨hJ.union isOpen_Ioo, IsPreconnected.union t₁ ht₁ ht₁I' hJc isPreconnected_Ioo,
        Or.inl hJ0, (hζJ hJ0).trans hγ0, ?_, hζgeo⟩
      rw [hev.mfderiv_eq]
      exact hγv
    exact fun t ht => hmax _ _ hdata (Or.inr ht)
  -- hence `J` contains `± k ε / 2` for every `k`, and is an interval
  have hpos : ∀ k : ℕ, (k : ℝ) * (ε / 2) ∈ J ∧ -((k : ℝ) * (ε / 2)) ∈ J := by
    intro k
    induction k with
    | zero => simpa using hJ0
    | succ k ih =>
      refine ⟨hstep _ ih.1 ⟨?_, ?_⟩, hstep _ ih.2 ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith
  refine Set.eq_univ_of_forall fun s => ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (|s| / (ε / 2))
  have hk' : |s| < k * (ε / 2) := by
    rwa [div_lt_iff₀ (by positivity)] at hk
  exact hJc.ordConnected.out (hpos k).2 (hpos k).1
    ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩

/-- ★★★ **`ℂℙⁿ` with the Fubini–Study metric is geodesically complete**: for every `x₀ ∈ ℂℙⁿ` and
`v₀ ∈ T_{x₀}ℂℙⁿ` there is a geodesic `γ : ℝ → ℂℙⁿ` (an `IsGeodesic`, defined for all time)
with `γ 0 = x₀` and `γ'(0) = v₀`, and every geodesic with these initial data on an open interval
containing `0` agrees with it there. -/
theorem exists_isGeodesic_fs (x₀ : ℙ ℂ (Ambient n)) (v₀ : TangentSpace 𝓘(ℝ, Fin n → ℂ) x₀) :
    ∃ γ : ℝ → ℙ ℂ (Ambient n), γ 0 = x₀ ∧ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) γ 0 (1 : ℝ) = v₀ ∧
      IsGeodesic (leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))) γ ∧
      ∀ I η, IsFSGeodesicData x₀ v₀ I η → Set.EqOn η γ I := by
  obtain ⟨J, γ, hγ, hmax⟩ := exists_maximal_isGeodesicOn_fs x₀ v₀
  have hJ : J = Set.univ := eq_univ_of_maximal_fs hγ fun I η h => (hmax I η h).1
  obtain ⟨-, -, -, hγ0, hγv, hgeo⟩ := hγ
  rw [hJ, isGeodesicOn_univ] at hgeo
  exact ⟨γ, hγ0, hγv, hgeo, fun I η h => (hmax I η h).2⟩

end Projectivization
