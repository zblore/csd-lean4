/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianLieDerivative
public import CsdLean4.Mathlib.Geometry.Manifold.IntegralCurve.FlowContinuity
public import CsdLean4.Mathlib.Geometry.Manifold.TopFormMeasure
public import CsdLean4.Mathlib.Geometry.Manifold.WedgeForm

/-!
# The Hamiltonian flow on a compact symplectic manifold preserves the symplectic volume

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Liouville)** — this module uses the *restricted* senses
of "Hamiltonian" and "Liouville"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Q29(d′) of
`specs/generator-layer-scoping.md`, the assembly of Q29(a)–(c′).

The pieces: the global flow `integralFlow` of a `C^1` field on a compact manifold with its group
law (`IntegralCurve/GlobalFlow.lean`), its joint continuity (`IntegralCurve/FlowContinuity.lean`),
the differentiable dependence of the local flow on the initial point with the flat Liouville
theorem (`Analysis/ODE/FlowDerivative.lean`: `ContDiffAt.exists_localFlow_form_invariant`), the
vanishing of the flat Lie derivative of a symplectic form's local representative along its local
Hamiltonian vector (`HamiltonianLieDerivative.lean`), and the change-of-variables theorem for the
measure of a top form (`TopFormMeasure.lean`: `topFormMeasure_map_eq`). This file assembles them.

* `chartField_eq_trivializationAt_snd`, `DifferentialForm.chartField_hamiltonianVectorField` —
  the chart field of `FlowContinuity.lean` is the trivialised section, and for the Hamiltonian
  vector field it is the local Hamiltonian vector on the chart's target;
* `ContinuousAlternatingMap.compContinuousLinearMap_comp`, ★
  `DifferentialForm.forall_chart_of_forall_exists_chart` — **from one chart to two**: if around
  every point *some* chart carries the differentiability and the pullback identity of a map `g`
  for a form family, then *every* pair of charts does (`localRep_transition` moves the pullback
  across the two chart transitions);
* ★ `DifferentialForm.exists_nhds_forall_integralFlow_localRep_eq` — **local invariance**: near
  every point, for `t ∈ [0, ε]`, the chart expression of the Hamiltonian flow is differentiable
  and pulls the local representative of the symplectic form back to itself. In the chart the
  flow is the Picard–Lindelöf local flow (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`),
  its derivative solves the variational equation, and the flat Liouville theorem applies;
* `integralFlowHomeomorph` — the time-`t` map as a homeomorphism (inverse: time `-t`);
  `map_integralFlow_eq_of_forall_Icc` — a measure invariant for all small non-negative times is
  invariant for all times (iterate the group law; `φ t ∘ φ (-t) = id`);
* ★ `DifferentialForm.exists_forall_map_integralFlow_topFormMeasure_wedgePow_eq` — **small-time
  invariance of the measure of every power `α^k`**: a finite subcover, the two-chart lemma with
  the naturality `wedgePow_compContinuousLinearMap` of the wedge power under pullback, and
  `topFormMeasure_map_eq`;
* `DifferentialForm.IsSymplectic.hamiltonianFlow` — **the Hamiltonian flow** of a smooth energy
  on a compact symplectic manifold;
* ★★★ `DifferentialForm.IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow` — **Liouville's
  theorem**: the Hamiltonian flow of every smooth `H` preserves the measure of every power of the
  symplectic form, at every time, for every Haar measure on the model, basis and chart cover.

The `ℂℙⁿ` instance (`fsVolume_map_hamiltonianFlow`) is in
`Instances/ProjectiveSpaceHamiltonianFlow.lean`.
-/

@[expose] public section

open Set Filter Topology Bundle Metric
open scoped ContDiff Manifold Bundle

/-! ### The chart field is the trivialised section -/

section ChartField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℝ E) 1 M]

/-- The chart field of `FlowContinuity.lean` is the second component of the tangent
trivialisation of the section, at the chart preimage. -/
theorem chartField_eq_trivializationAt_snd (v : (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x)
    (x₀ : M) (w : E) :
    chartField v x₀ w
      = (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀
          ⟨(chartAt E x₀).symm w, v ((chartAt E x₀).symm w)⟩).2 := by
  simp only [chartField, Function.comp_apply]
  rfl

end ChartField

/-! ### Two charts from one -/

section TwoCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Pullback along a composition is the composition of the pullbacks. -/
theorem ContinuousAlternatingMap.compContinuousLinearMap_comp {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E [⋀^ι]→L[ℝ] ℝ) (g : F →L[ℝ] E) (h : G →L[ℝ] F) :
    f.compContinuousLinearMap (g ∘L h) = (f.compContinuousLinearMap g).compContinuousLinearMap h := by
  ext m
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply]

namespace DifferentialForm

variable (s : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^ι]→L[ℝ] Bundle.Trivial M ℝ x)

/-- ★ **From one chart to two.** If around every point some chart carries the differentiability
and the pullback identity of `g` for `s`, then every pair of charts does: the chart expression in
the pair is the one-chart expression conjugated by two transitions, and `localRep_transition`
moves the pullback across each. -/
theorem forall_chart_of_forall_exists_chart (g : M → M) (hg : Continuous g)
    (hloc : ∀ p : M, ∃ y : M, p ∈ (chartAt E y).source ∧ g p ∈ (chartAt E y).source ∧
      DifferentiableAt ℝ (chartAt E y ∘ g ∘ (chartAt E y).symm) (chartAt E y p) ∧
      (localRep s y (chartAt E y (g p))).compContinuousLinearMap
        (fderiv ℝ (chartAt E y ∘ g ∘ (chartAt E y).symm) (chartAt E y p))
        = localRep s y (chartAt E y p)) :
    ∀ x₀ z : M, ∀ w ∈ (chartAt E x₀).target, g ((chartAt E x₀).symm w) ∈ (chartAt E z).source →
      DifferentiableAt ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w ∧
      (localRep s z ((chartAt E z ∘ g ∘ (chartAt E x₀).symm) w)).compContinuousLinearMap
        (fderiv ℝ (chartAt E z ∘ g ∘ (chartAt E x₀).symm) w) = localRep s x₀ w := by
  intro x₀ z w hw hz
  set p : M := (chartAt E x₀).symm w with hp
  obtain ⟨y, hpy, hgy, hΨ, hinv⟩ := hloc p
  -- the three pieces
  set τ₁ : E → E := chartAt E y ∘ (chartAt E x₀).symm with hτ₁
  set Ψ : E → E := chartAt E y ∘ g ∘ (chartAt E y).symm with hΨdef
  set τ₂ : E → E := chartAt E z ∘ (chartAt E y).symm with hτ₂
  have ha : τ₁ w = chartAt E y p := rfl
  have hb : Ψ (chartAt E y p) = chartAt E y (g p) := by
    simp only [Ψ, Function.comp_apply, (chartAt E y).left_inv hpy]
  have hby : chartAt E y (g p) ∈ (chartAt E y).target := (chartAt E y).map_source hgy
  have hbz : (chartAt E y).symm (chartAt E y (g p)) ∈ (chartAt E z).source := by
    rw [(chartAt E y).left_inv hgy]; exact hz
  have hτ₁d : DifferentiableAt ℝ τ₁ w :=
    (contDiffAt_chart_transition x₀ y hw hpy).differentiableAt (by simp)
  have hτ₂d : DifferentiableAt ℝ τ₂ (chartAt E y (g p)) :=
    (contDiffAt_chart_transition y z hby hbz).differentiableAt (by simp)
  -- the eventual identity of the chart expressions
  have hev : (chartAt E z ∘ g ∘ (chartAt E x₀).symm) =ᶠ[𝓝 w] τ₂ ∘ Ψ ∘ τ₁ := by
    have h1 : (chartAt E x₀).symm ⁻¹' (chartAt E y).source ∈ 𝓝 w :=
      ((chartAt E x₀).continuousAt_symm hw).preimage_mem_nhds
        ((chartAt E y).open_source.mem_nhds hpy)
    have h2 : (chartAt E x₀).symm ⁻¹' (g ⁻¹' (chartAt E y).source) ∈ 𝓝 w :=
      ((chartAt E x₀).continuousAt_symm hw).preimage_mem_nhds
        ((hg.continuousAt).preimage_mem_nhds ((chartAt E y).open_source.mem_nhds hgy))
    filter_upwards [h1, h2] with w' hw1 hw2
    simp only [Function.comp_apply, τ₂, Ψ, τ₁]
    rw [(chartAt E y).left_inv hw1, (chartAt E y).left_inv hw2]
  have hΨd : DifferentiableAt ℝ Ψ (τ₁ w) := by rw [ha]; exact hΨ
  have hτ₂d' : DifferentiableAt ℝ τ₂ (Ψ (τ₁ w)) := by rw [ha, hb]; exact hτ₂d
  have hcomp : DifferentiableAt ℝ (τ₂ ∘ Ψ ∘ τ₁) w := hτ₂d'.comp w (hΨd.comp w hτ₁d)
  refine ⟨hcomp.congr_of_eventuallyEq hev, ?_⟩
  rw [hev.fderiv_eq, hev.eq_of_nhds]
  rw [show τ₂ ∘ Ψ ∘ τ₁ = τ₂ ∘ (Ψ ∘ τ₁) from rfl, fderiv_comp w hτ₂d' (hΨd.comp w hτ₁d),
    fderiv_comp w hΨd hτ₁d, Function.comp_apply, Function.comp_apply, ha, hb,
    ContinuousAlternatingMap.compContinuousLinearMap_comp,
    ContinuousAlternatingMap.compContinuousLinearMap_comp]
  -- the outer transition
  have ht2 := localRep_transition s y z hby hbz
  rw [(chartAt E y).left_inv hgy] at ht2
  have hτ₂b : τ₂ (chartAt E y (g p)) = chartAt E z (g p) := by
    simp only [τ₂, Function.comp_apply, (chartAt E y).left_inv hgy]
  rw [hτ₂b, ← ht2, hinv]
  -- the inner transition
  exact (localRep_transition s x₀ y hw hpy).symm

end DifferentialForm

end TwoCharts

/-! ### The chart field of a Hamiltonian vector field, and the local invariance -/

section HamiltonianFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℝ E) ∞ M]

namespace DifferentialForm

variable (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) (H : M → ℝ)

/-- The chart field of the Hamiltonian vector field is the local Hamiltonian vector, on the
chart's target. -/
theorem chartField_hamiltonianVectorField
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) :
    chartField (hamiltonianVectorField (fun x => α x) hnd H) x₀ w
      = localHamiltonianVector α H x₀ w := by
  rw [chartField_eq_trivializationAt_snd,
    trivializationAt_hamiltonianVectorField_snd α H hnd hH x₀ ((chartAt E x₀).map_target hw),
    (chartAt E x₀).right_inv hw]

variable [CompactSpace M] [T2Space M]

/-- ★ **Local invariance of the symplectic form under the Hamiltonian flow, in a chart.** Near
every `y` there are an open neighbourhood `U` of `y` inside the chart's source and a time `ε > 0`
such that for `p ∈ U` and `t ∈ [0, ε]` the flow keeps `p` in the chart at `y`, its chart
expression is differentiable at `chartAt E y p`, and it pulls the local representative of `α`
back to itself: in the chart the flow is the Picard–Lindelöf local flow (uniqueness of integral
curves), whose derivative solves the variational equation, and the flat Liouville theorem applies
because the flat Lie derivative of the local representative along the local Hamiltonian vector
vanishes. -/
theorem exists_nhds_forall_integralFlow_localRep_eq (hα : IsSymplectic α)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (hv : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E).tangent 1
      (fun x => (⟨x, hα.hamiltonianVectorField H x⟩ : TangentBundle (modelWithCornersSelf ℝ E) M)))
    (y : M) :
    ∃ U ∈ 𝓝 y, IsOpen U ∧ U ⊆ (chartAt E y).source ∧ ∃ ε > (0 : ℝ), ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) ε,
      integralFlow hv t p ∈ (chartAt E y).source ∧
      DifferentiableAt ℝ (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm) (chartAt E y p) ∧
      (localRep (fun x => α x) y (chartAt E y (integralFlow hv t p))).compContinuousLinearMap
        (fderiv ℝ (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm) (chartAt E y p))
        = localRep (fun x => α x) y (chartAt E y p) := by
  have hx : (modelWithCornersSelf ℝ E).IsInteriorPoint y := BoundarylessManifold.isInteriorPoint
  have hv' := hv y
  rw [contMDiffAt_iff] at hv'
  obtain ⟨_, hv'⟩ := hv'
  have hf : ContDiffAt ℝ 1 (chartField (hα.hamiltonianVectorField H) y) (chartAt E y y) :=
    (hv'.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  have hyt : chartAt E y y ∈ (chartAt E y).target := mem_chart_target E y
  have hΩ : ContDiffAt ℝ 1 (localRep (fun x => α x) y) (chartAt E y y) :=
    (contDiffAt_localRep (fun x => α x) α.contMDiff_toFun y hyt).of_le (by simp)
  -- the flat Lie derivative vanishes near the base point: (c′), through the chart field
  have hL : ∀ᶠ z in 𝓝 (chartAt E y y), ∀ m,
      flatLieDeriv (chartField (hα.hamiltonianVectorField H) y) (localRep (fun x => α x) y) z m
        = 0 := by
    filter_upwards [(chartAt E y).open_target.mem_nhds hyt] with z hz m
    have hev : chartField (hα.hamiltonianVectorField H) y =ᶠ[𝓝 z]
        localHamiltonianVector α H y := by
      filter_upwards [(chartAt E y).open_target.mem_nhds hz] with z' hz'
      exact chartField_hamiltonianVectorField α H hα.nondegenerate hH y hz'
    rw [← flatLieDeriv_localHamiltonianVector_localRep_eq_zero α H hα hH y hz m]
    simp only [flatLieDeriv, hev.fderiv_eq, hev.eq_of_nhds]
  have hint : interior (extChartAt (modelWithCornersSelf ℝ E) y).target ∈ 𝓝 (chartAt E y y) :=
    isOpen_interior.mem_nhds ((modelWithCornersSelf ℝ E).isInteriorPoint_iff.mp hx)
  obtain ⟨r, hr, ε, hε, a, Y, ha, hY⟩ := hf.exists_localFlow_form_invariant hΩ hL hint
  set U : Set M := (chartAt E y).source ∩ chartAt E y ⁻¹' ball (chartAt E y y) r with hU
  have hUo : IsOpen U :=
    (chartAt E y).continuousOn.isOpen_inter_preimage (chartAt E y).open_source isOpen_ball
  have hUy : U ∈ 𝓝 y := hUo.mem_nhds ⟨mem_chart_source E y, mem_ball_self hr⟩
  refine ⟨U, hUy, hUo, fun p hp => hp.1, ε / 2, half_pos hε, ?_⟩
  have hmem : ∀ p ∈ U, chartAt E y p ∈ closedBall (chartAt E y y) r :=
    fun p hp => ball_subset_closedBall hp.2
  -- confinement to the chart target
  have htarget : ∀ p ∈ U, ∀ t, a (chartAt E y p) t ∈ (chartAt E y).target := by
    intro p hp t
    have h2 := interior_subset ((ha _ (hmem p hp)).2.2 t)
    rw [extChartAt_target] at h2
    simpa [mfld_simps] using h2
  -- identification with `integralFlow` on `Ioo (-ε) ε`
  have hflow : ∀ p ∈ U, ∀ t ∈ Ioo (-ε) ε,
      integralFlow hv t p = (chartAt E y).symm (a (chartAt E y p) t) := by
    intro p hp t ht
    have hcurve : IsMIntegralCurveOn ((chartAt E y).symm ∘ a (chartAt E y p))
        (hα.hamiltonianVectorField H) (Ioo (-ε) ε) :=
      isMIntegralCurveOn_extChartAt_symm_comp y
        (fun t ht => ((ha _ (hmem p hp)).2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2))
        (fun t => (ha _ (hmem p hp)).2.2 t)
    have hflowOn : IsMIntegralCurveOn (fun t => integralFlow hv t p)
        (hα.hamiltonianVectorField H) (Ioo (-ε) ε) :=
      (isMIntegralCurve_integralFlow hv p).isMIntegralCurveOn _
    have h0 : (fun t => integralFlow hv t p) 0 = ((chartAt E y).symm ∘ a (chartAt E y p)) 0 := by
      simp only [Function.comp_apply, integralFlow_zero, (ha _ (hmem p hp)).1]
      exact ((chartAt E y).left_inv hp.1).symm
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0) ⟨by linarith, hε⟩ hv
      hflowOn hcurve h0 ht
  intro p hp t ht
  have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
  have hpb : chartAt E y p ∈ ball (chartAt E y y) r := hp.2
  obtain ⟨hYd, hYinv⟩ := hY _ hpb t htε
  have hfl := hflow p hp t ht'
  have hat : a (chartAt E y p) t ∈ (chartAt E y).target := htarget p hp t
  have hchart : chartAt E y (integralFlow hv t p) = a (chartAt E y p) t := by
    rw [hfl, (chartAt E y).right_inv hat]
  -- the chart expression agrees with `a · t` near `chartAt E y p`
  have hev : (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm)
      =ᶠ[𝓝 (chartAt E y p)] (a · t) := by
    have hnb : (chartAt E y).target ∩ ball (chartAt E y y) r ∈ 𝓝 (chartAt E y p) :=
      ((chartAt E y).open_target.inter isOpen_ball).mem_nhds
        ⟨(chartAt E y).map_source hp.1, hpb⟩
    filter_upwards [hnb] with w hw
    have hwU : (chartAt E y).symm w ∈ U := by
      refine ⟨(chartAt E y).map_target hw.1, ?_⟩
      show chartAt E y ((chartAt E y).symm w) ∈ ball (chartAt E y y) r
      rw [(chartAt E y).right_inv hw.1]
      exact hw.2
    simp only [Function.comp_apply]
    rw [hflow _ hwU t ht', (chartAt E y).right_inv (htarget _ hwU t), (chartAt E y).right_inv hw.1]
  have hD : HasFDerivAt (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm)
      (Y (chartAt E y p) t) (chartAt E y p) :=
    hYd.congr_of_eventuallyEq hev
  refine ⟨?_, hD.differentiableAt, ?_⟩
  · rw [hfl]; exact (chartAt E y).map_target hat
  · rw [hD.fderiv, hchart]; exact hYinv

end DifferentialForm

end HamiltonianFlow

/-! ### The flow as a homeomorphism, and invariance for all times from small times -/

section FlowHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} [CompactSpace M] [T2Space M]
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))

/-- The flow at time `t` as a homeomorphism of `M` (inverse: the flow at time `-t`). -/
noncomputable def integralFlowHomeomorph (t : ℝ) : M ≃ₜ M where
  toFun := integralFlow hv t
  invFun := integralFlow hv (-t)
  left_inv x := by rw [← integralFlow_add, neg_add_cancel, integralFlow_zero]
  right_inv x := by rw [← integralFlow_add, add_neg_cancel, integralFlow_zero]
  continuous_toFun := continuous_integralFlow_point hv t
  continuous_invFun := continuous_integralFlow_point hv (-t)

@[simp]
theorem integralFlowHomeomorph_apply (t : ℝ) (x : M) :
    integralFlowHomeomorph hv t x = integralFlow hv t x := rfl

/-- A measure invariant under the flow for all small non-negative times is invariant for all
times: iterate the group law forward, and use `φ t ∘ φ (-t) = id` backward. -/
theorem map_integralFlow_eq_of_forall_Icc [MeasurableSpace M] [BorelSpace M]
    {μ : MeasureTheory.Measure M} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ t ∈ Icc (0 : ℝ) ε₀, MeasureTheory.Measure.map (integralFlow hv t) μ = μ) (t : ℝ) :
    MeasureTheory.Measure.map (integralFlow hv t) μ = μ := by
  have hmeas : ∀ s : ℝ, Measurable (integralFlow hv s) := fun s =>
    (continuous_integralFlow_point hv s).measurable
  have hiter : ∀ s ∈ Icc (0 : ℝ) ε₀, ∀ N : ℕ,
      MeasureTheory.Measure.map ((fun y => integralFlow hv s y)^[N]) μ = μ := by
    intro s hs N
    induction N with
    | zero => simp only [Function.iterate_zero, MeasureTheory.Measure.map_id]
    | succ N ih =>
      rw [Function.iterate_succ', ← MeasureTheory.Measure.map_map (hmeas s) ((hmeas s).iterate N),
        ih, h s hs]
  have hnonneg : ∀ t : ℝ, 0 ≤ t → MeasureTheory.Measure.map (integralFlow hv t) μ = μ := by
    intro t ht
    obtain ⟨N, hN⟩ : ∃ N : ℕ, t / ε₀ < N := exists_nat_gt _
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hsmall : t / N ∈ Icc (0 : ℝ) ε₀ := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hNpos]
      rw [div_lt_iff₀ hε₀] at hN
      linarith
    have heq : integralFlow hv t = (fun y => integralFlow hv (t / N) y)^[N] := by
      funext x
      rw [← integralFlow_nsmul]
      congr 1
      field_simp
    rw [heq]
    exact hiter _ hsmall N
  rcases le_or_gt 0 t with ht | ht
  · exact hnonneg t ht
  · have hneg := hnonneg (-t) (by linarith)
    have hid : integralFlow hv t ∘ integralFlow hv (-t) = id := by
      funext x
      simp only [Function.comp_apply, id]
      rw [← integralFlow_add, add_neg_cancel, integralFlow_zero]
    calc MeasureTheory.Measure.map (integralFlow hv t) μ
        = MeasureTheory.Measure.map (integralFlow hv t)
            (MeasureTheory.Measure.map (integralFlow hv (-t)) μ) := by rw [hneg]
      _ = MeasureTheory.Measure.map (integralFlow hv t ∘ integralFlow hv (-t)) μ :=
          MeasureTheory.Measure.map_map (hmeas t) (hmeas (-t))
      _ = μ := by rw [hid, MeasureTheory.Measure.map_id]

end FlowHomeomorph

/-! ### Assembly: the Hamiltonian flow preserves the measure of every power of the form -/

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [CompactSpace M] [T2Space M]

namespace DifferentialForm

omit [CompactSpace M] [T2Space M] in
/-- The Hamiltonian vector field of a symplectic form, as a `C^1` section of the tangent bundle in
the form `integralFlow` takes. -/
theorem IsSymplectic.contMDiff_hamiltonianVectorField_tangent
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    {H : M → ℝ} (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E).tangent 1
      (fun x => (⟨x, hβ.hamiltonianVectorField H x⟩ : TangentBundle (modelWithCornersSelf ℝ E) M)) :=
  (hβ.contMDiff_hamiltonianVectorField H hH).of_le (mod_cast le_top)

/-- **The Hamiltonian flow** of a smooth `H` on a compact symplectic manifold: the flow of its
Hamiltonian vector field. -/
noncomputable def IsSymplectic.hamiltonianFlow
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    {H : M → ℝ} (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (t : ℝ) (x : M) : M :=
  integralFlow (hβ.contMDiff_hamiltonianVectorField_tangent hH) t x

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
  (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) (H : M → ℝ)

/-- ★ **Small-time invariance of the top-power measure.** For a symplectic `α` and a smooth `H`,
there is `ε₀ > 0` such that for `t ∈ [0, ε₀]` the Hamiltonian flow at time `t` preserves the
measure of `α^k` (any `k`, any Haar `μ`, any basis, any chart cover): the local statement at
every point, a finite subcover, the two-chart lemma, and `topFormMeasure_map_eq`. -/
theorem exists_forall_map_integralFlow_topFormMeasure_wedgePow_eq (hα : IsSymplectic α)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (hv : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E).tangent 1
      (fun x => (⟨x, hα.hamiltonianVectorField H x⟩ : TangentBundle (modelWithCornersSelf ℝ E) M)))
    (k : ℕ) (e : Module.Basis (Fin (2 * k)) ℝ E) (c : ChartCover E M) :
    ∃ ε₀ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) ε₀,
      MeasureTheory.Measure.map (integralFlow hv t)
          (topFormMeasure μ e (fun x => wedgePow α k x) c)
        = topFormMeasure μ e (fun x => wedgePow α k x) c := by
  choose U hU hUo hUs ε hε hloc using exists_nhds_forall_integralFlow_localRep_eq α H hα hH hv
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  by_cases hne : s.Nonempty
  · set ε₀ : ℝ := s.inf' hne ε with hε₀
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀, Finset.lt_inf'_iff]
      exact fun y _ => hε y
    refine ⟨ε₀, hε₀pos, fun t ht => ?_⟩
    -- the one-chart statement at every point, for the top power
    have hloc' : ∀ p : M, ∃ y : M, p ∈ (chartAt E y).source ∧
        integralFlow hv t p ∈ (chartAt E y).source ∧
        DifferentiableAt ℝ (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm) (chartAt E y p) ∧
        (localRep (fun x => wedgePow α k x) y
            (chartAt E y (integralFlow hv t p))).compContinuousLinearMap
          (fderiv ℝ (chartAt E y ∘ integralFlow hv t ∘ (chartAt E y).symm) (chartAt E y p))
          = localRep (fun x => wedgePow α k x) y (chartAt E y p) := by
      intro p
      have hp : p ∈ ⋃ y₀ ∈ s, U y₀ := by rw [hs]; trivial
      obtain ⟨y₀, hy₀s, hpU⟩ := Set.mem_iUnion₂.mp hp
      have hle : ε₀ ≤ ε y₀ := Finset.inf'_le _ hy₀s
      obtain ⟨h1, h2, h3⟩ := hloc y₀ p hpU t ⟨ht.1, ht.2.trans hle⟩
      have hps : p ∈ (chartAt E y₀).source := hUs y₀ hpU
      refine ⟨y₀, hps, h1, h2, ?_⟩
      rw [localRep_wedgePow α y₀ ((chartAt E y₀).map_source h1) k,
        localRep_wedgePow α y₀ ((chartAt E y₀).map_source hps) k,
        ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, h3]
    have hall := forall_chart_of_forall_exists_chart (fun x => wedgePow α k x) (integralFlow hv t)
      (continuous_integralFlow_point hv t) hloc'
    exact topFormMeasure_map_eq μ e (fun x => wedgePow α k x) c (integralFlowHomeomorph hv t)
      (fun x₀ z w hw hz => (hall x₀ z w hw hz).1) (fun x₀ z w hw hz => (hall x₀ z w hw hz).2)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hempty : IsEmpty M := ⟨fun x => by
      have : x ∈ (⋃ y₀ ∈ (∅ : Finset M), U y₀) := by rw [hs]; trivial
      simp at this⟩
    exact ⟨1, one_pos, fun t _ => (MeasureTheory.Measure.eq_zero_of_isEmpty _).trans
      (MeasureTheory.Measure.eq_zero_of_isEmpty _).symm⟩

/-- ★★★ **Liouville's theorem on a compact symplectic manifold.** The Hamiltonian flow of every
smooth `H` preserves the measure of every power `β^k` of the symplectic form, at every time. -/
theorem IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    {H : M → ℝ} (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (k : ℕ) (e : Module.Basis (Fin (2 * k)) ℝ E) (c : ChartCover E M) (t : ℝ) :
    MeasureTheory.Measure.map (hβ.hamiltonianFlow hH t)
        (topFormMeasure μ e (fun x => wedgePow β k x) c)
      = topFormMeasure μ e (fun x => wedgePow β k x) c := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_forall_map_integralFlow_topFormMeasure_wedgePow_eq μ β H hβ hH
    (hβ.contMDiff_hamiltonianVectorField_tangent hH) k e c
  exact map_integralFlow_eq_of_forall_Icc _ hε₀ h t

end DifferentialForm

end Assembly
