/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.IntegralCurve.GlobalFlow

/-!
# The flow of a `C^1` vector field on a compact manifold is jointly continuous

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Q29(a′) of
`specs/generator-layer-scoping.md`.

`GlobalFlow.lean` built `integralFlow` (the flow of a `C^1` field on a compact boundaryless
manifold) with its group law and continuity in time. This file proves it is **jointly continuous**
in `(t, x)`:

* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem` —
  Mathlib's Picard–Lindelöf local flow with Lipschitz dependence on the initial point
  (`exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`), with the confinement of every
  solution to `closedBall x₀ a` made explicit;
* ★ `ContDiffAt.exists_localFlow` — a `C^1` field has a local flow near `x₀`, **jointly continuous**
  on `Icc (-ε) ε ×ˢ closedBall x₀ r` (Lipschitz in the initial point, uniformly in time, plus
  continuity in time: `continuousOn_prod_of_continuousOn_lipschitzOnWith'`), confined to a
  prescribed neighbourhood;
* `chartField`, `isMIntegralCurveOn_extChartAt_symm_comp` — the chart-to-manifold transport of a
  confined chart solution, factored out of `exists_nhds_forall_exists_isMIntegralCurveOn_Ioo`;
* ★ `exists_nhds_continuousOn_integralFlow` — **local joint continuity**: near every point, for
  `|t| < ε`, the flow is the transported chart flow (uniqueness of integral curves on an open
  interval, `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`), hence continuous;
* `exists_forall_continuous_integralFlow_of_abs_lt`, `integralFlow_nsmul`,
  ★ `continuous_integralFlow_point` — continuity in the initial point at every time, by a uniform
  small time (compactness) and iteration of the group law;
* ★★ `continuous_integralFlow` — **joint continuity**, from the group law
  `φ t x = φ (t − t₀) (φ t₀ x)` and the local statement at `(0, φ t₀ x₀)`.

What is not here: differentiable dependence on the initial point (the variational equation), which
Mathlib lacks and which Q29(b′) needs.
-/

@[expose] public section

open Set Metric Filter Topology Manifold ContDiff
open scoped NNReal


/-! ### Flat: Picard–Lindelöf with Lipschitz dependence on the initial point and confinement -/

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mathlib's `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` with the
confinement of every solution to `closedBall x₀ a` made explicit. -/
theorem IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      ∀ t, α x t ∈ closedBall x₀ a) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r) := ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_, fun t => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, ODE.FunSpace.compProj_apply]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx]
    exact α x hx |>.compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨L', h⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply, ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- ★ **A `C^1` field has a local flow near `x₀`, jointly continuous, confined to a prescribed
neighbourhood.** -/
theorem ContDiffAt.exists_localFlow {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) {s : Set E}
    (hs : s ∈ 𝓝 x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r, α x 0 = x ∧ (∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (f (α x t)) t)
        ∧ ∀ t, α x t ∈ s)
      ∧ ContinuousOn (fun p : ℝ × E => α p.2 p.1) (Icc (-ε) ε ×ˢ closedBall x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, has, hpl⟩ := hf.isPicardLindelof_subset hs
  obtain ⟨α, hα, L', hL'⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem
  refine ⟨r, hr, ε, hε, α, fun x hx ↦ ⟨(hα x hx).1, fun t ht ↦ ?_, fun t => has ((hα x hx).2.2 t)⟩, ?_⟩
  · have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa using ht
    exact (hα x hx).2.1 t (Ioo_subset_Icc_self ht') |>.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
  · have hI : Icc (-ε) ε = Icc (0 - ε) (0 + ε) := by simp
    rw [hI]
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith' (fun p : ℝ × E => α p.2 p.1) L'
      (fun t ht => hL' t ht) fun x hx => ?_
    exact fun t ht => ((hα x hx).2.1 t ht).continuousWithinAt

end Flat

/-! ### Manifold: joint continuity of the flow -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- The vector field read in the chart at `x₀`: the second component of the tangent-bundle chart
of the section. -/
noncomputable def chartField (v : (x : M) → TangentSpace I x) (x₀ : M) : E → E :=
  fun w => ((extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M) ∘
    (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∘ (extChartAt I x₀).symm) w).2

omit [CompleteSpace E] [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency false in
/-- A chart solution confined to the interior of the chart target transports to an integral curve
on the manifold (the transport step of `exists_nhds_forall_exists_isMIntegralCurveOn_Ioo`,
factored out). -/
theorem isMIntegralCurveOn_extChartAt_symm_comp (x₀ : M) {f : ℝ → E} {ε : ℝ}
    (hf2 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt f (chartField v x₀ (f t)) t)
    (hf3 : ∀ t, f t ∈ interior (extChartAt I x₀).target) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) v (Ioo (-ε) ε) := by
  intro t ht
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have h : HasDerivAt f (x := t) <| fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := hf2 t ht
  rw [← tangentCoordChange_def] at h
  have hf3t := hf3 t
  have hf3' := mem_of_mem_of_subset hf3t interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3t⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

variable [CompactSpace M] [T2Space M]
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))

/-- ★ **Local joint continuity of the flow.** Near every `x₀` there are an open neighbourhood `U`
and an `ε > 0` on which `(t, x) ↦ integralFlow t x` is continuous, for `|t| < ε`: in the chart
the flow is the Picard–Lindelöf local flow, jointly continuous by Lipschitz dependence on the
initial point, and uniqueness of integral curves identifies it with `integralFlow`. -/
theorem exists_nhds_continuousOn_integralFlow (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, IsOpen U ∧ ∃ ε > (0 : ℝ),
      ContinuousOn (fun p : ℝ × M => integralFlow hv p.1 p.2) (Ioo (-ε) ε ×ˢ U) := by
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hv' := hv x₀
  rw [contMDiffAt_iff] at hv'
  obtain ⟨_, hv'⟩ := hv'
  have hf : ContDiffAt ℝ 1
      (fun w => (extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M) ∘
        (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∘ (extChartAt I x₀).symm) w)
      (extChartAt I x₀ x₀) :=
    hv'.contDiffAt (range_mem_nhds_isInteriorPoint hx)
  have hint : interior (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx)
  obtain ⟨r, hr, ε, hε, α, hα, hαc⟩ := hf.snd.exists_localFlow hint
  set φ := extChartAt I x₀ with hφ
  set U : Set M := φ.source ∩ φ ⁻¹' ball (φ x₀) r with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) isOpen_ball
  have hUx : U ∈ 𝓝 x₀ :=
    hUo.mem_nhds ⟨mem_extChartAt_source x₀, mem_ball_self hr⟩
  refine ⟨U, hUx, hUo, ε, hε, ?_⟩
  -- on `Ioo (-ε) ε ×ˢ U` the flow is the transported chart flow
  have hmem : ∀ y ∈ U, φ y ∈ closedBall (φ x₀) r := fun y hy => ball_subset_closedBall hy.2
  have hflow : ∀ y ∈ U, ∀ t ∈ Ioo (-ε) ε, integralFlow hv t y = φ.symm (α (φ y) t) := by
    intro y hy t ht
    have hcurve : IsMIntegralCurveOn (φ.symm ∘ α (φ y)) v (Ioo (-ε) ε) :=
      isMIntegralCurveOn_extChartAt_symm_comp x₀ (fun t ht => (hα _ (hmem y hy)).2.1 t ht)
        (fun t => (hα _ (hmem y hy)).2.2 t)
    have hflowOn : IsMIntegralCurveOn (fun t => integralFlow hv t y) v (Ioo (-ε) ε) :=
      (isMIntegralCurve_integralFlow hv y).isMIntegralCurveOn _
    have h0 : (fun t => integralFlow hv t y) 0 = (φ.symm ∘ α (φ y)) 0 := by
      simp only [Function.comp_apply, integralFlow_zero, (hα _ (hmem y hy)).1]
      exact (φ.left_inv hy.1).symm
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0) ⟨by linarith, hε⟩ hv
      hflowOn hcurve h0 ht
  -- the transported chart flow is continuous on the product
  have hcont : ContinuousOn (fun p : ℝ × M => φ.symm (α (φ p.2) p.1)) (Ioo (-ε) ε ×ˢ U) := by
    refine (continuousOn_extChartAt_symm x₀).comp ?_ ?_
    · refine hαc.comp (f := fun p : ℝ × M => (p.1, φ p.2)) ?_ ?_
      · exact (continuous_fst.continuousOn).prodMk
          ((continuousOn_extChartAt x₀).comp continuous_snd.continuousOn fun p hp => hp.2.1)
      · intro p hp
        exact ⟨Ioo_subset_Icc_self hp.1, hmem _ hp.2⟩
    · intro p hp
      exact interior_subset ((hα _ (hmem _ hp.2)).2.2 p.1)
  exact hcont.congr fun p hp => hflow p.2 hp.2 p.1 hp.1

/-- Continuity of the flow at time `t` in the initial point, for `|t|` below a uniform time. -/
theorem exists_forall_continuous_integralFlow_of_abs_lt :
    ∃ ε₀ > (0 : ℝ), ∀ t : ℝ, |t| < ε₀ → Continuous fun x => integralFlow hv t x := by
  choose U hU hUo ε hε hcont using exists_nhds_continuousOn_integralFlow hv
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  by_cases hne : s.Nonempty
  · set ε₀ : ℝ := s.inf' hne ε with hε₀
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀, Finset.lt_inf'_iff]
      exact fun y _ => hε y
    refine ⟨ε₀, hε₀pos, fun t ht => continuous_iff_continuousAt.mpr fun x => ?_⟩
    have hx : x ∈ ⋃ y₀ ∈ s, U y₀ := by rw [hs]; trivial
    obtain ⟨y₀, hy₀s, hxU⟩ := Set.mem_iUnion₂.mp hx
    have hle : ε₀ ≤ ε y₀ := Finset.inf'_le _ hy₀s
    have hopen : IsOpen (Ioo (-(ε y₀)) (ε y₀) ×ˢ U y₀) := isOpen_Ioo.prod (hUo y₀)
    have hmem : (t, x) ∈ Ioo (-(ε y₀)) (ε y₀) ×ˢ U y₀ := by
      refine ⟨?_, hxU⟩
      rw [mem_Ioo]
      constructor <;> [linarith [abs_lt.mp ht |>.1]; linarith [abs_lt.mp ht |>.2]]
    have hat : ContinuousAt (fun p : ℝ × M => integralFlow hv p.1 p.2) (t, x) :=
      (hcont y₀).continuousAt (hopen.mem_nhds hmem)
    exact hat.comp (Continuous.prodMk continuous_const continuous_id).continuousAt
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hempty : ∀ x : M, False := fun x => by
      have : x ∈ (⋃ y₀ ∈ (∅ : Finset M), U y₀) := by rw [hs]; trivial
      simp at this
    exact ⟨1, one_pos, fun t _ => continuous_iff_continuousAt.mpr fun x => (hempty x).elim⟩

/-- The flow at time `k • s` is the `k`-th iterate of the flow at time `s`. -/
theorem integralFlow_nsmul (s : ℝ) (k : ℕ) (x : M) :
    integralFlow hv (k * s) x = (fun y => integralFlow hv s y)^[k] x := by
  induction k generalizing x with
  | zero => simp [integralFlow_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, ← integralFlow_add]
    congr 1
    push_cast
    ring

/-- ★ For every time `t`, `x ↦ integralFlow t x` is continuous (iterate a small time). -/
theorem continuous_integralFlow_point (t : ℝ) : Continuous fun x => integralFlow hv t x := by
  obtain ⟨ε₀, hε₀, hsmall⟩ := exists_forall_continuous_integralFlow_of_abs_lt hv
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |t| / ε₀ < N := exists_nat_gt _
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hlt : |t / N| < ε₀ := by
    rw [abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε₀] at hN
    linarith
  have heq : (fun x => integralFlow hv t x) = fun x => integralFlow hv (N * (t / N)) x := by
    funext x
    congr 1
    field_simp
  rw [heq]
  simp_rw [integralFlow_nsmul hv (t / N) N]
  exact (hsmall (t / N) hlt).iterate N

/-- ★★ **The flow of a `C^1` vector field on a compact manifold is jointly continuous.** -/
theorem continuous_integralFlow : Continuous fun p : ℝ × M => integralFlow hv p.1 p.2 := by
  refine continuous_iff_continuousAt.mpr fun ⟨t₀, x₀⟩ => ?_
  -- the flow is the local flow composed with `(t, x) ↦ (t - t₀, integralFlow t₀ x)`
  have hg : Continuous fun p : ℝ × M => (p.1 - t₀, integralFlow hv t₀ p.2) :=
    (continuous_fst.sub continuous_const).prodMk
      ((continuous_integralFlow_point hv t₀).comp continuous_snd)
  have hloc : ContinuousAt (fun p : ℝ × M => integralFlow hv p.1 p.2) (0, integralFlow hv t₀ x₀) := by
    obtain ⟨U, hU, hUo, ε, hε, hcont⟩ := exists_nhds_continuousOn_integralFlow hv (integralFlow hv t₀ x₀)
    exact hcont.continuousAt ((isOpen_Ioo.prod hUo).mem_nhds ⟨⟨by linarith, hε⟩, mem_of_mem_nhds hU⟩)
  have heq : (fun p : ℝ × M => integralFlow hv p.1 p.2)
      = (fun p : ℝ × M => integralFlow hv p.1 p.2) ∘ fun p => (p.1 - t₀, integralFlow hv t₀ p.2) := by
    funext p
    simp only [Function.comp_apply]
    rw [← integralFlow_add, sub_add_cancel]
  rw [heq]
  have hg0 : ContinuousAt (fun p : ℝ × M => integralFlow hv p.1 p.2)
      ((fun p : ℝ × M => (p.1 - t₀, integralFlow hv t₀ p.2)) (t₀, x₀)) := by simpa using hloc
  exact ContinuousAt.comp (f := fun p : ℝ × M => (p.1 - t₀, integralFlow hv t₀ p.2))
    (g := fun p : ℝ × M => integralFlow hv p.1 p.2) hg0 hg.continuousAt

end Manifold
