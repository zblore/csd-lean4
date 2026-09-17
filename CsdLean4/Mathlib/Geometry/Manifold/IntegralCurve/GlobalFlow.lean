/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Dynamics.Flow
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Global integral curves and the flow of a `C^1` vector field on a compact manifold

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.IntegralCurve`).

Mathlib has local existence (`exists_isMIntegralCurveAt_of_contMDiffAt`), uniqueness
(`isMIntegralCurve_eq_of_contMDiff`), and the uniform-time principle
`exists_isMIntegralCurve_of_isMIntegralCurveOn`: if every point has a local integral curve on one
and the same `Ioo (-ε) ε`, every point has a *global* one. What it does not have is the uniform
`ε` itself. On a compact manifold it exists, and this module proves it:

* ★ `exists_nhds_forall_exists_isMIntegralCurveOn_Ioo` — **uniform local existence time on a
  neighbourhood**: around every point there is a neighbourhood `U` and an `ε > 0` such that every
  `x ∈ U` has an integral curve on `Ioo (-ε) ε` with `γ 0 = x`. This is Mathlib's local proof with
  the *ball* of Picard–Lindelöf kept
  (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
  gives one `ε` for a whole closed ball of chart initial points), and the confinement of the chart
  solutions to the chart's target made uniform by shrinking the ball.
* ★★ `exists_isMIntegralCurve_of_compactSpace` — **on a compact manifold every `C^1` vector field
  has a global integral curve through every point** (finite subcover, minimum `ε`, Mathlib's
  uniform-time principle).
* ★★ `integralFlow hv` — **the flow** `ℝ → M → M` (indexed by the existence proof `hv`, well-defined
  by uniqueness), with `integralFlow hv 0 = id`,
  `integralFlow_add` (the group law, from uniqueness applied to `t ↦ φ (s + t) x`), and
  `isMIntegralCurve_integralFlow` (each orbit is an integral curve); `integralFlow_continuous_time`
  (continuity in `t`) is what uniqueness plus the curves' continuity gives; **joint continuity in
  `(t, x)` is not stated** (see scope).

## Honest scope

**Against Mathlib's ODE API (checked 2026-09-17).** The three flat lemmas are not duplicates of
Mathlib's `IsPicardLindelof.of_contDiffAt_one`,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt` and
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`: each adds the
*confinement* of the solutions to a prescribed neighbourhood (the closed Lipschitz ball inside a
given `s ∈ 𝓝 x₀`, `∀ t, α t ∈ s`), which Mathlib's statements do not provide and the manifold
transport needs (the chart solutions must stay in the chart's target). They are the natural
upstream strengthening of Mathlib's lemmas, not restatements of them; uniqueness and the
uniform-time principle are Mathlib's own (`isMIntegralCurve_eq_of_contMDiff`,
`exists_isMIntegralCurve_of_isMIntegralCurveOn`).


⚠️ **The flow is not yet a `Flow`.** Mathlib's `Flow τ α` needs joint continuity `ℝ × M → M`.
Continuity in `t` for fixed `x` is here. Continuity in `x` needs continuous dependence of the
integral curve on its initial point at manifold level; the flat Lipschitz dependence exists
(`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`) and gluing it
along the chart cover is the residue (Q29(a′), S–M). Nothing downstream consumes joint continuity
until Q29(d′), which needs the time-`t` maps as homeomorphisms — that is where (a′) is spent.

⚠️ **`C^1`, and `x₀`'s chart.** The field is assumed `C^1` as a section of the tangent bundle, the
hypothesis Mathlib's local theorem takes; `C^∞` fields qualify by `ContMDiff.of_le`. The
transport in `exists_nhds_forall_exists_isMIntegralCurveOn_Ioo` works in the chart at `x₀` and
produces curves for initial points in a chart-neighbourhood of `x₀`; the neighbourhood is the
preimage of a closed ball, a neighbourhood of `x₀` in `M` by `continuousAt_extChartAt`.

**Provenance and references.** The generator-layer plan §11 (Q29);
`Mathlib/Geometry/Manifold/IntegralCurve/`
(`ExistUnique.lean`, `UniformTime.lean`); `Mathlib/Analysis/ODE/ExistUnique.lean`
(`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`).
-/

@[expose] public section

noncomputable section

open Set Filter Metric Topology
open scoped Manifold ContDiff NNReal

/-! ### Picard–Lindelöf with the confinement ball kept -/

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Picard–Lindelöf data for a `C^1` field at `x₀`, with the Lipschitz ball inside a prescribed
neighbourhood `s`. Mathlib's `IsPicardLindelof.of_contDiffAt_one` with one extra intersection. -/
theorem ContDiffAt.isPicardLindelof_subset {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), closedBall x₀ a ⊆ s ∧ ∀ (t₀ : ℝ),
      IsPicardLindelof (fun _ ↦ f) (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, (by simp [le_of_lt ‹0 < ε›])⟩ x₀ a r L K := by
  obtain ⟨K, u, hu, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha : 0 < a, hau⟩ := Metric.mem_nhds_iff.mp (inter_mem hu hs)
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hball : closedBall x₀ (a / 2) ⊆ u ∩ s :=
    (closedBall_subset_ball (half_lt_self ha)).trans hau
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhds hu)
        exact (hball hx).1
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    .mk (a / 2) (half_pos ha).le, (.mk (a / 2) (half_pos ha).le) / 2,
    .mk L hL0.le, K, half_pos <| half_pos ha, fun x hx => (hball hx).2, fun t₀ ↦ ?_⟩
  apply IsPicardLindelof.of_time_independent hb (hl.mono fun x hx => (hball hx).1)
  simp [ε, field]
  norm_num

/-- Picard–Lindelöf with the confinement of the solution made explicit
(`ODE.FunSpace.compProj_mem_closedBall`). -/
theorem IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {x : E} (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      ∀ t, α t ∈ closedBall x₀ a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht ↦ ?_, fun t => α.compProj_mem_closedBall hf.mul_max_le⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- ★ `C^1` at `x₀`: a uniform existence time `ε` for all initial points in a closed ball, with
the solutions confined to a prescribed neighbourhood `s` of `x₀`, uniformly. -/
theorem ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt_mem
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α 0 = x ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt α (f (α t)) t) ∧ ∀ t, α t ∈ s := by
  obtain ⟨ε, hε, a, r, L, K, hr, has, hpl⟩ := hf.isPicardLindelof_subset hs
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  obtain ⟨α, hα1, hα2, hα3⟩ := (hpl 0).exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall hx
  refine ⟨α, hα1, fun t ht ↦ ?_, fun t => has (hα3 t)⟩
  have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa using ht
  exact hα2 t (Ioo_subset_Icc_self ht') |>.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

end Flat

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-! ### Uniform local existence time on a neighbourhood -/

set_option backward.isDefEq.respectTransparency false in
/-- ★ **Uniform local existence time on a neighbourhood.** For a `C^1` vector field and a point
`x₀`, there are a neighbourhood `U` of `x₀` and an `ε > 0` such that every `x ∈ U` is the initial
point of an integral curve defined on `Ioo (-ε) ε`.

Mathlib's local theorem (`exists_isMIntegralCurveAt_of_contMDiffAt`) transported with the ball kept:
the flat Picard–Lindelöf statement gives one `ε` for every chart initial point in a closed ball
around `φ x₀`, and the chart solutions are confined, uniformly, to a ball inside
`interior φ.target`
(`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt_mem`),
so `φ.symm ∘ f` is an integral curve on the whole interval. -/
theorem exists_nhds_forall_exists_isMIntegralCurveOn_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∀ x ∈ U,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  -- the field in the chart at `x₀`, `C^1` at the chart point
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hv' := hv x₀
  rw [contMDiffAt_iff] at hv'
  obtain ⟨_, hv'⟩ := hv'
  have hf : ContDiffAt ℝ 1
      (fun w => (extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M) ∘
        (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∘ (extChartAt I x₀).symm) w)
      (extChartAt I x₀ x₀) :=
    hv'.contDiffAt (range_mem_nhds_isInteriorPoint hx)
  -- the chart field `F w := snd (chart of the section at w)`, C^1; confine to the interior of the
  -- target
  have hint : interior (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx)
  obtain ⟨r, hr, ε, hε, H⟩
      := hf.snd.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt_mem hint
  -- the neighbourhood on `M`: the preimage of the closed ball under the chart, intersected with the
  -- source
  refine ⟨(extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' closedBall (extChartAt I x₀ x₀) r,
    inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (closedBall_mem_nhds _ hr)),
    ε, hε, fun x ⟨hxs, hxb⟩ => ?_⟩
  obtain ⟨f, hf1, hf2, hf3⟩ := H (extChartAt I x₀ x) hxb
  refine ⟨(extChartAt I x₀).symm ∘ f,
    by rw [Function.comp_apply, hf1, PartialEquiv.left_inv _ hxs], ?_⟩
  intro t ht
  -- from here: Mathlib's local proof, with `hf3 t` in place of the neighbourhood argument
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


/-! ### Global integral curves on a compact manifold -/

/-- ★★ **On a compact manifold every `C^1` vector field has a global integral curve through every
point.** Cover by the neighbourhoods of `exists_nhds_forall_exists_isMIntegralCurveOn_Ioo`, take a
finite subcover, the minimum of its `ε`s is a uniform existence time, and Mathlib's
`exists_isMIntegralCurve_of_isMIntegralCurveOn` extends every local curve to a global one. -/
theorem exists_isMIntegralCurve_of_compactSpace [CompactSpace M] [T2Space M]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  choose U hU ε hε hcurve using exists_nhds_forall_exists_isMIntegralCurveOn_Ioo hv
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  -- the uniform time: the minimum over the finite subcover, or `1` if it is empty (it is not)
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    have : x ∈ (⋃ y₀ ∈ (∅ : Finset M), U y₀) := by rw [hs]; trivial
    simp at this
  set ε₀ : ℝ := s.inf' hne ε with hε₀
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀, Finset.lt_inf'_iff]
    exact fun y _ => hε y
  refine exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε₀pos (fun y => ?_) x
  -- every point lies in some `U y₀` of the subcover
  have hy : y ∈ ⋃ y₀ ∈ s, U y₀ := by rw [hs]; trivial
  obtain ⟨y₀, hy₀s, hyU⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨γ, hγ0, hγ⟩ := hcurve y₀ y hyU
  have : ε₀ ≤ ε y₀ := Finset.inf'_le _ hy₀s
  exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg this) this)⟩

/-! ### The flow -/

variable [CompactSpace M] [T2Space M]
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))

/-- ★★ **The flow of a `C^1` vector field on a compact manifold**: `integralFlow hv t x` is the
value at time `t` of the (unique) global integral curve through `x` at time `0`. -/
def integralFlow (t : ℝ) (x : M) : M :=
  (exists_isMIntegralCurve_of_compactSpace hv x).choose t

theorem integralFlow_zero (x : M) : integralFlow hv 0 x = x :=
  (exists_isMIntegralCurve_of_compactSpace hv x).choose_spec.1

/-- Each orbit of the flow is a global integral curve. -/
theorem isMIntegralCurve_integralFlow (x : M) :
    IsMIntegralCurve (fun t => integralFlow hv t x) v :=
  (exists_isMIntegralCurve_of_compactSpace hv x).choose_spec.2

/-- The flow is the unique global integral curve through `x` at `0`. -/
theorem integralFlow_eq_of_isMIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {x : M}
    (h0 : γ 0 = x) : γ = fun t => integralFlow hv t x :=
  isMIntegralCurve_eq_of_contMDiff (fun _ => BoundarylessManifold.isInteriorPoint) hv hγ
    (isMIntegralCurve_integralFlow hv x) (t₀ := 0) (h0.trans (integralFlow_zero hv x).symm)

/-- ★★ **The group law** `φ (s + t) = φ s ∘ φ t`: `u ↦ φ (u + t) x` is an integral curve through
`φ t x` at `0` (`IsMIntegralCurve.comp_add`), so by uniqueness it is `u ↦ φ u (φ t x)`. -/
theorem integralFlow_add (s t : ℝ) (x : M) :
    integralFlow hv (s + t) x = integralFlow hv s (integralFlow hv t x) := by
  have h : (fun u : ℝ => integralFlow hv (u + t) x) = fun u => integralFlow hv u (integralFlow hv t
      x) :=
    integralFlow_eq_of_isMIntegralCurve hv ((isMIntegralCurve_integralFlow hv x).comp_add t)
      (by simp)
  exact congrFun h s

theorem continuous_integralFlow_time (x : M) : Continuous fun t => integralFlow hv t x :=
  (isMIntegralCurve_integralFlow hv x).continuous

end Manifold

end
