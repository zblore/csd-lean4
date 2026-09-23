/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `C^n` dependence of a parametric interval integral on its parameter

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #60, the
regularity the Poincaré primitive needs for Darboux's theorem at order `n`.

If `F : E → ℝ → ℝ` is jointly `C^n` on an open set containing `U × [0, 1]`, with `E`
finite-dimensional, then `x ↦ ∫₀¹ F x t dt` is `C^n` on `U`. The proof is by induction on `n`:
the derivative of the integral is the integral of the partial derivative
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, with a bound on a compact
tube), and that derivative is `C^{n−1}` because, applied to any fixed vector, it is again a
parametric integral of a jointly `C^{n−1}` scalar integrand (`contDiffOn_clm_apply`, finite
dimension). Mathlib at the pin has the `C¹` step and the continuity, not the iteration.

* `exists_closedBall_prod_Icc_subset` — the compact tube around a point of `U`;
* ★ `contDiffOn_intervalIntegral_of_contDiffOn` — the theorem, for `n ≤ ∞`.

References: `Analysis/Calculus/DifferentialForm/Poincare.lean` (the consumer);
`specs/BACKLOG.md` #60.
-/

@[expose] public section

open Set Metric Filter MeasureTheory intervalIntegral
open scoped Topology Interval ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A closed ball around `x ∈ U`, inside `U`, whose product with `[0, 1]` lies in the open `W`. -/
theorem exists_closedBall_prod_Icc_subset {U : Set E} (hU : IsOpen U) {W : Set (E × ℝ)}
    (hW : IsOpen W) (hUW : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ W) {x : E} (hx : x ∈ U) :
    ∃ ρ > 0, closedBall x ρ ⊆ U ∧ ∀ y ∈ closedBall x ρ, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ W := by
  obtain ⟨u, v, hu, -, hxu, hIv, huv⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hW
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := hp
      rw [mem_singleton_iff] at hp1
      have : p = (x, p.2) := Prod.ext hp1 rfl
      rw [this]
      exact hUW x hx p.2 hp2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hu.inter hU) x ⟨hxu (mem_singleton x), hx⟩
  have hcb : closedBall x (ε / 2) ⊆ ball x ε := closedBall_subset_ball (by linarith)
  refine ⟨ε / 2, by positivity, fun y hy => (hball (hcb hy)).2, fun y hy t ht => ?_⟩
  exact huv ⟨(hball (hcb hy)).1, hIv ht⟩

variable [FiniteDimensional ℝ E]

/-- The induction behind `contDiffOn_intervalIntegral_of_contDiffOn`, on the order. -/
theorem contDiffOn_intervalIntegral_aux (k : ℕ) :
    ∀ (F : E → ℝ → ℝ) (U : Set E), IsOpen U → ∀ (W : Set (E × ℝ)), IsOpen W →
      (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ W) →
      ContDiffOn ℝ k (Function.uncurry F) W →
      ContDiffOn ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) U := by
  induction k with
  | zero =>
    intro F U hU W hW hUW hF
    rw [Nat.cast_zero, contDiffOn_zero] at hF ⊢
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    obtain ⟨ρ, hρ, -, hρW⟩ := exists_closedBall_prod_Icc_subset hU hW hUW hx
    have hKc : IsCompact (closedBall x ρ ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_closedBall x ρ).prod isCompact_Icc
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hF.mono fun p hp => hρW p.1 hp.1 p.2 hp.2)
    have hIcc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
      rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
    have hcont : ∀ y ∈ closedBall x ρ, ContinuousOn (F y) (Icc 0 1) := fun y hy =>
      hF.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht => hρW y hy t ht
    refine continuousAt_of_dominated_interval (bound := fun _ => B) ?_ ?_ intervalIntegrable_const
      ?_
    · filter_upwards [closedBall_mem_nhds x hρ] with y hy
      exact ((hcont y hy).mono hIcc).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [closedBall_mem_nhds x hρ] with y hy
      exact Filter.Eventually.of_forall fun t ht => hB (y, t) ⟨hy, hIcc ht⟩
    · refine Filter.Eventually.of_forall fun t ht => ?_
      have hxt : (x, t) ∈ W := hρW x (mem_closedBall_self hρ.le) t (hIcc ht)
      exact ContinuousAt.comp (f := fun y : E => (y, t)) (hF.continuousAt (hW.mem_nhds hxt))
        (continuous_id.prodMk continuous_const).continuousAt
  | succ k ih =>
    intro F U hU W hW hUW hF
    have hn : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by norm_cast; omega
    -- the partial derivative in the parameter
    have hFd : ∀ p ∈ W, HasFDerivAt (fun y => F y p.2)
        (fderiv ℝ (Function.uncurry F) p ∘L ContinuousLinearMap.inl ℝ E ℝ) p.1 := by
      rintro ⟨y, t⟩ hp
      have hd : DifferentiableAt ℝ (Function.uncurry F) (y, t) :=
        (hF.differentiableOn (lt_of_lt_of_le zero_lt_one hn).ne').differentiableAt
          (hW.mem_nhds hp)
      exact hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
    set F' : E → ℝ → E →L[ℝ] ℝ :=
      fun y t => fderiv ℝ (Function.uncurry F) (y, t) ∘L ContinuousLinearMap.inl ℝ E ℝ with hF'
    have hF'c : ContinuousOn (fun p : E × ℝ => F' p.1 p.2) W :=
      (hF.continuousOn_fderiv_of_isOpen hW hn).clm_comp continuousOn_const
    have hIcc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
      rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
    -- the integral is differentiable, with derivative the integral of `F'`
    have hd : ∀ x ∈ U, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, F x t)
        (∫ t in (0 : ℝ)..1, F' x t) x := by
      intro x hx
      obtain ⟨ρ, hρ, -, hρW⟩ := exists_closedBall_prod_Icc_subset hU hW hUW hx
      have hKc : IsCompact (closedBall x ρ ×ˢ Icc (0 : ℝ) 1) :=
        (isCompact_closedBall x ρ).prod isCompact_Icc
      obtain ⟨B, hB⟩ :=
        hKc.exists_bound_of_continuousOn (hF'c.mono fun p hp => hρW p.1 hp.1 p.2 hp.2)
      have hcont : ∀ y ∈ closedBall x ρ, ContinuousOn (F y) (Icc 0 1) := fun y hy =>
        hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          fun t ht => hρW y hy t ht
      have hcont' : ContinuousOn (F' x) (Icc 0 1) :=
        hF'c.comp (continuous_const.prodMk continuous_id).continuousOn
          fun t ht => hρW x (mem_closedBall_self hρ.le) t ht
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x ρ) (bound := fun _ => B)
        (ball_mem_nhds x hρ) ?_ ?_ ?_ ?_ ?_ ?_
      · filter_upwards [ball_mem_nhds x hρ] with y hy
        exact ((hcont y (ball_subset_closedBall hy)).mono hIcc).aestronglyMeasurable
          measurableSet_uIoc
      · exact (hcont x (mem_closedBall_self hρ.le)).intervalIntegrable_of_Icc zero_le_one
      · exact (hcont'.mono hIcc).aestronglyMeasurable measurableSet_uIoc
      · exact Filter.Eventually.of_forall fun t ht y hy =>
          hB (y, t) ⟨ball_subset_closedBall hy, hIcc ht⟩
      · exact intervalIntegrable_const
      · exact Filter.Eventually.of_forall fun t ht y hy =>
          hFd (y, t) (hρW y (ball_subset_closedBall hy) t (hIcc ht))
    -- `C^{k+1}`: differentiable with a `C^k` derivative
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hderiv : ContDiffOn ℝ k (fun x => ∫ t in (0 : ℝ)..1, F' x t) U := by
      rw [contDiffOn_clm_apply]
      intro h
      have hint : ∀ x ∈ U, IntervalIntegrable (F' x) volume 0 1 := fun x hx =>
        (hF'c.comp (continuous_const.prodMk continuous_id).continuousOn
          fun t ht => hUW x hx t ht).intervalIntegrable_of_Icc zero_le_one
      have hFh : ContDiffOn ℝ k (Function.uncurry fun y t => F' y t h) W :=
        ((hF.fderiv_of_isOpen hW (by push_cast; exact le_rfl)).clm_comp
          contDiffOn_const).clm_apply contDiffOn_const
      exact (ih (fun y t => F' y t h) U hU W hW hUW hFh).congr fun x hx =>
        ContinuousLinearMap.intervalIntegral_apply (hint x hx) h
    exact hderiv.congr fun x hx => (hd x hx).fderiv

/-- ★ **A parametric interval integral of a jointly `C^n` integrand is `C^n` in the parameter**
(`n ≤ ∞`, finite-dimensional parameter space): if `F` is `C^n` on an open set containing
`U × [0, 1]`, then `x ↦ ∫₀¹ F x t dt` is `C^n` on the open `U`. -/
theorem contDiffOn_intervalIntegral_of_contDiffOn {n : ℕ∞} {F : E → ℝ → ℝ} {U : Set E}
    (hU : IsOpen U) {W : Set (E × ℝ)} (hW : IsOpen W)
    (hUW : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ W)
    (hF : ContDiffOn ℝ n (Function.uncurry F) W) :
    ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, F x t) U := by
  induction n using ENat.recTopCoe with
  | top =>
    rw [contDiffOn_infty]
    intro m
    exact contDiffOn_intervalIntegral_aux m F U hU W hW hUW (contDiffOn_infty.mp hF m)
  | coe m => exact contDiffOn_intervalIntegral_aux m F U hU W hW hUW hF

end
