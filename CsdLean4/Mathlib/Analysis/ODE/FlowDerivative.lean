/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.IntegralCurve.FlowContinuity
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Differentiable dependence of a flow on its initial point, and flat Liouville

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Q29(b′) of
`specs/generator-layer-scoping.md`.

Mathlib's Picard–Lindelöf theorem gives existence, uniqueness and Lipschitz dependence of the
local flow of a `C¹` vector field on the initial point, but not **differentiable** dependence.
This file proves it, with the derivative given by the **variational equation**, and draws the
consequence the corpus needs: a `C¹` 2-form whose flat Lie derivative along the field vanishes is
pulled back to itself by the local flow (the flat Liouville theorem).

* `gronwallBound_zero_le` — the Grönwall bound with zero initial gap is at most `ε x e^{K x}`;
* `exists_linearODE_solution` — the linear ODE `Y' = A(t) Y` on a Banach space has a solution on
  a short interval whose length depends only on a bound for `‖A‖` and on `‖Y₀‖` (Picard–Lindelöf
  on the operator space); `exists_linearODE_solution_of_le` — on all of `[0, T]` when
  `T · M · (‖Y₀‖ + 1) ≤ 1`;
* `norm_le_exp_of_linearODE` — a solution of the operator-valued `Y' = A(t) ∘ Y`, `Y 0 = 1`,
  `‖A‖ ≤ M` has `‖Y t‖ ≤ e^{M t}`; ★ `dist_le_of_linearODE_coeff_close` — **continuous
  dependence of a linear ODE's solution on its coefficient**: two such solutions whose
  coefficients are `ε`-close on `[0, T]` are within `ε e^{M T} · T e^{M T}` (Grönwall for
  approximate trajectories on the operator space);
* ★★ `hasFDerivAt_flow_of_variational_timeDependent` — **differentiable dependence**, for a
  time-dependent field: for `f t` differentiable on an open set with `(t, z) ↦ D(f t)(z)`
  continuous, a flow `α` confined to a compact and Lipschitz in the initial point, and a solution
  `Y` of the variational equation `Y' = D(f t)(α x t) ∘ Y`, `Y 0 = 1`, the time-`t` map is
  differentiable at `x` with derivative `Y t`. The proof is Grönwall's inequality for approximate
  trajectories (`dist_le_of_approx_trajectories_ODE_of_mem`): the difference of two trajectories
  is an approximate solution of the linearised equation, with defect controlled by the mean value
  inequality and the uniform continuity of `(t, z) ↦ D(f t)(z)` on a compact thickening;
  ★★ `hasFDerivAt_flow_of_variational` is the autonomous case;
* ★ `ContDiffAt.exists_localFlow_hasFDerivAt` — a `C¹` field has a local flow, confined to a
  prescribed neighbourhood, differentiable in the initial point for a uniform short time;
* ★ `exists_flow_hasFDerivAt_of_norm_fderiv_le` — **the flow of a small time-dependent field
  up to a prescribed time `T`** (`‖D(f t)‖ ≤ M` on a ball, `M T ≤ 1/2`, `f t x₀ = 0`): trajectories
  on `[0, T]` confined to the ball, the Grönwall separation `e^{M t}`, the variational
  derivative at every point of the half-ball, **and its continuous dependence on the point**
  (`x ↦ Dφ_t(x)` is continuous, so the time-`t` map is `C¹`) — what Moser's trick needs
  (Darboux, time `1`);
* `flatLieDeriv` — the flat Lie derivative of a 2-form along a field,
  `(L_X ω)(m) = Dω(X)(m) + ω(DX m₀, m₁) + ω(m₀, DX m₁)`;
* ★ `form_invariant_of_flatLieDeriv_eq_zero_timeDependent` — **flat transport for a
  time-dependent form and field**: along an integral curve with its variational solution,
  `Ω t (α t) (Y t ∘ m) = Ω 0 (α 0) m` when `∂ₜΩ + L_{f t} Ω t = 0`
  (`constant_of_has_deriv_right_zero` on the product-rule derivative);
  ★ `form_invariant_of_flatLieDeriv_eq_zero` is the autonomous case, `ω (α t) (Y t ∘ m) = ω (α 0) m`
  when the flat Lie derivative vanishes;
* ★★ `ContDiffAt.exists_localFlow_form_invariant` — **flat Liouville**: the local flow pulls the
  form back to itself, `(ω (α x t)).compContinuousLinearMap (D(α · t) x) = ω x`, confined to a
  prescribed neighbourhood.

The local flow solves the equation on `[-ε, ε]` (what the identification with the manifold flow
by uniqueness on an open interval needs); the derivative and the invariance are for forward time
`t ∈ [0, ε]` on a proper space (finite-dimensional in the application), and negative times follow
downstream from the group law of the manifold flow. The flat Cartan formula identifying
`flatLieDeriv` with `d(ι_X ω) + ι_X dω` is `Geometry/Manifold/HamiltonianLieDerivative.lean`
(Q29(c′)); the manifold assembly is `Geometry/Manifold/HamiltonianFlowVolume.lean` (Q29(d′)).
-/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal ContDiff


section Gronwall

/-- The Grönwall bound with zero initial gap is at most `ε x e^{K x}`. -/
theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (_hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * (x * Real.exp (K * x)) := by
  rcases eq_or_lt_of_le hK with rfl | hK'
  · rw [gronwallBound_K0]
    simp only [zero_mul, Real.exp_zero, mul_one, zero_add, le_refl]
  · rw [gronwallBound_of_K_ne_0 hK'.ne']
    have hpos := Real.exp_pos (K * x)
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h := Real.add_one_le_exp (-(K * x))
      rw [Real.exp_neg] at h
      have h2 := mul_le_mul_of_nonneg_right h hpos.le
      rw [inv_mul_cancel₀ hpos.ne'] at h2
      nlinarith
    calc 0 * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1)
        = ε / K * (Real.exp (K * x) - 1) := by ring
      _ ≤ ε / K * (K * x * Real.exp (K * x)) := by gcongr
      _ = ε * (x * Real.exp (K * x)) := by field_simp

end Gronwall

section LinearODE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The linear ODE `Y' = A(t) Y` has a solution on a short interval** whose length depends only
on a bound for `‖A‖` and on `‖Y₀‖` (Picard–Lindelöf on the Banach space `F`). -/
theorem exists_linearODE_solution (A : ℝ → F →L[ℝ] F) {T M τ : ℝ} (hT : 0 < T)
    (hA : ∀ Y, ContinuousOn (fun t => A t Y) (Icc 0 T)) (hM : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    (Y₀ : F) (hτ0 : 0 < τ) (hτT : τ ≤ T) (hτL : τ * (M * (‖Y₀‖ + 1) + 1) ≤ 1) :
    ∃ Y : ℝ → F, Y 0 = Y₀ ∧ ∀ t ∈ Icc 0 τ, HasDerivWithinAt Y (A t (Y t)) (Icc 0 τ) t := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set L : ℝ := M * (‖Y₀‖ + 1) + 1 with hL
  have hL0 : 0 < L := by positivity
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc_right hτT
  have hpl : IsPicardLindelof (fun t (Y : F) => A t Y) (tmin := 0) (tmax := τ)
      ⟨0, ⟨le_rfl, hτ0.le⟩⟩ Y₀ ⟨1, zero_le_one⟩ 0 ⟨L, hL0.le⟩ ⟨M, hM0⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ((A t).lipschitz.weaken ?_).lipschitzOnWith
      exact_mod_cast hM t (hsub ht)
    · intro Y _
      exact (hA Y).mono hsub
    · intro t ht Y hY
      have h1 : ‖Y‖ ≤ ‖Y₀‖ + 1 := by
        have h1' : ‖Y - Y₀‖ ≤ 1 :=
          calc ‖Y - Y₀‖ ≤ ((⟨1, zero_le_one⟩ : ℝ≥0) : ℝ) := mem_closedBall_iff_norm.mp hY
            _ = 1 := rfl
        calc ‖Y‖ = ‖Y₀ + (Y - Y₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖Y₀‖ + ‖Y - Y₀‖ := norm_add_le _ _
          _ ≤ ‖Y₀‖ + 1 := by gcongr
      calc ‖A t Y‖ ≤ ‖A t‖ * ‖Y‖ := (A t).le_opNorm Y
        _ ≤ M * (‖Y₀‖ + 1) := by gcongr; exact hM t (hsub ht)
        _ ≤ L := by rw [hL]; linarith
    · show L * max (τ - 0) (0 - 0) ≤ (1 : ℝ) - 0
      rw [sub_zero, sub_zero, sub_zero, max_eq_left hτ0.le, mul_comm]
      exact hτL
  obtain ⟨Y, hY0, hY⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Y, hY0, hY⟩

/-- **The linear ODE `Y' = A(t) Y` has a solution on the whole of `[0, T]`** when
`T · M · (‖Y₀‖ + 1) ≤ 1`, `M` a bound for `‖A‖` (Picard–Lindelöf on the Banach space `F`, on the
ball of radius `1` about `Y₀`). -/
theorem exists_linearODE_solution_of_le (A : ℝ → F →L[ℝ] F) {T M : ℝ} (hT : 0 < T)
    (hA : ∀ Y, ContinuousOn (fun t => A t Y) (Icc 0 T)) (hM : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    (Y₀ : F) (hTL : T * (M * (‖Y₀‖ + 1)) ≤ 1) :
    ∃ Y : ℝ → F, Y 0 = Y₀ ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (A t (Y t)) (Icc 0 T) t := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set L : ℝ := M * (‖Y₀‖ + 1) with hL
  have hL0 : 0 ≤ L := by positivity
  have hpl : IsPicardLindelof (fun t (Y : F) => A t Y) (tmin := 0) (tmax := T)
      ⟨0, ⟨le_rfl, hT.le⟩⟩ Y₀ ⟨1, zero_le_one⟩ 0 ⟨L, hL0⟩ ⟨M, hM0⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ((A t).lipschitz.weaken ?_).lipschitzOnWith
      exact_mod_cast hM t ht
    · intro Y _
      exact hA Y
    · intro t ht Y hY
      have h1 : ‖Y‖ ≤ ‖Y₀‖ + 1 := by
        have h1' : ‖Y - Y₀‖ ≤ 1 :=
          calc ‖Y - Y₀‖ ≤ ((⟨1, zero_le_one⟩ : ℝ≥0) : ℝ) := mem_closedBall_iff_norm.mp hY
            _ = 1 := rfl
        calc ‖Y‖ = ‖Y₀ + (Y - Y₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖Y₀‖ + ‖Y - Y₀‖ := norm_add_le _ _
          _ ≤ ‖Y₀‖ + 1 := by gcongr
      calc ‖A t Y‖ ≤ ‖A t‖ * ‖Y‖ := (A t).le_opNorm Y
        _ ≤ M * (‖Y₀‖ + 1) := by gcongr; exact hM t ht
    · show L * max (T - 0) (0 - 0) ≤ (1 : ℝ) - 0
      rw [sub_zero, sub_zero, sub_zero, max_eq_left hT.le, mul_comm]
      exact hTL
  obtain ⟨Y, hY0, hY⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Y, hY0, hY⟩

end LinearODE

section LinearODEEstimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution of the operator-valued linear ODE `Y' = A(t) ∘ Y`, `Y 0 = 1`, with `‖A t‖ ≤ M` on
`[0, T]`, has `‖Y t‖ ≤ e^{M t}` there (Grönwall against the zero solution). -/
theorem norm_le_exp_of_linearODE {A Y : ℝ → E →L[ℝ] E} {T M : ℝ} (hM0 : 0 ≤ M)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M) (hY0 : Y 0 = 1)
    (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (A t ∘L Y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ Real.exp (M * t) := by
  have hIci : ∀ s ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝[≥] s := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  intro t ht
  have h := dist_le_of_trajectories_ODE_of_mem
    (v := fun s Z => A s ∘L Z) (s := fun _ => univ) (K := ⟨M, hM0⟩)
    (f := Y) (g := fun _ => 0) (a := 0) (b := T) (δ := 1)
    (fun s hs => lipschitzOnWith_univ.mpr (LipschitzWith.of_dist_le_mul fun Z W => by
      show dist (A s ∘L Z) (A s ∘L W) ≤ M * dist Z W
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      calc ‖A s ∘L (Z - W)‖ ≤ ‖A s‖ * ‖Z - W‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * ‖Z - W‖ := by gcongr; exact hA s (Ico_subset_Icc_self hs)))
    (fun s hs => (hYd s hs).continuousWithinAt)
    (fun s hs => (hYd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
    (fun _ _ => mem_univ _)
    continuousOn_const
    (fun s _ => by
      show HasDerivWithinAt (fun _ : ℝ => (0 : E →L[ℝ] E)) (A s ∘L 0) (Ici s) s
      rw [ContinuousLinearMap.comp_zero]
      exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => mem_univ _)
    (by
      show dist (Y 0) 0 ≤ 1
      rw [hY0, dist_zero_right]
      exact ContinuousLinearMap.norm_id_le)
    t ht
  simp only [dist_zero_right, sub_zero, one_mul] at h
  exact h

/-- ★ **Continuous dependence of the solution of a linear ODE on its coefficient.** Two solutions
of `Y' = A(t) ∘ Y`, `Z' = B(t) ∘ Z` with `Y 0 = Z 0 = 1`, `‖A‖, ‖B‖ ≤ M` and `‖B − A‖ ≤ ε` on
`[0, T]` are within `ε e^{M T} · T e^{M T}` on `[0, T]`: `Z` is an approximate trajectory of `Y`'s
equation with defect `‖(B − A) ∘ Z‖ ≤ ε e^{M T}`, and Grönwall
(`dist_le_of_approx_trajectories_ODE_of_mem`) bounds the gap. -/
theorem dist_le_of_linearODE_coeff_close {A B Y Z : ℝ → E →L[ℝ] E} {T M ε : ℝ}
    (hM0 : 0 ≤ M) (hε : 0 ≤ ε)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M) (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ M)
    (hAB : ∀ t ∈ Icc 0 T, ‖B t - A t‖ ≤ ε)
    (hY0 : Y 0 = 1) (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (A t ∘L Y t) (Icc 0 T) t)
    (hZ0 : Z 0 = 1) (hZd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (B t ∘L Z t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, dist (Y t) (Z t) ≤ ε * Real.exp (M * T) * (T * Real.exp (M * T)) := by
  have hIci : ∀ s ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝[≥] s := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hZn := norm_le_exp_of_linearODE hM0 hB hZ0 hZd
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hgron := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun s W => A s ∘L W) (s := fun _ => univ) (K := ⟨M, hM0⟩)
    (f := Y) (f' := fun s => A s ∘L Y s) (g := Z) (g' := fun s => B s ∘L Z s) (a := 0) (b := T)
    (εf := 0) (εg := ε * Real.exp (M * T)) (δ := 0)
    (fun s hs => lipschitzOnWith_univ.mpr (LipschitzWith.of_dist_le_mul fun V W => by
      show dist (A s ∘L V) (A s ∘L W) ≤ M * dist V W
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      calc ‖A s ∘L (V - W)‖ ≤ ‖A s‖ * ‖V - W‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * ‖V - W‖ := by gcongr; exact hA s (Ico_subset_Icc_self hs)))
    (fun s hs => (hYd s hs).continuousWithinAt)
    (fun s hs => (hYd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
    (fun s _ => by
      show dist (A s ∘L Y s) (A s ∘L Y s) ≤ 0
      simp)
    (fun _ _ => mem_univ _)
    (fun s hs => (hZd s hs).continuousWithinAt)
    (fun s hs => (hZd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      show dist (B s ∘L Z s) (A s ∘L Z s) ≤ ε * Real.exp (M * T)
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
      calc ‖(B s - A s) ∘L Z s‖ ≤ ‖B s - A s‖ * ‖Z s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * Real.exp (M * T) := by
            gcongr
            · exact hAB s hs'
            · exact (hZn s hs').trans (Real.exp_le_exp.mpr (by gcongr; exact hs'.2)))
    (fun _ _ => mem_univ _)
    (by simp [hY0, hZ0])
    t ht
  rw [zero_add, sub_zero] at hgron
  refine hgron.trans ?_
  calc gronwallBound 0 M (ε * Real.exp (M * T)) t
      ≤ ε * Real.exp (M * T) * (t * Real.exp (M * t)) :=
        gronwallBound_zero_le hM0 (by positivity) ht.1
    _ ≤ ε * Real.exp (M * T) * (T * Real.exp (M * T)) := by
        gcongr
        · exact ht.2
        · exact ht.2

end LinearODEEstimates

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]

omit [CompleteSpace E] in
/-- **Differentiable dependence of a flow on the initial point, with the variational equation**,
for a time-dependent field. Let `f t` be differentiable on an open `U` for `t ∈ [0, T]` with
`(t, z) ↦ D(f t)(z)` continuous, `α` a flow of `f` on a closed ball around `x` for times in
`[0, T]`, confined to a compact `K ⊆ U` and Lipschitz in the initial point uniformly in time, and
let `Y` solve the linear variational equation `Y' = D(f t)(α x t) ∘ Y`, `Y 0 = 1`, along the curve
of `x`. Then `α · t` is differentiable at `x` with derivative `Y t`. -/
theorem hasFDerivAt_flow_of_variational_timeDependent
    {f : ℝ → E → E} {U : Set E} (hU : IsOpen U) {T : ℝ} (hT : 0 < T)
    (hfd : ∀ t ∈ Icc 0 T, ∀ z ∈ U, HasFDerivAt (f t) (fderiv ℝ (f t) z) z)
    (hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Icc 0 T ×ˢ U))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {α : E → ℝ → E} {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hα0 : ∀ y ∈ closedBall x ρ, α y 0 = y)
    (hαd : ∀ y ∈ closedBall x ρ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (α y) (f t (α y t)) (Icc 0 T) t)
    (hαK : ∀ y ∈ closedBall x ρ, ∀ t ∈ Icc 0 T, α y t ∈ K)
    {L' : ℝ≥0} (hlip : ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x ρ))
    {Y : ℝ → E →L[ℝ] E} (hY0 : Y 0 = 1)
    (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ (f t) (α x t) ∘L Y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (Y t) x := by
  have hxρ : x ∈ closedBall x ρ := mem_closedBall_self hρ.le
  -- a compact thickening of `K` inside `U`
  obtain ⟨δ₀, hδ₀, hK'U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have hKK' : IsCompact (Icc (0 : ℝ) T ×ˢ cthickening δ₀ K) := isCompact_Icc.prod hK'
  have hsub : Icc (0 : ℝ) T ×ˢ cthickening δ₀ K ⊆ Icc 0 T ×ˢ U := prod_mono subset_rfl hK'U
  obtain ⟨M₀, hM₀⟩ := hKK'.exists_bound_of_continuousOn (hDc.mono hsub)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ s ∈ Icc (0 : ℝ) T, ∀ z ∈ cthickening δ₀ K, ‖fderiv ℝ (f s) z‖ ≤ M :=
    fun s hs z hz => (hM₀ (s, z) ⟨hs, hz⟩).trans (le_max_left _ _)
  have hunif : UniformContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ cthickening δ₀ K) :=
    hKK'.uniformContinuousOn_of_continuous (hDc.mono hsub)
  intro t ht
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set C₀ : ℝ := (L' : ℝ) * (T * Real.exp (M * T)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  set ε : ℝ := c / (C₀ + 1) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.uniformContinuousOn_iff.mp hunif ε hε0
  set δ₂ : ℝ := min (δ₁ / 2) δ₀ with hδ₂
  have hδ₂0 : 0 < δ₂ := lt_min (by positivity) hδ₀
  have hδ₂₁ : δ₂ < δ₁ := (min_le_left _ _).trans_lt (by linarith)
  have hδ₂₀ : δ₂ ≤ δ₀ := min_le_right _ _
  -- the neighbourhood of `h = 0`
  set η : ℝ := min ρ (δ₂ / ((L' : ℝ) + 1)) with hη
  have hη0 : 0 < η := lt_min hρ (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hη0] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhρ : ‖h‖ ≤ ρ := (hh.le.trans (min_le_left _ _))
  have hhδ : (L' : ℝ) * ‖h‖ ≤ δ₂ := by
    have h1 : ‖h‖ ≤ δ₂ / ((L' : ℝ) + 1) := hh.le.trans (min_le_right _ _)
    calc (L' : ℝ) * ‖h‖ ≤ ((L' : ℝ) + 1) * (δ₂ / ((L' : ℝ) + 1)) := by
          gcongr; linarith
      _ = δ₂ := by field_simp
  have hxh : x + h ∈ closedBall x ρ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hhρ
  -- the two trajectories and their difference
  have hdist : ∀ s ∈ Icc 0 T, ‖α (x + h) s - α x s‖ ≤ (L' : ℝ) * ‖h‖ := by
    intro s hs
    have := (hlip s hs).dist_le_mul (x + h) hxh x hxρ
    rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
  -- the approximate-solution estimate, from the mean value inequality on a small ball
  have happrox : ∀ s ∈ Icc 0 T,
      ‖f s (α (x + h) s) - f s (α x s) - fderiv ℝ (f s) (α x s) (α (x + h) s - α x s)‖
        ≤ ε * ((L' : ℝ) * ‖h‖) := by
    intro s hs
    have hz : α x s ∈ K := hαK x hxρ s hs
    have hzK' : α x s ∈ cthickening δ₀ K := self_subset_cthickening _ hz
    have hball : closedBall (α x s) δ₂ ⊆ cthickening δ₀ K := fun w hw =>
      mem_cthickening_of_dist_le w (α x s) δ₀ K hz ((mem_closedBall.mp hw).trans hδ₂₀)
    have hy : α (x + h) s ∈ closedBall (α x s) δ₂ := by
      rw [mem_closedBall, dist_eq_norm]; exact (hdist s hs).trans hhδ
    have hmv := (convex_closedBall (α x s) δ₂).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f s) (f' := fderiv ℝ (f s)) (φ := fderiv ℝ (f s) (α x s)) (C := ε)
      (fun w hw => (hfd s hs w (hK'U (hball hw))).hasFDerivWithinAt)
      (fun w hw => by
        have := hδ₁c (s, w) ⟨hs, hball hw⟩ (s, α x s) ⟨hs, hzK'⟩ (by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
          exact (mem_closedBall.mp hw).trans_lt hδ₂₁)
        rw [dist_eq_norm] at this
        exact this.le)
      (mem_closedBall_self hδ₂0.le) hy
    exact hmv.trans (by gcongr; exact hdist s hs)
  -- Grönwall
  set Fn : ℝ → E := fun s => α (x + h) s - α x s with hFn
  set G : ℝ → E := fun s => Y s h with hG
  have hcontα : ∀ y ∈ closedBall x ρ, ContinuousOn (α y) (Icc 0 T) := fun y hy s hs =>
    (hαd y hy s hs).continuousWithinAt
  have hIci : ∀ s ∈ Ico 0 T, Icc (0 : ℝ) T ∈ 𝓝[≥] s := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hgron := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun s y => fderiv ℝ (f s) (α x s) y) (s := fun _ => univ) (K := ⟨M, hM0⟩)
    (f := Fn) (f' := fun s => f s (α (x + h) s) - f s (α x s)) (g := G)
    (g' := fun s => (fderiv ℝ (f s) (α x s) ∘L Y s) h) (a := 0) (b := T)
    (εf := ε * ((L' : ℝ) * ‖h‖)) (εg := 0) (δ := 0)
    (fun s hs => by
      refine lipschitzOnWith_univ.mpr ((fderiv ℝ (f s) (α x s)).lipschitz.weaken ?_)
      exact_mod_cast hM s (Ico_subset_Icc_self hs) _
        (self_subset_cthickening _ (hαK x hxρ s (Ico_subset_Icc_self hs))))
    ((hcontα _ hxh).sub (hcontα _ hxρ))
    (fun s hs => ((hαd _ hxh s (Ico_subset_Icc_self hs)).sub
      (hαd _ hxρ s (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin (hIci s hs))
    (fun s hs => by
      rw [dist_eq_norm]
      exact happrox s (Ico_subset_Icc_self hs))
    (fun _ _ => mem_univ _)
    (fun s hs => ((hYd s hs).continuousWithinAt).clm_apply continuousWithinAt_const)
    (fun s hs => by
      have := ((hYd s (Ico_subset_Icc_self hs)).clm_apply
        (hasDerivWithinAt_const s (Icc (0 : ℝ) T) h)).mono_of_mem_nhdsWithin (hIci s hs)
      simpa using this)
    (fun s hs => by simp [G])
    (fun _ _ => mem_univ _)
    (by
      simp only [Fn, G, hα0 _ hxh, hα0 _ hxρ, hY0, one_apply_eq_self,
        add_sub_cancel_left, dist_self, le_refl])
    t ht
  rw [dist_eq_norm] at hgron
  simp only [Fn, G, add_zero, sub_zero] at hgron
  refine hgron.trans ?_
  -- gronwallBound 0 M (ε L' ‖h‖) t ≤ c ‖h‖
  calc gronwallBound 0 M (ε * ((L' : ℝ) * ‖h‖)) t
      ≤ ε * ((L' : ℝ) * ‖h‖) * (t * Real.exp (M * t)) :=
        gronwallBound_zero_le hM0 (by positivity) ht.1
    _ ≤ ε * ((L' : ℝ) * ‖h‖) * (T * Real.exp (M * T)) := by
        gcongr
        · exact ht.2
        · exact ht.2
    _ = ε * C₀ * ‖h‖ := by rw [hC₀]; ring
    _ ≤ c * ‖h‖ := by
        gcongr
        rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

omit [CompleteSpace E] in
/-- **Differentiable dependence of a flow on the initial point, with the variational equation.**
Let `f` be `C¹` on an open `U`, `α` a flow of `f` on a closed ball around `x` for times in
`[0, T]`, confined to a compact `K ⊆ U` and Lipschitz in the initial point uniformly in time, and
let `Y` solve the linear variational equation `Y' = Df(α x t) ∘ Y`, `Y 0 = 1`, along the curve of
`x`. Then `α · t` is differentiable at `x` with derivative `Y t`
(`hasFDerivAt_flow_of_variational_timeDependent` for the constant family). -/
theorem hasFDerivAt_flow_of_variational
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {α : E → ℝ → E} {x : E} {ρ T : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (hα0 : ∀ y ∈ closedBall x ρ, α y 0 = y)
    (hαd : ∀ y ∈ closedBall x ρ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (α y) (f (α y t)) (Icc 0 T) t)
    (hαK : ∀ y ∈ closedBall x ρ, ∀ t ∈ Icc 0 T, α y t ∈ K)
    {L' : ℝ≥0} (hlip : ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x ρ))
    {Y : ℝ → E →L[ℝ] E} (hY0 : Y 0 = 1)
    (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ f (α x t) ∘L Y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (Y t) x := by
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ f p.2) (Icc 0 T ×ˢ U) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp continuousOn_snd fun p hp => hp.2
  exact hasFDerivAt_flow_of_variational_timeDependent (f := fun _ => f) hU hT
    (fun _ _ z hz => ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)).hasFDerivAt)
    hDc hK hKU hρ hα0 hαd hαK hlip hY0 hYd

/-- **A `C¹` field has a local flow that is differentiable in the initial point**, with the
derivative solving the variational equation along the curve. The flow satisfies the equation on
`[-ε, ε]`; the derivative is established for forward times `[0, ε]`. -/
theorem ContDiffAt.exists_localFlow_hasFDerivAt {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ s ∧ ContDiffOn ℝ 1 f U ∧
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∃ Y : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ closedBall x₀ r, α x 0 = x ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧ ∀ t, α x t ∈ U) ∧
      ∀ x ∈ ball x₀ r, Y x 0 = 1 ∧
        (∀ t ∈ Icc 0 ε, HasDerivWithinAt (Y x) (fderiv ℝ f (α x t) ∘L Y x t) (Icc 0 ε) t) ∧
        ∀ t ∈ Icc 0 ε, HasFDerivAt (α · t) (Y x t) x := by
  classical
  obtain ⟨U₀, hU₀o, hx₀U₀, hfU₀⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hfU₀
  set U : Set E := U₀ ∩ interior s with hUdef
  have hUo : IsOpen U := hU₀o.inter isOpen_interior
  have hx₀U : x₀ ∈ U := ⟨hx₀U₀, mem_interior_iff_mem_nhds.mpr hs⟩
  have hUs : U ⊆ s := fun z hz => interior_subset hz.2
  have hfU : ContDiffOn ℝ 1 f U := hfU₀.mono inter_subset_left
  obtain ⟨ε, hε, a, r, L, K, hr, haU, hpl⟩ := hf.isPicardLindelof_subset (hUo.mem_nhds hx₀U)
  obtain ⟨α, hα, L', hL'⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem
  simp only [zero_sub, zero_add] at hα hL'
  have hKc : IsCompact (closedBall x₀ (a : ℝ)) := isCompact_closedBall x₀ a
  have hDc : ContinuousOn (fderiv ℝ f) U := hfU.continuousOn_fderiv_of_isOpen hUo le_rfl
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hDc.mono haU)
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ z ∈ closedBall x₀ (a : ℝ), ‖fderiv ℝ f z‖ ≤ M := fun z hz =>
    (hM₀ z hz).trans (le_max_left _ _)
  set ε' : ℝ := min ε (1 / (M * 2 + 1)) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hsub : Icc (0 : ℝ) ε' ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) hε'ε
  have hsub2 : Icc (-ε') ε' ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) hε'ε
  have hcontα : ∀ x ∈ closedBall x₀ (r : ℝ), ContinuousOn (α x) (Icc 0 ε) := fun x hx t ht =>
    ((hα x hx).2.1 t ⟨by linarith [ht.1], ht.2⟩).continuousWithinAt.mono
      (Icc_subset_Icc (by linarith) le_rfl)
  -- the variational equation along each curve
  have hlin : ∀ x ∈ ball x₀ (r : ℝ), ∃ Y : ℝ → E →L[ℝ] E, Y 0 = 1 ∧
      ∀ t ∈ Icc 0 ε', HasDerivWithinAt Y (fderiv ℝ f (α x t) ∘L Y t) (Icc 0 ε') t := by
    intro x hx
    have hx' : x ∈ closedBall x₀ (r : ℝ) := ball_subset_closedBall hx
    have hA : ∀ Z : E →L[ℝ] E, ContinuousOn
        (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ f (α x t)) Z) (Icc 0 ε) := by
      intro Z
      simp only [ContinuousLinearMap.compL_apply]
      exact (hDc.comp (hcontα x hx') (fun t _ => haU ((hα x hx').2.2 t))).clm_comp
        continuousOn_const
    have hAM : ∀ t ∈ Icc (0 : ℝ) ε, ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ f (α x t))‖ ≤ M := by
      intro t _
      calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ f (α x t))‖
          ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ f (α x t)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * M := by
            gcongr
            · exact ContinuousLinearMap.norm_compL_le ℝ E E E
            · exact hMb _ ((hα x hx').2.2 t)
        _ = M := one_mul M
    have hτ : ε' * (M * (‖(1 : E →L[ℝ] E)‖ + 1) + 1) ≤ 1 := by
      have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      have h2 : ε' ≤ 1 / (M * 2 + 1) := min_le_right _ _
      calc ε' * (M * (‖(1 : E →L[ℝ] E)‖ + 1) + 1) ≤ (1 / (M * 2 + 1)) * (M * 2 + 1) := by
            gcongr
            linarith
        _ = 1 := by field_simp
    obtain ⟨Y, hY0, hY⟩ := exists_linearODE_solution
      (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ f (α x t))) hε hA hAM
      (1 : E →L[ℝ] E) hε'0 hε'ε hτ
    exact ⟨Y, hY0, fun t ht => by simpa [ContinuousLinearMap.compL_apply] using hY t ht⟩
  choose Y hY using hlin
  set Y' : E → ℝ → E →L[ℝ] E := fun x =>
    if hx : x ∈ ball x₀ (r : ℝ) then Y x hx else fun _ => 1 with hY'
  refine ⟨U, hUo, hx₀U, hUs, hfU, r, hr, ε', hε'0, α, Y', fun x hx => ?_, fun x hx => ?_⟩
  · exact ⟨(hα x hx).1, fun t ht => ((hα x hx).2.1 t (hsub2 ht)).mono hsub2,
      fun t => haU ((hα x hx).2.2 t)⟩
  · have hYx : Y' x = Y x hx := by simp only [Y', dif_pos hx]
    rw [hYx]
    refine ⟨(hY x hx).1, (hY x hx).2, ?_⟩
    -- the core lemma on the ball `closedBall x ρ ⊆ closedBall x₀ r`
    set ρ : ℝ := r - dist x x₀ with hρ
    have hρ0 : 0 < ρ := by
      have := mem_ball.mp hx
      linarith
    have hball : closedBall x ρ ⊆ closedBall x₀ (r : ℝ) :=
      closedBall_subset_closedBall' (by rw [hρ]; linarith)
    exact hasFDerivAt_flow_of_variational hUo hfU hKc haU hρ0 hε'0
      (fun y hy => (hα y (hball hy)).1)
      (fun y hy t ht => ((hα y (hball hy)).2.1 t (hsub ht)).mono hsub)
      (fun y hy t _ => (hα y (hball hy)).2.2 t)
      (L' := L') (fun t ht => (hL' t (hsub ht)).mono hball)
      (hY x hx).1 (hY x hx).2

/-- ★ **The flow of a small time-dependent field, up to time `T`, with its variational solution
and its Grönwall estimate.** Let `f t` be differentiable on an open `U ⊇ closedBall x₀ a` for
`t ∈ [0, T]`, with `f` and `(t, z) ↦ D(f t)(z)` continuous on `[0, T] × U`,
`‖D(f t)(z)‖ ≤ M` on `[0, T] × closedBall x₀ a` with `M T ≤ 1/2`, and `f t x₀ = 0`. Then every
`x ∈ closedBall x₀ (a/2)` has a trajectory on `[0, T]` confined to `closedBall x₀ a`, two
trajectories separate by at most `e^{M t}` times their initial distance, for
`x ∈ ball x₀ (a/2)` the time-`t` map is differentiable at `x` with derivative the variational
solution `Y x t`, and `x ↦ Y x t` is continuous on the half-ball (so the time-`t` map is `C¹`
there). (Picard–Lindelöf on `[0, T]` directly: the field is `M a`-bounded and `M`-Lipschitz on
the ball, and `M a T ≤ a/2`; the continuity is `dist_le_of_linearODE_coeff_close` with the
uniform continuity of `(t, z) ↦ D(f t)(z)` on `[0, T] × closedBall x₀ a` and the Grönwall
separation.) -/
theorem exists_flow_hasFDerivAt_of_norm_fderiv_le
    {f : ℝ → E → E} {x₀ : E} {a T M : ℝ} (ha : 0 < a) (hT : 0 < T)
    {U : Set E} (hU : IsOpen U) (haU : closedBall x₀ a ⊆ U)
    (hfc : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ U))
    (hfd : ∀ t ∈ Icc 0 T, ∀ z ∈ U, HasFDerivAt (f t) (fderiv ℝ (f t) z) z)
    (hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Icc 0 T ×ˢ U))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Icc 0 T, ∀ z ∈ closedBall x₀ a, ‖fderiv ℝ (f t) z‖ ≤ M)
    (hMT : M * T ≤ 1 / 2) (hf0 : ∀ t ∈ Icc 0 T, f t x₀ = 0) :
    ∃ α : E → ℝ → E, ∃ Y : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ closedBall x₀ (a / 2), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f t (α x t)) (Icc 0 T) t) ∧
        ∀ t, α x t ∈ closedBall x₀ a) ∧
      (∀ x ∈ closedBall x₀ (a / 2), ∀ y ∈ closedBall x₀ (a / 2), ∀ t ∈ Icc 0 T,
        dist (α x t) (α y t) ≤ dist x y * Real.exp (M * t)) ∧
      (∀ x ∈ ball x₀ (a / 2), Y x 0 = 1 ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (Y x) (fderiv ℝ (f t) (α x t) ∘L Y x t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (Y x t) x) ∧
      ∀ t ∈ Icc 0 T, ContinuousOn (fun x => Y x t) (ball x₀ (a / 2)) := by
  classical
  -- Lipschitz and norm bounds on the ball
  have hlipf : ∀ t ∈ Icc (0 : ℝ) T, LipschitzOnWith ⟨M, hM0⟩ (f t) (closedBall x₀ a) := by
    intro t ht
    refine (convex_closedBall x₀ a).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hfd t ht z (haU hz)).differentiableAt) (fun z hz => ?_)
    exact NNReal.coe_le_coe.mp (hM t ht z hz)
  have hnormf : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ closedBall x₀ a, ‖f t z‖ ≤ M * a := by
    intro t ht z hz
    have := (hlipf t ht).dist_le_mul z hz x₀ (mem_closedBall_self ha.le)
    rw [hf0 t ht, dist_zero_right, dist_eq_norm] at this
    calc ‖f t z‖ ≤ M * ‖z - x₀‖ := this
      _ ≤ M * a := by gcongr; exact mem_closedBall_iff_norm.mp hz
  -- Picard–Lindelöf on `[0, T]`
  have hpl : IsPicardLindelof f (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT.le⟩⟩ x₀ ⟨a, ha.le⟩
      ⟨a / 2, by positivity⟩ ⟨M * a, by positivity⟩ ⟨M, hM0⟩ := by
    refine ⟨hlipf, ?_, ?_, ?_⟩
    · intro z hz
      exact hfc.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, haU hz⟩
    · intro t ht z hz
      exact hnormf t ht z hz
    · show M * a * max (T - 0) (0 - 0) ≤ a - a / 2
      rw [sub_zero, sub_zero, max_eq_left hT.le]
      nlinarith
  obtain ⟨α, hα, L', hL'⟩ :=
    hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem
  -- the trajectories are continuous
  have hcontα : ∀ x ∈ closedBall x₀ (a / 2), ContinuousOn (α x) (Icc 0 T) := fun x hx t ht =>
    ((hα x hx).2.1 t ht).continuousWithinAt
  have hIci : ∀ s ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝[≥] s := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  -- Grönwall
  have hgron : ∀ x ∈ closedBall x₀ (a / 2), ∀ y ∈ closedBall x₀ (a / 2), ∀ t ∈ Icc 0 T,
      dist (α x t) (α y t) ≤ dist x y * Real.exp (M * t) := by
    intro x hx y hy t ht
    have := dist_le_of_trajectories_ODE_of_mem (v := f) (s := fun _ => closedBall x₀ a)
      (K := ⟨M, hM0⟩) (f := α x) (g := α y) (a := 0) (b := T) (δ := dist x y)
      (fun s hs => hlipf s (Ico_subset_Icc_self hs)) (hcontα x hx)
      (fun s hs => ((hα x hx).2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
      (fun s _ => (hα x hx).2.2 s) (hcontα y hy)
      (fun s hs => ((hα y hy).2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
      (fun s _ => (hα y hy).2.2 s) (by rw [(hα x hx).1, (hα y hy).1]) t ht
    rw [sub_zero] at this
    exact this
  -- the variational equation along each curve
  have hlin : ∀ x ∈ ball x₀ (a / 2), ∃ Y : ℝ → E →L[ℝ] E, Y 0 = 1 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ (f t) (α x t) ∘L Y t) (Icc 0 T) t := by
    intro x hx
    have hx' : x ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hx
    have hA : ∀ Z : E →L[ℝ] E, ContinuousOn
        (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t)) Z) (Icc 0 T) := by
      intro Z
      simp only [ContinuousLinearMap.compL_apply]
      have hD : ContinuousOn (fun t => fderiv ℝ (f t) (α x t)) (Icc 0 T) :=
        hDc.comp (continuousOn_id.prodMk (hcontα x hx'))
          fun t ht => ⟨ht, haU ((hα x hx').2.2 t)⟩
      exact hD.clm_comp continuousOn_const
    have hAM : ∀ t ∈ Icc (0 : ℝ) T,
        ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))‖ ≤ M := by
      intro t ht
      calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))‖
          ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ (f t) (α x t)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * M := by
            gcongr
            · exact ContinuousLinearMap.norm_compL_le ℝ E E E
            · exact hM t ht _ ((hα x hx').2.2 t)
        _ = M := one_mul M
    have hτ : T * (M * (‖(1 : E →L[ℝ] E)‖ + 1)) ≤ 1 := by
      have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      nlinarith [norm_nonneg (1 : E →L[ℝ] E)]
    obtain ⟨Y, hY0, hY⟩ := exists_linearODE_solution_of_le
      (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (f t) (α x t))) hT hA hAM
      (1 : E →L[ℝ] E) hτ
    exact ⟨Y, hY0, fun t ht => by simpa [ContinuousLinearMap.compL_apply] using hY t ht⟩
  choose Y hY using hlin
  set Y' : E → ℝ → E →L[ℝ] E := fun x =>
    if hx : x ∈ ball x₀ (a / 2) then Y x hx else fun _ => 1 with hY'
  refine ⟨α, Y', fun x hx => ⟨(hα x hx).1, (hα x hx).2.1, (hα x hx).2.2⟩, hgron,
    fun x hx => ?_, ?_⟩
  · have hYx : Y' x = Y x hx := by simp only [Y', dif_pos hx]
    rw [hYx]
    refine ⟨(hY x hx).1, (hY x hx).2, ?_⟩
    set ρ : ℝ := a / 2 - dist x x₀ with hρ
    have hρ0 : 0 < ρ := by
      have := mem_ball.mp hx
      linarith
    have hball : closedBall x ρ ⊆ closedBall x₀ (a / 2) :=
      closedBall_subset_closedBall' (by rw [hρ]; linarith)
    exact hasFDerivAt_flow_of_variational_timeDependent hU hT hfd hDc (isCompact_closedBall x₀ a)
      haU hρ0 (fun y hy => (hα y (hball hy)).1)
      (fun y hy t ht => (hα y (hball hy)).2.1 t ht)
      (fun y hy t _ => (hα y (hball hy)).2.2 t)
      (L' := L') (fun t ht => (hL' t ht).mono hball)
      (hY x hx).1 (hY x hx).2
  · -- continuous dependence of the variational solution on the initial point
    have hunif : UniformContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (Icc (0 : ℝ) T ×ˢ closedBall x₀ a) :=
      (isCompact_Icc.prod (isCompact_closedBall x₀ a)).uniformContinuousOn_of_continuous
        (hDc.mono (prod_mono subset_rfl haU))
    have hAM : ∀ z ∈ ball x₀ (a / 2), ∀ s ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (f s) (α z s)‖ ≤ M :=
      fun z hz s hs => hM s hs _ ((hα z (ball_subset_closedBall hz)).2.2 s)
    intro t ht
    rw [Metric.continuousOn_iff]
    intro x hx ε hε
    set C : ℝ := Real.exp (M * T) * (T * Real.exp (M * T)) with hC
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    have hC1 : C + 1 ≠ 0 := by positivity
    set ε₁ : ℝ := ε / (2 * (C + 1)) with hε₁
    have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
    obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.uniformContinuousOn_iff.mp hunif ε₁ hε₁0
    refine ⟨δ₁ / Real.exp (M * T), by positivity, fun y hy hyx => ?_⟩
    have hx' : x ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hx
    have hy' : y ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hy
    -- the coefficients of the two variational equations are uniformly close
    have hAB : ∀ s ∈ Icc (0 : ℝ) T,
        ‖fderiv ℝ (f s) (α y s) - fderiv ℝ (f s) (α x s)‖ ≤ ε₁ := by
      intro s hs
      have h1 : dist (α y s) (α x s) < δ₁ :=
        calc dist (α y s) (α x s) ≤ dist y x * Real.exp (M * s) := hgron y hy' x hx' s hs
          _ ≤ dist y x * Real.exp (M * T) := by gcongr; exact hs.2
          _ < δ₁ / Real.exp (M * T) * Real.exp (M * T) := by gcongr
          _ = δ₁ := div_mul_cancel₀ _ (Real.exp_pos _).ne'
      have := hδ₁c (s, α y s) ⟨hs, (hα y hy').2.2 s⟩ (s, α x s) ⟨hs, (hα x hx').2.2 s⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact h1)
      rw [dist_eq_norm] at this
      exact this.le
    show dist (Y' y t) (Y' x t) < ε
    have hYx : Y' x = Y x hx := by simp only [Y', dif_pos hx]
    have hYy : Y' y = Y y hy := by simp only [Y', dif_pos hy]
    rw [hYy, hYx, dist_comm]
    calc dist (Y x hx t) (Y y hy t)
        ≤ ε₁ * Real.exp (M * T) * (T * Real.exp (M * T)) :=
          dist_le_of_linearODE_coeff_close hM0 hε₁0.le (hAM x hx) (hAM y hy) hAB
            (hY x hx).1 (hY x hx).2 (hY y hy).1 (hY y hy).2 t ht
      _ = ε₁ * C := by rw [hC]; ring
      _ ≤ ε₁ * (C + 1) := by nlinarith [hε₁0.le, hC0]
      _ = ε / 2 := by rw [hε₁]; field_simp
      _ < ε := by linarith

/-! ### The flat Lie derivative and Liouville -/

/-- The flat Lie derivative of a 2-form `Ω` along a vector field `X`, as a bilinear expression:
`(L_X Ω)(z)(m) = DΩ(z)(X z)(m) + Ω(z)(DX(z) m₀, m₁) + Ω(z)(m₀, DX(z) m₁)`. -/
noncomputable def flatLieDeriv (X : E → E) (Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E)
    (m : Fin 2 → E) : ℝ :=
  fderiv ℝ Ω z (X z) m + ∑ i, Ω z (Function.update m i (fderiv ℝ X z (m i)))

omit [CompleteSpace E] [ProperSpace E] in
/-- **Flat transport for a time-dependent form and field.** If `Ω t` is a family of 2-forms, jointly
differentiable in `(t, z)` on `[0, T] × U`, and `∂ₜΩ + L_{f t} Ω t = 0` there — as the combined
condition `DΩ(t, z)(1, f t z) m + ∑ᵢ Ω t z (update m i (D(f t)(z) (m i))) = 0` — then along any
integral curve `α` of `f` with its variational solution `Y`, `Ω t (α t) (Y t ∘ m) = Ω 0 (α 0) m`
(`constant_of_has_deriv_right_zero` on the product-rule derivative). -/
theorem form_invariant_of_flatLieDeriv_eq_zero_timeDependent
    {f : ℝ → E → E} {U : Set E} {T : ℝ}
    {Ω : ℝ → E → E [⋀^Fin 2]→L[ℝ] ℝ}
    (hΩ : ∀ t ∈ Icc 0 T, ∀ z ∈ U, DifferentiableAt ℝ (Function.uncurry Ω) (t, z))
    (hL : ∀ t ∈ Icc 0 T, ∀ z ∈ U, ∀ m : Fin 2 → E,
      fderiv ℝ (Function.uncurry Ω) (t, z) (1, f t z) m
        + ∑ i, Ω t z (Function.update m i (fderiv ℝ (f t) z (m i))) = 0)
    {α : ℝ → E} {x : E} (hα0 : α 0 = x)
    (hαd : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f t (α t)) (Icc 0 T) t)
    (hαU : ∀ t ∈ Icc 0 T, α t ∈ U)
    {Y : ℝ → E →L[ℝ] E} (hY0 : Y 0 = 1)
    (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ (f t) (α t) ∘L Y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ m : Fin 2 → E, Ω t (α t) (fun i => Y t (m i)) = Ω 0 x m := by
  intro t ht m
  have hderiv : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun s => Ω s (α s) (fun i => Y s (m i))) 0 (Icc 0 T) s := by
    intro s hs
    have hcurve : HasDerivWithinAt (fun s => (s, α s)) ((1 : ℝ), f s (α s)) (Icc 0 T) s :=
      (hasDerivWithinAt_id s _).prodMk (hαd s hs)
    have h1' := (hΩ s hs _ (hαU s hs)).hasFDerivAt.comp_hasDerivWithinAt s hcurve
    have h1 : HasDerivWithinAt (fun s => Ω s (α s))
        (fderiv ℝ (Function.uncurry Ω) (s, α s) (1, f s (α s))) (Icc 0 T) s := h1'
    have h2 : ∀ i, HasDerivWithinAt (fun s => Y s (m i))
        ((fderiv ℝ (f s) (α s) ∘L Y s) (m i)) (Icc 0 T) s := fun i => by
      simpa using (hYd s hs).clm_apply (hasDerivWithinAt_const s (Icc (0 : ℝ) T) (m i))
    have h3 := (hasDerivWithinAt_iff_hasFDerivWithinAt.mp h1).continuousAlternatingMap_apply
      (g := fun i s => Y s (m i))
      (g' := fun i => (1 : ℝ →L[ℝ] ℝ).smulRight ((fderiv ℝ (f s) (α s) ∘L Y s) (m i)))
      (fun i => hasDerivWithinAt_iff_hasFDerivWithinAt.mp (h2 i))
    have h4 := h3.hasDerivWithinAt
    have := hL s hs _ (hαU s hs) (fun i => Y s (m i))
    convert h4 using 1
    all_goals try rfl
    simp only [add_apply, ContinuousLinearMap.comp_apply, sum_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply, one_smul,
      one_apply_eq_self, ContinuousAlternatingMap.apply_apply,
      ContinuousAlternatingMap.toContinuousLinearMap_apply]
    linarith [this]
  have hcont : ContinuousOn (fun s => Ω s (α s) (fun i => Y s (m i))) (Icc 0 T) :=
    fun s hs => (hderiv s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun s hs =>
    (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) t ht
  simpa [hα0, hY0] using hconst

omit [CompleteSpace E] [ProperSpace E] in
/-- **Flat Liouville.** If the flat Lie derivative of a `C¹` 2-form along a `C¹` field vanishes on
an open set, then along any integral curve `α` with the variational solution `Y`, the pullback of
the form is constant: `Ω (α t) (Y t ∘ m) = Ω (α 0) m`
(`form_invariant_of_flatLieDeriv_eq_zero_timeDependent` for constant families). -/
theorem form_invariant_of_flatLieDeriv_eq_zero
    {f : E → E} {U : Set E} (hU : IsOpen U)
    {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hΩ : ContDiffOn ℝ 1 Ω U)
    (hL : ∀ z ∈ U, ∀ m, flatLieDeriv f Ω z m = 0)
    {α : ℝ → E} {x : E} {T : ℝ} (hα0 : α 0 = x)
    (hαd : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f (α t)) (Icc 0 T) t)
    (hαU : ∀ t ∈ Icc 0 T, α t ∈ U)
    {Y : ℝ → E →L[ℝ] E} (hY0 : Y 0 = 1)
    (hYd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (fderiv ℝ f (α t) ∘L Y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ m : Fin 2 → E, Ω (α t) (fun i => Y t (m i)) = Ω x m := by
  have hΩd : ∀ z ∈ U, HasFDerivAt Ω (fderiv ℝ Ω z) z := fun z hz =>
    ((hΩ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hunc : ∀ t z, z ∈ U → HasFDerivAt (Function.uncurry fun _ : ℝ => Ω)
      (fderiv ℝ Ω z ∘L ContinuousLinearMap.snd ℝ ℝ E) (t, z) :=
    fun t z hz => (hΩd z hz).comp (t, z) hasFDerivAt_snd
  refine form_invariant_of_flatLieDeriv_eq_zero_timeDependent (f := fun _ => f) (U := U) (T := T)
    (Ω := fun _ => Ω) (fun t _ z hz => (hunc t z hz).differentiableAt)
    (fun t _ z hz m => ?_) hα0 hαd hαU hY0 hYd
  have h := hL z hz m
  simp only [flatLieDeriv] at h
  rw [(hunc t z hz).fderiv]
  simpa using h

/-- ★★ **Flat Liouville for the local flow of a `C¹` field.** If the flat Lie derivative of a `C¹`
2-form `Ω` along a `C¹` field `f` vanishes near `x₀`, the local flow `α` of `f` near `x₀` is
differentiable in the initial point and pulls `Ω` back to itself:
`(Ω (α x t)).compContinuousLinearMap (D(α · t) x) = Ω x`. -/
theorem ContDiffAt.exists_localFlow_form_invariant {f : E → E} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀) {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hΩ : ContDiffAt ℝ 1 Ω x₀)
    (hL : ∀ᶠ z in 𝓝 x₀, ∀ m, flatLieDeriv f Ω z m = 0) {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∃ Y : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ closedBall x₀ r, α x 0 = x ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧
        ∀ t, α x t ∈ s) ∧
      ∀ x ∈ ball x₀ r, ∀ t ∈ Icc 0 ε, HasFDerivAt (α · t) (Y x t) x ∧
        (Ω (α x t)).compContinuousLinearMap (Y x t) = Ω x := by
  obtain ⟨V, hVo, hx₀V, hΩV⟩ := hΩ.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hΩV
  obtain ⟨W, hW, hLW⟩ := Filter.eventually_iff_exists_mem.mp hL
  obtain ⟨U, hUo, hx₀U, hUs, hfU, r, hr, ε, hε, α, Y, hα, hY⟩ :=
    hf.exists_localFlow_hasFDerivAt (s := V ∩ W ∩ s)
      (inter_mem (inter_mem (hVo.mem_nhds hx₀V) hW) hs)
  refine ⟨r, hr, ε, hε, α, Y, fun x hx => ⟨(hα x hx).1, (hα x hx).2.1,
    fun t => (hUs ((hα x hx).2.2 t)).2⟩, fun x hx t ht => ?_⟩
  refine ⟨(hY x hx).2.2 t ht, ?_⟩
  have hx' : x ∈ closedBall x₀ r := ball_subset_closedBall hx
  have hinv := form_invariant_of_flatLieDeriv_eq_zero hUo (hΩV.mono fun z hz => (hUs hz).1.1)
    (fun z hz m => hLW z (hUs hz).1.2 m) (hα x hx').1
    (fun t ht => ((hα x hx').2.1 t (Icc_subset_Icc (by linarith) le_rfl ht)).mono
      (Icc_subset_Icc (by linarith) le_rfl))
    (fun t _ => (hα x hx').2.2 t)
    (hY x hx).1 (hY x hx).2.1 t ht
  ext m
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact hinv m

end Flat
