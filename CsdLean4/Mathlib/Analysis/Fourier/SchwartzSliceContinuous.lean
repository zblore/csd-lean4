/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzPartialIntegral
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzSlice
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Slicing is Lipschitz in the slice parameter

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #123, out of #121(i).

★★★ `SchwartzMap.lipschitz_seminorm_slice` — **each Schwartz seminorm of `slice K e − slice K e₀` is
at most `‖e − e₀‖` times one seminorm of `K`**, so ★★★ `SchwartzMap.continuous_slice`: the slice
family `e ↦ slice K e` is continuous into `𝓢(F, G)` for the Schwartz topology. #121(i) proved slicing
continuous **in the kernel** (`sliceCLM` is a continuous linear map for each fixed `e`), which is what
transfers theorems; this is the other direction, and the row recorded it as a genuinely different
statement. It is.

## The route the row recorded, and what it cost

* ★★ `iteratedFDeriv_comp_inr` — the derivatives of a slice are the kernel's derivatives
  precomposed with the inclusion `w ↦ (e, w)`. This is the mirror of #126(ii)'s
  `iteratedFDeriv_comp_inl` and was the first of the two pieces the row named as needed;
* ★★ `norm_fderiv_iteratedFDeriv_comp_inl_le` — the second: `e ↦ ∂ⁿK(e, w)` is differentiable with
  derivative bounded by `‖∂ⁿ⁺¹K(e, w)‖`, which is `K`'s decay **at one order higher**, exactly as the
  row predicted;
* ★★★ `lipschitz_seminorm_slice` — the mean value inequality, with the weight handled by a **case
  split** on whether it vanishes. Weighting the map *before* the mean value step is the
  mathematically natural move — the derivative bound `‖w‖ᵏ‖∂ⁿ⁺¹K(u, w)‖ ≤ 𝒮_{k,n+1}(K)` is then
  uniform in both variables — but it puts a scalar `smul` on a space of continuous multilinear maps,
  where the `NormSMulClass` instance the norm computation needs is absent at this pin. The case split
  costs two lines and needs no instances.

**The row said "locally Lipschitz"; it is globally Lipschitz.** The derivative bound is a seminorm of
`K`, which does not depend on the base point, so no localisation is needed and the estimate holds
between any two parameters.

## Honest scope

⚠️ **Nothing is gated on this.** The row records it because #121(i) names it and because a
symbol-valued calculus would want it; #121(ii) goes by #124 alone. It is here because it was
*unblocked*, not because something waits on it.

⚠️ **Not a curry.** As #123 was corrected on 2026-10-07, `𝓢(E, 𝓢(F, G))` does not typecheck —
`SchwartzMap` needs a normed target and Schwartz space is Fréchet — so this is a continuity statement
about one map, with no larger object behind it. In particular the slice family is **not** claimed to
be a Schwartz function of `e`, which would need every derivative in `e` and a weight, and is a
different statement.

⚠️ **Lipschitz in each seminorm, not for a norm.** `𝓢(F, G)` has no norm; the conclusion is the
seminorm-wise estimate and the continuity it gives, not `LipschitzWith`.

References: [`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i), `slice`, `sliceCLM`),
[`SchwartzPartialIntegral.lean`](SchwartzPartialIntegral.lean) (#126(ii), `iteratedFDeriv_comp_inl`,
whose mirror this is); `specs/BACKLOG.md` #123, #121.
-/

@[expose] public section

open SchwartzMap

noncomputable section

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [SMulCommClass ℝ ℂ G]

/-! ### The derivatives of a slice -/

omit [NormedSpace ℂ G] [SMulCommClass ℝ ℂ G] in
/-- ★★ The iterated chain rule through the slice inclusion `w ↦ (e, w)` — the mirror of #126(ii)'s
`iteratedFDeriv_comp_inl`, and the first piece #123 named. -/
theorem iteratedFDeriv_comp_inr {K : E × F → G} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (e : E) (k : ℕ)
    (w : F) :
    iteratedFDeriv ℝ k (fun v => K (e, v)) w
      = (iteratedFDeriv ℝ k K (e, w)).compContinuousLinearMap
          fun _ => ContinuousLinearMap.inr ℝ E F := by
  have hfun : (fun v : F => K (e, v))
      = (fun p : E × F => K ((e, (0 : F)) + p)) ∘ (ContinuousLinearMap.inr ℝ E F) := by
    funext v
    simp
  have hKc : ContDiff ℝ (⊤ : ℕ∞) fun p : E × F => K ((e, (0 : F)) + p) :=
    hK.comp (contDiff_const.add contDiff_id)
  have hcr : iteratedFDeriv ℝ k
        ((fun p : E × F => K ((e, (0 : F)) + p)) ∘ (ContinuousLinearMap.inr ℝ E F)) w
      = (iteratedFDeriv ℝ k (fun p : E × F => K ((e, (0 : F)) + p))
          (ContinuousLinearMap.inr ℝ E F w)).compContinuousLinearMap
            fun _ => ContinuousLinearMap.inr ℝ E F :=
    (ContinuousLinearMap.inr ℝ E F).iteratedFDeriv_comp_right hKc w (by exact_mod_cast le_top)
  rw [hfun, hcr, iteratedFDeriv_comp_add_left]
  congr 2
  simp

omit [NormedSpace ℂ G] [SMulCommClass ℝ ℂ G] in
/-- The slice inclusion is short, so no power of it appears in any bound. -/
theorem norm_inr_le_one : ‖ContinuousLinearMap.inr ℝ E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  simp [Prod.norm_def]

/-! ### Differentiating in the parameter -/

omit [NormedSpace ℂ G] [SMulCommClass ℝ ℂ G] in
/-- The inclusion of the first factor is short too. -/
theorem norm_inl_le_one' : ‖ContinuousLinearMap.inl ℝ E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => ?_
  simp [Prod.norm_def]

omit [NormedSpace ℂ G] [SMulCommClass ℝ ℂ G] in
/-- ★★ **The second piece #123 named**: the kernel's `n`-th derivative is differentiable in the
parameter, with derivative bounded by its `(n+1)`-st — `K`'s decay at one order higher. -/
theorem norm_fderiv_iteratedFDeriv_comp_inl_le {K : E × F → G} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (n : ℕ)
    (e : E) (w : F) :
    ‖fderiv ℝ (fun u : E => iteratedFDeriv ℝ n K (u, w)) e‖
      ≤ ‖iteratedFDeriv ℝ (n + 1) K (e, w)‖ := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n K) :=
    hK.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hslice : HasFDerivAt (fun u : E => (u, w)) (ContinuousLinearMap.inl ℝ E F) e := by
    simpa using ((ContinuousLinearMap.inl ℝ E F).hasFDerivAt (x := e)).add_const ((0 : E), w)
  have hcomp : HasFDerivAt (fun u : E => iteratedFDeriv ℝ n K (u, w))
      ((fderiv ℝ (iteratedFDeriv ℝ n K) (e, w)).comp (ContinuousLinearMap.inl ℝ E F)) e :=
    (hΦ.differentiable (by simp) (e, w)).hasFDerivAt.comp e hslice
  rw [hcomp.fderiv]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  calc ‖fderiv ℝ (iteratedFDeriv ℝ n K) (e, w)‖ * ‖ContinuousLinearMap.inl ℝ E F‖
      ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n K) (e, w)‖ * 1 :=
        mul_le_mul_of_nonneg_left norm_inl_le_one'
          (norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ n K) (e, w)))
    _ = ‖iteratedFDeriv ℝ (n + 1) K (e, w)‖ := by
        rw [mul_one, norm_fderiv_iteratedFDeriv]

/-! ### The Lipschitz estimate -/

/-- ★★★ **Each seminorm of the slice difference is `‖e − e₀‖` times one seminorm of the kernel** —
the kernel's, at one order higher in the derivative. The mean value inequality is applied to the
**weighted** map `u ↦ ‖w‖ᵏ·∂ⁿK(u, w)`, whose derivative bound `‖w‖ᵏ‖∂ⁿ⁺¹K(u, w)‖ ≤ 𝒮_{k,n+1}(K)` is
uniform in both `u` and `w`; weighting afterwards would have forced a division by `‖w‖ᵏ`. -/
theorem norm_pow_mul_norm_iteratedFDeriv_slice_sub_le (K : 𝓢(E × F, G)) (k n : ℕ) (e₀ e : E)
    (w : F) :
    ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (slice K e - slice K e₀) w‖
      ≤ SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖ := by
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (K : E × F → G) := K.smooth'
  have hS0 : (0 : ℝ) ≤ SchwartzMap.seminorm ℂ k (n + 1) K := apply_nonneg _ _
  -- the slice difference is the kernel difference precomposed, so its norm is no larger
  have hcoe : ∀ u : E, iteratedFDeriv ℝ n (slice K u : F → G) w
      = (iteratedFDeriv ℝ n (K : E × F → G) (u, w)).compContinuousLinearMap
          fun _ => ContinuousLinearMap.inr ℝ E F := by
    intro u
    have hslice : (slice K u : F → G) = fun v => (K : E × F → G) (u, v) := by
      funext v
      rw [slice_apply]
    rw [hslice]
    exact iteratedFDeriv_comp_inr hKsm u n w
  have hprod : ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ E F‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_inr_le_one
  have hdrop : ‖iteratedFDeriv ℝ n (slice K e - slice K e₀) w‖
      ≤ ‖iteratedFDeriv ℝ n (K : E × F → G) (e, w)
          - iteratedFDeriv ℝ n (K : E × F → G) (e₀, w)‖ := by
    have hstep : iteratedFDeriv ℝ n (slice K e - slice K e₀) w
        = (iteratedFDeriv ℝ n (K : E × F → G) (e, w)
            - iteratedFDeriv ℝ n (K : E × F → G) (e₀, w)).compContinuousLinearMap
              fun _ => ContinuousLinearMap.inr ℝ E F := by
      have hsub : iteratedFDeriv ℝ n (slice K e - slice K e₀) w
          = iteratedFDeriv ℝ n (slice K e : F → G) w
            - iteratedFDeriv ℝ n (slice K e₀ : F → G) w := by
        refine iteratedFDeriv_sub_apply ?_ ?_
        · exact ((slice K e).smooth' : ContDiff ℝ (⊤ : ℕ∞) _).contDiffAt.of_le
            (by exact_mod_cast le_top)
        · exact ((slice K e₀).smooth' : ContDiff ℝ (⊤ : ℕ∞) _).contDiffAt.of_le
            (by exact_mod_cast le_top)
      rw [hsub, hcoe e, hcoe e₀]
      ext m
      simp
    rw [hstep]
    refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
    calc ‖iteratedFDeriv ℝ n (K : E × F → G) (e, w)
            - iteratedFDeriv ℝ n (K : E × F → G) (e₀, w)‖
          * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ E F‖
        ≤ ‖iteratedFDeriv ℝ n (K : E × F → G) (e, w)
            - iteratedFDeriv ℝ n (K : E × F → G) (e₀, w)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = _ := mul_one _
  -- the parameter map is differentiable
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n (K : E × F → G)) :=
    hKsm.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hincl : ∀ u : E, HasFDerivAt (fun v : E => (v, w)) (ContinuousLinearMap.inl ℝ E F) u := by
    intro u
    simpa using ((ContinuousLinearMap.inl ℝ E F).hasFDerivAt (x := u)).add_const ((0 : E), w)
  have hdiffpt : ∀ u : E,
      DifferentiableAt ℝ (fun v : E => iteratedFDeriv ℝ n (K : E × F → G) (v, w)) u := fun u =>
    ((hΦ.differentiable (by simp) (u, w)).hasFDerivAt.comp u (hincl u)).differentiableAt
  -- the weight is either zero, when there is nothing to prove, or invertible
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ ‖w‖ ^ k) with hz | hpos
  · rw [← hz, zero_mul]
    exact mul_nonneg hS0 (norm_nonneg _)
  · have hbound : ∀ u : E,
        ‖fderiv ℝ (fun v : E => iteratedFDeriv ℝ n (K : E × F → G) (v, w)) u‖
          ≤ SchwartzMap.seminorm ℂ k (n + 1) K / ‖w‖ ^ k := by
      intro u
      rw [le_div_iff₀ hpos]
      calc ‖fderiv ℝ (fun v : E => iteratedFDeriv ℝ n (K : E × F → G) (v, w)) u‖ * ‖w‖ ^ k
          ≤ ‖iteratedFDeriv ℝ (n + 1) (K : E × F → G) (u, w)‖ * ‖w‖ ^ k :=
            mul_le_mul_of_nonneg_right (norm_fderiv_iteratedFDeriv_comp_inl_le hKsm n u w)
              (by positivity)
        _ = ‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (K : E × F → G) (u, w)‖ := by ring
        _ ≤ ‖((u, w) : E × F)‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (K : E × F → G) (u, w)‖ := by
            gcongr
            exact norm_snd_le ((u, w) : E × F)
        _ ≤ SchwartzMap.seminorm ℂ k (n + 1) K := SchwartzMap.le_seminorm ℂ k (n + 1) K ((u, w))
    have hmvt : ‖iteratedFDeriv ℝ n (K : E × F → G) (e, w)
          - iteratedFDeriv ℝ n (K : E × F → G) (e₀, w)‖
        ≤ SchwartzMap.seminorm ℂ k (n + 1) K / ‖w‖ ^ k * ‖e - e₀‖ :=
      convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun u _ => hdiffpt u)
        (fun u _ => hbound u) (Set.mem_univ e₀) (Set.mem_univ e)
    calc ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (slice K e - slice K e₀) w‖
        ≤ ‖w‖ ^ k * (SchwartzMap.seminorm ℂ k (n + 1) K / ‖w‖ ^ k * ‖e - e₀‖) :=
          mul_le_mul_of_nonneg_left (le_trans hdrop hmvt) (le_of_lt hpos)
      _ = SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖ := by
          field_simp

/-- ★★★ **The seminorm-wise Lipschitz estimate.** Each Schwartz seminorm of the slice difference is
at most `‖e − e₀‖` times *one* seminorm of the kernel, the same one at one order higher. The row said
"locally Lipschitz"; the bound does not depend on the base point, so it is **globally** Lipschitz. -/
theorem lipschitz_seminorm_slice (K : 𝓢(E × F, G)) (k n : ℕ) (e₀ e : E) :
    SchwartzMap.seminorm ℂ k n (slice K e - slice K e₀)
      ≤ SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖ := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ ?_ ?_
  · exact mul_nonneg (apply_nonneg _ _) (norm_nonneg _)
  · intro w
    exact norm_pow_mul_norm_iteratedFDeriv_slice_sub_le K k n e₀ e w

/-- ★★★ **Slicing is continuous in the slice parameter** for the Schwartz topology — #123's
statement. It falls straight out of the Lipschitz estimate, since a seminorm of the difference is
bounded by a constant times `‖e − e₀‖`. -/
theorem continuous_slice (K : 𝓢(E × F, G)) : Continuous fun e : E => slice K e := by
  rw [continuous_iff_continuousAt]
  intro e₀
  rw [ContinuousAt, (schwartz_withSeminorms ℂ F G).tendsto_nhds]
  intro i ε hε
  obtain ⟨k, n⟩ := i
  have hS0 : (0 : ℝ) ≤ SchwartzMap.seminorm ℂ k (n + 1) K := apply_nonneg _ _
  -- on a small enough ball the Lipschitz bound is below ε
  have hball : ∀ᶠ e in nhds e₀, ‖e - e₀‖ < ε / (SchwartzMap.seminorm ℂ k (n + 1) K + 1) := by
    have hpos : (0 : ℝ) < ε / (SchwartzMap.seminorm ℂ k (n + 1) K + 1) := by positivity
    have h := Metric.ball_mem_nhds e₀ hpos
    filter_upwards [h] with e he
    rwa [Metric.mem_ball, dist_eq_norm] at he
  filter_upwards [hball] with e he
  have hlip := lipschitz_seminorm_slice K k n e₀ e
  have hkey : SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖ < ε := by
    have hlt : SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖
        ≤ (SchwartzMap.seminorm ℂ k (n + 1) K + 1) * ‖e - e₀‖ := by
      refine mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hdiv : (SchwartzMap.seminorm ℂ k (n + 1) K + 1) * ‖e - e₀‖ < ε := by
      rw [← lt_div_iff₀' (by positivity)]
      exact he
    linarith
  calc (schwartzSeminormFamily ℂ F G (k, n)) (slice K e - slice K e₀)
      = SchwartzMap.seminorm ℂ k n (slice K e - slice K e₀) := rfl
    _ ≤ SchwartzMap.seminorm ℂ k (n + 1) K * ‖e - e₀‖ := hlip
    _ < ε := hkey

end SchwartzMap

end

end
