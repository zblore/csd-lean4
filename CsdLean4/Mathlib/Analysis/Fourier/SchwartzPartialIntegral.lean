/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Calculus.ContDiffParametricIntegralFDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrating out one variable preserves Schwartz space

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #126(ii), out of #122.

★★★ `SchwartzMap.integralLastCLM` — **`𝓢(E × ℝ, ℂ) →L[ℂ] 𝓢(E, ℂ)`, `G ↦ fun p => ∫ t, G (p, t)`.**
Mathlib has `SchwartzMap.integralCLM`, which integrates over the *whole* domain into a scalar, and
nothing that integrates out one variable: this is the two-variable gap #121 names, in its integral
form. It is what #126 needs, because a composite integral kernel is exactly one variable integrated
out of a product of two kernels.

## The two halves, and where each comes from

**Smoothness** is #124 (differentiation under the integral over a finite-dimensional parameter) and
**decay** is #126's gate in that file (`norm_iteratedFDeriv_integral_le`, the bound at every order).
What this file supplies is the bridge from Schwartz data to #124's directional hypotheses:

* ★ `fderiv_comp_inl` and ★★ `iteratedFDeriv_comp_inl` — the chain rule through the inclusion
  `y ↦ (y, t)`, with ★ `norm_iteratedFDeriv_comp_inl_le`: a derivative in the first factor is no
  bigger than the full derivative, because the inclusion has norm one;
* `prodDirDeriv` and ★★ `dirDeriv_eq_prodDirDeriv` — **the directional derivatives, viewed jointly in
  both variables.** This is what makes #124's measurability hypotheses dischargeable: as a function
  of the integration variable, a directional derivative in the parameter is a *slice of something
  jointly smooth* (★ `contDiff_prodDirDeriv`), hence continuous, hence measurable — including the
  operator-valued one (`hmeasD`), which #124's own scope note flags as unavoidable and which nothing
  had discharged before this file;
* ★★ `one_add_norm_pow_mul_norm_iteratedFDeriv_le` — **the weight transfer**: `G`'s decay at two
  orders apart gives `(1 + ‖p‖)ᴺ·‖∂ᵏG(p, t)‖ ≤ 2^(N+2)·S·(1 + t²)⁻¹` with `S` a *single* `Finset.sup`
  of `G`'s seminorms. The same two-order combination #122's decay half runs on, with the slots
  swapped, and in a form `SchwartzMap.mkCLM` can consume;
* ★ `one_add_norm_le_of_sub_norm_le` — the parameter weight moves between nearby points, which is
  what lets a bound family that is *constant on a ball* carry a weight evaluated at the ball's
  centre.

## Honest scope

⚠️ **One variable, and it is the last one.** `𝓢(E × F, ℂ) → 𝓢(E, ℂ)` for a general second factor `F`
is the same proof with `(1 + t²)⁻¹` replaced by an integrable profile on `F`; only `F = ℝ` is proved
here, because that is what a kernel composition integrates over and because the profile is where the
measure enters.

⚠️ **The constants are not sharp.** `2^(2N+2)·π` falls out of the route.

⚠️ **Nothing here is a Fubini statement.** That the iterated integral equals the double integral is a
separate step, and the consumer (#126) does it with Mathlib's `integral_integral_swap` rather than
anything in this file.

References: [`ContDiffParametricIntegralFDeriv.lean`](../Calculus/ContDiffParametricIntegralFDeriv.lean)
(#124 and #126's gate), [`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i), slicing),
[`WeylSmooth.lean`](WeylSmooth.lean) (#122, the same two-order decay combination);
`specs/BACKLOG.md` #126, #124, #122, #121.
-/

@[expose] public section

open MeasureTheory SchwartzMap Metric

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The inclusion of the first factor -/

/-- The chain rule through `y ↦ (y, t)`: every statement below moves between a derivative in the
first factor and the full derivative along it. -/
theorem fderiv_comp_inl {D : H × ℝ → E} (hD : Differentiable ℝ D) (x : H) (t : ℝ) :
    fderiv ℝ (fun y => D (y, t)) x = (fderiv ℝ D (x, t)).comp (ContinuousLinearMap.inl ℝ H ℝ) := by
  have h1 : HasFDerivAt (fun y : H => (y, t)) (ContinuousLinearMap.inl ℝ H ℝ) x := by
    simpa using ((ContinuousLinearMap.inl ℝ H ℝ).hasFDerivAt (x := x)).add_const ((0 : H), t)
  exact ((hD (x, t)).hasFDerivAt.comp x h1).fderiv

/-- ★★ The iterated chain rule through the inclusion: the derivative in the first factor is the full
derivative precomposed with `inl` in every slot. -/
theorem iteratedFDeriv_comp_inl {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D) (t : ℝ) (k : ℕ)
    (x : H) :
    iteratedFDeriv ℝ k (fun y => D (y, t)) x
      = (iteratedFDeriv ℝ k D (x, t)).compContinuousLinearMap
          fun _ => ContinuousLinearMap.inl ℝ H ℝ := by
  have hfun : (fun y : H => D (y, t))
      = (fun p : H × ℝ => D (((0 : H), t) + p)) ∘ (ContinuousLinearMap.inl ℝ H ℝ) := by
    funext y
    simp
  have hDc : ContDiff ℝ (⊤ : ℕ∞) fun p : H × ℝ => D (((0 : H), t) + p) :=
    hD.comp (contDiff_const.add contDiff_id)
  have hcr : iteratedFDeriv ℝ k
        ((fun p : H × ℝ => D (((0 : H), t) + p)) ∘ (ContinuousLinearMap.inl ℝ H ℝ)) x
      = (iteratedFDeriv ℝ k (fun p : H × ℝ => D (((0 : H), t) + p))
          (ContinuousLinearMap.inl ℝ H ℝ x)).compContinuousLinearMap
            fun _ => ContinuousLinearMap.inl ℝ H ℝ :=
    (ContinuousLinearMap.inl ℝ H ℝ).iteratedFDeriv_comp_right hDc x (by exact_mod_cast le_top)
  rw [hfun, hcr, iteratedFDeriv_comp_add_left]
  congr 2
  simp

/-- The inclusion has norm at most one, so no power of it appears in any bound. -/
theorem norm_inl_le_one : ‖ContinuousLinearMap.inl ℝ H ℝ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  simp [Prod.norm_def]

/-- ★ **A derivative in the first factor is no bigger than the full derivative.** -/
theorem norm_iteratedFDeriv_comp_inl_le {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D) (t : ℝ)
    (k : ℕ) (x : H) :
    ‖iteratedFDeriv ℝ k (fun y => D (y, t)) x‖ ≤ ‖iteratedFDeriv ℝ k D (x, t)‖ := by
  rw [iteratedFDeriv_comp_inl hD t k x]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℝ H ℝ‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_inl_le_one
  calc ‖iteratedFDeriv ℝ k D (x, t)‖ * ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℝ H ℝ‖
      ≤ ‖iteratedFDeriv ℝ k D (x, t)‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k D (x, t)‖ := mul_one _

/-! ### The directional derivatives, viewed in both variables

#124's hypotheses ask for the directional derivatives of `p ↦ G (p, t)` to be measurable **in `t`**,
including the operator-valued first one. Folding the inclusion into the recursion makes each of them
a slice of a jointly smooth function, which is what discharges those hypotheses. -/

/-- The directional derivatives in the first factor, as functions of both variables. -/
noncomputable def prodDirDeriv (D : H × ℝ → E) : List H → H × ℝ → E
  | [] => D
  | h :: hs => fun q => fderiv ℝ (prodDirDeriv D hs) q (h, 0)

/-- ★ Each of them is jointly smooth. -/
theorem contDiff_prodDirDeriv {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D) (hs : List H) :
    ContDiff ℝ (⊤ : ℕ∞) (prodDirDeriv D hs) := by
  induction hs with
  | nil => exact hD
  | cons h hs ih =>
      have hrw : prodDirDeriv D (h :: hs) = fun q => (fderiv ℝ (prodDirDeriv D hs) q) (h, 0) := rfl
      rw [hrw]
      exact (ih.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const

/-- ★★ **And they are #124's directional derivatives.** -/
theorem dirDeriv_eq_prodDirDeriv {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D) (hs : List H) :
    ∀ (x : H) (t : ℝ),
      dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs x t = prodDirDeriv D hs (x, t) := by
  induction hs with
  | nil => intro x t; rfl
  | cons h hs ih =>
      intro x t
      have heq : (fun y => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs y t)
          = fun y => prodDirDeriv D hs (y, t) := funext fun y => ih y t
      show fderiv ℝ (fun y => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs y t) x h
          = prodDirDeriv D (h :: hs) (x, t)
      rw [heq, fderiv_comp_inl ((contDiff_prodDirDeriv hD hs).differentiable (by simp)) x t]
      rfl

/-- The measurability hypothesis #124 asks for. -/
theorem aestronglyMeasurable_dirDeriv_prodMk {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D)
    (hs : List H) (x : H) :
    AEStronglyMeasurable
      (fun t => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs x t) volume := by
  have heq : (fun t => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs x t)
      = fun t => prodDirDeriv D hs (x, t) := funext fun t => dirDeriv_eq_prodDirDeriv hD hs x t
  rw [heq]
  exact ((contDiff_prodDirDeriv hD hs).continuous.comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- The operator-valued measurability hypothesis #124's scope note flags as unavoidable. The
inclusion is what makes it a continuity statement about a jointly smooth function. -/
theorem aestronglyMeasurable_fderiv_dirDeriv_prodMk {D : H × ℝ → E} (hD : ContDiff ℝ (⊤ : ℕ∞) D)
    (hs : List H) (x : H) :
    AEStronglyMeasurable
      (fun t => fderiv ℝ (fun y => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs y t) x)
      volume := by
  have heq : (fun t => fderiv ℝ (fun y => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs y t) x)
      = fun t => (fderiv ℝ (prodDirDeriv D hs) (x, t)).comp (ContinuousLinearMap.inl ℝ H ℝ) := by
    funext t
    have h2 : (fun y => dirDeriv (fun (p : H) (s : ℝ) => D (p, s)) hs y t)
        = fun y => prodDirDeriv D hs (y, t) := funext fun y => dirDeriv_eq_prodDirDeriv hD hs y t
    rw [h2]
    exact fderiv_comp_inl ((contDiff_prodDirDeriv hD hs).differentiable (by simp)) x t
  rw [heq]
  refine Continuous.aestronglyMeasurable ?_
  have hclm : Continuous
      fun L : (H × ℝ) →L[ℝ] E => L.comp (ContinuousLinearMap.inl ℝ H ℝ) :=
    (ContinuousLinearMap.compL ℝ H (H × ℝ) E).continuous.clm_apply continuous_const
  exact hclm.comp
    (((contDiff_prodDirDeriv hD hs).continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_id))

/-! ### The decay the bound family needs -/

omit [NormedSpace ℝ H] in
/-- The parameter weight moves between nearby points, which is what lets a bound family that is
constant on a ball carry a weight evaluated at the ball's centre. -/
theorem one_add_norm_le_of_sub_norm_le (N : ℕ) {p x : H} (h : ‖x - p‖ ≤ 1) :
    (1 + ‖p‖) ^ N ≤ 2 ^ N * (1 + ‖x‖) ^ N := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ N
  have h1 : ‖p‖ ≤ ‖x‖ + 1 := by
    have h2 : ‖p‖ - ‖x‖ ≤ ‖x - p‖ := by
      have := norm_sub_norm_le p x
      rw [norm_sub_rev] at this
      linarith [this]
    linarith
  linarith [norm_nonneg x]

/-- ★★ **The weight transfer.** Two orders of `G`'s decay give a bound that already carries a
polynomial weight in the *parameter* and still has an integrable profile in the integration
variable — with the constant a single `Finset.sup` of `G`'s seminorms, which is the shape
`SchwartzMap.mkCLM` consumes. -/
theorem one_add_norm_pow_mul_norm_iteratedFDeriv_le [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E]
    (G : 𝓢(H × ℝ, E)) (N k : ℕ) (p : H) (t : ℝ) :
    (1 + ‖p‖) ^ N * ‖iteratedFDeriv ℝ k (G : H × ℝ → E) (p, t)‖
      ≤ 2 ^ (N + 2) * (Finset.Iic (N + 2, k)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
          * (1 + t ^ 2)⁻¹ := by
  have hr : (0 : ℝ) ≤ ‖((p, t) : H × ℝ)‖ := norm_nonneg _
  have h1 : (1 + ‖p‖) ^ N ≤ (1 + ‖((p, t) : H × ℝ)‖) ^ N := by
    gcongr
    exact norm_fst_le ((p, t) : H × ℝ)
  have h2 : 1 + t ^ 2 ≤ (1 + ‖((p, t) : H × ℝ)‖) ^ 2 := by
    have ht : |t| ≤ ‖((p, t) : H × ℝ)‖ := by simp
    nlinarith [abs_nonneg t, sq_abs t]
  have h3 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + 2, k))
    (le_refl (N + 2)) (le_refl k) G (p, t)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  calc (1 + ‖p‖) ^ N * ‖iteratedFDeriv ℝ k (G : H × ℝ → E) (p, t)‖ * (1 + t ^ 2)
      ≤ (1 + ‖((p, t) : H × ℝ)‖) ^ N * ‖iteratedFDeriv ℝ k (G : H × ℝ → E) (p, t)‖
          * (1 + ‖((p, t) : H × ℝ)‖) ^ 2 := by gcongr
    _ = (1 + ‖((p, t) : H × ℝ)‖) ^ (N + 2)
          * ‖iteratedFDeriv ℝ k (G : H × ℝ → E) (p, t)‖ := by rw [pow_add]; ring
    _ ≤ 2 ^ (N + 2) * (Finset.Iic (N + 2, k)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G := h3


/-! ### The partial integral -/

section Integral

variable [FiniteDimensional ℝ H] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E]

omit [FiniteDimensional ℝ H] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] in
/-- Each slice of a Schwartz function is smooth in the first variable, which is #124's smoothness
hypothesis. -/
theorem contDiff_slice_left (G : 𝓢(H × ℝ, E)) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : H => G (y, t) :=
  (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)).comp (contDiff_id.prodMk contDiff_const)

omit [FiniteDimensional ℝ H] in
/-- The slice is integrable, which every statement below needs. -/
theorem integrable_slice_left (G : 𝓢(H × ℝ, E)) (p : H) :
    Integrable (fun t : ℝ => G (p, t)) volume := by
  have hmaj : Integrable (fun t : ℝ =>
      2 ^ 2 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
        * (1 + t ^ 2)⁻¹) volume := integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' (G.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have h := one_add_norm_pow_mul_norm_iteratedFDeriv_le G 0 0 p t
  simpa [norm_iteratedFDeriv_zero] using h

omit [FiniteDimensional ℝ H] in
/-- ★★ **The bound family both statements below run on**: a directional derivative of the slice,
dominated uniformly in the parameter by `G`'s decay with the integrable profile `(1 + t²)⁻¹`, and
carrying whatever polynomial weight in the parameter is asked for. -/
theorem norm_dirDeriv_slice_le (G : 𝓢(H × ℝ, E)) (N : ℕ) (hs : List H) (x : H) (t : ℝ) :
    ‖dirDeriv (fun (p : H) (s : ℝ) => G (p, s)) hs x t‖
      ≤ dirWeight hs * (((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2)
          * (Finset.Iic (N + 2, hs.length)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
          * (1 + t ^ 2)⁻¹)) := by
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ N := by positivity
  have h1 := norm_dirDeriv_le hs (fun (p : H) (s : ℝ) => G (p, s))
    (fun t => contDiff_slice_left G t) x t
  have h2 := norm_iteratedFDeriv_comp_inl_le
    (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)) t hs.length x
  have h3 := one_add_norm_pow_mul_norm_iteratedFDeriv_le G N hs.length x t
  have h4 : ‖iteratedFDeriv ℝ hs.length (G : H × ℝ → E) (x, t)‖
      ≤ ((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2)
          * (Finset.Iic (N + 2, hs.length)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
          * (1 + t ^ 2)⁻¹) := by
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    calc ‖iteratedFDeriv ℝ hs.length (G : H × ℝ → E) (x, t)‖ * (1 + ‖x‖) ^ N
        = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ hs.length (G : H × ℝ → E) (x, t)‖ := by ring
      _ ≤ _ := h3
  calc ‖dirDeriv (fun (p : H) (s : ℝ) => G (p, s)) hs x t‖
      ≤ ‖iteratedFDeriv ℝ hs.length (fun y => G (y, t)) x‖ * dirWeight hs := h1
    _ ≤ ‖iteratedFDeriv ℝ hs.length (G : H × ℝ → E) (x, t)‖ * dirWeight hs :=
        mul_le_mul_of_nonneg_right h2 (dirWeight_nonneg hs)
    _ ≤ (((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2)
          * (Finset.Iic (N + 2, hs.length)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
          * (1 + t ^ 2)⁻¹)) * dirWeight hs :=
        mul_le_mul_of_nonneg_right h4 (dirWeight_nonneg hs)
    _ = dirWeight hs * (((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2)
          * (Finset.Iic (N + 2, hs.length)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G
          * (1 + t ^ 2)⁻¹)) := by ring

/-- ★★ **The partial integral is smooth**, by #124 with the bound family above — which is uniform in
the parameter, so no ball is needed here. -/
theorem contDiff_integral_slice (G : 𝓢(H × ℝ, E)) (m : ℕ) :
    ContDiff ℝ (m : ℕ) fun p : H => ∫ t : ℝ, G (p, t) := by
  refine contDiff_integral_of_dirBound
    (bound := fun k t => 2 ^ 2
      * (Finset.Iic (2, k)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G * (1 + t ^ 2)⁻¹)
    (fun t => (contDiff_slice_left G t).of_le (by exact_mod_cast le_top))
    (fun hs _ x => aestronglyMeasurable_dirDeriv_prodMk
      (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)) hs x)
    (fun hs _ x => aestronglyMeasurable_fderiv_dirDeriv_prodMk
      (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)) hs x)
    (fun k _ => integrable_inv_one_add_sq.const_mul _)
    (fun k _ t => by positivity) ?_
  intro hs _ x t
  have h := norm_dirDeriv_slice_le G 0 hs x t
  simpa using h

/-- ★★★ **The seminorm estimate**, which is what makes the partial integral a *Schwartz* function.
The weight is carried by a bound family that is **constant on a unit ball** of parameters — which is
the shape #126's gate consumes — and `∫ (1 + t²)⁻¹ = π` finishes it. The right-hand side is linear
in a single `Finset.sup` of `G`'s seminorms, which is what `SchwartzMap.mkCLM` asks for. -/
theorem norm_pow_mul_norm_iteratedFDeriv_integral_le (G : 𝓢(H × ℝ, E)) (N k : ℕ) (p : H) :
    ‖p‖ ^ N * ‖iteratedFDeriv ℝ k (fun q : H => ∫ t : ℝ, G (q, t)) p‖
      ≤ 2 ^ (2 * N + 2) * Real.pi
          * (Finset.Iic (N + 2, k)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ,
      ∀ j, S j = (Finset.Iic (N + 2, j)).sup (schwartzSeminormFamily ℂ (H × ℝ) E) G :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ j, 0 ≤ S j := fun j => by rw [hS]; exact apply_nonneg _ _
  have hwpos : (0 : ℝ) < (1 + ‖p‖) ^ N := by positivity
  have hb0 : ∀ (j : ℕ) (t : ℝ),
      0 ≤ 2 ^ (2 * N + 2) * S j * ((1 + ‖p‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by
    intro j t
    have := hS0 j
    positivity
  have hbd : ∀ hs : List H, ∀ x ∈ ball p 1, ∀ t : ℝ,
      ‖dirDeriv (fun (q : H) (s : ℝ) => G (q, s)) hs x t‖
        ≤ dirWeight hs
            * (2 ^ (2 * N + 2) * S hs.length * ((1 + ‖p‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹) := by
    intro hs x hx t
    have hsub : ‖x - p‖ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hx
      exact hx.le
    have hshift : (1 + ‖p‖) ^ N ≤ 2 ^ N * (1 + ‖x‖) ^ N := one_add_norm_le_of_sub_norm_le N hsub
    have hxpos : (0 : ℝ) < (1 + ‖x‖) ^ N := by positivity
    have hkey : ((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2) * S hs.length * (1 + t ^ 2)⁻¹)
        ≤ 2 ^ (2 * N + 2) * S hs.length * ((1 + ‖p‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by
      have h2 : ((1 + ‖x‖) ^ N)⁻¹ * 2 ^ (N + 2) ≤ ((1 + ‖p‖) ^ N)⁻¹ * 2 ^ (2 * N + 2) := by
        rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hxpos hwpos]
        calc 2 ^ (N + 2) * (1 + ‖p‖) ^ N
            ≤ 2 ^ (N + 2) * (2 ^ N * (1 + ‖x‖) ^ N) :=
              mul_le_mul_of_nonneg_left hshift (by positivity)
          _ = 2 ^ (2 * N + 2) * (1 + ‖x‖) ^ N := by ring
      have hrest : (0 : ℝ) ≤ S hs.length * (1 + t ^ 2)⁻¹ := by
        have := hS0 hs.length
        positivity
      calc ((1 + ‖x‖) ^ N)⁻¹ * (2 ^ (N + 2) * S hs.length * (1 + t ^ 2)⁻¹)
          = (((1 + ‖x‖) ^ N)⁻¹ * 2 ^ (N + 2)) * (S hs.length * (1 + t ^ 2)⁻¹) := by ring
        _ ≤ (((1 + ‖p‖) ^ N)⁻¹ * 2 ^ (2 * N + 2)) * (S hs.length * (1 + t ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_right h2 hrest
        _ = 2 ^ (2 * N + 2) * S hs.length * ((1 + ‖p‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by ring
    refine le_trans (norm_dirDeriv_slice_le G N hs x t) ?_
    refine mul_le_mul_of_nonneg_left ?_ (dirWeight_nonneg hs)
    rw [hS hs.length] at hkey ⊢
    exact hkey
  -- #126's gate, on the ball
  have hgate := norm_iteratedFDeriv_integral_le k (fun (q : H) (s : ℝ) => G (q, s)) (ball p 1)
    (fun j t => 2 ^ (2 * N + 2) * S j * ((1 + ‖p‖) ^ N)⁻¹ * (1 + t ^ 2)⁻¹)
    isOpen_ball (fun m t => (contDiff_slice_left G t).of_le (by exact_mod_cast le_top))
    (fun hs x => aestronglyMeasurable_dirDeriv_prodMk
      (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)) hs x)
    (fun hs x => aestronglyMeasurable_fderiv_dirDeriv_prodMk
      (G.smooth' : ContDiff ℝ (⊤ : ℕ∞) (G : H × ℝ → E)) hs x)
    (fun j => integrable_inv_one_add_sq.const_mul _) hb0 hbd p (mem_ball_self one_pos)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hgate
  have hwle : ‖p‖ ^ N ≤ (1 + ‖p‖) ^ N :=
    pow_le_pow_left₀ (norm_nonneg p) (by linarith) N
  rw [← hS k]
  calc ‖p‖ ^ N * ‖iteratedFDeriv ℝ k (fun q : H => ∫ t : ℝ, G (q, t)) p‖
      ≤ (1 + ‖p‖) ^ N * (2 ^ (2 * N + 2) * S k * ((1 + ‖p‖) ^ N)⁻¹ * Real.pi) :=
        mul_le_mul hwle hgate (norm_nonneg _) (by positivity)
    _ = 2 ^ (2 * N + 2) * Real.pi * S k := by
        field_simp

/-- ★★★ **Integrating out the last variable maps Schwartz space to Schwartz space**, continuously
and linearly. -/
noncomputable def SchwartzMap.integralLastCLM : 𝓢(H × ℝ, E) →L[ℂ] 𝓢(H, E) :=
  mkCLM (fun G p => ∫ t : ℝ, G (p, t))
    (fun G₁ G₂ p => by
      show ∫ t : ℝ, (G₁ + G₂) (p, t) = (∫ t : ℝ, G₁ (p, t)) + ∫ t : ℝ, G₂ (p, t)
      rw [← integral_add (integrable_slice_left G₁ p) (integrable_slice_left G₂ p)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => rfl))
    (fun c G p => by
      show ∫ t : ℝ, (c • G) (p, t) = (RingHom.id ℂ) c • ∫ t : ℝ, G (p, t)
      rw [RingHom.id_apply, ← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => rfl))
    (fun G => contDiff_infty.2 fun m => contDiff_integral_slice G m)
    (fun n => ⟨Finset.Iic (n.1 + 2, n.2), 2 ^ (2 * n.1 + 2) * Real.pi, by positivity,
      fun G p => norm_pow_mul_norm_iteratedFDeriv_integral_le G n.1 n.2 p⟩)

@[simp]
theorem SchwartzMap.integralLastCLM_apply (G : 𝓢(H × ℝ, E)) (p : H) :
    (SchwartzMap.integralLastCLM (E := E) G) p = ∫ t : ℝ, G (p, t) := rfl

end Integral

end

end
