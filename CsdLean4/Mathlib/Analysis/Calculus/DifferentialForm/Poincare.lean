/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianLieDerivative
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Poincaré lemma for 2-forms on a ball

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Analysis.Calculus.DifferentialForm`).

A closed `C¹` 2-form on a ball is exact, with an explicit primitive: the **radial primitive**
`β x = ∫₀¹ t · ι_{x − x₀} ω(x₀ + t (x − x₀)) dt`, the homotopy operator of the classical proof.
Differentiating under the integral and using closedness (`extDeriv ω = 0`) at the segment points,
the exterior derivative of `β` at `x` is `∫₀¹ (d/dt)(t² ω(x₀ + t (x − x₀))) dt = ω x`.

Every integral here is a scalar one: `radialPrimitiveVal ω x₀ x v` is the value of the primitive
on `v`, its `x`-derivative is a covector-valued integral, and the primitive is packaged as a
covector (`radialPrimitive`) and as an alternating 1-form (`radialPrimitiveForm`) by linearity in
`v` and finite dimension. (At this Mathlib pin the operator spaces over operator or alternating
spaces do not carry the measurability instances the parametric integrals need, so the covector-
and form-valued objects are never integrated.)

* `isBoundedBilinearMap_apply_vecCons` — `(ξ, h) ↦ ξ ![h, v]` is bounded bilinear;
  `evalPair ω v (y, h) = ω y ![h, v]`, `hasFDerivAt_evalPair`;
* `radialPrimitiveVal`, `radialPrimitiveIntegrand`, `radialPrimitiveDerivIntegrand`,
  `radialPrimitiveDerivVal` — the scalar primitive `β x v` and its `x`-derivative
  `∫₀¹ t · D(evalPair ω v)(y_t, x − x₀) ∘ (t·1, 1)`;
* ★ `hasFDerivAt_radialPrimitiveVal` — **`β · v` is differentiable on the ball** (Mathlib's
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` on the interval), and
  `continuousOn_radialPrimitiveDerivVal`, `contDiffOn_radialPrimitiveVal` — **it is `C¹`**
  (`continuousAt_of_dominated_interval`);
* `radialPrimitive ω x₀ x`, `radialPrimitiveForm ω x₀ x` — the primitive as a covector and as a
  1-form (`radialPrimitiveForm_apply`, `radialPrimitiveForm_self`), with
  ★ `contDiffOn_radialPrimitive`, ★ `contDiffOn_radialPrimitiveForm` and
  `hasFDerivAt_radialPrimitiveForm` (through a basis of `E`);
* `fderiv_radialPrimitive_self`, `hasFDerivAt_radialPrimitiveForm_self` — if `ω x₀ = 0` then
  `Dβ(x₀) = 0`: the primitive of a form vanishing at the centre vanishes to second order there
  (what makes Moser's vector field small);
* ★★ `extDeriv_radialPrimitiveForm` — **the Poincaré lemma**: for `ω` closed on the ball,
  `d β = ω` on the ball.

## Honest scope

⚠️ **Degree 2 only, real-valued, on a ball.** The homotopy operator in every degree and on every
star-shaped set is the same computation with more indices; only the case Darboux's theorem needs
is written.

⚠️ **`C¹`.** The form is assumed `C¹` on the ball, and the primitive is shown `C¹`; higher
regularity of the primitive (which the parametric integral inherits) is not stated.

References: `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`);
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` (`continuousAt_of_dominated_interval`);
`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (`extDeriv_apply`);
`Geometry/Manifold/HamiltonianLieDerivative.lean` (the `Fin 2`/`Fin 3` exterior-derivative
idioms); intended consumer: Darboux's theorem by Moser's trick, `specs/BACKLOG.md` ▶ OPEN QUEUE #8
(the assembly that remains).
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory intervalIntegral
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Evaluating a 2-form on a pair -/

section Eval

theorem Matrix.update_vecCons_zero {α : Type*} (a b c : α) :
    Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> simp

theorem Matrix.update_vecCons_one {α : Type*} (a b c : α) :
    Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> simp

/-- `(ξ, h) ↦ ξ ![h, v]` is bounded bilinear. -/
theorem isBoundedBilinearMap_apply_vecCons (v : E) :
    IsBoundedBilinearMap ℝ (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × E => p.1 ![p.2, v]) where
  add_left := fun ξ ξ' h => by simp
  smul_left := fun c ξ h => by simp
  add_right := fun ξ h h' => by
    have := ContinuousAlternatingMap.map_update_add ξ ![h, v] 0 h h'
    simpa only [Matrix.update_vecCons_zero] using this
  smul_right := fun c ξ h => by
    have := ContinuousAlternatingMap.map_update_smul ξ ![h, v] 0 c h
    simpa only [Matrix.update_vecCons_zero] using this
  bound := ⟨‖v‖ + 1, by positivity, fun ξ h => by
    calc ‖ξ ![h, v]‖ ≤ ‖ξ‖ * ∏ i, ‖![h, v] i‖ := ContinuousAlternatingMap.le_opNorm ξ _
      _ = ‖ξ‖ * (‖h‖ * ‖v‖) := by simp [Fin.prod_univ_two]
      _ ≤ (‖v‖ + 1) * ‖ξ‖ * ‖h‖ := by nlinarith [norm_nonneg ξ, norm_nonneg h, norm_nonneg v]⟩

/-- The scalar function `(y, h) ↦ ω y ![h, v]` on `E × E`. -/
def evalPair (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (v : E) (p : E × E) : ℝ := ω p.1 ![p.2, v]

theorem evalPair_apply (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (v : E) (y h : E) :
    evalPair ω v (y, h) = ω y ![h, v] := rfl

/-- The derivative of `evalPair`: `D(evalPair ω v)(y, h) (a, b) = Dω(y) a ![h, v] + ω y ![b, v]`. -/
theorem hasFDerivAt_evalPair {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} (v : E) {y : E}
    (hω : DifferentiableAt ℝ ω y) (h : E) :
    HasFDerivAt (evalPair ω v)
      (((isBoundedBilinearMap_apply_vecCons v).deriv (ω y, h)) ∘L
        ((fderiv ℝ ω y ∘L ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)))
      (y, h) := by
  have h1 : HasFDerivAt (fun p : E × E => (ω p.1, p.2))
      ((fderiv ℝ ω y ∘L ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E))
      (y, h) :=
    (hω.hasFDerivAt.comp (y, h) hasFDerivAt_fst).prodMk hasFDerivAt_snd
  exact ((isBoundedBilinearMap_apply_vecCons v).hasFDerivAt (ω y, h)).comp (y, h) h1

theorem fderiv_evalPair_apply {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} (v : E) {y : E}
    (hω : DifferentiableAt ℝ ω y) (h a b : E) :
    fderiv ℝ (evalPair ω v) (y, h) (a, b) = fderiv ℝ ω y a ![h, v] + ω y ![b, v] := by
  rw [(hasFDerivAt_evalPair v hω h).fderiv, ContinuousLinearMap.comp_apply,
    IsBoundedBilinearMap.deriv_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

theorem contDiffOn_evalPair {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}
    (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E) :
    ContDiffOn ℝ 1 (evalPair ω v) (ball x₀ R ×ˢ univ) := by
  have h1 : ContDiffOn ℝ 1 (fun p : E × E => (ω p.1, p.2)) (ball x₀ R ×ˢ univ) :=
    (hω.comp contDiffOn_fst fun p hp => hp.1).prodMk contDiffOn_snd
  exact (isBoundedBilinearMap_apply_vecCons v).contDiff.comp_contDiffOn h1

end Eval

/-! ### The segment -/

section Segment

/-- The point at parameter `t` on the segment from `x₀` to `x`. -/
abbrev segPt (x₀ x : E) (t : ℝ) : E := x₀ + t • (x - x₀)

theorem segPt_zero (x₀ x : E) : segPt x₀ x 0 = x₀ := by simp [segPt]

theorem segPt_one (x₀ x : E) : segPt x₀ x 1 = x := by simp [segPt]

theorem segPt_self (x₀ : E) (t : ℝ) : segPt x₀ x₀ t = x₀ := by simp [segPt]

theorem norm_segPt_sub_le {x₀ x : E} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segPt x₀ x t - x₀‖ ≤ ‖x - x₀‖ := by
  simp only [segPt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

theorem segPt_mem_ball {x₀ x : E} {R : ℝ} (hx : x ∈ ball x₀ R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segPt x₀ x t ∈ ball x₀ R := by
  rw [mem_ball, dist_eq_norm] at hx ⊢
  exact (norm_segPt_sub_le ht).trans_lt hx

theorem segPt_mem_closedBall {x₀ x : E} {r : ℝ} (hx : x ∈ closedBall x₀ r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : segPt x₀ x t ∈ closedBall x₀ r := by
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  exact (norm_segPt_sub_le ht).trans hx

theorem hasFDerivAt_segPt (x₀ : E) (t : ℝ) (x : E) :
    HasFDerivAt (fun x => segPt x₀ x t) (t • ContinuousLinearMap.id ℝ E) x :=
  (((hasFDerivAt_id x).sub_const x₀).const_smul t).const_add x₀

theorem continuous_segPt (x₀ x : E) : Continuous (segPt x₀ x) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem continuous_segPt_left (x₀ : E) (t : ℝ) : Continuous (fun x => segPt x₀ x t) :=
  continuous_const.add (continuous_const.smul (continuous_id.sub continuous_const))

theorem hasDerivAt_segPt (x₀ x : E) (t : ℝ) : HasDerivAt (segPt x₀ x) (x - x₀) t := by
  have := ((hasDerivAt_id t).smul_const (x - x₀)).const_add x₀
  simpa [segPt] using this

end Segment

/-! ### The scalar primitive and its derivative -/

section Primitive

variable (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (x₀ : E)

/-- The integrand of the radial primitive evaluated on `v`: `t · ω(x₀ + t (x − x₀)) ![x − x₀, v]`. -/
def radialPrimitiveIntegrand (v x : E) (t : ℝ) : ℝ :=
  t * evalPair ω v (segPt x₀ x t, x - x₀)

/-- **The radial primitive** evaluated on `v`:
`β x v = ∫₀¹ t · ω(x₀ + t (x − x₀)) ![x − x₀, v] dt`. -/
def radialPrimitiveVal (x v : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, radialPrimitiveIntegrand ω x₀ v x t

/-- The `x`-derivative of the integrand. -/
def radialPrimitiveDerivIntegrand (v x : E) (t : ℝ) : E →L[ℝ] ℝ :=
  t • (t • (fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inl ℝ E E)
    + fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inr ℝ E E)

/-- The `x`-derivative of `β · v`: the integral of the derivative of the integrand. -/
def radialPrimitiveDerivVal (x v : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, radialPrimitiveDerivIntegrand ω x₀ v x t

variable {ω x₀}

theorem radialPrimitiveIntegrand_apply (v x : E) (t : ℝ) :
    radialPrimitiveIntegrand ω x₀ v x t = t * ω (segPt x₀ x t) ![x - x₀, v] := rfl

theorem radialPrimitiveDerivIntegrand_apply (v x : E) (t : ℝ) (u : E) :
    radialPrimitiveDerivIntegrand ω x₀ v x t u
      = t * fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) (t • u, u) := by
  have hsplit : ((t • u, u) : E × E) = t • ((u, 0) : E × E) + (0, u) := by simp
  simp only [radialPrimitiveDerivIntegrand, hsplit, map_add, map_smul, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    smul_eq_mul]

/-- `β x₀ v = 0`. -/
theorem radialPrimitiveVal_self (v : E) : radialPrimitiveVal ω x₀ x₀ v = 0 := by
  have h0 : ∀ t : ℝ, radialPrimitiveIntegrand ω x₀ v x₀ t = 0 := fun t => by
    rw [radialPrimitiveIntegrand_apply, sub_self, ContinuousAlternatingMap.map_coord_zero _ 0 rfl,
      mul_zero]
  simp [radialPrimitiveVal, h0]

/-- The integrand is differentiable in `x` wherever `ω` is differentiable at the segment
point. -/
theorem hasFDerivAt_radialPrimitiveIntegrand (v : E) {x : E} {t : ℝ}
    (hω : DifferentiableAt ℝ ω (segPt x₀ x t)) :
    HasFDerivAt (fun x => radialPrimitiveIntegrand ω x₀ v x t)
      (radialPrimitiveDerivIntegrand ω x₀ v x t) x := by
  have hp : HasFDerivAt (fun x : E => (segPt x₀ x t, x - x₀))
      ((t • ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_segPt x₀ t x).prodMk ((hasFDerivAt_id x).sub_const x₀)
  have he := (hasFDerivAt_evalPair v hω (x - x₀)).comp x hp
  refine (he.const_mul t).congr_fderiv ?_
  rw [← (hasFDerivAt_evalPair v hω (x - x₀)).fderiv]
  ext u
  have hsplit : ((t • u, u) : E × E) = t • ((u, 0) : E × E) + (0, u) := by simp
  simp only [radialPrimitiveDerivIntegrand, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [hsplit, map_add, map_smul]
  simp only [smul_eq_mul]

end Primitive

/-! ### Differentiability and continuity, by dominated convergence -/

section Dominated

variable {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

/-- Continuity of the integrand in `t` on `[0, 1]`, for `x` in the ball. -/
theorem continuousOn_radialPrimitiveIntegrand (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E)
    {x : E} (hx : x ∈ ball x₀ R) :
    ContinuousOn (radialPrimitiveIntegrand ω x₀ v x) (Icc 0 1) := by
  have h1 : ContinuousOn (fun t => evalPair ω v (segPt x₀ x t, x - x₀)) (Icc 0 1) :=
    (contDiffOn_evalPair hω v).continuousOn.comp
      ((continuous_segPt x₀ x).prodMk continuous_const).continuousOn
      fun t ht => ⟨segPt_mem_ball hx ht, mem_univ _⟩
  exact continuousOn_id.mul h1

/-- Continuity of the derivative integrand in `t` on `[0, 1]`, for `x` in the ball. -/
theorem continuousOn_radialPrimitiveDerivIntegrand (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E)
    {x : E} (hx : x ∈ ball x₀ R) :
    ContinuousOn (radialPrimitiveDerivIntegrand ω x₀ v x) (Icc 0 1) := by
  have hD : ContinuousOn (fderiv ℝ (evalPair ω v)) (ball x₀ R ×ˢ univ) :=
    (contDiffOn_evalPair hω v).continuousOn_fderiv_of_isOpen (isOpen_ball.prod isOpen_univ) le_rfl
  have h1 : ContinuousOn (fun t => fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀)) (Icc 0 1) :=
    hD.comp ((continuous_segPt x₀ x).prodMk continuous_const).continuousOn
      fun t ht => ⟨segPt_mem_ball hx ht, mem_univ _⟩
  exact continuousOn_id.smul ((continuousOn_id.smul (h1.clm_comp continuousOn_const)).add
    (h1.clm_comp continuousOn_const))

variable [FiniteDimensional ℝ E]

/-- A uniform bound on the derivative integrand on a closed ball inside the ball of definition. -/
theorem exists_bound_radialPrimitiveDerivIntegrand (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E)
    {r : ℝ} (hr : r < R) :
    ∃ B : ℝ, ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖radialPrimitiveDerivIntegrand ω x₀ v x t‖ ≤ B := by
  have hsub : closedBall x₀ r ⊆ ball x₀ R := closedBall_subset_ball hr
  have hD : ContinuousOn (fderiv ℝ (evalPair ω v)) (ball x₀ R ×ˢ univ) :=
    (contDiffOn_evalPair hω v).continuousOn_fderiv_of_isOpen (isOpen_ball.prod isOpen_univ) le_rfl
  have hK : IsCompact (closedBall x₀ r ×ˢ closedBall (0 : E) (max r 0)) :=
    (isCompact_closedBall x₀ r).prod (isCompact_closedBall 0 _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fderiv ℝ (evalPair ω v)) (hD.mono fun p hp => ⟨hsub hp.1, mem_univ _⟩)
  refine ⟨2 * max C 0, fun x hx t ht => ?_⟩
  have hy : segPt x₀ x t ∈ closedBall x₀ r := segPt_mem_closedBall hx ht
  have hxr : x - x₀ ∈ closedBall (0 : E) (max r 0) := by
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff]
    exact hx.trans (le_max_left _ _)
  have ht' : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
  have hinl : ‖ContinuousLinearMap.inl ℝ E E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
      simp [Prod.norm_def]
  have hinr : ‖ContinuousLinearMap.inr ℝ E E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
      simp [Prod.norm_def]
  have hDb : ‖fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀)‖ ≤ max C 0 :=
    (hC _ ⟨hy, hxr⟩).trans (le_max_left _ _)
  have h1 : ‖t • (fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inl ℝ E E)‖
      ≤ max C 0 := by
    rw [norm_smul]
    calc ‖t‖ * ‖fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inl ℝ E E‖
        ≤ 1 * (max C 0 * 1) := by
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hDb hinl (norm_nonneg _)
            (le_max_right _ _))
      _ = max C 0 := by ring
  have h2 : ‖fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inr ℝ E E‖
      ≤ max C 0 := by
    calc ‖fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inr ℝ E E‖
        ≤ max C 0 * 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hDb hinr (norm_nonneg _) (le_max_right _ _))
      _ = max C 0 := mul_one _
  calc ‖radialPrimitiveDerivIntegrand ω x₀ v x t‖
      = ‖t‖ * ‖t • (fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inl ℝ E E)
          + fderiv ℝ (evalPair ω v) (segPt x₀ x t, x - x₀) ∘L ContinuousLinearMap.inr ℝ E E‖ :=
        norm_smul _ _
    _ ≤ 1 * (max C 0 + max C 0) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * max C 0 := by ring

/-- ★ **`β · v` is differentiable on the ball**, with derivative the integral of the derivative
of the integrand. -/
theorem hasFDerivAt_radialPrimitiveVal (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E) {x : E}
    (hx : x ∈ ball x₀ R) :
    HasFDerivAt (fun x => radialPrimitiveVal ω x₀ x v) (radialPrimitiveDerivVal ω x₀ x v) x := by
  have hxb := hx
  rw [mem_ball, dist_eq_norm] at hx
  set r : ℝ := (‖x - x₀‖ + R) / 2 with hr
  set ρ : ℝ := (R - ‖x - x₀‖) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hrR : r < R := by rw [hr]; linarith
  have hs : ∀ y ∈ ball x ρ, y ∈ closedBall x₀ r := fun y hy => by
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ r := by rw [hr]; linarith
  have hsub : closedBall x₀ r ⊆ ball x₀ R := closedBall_subset_ball hrR
  obtain ⟨B, hB⟩ := exists_bound_radialPrimitiveDerivIntegrand hω v hrR
  have hIcc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x ρ) (bound := fun _ => B)
    (ball_mem_nhds x hρ0) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ball_mem_nhds x hρ0] with y hy
    exact ContinuousOn.aestronglyMeasurable
      ((continuousOn_radialPrimitiveIntegrand hω v (hsub (hs y hy))).mono hIcc) measurableSet_uIoc
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (continuousOn_radialPrimitiveIntegrand hω v hxb)
  · exact ContinuousOn.aestronglyMeasurable
      ((continuousOn_radialPrimitiveDerivIntegrand hω v hxb).mono hIcc) measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht y hy => hB y (hs y hy) t (hIcc ht)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht y hy => hasFDerivAt_radialPrimitiveIntegrand v ?_
    exact (hω.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (segPt_mem_ball (hsub (hs y hy)) (hIcc ht)))

/-- The derivative of `β · v` is continuous on the ball. -/
theorem continuousOn_radialPrimitiveDerivVal (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E) :
    ContinuousOn (fun x => radialPrimitiveDerivVal ω x₀ x v) (ball x₀ R) := by
  intro x hxb
  refine ContinuousAt.continuousWithinAt ?_
  have hx := hxb
  rw [mem_ball, dist_eq_norm] at hx
  set r : ℝ := (‖x - x₀‖ + R) / 2 with hr
  set ρ : ℝ := (R - ‖x - x₀‖) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hrR : r < R := by rw [hr]; linarith
  have hs : ∀ y ∈ ball x ρ, y ∈ closedBall x₀ r := fun y hy => by
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ r := by rw [hr]; linarith
  have hsub : closedBall x₀ r ⊆ ball x₀ R := closedBall_subset_ball hrR
  obtain ⟨B, hB⟩ := exists_bound_radialPrimitiveDerivIntegrand hω v hrR
  have hIcc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have hD : ContinuousOn (fderiv ℝ (evalPair ω v)) (ball x₀ R ×ˢ univ) :=
    (contDiffOn_evalPair hω v).continuousOn_fderiv_of_isOpen (isOpen_ball.prod isOpen_univ) le_rfl
  refine continuousAt_of_dominated_interval (bound := fun _ => B) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds x hρ0] with y hy
    exact ContinuousOn.aestronglyMeasurable
      ((continuousOn_radialPrimitiveDerivIntegrand hω v (hsub (hs y hy))).mono hIcc)
      measurableSet_uIoc
  · filter_upwards [ball_mem_nhds x hρ0] with y hy
    exact Filter.Eventually.of_forall fun t ht => hB y (hs y hy) t (hIcc ht)
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := hIcc ht
    have hyx : (segPt x₀ x t, x - x₀) ∈ ball x₀ R ×ˢ univ := ⟨segPt_mem_ball hxb ht', mem_univ _⟩
    have hseg : ContinuousAt (fun y : E => (segPt x₀ y t, y - x₀)) x :=
      ((continuous_segPt_left x₀ t).prodMk (continuous_id.sub continuous_const)).continuousAt
    have h1 : ContinuousAt (fun y => fderiv ℝ (evalPair ω v) (segPt x₀ y t, y - x₀)) x :=
      ContinuousAt.comp (f := fun y : E => (segPt x₀ y t, y - x₀))
        (hD.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds hyx)) hseg
    exact (continuousAt_const (y := t)).smul (((continuousAt_const (y := t)).smul
      (h1.clm_comp (continuousAt_const (y := ContinuousLinearMap.inl ℝ E E)))).add
      (h1.clm_comp (continuousAt_const (y := ContinuousLinearMap.inr ℝ E E))))

/-- ★ **`β · v` is `C¹` on the ball.** -/
theorem contDiffOn_radialPrimitiveVal (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E) :
    ContDiffOn ℝ 1 (fun x => radialPrimitiveVal ω x₀ x v) (ball x₀ R) := by
  have hd : ∀ x ∈ ball x₀ R,
      HasFDerivAt (fun x => radialPrimitiveVal ω x₀ x v) (radialPrimitiveDerivVal ω x₀ x v) x :=
    fun x hx => hasFDerivAt_radialPrimitiveVal hω v hx
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (continuousOn_radialPrimitiveDerivVal hω v).congr fun x hx => (hd x hx).fderiv

end Dominated

/-! ### The primitive as a covector and as a 1-form -/

section Form

variable [FiniteDimensional ℝ E] (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (x₀ : E)

omit [FiniteDimensional ℝ E] in
/-- The integrand is additive in `v`. -/
theorem radialPrimitiveIntegrand_add (x : E) (t : ℝ) (v w : E) :
    radialPrimitiveIntegrand ω x₀ (v + w) x t
      = radialPrimitiveIntegrand ω x₀ v x t + radialPrimitiveIntegrand ω x₀ w x t := by
  simp only [radialPrimitiveIntegrand, evalPair]
  have := ContinuousAlternatingMap.map_update_add (ω (segPt x₀ x t)) ![x - x₀, v] 1 v w
  simp only [Matrix.update_vecCons_one] at this
  rw [this, mul_add]

omit [FiniteDimensional ℝ E] in
/-- The integrand is homogeneous in `v`. -/
theorem radialPrimitiveIntegrand_smul (x : E) (t : ℝ) (c : ℝ) (v : E) :
    radialPrimitiveIntegrand ω x₀ (c • v) x t = c * radialPrimitiveIntegrand ω x₀ v x t := by
  simp only [radialPrimitiveIntegrand, evalPair]
  have := ContinuousAlternatingMap.map_update_smul (ω (segPt x₀ x t)) ![x - x₀, v] 1 c v
  simp only [Matrix.update_vecCons_one, smul_eq_mul] at this
  rw [this]; ring

variable {ω x₀} {R : ℝ}

omit [FiniteDimensional ℝ E] in
theorem radialPrimitiveVal_add (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E} (hx : x ∈ ball x₀ R)
    (v w : E) :
    radialPrimitiveVal ω x₀ x (v + w) = radialPrimitiveVal ω x₀ x v + radialPrimitiveVal ω x₀ x w := by
  simp only [radialPrimitiveVal, radialPrimitiveIntegrand_add]
  exact intervalIntegral.integral_add
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_radialPrimitiveIntegrand hω v hx))
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_radialPrimitiveIntegrand hω w hx))

omit [FiniteDimensional ℝ E] in
theorem radialPrimitiveVal_smul {x : E} (c : ℝ) (v : E) :
    radialPrimitiveVal ω x₀ x (c • v) = c * radialPrimitiveVal ω x₀ x v := by
  simp only [radialPrimitiveVal, radialPrimitiveIntegrand_smul]
  exact intervalIntegral.integral_const_mul c _

omit [FiniteDimensional ℝ E] in
theorem radialPrimitiveVal_zero {x : E} : radialPrimitiveVal ω x₀ x 0 = 0 := by
  have := radialPrimitiveVal_smul (ω := ω) (x₀ := x₀) (x := x) 0 0
  rwa [zero_smul, zero_mul] at this

variable (ω x₀)

open Classical in
/-- **The radial primitive** as a covector, on the ball (`0` off it). -/
def radialPrimitive (R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  if h : ContDiffOn ℝ 1 ω (ball x₀ R) ∧ x ∈ ball x₀ R then
    LinearMap.toContinuousLinearMap
      { toFun := radialPrimitiveVal ω x₀ x
        map_add' := radialPrimitiveVal_add h.1 h.2
        map_smul' := fun c v => radialPrimitiveVal_smul c v }
  else 0

/-- The radial primitive as an alternating 1-form. -/
def radialPrimitiveForm (R : ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
    (radialPrimitive ω x₀ R x)

variable {ω x₀}

theorem radialPrimitive_apply (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E} (hx : x ∈ ball x₀ R)
    (v : E) : radialPrimitive ω x₀ R x v = radialPrimitiveVal ω x₀ x v := by
  simp [radialPrimitive, hω, hx]

theorem radialPrimitiveForm_apply (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E} (hx : x ∈ ball x₀ R)
    (m : Fin 1 → E) : radialPrimitiveForm ω x₀ R x m = radialPrimitiveVal ω x₀ x (m 0) := by
  show radialPrimitive ω x₀ R x (m 0) = _
  exact radialPrimitive_apply hω hx (m 0)

theorem radialPrimitiveForm_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R) :
    radialPrimitiveForm ω x₀ R x₀ = 0 := by
  ext m
  rw [radialPrimitiveForm_apply hω (mem_ball_self hR), radialPrimitiveVal_self]
  rfl

/-- The covector `β x` expanded in a basis of `E`: `β x = ∑ᵢ β x (bᵢ) • bᵢ*`. -/
theorem radialPrimitive_eq_sum (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E} (hx : x ∈ ball x₀ R)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    radialPrimitive ω x₀ R x
      = ∑ i, radialPrimitiveVal ω x₀ x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
  ext v
  rw [radialPrimitive_apply hω hx]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, smul_eq_mul]
  conv_lhs => rw [← b.sum_repr v]
  have hlin : ∀ (s : Finset (Fin (Module.finrank ℝ E))),
      radialPrimitiveVal ω x₀ x (∑ i ∈ s, b.repr v i • b i)
        = ∑ i ∈ s, radialPrimitiveVal ω x₀ x (b i) * b.repr v i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [radialPrimitiveVal_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, radialPrimitiveVal_add hω hx, ih,
        radialPrimitiveVal_smul]
      ring
  exact hlin Finset.univ

/-- The 1-form `β x` expanded in a basis of `E`. -/
theorem radialPrimitiveForm_eq_sum (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E}
    (hx : x ∈ ball x₀ R) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    radialPrimitiveForm ω x₀ R x
      = ∑ i, radialPrimitiveVal ω x₀ x (b i) •
          ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
            (LinearMap.toContinuousLinearMap (b.coord i)) := by
  rw [radialPrimitiveForm, radialPrimitive_eq_sum hω hx b, map_sum]
  simp only [map_smul]

/-- ★ **The radial primitive is `C¹` on the ball** (as a covector field). -/
theorem contDiffOn_radialPrimitive (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) :
    ContDiffOn ℝ 1 (radialPrimitive ω x₀ R) (ball x₀ R) := by
  let b := Module.finBasis ℝ E
  have h : ContDiffOn ℝ 1 (fun x => ∑ i, radialPrimitiveVal ω x₀ x (b i) •
      LinearMap.toContinuousLinearMap (b.coord i)) (ball x₀ R) :=
    ContDiffOn.sum fun i _ => (contDiffOn_radialPrimitiveVal hω (b i)).smul contDiffOn_const
  exact h.congr fun x hx => radialPrimitive_eq_sum hω hx b

/-- ★ **The radial primitive is `C¹` on the ball** (as a 1-form). -/
theorem contDiffOn_radialPrimitiveForm (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) :
    ContDiffOn ℝ 1 (radialPrimitiveForm ω x₀ R) (ball x₀ R) :=
  ContDiff.comp_contDiffOn
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff
    (contDiffOn_radialPrimitive hω)

/-- The derivative of the 1-form `β`, through a basis. -/
theorem hasFDerivAt_radialPrimitiveForm (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {x : E}
    (hx : x ∈ ball x₀ R) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    HasFDerivAt (radialPrimitiveForm ω x₀ R)
      (∑ i, (radialPrimitiveDerivVal ω x₀ x (b i)).smulRight
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
          (LinearMap.toContinuousLinearMap (b.coord i)))) x := by
  have h := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i y => radialPrimitiveVal ω x₀ y (b i) •
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
        (LinearMap.toContinuousLinearMap (b.coord i)))
    (A' := fun i => (radialPrimitiveDerivVal ω x₀ x (b i)).smulRight
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
        (LinearMap.toContinuousLinearMap (b.coord i))))
    fun i _ => (hasFDerivAt_radialPrimitiveVal hω (b i) hx).smul_const
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
        (LinearMap.toContinuousLinearMap (b.coord i)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [radialPrimitiveForm_eq_sum hω hy b]
  simp [Finset.sum_apply]

omit [FiniteDimensional ℝ E] in
/-- If the form vanishes at the centre, its radial primitive vanishes to second order there:
`D(β · v)(x₀) = 0`. -/
theorem radialPrimitiveDerivVal_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (h0 : ω x₀ = 0) (v : E) : radialPrimitiveDerivVal ω x₀ x₀ v = 0 := by
  have hωd : DifferentiableAt ℝ ω x₀ :=
    (hω.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have : ∀ t : ℝ, radialPrimitiveDerivIntegrand ω x₀ v x₀ t = 0 := fun t => by
    ext u
    rw [radialPrimitiveDerivIntegrand_apply, segPt_self, sub_self, fderiv_evalPair_apply v hωd,
      h0]
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, add_zero, zero_apply]
    rw [ContinuousAlternatingMap.map_coord_zero _ 0 rfl]
    ring
  simp [radialPrimitiveDerivVal, this]

/-- If the form vanishes at the centre, the 1-form `β` has derivative `0` at `x₀`. -/
theorem hasFDerivAt_radialPrimitiveForm_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (h0 : ω x₀ = 0) :
    HasFDerivAt (radialPrimitiveForm ω x₀ R) (0 : E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) x₀ := by
  have h := hasFDerivAt_radialPrimitiveForm hω (mem_ball_self hR) (Module.finBasis ℝ E)
  refine h.congr_fderiv (Finset.sum_eq_zero fun i _ => ?_)
  rw [radialPrimitiveDerivVal_self hω hR h0]
  ext u
  simp

/-- If the form vanishes at the centre, `Dβ(x₀) = 0`. -/
theorem fderiv_radialPrimitive_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (h0 : ω x₀ = 0) : fderiv ℝ (radialPrimitive ω x₀ R) x₀ = 0 := by
  let b := Module.finBasis ℝ E
  have h := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i y => radialPrimitiveVal ω x₀ y (b i) • LinearMap.toContinuousLinearMap (b.coord i))
    (A' := fun i => (radialPrimitiveDerivVal ω x₀ x₀ (b i)).smulRight
      (LinearMap.toContinuousLinearMap (b.coord i)))
    fun i _ => (hasFDerivAt_radialPrimitiveVal hω (b i) (mem_ball_self hR)).smul_const
      (LinearMap.toContinuousLinearMap (b.coord i))
  have h' : HasFDerivAt (radialPrimitive ω x₀ R)
      (∑ i, (radialPrimitiveDerivVal ω x₀ x₀ (b i)).smulRight
        (LinearMap.toContinuousLinearMap (b.coord i))) x₀ := by
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with y hy
    rw [radialPrimitive_eq_sum hω hy b]
    simp [Finset.sum_apply]
  rw [h'.fderiv]
  simp [radialPrimitiveDerivVal_self hω hR h0]

end Form

/-! ### The Poincaré lemma -/

section Poincare

variable [FiniteDimensional ℝ E] {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

omit [FiniteDimensional ℝ E] in
/-- The value of the derivative of `β · v` on `u`: the integral of the derivative integrand's
values. -/
theorem radialPrimitiveDerivVal_apply (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (v : E) {x : E}
    (hx : x ∈ ball x₀ R) (u : E) :
    radialPrimitiveDerivVal ω x₀ x v u
      = ∫ t in (0 : ℝ)..1, (t ^ 2 * fderiv ℝ ω (segPt x₀ x t) u ![x - x₀, v]
        + t * ω (segPt x₀ x t) ![u, v]) := by
  have hint : IntervalIntegrable (radialPrimitiveDerivIntegrand ω x₀ v x) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (continuousOn_radialPrimitiveDerivIntegrand hω v hx)
  have h1 := (ContinuousLinearMap.apply ℝ ℝ u).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.apply_apply] at h1
  rw [radialPrimitiveDerivVal, ← h1]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have hωd : DifferentiableAt ℝ ω (segPt x₀ x t) :=
    (hω.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (segPt_mem_ball hx ht))
  rw [radialPrimitiveDerivIntegrand_apply, fderiv_evalPair_apply v hωd, map_smul]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- ★★ **The Poincaré lemma for 2-forms on a ball**: if `ω` is `C¹` and closed on the ball, the
exterior derivative of its radial primitive is `ω`. -/
theorem extDeriv_radialPrimitiveForm (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0) {x : E} (hx : x ∈ ball x₀ R) :
    extDeriv (radialPrimitiveForm ω x₀ R) x = ω x := by
  let b := Module.finBasis ℝ E
  have hβf := hasFDerivAt_radialPrimitiveForm hω hx b
  have hωd : ∀ y ∈ ball x₀ R, DifferentiableAt ℝ ω y := fun y hy =>
    (hω.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hy)
  -- the scalar derivatives of `y ↦ β y v`
  have hval : ∀ v u : E, fderiv ℝ (fun y => radialPrimitiveForm ω x₀ R y ![v]) x u
      = radialPrimitiveDerivVal ω x₀ x v u := by
    intro v u
    have h := hasFDerivAt_radialPrimitiveVal hω v hx
    have hfun : (fun y => radialPrimitiveForm ω x₀ R y ![v])
        =ᶠ[𝓝 x] fun y => radialPrimitiveVal ω x₀ y v := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [radialPrimitiveForm_apply hω hy]
      rfl
    rw [hfun.fderiv_eq, h.fderiv]
  ext m
  have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
  rw [extDeriv_apply hβf.differentiableAt, Fin.sum_univ_two]
  simp only [Fin.removeNth_zero_two, Fin.removeNth_one_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_smul, neg_one_smul]
  rw [hval, hval, radialPrimitiveDerivVal_apply hω _ hx, radialPrimitiveDerivVal_apply hω _ hx]
  -- the closedness identity at each segment point
  set h : E := x - x₀ with hh
  have hcl : ∀ t ∈ Icc (0 : ℝ) 1,
      fderiv ℝ ω (segPt x₀ x t) (m 0) ![h, m 1] - fderiv ℝ ω (segPt x₀ x t) (m 1) ![h, m 0]
        = fderiv ℝ ω (segPt x₀ x t) h ![m 0, m 1] := by
    intro t ht
    have hy := segPt_mem_ball hx ht
    have hz := congrArg (fun ξ : E [⋀^Fin 3]→L[ℝ] ℝ => ξ ![h, m 0, m 1]) (hclosed _ hy)
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hz
    rw [extDeriv_apply (hωd _ hy), Fin.sum_univ_three] at hz
    simp only [Fin.removeNth_zero_three, Fin.removeNth_one_three, Fin.removeNth_two_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.val_zero, Fin.val_one,
      Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul,
      fderiv_continuousAlternatingMap_apply_const_apply (hωd _ hy)] at hz
    simp only [Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one, Function.comp_apply,
      neg_one_sq, one_smul] at hz
    have e1 : (![m 0, m 1] : Fin 2 → E) 1 = m 1 := rfl
    simp only [e1] at hz
    linarith
  -- the integrand is the derivative of `t ↦ t² ω(y_t) ![m 0, m 1]`
  have hg : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => t ^ 2 * ω (segPt x₀ x t) ![m 0, m 1])
        (2 * t * ω (segPt x₀ x t) ![m 0, m 1]
          + t ^ 2 * fderiv ℝ ω (segPt x₀ x t) h ![m 0, m 1]) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hy := segPt_mem_ball hx ht
    have h1 : HasDerivAt (fun t => ω (segPt x₀ x t)) (fderiv ℝ ω (segPt x₀ x t) h) t :=
      (hωd _ hy).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_segPt x₀ x t)
    have h2 : HasDerivAt (fun t => ω (segPt x₀ x t) ![m 0, m 1])
        (fderiv ℝ ω (segPt x₀ x t) h ![m 0, m 1]) t :=
      (ContinuousAlternatingMap.apply ℝ E ℝ ![m 0, m 1]).hasFDerivAt.comp_hasDerivAt t h1
    exact ((hasDerivAt_pow 2 t).mul h2).congr_deriv (by norm_num)
  have hc1 : ContinuousOn (fun t => ω (segPt x₀ x t)) (Icc 0 1) :=
    hω.continuousOn.comp (continuous_segPt x₀ x).continuousOn fun t ht => segPt_mem_ball hx ht
  have hD : ContinuousOn (fderiv ℝ ω) (ball x₀ R) :=
    hω.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hc2 : ContinuousOn (fun t => fderiv ℝ ω (segPt x₀ x t)) (Icc 0 1) :=
    hD.comp (continuous_segPt x₀ x).continuousOn fun t ht => segPt_mem_ball hx ht
  have hint : IntervalIntegrable (fun t => 2 * t * ω (segPt x₀ x t) ![m 0, m 1]
      + t ^ 2 * fderiv ℝ ω (segPt x₀ x t) h ![m 0, m 1]) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (((continuousOn_const.mul continuousOn_id).mul
        (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ ![m 0, m 1]).continuous hc1)).add
        ((continuousOn_id.pow 2).mul (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ ![m 0, m 1]).continuous
          (hc2.clm_apply continuousOn_const))))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint
  simp only [segPt_one, segPt_zero, one_mul, sq, mul_zero, zero_mul, sub_zero] at hftc
  have hi1 : IntervalIntegrable (fun t => t ^ 2 * fderiv ℝ ω (segPt x₀ x t) (m 0) ![h, m 1]
      + t * ω (segPt x₀ x t) ![m 0, m 1]) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (((continuousOn_id.pow 2).mul (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ _).continuous
        (hc2.clm_apply continuousOn_const))).add
        (continuousOn_id.mul (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ _).continuous hc1)))
  have hi2 : IntervalIntegrable (fun t => t ^ 2 * fderiv ℝ ω (segPt x₀ x t) (m 1) ![h, m 0]
      + t * ω (segPt x₀ x t) ![m 1, m 0]) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (((continuousOn_id.pow 2).mul (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ _).continuous
        (hc2.clm_apply continuousOn_const))).add
        (continuousOn_id.mul (Continuous.comp_continuousOn (ContinuousAlternatingMap.apply ℝ E ℝ _).continuous hc1)))
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub hi1 hi2]
  conv_rhs => rw [hm]
  rw [← hftc]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have hsw := ContinuousAlternatingMap.apply_swap_two (ω (segPt x₀ x t)) (m 0) (m 1)
  have hc := hcl t ht
  linear_combination t ^ 2 * hc - t * hsw

end Poincare

end
