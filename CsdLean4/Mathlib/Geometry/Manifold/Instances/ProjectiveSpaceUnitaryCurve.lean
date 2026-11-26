/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow

/-!
# The orbit of a unitary curve on `ℂℙⁿ`: its velocity is a Schrödinger field

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (1-Mathlib-staging in its mathematics; it consumes the corpus's
`Matrix.unitaryGroup` action on `ℂℙⁿ` and `schrodingerField`).

`isMIntegralCurve_schrodingerUnitary_smul` gives the velocity of `t ↦ exp(-itH) • p`: one
matrix and the clock `t`. Here the curve of unitaries is any curve `W` whose matrix is
differentiable at `t` with derivative `(-i K) W(t)`. Its orbit of a point `p` then has, at
`t`, the velocity `schrodingerField K (W t • p)`. `K` may depend on `t`: this is what a
product of commuting one-parameter groups run with different clocks needs.

* ★ `hasDerivAt_chartFun_unitaryCurve_smul_chartInv` — in a chart: for a curve `V` of
  unitaries with `V t = 1` and derivative `-i K` at `t`, the derivative at `t` of
  `s ↦ chartFun i (V s • chartInv i w)` is `schrodingerChartField K i w`;
* ★★ `hasMFDerivAt_unitaryCurve_smul` — **on `ℂℙⁿ`: for a continuous curve `W` of unitaries
  whose matrix has the derivative `(-i K) W(t)` at `t`, the orbit `s ↦ W s • p` has the
  manifold derivative `schrodingerField K (W t • p)` at `t`**.

## Honest scope

⚠️ **A derivative at one time.** No flow is built and no uniqueness is used. `K` is any
matrix: that it be Hermitian is not needed for the derivative.

⚠️ **`W` continuous** is a hypothesis, used for the continuity that a manifold derivative
carries. It follows from differentiability at every time, which is not assumed.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-24, UO-26; §9.4); `specs/unified-records-spacetime-task-plans.md` (§9, route (α));
`Instances/ProjectiveSpaceSchrodingerFlow.lean` (`hasDerivAt_chartFun_schrodingerUnitary`,
`isMIntegralCurve_schrodingerUnitary_smul`, `schrodingerChartField`, `schrodingerField`,
`mulVecEntryCLM`); `Instances/ProjectiveSpaceUnitaryAction.lean` (`chartFun_smul_chartInv`);
`specs/TERMS.md` (Hamiltonian); `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix Matrix.Norms.L2Operator
open Kahler DifferentialForm

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- ★ **The velocity of a unitary curve's orbit, in a chart.** For a curve `V` of unitaries
with `V t = 1` whose matrix has the derivative `-i K` at `t`, the derivative at `t` of
`s ↦ chartFun i (V s • chartInv i w)` is `schrodingerChartField K i w`. -/
theorem hasDerivAt_chartFun_unitaryCurve_smul_chartInv
    {K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {V : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ}
    {t : ℝ} (hV1 : V t = 1)
    (hV : HasDerivAt (fun s : ℝ => (V s : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      ((-Complex.I) • K) t) (i : Fin (n + 1)) (w : Fin n → ℂ) :
    HasDerivAt (fun s : ℝ => chartFun i (V s • chartInv i w)) (schrodingerChartField K i w)
      t := by
  simp_rw [chartFun_smul_chartInv]
  refine hasDerivAt_pi.2 fun j => ?_
  have hV1' : (V t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
    rw [hV1]
    rfl
  have hentry : ∀ k, HasDerivAt
      (fun s : ℝ => ((V s : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) k)
      (-Complex.I * (K *ᵥ (insertOne i w).ofLp) k) t := by
    intro k
    have h := (mulVecEntryCLM (insertOne i w).ofLp k).hasFDerivAt.comp_hasDerivAt t hV
    refine h.congr_deriv ?_
    rw [mulVecEntryCLM_apply, Matrix.smul_mulVec]
    simp
  have hnum := hentry (i.succAbove j)
  have hden := hentry i
  have hden0 : ((V t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      *ᵥ (insertOne i w).ofLp) i = 1 := by
    rw [hV1', Matrix.one_mulVec]
    exact insertOne_apply_same i w
  have hnum0 : ((V t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      *ᵥ (insertOne i w).ofLp) (i.succAbove j) = w j := by
    rw [hV1', Matrix.one_mulVec]
    exact insertOne_apply_succAbove i w j
  show HasDerivAt (fun s : ℝ =>
    ((V s : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) (i.succAbove j)
      / ((V s : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) i) (schrodingerChartField K i w j) t
  refine (hnum.div hden (by rw [hden0]; exact one_ne_zero)).congr_deriv ?_
  rw [hden0, hnum0]
  simp only [schrodingerChartField]
  ring

/-- ★★ **The velocity of a unitary curve's orbit on `ℂℙⁿ`.** For a continuous curve `W` of
unitaries whose matrix has the derivative `(-i K) W(t)` at `t`, the orbit `s ↦ W s • p` has
the manifold derivative `schrodingerField K (W t • p)` at `t`. -/
theorem hasMFDerivAt_unitaryCurve_smul {K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {W : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ} (hWc : Continuous W) {t : ℝ}
    (hW : HasDerivAt (fun s : ℝ => (W s : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (((-Complex.I) • K) * (W t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) t)
    (p : ℙ ℂ (Ambient n)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℂ) (fun s : ℝ => W s • p) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (schrodingerField K (W t • p))) := by
  have hcont : Continuous fun s : ℝ => W s • p := hWc.smul continuous_const
  refine ⟨hcont.continuousAt, ?_⟩
  have hq : chartInv (idx (W t • p)) (chartFun (idx (W t • p)) (W t • p)) = W t • p :=
    chartInv_chartFun _ _ (idx_spec _)
  have hfun : (fun s : ℝ => chartFun (idx (W t • p)) (W s • p))
      = fun s : ℝ => chartFun (idx (W t • p))
          ((W s * (W t)⁻¹) • chartInv (idx (W t • p))
            (chartFun (idx (W t • p)) (W t • p))) := by
    funext s
    rw [hq, ← mul_smul, inv_mul_cancel_right]
  have hinv : (W t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      * (((W t)⁻¹ : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel (W t))
  have hVd : HasDerivAt
      (fun s : ℝ => ((W s * (W t)⁻¹ : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ((-Complex.I) • K) t := by
    have h := hW.mul_const (((W t)⁻¹ : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    refine h.congr_deriv ?_
    rw [mul_assoc, hinv, mul_one]
  have hd : HasDerivAt (fun s : ℝ => chartFun (idx (W t • p)) (W s • p))
      (schrodingerField K (W t • p)) t := by
    rw [hfun]
    exact hasDerivAt_chartFun_unitaryCurve_smul_chartInv (mul_inv_cancel (W t)) hVd
      (idx (W t • p)) (chartFun (idx (W t • p)) (W t • p))
  have hw : writtenInExtChartAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (Fin n → ℂ)) t (fun s : ℝ => W s • p)
      = fun s : ℝ => chartFun (idx (W t • p)) (W s • p) := by
    funext s
    simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id, extChartAt_coe,
      modelWithCornersSelf_coe]
    rfl
  rw [hw]
  exact hd.hasFDerivAt.hasFDerivWithinAt

end Projectivization

end
