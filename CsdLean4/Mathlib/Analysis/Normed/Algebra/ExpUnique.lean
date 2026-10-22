/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The exponential is the unique solution of `U' = X U`, `U 0 = 1`; the closed form for `X² = P`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #183.

In a complete normed algebra over `ℝ` or `ℂ`, a differentiable `U` with `U 0 = 1` and
`U' a = X * U a` for all `a` is `a ↦ exp (a • X)`: the function `a ↦ exp (−a • X) * U a` has zero
derivative, so it is constant, and equals `1` at `0`. This replaces series manipulations by an ODE
argument whenever a candidate closed form is at hand.

The application: if `X * X = P` and `X * P = X` (so `X` is an "involution on its own range", e.g. a
symmetric hop `|10⟩⟨01| + |01⟩⟨10|` with `P` the projector on the two configurations it exchanges),
then `exp (a • X) = 1 + (cosh a − 1) • P + sinh a • X` for every `a : ℂ`.

* `exp_smul_mul_exp_neg_smul` — `exp (a • X) * exp (−a • X) = 1`;
* ★★ `exp_smul_eq_of_hasDerivAt` — **uniqueness**: `U 0 = 1` and `U' = X U` force `U a = exp (a • X)`;
* ★★ `exp_smul_eq_cosh_sinh` — **the closed form** for `X² = P`, `X P = X`.

## Honest scope

* The uniqueness statement is for the left equation `U' = X U`; the right equation `U' = U X` is
  the same proof with the factors swapped and is not duplicated.
* The closed form is stated over `ℂ`, where `cosh` and `sinh` live; the purely imaginary case
  `a = −iθ` gives `cos θ` and `−i sin θ` through `Complex.cosh_mul_I`, `Complex.sinh_mul_I`.

References: `Mathlib/Analysis/SpecialFunctions/Exponential.lean` (`hasDerivAt_exp_smul_const`),
`Mathlib/Analysis/Calculus/MeanValue.lean` (`is_const_of_deriv_eq_zero`); `specs/BACKLOG.md` #183.
-/

@[expose] public section

open NormedSpace

section Unique

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem exp_smul_mul_exp_neg_smul (X : 𝔸) (a : 𝕂) : exp (a • X) * exp ((-a) • X) = 1 := by
  have hr := expSeries_radius_eq_top 𝕂 𝔸
  rw [← exp_add_of_commute_of_mem_ball (((Commute.refl X).smul_left a).smul_right (-a))
      (hr.symm ▸ edist_lt_top _ _) (hr.symm ▸ edist_lt_top _ _), neg_smul, add_neg_cancel, exp_zero]

/-- ★★ **Uniqueness of the exponential as an ODE solution**: if `U 0 = 1` and `U' a = X * U a` for
every `a`, then `U a = exp (a • X)`. -/
theorem exp_smul_eq_of_hasDerivAt {U : 𝕂 → 𝔸} (X : 𝔸) (h0 : U 0 = 1)
    (hU : ∀ a, HasDerivAt U (X * U a) a) (a : 𝕂) : U a = exp (a • X) := by
  have hV : ∀ b : 𝕂, HasDerivAt (fun c : 𝕂 => exp ((-c) • X) * U c) 0 b := by
    intro b
    have hL : HasDerivAt (fun c : 𝕂 => exp ((-c) • X)) ((-1 : 𝕂) • (exp ((-b) • X) * X)) b :=
      (hasDerivAt_exp_smul_const X (-b)).scomp b (hasDerivAt_neg b)
    refine (hL.mul (hU b)).congr_deriv ?_
    rw [neg_one_smul, neg_mul, ← mul_assoc, neg_add_cancel]
  have hdiff : Differentiable 𝕂 (fun c : 𝕂 => exp ((-c) • X) * U c) :=
    fun b => (hV b).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun b => (hV b).deriv) a 0
  simp only [neg_zero, zero_smul, exp_zero, one_mul, h0] at hconst
  calc U a = (exp (a • X) * exp ((-a) • X)) * U a := by
        rw [exp_smul_mul_exp_neg_smul, one_mul]
    _ = exp (a • X) * (exp ((-a) • X) * U a) := by rw [mul_assoc]
    _ = exp (a • X) := by rw [hconst, mul_one]

end Unique

section ClosedForm

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- ★★ **The closed form for `X² = P`, `X P = X`**:
`exp (a • X) = 1 + (cosh a − 1) • P + sinh a • X`. -/
theorem exp_smul_eq_cosh_sinh {X P : 𝔸} (hXX : X * X = P) (hXP : X * P = X) (a : ℂ) :
    exp (a • X) = 1 + (Complex.cosh a - 1) • P + Complex.sinh a • X := by
  refine (exp_smul_eq_of_hasDerivAt (U := fun c : ℂ => 1 + (Complex.cosh c - 1) • P
    + Complex.sinh c • X) X ?_ ?_ a).symm
  · simp
  · intro b
    have h1 : HasDerivAt (fun c : ℂ => (Complex.cosh c - 1) • P) (Complex.sinh b • P) b :=
      ((Complex.hasDerivAt_cosh b).sub_const 1).smul_const P
    have h2 : HasDerivAt (fun c : ℂ => Complex.sinh c • X) (Complex.cosh b • X) b :=
      (Complex.hasDerivAt_sinh b).smul_const X
    refine (((hasDerivAt_const b (1 : 𝔸)).add h1).add h2).congr_deriv ?_
    rw [mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm, hXP, hXX, sub_smul, one_smul]
    abel

end ClosedForm

end
