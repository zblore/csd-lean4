/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Module

/-!
# Finite-dimensional Stone's theorem, C^1 form

A `C^1` (differentiable) one-parameter unitary group of `N x N` complex matrices is
`t ↦ exp (t • A)` for its skew-Hermitian generator `A`. This is the load-bearing
content of Stone's theorem in finite dimensions: a differentiable one-parameter
group IS the exponential of its generator.

Mathlib has no Stone theorem (the `Stone*` names there are Stone-Weierstrass /
Stone-Cech / Stone separation). This file supplies the forward direction under a
smoothness hypothesis, closing the CSD dynamics-spine residue W5-S2 for the `C^1`
case. The full-continuity strengthening (strong continuity implies differentiability,
via integral averaging + FTC + invertibility) is the named residual and is NOT
included here.

## Main results

* `CSD.StoneC1.eq_exp_of_hasDeriv` : ODE-uniqueness core. If `U' t = U t * A` and
  `U 0 = 1`, then `U t = exp (t • A)`. This recovers the generator from the group.
* `CSD.StoneC1.exp_smul_unitary` : skew-Hermitian `A` gives each `exp (t • A)`
  unitary (`(exp (t • A))ᴴ * exp (t • A) = 1`).
* `CSD.StoneC1.stone_c1` : the packaged C^1 Stone theorem. From `star A = -A`,
  `∀ t, HasDerivAt U (U t * A) t`, `U 0 = 1`, conclude `∀ t, U t = exp (t • A)` and
  each `U t` is unitary.
* `CSD.StoneC1.trivial_group`, `CSD.StoneC1.skew_witness` : non-vacuity round-trips.

## Implementation notes

`NormedSpace.exp` is field-independent in current Mathlib (a single-argument
`exp (x : 𝔸)`), so it is written unqualified-by-field as `NormedSpace.exp (t • A)`.

The route is ODE uniqueness (`ODE_solution_unique_univ`, Gronwall) against the
reference solution `t ↦ exp (t • A)` whose derivative is `hasDerivAt_exp_smul_const`.
No integral averaging, no continuity-to-differentiability step.

The matrix norm is the `C^*`-algebra L2-operator norm (`open scoped
Matrix.Norms.L2Operator`), NOT the plain operator or Frobenius norm. This is
load-bearing: `hasDerivAt_exp_smul_const` needs `CompleteSpace (Matrix ...)`, and
under the plain operator / Frobenius scopes the finite-dimensional completeness
instance does not unify with the scoped `NormedAddCommGroup` (an instance diamond),
so synthesis fails. The `C^*`-algebra norm carries completeness by definition, so
`CompleteSpace` is automatic with no diamond, and `norm_mul_le` (submultiplicativity)
still holds.

The scalar-action side conditions (`0 • A = 0`, `t • (-A) = -(t • A)`) are discharged
with `module`, not the generic `zero_smul` / `smul_neg` rewrites: under the scoped
matrix-norm the `SMul ℝ (Matrix ...)` instance path defeats those rewrites, while
`module` normalises through the correct instance.

Declarations use dotted `CSD.StoneC1.*` names at top level rather than a
`namespace ... end` block (a namespace block can select a spurious `SMul` diamond).
-/

open scoped Matrix.Norms.L2Operator Matrix

noncomputable section

variable {N : ℕ}

/-- ODE-uniqueness core. A `C^1` curve solving `Y' = Y * A` with `Y 0 = 1` is the
matrix exponential `t ↦ exp (t • A)`. Reuses `ODE_solution_unique_univ` (Gronwall)
with the `‖A‖`-Lipschitz linear field `Y ↦ Y * A` and `hasDerivAt_exp_smul_const`
for the reference solution. -/
theorem CSD.StoneC1.eq_exp_of_hasDeriv (A : Matrix (Fin N) (Fin N) ℂ)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hderiv : ∀ t, HasDerivAt U (U t * A) t) (hU0 : U 0 = 1) :
    ∀ t, U t = NormedSpace.exp (t • A) := by
  have key : U = fun t => NormedSpace.exp (t • A) := by
    apply ODE_solution_unique_univ (v := fun _ Y => Y * A) (s := fun _ => Set.univ)
        (K := ‖A‖₊) (t₀ := 0)
    · intro t
      apply LipschitzOnWith.of_dist_le_mul
      intro Y1 _ Y2 _
      rw [dist_eq_norm, dist_eq_norm, ← sub_mul]
      calc ‖(Y1 - Y2) * A‖ ≤ ‖Y1 - Y2‖ * ‖A‖ := norm_mul_le _ _
        _ = ‖A‖₊ * ‖Y1 - Y2‖ := by rw [coe_nnnorm]; ring
    · intro t; exact ⟨hderiv t, Set.mem_univ _⟩
    · intro t; exact ⟨hasDerivAt_exp_smul_const A t, Set.mem_univ _⟩
    · rw [hU0, show ((0 : ℝ) • A) = 0 from by module, NormedSpace.exp_zero]
  intro t; exact congrFun key t

/-- For a skew-Hermitian generator `A` (`star A = -A`), each `exp (t • A)` is unitary.
Reuses `Matrix.exp_conjTranspose` and `Matrix.exp_add_of_commute`. -/
theorem CSD.StoneC1.exp_smul_unitary (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : star A = -A) (t : ℝ) :
    (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 := by
  have hAH : Aᴴ = -A := by rw [← Matrix.star_eq_conjTranspose]; exact hA
  have hskew : (t • A)ᴴ = -(t • A) := by
    rw [Matrix.conjTranspose_smul, star_trivial, hAH]; module
  have hcomm : Commute (-(t • A)) (t • A) := (Commute.refl (t • A)).neg_left
  rw [← Matrix.exp_conjTranspose, hskew, ← Matrix.exp_add_of_commute _ _ hcomm,
    neg_add_cancel, NormedSpace.exp_zero]

/-- **C^1 finite-dimensional Stone theorem.** A differentiable one-parameter unitary
group with skew-Hermitian generator `A` is `t ↦ exp (t • A)`, and every `U t` is
unitary. The generator is recovered from the group. -/
theorem CSD.StoneC1.stone_c1 (A : Matrix (Fin N) (Fin N) ℂ)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ) (hA : star A = -A)
    (hderiv : ∀ t, HasDerivAt U (U t * A) t) (hU0 : U 0 = 1) :
    (∀ t, U t = NormedSpace.exp (t • A)) ∧
      (∀ t, (U t)ᴴ * U t = 1) := by
  have hexp := CSD.StoneC1.eq_exp_of_hasDeriv A U hderiv hU0
  refine ⟨hexp, fun t => ?_⟩
  rw [hexp t]
  exact CSD.StoneC1.exp_smul_unitary A hA t

/-- Non-vacuity: the trivial group. `A = 0` gives the constant unit curve, whose
generator is recovered as `0` and `U t = exp (t • 0) = 1`. -/
theorem CSD.StoneC1.trivial_group :
    ∀ t : ℝ, (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) t
      = NormedSpace.exp (t • (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply CSD.StoneC1.eq_exp_of_hasDeriv
  · intro t; simpa using hasDerivAt_const t (1 : Matrix (Fin 2) (Fin 2) ℂ)
  · rfl

/-- Non-vacuity: a concrete skew-Hermitian generator `A = I • 1` on `Fin 2`. The
skew-Hermitian hypothesis holds, so `exp (t • A)` is a genuine unitary group. -/
theorem CSD.StoneC1.skew_witness :
    star (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = -(Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      ∀ t : ℝ, (NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))))ᴴ
          * NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 1 := by
  have hI : star Complex.I = -Complex.I := by simp
  have hskew : star (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = -(Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [star_smul, star_one, hI]; module
  exact ⟨hskew, fun t => CSD.StoneC1.exp_smul_unitary _ hskew t⟩

end
