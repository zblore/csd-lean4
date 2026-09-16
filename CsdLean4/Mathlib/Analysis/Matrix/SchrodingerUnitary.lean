/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.Module

/-!
# The one-parameter unitary group `exp(−itH)` of a Hermitian matrix

**Category:** 1-Mathlib (CSD-free; the matrix exponential of a skew-Hermitian generator).

For a Hermitian matrix `H` and a real time `t`, the generator `−(it) H` is skew-Hermitian, so its
matrix exponential is unitary. This file packages `exp(−itH)` as an element of
`Matrix.unitaryGroup`, proves that the family is a one-parameter group, and differentiates it:
`U t` has derivative `U t * (−iH)` at every `t`, the C¹ datum finite-dimensional Stone theorems
consume. The derivative is taken under the `C*`-algebra `L2Operator` norm scope, where the
completeness instance that `hasDerivAt_exp_smul_const` needs synthesises without a diamond.

## Main declarations

* `Matrix.schrodingerGen H t = (−t i) • H` and `schrodingerGen_star` (skew-Hermitian for Hermitian
  `H`); `schrodingerGen_exp_mem_unitaryGroup` — its exponential is unitary.
* `Matrix.schrodingerUnitary hH t : unitaryGroup (Fin N) ℂ` — the bundled `exp(−itH)`.
* `expNegITH_unitary_group` — `U (s + t) = U s * U t` and `U 0 = 1` in the unitary group.
* `schrodingerUnitary_hasDerivAt` — `HasDerivAt (U ·) (U t * (−i • H)) t`, with the helpers
  `schrodingerGen_neg_i_smul_skew` and `schrodingerGen_eq_real_smul`.

## Provenance

Moved verbatim on 2026-09-16 from `CsdLean4/LF4/ProjectedDynamics.lean` (the generator, the
unitary and the group law, 2026-06) and `CsdLean4/LF4/ManyToOneSchrodingerDerived.lean` (the
derivative, 2026-07-19), where they back the projected Schrödinger flow of that programme;
`CSD.LF4` re-exports the names. The move makes the Category-1 manifold modules that use
`exp(−itH)` (the Schrödinger flow on `ℂℙⁿ`) Category 1 by closure.

## References

* `specs/future-work.md` (the completed-work ledger).
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace Matrix

variable {N : ℕ}

/-- The candidate Schrödinger generator matrix `-(i t) H` for a time `t` and a
matrix `H`. When `H` is Hermitian and `t` real this is skew-Hermitian, so its
matrix exponential is unitary. -/
def schrodingerGen (H : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (-(t : ℂ) * Complex.I) • H

/-- For Hermitian `H`, the generator `-(i t) H` is skew-Hermitian:
`(schrodingerGen H t)ᴴ = - schrodingerGen H t`. -/
theorem schrodingerGen_star {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (t : ℝ) :
    (schrodingerGen H t)ᴴ = -schrodingerGen H t := by
  unfold schrodingerGen
  rw [Matrix.conjTranspose_smul, hH, ← neg_smul]
  congr 1
  simp only [star_mul', star_neg, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **`exp(-itH)` is unitary.** For Hermitian `H` and real `t`, the matrix exponential
`exp(schrodingerGen H t) = exp(-i t H)` lies in `unitaryGroup (Fin N) ℂ`: the generator is
skew-Hermitian, so `(exp A)ᴴ = exp (Aᴴ) = exp (-A)` and `exp A * exp (-A) = exp 0 = 1`. -/
theorem schrodingerGen_exp_mem_unitaryGroup {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (t : ℝ) : NormedSpace.exp (schrodingerGen H t) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, schrodingerGen_star hH t,
    ← Matrix.exp_add_of_commute (schrodingerGen H t) (-schrodingerGen H t)
      (Commute.neg_right (Commute.refl (schrodingerGen H t))),
    add_neg_cancel, NormedSpace.exp_zero]

/-- The unitary `exp(-i t H) ∈ unitaryGroup` as a bundled group element. -/
def schrodingerUnitary {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (t : ℝ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨NormedSpace.exp (schrodingerGen H t), schrodingerGen_exp_mem_unitaryGroup hH t⟩

/-- **The `exp(-itH)` family is a one-parameter unitary group.** For Hermitian `H`, the family
`U t = exp(-i t H)` satisfies `U (s + t) = U s * U t` and `U 0 = 1` as genuine unitary-group
identities (not merely up to phase). -/
theorem expNegITH_unitary_group {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    (∀ s t, schrodingerUnitary hH (s + t) = schrodingerUnitary hH s * schrodingerUnitary hH t)
      ∧ schrodingerUnitary hH 0 = 1 := by
  constructor
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp (schrodingerGen H (s + t))
      = NormedSpace.exp (schrodingerGen H s) * NormedSpace.exp (schrodingerGen H t)
    have hcomm : Commute (schrodingerGen H s) (schrodingerGen H t) :=
      ((Commute.refl H).smul_left _).smul_right _
    have hadd : schrodingerGen H (s + t) = schrodingerGen H s + schrodingerGen H t := by
      unfold schrodingerGen
      rw [← add_smul]
      congr 1
      push_cast
      ring
    rw [hadd, Matrix.exp_add_of_commute _ _ hcomm]
  · apply Subtype.ext
    show NormedSpace.exp (schrodingerGen H 0) = 1
    unfold schrodingerGen
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, zero_smul]
    exact NormedSpace.exp_zero

/-- The skew-Hermitian Schrödinger generator `A = -i H` for Hermitian `H`:
`star (-i H) = -(-i H)`. -/
theorem schrodingerGen_neg_i_smul_skew (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian) :
    star ((-Complex.I) • H) = -((-Complex.I) • H) := by
  rw [star_smul, show star (-Complex.I) = Complex.I by simp,
    show star H = H from by rw [Matrix.star_eq_conjTranspose]; exact hH]
  module

/-- `schrodingerGen H τ = τ • (-i H)` as a real scalar action (tower `ℝ → ℂ → Matrix`).
Rewrites the time-`τ` generator into the `t • A` form `hasDerivAt_exp_smul_const` expects. -/
theorem schrodingerGen_eq_real_smul (H : Matrix (Fin N) (Fin N) ℂ) (τ : ℝ) :
    schrodingerGen H τ = τ • ((-Complex.I) • H) := by
  unfold schrodingerGen
  rw [← smul_assoc]
  congr 1
  rw [Complex.real_smul]
  ring

/-- **The C¹ datum.** The family `U t = exp(-itH)` has derivative `U t * (-iH)` at every `t`,
for every Hermitian `H` — the hypothesis finite-dimensional Stone theorems consume. -/
theorem schrodingerUnitary_hasDerivAt (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ))
      ((schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ) * ((-Complex.I) • H)) t := by
  have hfun : (fun τ : ℝ => (schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ))
      = (fun τ : ℝ => NormedSpace.exp (τ • ((-Complex.I) • H))) := by
    funext τ
    show NormedSpace.exp (schrodingerGen H τ) = _
    rw [schrodingerGen_eq_real_smul]
  have hval : (schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ)
      = NormedSpace.exp (t • ((-Complex.I) • H)) := by
    show NormedSpace.exp (schrodingerGen H t) = _
    rw [schrodingerGen_eq_real_smul]
  rw [hfun, hval]
  exact hasDerivAt_exp_smul_const ((-Complex.I) • H) t

end Matrix
