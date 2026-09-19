/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.TrotterProduct
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PathSum

/-!
# The sum over paths: Feynman's formulation at finite dimension

**Category:** 1-Mathlib (CSD-free; staged for upstream).

For a splitting `A + B` of a skew-Hermitian generator, the `(i, j)` entry of `exp (A + B)` is the
limit, as the number of steps grows, of a sum over all discrete paths from `i` to `j` of the
product of the one-step amplitudes along the path. This is Feynman's sum over histories as a
theorem rather than a postulate, in the finite-dimensional setting where every object is a matrix:
the "paths" are sequences of basis states, the "action" is the product of transfer-matrix entries,
and the limit is the Lie–Trotter product formula read entry by entry through the path expansion
of a matrix power.

* `Matrix.trotterStep A B n = exp (A / n) * exp (B / n)` — the one-step transfer matrix of the
  splitting into `n` steps; its `(i, j)` entry is `∑ k, exp (A / n) i k * exp (B / n) k j`
  (`Matrix.mul_apply`), the amplitude of one step through the intermediate state `k`;
* `Matrix.tendsto_apply_of_tendsto` — convergence in the operator norm gives convergence of
  every entry;
* `Matrix.trotterStep_pow_apply_tendsto` — the Trotter approximants converge entrywise;
* ★★ `Matrix.exp_add_apply_tendsto_sum_pathWeight` — **the sum over paths**: the `(i, j)` entry
  of `exp (A + B)` is the limit of
  `∑ p : Fin n → m, pathWeight (trotterStep A B (n + 1)) (i, p, j)`, the sum over every
  sequence of `n` intermediate states of the product of the `n + 1` one-step amplitudes;
* `Matrix.conjTranspose_neg_I_mul_smul_of_isHermitian` — for Hermitian `H` the Schrödinger
  generator `-(i t) H` is skew-Hermitian, and
  ★★ `Matrix.exp_neg_I_mul_smul_add_apply_tendsto_sum_pathWeight` — the same statement for a
  Hamiltonian `H₁ + H₂` split into two Hermitian parts (kinetic and potential, or any other split)
  at time `t`: the propagator's matrix element is the limit of sums over paths of products of the
  short-time propagators `exp (-(i t/(n+1)) H₁) exp (-(i t/(n+1)) H₂)`.

## Honest scope

⚠️ **Finite dimension, discrete paths.** This is the sum over paths of a finite-level system: no
continuum of positions, no measure on path space, no action functional. It is what the corpus's
finite-dimensional reconstruction can say, and it is exact. The continuum path integral (Wiener
measure and Feynman–Kac in imaginary time, or the Trotter–Kato limit for unbounded generators) is
a different rung and is not here.

⚠️ **The limit, not a rate.** The convergence is inherited from `trotter_skew`, whose bound is
`O(1/n)` in the operator norm; no rate is restated here entrywise.

References: R. P. Feynman, *Space-time approach to non-relativistic quantum mechanics*, Rev. Mod.
Phys. 20, 367 (1948); E. Nelson, *Feynman integrals and the Schrödinger equation*, J. Math. Phys.
5, 332 (1964), the Trotter route; `Analysis/Matrix/TrotterProduct.lean` (`trotter_skew`);
`LinearAlgebra/Matrix/PathSum.lean` (`pow_succ_apply_eq_sum_pathWeight`); `specs/future-work.md`,
`specs/BACKLOG.md` #36.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace Filter Topology

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- The one-step transfer matrix of the splitting `A + B` into `n` steps:
`exp (A / n) * exp (B / n)`. Its `(i, j)` entry is the amplitude of one step from `i` to `j`,
summed over the intermediate state between the `A`-half and the `B`-half of the step
(`Matrix.mul_apply`). The quantitative entry bound `norm_entry_le_l2_opNorm`
(`Analysis/Matrix/L2OpNormEntry.lean`) is the companion of `tendsto_apply_of_tendsto` below. -/
noncomputable def trotterStep (A B : Matrix m m ℂ) (n : ℕ) : Matrix m m ℂ :=
  exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)

omit [Nonempty m] in
/-- `trotterStep`, unfolded. -/
theorem trotterStep_def (A B : Matrix m m ℂ) (n : ℕ) :
    trotterStep A B n = exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B) :=
  rfl

omit [Nonempty m] in
/-- The one-step amplitude, as the sum over the intermediate state of the step. -/
theorem trotterStep_apply (A B : Matrix m m ℂ) (n : ℕ) (i j : m) :
    trotterStep A B n i j = ∑ k, exp ((n : ℝ)⁻¹ • A) i k * exp ((n : ℝ)⁻¹ • B) k j :=
  Matrix.mul_apply

omit [Fintype m] [DecidableEq m] [Nonempty m] in
/-- Convergence of a sequence of matrices in the operator norm gives convergence of every entry
(the operator-norm topology is the product topology, and the entry map is continuous). -/
theorem tendsto_apply_of_tendsto {f : ℕ → Matrix m m ℂ} {X : Matrix m m ℂ}
    (h : Tendsto f atTop (𝓝 X)) (i j : m) :
    Tendsto (fun n => f n i j) atTop (𝓝 (X i j)) :=
  ((continuous_id.matrix_elem i j).tendsto X).comp h

/-- The Trotter approximants converge entry by entry. -/
theorem trotterStep_pow_apply_tendsto {A B : Matrix m m ℂ} (hA : Aᴴ = -A) (hB : Bᴴ = -B)
    (i j : m) :
    Tendsto (fun n : ℕ => (trotterStep A B n ^ n) i j) atTop (𝓝 (exp (A + B) i j)) :=
  tendsto_apply_of_tendsto (trotter_skew hA hB) i j

/-- ★★ **The sum over paths.** For skew-Hermitian `A` and `B`, the `(i, j)` entry of `exp (A + B)`
is the limit, as `n → ∞`, of the sum over every sequence `p` of `n` intermediate basis states of
the product of the `n + 1` one-step amplitudes of `trotterStep A B (n + 1)` along the path
`i, p 0, …, p (n - 1), j`. -/
theorem exp_add_apply_tendsto_sum_pathWeight {A B : Matrix m m ℂ} (hA : Aᴴ = -A)
    (hB : Bᴴ = -B) (i j : m) :
    Tendsto
      (fun n : ℕ =>
        ∑ p : Fin n → m, pathWeight (trotterStep A B (n + 1)) (Fin.cons i (Fin.snoc p j)))
      atTop (𝓝 (exp (A + B) i j)) := by
  have h := (trotterStep_pow_apply_tendsto hA hB i j).comp (tendsto_add_atTop_nat 1)
  refine Filter.Tendsto.congr (fun n => ?_) h
  exact pow_succ_apply_eq_sum_pathWeight _ n i j

omit [Fintype m] [DecidableEq m] [Nonempty m] in
/-- For Hermitian `H` and real `t`, the Schrödinger generator `-(i t) H` is skew-Hermitian. -/
theorem conjTranspose_neg_I_mul_smul_of_isHermitian {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (t : ℝ) :
    ((-(t : ℂ) * Complex.I) • H)ᴴ = -((-(t : ℂ) * Complex.I) • H) := by
  rw [Matrix.conjTranspose_smul, hH.eq, ← neg_smul]
  congr 1
  simp

/-- ★★ **The sum over paths for a split Hamiltonian.** For Hermitian `H₁`, `H₂` and a real time `t`,
the matrix element of the propagator `exp (-(i t) (H₁ + H₂))` between the basis states `i` and `j`
is the limit of the sum over every sequence of `n` intermediate states of the product of the
short-time propagators `exp (-(i t/(n+1)) H₁) exp (-(i t/(n+1)) H₂)` along the path. -/
theorem exp_neg_I_mul_smul_add_apply_tendsto_sum_pathWeight {H₁ H₂ : Matrix m m ℂ}
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian) (t : ℝ) (i j : m) :
    Tendsto
      (fun n : ℕ =>
        ∑ p : Fin n → m,
          pathWeight
            (trotterStep ((-(t : ℂ) * Complex.I) • H₁) ((-(t : ℂ) * Complex.I) • H₂) (n + 1))
            (Fin.cons i (Fin.snoc p j)))
      atTop (𝓝 (exp ((-(t : ℂ) * Complex.I) • (H₁ + H₂)) i j)) := by
  rw [smul_add]
  exact exp_add_apply_tendsto_sum_pathWeight (conjTranspose_neg_I_mul_smul_of_isHermitian h₁ t)
    (conjTranspose_neg_I_mul_smul_of_isHermitian h₂ t) i j

end Matrix
