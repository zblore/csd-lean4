/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators

/-!
# CV-1: a finite position observable on a lattice

**Category:** 3-Local (a finite position observable on a lattice).

The first constructive step of the continuous-variable track. `W4`
(`CV/ApproxCCR.lean`) proved the *no-go*: no pair of finite matrices satisfies
the exact canonical commutation relation `[Q, P] = iℏ·1`. This module builds the
first *positive* object it motivates — a genuine finite **position observable**.

On an `N`-point symmetric grid of spacing `a`, centered at the origin, the
position observable is the diagonal Hermitian matrix

    `Q_N = diag(x₀, …, x_{N-1})`,   `x_j = a · (j − (N−1)/2)`,

whose eigenvalues are exactly the `N` lattice positions (the standard basis
vector `e_j` is an eigenvector with eigenvalue `x_j`), distinct when `a ≠ 0`, and
bounded by `|a|·(N−1)/2`. This is a bounded, discrete-spectrum finite observable —
precisely the "continuous but limited" observable-value structure the CSD
finite-`N` reading predicts (`specs/csd-departures-eft.md` §3.1): finitely many
levels, evenly spaced, looking continuous for astronomically large `N`.

## CSD reading

`Q_N` is an operational position observable in a finite sector. Its spectrum is
bounded and discrete — there is a maximum and minimum representable position and
finitely many resolvable values — the finite-information-capacity picture, not a
spacetime lattice. The continuum position operator is the ideal `N → ∞` (with
`a → 0`) limit; at finite `N` position is this approximate, coarse-grained
observable. Conjugate momentum (via the finite Fourier transform) and the
approximate CCR `‖[Q_N, P_N] − iℏ·1‖ ≤ ε` are the follow-ons CV-2 / CV-3.

## Honest scope (load-bearing)

CV-1 constructs the finite position observable and proves its spectral data
(Hermitian, eigenvalues = lattice points, distinct, bounded). It does **not**
construct momentum, does **not** establish any commutation relation, and does
**not** derive continuous-variable QM. It is the position half of the finite CV
sector; momentum and the approximate CCR are CV-2 / CV-3.

## Category

Cat-1: `positionOp` and its spectral lemmas are CSD-free general facts about a
finite diagonal matrix. The CSD interpretation lives only in this docstring.

## Main results

- `positionOp_isHermitian` : `Q_N` is Hermitian (a genuine self-adjoint observable).
- `positionOp_mulVec_single` : `Q_N · e_j = x_j • e_j` (the lattice points are the
  eigenvalues, the standard basis is the position eigenbasis).
- `latticePoint_injective` : the eigenvalues are distinct for `a ≠ 0` (`N` distinct
  outcomes, a non-degenerate observable).
- `abs_latticePoint_le` : the spectrum is bounded, `|x_j| ≤ |a|·(N−1)/2`.
- `positionOp_trace_eq_zero` : the mean position is `0` (the grid is centered).
-/

@[expose] public section

namespace CSD.CV

open Matrix

variable (N : ℕ) (a : ℝ)

/-- The `j`-th lattice position on the symmetric `N`-point grid of spacing `a`,
centered at the origin: `x_j = a · (j − (N−1)/2)`. Real subtraction throughout
(no `ℕ` truncation), so the grid is `{−(N−1)/2, …, (N−1)/2}` scaled by `a`. -/
noncomputable def latticePoint (j : Fin N) : ℝ :=
  a * ((j : ℝ) - ((N : ℝ) - 1) / 2)

/-- The **finite position observable** `Q_N = diag(x₀, …, x_{N-1})`: the diagonal
matrix whose entries are the lattice positions. -/
noncomputable def positionOp : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun j => (latticePoint N a j : ℂ))

variable {N a}

@[simp] lemma positionOp_apply (i j : Fin N) :
    positionOp N a i j = if i = j then (latticePoint N a i : ℂ) else 0 := by
  simp [positionOp, Matrix.diagonal_apply]

/-- **`Q_N` is Hermitian**: a genuine self-adjoint observable (real diagonal, so
`Q_Nᴴ = Q_N`), hence has real eigenvalues. -/
theorem positionOp_isHermitian : (positionOp N a).IsHermitian := by
  unfold Matrix.IsHermitian positionOp
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

/-- **The lattice points are the eigenvalues.** The standard basis vector `e_j` is
an eigenvector of `Q_N` with eigenvalue the lattice position `x_j`:
`Q_N · e_j = x_j • e_j`. So the standard basis is the position eigenbasis and the
spectrum is `{x_0, …, x_{N-1}}`. -/
theorem positionOp_mulVec_single (j : Fin N) :
    (positionOp N a).mulVec (Pi.single j 1 : Fin N → ℂ)
      = (latticePoint N a j : ℂ) • (Pi.single j 1 : Fin N → ℂ) := by
  funext i
  rw [positionOp, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs with h
  · simp [h]
  · simp

/-- **The eigenvalues are distinct** for `a ≠ 0`: the lattice map `j ↦ x_j` is
injective, so `Q_N` has `N` distinct eigenvalues in the `N`-dimensional space — a
non-degenerate observable with `N` sharp outcomes. -/
theorem latticePoint_injective (ha : a ≠ 0) : Function.Injective (latticePoint N a) := by
  intro j k h
  unfold latticePoint at h
  have hjk : (j : ℝ) = (k : ℝ) := by
    have := mul_left_cancel₀ ha h
    linarith
  exact Fin.ext (by exact_mod_cast hjk)

/-- **The spectrum is bounded**: every lattice position satisfies
`|x_j| ≤ |a|·(N−1)/2`. So `Q_N` is a bounded observable with a maximum and minimum
representable position — the finite-information-capacity picture. -/
theorem abs_latticePoint_le (j : Fin N) :
    |latticePoint N a j| ≤ |a| * ((N : ℝ) - 1) / 2 := by
  unfold latticePoint
  rw [abs_mul]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : 1 ≤ N := by have := j.isLt; omega
    exact_mod_cast h
  have hjlt : (j : ℝ) ≤ (N : ℝ) - 1 := by
    have : (j : ℕ) + 1 ≤ N := j.isLt
    have := (by exact_mod_cast this : (j : ℝ) + 1 ≤ (N : ℝ))
    linarith
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hbound : |(j : ℝ) - ((N : ℝ) - 1) / 2| ≤ ((N : ℝ) - 1) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc |a| * |(j : ℝ) - ((N : ℝ) - 1) / 2|
      ≤ |a| * (((N : ℝ) - 1) / 2) := by
        exact mul_le_mul_of_nonneg_left hbound (abs_nonneg a)
    _ = |a| * ((N : ℝ) - 1) / 2 := by ring

/-- **The mean position is zero**: `trace Q_N = 0`, since the grid is symmetric
about the origin. Proved by the reflection `j ↦ Fin.rev j`, under which
`x_{rev j} = −x_j`, so the sum equals its own negation. -/
theorem positionOp_trace_eq_zero : (positionOp N a).trace = 0 := by
  rw [positionOp, Matrix.trace_diagonal]
  -- Reduce to the real sum, which is `0` by the reflection `j ↦ Fin.rev j`.
  have hreal : ∑ j : Fin N, latticePoint N a j = 0 := by
    have hrev : ∀ j : Fin N, latticePoint N a (Fin.rev j) = - latticePoint N a j := by
      intro j
      have hval : ((Fin.rev j : Fin N) : ℝ) = (N : ℝ) - 1 - (j : ℝ) := by
        have h1 : ((Fin.rev j).val : ℕ) = N - ((j : ℕ) + 1) := Fin.val_rev j
        have hjlt : (j : ℕ) < N := j.isLt
        rw [h1, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ N)]
        push_cast; ring
      unfold latticePoint; rw [hval]; ring
    -- Reindexing by the reversal permutation leaves the sum unchanged.
    have hsum : (∑ j : Fin N, latticePoint N a (Fin.rev j))
        = ∑ j : Fin N, latticePoint N a j := by
      simpa using Equiv.sum_comp Fin.revPerm (latticePoint N a)
    have h2 : (∑ j : Fin N, latticePoint N a j)
        + ∑ j : Fin N, latticePoint N a (Fin.rev j) = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun j _ => by rw [hrev j]; ring
    rw [hsum] at h2
    linarith
  rw [← Complex.ofReal_sum, hreal, Complex.ofReal_zero]

end CSD.CV
