/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The entries of a matrix power as a sum over paths

**Category:** 1-Mathlib (CSD-free; staged for upstream).

An entry of `M ^ n` is a sum over all index paths of `n` steps from the row to the column index,
each path weighted by the product of the entries it traverses. Mathlib carries this only for
adjacency matrices, as a count of walks (`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`); this file
is the weighted form over a commutative semiring, in the shape the sum-over-paths reading of a
matrix exponential needs: the row and column indices fixed, the sum over the intermediate states.

* `Matrix.pathWeight M p` — the weight of the path `p : Fin (n + 1) → ι`, the product
  `∏ k, M (p k) (p (k + 1))` of the entries along its `n` steps;
* `Matrix.pathWeight_cons` — prepending a state multiplies the weight by the entry of the new
  first step;
* ★ `Matrix.pow_succ_apply_eq_sum_pathWeight` — **the sum over paths**:
  `(M ^ (n + 1)) i j = ∑ p : Fin n → ι, pathWeight M (Fin.cons i (Fin.snoc p j))`, the sum over
  every choice of the `n` intermediate states of the path from `i` to `j` in `n + 1` steps.

## Honest scope

⚠️ **Commutative scalars.** The weight of a path is a `Finset` product, so the scalars are a
`CommSemiring`; over a noncommutative ring the product along a path is ordered and would be a
`List.prod`. The consumer (`Analysis/Matrix/SumOverPaths.lean`) works over `ℂ`.

References: `Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean`
(`adjMatrix_pow_apply_eq_card_walk`, the unweighted case); consumer
`Analysis/Matrix/SumOverPaths.lean`; `specs/future-work.md`, `specs/BACKLOG.md` #36.
-/

@[expose] public section

open Finset

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The weight of an `n`-step path `p` through the index set, for the matrix `M`: the product of
the entries of `M` along the steps of `p`. -/
def pathWeight (M : Matrix ι ι R) {n : ℕ} (p : Fin (n + 1) → ι) : R :=
  ∏ k : Fin n, M (p k.castSucc) (p k.succ)

omit [Fintype ι] [DecidableEq ι] in
/-- `pathWeight`, unfolded. -/
theorem pathWeight_def (M : Matrix ι ι R) {n : ℕ} (p : Fin (n + 1) → ι) :
    pathWeight M p = ∏ k : Fin n, M (p k.castSucc) (p k.succ) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A path with no steps has weight one. -/
@[simp]
theorem pathWeight_zero (M : Matrix ι ι R) (p : Fin 1 → ι) : pathWeight (n := 0) M p = 1 := by
  simp [pathWeight]

omit [Fintype ι] [DecidableEq ι] in
/-- A one-step path has the weight of its one entry. -/
theorem pathWeight_one (M : Matrix ι ι R) (p : Fin 2 → ι) :
    pathWeight (n := 1) M p = M (p 0) (p 1) := by
  simp [pathWeight]

omit [Fintype ι] [DecidableEq ι] in
/-- Prepending a state `i` to a path `q` multiplies the weight by the entry of the new first
step, from `i` to the first state of `q`. -/
theorem pathWeight_cons (M : Matrix ι ι R) {n : ℕ} (i : ι) (q : Fin (n + 1) → ι) :
    pathWeight M (Fin.cons i q) = M i (q 0) * pathWeight M q := by
  simp only [pathWeight, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.castSucc_succ,
    Fin.cons_succ]

/-- ★ **The entries of a matrix power are sums over paths.** The `(i, j)` entry of `M ^ (n + 1)` is
the sum, over every choice `p` of the `n` intermediate states, of the weight of the path
`i, p 0, …, p (n - 1), j`. -/
theorem pow_succ_apply_eq_sum_pathWeight (M : Matrix ι ι R) (n : ℕ) (i j : ι) :
    (M ^ (n + 1)) i j = ∑ p : Fin n → ι, pathWeight M (Fin.cons i (Fin.snoc p j)) := by
  induction n generalizing i with
  | zero =>
    rw [pow_succ, pow_zero, one_mul, Fintype.sum_unique, pathWeight_one, Fin.cons_zero,
      Fin.cons_one]
    congr 1
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    show M i m * pathWeight M (Fin.cons m (Fin.snoc p j))
      = pathWeight M (Fin.cons i (Fin.snoc (Fin.cons m p) j))
    rw [← Fin.cons_snoc_eq_snoc_cons, pathWeight_cons M i, Fin.cons_zero]

end Matrix
