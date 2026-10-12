/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reindexing a square matrix: multiplicativity and the trace

**Category:** 1-Mathlib (CSD-free).

`Matrix.reindex e e` relabels a square matrix along `e : m ≃ n`. Mathlib has it as a linear
equivalence (`Matrix.reindexLinearEquiv`) and as an algebra equivalence
(`Matrix.reindexAlgEquiv`), but the two facts a reindexing argument actually reaches for are
awkward to get out of those packages: that it is multiplicative on the nose, and that it leaves
the trace alone.

* `Matrix.reindex_mul` — `reindex e e M * reindex e e N = reindex e e (M * N)`, from
  `Matrix.submatrix_mul_equiv`. The algebra equivalence gives this too, but only after
  unfolding its coercion, which is the step every call site was repeating.
* `Matrix.trace_reindex` — the trace is unchanged, by `Equiv.sum_comp` on the diagonal.

Both are stated for `reindex e e` with a single equivalence on both indices, which is the only
case a square matrix admits.

*Rule of two.* `CV/CompositeArena.lean`'s `trace_compositeReindex` is the first occurrence of the
trace fact and is now a one-line consequence of `trace_reindex`; `CV/ArenaIndexBridge.lean`'s
transport lemmas are the second, and are what prompted the extraction.

## References

`Mathlib/LinearAlgebra/Matrix/Reindex.lean` (`reindexAlgEquiv`, `reindex_apply`);
`Mathlib/Data/Matrix/Mul.lean` (`submatrix_mul_equiv`); `specs/future-work.md`;
`specs/BACKLOG.md` #133.
-/

@[expose] public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n]

/-- **Reindexing is multiplicative.** -/
theorem reindex_mul [NonUnitalNonAssocSemiring R] (e : m ≃ n) (M N : Matrix m m R) :
    reindex e e M * reindex e e N = reindex e e (M * N) := by
  simp only [reindex_apply]
  exact submatrix_mul_equiv M N e.symm e.symm e.symm

/-- **Reindexing preserves the trace**: the diagonal is permuted, not changed. -/
theorem trace_reindex [AddCommMonoid R] (e : m ≃ n) (M : Matrix m m R) :
    (reindex e e M).trace = M.trace := by
  rw [trace, trace]
  simp only [diag_apply, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp e.symm fun x => M x x

end Matrix

end
