import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Mathlib upstream candidate: partial trace of a matrix over a tensor factor

**Category:** 1-Mathlib (CSD-free; Mathlib has no partial-trace construction).

For a matrix `A` on a product index `m × n` — i.e. an operator on `ℂ^m ⊗ ℂ^n` in
the Kronecker realisation — the **partial traces** trace out one tensor factor:

- `Matrix.traceRight A : Matrix m m R`, tracing out the second factor `n`
  (`(traceRight A) i j = ∑ k, A (i, k) (j, k)`);
- `Matrix.traceLeft A : Matrix n n R`, tracing out the first factor `m`.

These are the matrix-level reduced-operator maps `ρ ↦ Tr_n ρ` of quantum
information. The API records the defining property on Kronecker products
(`traceRight_kronecker : traceRight (A ⊗ₖ B) = trace B • A`), trace-preservation
(`trace_traceRight`), linearity, and that the maps preserve Hermitian-ness and
positive-semidefiniteness (`traceRight_posSemidef`) — the facts needed to send a
density operator to its reduced density operator.

The positivity proof is clean: `traceRight A = ∑ k, A.submatrix (·,k) (·,k)`, a
finite sum of principal submatrices, so `Matrix.PosSemidef.submatrix` +
`Matrix.posSemidef_sum` give the result with no test-vector bookkeeping.

## Namespace / staging

Declarations live in `namespace Matrix` (Mathlib's natural symbol namespace), so
dot notation is preserved and upstreaming requires only a file move to (or append
onto) a `Mathlib/LinearAlgebra/Matrix/PartialTrace.lean`, no symbol rename.

## Provenance

Needed for the CSD empirical suite's no-communication theorem in reduced-density
form (E3b) and no-broadcasting (E2): see `specs/qm-empirical-tests.md` §3bis and
`specs/partial-trace-plan.md`. Mathlib has no partial trace as of the pinned
revision (Lean 4.29.0-rc8).

## Consumers

- `CsdLean4/LF2/ReducedDensity.lean` (`DensityOperatorIx.reduced`).
- (planned) `CsdLean4/Empirical/QM/NoCommunication.lean` E3b reduced-density form.

## Tags

matrix, partial trace, tensor product, kronecker, density operator, positive
semidefinite
-/

open scoped Kronecker

-- The partial-trace maps are inherently two-index (matrix index + summed index);
-- the per-component `rfl`-lemmas mention only one, which trips the section-var
-- linter without indicating any real issue.
set_option linter.unusedSectionVars false

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n]

section AddCommMonoid
variable [AddCommMonoid R]

/-- **Partial trace over the second factor.** For `A` on the product index
`m × n` (an operator on `ℂ^m ⊗ ℂ^n`), `traceRight A` traces out the `n` factor:
`(traceRight A) i j = ∑ k, A (i, k) (j, k)`. -/
def traceRight (A : Matrix (m × n) (m × n) R) : Matrix m m R :=
  Matrix.of fun i j => ∑ k, A (i, k) (j, k)

/-- **Partial trace over the first factor.** `traceLeft A` traces out the `m`
factor: `(traceLeft A) i j = ∑ k, A (k, i) (k, j)`. -/
def traceLeft (A : Matrix (m × n) (m × n) R) : Matrix n n R :=
  Matrix.of fun i j => ∑ k, A (k, i) (k, j)

@[simp]
theorem traceRight_apply (A : Matrix (m × n) (m × n) R) (i j : m) :
    traceRight A i j = ∑ k, A (i, k) (j, k) := rfl

@[simp]
theorem traceLeft_apply (A : Matrix (m × n) (m × n) R) (i j : n) :
    traceLeft A i j = ∑ k, A (k, i) (k, j) := rfl

/-- `traceRight` as a finite sum of principal submatrices over the second index. -/
theorem traceRight_eq_sum_submatrix (A : Matrix (m × n) (m × n) R) :
    traceRight A = ∑ k : n, A.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
  ext i j
  simp [traceRight, Matrix.sum_apply, Matrix.submatrix_apply]

@[simp]
theorem traceRight_zero : traceRight (0 : Matrix (m × n) (m × n) R) = 0 := by
  ext i j; simp [traceRight]

theorem traceRight_add (A B : Matrix (m × n) (m × n) R) :
    traceRight (A + B) = traceRight A + traceRight B := by
  ext i j; simp [traceRight, Finset.sum_add_distrib]

end AddCommMonoid

section Smul
variable [AddCommMonoid R] [Monoid S] [DistribMulAction S R]

theorem traceRight_smul (c : S) (A : Matrix (m × n) (m × n) R) :
    traceRight (c • A) = c • traceRight A := by
  ext i j; simp [traceRight, Finset.smul_sum]

end Smul

section CommSemiring
variable [CommSemiring R]

/-- **Defining property on Kronecker products.** Tracing out the second factor of
`A ⊗ B` scales `A` by `Tr B`: `traceRight (A ⊗ₖ B) = Tr B • A`.
`(traceRight (A ⊗ₖ B)) i j = ∑ k, A i j * B k k = A i j * Tr B = (Tr B • A) i j`. -/
theorem traceRight_kronecker (A : Matrix m m R) (B : Matrix n n R) :
    traceRight (A ⊗ₖ B) = trace B • A := by
  ext i j
  simp only [traceRight_apply, kronecker_apply, smul_apply, smul_eq_mul, trace,
    diag_apply, ← Finset.mul_sum, mul_comm]

/-- **Defining property on Kronecker products (left).**
`traceLeft (A ⊗ₖ B) = Tr A • B`.
`(traceLeft (A ⊗ₖ B)) i j = ∑ k, A k k * B i j = Tr A * B i j = (Tr A • B) i j`. -/
theorem traceLeft_kronecker (A : Matrix m m R) (B : Matrix n n R) :
    traceLeft (A ⊗ₖ B) = trace A • B := by
  ext i j
  simp only [traceLeft_apply, kronecker_apply, smul_apply, smul_eq_mul, trace,
    diag_apply, ← Finset.sum_mul]

end CommSemiring

section AddCommMonoidTrace
variable [AddCommMonoid R]

/-- **Partial trace is trace-preserving.** `Tr (traceRight A) = Tr A`.
`Tr (traceRight A) = ∑ i, ∑ k, A (i,k) (i,k) = ∑ (i,k), A (i,k) (i,k) = Tr A`. -/
theorem trace_traceRight (A : Matrix (m × n) (m × n) R) :
    trace (traceRight A) = trace A := by
  simp only [trace, diag_apply, traceRight_apply]
  rw [show (∑ x : m × n, A x x) = ∑ i : m, ∑ k : n, A (i, k) (i, k) from
    Fintype.sum_prod_type _]

/-- **Partial trace is trace-preserving (left).** `Tr (traceLeft A) = Tr A`. -/
theorem trace_traceLeft (A : Matrix (m × n) (m × n) R) :
    trace (traceLeft A) = trace A := by
  simp only [trace, diag_apply, traceLeft_apply]
  rw [show (∑ x : m × n, A x x) = ∑ k : n, ∑ i : m, A (i, k) (i, k) from
    Fintype.sum_prod_type_right _]

end AddCommMonoidTrace

section Star
variable [AddCommMonoid R] [StarAddMonoid R]

/-- `traceRight` commutes with conjugate-transpose, hence preserves
Hermitian-ness. -/
theorem traceRight_conjTranspose (A : Matrix (m × n) (m × n) R) :
    (traceRight A)ᴴ = traceRight Aᴴ := by
  ext i j
  simp [traceRight, conjTranspose_apply, star_sum]

theorem traceLeft_conjTranspose (A : Matrix (m × n) (m × n) R) :
    (traceLeft A)ᴴ = traceLeft Aᴴ := by
  ext i j
  simp [traceLeft, conjTranspose_apply, star_sum]

/-- `traceRight` preserves Hermitian-ness. -/
theorem IsHermitian.traceRight {A : Matrix (m × n) (m × n) R} (hA : A.IsHermitian) :
    (traceRight A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [traceRight_conjTranspose, hA.eq]

theorem IsHermitian.traceLeft {A : Matrix (m × n) (m × n) R} (hA : A.IsHermitian) :
    (traceLeft A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [traceLeft_conjTranspose, hA.eq]

end Star

section PosSemidef
variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-- **Partial trace preserves positive-semidefiniteness.** Since
`traceRight A = ∑ k, A.submatrix (·,k) (·,k)` is a finite sum of principal
submatrices, this follows from `PosSemidef.submatrix` + `posSemidef_sum`. This is
the load-bearing fact for the reduced density operator. -/
theorem PosSemidef.traceRight {A : Matrix (m × n) (m × n) R} (hA : A.PosSemidef) :
    (Matrix.traceRight A).PosSemidef := by
  rw [traceRight_eq_sum_submatrix]
  exact posSemidef_sum _ (fun k _ => hA.submatrix (fun i => (i, k)))

/-- **Partial trace preserves positive-semidefiniteness (left).** -/
theorem PosSemidef.traceLeft {A : Matrix (m × n) (m × n) R} (hA : A.PosSemidef) :
    (Matrix.traceLeft A).PosSemidef := by
  have heq : Matrix.traceLeft A
      = ∑ k : m, A.submatrix (fun i => (k, i)) (fun i => (k, i)) := by
    ext i j
    simp [Matrix.traceLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact posSemidef_sum _ (fun k _ => hA.submatrix (fun i => (k, i)))

end PosSemidef

end Matrix
