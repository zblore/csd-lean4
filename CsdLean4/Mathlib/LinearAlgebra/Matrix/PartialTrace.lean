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

section UnitaryInvariance
variable [DecidableEq m] [DecidableEq n] [CommRing R] [StarRing R]

/-- **Partial trace is invariant under a unitary on the traced-out factor.** If
`U` is unitary (`Uᴴ U = 1`) then conjugating `M` by `U ⊗ I` does not change the
partial trace over the *first* factor:
`traceLeft ((U ⊗ₖ I) · M · (U ⊗ₖ I)ᴴ) = traceLeft M`.

This is the matrix form of "a local unitary on Alice's subsystem leaves Bob's
reduced state invariant" — the no-communication / no-signalling content. The two
Kronecker `I` factors pin the Bob indices; the Alice factors collapse through
`Uᴴ U = I`. -/
theorem traceLeft_conjTranspose_kronecker_one
    {U : Matrix m m R} (hU : Uᴴ * U = 1) (M : Matrix (m × n) (m × n) R) :
    traceLeft ((U ⊗ₖ (1 : Matrix n n R)) * M * (U ⊗ₖ (1 : Matrix n n R))ᴴ)
      = traceLeft M := by
  ext i j
  rw [traceLeft_apply, traceLeft_apply]
  -- Each `(K M Kᴴ)(k,i)(k,j)` expands; summing over `k` recombines the Alice
  -- factors into `(Uᴴ U) = 1`, collapsing to `∑ a, M (a,i) (a,j)`.
  have hexp : ∀ k : m,
      ((U ⊗ₖ (1 : Matrix n n R)) * M * (U ⊗ₖ (1 : Matrix n n R))ᴴ) (k, i) (k, j)
        = ∑ c : m, ∑ a : m, U k a * star (U k c) * M (a, i) (c, j) := by
    intro k
    simp only [Matrix.mul_apply, conjTranspose_apply, kronecker_apply, one_apply,
      Fintype.sum_prod_type, apply_ite star, star_zero, mul_ite, ite_mul,
      mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    -- Bob deltas collapsed (b = i, d = j); after collapse the outer index is the
    -- Bob-`d` survivor `c`, the inner `Finset.sum_mul` exposes the Alice index `a`.
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  -- Goal: ∑ k, (K M Kᴴ)(k,i)(k,j) = ∑ a, M (a,i)(a,j).
  -- Push the `k`-sum all the way in to recombine the Alice factors into `(Uᴴ U)`.
  simp only [hexp]
  rw [Finset.sum_comm]                     -- ∑ c, ∑ k, ∑ a, …
  rw [show (∑ c : m, ∑ k : m, ∑ a : m, U k a * star (U k c) * M (a, i) (c, j))
        = ∑ c : m, ∑ a : m, (Uᴴ * U) c a * M (a, i) (c, j) from by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [conjTranspose_apply]; ring]
  rw [hU]
  -- ∑ c, ∑ a, (1 : Matrix) c a · M (a,i)(c,j) ; collapse `c`-delta to c = a.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [one_apply_eq, one_mul]
  · intro c _ hc; rw [one_apply_ne hc, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Partial trace is invariant under a local channel on the traced-out factor.**
The Kraus-summed generalisation of `traceLeft_conjTranspose_kronecker_one`: for any
finite family of (possibly rectangular) Kraus operators `K : ι → Matrix p m` that are
**trace-preserving** (`∑ᵢ (K i)ᴴ (K i) = 1`),

`traceLeft (∑ᵢ (K i ⊗ I) · M · (K i ⊗ I)ᴴ) = traceLeft M`.

This is the **no-communication / no-signalling content for an arbitrary trace-preserving
Kraus family** (a Kraus-sum object is automatically CP, so this covers any local channel):
applying it on Alice's subsystem leaves Bob's reduced state `Tr_A` invariant. The
load-bearing hypothesis is trace-preservation alone (`∑ᵢ (K i)ᴴ (K i) = 1`, used to
recombine the Alice factors); complete positivity is not needed for the proof. The two
Kronecker `I` factors pin the Bob indices. -/
theorem traceLeft_sum_conjTranspose_kronecker_one
    {p ι : Type*} [Fintype p] [Fintype ι] {K : ι → Matrix p m R}
    (hK : ∑ l, (K l)ᴴ * (K l) = 1) (M : Matrix (m × n) (m × n) R) :
    traceLeft (∑ l, (K l ⊗ₖ (1 : Matrix n n R)) * M * (K l ⊗ₖ (1 : Matrix n n R))ᴴ)
      = traceLeft M := by
  ext i j
  rw [traceLeft_apply, traceLeft_apply]
  -- Per-Kraus expansion, collapsing the two Bob deltas (b = i, d = j).
  have hexp : ∀ (l : ι) (k : p),
      ((K l ⊗ₖ (1 : Matrix n n R)) * M * (K l ⊗ₖ (1 : Matrix n n R))ᴴ) (k, i) (k, j)
        = ∑ c : m, ∑ a : m, K l k a * star (K l k c) * M (a, i) (c, j) := by
    intro l k
    simp only [Matrix.mul_apply, conjTranspose_apply, kronecker_apply, one_apply,
      Fintype.sum_prod_type, apply_ite star, star_zero, mul_ite, ite_mul,
      mul_zero, zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  -- The Alice factors recombine into `(∑ l (K l)ᴴ (K l)) c a = (1) c a`.
  have key : ∀ c a : m,
      (∑ k : p, ∑ l : ι, K l k a * star (K l k c)) = (1 : Matrix m m R) c a := by
    intro c a
    rw [← hK, Matrix.sum_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [conjTranspose_apply]; ring
  simp only [Matrix.sum_apply, hexp]
  -- Reorder `∑ k ∑ l ∑ c ∑ a` to `∑ c ∑ a ∑ k ∑ l`, then fold `k,l` into `key`.
  conv_lhs => enter [2]; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2]; ext c; enter [2]; ext k; rw [Finset.sum_comm]
  conv_lhs => enter [2]; ext c; rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [one_apply_eq, one_mul]
  · intro c _ hc; rw [one_apply_ne hc, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

end UnitaryInvariance

section Bimodule
variable [Semiring R]

/-- **Partial trace is a left module map over `X ⊗ I`.** Pulling a first-factor
operator `X ⊗ I` out of `traceRight`:
`traceRight ((X ⊗ₖ I) · M) = X · traceRight M`. The `I` on the Bob factor lets the
`X` commute straight through the partial trace over Bob's index. -/
theorem traceRight_kronecker_one_mul [DecidableEq n]
    (X : Matrix m m R) (M : Matrix (m × n) (m × n) R) :
    traceRight ((X ⊗ₖ (1 : Matrix n n R)) * M) = X * traceRight M := by
  ext i j
  rw [Matrix.mul_apply]
  -- RHS = ∑ a, X i a * (∑ k, M (a,k)(j,k)); LHS collapses the (X⊗I) Bob-delta.
  simp only [traceRight_apply, Matrix.mul_apply, Matrix.kronecker_apply, one_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  -- LHS: ∑ k, ∑ a, ∑ b, (if a=? ...) — collapse the inner Bob-delta `b = k`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **Partial trace is a right module map over `X ⊗ I`.**
`traceRight (M · (X ⊗ₖ I)) = traceRight M · X`. -/
theorem traceRight_mul_kronecker_one [DecidableEq n]
    (M : Matrix (m × n) (m × n) R) (X : Matrix m m R) :
    traceRight (M * (X ⊗ₖ (1 : Matrix n n R))) = traceRight M * X := by
  ext i j
  rw [Matrix.mul_apply]
  -- RHS = ∑ a, (∑ k, M (i,k)(a,k)) * X a j; LHS collapses the (X⊗I) Bob-delta.
  simp only [traceRight_apply, Matrix.mul_apply, Matrix.kronecker_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, mul_zero, mul_one, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

end Bimodule

end Matrix
