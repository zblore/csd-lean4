/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

/-!
# Empirical: Mermin–Peres magic square (no LHV assignment)

**Category:** 3-Local. The combinatorial impossibility is QM-generic
and promotion-ready to 2-Framework on demand; the QM operator-product
identities behind the constraints are documented in this file's
docstring and would be proved as a follow-up tranche
(see "QM-side operator identities" §).

## What Mermin–Peres says

Consider the 3×3 grid of two-qubit Pauli observables (Mermin 1990):

```
            col 0          col 1          col 2
row 0   σ_x ⊗ I       I ⊗ σ_x       σ_x ⊗ σ_x       row 0 product = +I
row 1   I ⊗ σ_y       σ_y ⊗ I       σ_y ⊗ σ_y       row 1 product = +I
row 2   σ_x ⊗ σ_y     σ_y ⊗ σ_x     σ_z ⊗ σ_z       row 2 product = +I

      col 0 prod      col 1 prod    col 2 prod
        = +I            = +I          = -I
```

- The three observables in each row pairwise commute (so they can be
  measured simultaneously). Likewise for each column.
- Each row's operator product equals `+I`. So QM predicts the
  product of measurement outcomes along any row equals `+1`.
- Two columns' operator products equal `+I`; the third (column 2)
  equals `-I`. So QM predicts column-2 outcomes multiply to `-1`,
  others to `+1`.

If we assign classical ±1 values `λ(i,j)` to each cell satisfying
these six product constraints, multiplying all 9 cells via rows
gives `(+1)·(+1)·(+1) = +1`, while via columns it gives
`(+1)·(+1)·(-1) = -1`. Same product, contradictory value. QED.

This is the **Mermin–Peres magic square / Peres-Mermin square**
contextuality proof: a single-shot no-go for hidden-variable models
of two qubits, structurally similar to GHZ (3 qubits) and
Kochen–Specker (any dimension ≥ 3) but in the smallest non-trivial
multi-qubit setting.

## Distinction from CHSH / GHZ / KS

- **CHSH (Bell.lean):** statistical inequality; needs many trials.
- **GHZ (Multipartite/GHZ.lean):** algebraic single-shot, three-qubit,
  local-hidden-variable specific.
- **KS (Contextuality/KS18.lean):** structural contextuality on
  18 rays in `ℝ⁴`; counts-based finite combinatorial argument.
- **Mermin–Peres (this file):** algebraic single-shot, two qubits,
  contextuality (not specifically non-local). Smallest finite
  no-go grid.

## Experimental verification

- Mermin 1990: *Phys. Rev. Lett.* **65**, 3373.
- Peres 1990: *Phys. Lett. A* **151**, 107.
- Cabello 2008: extension to a state-independent proof.

## QM-side operator identities (all proved below)

The six identities driving the constraints, all 4×4 matrix equalities, are
proved as `mermin_peres_R0` .. `mermin_peres_C2` further down in this file (an
earlier "deferred to a follow-up tranche" note is superseded):

```
R0: (σ_x ⊗ I)(I ⊗ σ_x)(σ_x ⊗ σ_x) = +I        -- from σ_x² = I
R1: (I ⊗ σ_y)(σ_y ⊗ I)(σ_y ⊗ σ_y) = +I        -- from σ_y² = I
R2: (σ_x ⊗ σ_y)(σ_y ⊗ σ_x)(σ_z ⊗ σ_z) = +I    -- from σ_x σ_y σ_z = iI
                                                  and (iI)(-iI) = +I
C0: (σ_x ⊗ I)(I ⊗ σ_y)(σ_x ⊗ σ_y) = +I        -- mixed-axis pairs square
C1: (I ⊗ σ_x)(σ_y ⊗ I)(σ_y ⊗ σ_x) = +I
C2: (σ_x ⊗ σ_x)(σ_y ⊗ σ_y)(σ_z ⊗ σ_z) = -I    -- (σ_x σ_y σ_z)² = (iI)² = -I
```

Each follows from `Matrix.mul_kronecker_mul`,
`Matrix.UnitaryGroup.pauliDot_sq` (where applicable), and the standard
Pauli relations σ_x σ_y = iσ_z, σ_y σ_x = -iσ_z, σ_z² = I — proved at the
operator level (mirroring the GHZ Mermin-expectation proofs in style) as the
`mermin_peres_R0` .. `_C2` theorems below.

## What this file proves

`no_lhv_mermin_peres`: no `λ : Fin 3 × Fin 3 → {±1}` satisfies all
six row/column sign constraints. Combinatorial, axiom-clean.

The contradiction obtains by multiplying all 9 cells two ways: along
rows (product `+1`) and along columns (product `-1`).

## Honest reading

This file's **theorem** is the combinatorial LHV impossibility:
given a 3×3 grid of ±1 values constrained as above, no such grid
exists. The **QM relevance** of this impossibility — i.e., that the
constraints in fact reflect operator-product identities — is
documented in prose but not separately proven here. A future tranche
should add the 6 operator-identity theorems (similar in flavor to
GHZ's four Mermin expectations) to close that loop.
-/

namespace CSD
namespace Empirical
namespace MerminPeres

/-- **No LHV assignment to the Mermin–Peres 3×3 grid.**

For any `λ : Fin 3 × Fin 3 → ℤ` taking values in `{±1}` satisfying
the six row-and-column product constraints (rows all `+1`; columns
`+1, +1, -1`), a contradiction follows by counting the all-cells
product two ways.

This is the algebraic Mermin–Peres contextuality theorem: a finite
combinatorial single-shot no-go for ±1 hidden-variable assignments
on the 3×3 grid of two-qubit Pauli observables (see file docstring
for the operator identities motivating the constraints). -/
theorem no_lhv_mermin_peres :
    ¬ ∃ (lambda : Fin 3 → Fin 3 → ℤ),
      (∀ i j, lambda i j = 1 ∨ lambda i j = -1) ∧
      -- Three row products = +1
      (lambda 0 0 * lambda 0 1 * lambda 0 2 = 1) ∧
      (lambda 1 0 * lambda 1 1 * lambda 1 2 = 1) ∧
      (lambda 2 0 * lambda 2 1 * lambda 2 2 = 1) ∧
      -- Two column products = +1; third column product = -1
      (lambda 0 0 * lambda 1 0 * lambda 2 0 = 1) ∧
      (lambda 0 1 * lambda 1 1 * lambda 2 1 = 1) ∧
      (lambda 0 2 * lambda 1 2 * lambda 2 2 = -1) := by
  rintro ⟨lambda, _hpm, hr0, hr1, hr2, hc0, hc1, hc2⟩
  -- Compute the all-cells product two ways and derive +1 = -1.
  have h_rows :
      (lambda 0 0 * lambda 0 1 * lambda 0 2)
        * (lambda 1 0 * lambda 1 1 * lambda 1 2)
        * (lambda 2 0 * lambda 2 1 * lambda 2 2) = 1 := by
    rw [hr0, hr1, hr2]
    ring
  have h_cols :
      (lambda 0 0 * lambda 1 0 * lambda 2 0)
        * (lambda 0 1 * lambda 1 1 * lambda 2 1)
        * (lambda 0 2 * lambda 1 2 * lambda 2 2) = -1 := by
    rw [hc0, hc1, hc2]
    ring
  have h_eq :
      (lambda 0 0 * lambda 0 1 * lambda 0 2)
        * (lambda 1 0 * lambda 1 1 * lambda 1 2)
        * (lambda 2 0 * lambda 2 1 * lambda 2 2)
      = (lambda 0 0 * lambda 1 0 * lambda 2 0)
          * (lambda 0 1 * lambda 1 1 * lambda 2 1)
          * (lambda 0 2 * lambda 1 2 * lambda 2 2) := by ring
  rw [h_rows, h_cols] at h_eq
  exact absurd h_eq (by norm_num)

/-! ## QM-side operator identities

The 9 two-qubit Pauli observables in the Mermin–Peres grid, with the
row/column product identities `R0..R2, C0..C2`. The QM constraints
in `no_lhv_mermin_peres` are exactly the eigenvalue products that
follow from these operator identities (e.g., R0 `= +I` forces row 0's
outcome product to be `+1`; C2 `= -I` forces column 2's outcome product
to be `-1`).

Self-contained: defines `sigmaX, sigmaY, sigmaZ : Matrix (Fin 2) (Fin 2) ℂ`
directly via `!![..]` notation; does not depend on the LF3 `pauliDot`
framework. The proof pattern uses `Matrix.mul_kronecker_mul` to reduce
each 4×4 product to two 2×2 Pauli-algebra computations.
-/

open scoped Kronecker
open Matrix Complex

/-- The Pauli X matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix. -/
noncomputable def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The Pauli Z matrix. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-! ### Pauli algebraic identities -/

@[simp] lemma sigmaX_sq : sigmaX * sigmaX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

@[simp] lemma sigmaY_sq : sigmaY * sigmaY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaY, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply,
          Complex.I_mul_I]

@[simp] lemma sigmaZ_sq : sigmaZ * sigmaZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

/-- `σ_x σ_y = i · σ_z`. -/
lemma sigmaX_mul_sigmaY : sigmaX * sigmaY = I • sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, sigmaY, sigmaZ, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]

/-- `σ_y σ_x = -i · σ_z`. -/
lemma sigmaY_mul_sigmaX : sigmaY * sigmaX = (-I) • sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, sigmaY, sigmaZ, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]

/-! ### Row product identities

Each row of the Mermin–Peres grid:
- Row 0: `(σ_x ⊗ I)(I ⊗ σ_x)(σ_x ⊗ σ_x) = +I`
- Row 1: `(I ⊗ σ_y)(σ_y ⊗ I)(σ_y ⊗ σ_y) = +I`
- Row 2: `(σ_x ⊗ σ_y)(σ_y ⊗ σ_x)(σ_z ⊗ σ_z) = +I`

The first two reduce to `σ_a² ⊗ σ_a² = I` after `mul_kronecker_mul`.
The third uses `σ_x σ_y σ_z = i·I` and `σ_y σ_x σ_z = -i·I`,
giving `(i)(-i) = +1` in the scalar factor and `I ⊗ I = I`. -/

/-- **Row 0 product**: `(σ_x ⊗ I)(I ⊗ σ_x)(σ_x ⊗ σ_x) = I`. -/
lemma mermin_peres_R0 :
    (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaX) *
        (sigmaX ⊗ₖ sigmaX) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, sigmaX_sq, Matrix.one_kronecker_one]

/-- **Row 1 product**: `(I ⊗ σ_y)(σ_y ⊗ I)(σ_y ⊗ σ_y) = I`. -/
lemma mermin_peres_R1 :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaY) *
      (sigmaY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (sigmaY ⊗ₖ sigmaY) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, sigmaY_sq, Matrix.one_kronecker_one]

/-- **Row 2 product**: `(σ_x ⊗ σ_y)(σ_y ⊗ σ_x)(σ_z ⊗ σ_z) = I`.

Uses `σ_x σ_y σ_z = (i·σ_z) σ_z = i·I` and `σ_y σ_x σ_z = (-i·σ_z) σ_z = -i·I`,
giving the scalar factor `i · (-i) = 1` and `I ⊗ I = I`. -/
lemma mermin_peres_R2 :
    (sigmaX ⊗ₖ sigmaY) * (sigmaY ⊗ₖ sigmaX) * (sigmaZ ⊗ₖ sigmaZ) = 1 := by
  rw [← Matrix.mul_kronecker_mul, sigmaX_mul_sigmaY, sigmaY_mul_sigmaX,
      ← Matrix.mul_kronecker_mul]
  simp only [Matrix.smul_mul, sigmaZ_sq,
             Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
             Matrix.one_kronecker_one]
  rw [show (-I : ℂ) * I = 1 from by rw [neg_mul, I_mul_I]; ring, one_smul]

/-! ### Column product identities

- Col 0: `(σ_x ⊗ I)(I ⊗ σ_y)(σ_x ⊗ σ_y) = +I`
- Col 1: `(I ⊗ σ_x)(σ_y ⊗ I)(σ_y ⊗ σ_x) = +I`
- Col 2: `(σ_x ⊗ σ_x)(σ_y ⊗ σ_y)(σ_z ⊗ σ_z) = -I`

C0 and C1 reduce to `σ_a² ⊗ σ_a² = I`. C2 — the load-bearing one for
the LHV contradiction — uses `(σ_x σ_y σ_z)² = (i·I)² = -I`. -/

/-- **Column 0 product**: `(σ_x ⊗ I)(I ⊗ σ_y)(σ_x ⊗ σ_y) = I`. -/
lemma mermin_peres_C0 :
    (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaY) *
        (sigmaX ⊗ₖ sigmaY) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, sigmaX_sq, sigmaY_sq,
      Matrix.one_kronecker_one]

/-- **Column 1 product**: `(I ⊗ σ_x)(σ_y ⊗ I)(σ_y ⊗ σ_x) = I`. -/
lemma mermin_peres_C1 :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaX) *
      (sigmaY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (sigmaY ⊗ₖ sigmaX) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, sigmaY_sq, sigmaX_sq,
      Matrix.one_kronecker_one]

/-- **Column 2 product**: `(σ_x ⊗ σ_x)(σ_y ⊗ σ_y)(σ_z ⊗ σ_z) = -I`.

The load-bearing identity. Both factors `σ_x σ_y σ_z = i·I` give
a scalar factor of `i·i = -1` and `I ⊗ I = I`. -/
lemma mermin_peres_C2 :
    (sigmaX ⊗ₖ sigmaX) * (sigmaY ⊗ₖ sigmaY) * (sigmaZ ⊗ₖ sigmaZ) = -1 := by
  rw [← Matrix.mul_kronecker_mul, sigmaX_mul_sigmaY,
      ← Matrix.mul_kronecker_mul]
  simp only [Matrix.smul_mul, sigmaZ_sq,
             Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
             Matrix.one_kronecker_one, I_mul_I]
  exact neg_one_smul ℂ _

end MerminPeres
end Empirical
end CSD
