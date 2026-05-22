import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Star.Unitary

/-!
# Compactness and measurability of the matrix unitary group

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

For `N : ℕ`, the matrix unitary group `Matrix.unitaryGroup (Fin N) ℂ`
is a compact Hausdorff topological group:

- topological group: from Mathlib's `Topology/Algebra/Star/Unitary.lean`
  (`unitary R` is a topological group whenever R is a topological star
  monoid with continuous multiplication and continuous star);
- compact: closed in `Matrix (Fin N) (Fin N) ℂ` (from
  `isClosed_unitary`) plus bounded (each entry's modulus ≤ 1 because
  columns are ℓ²-unit), and `Matrix (Fin N) (Fin N) ℂ` is a finite-dim
  normed space over `ℂ` (proper, by Heine-Borel via
  `FiniteDimensional.proper_rclike`).

This is the substrate Mathlib's `MeasureTheory.Measure.haar` needs to
produce a Haar measure on `Matrix.unitaryGroup (Fin N) ℂ`. The remaining
ingredients (`MeasurableSpace`, `BorelSpace`) are also installed here.

## Main results

- `Matrix.UnitaryGroup.val_norm_apply_le_one`: entry bound for unitary matrices.
- `Matrix.UnitaryGroup.val_norm_le_one`: matrix-norm bound (L∞-elementwise).
- `Matrix.UnitaryGroup.instCompactSpace`: compactness instance.
- `Matrix.UnitaryGroup.instMeasurableSpace`: Borel σ-algebra.
- `Matrix.UnitaryGroup.instBorelSpace`: witness that the σ-algebra is Borel.

## Hypothesis pattern

Specialised to `Matrix.unitaryGroup (Fin N) ℂ`. The argument works for
any `Matrix.unitaryGroup n α` where `n` is finite and `α` is an `RCLike`
field, but we install the concrete case used by LF4's eventual SU(N)
Haar construction.

## Provenance

Staged as upstream Mathlib material. The file is intended to land in
`Mathlib/LinearAlgebra/Matrix/UnitaryCompact.lean` (or similar) once
usage stabilises.

## Tags

unitary group, compactness, Haar measure
-/

open scoped Matrix.Norms.Elementwise

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-- For a unitary matrix `A`, the sum of squared moduli of any column
equals 1. This is the j-th diagonal entry of `star A * A = 1`. -/
lemma sum_norm_sq_col (A : Matrix.unitaryGroup (Fin N) ℂ) (j : Fin N) :
    ∑ k : Fin N, ‖A.val k j‖ ^ 2 = 1 := by
  -- Start from the unitarity identity `star A.val * A.val = 1`.
  have h_unit : (star A.val : Matrix (Fin N) (Fin N) ℂ) * A.val
                  = (1 : Matrix (Fin N) (Fin N) ℂ) :=
    Unitary.coe_star_mul_self A
  -- Evaluate at (j, j): the (j,j) entry equals 1.
  have h_jj : ((star A.val : Matrix (Fin N) (Fin N) ℂ) * A.val) j j = 1 := by
    rw [h_unit, Matrix.one_apply_eq]
  -- Expand the matrix product:
  --   ∑ k, (star A.val) j k * A.val k j = 1.
  rw [Matrix.mul_apply] at h_jj
  -- Use Matrix.star_apply : (star M) j k = star (M k j), so the LHS
  -- becomes ∑ k, star (A.val k j) * A.val k j.
  -- For complex numbers, star z * z = ↑(‖z‖²) (as a complex coercion of a real).
  have h_eq : ∀ k : Fin N,
      (star A.val : Matrix (Fin N) (Fin N) ℂ) j k * A.val k j
        = ((‖A.val k j‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Matrix.star_apply]
    exact_mod_cast Complex.conj_mul' (A.val k j)
  rw [Finset.sum_congr rfl (fun k _ => h_eq k)] at h_jj
  -- Now h_jj : (∑ k, ↑(‖A.val k j‖^2 : ℝ) : ℂ) = 1
  -- Push the cast: ↑(∑ ‖A k j‖²) = 1, so ∑ ‖A k j‖² = 1.
  rw [← Complex.ofReal_sum] at h_jj
  exact_mod_cast h_jj

/-- Each entry of a unitary matrix has modulus ≤ 1. Follows from
`sum_norm_sq_col`: `‖A_ij‖² ≤ ∑_k ‖A_kj‖² = 1`. -/
lemma val_norm_apply_le_one (A : Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) :
    ‖A.val i j‖ ≤ 1 := by
  have h_sum : ∑ k : Fin N, ‖A.val k j‖ ^ 2 = 1 := sum_norm_sq_col A j
  have h_i_le : ‖A.val i j‖ ^ 2 ≤ ∑ k, ‖A.val k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖A.val k j‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  rw [h_sum] at h_i_le
  -- h_i_le : ‖A.val i j‖² ≤ 1
  have h_nn : 0 ≤ ‖A.val i j‖ := norm_nonneg _
  nlinarith

/-- The L∞-elementwise matrix norm of a unitary matrix is ≤ 1. -/
lemma val_norm_le_one (A : Matrix.unitaryGroup (Fin N) ℂ) :
    ‖A.val‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  exact fun i j => val_norm_apply_le_one A i j

/-- The unitary group is bounded as a subset of `Matrix (Fin N) (Fin N) ℂ`. -/
lemma isBounded_underlyingSet :
    Bornology.IsBounded
      (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  refine Metric.isBounded_iff.mpr ⟨2, ?_⟩
  rintro A hA B hB
  rw [dist_eq_norm]
  calc ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
    _ ≤ 1 + 1 := add_le_add (val_norm_le_one ⟨A, hA⟩) (val_norm_le_one ⟨B, hB⟩)
    _ = 2 := by norm_num

/-- The unitary group is closed in `Matrix (Fin N) (Fin N) ℂ`.
Mathlib generic via `isClosed_unitary` (requires T1 ambient, ContinuousStar,
ContinuousMul — all satisfied for `Matrix _ _ ℂ`). -/
lemma isClosed_underlyingSet :
    IsClosed (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) :=
  isClosed_unitary

/-- The matrix unitary group is compact.

Routes through `Metric.isCompact_iff_isClosed_isBounded` on the
finite-dim normed `Matrix (Fin N) (Fin N) ℂ` (proper via
`FiniteDimensional.proper_rclike`), discharging `IsClosed` via
`isClosed_underlyingSet` and `IsBounded` via `isBounded_underlyingSet`. -/
instance instCompactSpace : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := by
  haveI : ProperSpace (Matrix (Fin N) (Fin N) ℂ) :=
    FiniteDimensional.proper_rclike ℂ _
  have h_compact :
      IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Submonoid _) :
        Set (Matrix (Fin N) (Fin N) ℂ)) :=
    Metric.isCompact_of_isClosed_isBounded
      isClosed_underlyingSet isBounded_underlyingSet
  exact isCompact_iff_compactSpace.mp h_compact

/-- The matrix unitary group carries the Borel σ-algebra induced from
its subspace topology. -/
noncomputable instance instMeasurableSpace :
    MeasurableSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  borel _

instance instBorelSpace : BorelSpace (Matrix.unitaryGroup (Fin N) ℂ) := ⟨rfl⟩

end Matrix.UnitaryGroup
