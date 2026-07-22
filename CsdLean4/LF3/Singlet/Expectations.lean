/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Singlet.State

/-!
# LF3 Singlet / Expectations: the headline 4×4 Pauli expectation calculation

**Category:** 3-Local (LF3 left/right zero expectations and `singlet_pauli_correlation = −a·b`).

Paper §6.

Three theorems on the Bell singlet:
- `singlet_left_pauli_expectation_zero : ⟨ψ⁻ | σ·a ⊗ I | ψ⁻⟩ = 0`
- `singlet_right_pauli_expectation_zero : ⟨ψ⁻ | I ⊗ σ·b | ψ⁻⟩ = 0`
- `singlet_pauli_correlation : ⟨ψ⁻ | σ·a ⊗ σ·b | ψ⁻⟩ = -a·b`

Strategy: a single helper lemma `expectation_formula` reduces the expectation
on any `(Fin 2 × Fin 2)`-indexed matrix to a `(1/2) · (sum of 4 entries)`
form. The three theorems then evaluate the entries of `sigmaDotLeft / Right /
Joint`.

The proof of `expectation_formula` is a 4×4 inner-product unfolding: reduce
to a dot product via `EuclideanSpace.inner_eq_star_dotProduct`, expand both
sums over `Fin 2 × Fin 2`, push `star` past pointwise application with
`Pi.star_apply`, substitute the four `singlet_apply_*` values (12 of 16
terms vanish from factors of zero), and close with `ring_nf` + the
`((√2)⁻¹)² = 1/2` helper.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Matrix

namespace CSD
namespace LF3

/-- Auxiliary: at index `(0, 0)` the singlet is zero. -/
lemma singlet_apply_00 : singlet (0, 0) = 0 := by
  simp [singlet, EuclideanSpace.single]

/-- Auxiliary: at index `(0, 1)` the singlet is `1/√2`. -/
lemma singlet_apply_01 : singlet (0, 1) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [singlet, EuclideanSpace.single]

/-- Auxiliary: at index `(1, 0)` the singlet is `−1/√2`. -/
lemma singlet_apply_10 : singlet (1, 0) = -((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [singlet, EuclideanSpace.single]

/-- Auxiliary: at index `(1, 1)` the singlet is zero. -/
lemma singlet_apply_11 : singlet (1, 1) = 0 := by
  simp [singlet, EuclideanSpace.single]

/-- Squaring the real `(√2)⁻¹` coerced to `ℂ` gives `1/2`. -/
lemma inv_sqrt_two_sq :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **Expectation formula.** On the Bell singlet, the expectation of an
    arbitrary `(Fin 2 × Fin 2)`-indexed matrix reduces to a half-sum over four
    specific matrix entries. The 12 of 16 double-sum terms vanish (each has a
    `singlet (0,0) = 0` or `singlet (1,1) = 0` factor); the surviving 4 factor
    through `((√2)⁻¹)² = 1/2`. -/
theorem expectation_formula (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expectation M
      = (1/2 : ℂ) *
          (M (0,1) (0,1) - M (0,1) (1,0) - M (1,0) (0,1) + M (1,0) (1,0)) := by
  unfold expectation
  -- Reduce the inner product to a dotProduct: ⟨x, M y⟩ = M·y ⬝ᵥ star x.
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin,
      dotProduct, Fintype.sum_prod_type]
  -- Expand the outer sum and the inner mulVec sums over Fin 2 × Fin 2.
  -- `Pi.star_apply` pushes `star` past the function application
  -- so the `singlet_apply_*` rewrites can match the outer occurrences.
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct,
             Fintype.sum_prod_type, Pi.star_apply]
  -- Substitute the four explicit singlet values and normalize `star`:
  -- `star 0 = 0`, `star (-x) = -(star x)`, and `star ((√2)⁻¹) = (√2)⁻¹`
  -- (the inverse is real).
  simp only [show singlet.ofLp (0, 0) = (0 : ℂ) from singlet_apply_00,
             show singlet.ofLp (0, 1) = ((Real.sqrt 2 : ℂ)⁻¹) from singlet_apply_01,
             show singlet.ofLp (1, 0) = -((Real.sqrt 2 : ℂ)⁻¹) from singlet_apply_10,
             show singlet.ofLp (1, 1) = (0 : ℂ) from singlet_apply_11,
             star_zero, star_neg,
             show star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) by
               rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]]
  -- Of the 16 double-sum terms, 12 contain a factor `0`; the surviving 4 each
  -- have a `((√2)⁻¹) * ((√2)⁻¹)` factor that must be reduced to `1/2`.
  -- Defensive close: `linear_combination` over `inv_sqrt_two_sq` with an
  -- explicit coefficient `(M(0,1)(0,1) - M(0,1)(1,0) - M(1,0)(0,1) + M(1,0)(1,0))`.
  -- Independent of `ring_nf`'s normalisation: the goal becomes a `ring` identity
  -- in `(Real.sqrt 2 : ℂ)⁻¹` and the four `M` entries once the hypothesis is
  -- subtracted off, which does not depend on whether the normal form picks
  -- `c * c` or `c ^ 2` for the squared inverse.
  linear_combination
    (M (0,1) (0,1) - M (0,1) (1,0) - M (1,0) (0,1) + M (1,0) (1,0))
      * inv_sqrt_two_sq

/-! ### Pauli matrix entries (auxiliaries) -/

/-- `pauliDot a 0 0 = a_z` (as a complex number). -/
lemma pauliDot_apply_00 (a : DetectorSetting) :
    pauliDot a 0 0 = ((a.vec 2 : ℝ) : ℂ) := by simp [pauliDot]

/-- `pauliDot a 0 1 = a_x − i a_y`. -/
lemma pauliDot_apply_01 (a : DetectorSetting) :
    pauliDot a 0 1 = ((a.vec 0 : ℝ) : ℂ) - Complex.I * ((a.vec 1 : ℝ) : ℂ) := by
  simp [pauliDot]

/-- `pauliDot a 1 0 = a_x + i a_y`. -/
lemma pauliDot_apply_10 (a : DetectorSetting) :
    pauliDot a 1 0 = ((a.vec 0 : ℝ) : ℂ) + Complex.I * ((a.vec 1 : ℝ) : ℂ) := by
  simp [pauliDot]

/-- `pauliDot a 1 1 = −a_z`. -/
lemma pauliDot_apply_11 (a : DetectorSetting) :
    pauliDot a 1 1 = -((a.vec 2 : ℝ) : ℂ) := by simp [pauliDot]

/-! ### The three headline expectations (paper §6.7, §6.8) -/

/-- **Singlet left-Pauli expectation vanishes.** `⟨ψ⁻ | σ·a ⊗ I | ψ⁻⟩ = 0`. -/
theorem singlet_left_pauli_expectation_zero (a : DetectorSetting) :
    expectation (sigmaDotLeft a) = 0 := by
  rw [expectation_formula]
  show (1/2 : ℂ) *
      (sigmaDotLeft a (0,1) (0,1) - sigmaDotLeft a (0,1) (1,0)
        - sigmaDotLeft a (1,0) (0,1) + sigmaDotLeft a (1,0) (1,0)) = 0
  simp only [sigmaDotLeft, Matrix.kroneckerMap_apply, Matrix.one_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11]
  simp

/-- **Singlet right-Pauli expectation vanishes.** `⟨ψ⁻ | I ⊗ σ·b | ψ⁻⟩ = 0`. -/
theorem singlet_right_pauli_expectation_zero (b : DetectorSetting) :
    expectation (sigmaDotRight b) = 0 := by
  rw [expectation_formula]
  show (1/2 : ℂ) *
      (sigmaDotRight b (0,1) (0,1) - sigmaDotRight b (0,1) (1,0)
        - sigmaDotRight b (1,0) (0,1) + sigmaDotRight b (1,0) (1,0)) = 0
  simp only [sigmaDotRight, Matrix.kroneckerMap_apply, Matrix.one_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11]
  simp

/-- **Singlet two-Pauli correlation.** `⟨ψ⁻ | σ·a ⊗ σ·b | ψ⁻⟩ = -a·b`. -/
theorem singlet_pauli_correlation (a b : DetectorSetting) :
    expectation (sigmaDotJoint a b)
      = -(((a.vec 0 * b.vec 0 + a.vec 1 * b.vec 1 + a.vec 2 * b.vec 2 : ℝ)) : ℂ) := by
  rw [expectation_formula]
  show (1/2 : ℂ) *
      (sigmaDotJoint a b (0,1) (0,1) - sigmaDotJoint a b (0,1) (1,0)
        - sigmaDotJoint a b (1,0) (0,1) + sigmaDotJoint a b (1,0) (1,0)) = _
  simp only [sigmaDotJoint, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11]
  push_cast
  ring_nf
  rw [show (Complex.I^2 : ℂ) = -1 from Complex.I_sq]
  ring

end LF3
end CSD
