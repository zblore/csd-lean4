import CsdLean4.LF3.Setup

/-!
# LF3 Singlet / State: Bell singlet vector and expectation functional

**Category:** 3-Local (LF3 Bell singlet `|ψ⁻⟩` in `EuclideanSpace ℂ (Fin 2 × Fin 2)`, unit-norm, expectation functional).

Paper §6.

The Bell singlet `|ψ⁻⟩` in `HAB := EuclideanSpace ℂ (Fin 4)` (basis order
`|++⟩, |+-⟩, |-+⟩, |--⟩`), its unit-norm property, and the expectation
functional `⟨ψ⁻ | A | ψ⁻⟩` for a 4×4 matrix `A`.

The joint spin eigenstate `jointSpinEig` and the singlet amplitude `cAmp` are
deferred to `Singlet/Kernel.lean`, where `cAmp` is supplied in closed form
sufficient for the algebraic core (paper §6.9) and the LF1↔LF2↔LF3 chain.
-/

open scoped BigOperators
open Matrix

namespace CSD
namespace LF3

/-- The Bell singlet `|ψ⁻⟩ = (1/√2)(|+-⟩ − |-+⟩)` in `HAB := EuclideanSpace ℂ
    (Fin 2 × Fin 2)` with basis order matching the `pauliDot`/`sigmaDot*`
    operators' `Fin 2 × Fin 2` indexing: `(0,0) = |++⟩, (0,1) = |+-⟩, (1,0) =
    |-+⟩, (1,1) = |--⟩`. -/
noncomputable def singlet : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ)
       - EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ))

/-- Expectation `⟨ψ⁻ | A | ψ⁻⟩` for a `(Fin 2 × Fin 2)`-indexed matrix `A`.
    Real part is the physically observable value; the complex output here is
    the raw inner product, real-extracted at the call site. -/
noncomputable def expectation (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  inner ℂ singlet ((Matrix.toEuclideanLin A) singlet)

/-! ### Singlet norm (paper §6.4) -/

/-- The Bell singlet is unit-normalised. Computed via the explicit basis
    decomposition: the only non-zero components are at `(0, 1)` and `(1, 0)`,
    each with magnitude `1/√2`, giving `‖ψ⁻‖² = 2 · (1/2) = 1`. -/
theorem singlet_norm : ‖singlet‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h00 : singlet (0, 0) = 0 := by simp [singlet, EuclideanSpace.single]
  have h01 : singlet (0, 1) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    simp [singlet, EuclideanSpace.single]
  have h10 : singlet (1, 0) = -((Real.sqrt 2 : ℂ)⁻¹) := by
    simp [singlet, EuclideanSpace.single]
  have h11 : singlet (1, 1) = 0 := by simp [singlet, EuclideanSpace.single]
  have h_norm_inv : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, h00, h01, h10, h11,
             norm_zero, norm_neg, ne_eq, OfNat.ofNat_ne_zero,
             not_false_eq_true, zero_pow, add_zero, zero_add, h_norm_inv]
  -- Goal: Real.sqrt (2⁻¹ + 2⁻¹) = 1
  rw [show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 from by norm_num, Real.sqrt_one]

end LF3
end CSD
