import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Empirical/QM: Robertson uncertainty relation

**Category:** 3-Local (promotion-ready to 2-Framework on demand). QM-generic:
no CSD ontology, pure inner-product geometry.

The Robertson uncertainty relation (Robertson 1929): for self-adjoint
observables `A, B` and a state `ψ`,

  `Var_ψ(A) · Var_ψ(B) ≥ ¼ |⟨ψ, [A,B] ψ⟩|²`,

where `[A,B] = AB − BA` is the commutator and `Var_ψ(A) = ‖(A − ⟨A⟩)ψ‖²`
is the variance of the centered observable. The bound is the squared
Cauchy–Schwarz inequality applied to the centered vectors `(A−⟨A⟩)ψ`,
`(B−⟨B⟩)ψ`, retaining only the imaginary part of their inner product,
which equals `½⟨ψ,[A,B]ψ⟩`.

Operators are `Module.End ℂ H = H →ₗ[ℂ] H`; self-adjointness is
`LinearMap.IsSymmetric` (the inner-product form `⟪T x, y⟫ = ⟪x, T y⟫`),
which sidesteps the `Star` synthesis issues noted in LF3. The proof needs
no finite-dimensionality.

## Source

Robertson 1929, *Phys. Rev.* **34**, 163; Schrödinger 1930 (the stronger
form with the anticommutator term, not formalised here).
-/

open ComplexConjugate

namespace CSD
namespace Empirical
namespace Uncertainty

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫`. -/
noncomputable def expectation (A : Module.End ℂ H) (ψ : H) : ℂ := inner ℂ ψ (A ψ)

/-- Variance `Var_ψ(A) = ‖(A − ⟨A⟩) ψ‖²`, the squared norm of the centered
observable applied to `ψ` (the standard quantum variance for a unit `ψ`). -/
noncomputable def variance (A : Module.End ℂ H) (ψ : H) : ℝ :=
  ‖A ψ - (expectation A ψ) • ψ‖ ^ 2

/-- For a symmetric operator the expectation value is real. -/
lemma expectation_conj (A : Module.End ℂ H) (hA : A.IsSymmetric) (ψ : H) :
    conj (expectation A ψ) = expectation A ψ := by
  rw [expectation, inner_conj_symm]
  exact hA ψ ψ

/-- Subtracting a real scalar multiple of the identity preserves symmetry. -/
lemma isSymmetric_sub_smul_one {A : Module.End ℂ H} (hA : A.IsSymmetric)
    {a : ℂ} (ha : conj a = a) : (A - a • (1 : Module.End ℂ H)).IsSymmetric := by
  intro x y
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hA x y]

/-- The commutator is invariant under shifting each operator by a scalar
multiple of the identity: `[A − a, B − b] = [A, B]`. -/
lemma commutator_shift (A B : Module.End ℂ H) (a b : ℂ) :
    (A - a • 1) * (B - b • 1) - (B - b • 1) * (A - a • 1) = A * B - B * A := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  module

/-- `Var_ψ(A) = ‖(A − ⟨A⟩•1) ψ‖²` (variance via the centered operator). -/
lemma variance_centered (A : Module.End ℂ H) (ψ : H) :
    variance A ψ = ‖(A - (expectation A ψ) • 1) ψ‖ ^ 2 := by
  unfold variance
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]

/-- **Core inequality.** For symmetric `A, B` and any `ψ`,
`‖A ψ‖² · ‖B ψ‖² ≥ ¼ ‖⟪ψ, [A,B] ψ⟫‖²`. The uncertainty relation is this
applied to the centered observables. -/
lemma robertson_core (A B : Module.End ℂ H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : H) :
    ‖A ψ‖ ^ 2 * ‖B ψ‖ ^ 2 ≥ (1 / 4) * ‖inner ℂ ψ ((A * B - B * A) ψ)‖ ^ 2 := by
  -- `z := ⟪A ψ, B ψ⟫`; push the operators onto the right via symmetry.
  have hz : inner ℂ (A ψ) (B ψ) = inner ℂ ψ ((A * B) ψ) := by
    rw [hA ψ (B ψ), ← Module.End.mul_apply]
  have hcz : conj (inner ℂ (A ψ) (B ψ)) = inner ℂ ψ ((B * A) ψ) := by
    rw [inner_conj_symm, hB ψ (A ψ), ← Module.End.mul_apply]
  have hsub : inner ℂ (A ψ) (B ψ) - conj (inner ℂ (A ψ) (B ψ))
      = inner ℂ ψ ((A * B - B * A) ψ) := by
    rw [hcz, hz, ← inner_sub_right, ← LinearMap.sub_apply]
  set z := inner ℂ (A ψ) (B ψ) with hz_def
  set C := inner ℂ ψ ((A * B - B * A) ψ) with hC_def
  -- `C = z − conj z = 2 i·Im z`, hence `‖C‖² = 4 (Im z)²`.
  have hCnorm : ‖C‖ ^ 2 = 4 * z.im ^ 2 := by
    rw [← hsub, Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    ring
  -- `(Im z)² ≤ ‖z‖²`.
  have him : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    have h := RCLike.abs_im_le_norm z
    have h' : |z.im| ≤ ‖z‖ := by simpa using h
    nlinarith [abs_nonneg z.im, norm_nonneg z, sq_abs z.im, h']
  -- Cauchy–Schwarz, squared.
  have hCS : ‖z‖ ^ 2 ≤ ‖A ψ‖ ^ 2 * ‖B ψ‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (A ψ) (B ψ)
    rw [← hz_def] at h
    nlinarith [h, norm_nonneg z, mul_nonneg (norm_nonneg (A ψ)) (norm_nonneg (B ψ))]
  rw [ge_iff_le]
  calc (1 / 4) * ‖C‖ ^ 2 = z.im ^ 2 := by rw [hCnorm]; ring
    _ ≤ ‖z‖ ^ 2 := him
    _ ≤ ‖A ψ‖ ^ 2 * ‖B ψ‖ ^ 2 := hCS

/-- **Robertson uncertainty relation.** For self-adjoint observables `A, B`
and any state `ψ`,
`Var_ψ(A) · Var_ψ(B) ≥ ¼ ‖⟪ψ, [A,B] ψ⟫‖²`. -/
theorem robertson_uncertainty (A B : Module.End ℂ H) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : H) :
    variance A ψ * variance B ψ ≥ (1 / 4) * ‖inner ℂ ψ ((A * B - B * A) ψ)‖ ^ 2 := by
  have hA' := isSymmetric_sub_smul_one hA (expectation_conj A hA ψ)
  have hB' := isSymmetric_sub_smul_one hB (expectation_conj B hB ψ)
  have key := robertson_core (A - (expectation A ψ) • 1) (B - (expectation B ψ) • 1) hA' hB' ψ
  rw [commutator_shift] at key
  rw [variance_centered A ψ, variance_centered B ψ]
  exact key

end Uncertainty
end Empirical
end CSD
