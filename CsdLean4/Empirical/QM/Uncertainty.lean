/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

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

@[expose] public section

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

/-- Standard deviation `σ_ψ(A) = ‖(A − ⟨A⟩) ψ‖`, the unsquared spread. `variance` is its
square (`variance_eq_stdDev_sq`); the error–disturbance relation of `Ozawa.lean` is stated in
unsquared quantities, which is why this lives beside `variance` rather than in that file. -/
noncomputable def stdDev (A : Module.End ℂ H) (ψ : H) : ℝ :=
  ‖A ψ - (expectation A ψ) • ψ‖

lemma stdDev_nonneg (A : Module.End ℂ H) (ψ : H) : 0 ≤ stdDev A ψ := norm_nonneg _

lemma variance_eq_stdDev_sq (A : Module.End ℂ H) (ψ : H) :
    variance A ψ = stdDev A ψ ^ 2 := rfl

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

/-- ★ **The commutator bound, unsquared.** For symmetric `A, B`,
`‖⟪ψ, [A,B] ψ⟫‖ ≤ 2 ‖A ψ‖ ‖B ψ‖`.

Both `robertson_core` (by squaring) and Ozawa's error–disturbance relation (by summing three
instances) are this inequality; the squared form cannot be summed, which is why the unsquared
one is the primitive. The content is that `⟪ψ,[A,B]ψ⟫ = z − conj z = 2i·Im z` for
`z = ⟪A ψ, B ψ⟫`, so the commutator sees only the imaginary part, and `|Im z| ≤ ‖z‖`. -/
lemma commutator_le_two_mul_norm (A B : Module.End ℂ H) (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (ψ : H) :
    ‖inner ℂ ψ ((A * B - B * A) ψ)‖ ≤ 2 * (‖A ψ‖ * ‖B ψ‖) := by
  have hz : inner ℂ (A ψ) (B ψ) = inner ℂ ψ ((A * B) ψ) := by
    rw [hA ψ (B ψ), ← Module.End.mul_apply]
  have hcz : conj (inner ℂ (A ψ) (B ψ)) = inner ℂ ψ ((B * A) ψ) := by
    rw [inner_conj_symm, hB ψ (A ψ), ← Module.End.mul_apply]
  have hsub : inner ℂ (A ψ) (B ψ) - conj (inner ℂ (A ψ) (B ψ))
      = inner ℂ ψ ((A * B - B * A) ψ) := by
    rw [hcz, hz, ← inner_sub_right, ← LinearMap.sub_apply]
  set z := inner ℂ (A ψ) (B ψ) with hz_def
  have hCnorm : ‖inner ℂ ψ ((A * B - B * A) ψ)‖ = 2 * |z.im| := by
    rw [← hsub, Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    norm_num
  have him : |z.im| ≤ ‖z‖ := by simpa using RCLike.abs_im_le_norm z
  have hCS : ‖z‖ ≤ ‖A ψ‖ * ‖B ψ‖ := by
    rw [hz_def]; exact norm_inner_le_norm (𝕜 := ℂ) (A ψ) (B ψ)
  rw [hCnorm]
  linarith

/-- **Core inequality.** For symmetric `A, B` and any `ψ`,
`‖A ψ‖² · ‖B ψ‖² ≥ ¼ ‖⟪ψ, [A,B] ψ⟫‖²`. The uncertainty relation is this
applied to the centered observables. Derived from the unsquared
`commutator_le_two_mul_norm` by squaring (CONVENTIONS §9.3: one Cauchy–Schwarz, two
consumers). -/
lemma robertson_core (A B : Module.End ℂ H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : H) :
    ‖A ψ‖ ^ 2 * ‖B ψ‖ ^ 2 ≥ (1 / 4) * ‖inner ℂ ψ ((A * B - B * A) ψ)‖ ^ 2 := by
  have h := commutator_le_two_mul_norm A B hA hB ψ
  have hnn : 0 ≤ ‖A ψ‖ * ‖B ψ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (inner ℂ ψ ((A * B - B * A) ψ)), h, hnn]

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
