/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.SpectralCarving

/-!
# LF4 §14.2 spectral variance and ontic variance correspondence

**Category:** 3-Local (LF4 §14.2 follow-up — Hilbert ↔ ontic variance
identity for any Hermitian observable, building on
`SpectralCarving.lean`'s integration headline).

For Hermitian `A : Matrix (Fin N) (Fin N) ℂ` and unit state
`ψ : EuclideanSpace ℂ (Fin N)`, the variance has both Hilbert and ontic
spectral expressions:

  `Var_ψ(A) := ‖A ψ‖² − ⟨A⟩²
            = ∑ᵢ (λᵢ − ⟨A⟩)² · ‖⟨uᵢ, ψ⟩‖²        (Hilbert spectral form)
            = ∫ (∑ᵢ (λᵢ − ⟨A⟩)² · 1_{R_i})(σ) dμψ  (ontic spectral form)`

where `⟨A⟩ = re ⟨ψ, A ψ⟩`, `λᵢ` are the eigenvalues, `uᵢ` are an
orthonormal eigenbasis (`Matrix.IsHermitian.eigenvectorBasis`), and
`R_i` are the N-arc spectral regions from `SpectralCarving`.

## Module contents

- **Phase F.1** — `inner_eigenvector_image` (extracted from
  `SpectralExpansion.lean`'s proof) and `hilbert_norm_sq_apply_hermitian`
  (`‖A ψ‖² = ∑ᵢ λᵢ² · bornWeights`), the Hilbert-side variance ingredient.

- **Phase F.2** — `spectralVariance hA ψ := ∑ᵢ (λᵢ − ⟨A⟩)² · bornWeights`
  (the spectral form) plus
  `spectralVariance_eq_hilbert_norm_sq_diff : spectralVariance = ‖A ψ‖² − ⟨A⟩²`
  (the Hilbert ↔ spectral identity, deriving the standard QM
  `Var = ⟨A²⟩ − ⟨A⟩²` form via `‖A ψ‖² = re ⟨ψ, A² ψ⟩` for self-adjoint `A`).

- **Phase F.3** — `spectralOnticCentered := ∑ᵢ (λᵢ − ⟨A⟩)² · 1_{R_i}`
  (the ontic counterpart) and the **headline**
  `integral_spectralOnticCentered_eq_variance :
    ∫ spectralOnticCentered dμψ = spectralVariance hA ψ`,
  the ontic ↔ Hilbert-spectral variance correspondence at the integration
  level. Composes the Phase D template (`integral_finsetSum +
  diracProd_spectralRegion`) with `bornWeights_sum_eq_one`.

## Tier-2 posture (unchanged)

`spectralVariance` is *defined* as the spectral form. The Hilbert ↔
spectral identity is a genuine algebraic theorem (expanding `(λᵢ − ⟨A⟩)²`
and using `∑ bornWeights = 1`, `∑ λᵢ · bornWeights = ⟨A⟩`,
`∑ λᵢ² · bornWeights = ‖A ψ‖²`). The ontic ↔ spectral identity is a
genuine measure-theoretic theorem (per-region carving + linearity of
integration). Both ends meet at the same value via structurally distinct
machinery.

## Axiom posture

Foundational triple only.
-/

@[expose] public section

open MeasureTheory Set
open Matrix Finset

namespace CSD
namespace LF4

/-! ### Phase F.1 — Hilbert variance helpers -/

/-- The eigenvalue equation projected onto an inner product: for Hermitian
`A` and eigenvector `uᵢ` (of eigenvalue `λᵢ`),
`⟨uᵢ, A ψ⟩ = (λᵢ : ℂ) · ⟨uᵢ, ψ⟩`. Extracted from `SpectralExpansion.lean`'s
proof of `hermitian_inner_spectral_expansion`. -/
lemma inner_eigenvector_image {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    inner ℂ (hA.eigenvectorBasis i) (A.toEuclideanLin ψ)
      = (hA.eigenvalues i : ℂ) * inner ℂ (hA.eigenvectorBasis i) ψ := by
  have hSym : A.toEuclideanLin.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff.symm).mp hA
  have hEigAct : A.toEuclideanLin (hA.eigenvectorBasis i)
      = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    simp [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
          Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.coe_reindex]
  rw [← hSym (hA.eigenvectorBasis i) ψ, hEigAct, inner_smul_left,
      Complex.conj_ofReal]

/-- **Hilbert norm-squared spectral expansion**: `‖A ψ‖² = ∑ᵢ λᵢ² · bornWeights i`
for any Hermitian `A` and any state `ψ`. Composes `Parseval`
(`OrthonormalBasis.sum_sq_norm_inner_right`) with `inner_eigenvector_image`. -/
theorem hilbert_norm_sq_apply_hermitian {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖A.toEuclideanLin ψ‖ ^ 2
      = ∑ i : Fin N, hA.eigenvalues i ^ 2 * bornWeights hA ψ i := by
  rw [← hA.eigenvectorBasis.sum_sq_norm_inner_right (A.toEuclideanLin ψ)]
  apply Finset.sum_congr rfl
  intros i _
  rw [inner_eigenvector_image hA ψ i, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

/-- `bornWeights`-form of the spectral expansion (the `SpectralExpansion`
form uses the surface form `‖⟨uᵢ, ψ⟩‖²`; this gives the `bornWeights`
surface form, equal by definition, for ergonomics in proofs that mix
the two). -/
lemma hermitian_inner_spectral_expansion_re_bornWeights {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (ψ : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))
      = ∑ i : Fin N, hA.eigenvalues i * bornWeights hA ψ i :=
  hermitian_inner_spectral_expansion_re hA ψ

/-! ### Phase F.2 — Spectral variance and Hilbert match -/

/-- **Spectral variance**: the eigenvalue-deviation-squared sum weighted by
the Born probabilities. By `spectralVariance_eq_hilbert_norm_sq_diff` this
equals `‖A ψ‖² − ⟨A⟩²`, the standard QM variance `⟨A²⟩ − ⟨A⟩²` for
self-adjoint `A`. -/
noncomputable def spectralVariance {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) : ℝ :=
  ∑ i : Fin N,
    (hA.eigenvalues i - RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))) ^ 2
      * bornWeights hA ψ i

lemma spectralVariance_nonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    0 ≤ spectralVariance hA ψ := by
  unfold spectralVariance
  apply Finset.sum_nonneg
  intros i _
  exact mul_nonneg (sq_nonneg _) (bornWeights_nonneg hA ψ i)

/-- **Hilbert ↔ spectral variance identity**: for any Hermitian `A` and unit
`ψ`, `spectralVariance hA ψ = ‖A ψ‖² − ⟨A⟩²`. The standard QM variance
`⟨A²⟩ − ⟨A⟩²` reduces to `‖A ψ‖² − ⟨A⟩²` via `⟨ψ, A² ψ⟩ = ⟨A ψ, A ψ⟩` for
self-adjoint `A`. -/
theorem spectralVariance_eq_hilbert_norm_sq_diff {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) :
    spectralVariance hA ψ
      = ‖A.toEuclideanLin ψ‖ ^ 2
        - (RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))) ^ 2 := by
  set μ := RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))
  unfold spectralVariance
  -- Expand (λᵢ − μ)² = λᵢ² − 2λᵢμ + μ², distribute the sum, and use:
  --   ∑ λᵢ² · bornWeights = ‖A ψ‖²    (hilbert_norm_sq_apply_hermitian)
  --   ∑ λᵢ · bornWeights  = μ          (hermitian_inner_spectral_expansion_re)
  --   ∑ bornWeights       = 1          (bornWeights_sum_eq_one, uses hψ).
  have key : ∑ i : Fin N, (hA.eigenvalues i - μ) ^ 2 * bornWeights hA ψ i
      = (∑ i : Fin N, hA.eigenvalues i ^ 2 * bornWeights hA ψ i)
        - 2 * μ * (∑ i : Fin N, hA.eigenvalues i * bornWeights hA ψ i)
        + μ ^ 2 * (∑ i : Fin N, bornWeights hA ψ i) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros i _; ring
  rw [key, ← hilbert_norm_sq_apply_hermitian hA ψ,
      ← hermitian_inner_spectral_expansion_re_bornWeights hA ψ,
      bornWeights_sum_eq_one hA hψ]
  ring

/-! ### Phase F.3 — Ontic variance observable and integration headline -/

/-- **Ontic centered spectral observable**: the deviation-squared
eigenvalue-weighted indicator sum over the N spectral outcome regions.
Equals `(spectralOntic hA ψ σ − ⟨A⟩)²` for `σ ∈ ⋃ᵢ R_i` (which has
full `μψ`-measure under `hψ : ‖ψ‖ = 1`); the integration identity
below holds without invoking that a.e. equivalence. -/
noncomputable def spectralOnticCentered {N M : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    KSigma M → ℝ := fun σ =>
  ∑ i : Fin N,
    (hA.eigenvalues i - RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))) ^ 2 *
      (spectralRegion (M := M) (bornWeights hA ψ) i).indicator (fun _ => (1 : ℝ)) σ

lemma spectralOnticCentered_measurable {N M : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (ψ : EuclideanSpace ℂ (Fin N)) :
    Measurable (spectralOnticCentered (M := M) hA ψ) := by
  apply Finset.measurable_sum
  intros i _
  exact (measurable_const.indicator (spectralRegion_measurable _ _)).const_mul _

/-- **§14.2 ontic ↔ Hilbert-spectral variance correspondence at the
integration level**: for any Hermitian `A : Matrix (Fin N) (Fin N) ℂ` and
unit `ψ : EuclideanSpace ℂ (Fin N)`, on any Kähler instance `KSigma M`
with preparation `(Dirac p₀) × vol_T²`,

  `∫ spectralOnticCentered dμψ = spectralVariance hA ψ`.

Composes `diracProd_spectralRegion` (per-region carving) with
linearity of the Lebesgue integral over the finite eigenvalue sum.
Combined with `spectralVariance_eq_hilbert_norm_sq_diff`, this gives the
full Hilbert variance ↔ ontic variance correspondence on the Kähler
instance. -/
theorem integral_spectralOnticCentered_eq_variance {N M : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (p₀ : CPN M) :
    ∫ σ, spectralOnticCentered (M := M) hA ψ σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus))
      = spectralVariance hA ψ := by
  unfold spectralOnticCentered spectralVariance
  haveI : IsProbabilityMeasure ((Measure.dirac p₀).prod (volume : Measure KTorus)) :=
    inferInstance
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intros i _
    rw [integral_const_mul]
    congr 1
    change ∫ σ, (spectralRegion (M := M) (bornWeights hA ψ) i).indicator 1 σ
      ∂((Measure.dirac p₀).prod (volume : Measure KTorus)) = _
    rw [MeasureTheory.integral_indicator_one (spectralRegion_measurable _ _),
        measureReal_def,
        diracProd_spectralRegion p₀ (bornWeights_nonneg hA ψ)
          (le_of_eq (bornWeights_sum_eq_one hA hψ)) i,
        ENNReal.toReal_ofReal (bornWeights_nonneg hA ψ i)]
  · intros i _
    refine Integrable.const_mul ?_ _
    exact MeasureTheory.Integrable.indicator (integrable_const (1 : ℝ))
      (spectralRegion_measurable _ _)

/-- **Composite headline**: under unit `ψ`, the integrated centered ontic
observable matches the standard QM variance `‖A ψ‖² − ⟨A⟩²`. -/
theorem integral_spectralOnticCentered_eq_hilbert_norm_sq_diff {N M : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (p₀ : CPN M) :
    ∫ σ, spectralOnticCentered (M := M) hA ψ σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus))
      = ‖A.toEuclideanLin ψ‖ ^ 2
        - (RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ))) ^ 2 := by
  rw [integral_spectralOnticCentered_eq_variance hA hψ,
      spectralVariance_eq_hilbert_norm_sq_diff hA hψ]

end LF4
end CSD
