import Mathlib.Analysis.Matrix.Spectrum

/-!
# LF4 §14.2 general N×N spectral expansion of the Hilbert expectation

**Category:** 3-Local (LF4 §14.2 — general Hermitian observable
spectral expansion at the Hilbert level).

For any Hermitian matrix `A : Matrix (Fin N) (Fin N) ℂ` and any
state `ψ : EuclideanSpace ℂ (Fin N)`, the expectation
`⟨ψ, A ψ⟩` decomposes as

  `⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²`

where `λᵢ : ℝ` are the eigenvalues of `A` and `uᵢ : EuclideanSpace ℂ (Fin N)`
are an orthonormal eigenbasis (both provided by Mathlib's
`Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorBasis`).

This is the **Hilbert side** of the LF4 §14.2 general N×N observable
correspondence. The ontic side carves N outcome regions of measure
`‖⟨uᵢ, ψ⟩‖²` (one per eigenvector) and integrates the eigenvalue-weighted
indicator sum — that construction is per-state and built on top of this
spectral identity. The headline result here is `hermitian_inner_spectral_expansion`.

## What §14.2 General unlocks

- **Variance identity**: `Var_ψ(A) = ∑ᵢ (λᵢ − ⟨A⟩)² · ‖⟨uᵢ, ψ⟩‖²` follows by
  applying the spectral expansion to both `⟨A⟩` and `⟨A²⟩`. The full
  Robertson–uncertainty bundle's per-observable §14 correspondence
  (matching `∫ A_ontic dμψ = ⟨ψ, A ψ⟩` AND `∫ (A_ontic − ⟨A⟩)² dμψ = Var(A)`)
  composes via this identity plus the per-eigenvector carving.

- **Multi-eigenvalue Hardy / Mermin–Peres lifts**: observables that are
  NOT ±1-valued (e.g. spin-1, GHZ stabiliser generators, generic
  Hermitian operators) get their ontic counterparts via this same
  spectral pattern.

## Proof route

Uses Mathlib's `Matrix.IsHermitian.mulVec_eigenvectorBasis` (eigenvalue
equation `A uᵢ = λᵢ • uᵢ`), `Matrix.isHermitian_iff_isSymmetric`
(self-adjointness of the linear-map action), and
`OrthonormalBasis.sum_inner_mul_inner` (Parseval). The chain:

1. `⟨ψ, A ψ⟩ = ∑ᵢ ⟨ψ, uᵢ⟩ · ⟨uᵢ, A ψ⟩` (Parseval on the eigenbasis).
2. `⟨uᵢ, A ψ⟩ = ⟨A uᵢ, ψ⟩ = ⟨λᵢ • uᵢ, ψ⟩ = (λᵢ : ℂ) · ⟨uᵢ, ψ⟩` (self-adjoint + eigenequation; λᵢ real).
3. `⟨ψ, uᵢ⟩ · (λᵢ : ℂ) · ⟨uᵢ, ψ⟩ = (λᵢ : ℂ) · conj(⟨uᵢ, ψ⟩) · ⟨uᵢ, ψ⟩ = (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²`.

## Axiom posture

Foundational triple only.
-/

open Matrix Finset

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **§14.2 general N×N spectral expansion of the Hilbert expectation.**

For any Hermitian `A : Matrix (Fin N) (Fin N) ℂ` and any
`ψ : EuclideanSpace ℂ (Fin N)`,

  `⟨ψ, A ψ⟩ = ∑ᵢ (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²`

where `λᵢ = hA.eigenvalues i` and `uᵢ = hA.eigenvectorBasis i`.

The action of `A` on `ψ` is taken through `Matrix.toEuclideanLin` (the
canonical bounded linear map associated with the matrix on the
`EuclideanSpace` L² model). -/
theorem hermitian_inner_spectral_expansion
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (ψ : EuclideanSpace ℂ (Fin N)) :
    inner ℂ ψ (A.toEuclideanLin ψ)
      = ∑ i : Fin N, (hA.eigenvalues i : ℂ)
          * ((‖inner ℂ (hA.eigenvectorBasis i) ψ‖ : ℂ) ^ 2) := by
  -- Step 1: Parseval on the eigenbasis -- ⟨ψ, A ψ⟩ = ∑ᵢ ⟨ψ, uᵢ⟩ · ⟨uᵢ, A ψ⟩.
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner ψ (A.toEuclideanLin ψ)]
  apply Finset.sum_congr rfl
  intro i _
  -- Step 2: use self-adjointness + eigenvalue equation to rewrite ⟨uᵢ, A ψ⟩.
  have hSym : A.toEuclideanLin.IsSymmetric :=
    (Matrix.isHermitian_iff_isSymmetric).mp hA
  have hEigAct : A.toEuclideanLin (hA.eigenvectorBasis i)
      = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    -- Use the linear-map spectral-API directly via `IsSymmetric.apply_eigenvectorBasis`,
    -- which already produces the `(λ : 𝕜) • ·` form. Bridge the Matrix-level reindexed
    -- eigenvectorBasis/eigenvalues to the LinearMap-level forms via the reindex equiv;
    -- this matches the calling pattern Mathlib uses internally in `Matrix.Spectrum`.
    have := hSym.apply_eigenvectorBasis finrank_euclideanSpace
              ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    simpa [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
           Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.coe_reindex] using this
  -- ⟨uᵢ, A ψ⟩ = ⟨A uᵢ, ψ⟩ (self-adjoint) = ⟨(λᵢ : ℂ) • uᵢ, ψ⟩ = conj(λᵢ : ℂ) · ⟨uᵢ, ψ⟩
  --        = (λᵢ : ℂ) · ⟨uᵢ, ψ⟩    (λᵢ real so its complex coercion is self-conjugate).
  have hInner_uA :
      inner ℂ (hA.eigenvectorBasis i) (A.toEuclideanLin ψ)
        = (hA.eigenvalues i : ℂ) * inner ℂ (hA.eigenvectorBasis i) ψ := by
    rw [← hSym (hA.eigenvectorBasis i) ψ, hEigAct, inner_smul_left,
        Complex.conj_ofReal]
  -- Step 3: assemble the algebraic identity.
  -- ⟨ψ, uᵢ⟩ · ⟨uᵢ, A ψ⟩ = ⟨ψ, uᵢ⟩ · (λᵢ : ℂ) · ⟨uᵢ, ψ⟩
  --                     = (λᵢ : ℂ) · (⟨ψ, uᵢ⟩ · conj⟨ψ, uᵢ⟩)         (since ⟨uᵢ, ψ⟩ = conj⟨ψ, uᵢ⟩)
  --                     = (λᵢ : ℂ) · ‖⟨ψ, uᵢ⟩‖²                       (Complex.mul_conj)
  --                     = (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²                       (norm of conjugate = norm).
  rw [hInner_uA]
  have hConj : (starRingEnd ℂ) (inner ℂ ψ (hA.eigenvectorBasis i))
      = inner ℂ (hA.eigenvectorBasis i) ψ := inner_conj_symm _ _
  rw [show inner ℂ ψ (hA.eigenvectorBasis i) *
        ((hA.eigenvalues i : ℂ) * inner ℂ (hA.eigenvectorBasis i) ψ)
        = (hA.eigenvalues i : ℂ) *
          (inner ℂ ψ (hA.eigenvectorBasis i) *
           (starRingEnd ℂ) (inner ℂ ψ (hA.eigenvectorBasis i))) by rw [hConj]; ring,
      Complex.mul_conj]
  -- Goal: (λᵢ : ℂ) * (Complex.normSq ⟨ψ, uᵢ⟩ : ℂ) = (λᵢ : ℂ) * ((‖⟨uᵢ, ψ⟩‖ : ℂ)^2).
  -- Bridge: Complex.normSq z = ‖z‖² (as ℝ); ‖conj z‖ = ‖z‖.
  congr 1
  rw [Complex.normSq_eq_norm_sq, ← hConj, RCLike.norm_conj]
  push_cast
  ring

/-- **§14.2 general N×N spectral expansion: real-valued form.**

The expectation `⟨ψ, A ψ⟩` of a Hermitian observable is a real number
(its imaginary part vanishes), and admits the real spectral expansion

  `re ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²`.

Real form is what variance/expectation/uncertainty arguments consume. -/
theorem hermitian_inner_spectral_expansion_re
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (ψ : EuclideanSpace ℂ (Fin N)) :
    (RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ)) : ℝ)
      = ∑ i : Fin N, hA.eigenvalues i * (‖inner ℂ (hA.eigenvectorBasis i) ψ‖ ^ 2) := by
  have h := hermitian_inner_spectral_expansion hA ψ
  -- Take real part: re of a real sum equals the sum.
  apply_fun (RCLike.re : ℂ → ℝ) at h
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- re ((λᵢ : ℂ) * ((‖.‖ : ℂ))²) = λᵢ * ‖.‖²
  simp [Complex.ofReal_re, Complex.ofReal_im, pow_two]

end LF4
end CSD
