/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.SpectralVariance
import CsdLean4.Empirical.QM.Uncertainty

/-!
# LF4 §14.2 Robertson uncertainty on the Kähler instance (ontic variance form)

**Category:** 3-Local (LF4 §14.2 follow-up — concrete Robertson bound
expressed in terms of ontic-side integrated variances).

Connects `CsdLean4/LF4/SpectralVariance.lean` (the Hilbert ↔ ontic
variance correspondence at the integration level) to
`CsdLean4/Empirical/QM/Uncertainty.lean` (the QM Robertson bound on
Hilbert variances). The composite gives the **Robertson bound on ontic
variances**: for any pair of Hermitian matrices `A, B : Matrix (Fin N)
(Fin N) ℂ` and unit `ψ : EuclideanSpace ℂ (Fin N)`, on any Kähler
instance with preparation `Dirac p₀ × vol_T²`,

  `(∫ A_centered_ontic dμψ) · (∫ B_centered_ontic dμψ)
    ≥ ¼ ‖⟨ψ, [A, B] ψ⟩‖²`.

## Module contents

- **`variance_eq_norm_sq_sub_expectation_sq`** — generic Hilbert-space
  variance simplification: for symmetric `T` and unit `ψ`,
  `Var T ψ = ‖T ψ‖² − (re ⟨ψ, T ψ⟩)²`. This is the standard QM identity
  `Var = ⟨A²⟩ − ⟨A⟩²` in the form needed to bridge `SpectralVariance`.

- **`QM_variance_eq_spectralVariance`** — the bridge: for Hermitian `A`
  and unit `ψ`, `Empirical.Uncertainty.variance A.toEuclideanLin ψ
  = spectralVariance hA ψ`.

- **`QM_variance_eq_integral_spectralOnticCentered`** — composition with
  the integration headline from `SpectralCarving` / `SpectralVariance`:
  `Empirical.Uncertainty.variance A.toEuclideanLin ψ
    = ∫ spectralOnticCentered hA ψ dμψ` on the Kähler instance.

- **`kahler_robertson_ontic_variance`** — the headline ontic-variance
  Robertson bound. Composes `QM_variance_eq_integral_spectralOnticCentered`
  (applied twice, to `A` and `B`) with the QM-side
  `Empirical.Uncertainty.robertson_uncertainty` (the abstract Hilbert
  Robertson bound) into a concrete inequality on the Kähler instance
  with the LHS expressed purely via ontic-side integrals.

## Tier-2 posture (unchanged)

The bridge `variance = spectralVariance = ∫ spectralOnticCentered dμψ`
composes three theorems that each compute the same value via
structurally distinct machinery (Hilbert-space variance via norm-sub-sq;
spectral expansion via Parseval + eigenvalue equation; ontic-side via
N-arc carving + Lebesgue integral). The Robertson bound itself is QM-side
Hilbert-only content (Cauchy–Schwarz + commutator algebra); the LF4
content is the realisation of that bound on ontic-side observables.

## Axiom posture

Foundational triple only.
-/

open MeasureTheory Set
open Matrix Finset

namespace CSD
namespace LF4

/-- **Variance equals norm-squared minus expectation-squared** (under
symmetric `T` and unit `ψ`). The standard QM `Var = ⟨A²⟩ − ⟨A⟩²`
written via `‖T ψ‖²` (which equals `re ⟨ψ, T² ψ⟩` for self-adjoint `T`).
Generic Hilbert-space statement; no matrix or Kähler structure. -/
theorem variance_eq_norm_sq_sub_expectation_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : Module.End ℂ H} (hT : T.IsSymmetric)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    CSD.Empirical.Uncertainty.variance T ψ
      = ‖T ψ‖ ^ 2 - (RCLike.re (inner ℂ ψ (T ψ))) ^ 2 := by
  unfold CSD.Empirical.Uncertainty.variance CSD.Empirical.Uncertainty.expectation
  set e := inner ℂ ψ (T ψ) with he_def
  -- `e` is real for symmetric `T`: `conj e = e`, hence `e.im = 0`.
  have he_real : (starRingEnd ℂ) e = e := by
    rw [he_def, inner_conj_symm]; exact hT ψ ψ
  have he_im_zero : e.im = 0 := Complex.conj_eq_iff_im.mp he_real
  -- Expand `‖T ψ − e • ψ‖²` via `norm_sub_sq` + chain:
  -- ⟨T ψ, e • ψ⟩ → e · ⟨T ψ, ψ⟩ → e · conj e → (normSq e : ℂ),
  -- ‖e • ψ‖ → ‖e‖ · ‖ψ‖ = ‖e‖ (under hψ).
  -- Then collapse `re ((normSq e : ℂ)) → normSq e → e.re² + e.im² → e.re²` (im = 0).
  rw [norm_sub_sq (𝕜 := ℂ),
      inner_smul_right (𝕜 := ℂ) (T ψ) ψ e,
      show inner ℂ (T ψ) ψ = (starRingEnd ℂ) e from (inner_conj_symm _ _).symm,
      Complex.mul_conj, norm_smul, hψ, mul_one]
  -- Goal: ‖T ψ‖² − 2 · re ((normSq e : ℂ)) + ‖e‖² = ‖T ψ‖² − (re e)².
  -- Convert RCLike.re to .re (defeq for ℂ) and apply Complex.ofReal_re.
  simp only [show @RCLike.re ℂ _ = (fun z : ℂ => z.re) from rfl,
             Complex.ofReal_re]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, he_im_zero]
  ring

/-- **Hilbert variance ↔ spectral variance bridge** for Hermitian matrices
on `EuclideanSpace ℂ (Fin N)` and unit `ψ`. Composes
`variance_eq_norm_sq_sub_expectation_sq` (the QM-side simplification)
with `spectralVariance_eq_hilbert_norm_sq_diff` (the spectral identity). -/
theorem QM_variance_eq_spectralVariance {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) :
    CSD.Empirical.Uncertainty.variance A.toEuclideanLin ψ
      = spectralVariance hA ψ := by
  rw [variance_eq_norm_sq_sub_expectation_sq
        (Matrix.isSymmetric_toEuclideanLin_iff.symm.mp hA) hψ,
      spectralVariance_eq_hilbert_norm_sq_diff hA hψ]

/-- **QM variance ↔ ontic-side integrated variance**: composition of the
spectral bridge with the integration headline. The Hilbert-space variance
of a Hermitian matrix's action on a unit state, on the Kähler instance,
equals the integral of the centered ontic spectral observable. -/
theorem QM_variance_eq_integral_spectralOnticCentered {N M : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (p₀ : CPN M) :
    CSD.Empirical.Uncertainty.variance A.toEuclideanLin ψ
      = ∫ σ, spectralOnticCentered (M := M) hA ψ σ
          ∂((Measure.dirac p₀).prod (volume : Measure KTorus)) := by
  rw [QM_variance_eq_spectralVariance hA hψ,
      ← integral_spectralOnticCentered_eq_variance hA hψ p₀]

/-- **Robertson uncertainty on ontic variances** (the LF4 §14.2
realisation of the QM Robertson bound). For any pair of Hermitian
matrices `A, B : Matrix (Fin N) (Fin N) ℂ` and unit
`ψ : EuclideanSpace ℂ (Fin N)`, on any Kähler instance `KSigma M`
with preparation `(Dirac p₀) × vol_T²`,

  `(∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ)
    ≥ ¼ ‖⟨ψ, [A.toEuclideanLin, B.toEuclideanLin] ψ⟩‖²`.

Composes `QM_variance_eq_integral_spectralOnticCentered` (applied to `A`
and `B`) with `Empirical.Uncertainty.robertson_uncertainty` (the QM
Hilbert Robertson bound). The LHS is purely ontic; the RHS is the
Hilbert-space commutator overlap (the Robertson lower bound). -/
theorem kahler_robertson_ontic_variance {N M : ℕ}
    {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (p₀ : CPN M) :
    (∫ σ, spectralOnticCentered (M := M) hA ψ σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)))
      * (∫ σ, spectralOnticCentered (M := M) hB ψ σ
          ∂((Measure.dirac p₀).prod (volume : Measure KTorus)))
      ≥ (1 / 4) * ‖inner ℂ ψ
          ((A.toEuclideanLin * B.toEuclideanLin
            - B.toEuclideanLin * A.toEuclideanLin) ψ)‖ ^ 2 := by
  rw [← QM_variance_eq_integral_spectralOnticCentered hA hψ p₀,
      ← QM_variance_eq_integral_spectralOnticCentered hB hψ p₀]
  exact CSD.Empirical.Uncertainty.robertson_uncertainty
    A.toEuclideanLin B.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.symm.mp hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.symm.mp hB) ψ

end LF4
end CSD
