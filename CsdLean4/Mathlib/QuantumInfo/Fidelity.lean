/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Subadditivity

/-!
# Uhlmann fidelity — the core

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **fidelity** of two states,

  `F(ρ, σ) = Tr √(√ρ · σ · √ρ) = ∑ᵢ √(λᵢ(√ρ σ √ρ))`,

defined spectrally, exactly as `traceNorm` is (`TraceDistance.lean`). The sandwich
`√ρ σ √ρ` is positive semidefinite (`posSemidef_sandwich`), so every eigenvalue is
nonnegative and the square roots are real.

What this module delivers:

* the definition, and non-negativity (`fidelity_nonneg`);
* ★ **symmetry** `F(ρ, σ) = F(σ, ρ)` (`fidelity_comm`) — the one property that is
  normally real work, because the two sandwiches `√ρ σ √ρ` and `√σ ρ √σ` are
  different matrices. It falls out of the corpus's own rectangular-spectrum lemma
  `spectral_sum_mul_conjTranspose_comm` (`∑ g(λ(M Mᴴ)) = ∑ g(λ(Mᴴ M))` for `g 0 = 0`)
  at `M = √σ √ρ`, since `Mᴴ M = √ρ σ √ρ` and `M Mᴴ = √σ ρ √σ`;
* the transport hinge `sqrt_eigenvalue_sum_congr` (eigenvalue sums depend on the matrix,
  not on the supplied Hermitian witness), which is what lets the two sandwiches be
  compared at all.

**Honest scope.** `F ≤ 1`, `F = 1 ↔ ρ = σ`, monotonicity under channels, Uhlmann's
theorem and the Fuchs–van de Graaf inequalities are **not attempted here**. In general
they route through the variational form `F = max_U |Tr(√ρ √σ U)|`, which needs a polar
decomposition; Mathlib has singular *values* (`LinearMap.singularValues`) but no
`A = U Σ Vᴴ` or polar factorisation at the pin. MATHLIB-ABSENT(Matrix.polarDecomposition)
The purification half that Uhlmann also needs *is* in the corpus
(`QuantumInfo.exists_purification`, `Subadditivity.lean`).

Reference: Nielsen–Chuang §9.2.2 (fidelity); Uhlmann, *Rep. Math. Phys.* **9** (1976) 273.
In-corpus: `Mathlib/QuantumInfo/TraceDistance.lean` (the sibling metric),
`Mathlib/QuantumInfo/Subadditivity.lean` (`sqrtMat`, the spectrum lemma, purification).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sandwich `√ρ · σ · √ρ` is positive semidefinite: it is `Bᴴ σ B` at `B = √ρ`,
which is Hermitian. -/
theorem posSemidef_sandwich {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (sqrtMat hρ.1 * σ * sqrtMat hρ.1).PosSemidef := by
  have h := hσ.conjTranspose_mul_mul_same (sqrtMat hρ.1)
  rwa [show (sqrtMat hρ.1)ᴴ = sqrtMat hρ.1 from sqrtMat_isHermitian hρ.1] at h

/-- **Uhlmann fidelity** `F(ρ, σ) = Tr √(√ρ σ √ρ)`, defined spectrally as the sum of the
square roots of the (nonnegative) eigenvalues of the sandwich. -/
noncomputable def fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : ℝ :=
  ∑ i, Real.sqrt ((posSemidef_sandwich hρ hσ).1.eigenvalues i)

/-- Transport of a `√`-eigenvalue sum along an equality of matrices: the eigenvalues are
determined by the matrix, not by the supplied Hermitian witness. Same proof-irrelevance
hinge as `entropy_congr_of_eq`. -/
theorem sqrt_eigenvalue_sum_congr {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) :
    ∑ i, Real.sqrt (hA.eigenvalues i) = ∑ i, Real.sqrt (hB.eigenvalues i) := by
  subst h; rfl

/-- Fidelity is nonnegative. -/
theorem fidelity_nonneg {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    0 ≤ fidelity hρ hσ :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- ★ **Fidelity is symmetric**, `F(ρ, σ) = F(σ, ρ)`, even though the two sandwiches
`√ρ σ √ρ` and `√σ ρ √σ` are different matrices. At `M = √σ √ρ` one has `Mᴴ M = √ρ σ √ρ`
and `M Mᴴ = √σ ρ √σ`, so this is `spectral_sum_mul_conjTranspose_comm` with `g = √`
(and `√0 = 0`). -/
theorem fidelity_comm {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    fidelity hρ hσ = fidelity hσ hρ := by
  set M : Matrix n n ℂ := sqrtMat hσ.1 * sqrtMat hρ.1 with hM
  have hsρ : (sqrtMat hρ.1)ᴴ = sqrtMat hρ.1 := sqrtMat_isHermitian hρ.1
  have hsσ : (sqrtMat hσ.1)ᴴ = sqrtMat hσ.1 := sqrtMat_isHermitian hσ.1
  have hMH : Mᴴ = sqrtMat hρ.1 * sqrtMat hσ.1 := by
    rw [hM, Matrix.conjTranspose_mul, hsρ, hsσ]
  have hMHM : Mᴴ * M = sqrtMat hρ.1 * σ * sqrtMat hρ.1 := by
    rw [hMH, hM]
    rw [show sqrtMat hρ.1 * sqrtMat hσ.1 * (sqrtMat hσ.1 * sqrtMat hρ.1)
        = sqrtMat hρ.1 * (sqrtMat hσ.1 * sqrtMat hσ.1) * sqrtMat hρ.1 by
      simp only [Matrix.mul_assoc]]
    rw [sqrtMat_mul_self hσ]
  have hMMH : M * Mᴴ = sqrtMat hσ.1 * ρ * sqrtMat hσ.1 := by
    rw [hMH, hM]
    rw [show sqrtMat hσ.1 * sqrtMat hρ.1 * (sqrtMat hρ.1 * sqrtMat hσ.1)
        = sqrtMat hσ.1 * (sqrtMat hρ.1 * sqrtMat hρ.1) * sqrtMat hσ.1 by
      simp only [Matrix.mul_assoc]]
    rw [sqrtMat_mul_self hρ]
  have key := spectral_sum_mul_conjTranspose_comm M (g := Real.sqrt) Real.sqrt_zero
  rw [fidelity, fidelity]
  rw [sqrt_eigenvalue_sum_congr (posSemidef_sandwich hρ hσ).1
        (Matrix.isHermitian_conjTranspose_mul_self M) hMHM.symm]
  rw [sqrt_eigenvalue_sum_congr (posSemidef_sandwich hσ hρ).1
        (Matrix.isHermitian_mul_conjTranspose_self M) hMMH.symm]
  exact key.symm

end QuantumInfo
