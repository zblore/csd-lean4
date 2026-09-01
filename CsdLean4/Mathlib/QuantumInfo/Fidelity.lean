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

★ **The upper bound is proved** (2026-09-01): `fidelity_le_one`, for states that are
positive definite. The route builds the two missing pieces rather than importing them —
Hilbert–Schmidt Cauchy–Schwarz (`norm_trace_conjTranspose_mul_le`, by transporting matrices
to `EuclideanSpace ℂ (n × n)`, since Mathlib gives `Matrix` only a Frobenius *norm* and no
inner product) and the polar decomposition of an invertible matrix
(`exists_unitary_conjTranspose_mul_eq_sqrt`, elementary: `U = X P⁻¹`).

**Honest scope.** Positive-definiteness in `fidelity_le_one` is **load-bearing, not
decorative**: it makes `X = √σ √ρ` invertible, and the elementary polar decomposition exists
only for invertible `X`. Removing it needs a general polar/singular-value factorisation, which
Mathlib does not have — it has singular *values* (`LinearMap.singularValues`) but no
`A = U Σ Vᴴ`. MATHLIB-ABSENT(Matrix.polarDecomposition) This is the same posture as
`klein_inequality`, which carries a `PosDef` hypothesis for a related reason.
`F = 1 ↔ ρ = σ`, monotonicity under channels, Uhlmann's theorem and Fuchs–van de Graaf are
**not attempted**. The purification half Uhlmann also needs *is* in the corpus
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

/-! ### The Hilbert–Schmidt Cauchy–Schwarz inequality

Mathlib has no inner-product structure on `Matrix` (only the Frobenius *norm*), so the
inequality is obtained by transporting matrices to `EuclideanSpace ℂ (n × n)`, where
`norm_inner_le_norm` is Cauchy–Schwarz. -/

/-- A matrix read as a vector of `ℂ^{n×n}`. -/
noncomputable def vecOf (A : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun p : n × n => A p.1 p.2)

omit [DecidableEq n] in
lemma inner_vecOf (A B : Matrix n n ℂ) :
    (inner ℂ (vecOf A) (vecOf B) : ℂ) = (Aᴴ * B).trace := by
  rw [PiLp.inner_apply, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.inner_apply, vecOf]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_comm]

omit [DecidableEq n] in
lemma norm_sq_vecOf (A : Matrix n n ℂ) : ‖vecOf A‖ ^ 2 = (Aᴴ * A).trace.re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (vecOf A), inner_vecOf]
  rfl

omit [DecidableEq n] in
/-- ★ **Hilbert–Schmidt Cauchy–Schwarz**: `|Tr(Aᴴ B)| ≤ ‖A‖₂ ‖B‖₂`. -/
theorem norm_trace_conjTranspose_mul_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖
      ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (vecOf A) (vecOf B)
  rw [inner_vecOf] at h
  have hA : ‖vecOf A‖ = Real.sqrt ((Aᴴ * A).trace.re) := by
    rw [← norm_sq_vecOf]; exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hB : ‖vecOf B‖ = Real.sqrt ((Bᴴ * B).trace.re) := by
    rw [← norm_sq_vecOf]; exact (Real.sqrt_sq (norm_nonneg _)).symm
  rwa [hA, hB] at h

/-! ### Polar decomposition for an invertible matrix

Mathlib has singular *values* (`LinearMap.singularValues`) but no `A = U Σ Vᴴ` and no polar
factorisation. MATHLIB-ABSENT(Matrix.polarDecomposition) For an **invertible** `X` the
construction is elementary: `P := √(Xᴴ X)` is positive definite, hence invertible, and
`U := X P⁻¹` is unitary. That is all the fidelity bound needs, and it is why
`fidelity_le_one` below carries positive-definiteness hypotheses. -/

/-- For invertible `X`, the unitary factor of the polar decomposition, characterised by the
identity the fidelity bound consumes: `Uᴴ X = √(Xᴴ X)`. Invertibility of `P = √(Xᴴ X)` comes
from `det P * det P = det (Xᴴ X)`, so no separate positive-definiteness argument is needed. -/
theorem exists_unitary_conjTranspose_mul_eq_sqrt {X : Matrix n n ℂ}
    (hXX : (Xᴴ * X).PosDef) :
    ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧ Uᴴ * X = sqrtMat hXX.1 := by
  set P := sqrtMat hXX.1 with hP
  have hPherm : Pᴴ = P := sqrtMat_isHermitian hXX.1
  have hPsq : P * P = Xᴴ * X := sqrtMat_mul_self hXX.posSemidef
  have hdet : IsUnit P.det := by
    have hXXd : IsUnit (Xᴴ * X).det := (Matrix.isUnit_iff_isUnit_det _).mp hXX.isUnit
    have hsq : P.det * P.det = (Xᴴ * X).det := by rw [← Matrix.det_mul, hPsq]
    rw [isUnit_iff_ne_zero] at hXXd ⊢
    intro h
    rw [h, zero_mul] at hsq
    exact hXXd hsq.symm
  have hinvherm : (P⁻¹)ᴴ = P⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hPherm]
  refine ⟨X * P⁻¹, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    calc (X * P⁻¹)ᴴ * (X * P⁻¹)
        = P⁻¹ * (Xᴴ * X) * P⁻¹ := by
          rw [Matrix.conjTranspose_mul, hinvherm]; noncomm_ring
      _ = (P⁻¹ * P) * (P * P⁻¹) := by rw [← hPsq]; noncomm_ring
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · calc (X * P⁻¹)ᴴ * X
        = P⁻¹ * (Xᴴ * X) := by rw [Matrix.conjTranspose_mul, hinvherm]; noncomm_ring
      _ = (P⁻¹ * P) * P := by rw [← hPsq]; noncomm_ring
      _ = P := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-! ### ★★ The upper bound -/

/-- `√ρ` is invertible when `ρ` is positive definite (`det √ρ * det √ρ = det ρ ≠ 0`). -/
theorem sqrtMat_isUnit {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) : IsUnit (sqrtMat hρ.1) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  have hsq : (sqrtMat hρ.1).det * (sqrtMat hρ.1).det = ρ.det := by
    rw [← Matrix.det_mul, sqrtMat_mul_self hρ.posSemidef]
  rw [h, zero_mul] at hsq
  exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hρ.isUnit)) hsq.symm

/-- The sandwich `√ρ σ √ρ` is positive definite when both states are. -/
theorem posDef_sandwich {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (sqrtMat hρ.1 * σ * sqrtMat hρ.1).PosDef := by
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := σ) (sqrtMat_isUnit hρ)).mpr hσ
  rwa [Matrix.star_eq_conjTranspose,
    show (sqrtMat hρ.1)ᴴ = sqrtMat hρ.1 from sqrtMat_isHermitian hρ.1] at h

/-- Fidelity as the trace of the matrix square root of the sandwich. -/
theorem fidelity_eq_re_trace {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    fidelity hρ hσ = RCLike.re (sqrtMat (posSemidef_sandwich hρ hσ).1).trace := by
  rw [fidelity, show sqrtMat (posSemidef_sandwich hρ hσ).1
      = cfc Real.sqrt (sqrtMat hρ.1 * σ * sqrtMat hρ.1) from
    (Matrix.IsHermitian.cfc_eq _ Real.sqrt).symm]
  rw [re_trace_cfc]

/-- Transport of `Tr √·` along an equality of matrices — the same proof-irrelevance hinge as
`sqrt_eigenvalue_sum_congr`. -/
theorem sqrtMat_trace_congr {M N : Matrix n n ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : M = N) : RCLike.re (sqrtMat hM).trace = RCLike.re (sqrtMat hN).trace := by
  subst h; rfl

/-- ★★ **`F(ρ,σ) ≤ 1` for states.** The route: `Xᴴ X = √ρ σ √ρ` at `X = √σ √ρ`, so the polar
factor of `X` has trace `F`; writing that trace as a Hilbert–Schmidt inner product
`⟪√σ U, √ρ⟫` and applying Cauchy–Schwarz gives `F ≤ ‖√σ U‖₂ ‖√ρ‖₂ = √(Tr σ) √(Tr ρ) = 1`.

⚠️ Positive-definiteness is load-bearing, not decorative: it is what makes `X` invertible, and
the elementary polar decomposition used here (`U = X P⁻¹`) exists only for invertible `X`.
Mathlib has no general polar/singular-value factorisation to remove the hypothesis with. -/
theorem fidelity_le_one {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    fidelity hρ.posSemidef hσ.posSemidef ≤ 1 := by
  have hA : (sqrtMat hρ.posSemidef.1)ᴴ = sqrtMat hρ.posSemidef.1 :=
    sqrtMat_isHermitian hρ.posSemidef.1
  have hB : (sqrtMat hσ.posSemidef.1)ᴴ = sqrtMat hσ.posSemidef.1 :=
    sqrtMat_isHermitian hσ.posSemidef.1
  set A := sqrtMat hρ.posSemidef.1 with hAdef
  set B := sqrtMat hσ.posSemidef.1 with hBdef
  set X := B * A with hXdef
  -- `Xᴴ X` is exactly the sandwich
  have hXX : Xᴴ * X = A * σ * A := by
    rw [hXdef, Matrix.conjTranspose_mul, hA, hB]
    rw [show A * B * (B * A) = A * (B * B) * A by noncomm_ring]
    rw [sqrtMat_mul_self hσ.posSemidef]
  have hsand : (A * σ * A).PosDef := posDef_sandwich hρ hσ
  have hXXpd : (Xᴴ * X).PosDef := by rw [hXX]; exact hsand
  obtain ⟨U, hUmem, hUX⟩ := exists_unitary_conjTranspose_mul_eq_sqrt hXXpd
  -- fidelity is the trace of that polar factor
  have hfid : fidelity hρ.posSemidef hσ.posSemidef
      = RCLike.re (sqrtMat hXXpd.1).trace := by
    rw [fidelity_eq_re_trace]
    exact sqrtMat_trace_congr _ _ hXX.symm
  rw [hfid, ← hUX]
  -- rewrite as a Hilbert–Schmidt pairing and apply Cauchy–Schwarz
  have hUherm : (B * U)ᴴ = Uᴴ * B := by rw [Matrix.conjTranspose_mul, hB]
  have hpair : Uᴴ * X = (B * U)ᴴ * A := by rw [hUherm, hXdef]; noncomm_ring
  rw [hpair]
  refine le_trans (RCLike.re_le_norm _) ?_
  refine le_trans (norm_trace_conjTranspose_mul_le (B * U) A) ?_
  have hUU : U * Uᴴ = 1 := by
    have := hUmem.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : ((B * U)ᴴ * (B * U)).trace = σ.trace := by
    rw [hUherm]
    rw [show Uᴴ * B * (B * U) = Uᴴ * (B * B) * U by noncomm_ring]
    rw [sqrtMat_mul_self hσ.posSemidef]
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  have h2 : (Aᴴ * A).trace = ρ.trace := by
    rw [hA, sqrtMat_mul_self hρ.posSemidef]
  rw [h1, h2, hρ1, hσ1]
  simp

end QuantumInfo
