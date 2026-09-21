/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Polarization
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.ProjectionPackage
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Gleason's theorem, finite-dimensional: the descent from a quadratic form to the density matrix

**Category:** 1-Mathlib (CSD-free; staged for upstream). "Layer C" of
`specs/gleason-feasibility.md`: everything that follows once the frame function is known to be
the quadratic form of a Hermitian matrix on the unit sphere. Shared by Busch's effect theorem
(`LF2/EffectGleason.lean`, whose state conditions and uniqueness are re-routed through
`quadraticForm_on_sphere_to_density`) and the projection theorem.

* `posSemidef_of_sphere_nonneg` — a Hermitian matrix whose quadratic form is nonnegative on the
  unit sphere is positive semidefinite;
* `trace_eq_sum_sphere` — its trace is the sum of the quadratic form over the standard basis;
* `eq_of_sphere_quadForm_eq` — two Hermitian matrices with the same quadratic form on the unit
  sphere are equal (scale off the sphere, then `matrix_eq_zero_of_quadForm_zero`);
* ★ `quadraticForm_on_sphere_to_density` — the three packaged: if `f v = Re ⟪v, A v⟫` on the
  sphere with `f ≥ 0` and `∑ᵢ f eᵢ = 1`, then `A` is a density matrix and is the only Hermitian
  matrix with that quadratic form on the sphere;
* `ProjectionPackage.p_eq_re_trace` — the projection descent: a package whose frame function is
  the quadratic form of `A` on the sphere satisfies `p P = Re Tr(A P)` for **every** projection
  `P` (spectral resolution `P = ∑ λᵢ |bᵢ⟩⟨bᵢ|` with `λᵢ ∈ {0, 1}`, additivity over the
  pairwise-orthogonal rank-ones);
* ★★ `ProjectionPackage.existsUnique_density_of_frame_quadratic` — Gleason's conclusion from
  the quadratic-form hypothesis: a unique density matrix `ρ` with `p P = Re Tr(ρ P)` for every
  projection. What Gleason's theorem adds is that the hypothesis holds whenever `N ≥ 3`
  (`specs/gleason-feasibility.md`, the core lemma).

## Source

Gleason 1957, *J. Math. Mech.* **6**, 885, §1 (frame functions and their weights) and the
end of §3.
-/

@[expose] public section

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace Gleason

variable {N : ℕ}

/-! ### The quadratic form of a Hermitian matrix -/

/-- Scaling the argument of a quadratic form: `⟨c x, A (c x)⟩ = conj c · c · ⟨x, A x⟩`. -/
lemma star_smul_dotProduct_mulVec_smul (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    star (c • x) ⬝ᵥ (A *ᵥ (c • x)) = (conj c * c) * (star x ⬝ᵥ (A *ᵥ x)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    Complex.star_def]
  ring

/-- The quadratic form of a Hermitian matrix is conjugation invariant (real). -/
lemma conj_star_dotProduct_mulVec {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (x : Fin N → ℂ) : conj (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [starRingEnd_apply, ← star_dotProduct, star_mulVec, ← dotProduct_mulVec, hA.eq]

/-- The quadratic form of a Hermitian matrix is its real part. -/
lemma ofReal_re_star_dotProduct_mulVec {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (x : Fin N → ℂ) : (((star x ⬝ᵥ (A *ᵥ x)).re : ℝ) : ℂ) = star x ⬝ᵥ (A *ᵥ x) :=
  Complex.conj_eq_iff_re.mp (conj_star_dotProduct_mulVec hA x)

/-- Every nonzero vector is a positive multiple of a unit vector of `EuclideanSpace`. -/
lemma exists_norm_one_smul_eq {x : Fin N → ℂ} (hx : x ≠ 0) :
    ∃ (r : ℝ) (v : EuclideanSpace ℂ (Fin N)), 0 < r ∧ ‖v‖ = 1 ∧ x = ((r : ℝ) : ℂ) • ⇑v := by
  set X : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 x with hX
  have hX0 : X ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun y : EuclideanSpace ℂ (Fin N) => (⇑y : Fin N → ℂ)) h
    simpa [hX] using this
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  refine ⟨‖X‖, ((‖X‖⁻¹ : ℝ) : ℂ) • X, hn, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  · change x = ((‖X‖ : ℝ) : ℂ) • (((‖X‖⁻¹ : ℝ) : ℂ) • x)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]

/-- **A Hermitian matrix with nonnegative quadratic form on the unit sphere is positive
semidefinite.** -/
theorem posSemidef_of_sphere_nonneg {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (h : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 → 0 ≤ (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (Complex.conj_eq_iff_im.mp (conj_star_dotProduct_mulVec hA x)).symm⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨r, v, hr, hv, rfl⟩ := exists_norm_one_smul_eq hx
  rw [star_smul_dotProduct_mulVec_smul, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (h v hv)

/-- The quadratic form at a standard basis vector is the diagonal entry. -/
lemma star_single_dotProduct_mulVec_single (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    star (⇑(EuclideanSpace.single i (1 : ℂ))) ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ)))
      = A i i := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- **The trace is the sum of the quadratic form over the standard basis.** -/
theorem trace_eq_sum_sphere (A : Matrix (Fin N) (Fin N) ℂ) :
    A.trace = ∑ i, star (⇑(EuclideanSpace.single i (1 : ℂ)))
      ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ))) := by
  simp only [star_single_dotProduct_mulVec_single, Matrix.trace, Matrix.diag_apply]

/-- The trace of a Hermitian matrix is real. -/
lemma ofReal_re_trace {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    (((A.trace).re : ℝ) : ℂ) = A.trace := by
  refine Complex.conj_eq_iff_re.mp ?_
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, hA.eq]

/-- **Two Hermitian matrices with the same quadratic form on the unit sphere are equal.** -/
theorem eq_of_sphere_quadForm_eq {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (h : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 →
      (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re = (star (⇑v) ⬝ᵥ (B *ᵥ ⇑v)).re) : A = B := by
  have hD : (A - B).IsHermitian := hA.sub hB
  have hsphere : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 →
      star (⇑v) ⬝ᵥ ((A - B) *ᵥ ⇑v) = 0 := by
    intro v hv
    rw [← ofReal_re_star_dotProduct_mulVec hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      h v hv, sub_self, Complex.ofReal_zero]
  have hall : ∀ x : Fin N → ℂ, star x ⬝ᵥ ((A - B) *ᵥ x) = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    obtain ⟨r, v, _, hv, rfl⟩ := exists_norm_one_smul_eq hx
    rw [star_smul_dotProduct_mulVec_smul, hsphere v hv, mul_zero]
  exact sub_eq_zero.mp (matrix_eq_zero_of_quadForm_zero hall)

/-- ★ **From a quadratic form on the sphere to a density matrix.** If `f v = Re ⟪v, A v⟫` for
every unit `v`, with `A` Hermitian, `f ≥ 0` on the sphere and `∑ᵢ f eᵢ = 1` over the standard
basis, then `A` is positive semidefinite with unit trace, and it is the only Hermitian matrix
whose quadratic form on the sphere is `f`. -/
theorem quadraticForm_on_sphere_to_density {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {f : EuclideanSpace ℂ (Fin N) → ℝ}
    (hf : ∀ v, ‖v‖ = 1 → f v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re)
    (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) (h1 : ∑ i, f (EuclideanSpace.single i (1 : ℂ)) = 1) :
    A.PosSemidef ∧ A.trace = 1 ∧ ∀ B : Matrix (Fin N) (Fin N) ℂ, B.IsHermitian →
      (∀ v, ‖v‖ = 1 → f v = (star (⇑v) ⬝ᵥ (B *ᵥ ⇑v)).re) → B = A := by
  have hsingle : ∀ i : Fin N, ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := fun i => by
    rw [PiLp.norm_single]; exact norm_one
  refine ⟨posSemidef_of_sphere_nonneg hA fun v hv => (hf v hv) ▸ h0 v hv, ?_, ?_⟩
  · have hs : ∑ i, (star (⇑(EuclideanSpace.single i (1 : ℂ)))
        ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℂ)))).re = 1 := by
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => (hf _ (hsingle i)).symm
    rw [← ofReal_re_trace hA, trace_eq_sum_sphere, Complex.re_sum, hs, Complex.ofReal_one]
  · intro B hB hfB
    exact eq_of_sphere_quadForm_eq hB hA fun v hv => by rw [← hfB v hv, hf v hv]

/-! ### The projection descent -/

/-- **Spectral resolution as a sum of rank-ones:** `A = ∑ᵢ λᵢ |bᵢ⟩⟨bᵢ|` over the eigenvector
basis of a Hermitian matrix. -/
theorem _root_.Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOne {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) :
    A = ∑ i, hA.eigenvalues i • rankOne (hA.eigenvectorBasis i) := by
  calc A = A * ∑ i, rankOne (hA.eigenvectorBasis i) := by
        rw [sum_rankOne_orthonormalBasis, Matrix.mul_one]
    _ = ∑ i, hA.eigenvalues i • rankOne (hA.eigenvectorBasis i) := by
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [rankOne, mul_vecMulVec, hA.mulVec_eigenvectorBasis, smul_vecMulVec]

/-- The eigenvalues of an orthogonal projection are `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P)
    (hPh : P.IsHermitian) (i : Fin N) : hPh.eigenvalues i = 0 ∨ hPh.eigenvalues i = 1 := by
  set b := hPh.eigenvectorBasis with hb
  set l := hPh.eigenvalues i with hl
  have h1 : P *ᵥ (P *ᵥ ⇑(b i)) = (l * l) • ⇑(b i) := by
    rw [hPh.mulVec_eigenvectorBasis, Matrix.mulVec_smul, hPh.mulVec_eigenvectorBasis, smul_smul]
  have h2 : P *ᵥ (P *ᵥ ⇑(b i)) = l • ⇑(b i) := by
    rw [Matrix.mulVec_mulVec, hP.isIdempotentElem.eq, hPh.mulVec_eigenvectorBasis]
  have hne : (⇑(b i) : Fin N → ℂ) ≠ 0 := by
    intro h
    have := b.orthonormal.norm_eq_one i
    rw [show b i = 0 from by ext j; exact congrFun h j] at this
    simp at this
  have h3 : (l * l - l) • (⇑(b i) : Fin N → ℂ) = 0 := by
    rw [sub_smul, h1.symm.trans h2, sub_self]
  have h4 : l * l - l = 0 := (smul_eq_zero.mp h3).resolve_right hne
  have h5 : l * (l - 1) = 0 := by rw [← h4]; ring
  rcases mul_eq_zero.mp h5 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

namespace ProjectionPackage

variable (OP : ProjectionPackage N)

/-- The weighted rank-one `λ • |b⟩⟨b|` with `λ ∈ {0, 1}` is a projection. -/
lemma isStarProjection_smul_rankOne {l : ℝ} (hl : l = 0 ∨ l = 1)
    {b : EuclideanSpace ℂ (Fin N)} (hb : ‖b‖ = 1) : IsStarProjection (l • rankOne b) := by
  rcases hl with rfl | rfl
  · simp
  · simpa using isStarProjection_rankOne hb

/-- `p (λ • |b⟩⟨b|) = λ · frame b` for `λ ∈ {0, 1}`. -/
lemma p_smul_rankOne {l : ℝ} (hl : l = 0 ∨ l = 1) (b : EuclideanSpace ℂ (Fin N)) :
    OP.p (l • rankOne b) = l * OP.frame b := by
  rcases hl with rfl | rfl
  · simp [OP.p_zero]
  · simp [frame]

/-- **The projection descent.** If the frame function is the quadratic form of a matrix `A` on
the unit sphere, then `p P = Re Tr(A P)` for every orthogonal projection `P`. -/
theorem p_eq_re_trace {A : Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re)
    {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P) :
    OP.p P = ((A * P).trace).re := by
  have hPh : P.IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  set b := hPh.eigenvectorBasis with hb
  set l := hPh.eigenvalues with hl
  have hspec : P = ∑ i, l i • rankOne (b i) := hPh.eq_sum_eigenvalues_smul_rankOne
  have hl01 : ∀ i, l i = 0 ∨ l i = 1 := eigenvalues_eq_zero_or_one hP hPh
  have hunit : ∀ i, ‖b i‖ = 1 := b.orthonormal.norm_eq_one
  have hsum : OP.p P = ∑ i, l i * OP.frame (b i) := by
    rw [hspec, OP.p_sum _ (fun i => isStarProjection_smul_rankOne (hl01 i) (hunit i))
      (fun i j hij => by
        rw [smul_mul_smul_comm, rankOne_mul_rankOne_of_orthonormal b.orthonormal hij, smul_zero])]
    exact Finset.sum_congr rfl fun i _ => OP.p_smul_rankOne (hl01 i) (b i)
  rw [hsum]
  conv_rhs => rw [hspec, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf _ (hunit i), Matrix.mul_smul, Matrix.trace_smul, rankOne, trace_mul_vecMulVec,
    Complex.real_smul, Complex.re_ofReal_mul]

/-- ★★ **Gleason's conclusion from the quadratic-form hypothesis.** If the frame function of a
projection package is the quadratic form of a Hermitian matrix on the unit sphere, then there is
a unique density matrix `ρ` with `p P = Re Tr(ρ P)` for every orthogonal projection `P`. -/
theorem existsUnique_density_of_frame_quadratic {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian)
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re := by
  have hsingle : ∀ i : Fin N, ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := fun i => by
    rw [PiLp.norm_single]; exact norm_one
  obtain ⟨hpsd, htr, huniq⟩ := quadraticForm_on_sphere_to_density hA hf
    (fun v hv => OP.frame_nonneg hv)
    (by
      have h := OP.sum_frame_orthonormalBasis (EuclideanSpace.basisFun (Fin N) ℂ)
      simpa [EuclideanSpace.basisFun_apply] using h)
  refine ⟨A, ⟨hpsd, htr, fun P hP => OP.p_eq_re_trace hf hP⟩, ?_⟩
  rintro ρ ⟨hρ, -, hρp⟩
  refine huniq ρ hρ.isHermitian fun v hv => ?_
  rw [frame, hρp _ (isStarProjection_rankOne hv), rankOne, trace_mul_vecMulVec]

end ProjectionPackage

end Gleason

end
