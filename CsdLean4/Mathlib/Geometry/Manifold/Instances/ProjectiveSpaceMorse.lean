/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceCriticalPoints
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The second-order behaviour of an expectation value at an eigenline

**TERM-SCOPE(Hamiltonian)** — this module uses the vector-field sense of "Hamiltonian";
`specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #337 (geometric QM, completion item 6 of 2026-11-08).

The eigenlines of a Hermitian `A` are the critical points of `⟨A⟩` on `ℂℙⁿ` (#326). Here is the
second order. Along the projective line through a unit eigenvector `ψ` (eigenvalue `λ`) in a
direction `v ⊥ ψ`, exactly,

  `⟨A⟩([ψ + t v]) = λ + t² (⟨v, A v⟩ − λ ‖v‖²) / (1 + t² ‖v‖²)`,

so the Hessian along the line is `2 (⟨v, A v⟩ − λ ‖v‖²)`. In Mathlib's eigenbasis `e_j` (eigenvalues
`μ_j`) this form is `Σ (μ_j − λ) |⟨e_j, v⟩|²`: negative on the span `N` of the `e_j` with
`μ_j < λ`, which is orthogonal to `ψ` and has real dimension `2 · #{j | μ_j < λ}`, and nonnegative
on `N`'s orthogonal complement. That is the Morse index of `⟨A⟩` at the eigenline:
**twice the number of eigenvalues below `λ`**, counted with multiplicity.

* `toEuclideanLin_eigenvectorBasis` — `A e_j = μ_j e_j`;
* `re_inner_toEuclideanLin_eq_sum`, `norm_sq_eq_sum_norm_inner_eigenvectorBasis`,
  ★ `hessForm_eq_sum` — **`⟨v, A v⟩ − λ ‖v‖² = Σ (μ_j − λ) |⟨e_j, v⟩|²`**;
* `add_smul_ne_zero`; ★★★ `expectation_mk_add_smul` — **the exact expansion along a projective
  line through an eigenline**;
* `belowSpan hA λ` — the span of the `e_j` with `μ_j < λ`;
  `inner_eigenvectorBasis_eq_zero_of_mem_belowSpan`, `inner_eq_zero_of_mem_belowSpan` (it is
  orthogonal to every eigenvector of eigenvalue `λ`);
* ★★ `finrank_real_belowSpan` — **its real dimension is `2 · #{j | μ_j < λ}`**;
* ★★ `hessForm_neg_of_mem_belowSpan` — **the form is negative definite on it**;
  ★★ `hessForm_nonneg_of_inner_eq_zero` — **nonnegative on its orthogonal complement**;
* ★★★ `expectation_mk_add_smul_lt_of_mem_belowSpan` — **`⟨A⟩` strictly decreases from `λ` along
  every projective line into the negative span**; `expectation_mk_add_smul_ge_of_inner_eq_zero` —
  it does not decrease along lines in the complement.

## Honest scope

⚠️ **The Hessian along projective lines.** The second-order form is computed along the curves
`t ↦ [ψ + t v]` (exactly, not just to second order); its identification with the chart Hessian
of `⟨A⟩` at the critical point is not stated. The index is stated as a negative-definite span of
the stated dimension with a nonnegative complement — the two facts that fix a Morse index — not
through a general Morse-index definition, and the Morse inequalities are not here.

⚠️ **Degenerate eigenvalues.** When `λ` is repeated the form has a kernel beyond the line itself
(the other eigenvectors of `λ`), so `⟨A⟩` is Morse–Bott, not Morse; the statements above hold as
written.

## References

T. Frankel, Ann. of Math. 70 (1959) 1 (`⟨A⟩` on `ℂℙⁿ` as a perfect Morse–Bott function);
J. Milnor, *Morse Theory* (1963) § 2; `Instances/ProjectiveSpaceCriticalPoints.lean` (#326, #334);
`specs/BACKLOG.md` #337; `specs/future-work.md`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Matrix ComplexConjugate

noncomputable section

namespace Projectivization

variable {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}

/-- `A e_j = μ_j e_j` for Mathlib's eigenvector basis. -/
theorem toEuclideanLin_eigenvectorBasis (hA : A.IsHermitian) (j : Fin (n + 1)) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis j)
      = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
  have hk := hA.mulVec_eigenvectorBasis j
  ext k
  have h := congrFun hk k
  simp only [Pi.smul_apply] at h
  rw [Matrix.toLpLin_apply]
  simp only [PiLp.smul_apply]
  rw [h, Complex.real_smul]
  rfl

/-- `⟨x, A x⟩ = Σ μ_j |⟨e_j, x⟩|²`. -/
theorem re_inner_toEuclideanLin_eq_sum (hA : A.IsHermitian) (x : Ambient n) :
    (inner ℂ x (Matrix.toEuclideanLin A x)).re
      = ∑ j, hA.eigenvalues j * ‖inner ℂ (hA.eigenvectorBasis j) x‖ ^ 2 := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin A x), Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : inner ℂ (hA.eigenvectorBasis j) (Matrix.toEuclideanLin A x)
      = (hA.eigenvalues j : ℂ) * inner ℂ (hA.eigenvectorBasis j) x := by
    rw [← hT, toEuclideanLin_eigenvectorBasis, inner_smul_left, Complex.conj_ofReal]
  rw [h1, ← inner_conj_symm (hA.eigenvectorBasis j) x, mul_left_comm, Complex.mul_conj',
    Complex.norm_conj]
  norm_cast

/-- `‖x‖² = Σ |⟨e_j, x⟩|²`. -/
theorem norm_sq_eq_sum_norm_inner_eigenvectorBasis (hA : A.IsHermitian) (x : Ambient n) :
    ‖x‖ ^ 2 = ∑ j, ‖inner ℂ (hA.eigenvectorBasis j) x‖ ^ 2 := by
  have h := congrArg Complex.re (hA.eigenvectorBasis.sum_inner_mul_inner x x)
  rw [Complex.re_sum, inner_self_eq_norm_sq_to_K] at h
  have hx : ((‖x‖ : ℂ) ^ 2).re = ‖x‖ ^ 2 := by norm_cast
  refine hx.symm.trans (h.symm.trans (Finset.sum_congr rfl fun j _ => ?_))
  rw [← inner_conj_symm (hA.eigenvectorBasis j) x, Complex.mul_conj', Complex.norm_conj]
  norm_cast

/-- ★ **The Hessian form in the eigenbasis**: `⟨v, A v⟩ − λ ‖v‖² = Σ (μ_j − λ) |⟨e_j, v⟩|²`. -/
theorem hessForm_eq_sum (hA : A.IsHermitian) (lam : ℝ) (v : Ambient n) :
    (inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2
      = ∑ j, (hA.eigenvalues j - lam) * ‖inner ℂ (hA.eigenvectorBasis j) v‖ ^ 2 := by
  rw [re_inner_toEuclideanLin_eq_sum hA, norm_sq_eq_sum_norm_inner_eigenvectorBasis hA v,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A unit vector plus an orthogonal one is nonzero. -/
theorem add_smul_ne_zero {ψ v : Ambient n} (h1 : ‖ψ‖ = 1) (hv : inner ℂ ψ v = 0) (t : ℝ) :
    ψ + (t : ℂ) • v ≠ 0 := by
  intro h0
  have h := congrArg (inner ℂ ψ) h0
  rw [inner_add_right, inner_smul_right, hv, mul_zero, add_zero, inner_zero_right,
    inner_self_eq_norm_sq_to_K, h1] at h
  norm_num at h

/-- ★★★ **The exact expansion along a projective line through an eigenline**: for a unit
eigenvector `ψ` of eigenvalue `λ` and `v ⊥ ψ`,
`⟨A⟩([ψ + t v]) = λ + t² (⟨v, A v⟩ − λ ‖v‖²) / (1 + t² ‖v‖²)`. -/
theorem expectation_mk_add_smul (hA : A.IsHermitian) {ψ v : Ambient n} {lam : ℝ}
    (hψ : Matrix.toEuclideanLin A ψ = (lam : ℂ) • ψ) (h1 : ‖ψ‖ = 1) (hv : inner ℂ ψ v = 0)
    (t : ℝ) :
    expectation A (mk ℂ (ψ + (t : ℂ) • v) (add_smul_ne_zero h1 hv t))
      = lam + t ^ 2 * ((inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2)
          / (1 + t ^ 2 * ‖v‖ ^ 2) := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have hv' : inner ℂ v ψ = 0 := by rw [← inner_conj_symm, hv, map_zero]
  have hψAv : inner ℂ ψ (Matrix.toEuclideanLin A v) = 0 := by
    rw [← hT, hψ, inner_smul_left, hv, mul_zero]
  have hvAψ : inner ℂ v (Matrix.toEuclideanLin A ψ) = 0 := by
    rw [hψ, inner_smul_right, hv', mul_zero]
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, h1]; norm_num
  have hn : ‖ψ + (t : ℂ) • v‖ ^ 2 = 1 + t ^ 2 * ‖v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ψ ((t : ℂ) • v)
      (by rw [inner_smul_right, hv, mul_zero])
    rw [sq, sq, h, h1, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [show |t| * ‖v‖ * (|t| * ‖v‖) = |t| ^ 2 * ‖v‖ ^ 2 by ring, sq_abs]
    ring
  rw [expectation_mk, hn, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, hψ, inner_smul_right,
    hψψ, hψAv, inner_smul_right, hv', Complex.conj_ofReal]
  have hpos : (0 : ℝ) < 1 + t ^ 2 * ‖v‖ ^ 2 := by positivity
  rw [div_eq_iff hpos.ne']
  simp only [mul_zero, add_zero, zero_add, mul_one, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
  ring

/-- **The negative span**: the span of the eigenvectors with eigenvalue below `λ`. -/
def belowSpan (hA : A.IsHermitian) (lam : ℝ) : Submodule ℂ (Ambient n) :=
  Submodule.span ℂ (Set.range fun j : {j : Fin (n + 1) // hA.eigenvalues j < lam} =>
    hA.eigenvectorBasis j)

/-- A vector of the negative span has no component along an eigenvector of eigenvalue `≥ λ`. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem_belowSpan (hA : A.IsHermitian) {lam : ℝ}
    {v : Ambient n} (hv : v ∈ belowSpan hA lam) {j : Fin (n + 1)}
    (hj : lam ≤ hA.eigenvalues j) : inner ℂ (hA.eigenvectorBasis j) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hjk : j ≠ k.1 := by
      rintro rfl
      exact absurd k.2 (not_lt.2 hj)
    exact hA.eigenvectorBasis.orthonormal.2 hjk
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- The negative span is orthogonal to every eigenvector of eigenvalue `λ`. -/
theorem inner_eq_zero_of_mem_belowSpan (hA : A.IsHermitian) {lam : ℝ} {ψ v : Ambient n}
    (hψ : Matrix.toEuclideanLin A ψ = (lam : ℂ) • ψ) (hv : v ∈ belowSpan hA lam) :
    inner ℂ ψ v = 0 := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have h := hT ψ (hA.eigenvectorBasis k)
    rw [hψ, toEuclideanLin_eigenvectorBasis, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal] at h
    have hne : (lam : ℂ) - (hA.eigenvalues k : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast (ne_of_lt k.2).symm
    have h2 : ((lam : ℂ) - (hA.eigenvalues k : ℂ)) * inner ℂ ψ (hA.eigenvectorBasis k) = 0 := by
      rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- ★★ **The negative span has real dimension `2 · #{j | μ_j < λ}`.** -/
theorem finrank_real_belowSpan (hA : A.IsHermitian) (lam : ℝ) :
    Module.finrank ℝ (belowSpan hA lam)
      = 2 * Fintype.card {j : Fin (n + 1) // hA.eigenvalues j < lam} := by
  rw [finrank_real_of_complex, belowSpan,
    finrank_span_eq_card (b := fun j : {j : Fin (n + 1) // hA.eigenvalues j < lam} =>
      hA.eigenvectorBasis j)
      (hA.eigenvectorBasis.orthonormal.linearIndependent.comp _ Subtype.val_injective)]

/-- ★★ **The Hessian form is negative definite on the negative span.** -/
theorem hessForm_neg_of_mem_belowSpan (hA : A.IsHermitian) {lam : ℝ} {v : Ambient n}
    (hv : v ∈ belowSpan hA lam) (hv0 : v ≠ 0) :
    (inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2 < 0 := by
  rw [hessForm_eq_sum hA]
  obtain ⟨j₀, hj₀⟩ : ∃ j, inner ℂ (hA.eigenvectorBasis j) v ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h := norm_sq_eq_sum_norm_inner_eigenvectorBasis hA v
    simp only [hall, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, pow_eq_zero_iff, norm_eq_zero] at h
    exact hv0 h
  have hlt : hA.eigenvalues j₀ < lam := by
    by_contra hge
    exact hj₀ (inner_eigenvectorBasis_eq_zero_of_mem_belowSpan hA hv (not_lt.1 hge))
  have hterm : ∀ j, (hA.eigenvalues j - lam) * ‖inner ℂ (hA.eigenvectorBasis j) v‖ ^ 2 ≤ 0 := by
    intro j
    by_cases hj : hA.eigenvalues j < lam
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · rw [inner_eigenvectorBasis_eq_zero_of_mem_belowSpan hA hv (not_lt.1 hj)]
      simp
  calc ∑ j, (hA.eigenvalues j - lam) * ‖inner ℂ (hA.eigenvectorBasis j) v‖ ^ 2
      < ∑ _j : Fin (n + 1), (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hterm j) ⟨j₀, Finset.mem_univ _,
          mul_neg_of_neg_of_pos (by linarith) (by positivity)⟩
    _ = 0 := Finset.sum_const_zero

/-- ★★ **The Hessian form is nonnegative on the orthogonal complement of the negative span.** -/
theorem hessForm_nonneg_of_inner_eq_zero (hA : A.IsHermitian) {lam : ℝ} {v : Ambient n}
    (hv : ∀ j, hA.eigenvalues j < lam → inner ℂ (hA.eigenvectorBasis j) v = 0) :
    0 ≤ (inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2 := by
  rw [hessForm_eq_sum hA]
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases hj : hA.eigenvalues j < lam
  · rw [hv j hj]
    simp
  · exact mul_nonneg (by linarith [not_lt.1 hj]) (by positivity)

/-- ★★★ **`⟨A⟩` strictly decreases from `λ` along every projective line into the negative
span.** -/
theorem expectation_mk_add_smul_lt_of_mem_belowSpan (hA : A.IsHermitian) {ψ v : Ambient n}
    {lam : ℝ} (hψ : Matrix.toEuclideanLin A ψ = (lam : ℂ) • ψ) (h1 : ‖ψ‖ = 1)
    (hv : v ∈ belowSpan hA lam) (hv0 : v ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    expectation A (mk ℂ (ψ + (t : ℂ) • v)
      (add_smul_ne_zero h1 (inner_eq_zero_of_mem_belowSpan hA hψ hv) t)) < lam := by
  rw [expectation_mk_add_smul hA hψ h1 (inner_eq_zero_of_mem_belowSpan hA hψ hv)]
  have hneg := hessForm_neg_of_mem_belowSpan hA hv hv0
  have ht2 : 0 < t ^ 2 := by positivity
  have hpos : (0 : ℝ) < 1 + t ^ 2 * ‖v‖ ^ 2 := by positivity
  have : t ^ 2 * ((inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2)
      / (1 + t ^ 2 * ‖v‖ ^ 2) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht2 hneg) hpos
  linarith

/-- `⟨A⟩` does not decrease from `λ` along projective lines orthogonal to the negative span. -/
theorem expectation_mk_add_smul_ge_of_inner_eq_zero (hA : A.IsHermitian) {ψ v : Ambient n}
    {lam : ℝ} (hψ : Matrix.toEuclideanLin A ψ = (lam : ℂ) • ψ) (h1 : ‖ψ‖ = 1)
    (hψv : inner ℂ ψ v = 0)
    (hv : ∀ j, hA.eigenvalues j < lam → inner ℂ (hA.eigenvectorBasis j) v = 0) (t : ℝ) :
    lam ≤ expectation A (mk ℂ (ψ + (t : ℂ) • v) (add_smul_ne_zero h1 hψv t)) := by
  rw [expectation_mk_add_smul hA hψ h1 hψv]
  have hnn := hessForm_nonneg_of_inner_eq_zero hA hv
  have hpos : (0 : ℝ) < 1 + t ^ 2 * ‖v‖ ^ 2 := by positivity
  have : 0 ≤ t ^ 2 * ((inner ℂ v (Matrix.toEuclideanLin A v)).re - lam * ‖v‖ ^ 2)
      / (1 + t ^ 2 * ‖v‖ ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg t) hnn) hpos.le
  linarith

end Projectivization
