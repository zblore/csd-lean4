/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Mathlib upstream candidate: the Cauchy–Binet formula

**Category:** 1-Mathlib (CSD-free).

For a `k × m` matrix `A` and an `m × k` matrix `B`, the determinant of the square product is a sum
over the `k`-element sets of columns of `A` (rows of `B`):

  `det (A * B) = ∑_{S, |S| = k} det A_S · det B_S`.

Mathlib proves `det_mul` only for square matrices. This file proves the rectangular formula in two
steps.

* `Matrix.det_mul_eq_sum_fun` — **the sum over all functions**:
  `det (A * B) = ∑ f : n → m, (∏ i, B (f i) i) * det (A.submatrix id f)`, the first step of
  Mathlib's own proof of `det_mul`, for any finite `m`; the terms with `f` not injective vanish
  (`det_submatrix_id_eq_zero_of_not_injective`).
* `Tuple.injectiveEquivStrictMonoPerm` — an injective tuple `Fin k → m` into a linear order is a
  strictly increasing tuple composed with a permutation, uniquely (by `Tuple.sort`); and
  `Tuple.sum_injective_eq_sum_strictMono_perm`, the regrouping it gives for any sum.
* ★★ `Matrix.det_mul_eq_sum_strictMono` — **Cauchy–Binet**, the sum over strictly increasing
  `g : Fin k → m`, i.e. over the `k`-element subsets of `m`;
* ★ `Matrix.det_conjTranspose_mul_self_eq_sum` — `det (Bᴴ * B) = ∑_g star (det B_g) * det B_g`, the
  form a Gram-determinant consumer needs.

## Namespace / staging

Declarations live in `namespace Matrix` and `namespace Tuple` (Mathlib's namespaces for `det` and
`Tuple.sort`), so upstreaming is a file move onto `Mathlib/LinearAlgebra/Matrix/Determinant/`, no
symbol rename. Mathlib has no Cauchy–Binet formula as of the pinned revision (the only mention is
the docstring of `cross_dot_cross`).
MATHLIB-ABSENT(Matrix.det_mul_eq_sum_strictMono) MATHLIB-ABSENT(Matrix.det_mul_eq_sum_fun)

## Consumers

- `CsdLean4/SigmaLayer/ManyIdenticalParticles.lean` (`norm_sq_slater`: the Slater determinant's norm
  is `n!` times the Gram determinant of the orbitals; BACKLOG #217).
-/

@[expose] public section

open Equiv Finset

namespace Tuple

variable {k : ℕ} {m : Type*} [LinearOrder m]

/-- Sorting an injective tuple after a permutation: `sort (f ∘ σ) = σ⁻¹ * sort f`. -/
theorem sort_comp_perm_of_injective {f : Fin k → m} (hf : Function.Injective f) (σ : Perm (Fin k)) :
    sort (f ∘ σ) = σ⁻¹ * sort f := by
  have h := comp_perm_comp_sort_eq_comp_sort (f := f) (σ := σ)
  have h2 : ⇑σ ∘ ⇑(sort (f ∘ σ)) = ⇑(sort f) := hf.comp_left h
  rw [eq_inv_mul_iff_mul_eq]
  exact DFunLike.coe_injective (by rw [Perm.coe_mul]; exact h2)

theorem strictMono_comp_sort_of_injective {f : Fin k → m} (hf : Function.Injective f) :
    StrictMono (f ∘ sort f) :=
  (monotone_sort f).strictMono_of_injective (hf.comp (sort f).injective)

/-- **An injective tuple is a strictly increasing tuple composed with a permutation**, uniquely:
`f = (f ∘ sort f) ∘ (sort f)⁻¹`. -/
def injectiveEquivStrictMonoPerm (k : ℕ) (m : Type*) [LinearOrder m] :
    {f : Fin k → m // Function.Injective f} ≃ {g : Fin k → m // StrictMono g} × Perm (Fin k) where
  toFun f := (⟨f.1 ∘ sort f.1, strictMono_comp_sort_of_injective f.2⟩, (sort f.1)⁻¹)
  invFun p := ⟨p.1.1 ∘ p.2, p.1.2.injective.comp p.2.injective⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    simp
  right_inv p := by
    obtain ⟨⟨g, hg⟩, τ⟩ := p
    have hs : sort (g ∘ τ) = τ⁻¹ := by
      rw [sort_comp_perm_of_injective hg.injective, (sort_eq_refl_iff_monotone).2 hg.monotone]
      rfl
    simp only [hs, inv_inv, Prod.mk.injEq, and_true]
    apply Subtype.ext
    funext i
    simp

/-- **Regrouping a sum over injective tuples** by their sorted form and the sorting permutation. -/
theorem sum_injective_eq_sum_strictMono_perm {M : Type*} [AddCommMonoid M]
    [Fintype {f : Fin k → m // Function.Injective f}]
    [Fintype {g : Fin k → m // StrictMono g}] (F : (Fin k → m) → M) :
    ∑ f : {f : Fin k → m // Function.Injective f}, F f.1
      = ∑ g : {g : Fin k → m // StrictMono g}, ∑ τ : Perm (Fin k), F (g.1 ∘ τ) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (injectiveEquivStrictMonoPerm k m) _ _ fun f =>
    congrArg F (funext fun i => by simp [injectiveEquivStrictMonoPerm])

end Tuple

namespace Matrix

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n]

/-- **The determinant of a rectangular product as a sum over all functions**:
`det (A * B) = ∑ f : n → m, (∏ i, B (f i) i) * det (A.submatrix id f)`. -/
theorem det_mul_eq_sum_fun [Fintype m] (A : Matrix n m R) (B : Matrix m n R) :
    det (A * B) = ∑ f : n → m, (∏ i, B (f i) i) * det (A.submatrix id f) := by
  simp only [det_apply', mul_apply, prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- A matrix with two equal columns has determinant zero: `A.submatrix id f` for `f` not
injective. -/
theorem det_submatrix_id_eq_zero_of_not_injective (A : Matrix n m R) {f : n → m}
    (hf : ¬ Function.Injective f) : det (A.submatrix id f) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨i, j, h, hne⟩ := hf
    exact ⟨i, j, h, hne⟩
  exact det_zero_of_column_eq hne fun r => by simp [hij]

/-- **The Cauchy–Binet formula**: for `A : k × m` and `B : m × k`, `det (A * B)` is the sum over the
strictly increasing `g : Fin k → m` (the `k`-element subsets of `m`) of
`det (A.submatrix id g) * det (B.submatrix g id)`. -/
theorem det_mul_eq_sum_strictMono {k : ℕ} [Fintype m] [LinearOrder m]
    [Fintype {g : Fin k → m // StrictMono g}] (A : Matrix (Fin k) m R) (B : Matrix m (Fin k) R) :
    det (A * B) = ∑ g : {g : Fin k → m // StrictMono g},
      det (A.submatrix id g.1) * det (B.submatrix g.1 id) := by
  classical
  rw [det_mul_eq_sum_fun, ← Fintype.sum_subtype_add_sum_subtype Function.Injective]
  rw [Fintype.sum_eq_zero (fun f : {f : Fin k → m // ¬ Function.Injective f} =>
      (∏ i, B (f.1 i) i) * det (A.submatrix id f.1))
    (fun f => by rw [det_submatrix_id_eq_zero_of_not_injective A f.2, mul_zero]), add_zero,
    Tuple.sum_injective_eq_sum_strictMono_perm (fun f => (∏ i, B (f i) i) * det (A.submatrix id f))]
  refine Fintype.sum_congr _ _ fun g => ?_
  have hperm : ∀ τ : Perm (Fin k),
      det (A.submatrix id (g.1 ∘ τ)) = (Perm.sign τ : R) * det (A.submatrix id g.1) := fun τ => by
    rw [show A.submatrix id (g.1 ∘ τ) = (A.submatrix id g.1).submatrix id τ from rfl,
      det_permute']
  simp only [hperm, det_apply' (B.submatrix g.1 id), submatrix_apply, id, Finset.mul_sum, Function.comp_apply]
  refine Fintype.sum_congr _ _ fun τ => ?_
  ring

/-- **Cauchy–Binet for `Bᴴ * B`**: `det (Bᴴ * B) = ∑_g star (det B_g) * det B_g` over the strictly
increasing `g : Fin k → m`. -/
theorem det_conjTranspose_mul_self_eq_sum {k : ℕ} [StarRing R] [Fintype m] [LinearOrder m]
    [Fintype {g : Fin k → m // StrictMono g}] (B : Matrix m (Fin k) R) :
    det (Bᴴ * B) = ∑ g : {g : Fin k → m // StrictMono g},
      star (det (B.submatrix g.1 id)) * det (B.submatrix g.1 id) := by
  rw [det_mul_eq_sum_strictMono]
  refine Fintype.sum_congr _ _ fun g => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose]

end Matrix
