/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ArenaBridge
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.KroneckerAlgHom
public import CsdLean4.Mathlib.Analysis.Normed.Algebra.ExpUnique
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Product rays of two carriers with different index types

**Category:** 3-Local (CV; continuous variables — composition of two carriers at the arena
level, over arbitrary finite index types).

`CV/CompositeArena.lean` composes two field sectors that share a level count, through mode
concatenation, and records that a composite of carriers with different index types needs the
arena API over an arbitrary index. `GenArena ι` is that API (#133). This module states the
product-state half of `CompositeArena.lean` on `GenArena (ι × κ)`, with no reindexing, and adds
the exponential of a Kronecker sum.

* `prodVec`, `prodVec_apply`, `prodVec_smul_smul`, `norm_prodVec`, `prodVec_ne_zero`;
  `prodRay`, `prodRay_mk` — the product ray of two rays (the Segre map);
* `arenaDM_prodRay` — its density is the Kronecker product of the two densities;
* `im_trace_arenaDM_mul`, ★ `arenaObs_kronecker` — **the expectation of `A ⊗ B` in a product ray
  is the product of the two expectations**, for Hermitian `A`; `arenaObs_kronecker_one`,
  `arenaObs_one_kronecker`;
* `kronecker_isHermitian`, `kronU`, `kronU_val`, `toEuclideanLin_kronU`, ★ `arenaKick_kronU` —
  **a product unitary carries a product ray to the product of the two kicked rays**;
* `exp_smul_kronecker_one`, `exp_smul_one_kronecker`, ★ `exp_smul_kronecker_add` — **the
  exponential of a Kronecker sum is the Kronecker product of the exponentials**.

## Exact scope

* **Product rays only.** Every statement about a ray is about a ray in the image of `prodRay`.
  That image is expected to be a proper closed subset of `GenArena (ι × κ)` when both index
  types have at least two elements; that is not proved here (`bell_not_join` of
  `CompositeArena.lean` is the analogue for field sectors). Nothing here is about an entangled
  ray.
* **Distinguishable carriers.** The index is the product `ι × κ`. No symmetrisation.
* **No dynamics is chosen here.** `exp_smul_kronecker_add` is a matrix identity.

## References

`specs/future-work.md` (records to spacetime; composition of sectors);
`specs/composite-arena-plan.md`; `CV/CompositeArena.lean` (`arenaJoin`, `arenaDM_join`,
`arenaObs_join_mul`, `arenaKick_join`: the same statements for field sectors);
`CV/ArenaBridge.lean` (`GenArena`, `arenaDM`, `arenaObs`, `arenaKick`);
`Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom.lean` (`kroneckerLeftAlgHom`,
`kroneckerRightAlgHom`); `Mathlib/Analysis/Normed/Algebra/ExpUnique.lean`
(`exp_smul_eq_of_hasDerivAt`).
-/

@[expose] public section

open Matrix NormedSpace
open scoped Kronecker Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.CV

section ProductRay

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The product vector and the product ray -/

/-- **The product vector** of two state vectors: `(u ⊗ v)(i, k) = u i · v k`. -/
noncomputable def prodVec (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun c => u c.1 * v c.2

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma prodVec_apply (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) (c : ι × κ) :
    prodVec u v c = u c.1 * v c.2 := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The product vector is bilinear on scalars. -/
lemma prodVec_smul_smul (a b : ℂ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    prodVec (a • u) (b • v) = (a * b) • prodVec u v := by
  ext c
  simp only [prodVec_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
/-- The norm of a product vector is the product of the norms. -/
lemma norm_prodVec (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    ‖prodVec u v‖ = ‖u‖ * ‖v‖ := by
  have hsum : ∑ c, ‖prodVec u v c‖ ^ 2 = (∑ a, ‖u a‖ ^ 2) * (∑ b, ‖v b‖ ^ 2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [prodVec_apply, norm_mul, mul_pow]
  have hsq : ‖prodVec u v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    rw [← euclid_sum_norm_sq (prodVec u v), hsum, euclid_sum_norm_sq u, euclid_sum_norm_sq v,
      mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).mp hsq

omit [DecidableEq ι] [DecidableEq κ] in
/-- The product of two nonzero vectors is nonzero. -/
lemma prodVec_ne_zero {u : EuclideanSpace ℂ ι} {v : EuclideanSpace ℂ κ} (hu : u ≠ 0)
    (hv : v ≠ 0) : prodVec u v ≠ 0 := by
  intro h0
  have h := norm_prodVec u v
  rw [h0, norm_zero] at h
  rcases mul_eq_zero.mp h.symm with h | h
  · exact hu (norm_eq_zero.mp h)
  · exact hv (norm_eq_zero.mp h)

/-- **The product ray** of two rays: the ray of the product of their representatives. -/
noncomputable def prodRay (p : GenArena ι) (q : GenArena κ) : GenArena (ι × κ) :=
  Projectivization.mk ℂ (prodVec p.rep q.rep)
    (prodVec_ne_zero (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q))

omit [DecidableEq ι] [DecidableEq κ] in
/-- The product ray on representatives: the choice of representatives washes out. -/
lemma prodRay_mk {u : EuclideanSpace ℂ ι} (hu : u ≠ 0) {v : EuclideanSpace ℂ κ} (hv : v ≠ 0) :
    prodRay (Projectivization.mk ℂ u hu) (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (prodVec u v) (prodVec_ne_zero hu hv) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (Projectivization.mk_rep (Projectivization.mk ℂ u hu))
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (Projectivization.mk_rep (Projectivization.mk ℂ v hv))
  rw [prodRay]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨a * b, by rw [← ha, ← hb, prodVec_smul_smul]⟩

/-! ### The density and the expectations of a product ray -/

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The density of a product ray is the Kronecker product of the densities.** -/
theorem arenaDM_prodRay (p : GenArena ι) (q : GenArena κ) :
    arenaDM (prodRay p q) = arenaDM p ⊗ₖ arenaDM q := by
  rw [prodRay, arenaDM_mk, arenaDM, arenaDM]
  set u := p.rep
  set v := q.rep
  ext c d
  rw [Matrix.kroneckerMap_apply, dmVec_apply', dmVec_apply', dmVec_apply', norm_prodVec,
    prodVec_apply, prodVec_apply]
  rw [show ((((‖u‖ * ‖v‖) ^ 2 : ℝ)) : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) from by
    push_cast; ring, mul_inv, star_mul']
  ring

omit [DecidableEq ι] in
/-- The expectation of a Hermitian matrix in a ray is real. -/
lemma im_trace_arenaDM_mul (p : GenArena ι) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((arenaDM p * A).trace).im = 0 := by
  have hherm : (arenaDM p)ᴴ = arenaDM p := (arenaDM_posSemidef p).1
  have hstar : star ((arenaDM p * A).trace) = (arenaDM p * A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hherm,
      Matrix.trace_mul_comm]
  rw [Complex.star_def] at hstar
  exact Complex.conj_eq_iff_im.mp hstar

omit [DecidableEq ι] [DecidableEq κ] in
/-- ★ **The expectation of `A ⊗ B` in a product ray is the product of the expectations**, for
Hermitian `A`. A property of product rays; it says nothing about an entangled ray. -/
theorem arenaObs_kronecker {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (B : Matrix κ κ ℂ)
    (p : GenArena ι) (q : GenArena κ) :
    arenaObs (A ⊗ₖ B) (prodRay p q) = arenaObs A p * arenaObs B q := by
  rw [arenaObs, arenaObs, arenaObs, arenaDM_prodRay, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker]
  simp only [RCLike.re_to_complex]
  rw [Complex.mul_re, im_trace_arenaDM_mul p hA, zero_mul, sub_zero]

omit [DecidableEq ι] in
/-- A first-factor observable read on a product ray sees the first ray only. -/
theorem arenaObs_kronecker_one (A : Matrix ι ι ℂ) (p : GenArena ι) (q : GenArena κ) :
    arenaObs (A ⊗ₖ (1 : Matrix κ κ ℂ)) (prodRay p q) = arenaObs A p := by
  rw [arenaObs, arenaObs, arenaDM_prodRay, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, arenaDM_trace, mul_one]

omit [DecidableEq κ] in
/-- A second-factor observable read on a product ray sees the second ray only. -/
theorem arenaObs_one_kronecker (B : Matrix κ κ ℂ) (p : GenArena ι) (q : GenArena κ) :
    arenaObs ((1 : Matrix ι ι ℂ) ⊗ₖ B) (prodRay p q) = arenaObs B q := by
  rw [arenaObs, arenaObs, arenaDM_prodRay, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, arenaDM_trace, one_mul]

/-! ### Product unitaries -/

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem kronecker_isHermitian {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- **The product unitary** `U ⊗ V` on the product index. -/
noncomputable def kronU (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨U.val ⊗ₖ V.val, by
    have hU : (U.val)ᴴ * U.val = 1 := by
      have hmem := U.property
      rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    have hV : (V.val)ᴴ * V.val = 1 := by
      have hmem := V.property
      rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
      Matrix.one_kronecker_one]⟩

@[simp] lemma kronU_val (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    (kronU U V).val = U.val ⊗ₖ V.val := rfl

/-- The product unitary acts on a product vector factor by factor. -/
lemma toEuclideanLin_kronU (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ)
    (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    Matrix.toEuclideanLin (kronU U V).val (prodVec u v)
      = prodVec (Matrix.toEuclideanLin U.val u) (Matrix.toEuclideanLin V.val v) := by
  ext c
  rw [show (Matrix.toEuclideanLin (kronU U V).val (prodVec u v)) c
      = ∑ d, (kronU U V).val c d * prodVec u v d from rfl, prodVec_apply,
    show (Matrix.toEuclideanLin U.val u) c.1 = ∑ b₁, U.val c.1 b₁ * u b₁ from rfl,
    show (Matrix.toEuclideanLin V.val v) c.2 = ∑ b₂, V.val c.2 b₂ * v b₂ from rfl,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  rw [kronU_val, Matrix.kroneckerMap_apply, prodVec_apply]
  ring

/-- ★ **A product unitary carries a product ray to the product of the two kicked rays.** -/
theorem arenaKick_kronU (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ)
    (p : GenArena ι) (q : GenArena κ) :
    arenaKick (kronU U V) (prodRay p q) = prodRay (arenaKick U p) (arenaKick V q) := by
  rw [show prodRay p q = Projectivization.mk ℂ (prodVec p.rep q.rep)
      (prodVec_ne_zero (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q))
      from rfl, arenaKick_mk, arenaKick, arenaKick, prodRay_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1, by rw [one_smul, toEuclideanLin_kronU]⟩

/-! ### The exponential of a Kronecker sum -/

/-- `exp (t (X ⊗ 1)) = exp (t X) ⊗ 1`: both sides solve `U' = (X ⊗ 1) U`, `U 0 = 1`. -/
theorem exp_smul_kronecker_one (X : Matrix ι ι ℂ) (t : ℝ) :
    exp (t • (X ⊗ₖ (1 : Matrix κ κ ℂ))) = exp (t • X) ⊗ₖ (1 : Matrix κ κ ℂ) := by
  let R : Matrix ι ι ℂ →L[ℝ] Matrix (ι × κ) (ι × κ) ℂ :=
    LinearMap.toContinuousLinearMap
      ((kroneckerLeftAlgHom ℂ ι κ).toLinearMap.restrictScalars ℝ)
  have hR : ∀ Y, R Y = Y ⊗ₖ (1 : Matrix κ κ ℂ) := fun Y => kroneckerLeftAlgHom_apply Y
  have hU : ∀ c : ℝ, HasDerivAt (fun c : ℝ => R (exp (c • X)))
      ((X ⊗ₖ (1 : Matrix κ κ ℂ)) * R (exp (c • X))) c := by
    intro c
    have h := R.hasFDerivAt.comp_hasDerivAt c (hasDerivAt_exp_smul_const' X c)
    refine h.congr_deriv ?_
    rw [hR, hR, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have h0 : (fun c : ℝ => R (exp (c • X))) 0 = 1 := by
    simp only [zero_smul, exp_zero, hR, Matrix.one_kronecker_one]
  have h := exp_smul_eq_of_hasDerivAt _ h0 hU t
  simpa only [hR] using h.symm

/-- `exp (t (1 ⊗ Y)) = 1 ⊗ exp (t Y)`. -/
theorem exp_smul_one_kronecker (Y : Matrix κ κ ℂ) (t : ℝ) :
    exp (t • ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) = (1 : Matrix ι ι ℂ) ⊗ₖ exp (t • Y) := by
  let R : Matrix κ κ ℂ →L[ℝ] Matrix (ι × κ) (ι × κ) ℂ :=
    LinearMap.toContinuousLinearMap
      ((kroneckerRightAlgHom ℂ ι κ).toLinearMap.restrictScalars ℝ)
  have hR : ∀ Z, R Z = (1 : Matrix ι ι ℂ) ⊗ₖ Z := fun Z => kroneckerRightAlgHom_apply Z
  have hU : ∀ c : ℝ, HasDerivAt (fun c : ℝ => R (exp (c • Y)))
      (((1 : Matrix ι ι ℂ) ⊗ₖ Y) * R (exp (c • Y))) c := by
    intro c
    have h := R.hasFDerivAt.comp_hasDerivAt c (hasDerivAt_exp_smul_const' Y c)
    refine h.congr_deriv ?_
    rw [hR, hR, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have h0 : (fun c : ℝ => R (exp (c • Y))) 0 = 1 := by
    simp only [zero_smul, exp_zero, hR, Matrix.one_kronecker_one]
  have h := exp_smul_eq_of_hasDerivAt _ h0 hU t
  simpa only [hR] using h.symm

/-- ★ **The exponential of a Kronecker sum is the Kronecker product of the exponentials**:
`exp (t (X ⊗ 1 + 1 ⊗ Y)) = exp (t X) ⊗ exp (t Y)`. -/
theorem exp_smul_kronecker_add (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (t : ℝ) :
    exp (t • (X ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ Y))
      = exp (t • X) ⊗ₖ exp (t • Y) := by
  have h0 : Commute (X ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ Y) := by
    rw [Commute, SemiconjBy, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hcomm : Commute (t • (X ⊗ₖ (1 : Matrix κ κ ℂ))) (t • ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) :=
    (h0.smul_left t).smul_right t
  rw [smul_add, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_kronecker_one,
    exp_smul_one_kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

end ProductRay

end CSD.CV

end
