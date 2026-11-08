/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonBracket
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MomentMap
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The unitary moment map of `ℂℙⁿ`: states as projectors

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(MomentMap)** — this module uses the vector-field sense of
"Hamiltonian" and the symplectic sense of "moment map"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #328 (geometric QM, item 7 of the 2026-11-08 plan).

The `U(n+1)` action on `ℂℙⁿ` has the moment map `μ(p) = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩`, valued in the
Hermitian matrices (the dual of `𝔲(n+1)` through the trace pairing). Its component along a
Hermitian `A` is the expectation value `tr(μ A) = ⟨A⟩`, whose Hamiltonian vector field generates
the flow `exp(-itA)` (#325, G13). The image of `μ` is exactly the rank-one projectors, `μ` is
injective, the convex hull of its image is the set of density matrices, and its diagonal is the
torus moment map.

## The projector of a vector

* `rankOneMatrix v = ‖v‖⁻² · v v*` (the matrix of `Projectivization.rankOneProj`, which is an
  operator on a general inner-product space), `star_dotProduct_self`, `ofReal_norm_sq_ne_zero`;
  `rankOneMatrix_smul` (scale invariance), `isHermitian_rankOneMatrix`, `trace_rankOneMatrix`,
  `rankOneMatrix_mul_self`, `rankOneMatrix_mulVec`, `posSemidef_rankOneMatrix`,
  `trace_rankOneMatrix_mul`, `rankOneMatrix_toEuclideanLin_unitary`.

## The moment map

* `unitaryMomentMap p = rankOneMatrix p.rep`; `unitaryMomentMap_mk`;
* ★ `unitaryMomentMap_smul` — **equivariance**: `μ(U • p) = U μ(p) U†`;
* ★★ `trace_unitaryMomentMap_mul`, `re_trace_unitaryMomentMap_mul`,
  `trace_unitaryMomentMap_mul_of_isHermitian` — **`tr(μ(p) A) = ⟨A⟩_p`**;
* ★★ `isHamiltonianVectorField_trace_unitaryMomentMap` — **the component `p ↦ tr(μ(p) A)` has the
  Hamiltonian vector field `-½ X_A`**, the generator of `exp(-itA)`;
* ★ `unitaryMomentMap_diag` — **the diagonal is the torus moment map** `‖ψₖ‖² / ‖ψ‖²`;
* ★★ `unitaryMomentMap_injective`;
* `eq_zero_of_isHermitian_idempotent_trace_eq_zero`; ★★★ `range_unitaryMomentMap` — **the image is
  exactly the Hermitian idempotents of trace one** (the rank-one projectors);
* `mul_diagonal_mul_conjTranspose_eq_sum` (the spectral expansion over the columns);
  ★★★ `convexHull_range_unitaryMomentMap` — **the convex hull of the image is the set of density
  matrices** `{ρ | ρ ≥ 0, tr ρ = 1}`.

## Honest scope

⚠️ **The pairing is the trace.** `μ` is valued in matrices, identified with `𝔲(n+1)*` through
`A ↦ tr(μ A)` on Hermitian `A`; no Lie-algebra dual is constructed, and the moment-map equation is
stated component by component (`isHamiltonianVectorField_trace_unitaryMomentMap`), with the
corpus's `-½` (from `schrodingerHamiltonian = -2⟨H⟩`).

⚠️ **The torus moment map is matched entrywise**, as the diagonal of `μ`; the torus action as a
restriction of the unitary one is G6's, not restated.

## References

T. W. B. Kibble, Commun. Math. Phys. 65 (1979) 189; A. Ashtekar, T. A. Schilling, in *On
Einstein's Path* (1999) 23, § 3; V. Guillemin, S. Sternberg, *Symplectic techniques in physics*
(1984), § 26; `Instances/ProjectiveSpacePoissonBracket.lean` (#325),
`LinearAlgebra/Projectivization/MomentMap.lean` (`momentMap`); `specs/BACKLOG.md` #328;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix ComplexOrder
open Kahler DifferentialForm Matrix

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-! ### The projector of a vector -/

/-- **The projector onto a vector**, `‖v‖⁻² · v v*`. -/
def rankOneMatrix (v : Ambient n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ • vecMulVec v.ofLp (star v.ofLp)

theorem star_dotProduct_self (v : Ambient n) :
    star v.ofLp ⬝ᵥ v.ofLp = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem ofReal_norm_sq_ne_zero {v : Ambient n} (hv : v ≠ 0) : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hv)

/-- Scale invariance. -/
theorem rankOneMatrix_smul {c : ℂ} (hc : c ≠ 0) (v : Ambient n) :
    rankOneMatrix (c • v) = rankOneMatrix v := by
  unfold rankOneMatrix
  have hofLp : (c • v).ofLp = c • v.ofLp := rfl
  rw [hofLp, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, norm_smul, mul_pow,
    Complex.ofReal_mul, smul_smul]
  congr 1
  have hc' : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
  have hcc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  rw [mul_assoc, hcc, mul_inv, mul_comm ((((‖c‖ ^ 2 : ℝ) : ℂ))⁻¹) _, mul_assoc,
    inv_mul_cancel₀ hc', mul_one]

theorem isHermitian_rankOneMatrix (v : Ambient n) : (rankOneMatrix v).IsHermitian := by
  unfold rankOneMatrix IsHermitian
  rw [conjTranspose_smul, conjTranspose_vecMulVec, star_star, star_inv₀, Complex.star_def,
    Complex.conj_ofReal]

theorem trace_rankOneMatrix {v : Ambient n} (hv : v ≠ 0) : (rankOneMatrix v).trace = 1 := by
  unfold rankOneMatrix
  rw [trace_smul, trace_vecMulVec, dotProduct_comm, star_dotProduct_self, smul_eq_mul,
    inv_mul_cancel₀ (ofReal_norm_sq_ne_zero hv)]

theorem rankOneMatrix_mulVec (v : Ambient n) (x : Fin (n + 1) → ℂ) :
    rankOneMatrix v *ᵥ x = (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ * (star v.ofLp ⬝ᵥ x)) • v.ofLp := by
  unfold rankOneMatrix
  rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem rankOneMatrix_mul_self {v : Ambient n} (hv : v ≠ 0) :
    rankOneMatrix v * rankOneMatrix v = rankOneMatrix v := by
  unfold rankOneMatrix
  rw [smul_mul_smul_comm, mul_vecMulVec, vecMulVec_mulVec, star_dotProduct_self]
  rw [show (MulOpposite.op (((‖v‖ ^ 2 : ℝ) : ℂ)) • v.ofLp) = ((‖v‖ ^ 2 : ℝ) : ℂ) • v.ofLp from
    op_smul_eq_smul _ _, smul_vecMulVec, smul_smul, mul_assoc,
    inv_mul_cancel₀ (ofReal_norm_sq_ne_zero hv),
    mul_one]

theorem posSemidef_rankOneMatrix (v : Ambient n) : (rankOneMatrix v).PosSemidef := by
  unfold rankOneMatrix
  refine (posSemidef_vecMulVec_self_star v.ofLp).smul ?_
  rw [← Complex.ofReal_inv]
  exact Complex.zero_le_real.2 (inv_nonneg.2 (sq_nonneg _))

/-- `tr(P_v A) = ⟪v, A v⟫ / ‖v‖²`. -/
theorem trace_rankOneMatrix_mul (v : Ambient n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (rankOneMatrix v * A).trace
      = ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ * inner ℂ v (Matrix.toEuclideanLin A v) := by
  unfold rankOneMatrix
  rw [smul_mul, trace_smul, vecMulVec_mul, trace_vecMulVec, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct]
  congr 1
  rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]
  rfl

/-- `P_{U v} = U P_v U†` for a unitary `U`. -/
theorem rankOneMatrix_toEuclideanLin_unitary (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (v : Ambient n) :
    rankOneMatrix (Matrix.toEuclideanLin (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) v)
      = (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * rankOneMatrix v
        * (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ := by
  unfold rankOneMatrix
  rw [norm_toEuclideanLin_unitary]
  have hU : (Matrix.toEuclideanLin (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) v).ofLp
      = (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v.ofLp := rfl
  rw [hU, star_mulVec, mul_smul_comm, smul_mul, mul_vecMulVec, vecMulVec_mul]

/-! ### The moment map -/

/-- **The unitary moment map** `μ(p) = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩`. -/
def unitaryMomentMap (p : ℙ ℂ (Ambient n)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  rankOneMatrix p.rep

theorem unitaryMomentMap_mk (ψ : Ambient n) (hψ : ψ ≠ 0) :
    unitaryMomentMap (mk ℂ ψ hψ) = rankOneMatrix ψ := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ ψ hψ
  unfold unitaryMomentMap
  rw [← ha, Units.smul_def, rankOneMatrix_smul a.ne_zero]

/-- ★ **Equivariance**: `μ(U • p) = U μ(p) U†`. -/
theorem unitaryMomentMap_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    unitaryMomentMap (U • p)
      = (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * unitaryMomentMap p
        * (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ := by
  have hw : Matrix.toEuclideanLin (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) p.rep ≠ 0 :=
    (Matrix.UnitaryGroup.toEuclideanLinearEquiv U).map_ne_zero_iff.2 (rep_nonzero p)
  have hsmul : U • p
      = mk ℂ (Matrix.toEuclideanLin (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) p.rep) hw := by
    conv_lhs => rw [← mk_rep p]
    rfl
  rw [hsmul, unitaryMomentMap_mk, rankOneMatrix_toEuclideanLin_unitary]
  rfl

/-- ★★ **`tr(μ(p) A) = ⟪ψ, Aψ⟫ / ‖ψ‖²`**, for any matrix `A`. -/
theorem trace_unitaryMomentMap_mul (p : ℙ ℂ (Ambient n))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (unitaryMomentMap p * A).trace
      = ((‖p.rep‖ ^ 2 : ℝ) : ℂ)⁻¹ * inner ℂ p.rep (Matrix.toEuclideanLin A p.rep) :=
  trace_rankOneMatrix_mul _ A

/-- ★★ **The real part of `tr(μ(p) A)` is `⟨A⟩_p`**; for Hermitian `A` it is real. -/
theorem re_trace_unitaryMomentMap_mul (p : ℙ ℂ (Ambient n))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (unitaryMomentMap p * A).trace.re = expectation A p := by
  rw [trace_unitaryMomentMap_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul, expectation,
    inv_mul_eq_div]

theorem trace_unitaryMomentMap_mul_of_isHermitian {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    (unitaryMomentMap p * A).trace = (expectation A p : ℂ) := by
  rw [← re_trace_unitaryMomentMap_mul]
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have him : (unitaryMomentMap p * A).trace.im = 0 := by
    rw [trace_unitaryMomentMap_mul, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
    have h := hT.coe_re_inner_apply_self p.rep
    rw [hT p.rep p.rep] at h
    have : (inner ℂ p.rep (Matrix.toEuclideanLin A p.rep)).im = 0 := by
      rw [← h]
      exact Complex.ofReal_im _
    rw [this, mul_zero]
  exact (Complex.ext rfl (by simp [him]))

/-- ★★ **The component `p ↦ tr(μ(p) A)` of the moment map has Hamiltonian vector field `-½ X_A`**,
the generator of `exp(-itA)`. -/
theorem isHamiltonianVectorField_trace_unitaryMomentMap {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    IsHamiltonianVectorField (fun x => fsForm x) (fun x => (-(1 / 2) : ℝ) • schrodingerField A x)
      (fun p => (unitaryMomentMap p * A).trace.re) := by
  have h : (fun p : ℙ ℂ (Ambient n) => (unitaryMomentMap p * A).trace.re) = expectation A :=
    funext fun p => re_trace_unitaryMomentMap_mul p A
  rw [h]
  exact expectation_isHamiltonianVectorField hA

/-- ★ **The diagonal of `μ` is the torus moment map.** -/
theorem unitaryMomentMap_diag (p : ℙ ℂ (Ambient n)) (k : Fin (n + 1)) :
    unitaryMomentMap p k k = (momentMap p k : ℂ) := by
  unfold unitaryMomentMap rankOneMatrix momentMap
  rw [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, Complex.star_def,
    Complex.mul_conj']
  push_cast
  ring

/-- ★★ **`μ` is injective.** -/
theorem unitaryMomentMap_injective : Function.Injective (unitaryMomentMap (n := n)) := by
  intro p q h
  have hp := rep_nonzero p
  have hpp : unitaryMomentMap p *ᵥ p.rep.ofLp = p.rep.ofLp := by
    unfold unitaryMomentMap
    rw [rankOneMatrix_mulVec, star_dotProduct_self, inv_mul_cancel₀ (ofReal_norm_sq_ne_zero hp),
      one_smul]
  rw [h, unitaryMomentMap, rankOneMatrix_mulVec] at hpp
  set c := ((‖q.rep‖ ^ 2 : ℝ) : ℂ)⁻¹ * (star q.rep.ofLp ⬝ᵥ p.rep.ofLp)
  have hv : c • q.rep = p.rep := by
    ext k
    exact congrFun hpp k
  rw [← mk_rep p, ← mk_rep q]
  exact ((mk_eq_mk_iff' ℂ _ _ hp (rep_nonzero q)).2 ⟨c, hv⟩)

/-- A Hermitian idempotent of trace zero is zero. -/
theorem eq_zero_of_isHermitian_idempotent_trace_eq_zero {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (ht : Q.trace = 0) : Q = 0 := by
  refine (trace_conjTranspose_mul_self_eq_zero_iff (A := Q)).1 ?_
  rw [hQ.eq, hQQ, ht]

/-- ★★★ **The image of `μ` is exactly the Hermitian idempotents of trace one.** -/
theorem range_unitaryMomentMap :
    Set.range (unitaryMomentMap (n := n))
      = {P | P.IsHermitian ∧ P * P = P ∧ P.trace = 1} := by
  ext P
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨isHermitian_rankOneMatrix _, rankOneMatrix_mul_self (rep_nonzero p),
      trace_rankOneMatrix (rep_nonzero p)⟩
  · rintro ⟨hH, hPP, htr⟩
    -- a column of `P` with nonzero diagonal entry
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, P k k ≠ 0 := by
      refine Finset.exists_ne_zero_of_sum_ne_zero ?_
      rw [show ∑ k, P k k = P.trace from rfl, htr]
      exact one_ne_zero
    set v : Ambient n := WithLp.toLp 2 (P *ᵥ Pi.single k 1) with hvdef
    have hvk : v.ofLp k = P k k := by
      simp [hvdef]
    have hv : v ≠ 0 := by
      intro h0
      apply hk
      rw [← hvk, h0]
      rfl
    have hPv : P *ᵥ v.ofLp = v.ofLp := by
      show P *ᵥ (P *ᵥ Pi.single k 1) = P *ᵥ Pi.single k 1
      rw [mulVec_mulVec, hPP]
    have hvP : star v.ofLp ᵥ* P = star v.ofLp := by
      conv_lhs => rw [← hH.eq]
      rw [← star_mulVec, hPv]
    set R := rankOneMatrix v
    have hPR : P * R = R := by
      unfold R rankOneMatrix
      rw [mul_smul_comm, mul_vecMulVec, hPv]
    have hRP : R * P = R := by
      unfold R rankOneMatrix
      rw [smul_mul, vecMulVec_mul, hvP]
    have hQ : P - R = 0 := by
      refine eq_zero_of_isHermitian_idempotent_trace_eq_zero ?_ ?_ ?_
      · exact hH.sub (isHermitian_rankOneMatrix v)
      · rw [sub_mul, mul_sub, mul_sub, hPP, hPR, hRP, rankOneMatrix_mul_self hv]
        abel
      · rw [trace_sub, htr, trace_rankOneMatrix hv, sub_self]
    refine ⟨mk ℂ v hv, ?_⟩
    rw [unitaryMomentMap_mk]
    exact (sub_eq_zero.1 hQ).symm

/-- The spectral expansion `U diag(d) U† = Σᵢ dᵢ uᵢ uᵢ*` over the columns `uᵢ` of `U`. -/
theorem mul_diagonal_mul_conjTranspose_eq_sum (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) :
    U * diagonal d * Uᴴ = ∑ i, d i • vecMulVec (fun a => U a i) (star fun a => U a i) := by
  ext a b
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.smul_apply,
    vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- ★★★ **The convex hull of the image of `μ` is the set of density matrices.** -/
theorem convexHull_range_unitaryMomentMap :
    convexHull ℝ (Set.range (unitaryMomentMap (n := n)))
      = {ρ | ρ.PosSemidef ∧ ρ.trace = 1} := by
  have hconv :
      Convex ℝ {ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | ρ.PosSemidef ∧ ρ.trace = 1} := by
    rintro x ⟨hx, hxt⟩ y ⟨hy, hyt⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · have hx' := hx.smul (a := (a : ℂ)) (by exact_mod_cast ha)
      have hy' := hy.smul (a := (b : ℂ)) (by exact_mod_cast hb)
      rw [Complex.coe_smul] at hx' hy'
      exact hx'.add hy'
    · rw [trace_add, trace_smul, trace_smul, hxt, hyt, Complex.real_smul, Complex.real_smul]
      simp only [mul_one]
      exact_mod_cast hab
  apply le_antisymm
  · refine convexHull_min ?_ hconv
    rintro _ ⟨p, rfl⟩
    exact ⟨posSemidef_rankOneMatrix _, trace_rankOneMatrix (rep_nonzero p)⟩
  · rintro ρ ⟨hρ, hρt⟩
    have hH : ρ.IsHermitian := hρ.isHermitian
    set U := Matrix.IsHermitian.eigenvectorUnitary hH
    set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      with hM
    have hMU : M ∈ unitaryGroup (Fin (n + 1)) ℂ := U.2
    set ev := Matrix.IsHermitian.eigenvalues hH
    have hspec := Matrix.IsHermitian.spectral_theorem hH
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      mul_diagonal_mul_conjTranspose_eq_sum] at hspec
    -- each column of `U` is a unit vector, so its projector is `u u*`
    have hcol : ∀ i, ∃ p : ℙ ℂ (Ambient n),
        unitaryMomentMap p = vecMulVec (fun a => M a i)
          (star fun a => M a i) := by
      intro i
      set u : Ambient n := WithLp.toLp 2 fun a => M a i
      have hnorm : ((‖u‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← star_dotProduct_self]
        have h1 := congrFun (congrFun (mem_unitaryGroup_iff'.1 hMU) i) i
        rw [star_eq_conjTranspose, mul_apply, one_apply_eq] at h1
        rw [← h1]
        simp [dotProduct, u]
      have hu : u ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hnorm
        norm_num at hnorm
      refine ⟨mk ℂ u hu, ?_⟩
      rw [unitaryMomentMap_mk, rankOneMatrix, hnorm, inv_one, one_smul]
    choose p hp using hcol
    have hsum : ∑ i, ev i = 1 := by
      have h := Matrix.IsHermitian.trace_eq_sum_eigenvalues hH
      rw [hρt] at h
      have := congrArg Complex.re h
      simpa using this.symm
    have hρ' : ρ = ∑ i, ev i • unitaryMomentMap (p i) := by
      conv_lhs => rw [hspec]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp i, Function.comp_apply, ← Complex.coe_smul]
      rfl
    rw [hρ']
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => Matrix.PosSemidef.eigenvalues_nonneg hρ i) hsum
      fun i _ => subset_convexHull ℝ _ ⟨p i, rfl⟩

end Projectivization
