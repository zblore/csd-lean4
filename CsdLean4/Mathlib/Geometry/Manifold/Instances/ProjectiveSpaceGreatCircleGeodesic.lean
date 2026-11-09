/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerGeodesic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFSDistance
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import CsdLean4.Mathlib.Geometry.Manifold.CovariantDerivativeAlongCurve

/-!
# Great circles are geodesics of the Fubini–Study metric

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #340 (geometric QM, completion item 8c; its Remainder after #341, #342).

For orthonormal `φ, χ` let `H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)`. Then `-iH φ = χ`, `-iH χ = -φ`, so the
Schrödinger orbit of `[φ]` is the great circle `t ↦ [cos t φ + sin t χ]` (#330), and `(ΔH)² ≤ 1`
everywhere (Bessel) with equality at `[φ]`. By #342 the orbit is a geodesic:

* `circleHam φ χ`, `toEuclideanLin_circleHam`, `circleHam_isHermitian`,
  `toEuclideanLin_negI_circleHam`; `toEuclideanCLML` (the matrix-to-operator isometry as a
  continuous linear map, for the product rule);
* ★★ `toEuclideanLin_schrodingerUnitary_circleHam` — **`exp(-itH) φ = cos t φ + sin t χ`**, by
  `d/dt [exp(itH) γ(t)] = 0` (no commutation of `exp` with `H` is used);
* `norm_sq_toEuclideanLin_circleHam`, `variance_circleHam_le_one`, `variance_circleHam_mk` —
  `(ΔH)² ≤ 1` (Bessel), `= 1` at `[φ]`;
* ★★★ `greatCircle_isGeodesic` — **the great circle `t ↦ [cos t φ + sin t χ]` is the integral curve
  of `X_H` through `[φ]`, and `∇_{X_H} X_H = 0` at every point of it.**

## Honest scope

⚠️ **Geodesic in both senses.** `greatCircle_isGeodesic` is the field sense of #342
(`∇_{X_H} X_H = 0` along the integral curve); `isGeodesic_greatCircle` /
`isGeodesic_schrodingerUnitary_smul_of_isMaxOn` are #339's `IsGeodesic` (a differentiable velocity
with `D_t γ' = 0` for the covariant derivative along a curve), via `isGeodesic_of_isMIntegralCurve`.
Unit speed is not normalised (the speed is `2ΔH = 2` in the corpus's metric, #329).

## References

`Instances/ProjectiveSpaceSchrodingerGeodesic.lean` (#342),
`Instances/ProjectiveSpaceFSDistance.lean` (#330, `fsPathLength_greatCircle`);
`specs/BACKLOG.md` #340; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix Matrix.Norms.L2Operator
open Bundle Kahler DifferentialForm Projectivization.FubiniStudy

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- `H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)`. -/
def circleHam (φ χ : Ambient n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Complex.I • (Matrix.vecMulVec χ.ofLp (star φ.ofLp) - Matrix.vecMulVec φ.ofLp (star χ.ofLp))

theorem toEuclideanLin_circleHam (φ χ x : Ambient n) :
    Matrix.toEuclideanLin (circleHam φ χ) x
      = Complex.I • (inner ℂ φ x • χ - inner ℂ χ x • φ) := by
  ext k
  simp only [Matrix.toLpLin_apply, circleHam, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, PiLp.smul_apply, PiLp.sub_apply, Pi.smul_apply, Pi.sub_apply,
    PiLp.inner_apply, WithLp.ofLp_toLp, dotProduct, smul_eq_mul, Pi.star_apply,
    RCLike.inner_apply]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Complex.star_def,
    mul_comm (x.ofLp _) _]
  ring

theorem circleHam_isHermitian (φ χ : Ambient n) : (circleHam φ χ).IsHermitian := by
  unfold Matrix.IsHermitian circleHam
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec,
    Matrix.conjTranspose_vecMulVec, star_star, star_star, Complex.star_def, Complex.conj_I,
    neg_smul, ← smul_neg, neg_sub]

/-- The matrix-to-operator map as a continuous `ℂ`-linear map (an isometry for the `L²` operator
norm). -/
def toEuclideanCLML : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℂ] (Ambient n →L[ℂ] Ambient n) :=
  (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.mkContinuous 1
    fun A => by
      rw [one_mul]
      exact (Matrix.l2_opNorm_toEuclideanCLM A).le

theorem toEuclideanCLML_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (v : Ambient n) :
    toEuclideanCLML A v = Matrix.toEuclideanLin A v := by
  show Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) A v = _
  exact LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A) v

variable {φ χ : Ambient n}

/-- `-iH x = ⟨φ, x⟩ χ − ⟨χ, x⟩ φ`. -/
theorem toEuclideanLin_negI_circleHam (φ χ x : Ambient n) :
    Matrix.toEuclideanLin ((-Complex.I) • circleHam φ χ) x
      = inner ℂ φ x • χ - inner ℂ χ x • φ := by
  rw [map_smul, LinearMap.smul_apply, toEuclideanLin_circleHam, smul_smul]
  rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]

/-- ★★ **`exp(-itH) φ = cos t φ + sin t χ`** for `H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)`, `φ, χ` orthonormal. -/
theorem toEuclideanLin_schrodingerUnitary_circleHam (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1)
    (h0 : inner ℂ φ χ = 0) (t : ℝ) :
    Matrix.toEuclideanLin (Matrix.schrodingerUnitary (circleHam_isHermitian φ χ) t
        : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) φ
      = (Real.cos t : ℂ) • φ + (Real.sin t : ℂ) • χ := by
  set hH := circleHam_isHermitian φ χ
  set K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (-Complex.I) • circleHam φ χ with hK
  set U : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun τ => (Matrix.schrodingerUnitary hH τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hU
  set γ : ℝ → Ambient n := fun τ => (Real.cos τ : ℂ) • φ + (Real.sin τ : ℂ) • χ with hγ
  set γ' : ℝ → Ambient n := fun τ => ((-Real.sin τ : ℝ) : ℂ) • φ + (Real.cos τ : ℂ) • χ
    with hγ'
  have hφφ : inner ℂ φ φ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hφ]; norm_num
  have hχχ : inner ℂ χ χ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hχ]; norm_num
  have hχφ : inner ℂ χ φ = (0 : ℂ) := by rw [← inner_conj_symm, h0, map_zero]
  have hKγ : ∀ τ, Matrix.toEuclideanLin K (γ τ) = γ' τ := by
    intro τ
    rw [hK, toEuclideanLin_negI_circleHam]
    simp only [hγ, hγ', inner_add_right, inner_smul_right, hφφ, hχχ, hχφ, h0, mul_one, mul_zero,
      zero_add, Complex.ofReal_neg, neg_smul, sub_eq_add_neg, add_comm]
  -- the derivative of `τ ↦ U(-τ) γ(τ)` vanishes
  set TR : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℝ] (Ambient n →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Ambient n) (Ambient n) ℝ ℝ).comp
      ((toEuclideanCLML (n := n)).restrictScalars ℝ) with hTR
  have hTRapp : ∀ A v, TR A v = Matrix.toEuclideanLin A v := fun A v => toEuclideanCLML_apply A v
  have hM : ∀ τ, HasDerivAt (fun s => U (-s)) ((-1 : ℝ) • (U (-τ) * K)) τ := fun τ =>
    (Matrix.schrodingerUnitary_hasDerivAt (circleHam φ χ) hH (-τ)).scomp τ (hasDerivAt_neg τ)
  have hu : ∀ τ, HasDerivAt γ (γ' τ) τ := fun τ =>
    ((Real.hasDerivAt_cos τ).ofReal_comp.smul_const φ).add
      ((Real.hasDerivAt_sin τ).ofReal_comp.smul_const χ)
  have hg : ∀ τ, HasDerivAt (fun s => TR (U (-s)) (γ s)) 0 τ := by
    intro τ
    have hc : HasDerivAt (fun s => TR (U (-s))) (TR ((-1 : ℝ) • (U (-τ) * K))) τ :=
      TR.hasFDerivAt.comp_hasDerivAt τ (hM τ)
    have h := hc.clm_apply (hu τ)
    convert h using 1
    rw [map_smul, FunLike.coe_smul, Pi.smul_apply, hTRapp, hTRapp,
      Matrix.toEuclideanLin_mul_apply, hKγ, neg_one_smul, neg_add_cancel]
  have hconst : ∀ τ, TR (U (-τ)) (γ τ) = TR (U (-0)) (γ 0) := fun τ =>
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) τ 0
  have hU0 : U 0 = 1 := by
    simp only [hU, (Matrix.expNegITH_unitary_group hH).2]
    rfl
  have hUt : U t * U (-t) = 1 := by
    simp only [hU]
    rw [← Submonoid.coe_mul, ← (Matrix.expNegITH_unitary_group hH).1, add_neg_cancel,
      (Matrix.expNegITH_unitary_group hH).2]
    rfl
  have h1 := hconst t
  rw [hTRapp, hTRapp, neg_zero, hU0, Matrix.toLpLin_one, LinearMap.id_apply] at h1
  have h2 := congrArg (Matrix.toEuclideanLin (U t)) h1
  rw [← Matrix.toEuclideanLin_mul_apply, hUt, Matrix.toLpLin_one, LinearMap.id_apply] at h2
  have hγ0 : γ 0 = φ := by simp [hγ]
  rw [hγ0] at h2
  exact h2.symm

/-- `‖H ψ‖² = |⟪φ, ψ⟫|² + |⟪χ, ψ⟫|²` for orthonormal `φ, χ`. -/
theorem norm_sq_toEuclideanLin_circleHam (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1)
    (h0 : inner ℂ φ χ = 0) (ψ : Ambient n) :
    ‖Matrix.toEuclideanLin (circleHam φ χ) ψ‖ ^ 2
      = ‖inner ℂ φ ψ‖ ^ 2 + ‖inner ℂ χ ψ‖ ^ 2 := by
  have hχφ : inner ℂ χ φ = (0 : ℂ) := by rw [← inner_conj_symm, h0, map_zero]
  rw [toEuclideanLin_circleHam, norm_smul, Complex.norm_I, one_mul]
  have horth : inner ℂ (inner ℂ φ ψ • χ) (inner ℂ χ ψ • φ) = 0 := by
    rw [inner_smul_left, inner_smul_right, hχφ, mul_zero, mul_zero]
  rw [@norm_sub_sq ℂ, horth, norm_smul, norm_smul, hφ, hχ, mul_one, mul_one]
  simp only [map_zero, mul_zero, sub_zero]

/-- `(ΔH)² ≤ 1` everywhere (Bessel). -/
theorem variance_circleHam_le_one (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1) (h0 : inner ℂ φ χ = 0)
    (p : ℙ ℂ (Ambient n)) : variance (circleHam φ χ) p ≤ 1 := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 (circleHam_isHermitian φ χ)
  have hψ : (0 : ℝ) < ‖p.rep‖ ^ 2 := by
    have := norm_pos_iff.2 (rep_nonzero p)
    positivity
  have hχφ : inner ℂ χ φ = (0 : ℂ) := by rw [← inner_conj_symm, h0, map_zero]
  have hon : Orthonormal ℂ ![φ, χ] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hφ, hχ, h0, hχφ]
  have hB := hon.sum_inner_products_le (s := Finset.univ) (x := p.rep)
  rw [Fin.sum_univ_two] at hB
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hB
  have hHH : expectation (circleHam φ χ * circleHam φ χ) p
      = ‖Matrix.toEuclideanLin (circleHam φ χ) p.rep‖ ^ 2 / ‖p.rep‖ ^ 2 := by
    unfold expectation
    rw [Matrix.toEuclideanLin_mul_apply, ← hT, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hle : expectation (circleHam φ χ * circleHam φ χ) p ≤ 1 := by
    rw [hHH, norm_sq_toEuclideanLin_circleHam hφ hχ h0, div_le_one hψ]
    exact hB
  unfold variance
  nlinarith [sq_nonneg (expectation (circleHam φ χ) p)]

/-- `(ΔH)² = 1` at `[φ]`. -/
theorem variance_circleHam_mk (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1) (h0 : inner ℂ φ χ = 0)
    (hφ0 : φ ≠ 0) : variance (circleHam φ χ) (mk ℂ φ hφ0) = 1 := by
  have hφφ : inner ℂ φ φ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hφ]; norm_num
  have hχχ : inner ℂ χ χ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hχ]; norm_num
  have hχφ : inner ℂ χ φ = (0 : ℂ) := by rw [← inner_conj_symm, h0, map_zero]
  have hHφ : Matrix.toEuclideanLin (circleHam φ χ) φ = Complex.I • χ := by
    rw [toEuclideanLin_circleHam, hφφ, hχφ, one_smul, zero_smul, sub_zero]
  have hHχ : Matrix.toEuclideanLin (circleHam φ χ) χ = -(Complex.I • φ) := by
    rw [toEuclideanLin_circleHam, h0, hχχ, zero_smul, one_smul, zero_sub, smul_neg]
  unfold variance
  rw [expectation_mk, expectation_mk, Matrix.toEuclideanLin_mul_apply, hHφ, map_smul, hHχ, hφ]
  simp [inner_neg_right, inner_smul_right, h0, hφ]

/-- The great-circle vector `cos t φ + sin t χ` of an orthonormal pair is never zero. -/
theorem greatCircleVec_ne_zero (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1) (h0 : inner ℂ φ χ = 0) (t : ℝ) :
    (Real.cos t : ℂ) • φ + (Real.sin t : ℂ) • χ ≠ 0 := by
  intro h
  have hφφ : inner ℂ φ φ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hφ]; norm_num
  have hχχ : inner ℂ χ χ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hχ]; norm_num
  have hχφ : inner ℂ χ φ = (0 : ℂ) := by rw [← inner_conj_symm, h0, map_zero]
  have h1 := congrArg (inner ℂ φ) h
  have h2 := congrArg (inner ℂ χ) h
  simp only [inner_add_right, inner_smul_right, hφφ, h0, hχφ, hχχ, mul_one, mul_zero, add_zero,
    zero_add, inner_zero_right, Complex.ofReal_eq_zero] at h1 h2
  have := Real.cos_sq_add_sin_sq t
  rw [h1, h2] at this
  norm_num at this

/-- ★★★ **Great circles are geodesics of the Fubini–Study metric**: for orthonormal `φ, χ`, the
great circle `t ↦ [cos t φ + sin t χ]` is the Schrödinger orbit of `[φ]` for
`H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)` (an integral curve of `X_H`), and `∇_{X_H} X_H = 0` at every point of
it. -/
theorem greatCircle_isGeodesic (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1) (h0 : inner ℂ φ χ = 0) :
    (∀ t : ℝ, Matrix.schrodingerUnitary (circleHam_isHermitian φ χ) t
        • mk ℂ φ (norm_ne_zero_iff.1 (hφ ▸ one_ne_zero))
        = mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t)) ∧
      IsMIntegralCurve (fun t : ℝ => mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t))
        (schrodingerField (circleHam φ χ)) ∧
      ∀ t : ℝ, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))
        (schrodingerField (circleHam φ χ)) (mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t))
        (schrodingerField (circleHam φ χ) (mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t))) = 0 := by
  have hφ0 : φ ≠ 0 := norm_ne_zero_iff.1 (hφ ▸ one_ne_zero)
  have horb : ∀ t : ℝ, Matrix.schrodingerUnitary (circleHam_isHermitian φ χ) t • mk ℂ φ hφ0
      = mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t) := by
    intro t
    show mapEquiv (Matrix.UnitaryGroup.toEuclideanLinearEquivHom _) (mk ℂ φ hφ0) = _
    rw [mapEquiv, Projectivization.map_mk]
    congr 1
    exact toEuclideanLin_schrodingerUnitary_circleHam hφ hχ h0 t
  have hmax : ∀ p, variance (circleHam φ χ) p ≤ variance (circleHam φ χ) (mk ℂ φ hφ0) := by
    intro p
    rw [variance_circleHam_mk hφ hχ h0]
    exact variance_circleHam_le_one hφ hχ h0 p
  obtain ⟨hint, hgeo⟩ :=
    leviCivita_schrodingerField_self_orbit_eq_zero (circleHam_isHermitian φ χ) hmax
  have hcurve : (fun t : ℝ => Matrix.schrodingerUnitary (circleHam_isHermitian φ χ) t
      • mk ℂ φ hφ0) = fun t : ℝ => mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t) := funext horb
  refine ⟨horb, hcurve ▸ hint, fun t => ?_⟩
  rw [← horb t]
  exact hgeo t

/-- ★★★ **The Schrödinger orbit of a global maximiser of `(ΔH)²` is a geodesic** in the sense of the
covariant derivative along a curve (#339): `D_t γ' = 0`. -/
theorem isGeodesic_schrodingerUnitary_smul_of_isMaxOn
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) {q : ℙ ℂ (Ambient n)}
    (hmax : ∀ p, variance H p ≤ variance H q) :
    CovariantDerivative.IsGeodesic
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)))
      (fun t : ℝ => Matrix.schrodingerUnitary hH t • q) := by
  obtain ⟨hint, hgeo⟩ := leviCivita_schrodingerField_self_orbit_eq_zero hH hmax
  exact CovariantDerivative.isGeodesic_of_isMIntegralCurve _ hint
    (fun t => mdifferentiableAt_schrodingerField hH _) hgeo

/-- ★★★ **Great circles are geodesics of the Fubini–Study metric**, in the sense of the covariant
derivative along a curve (#339): `D_t γ' = 0` for `γ t = [cos t φ + sin t χ]`. -/
theorem isGeodesic_greatCircle (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1) (h0 : inner ℂ φ χ = 0) :
    CovariantDerivative.IsGeodesic
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n)))
      (fun t : ℝ => mk ℂ _ (greatCircleVec_ne_zero hφ hχ h0 t)) := by
  obtain ⟨-, hint, hgeo⟩ := greatCircle_isGeodesic hφ hχ h0
  exact CovariantDerivative.isGeodesic_of_isMIntegralCurve _ hint
    (fun t => mdifferentiableAt_schrodingerField (circleHam_isHermitian φ χ) _) hgeo

end Projectivization
