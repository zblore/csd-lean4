/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.UncertaintyKahler
public import CsdLean4.LF4.SingleQubitKahler
public import CsdLean4.LF3.Setup

/-!
# LF4 §14.2 parametric Robertson: σ·â, σ·b̂ on |0⟩ for arbitrary axes (N=2)

**Category:** 3-Local (LF4 §14.2 concrete instance — parametric extension
of `PauliRobertson.lean`. Robertson bound for spin-½ Pauli observables
`σ·â`, `σ·b̂` along arbitrary unit-vector axes `â, b̂`, on the spin-up
state `|0⟩`).

## The parametric inequality

For unit vectors `â, b̂ ∈ ℝ³` (the `DetectorSetting` constraint) and the
spin-up state `|0⟩`:

- `⟨0 | σ·â | 0⟩ = a_z` (third component), real.
- `Var(σ·â) = ‖σ·â · 0‖² − a_z² = 1 − a_z²`  (Pauli unitarity).
- `[σ·â, σ·b̂] = 2i · σ·(â × b̂)`  (standard Pauli algebra).
- `⟨0 | [σ·â, σ·b̂] | 0⟩ = 2i · (â × b̂)_z = 2i · (a_x b_y − a_y b_x)`.
- `¼ · ‖⟨0 | [σ·â, σ·b̂] | 0⟩‖² = (a_x b_y − a_y b_x)²`.

The Robertson bound becomes the **geometric inequality**:

  `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²`.

Both sides are explicit polynomials in the components of `â` and `b̂`.
Equality holds when both axes lie in the xy-plane (`a_z = b_z = 0`) and
are perpendicular (`a_x b_y − a_y b_x = ±1`), e.g., `â = x̂, b̂ = ŷ` —
recovering `PauliRobertson.pauli_xy_robertson_saturation`.

## Axiom posture

Foundational triple only.
-/

@[expose] public section

open MeasureTheory Matrix CSD.LF3

namespace CSD
namespace LF4

/-! ### Variance and ontic integral for σ·â on |0⟩ -/

/-- The `‖σ·â · |0⟩‖² = 1` (Pauli unitarity computed entry-wise on `|0⟩`). -/
lemma pauliDot_zPlus_norm_sq (a : DetectorSetting) :
    ‖(pauliDot a).toEuclideanLin zPlusVec‖ ^ 2 = 1 := by
  -- Entry-wise: pauliDot a · |0⟩ has entries (a_z, a_x + i·a_y).
  have h0 : ((pauliDot a).toEuclideanLin zPlusVec).ofLp 0 = ((a.vec 2 : ℝ) : ℂ) := by
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    simp [pauliDot, Matrix.mulVec, dotProduct,
          zPlusVec, EuclideanSpace.single]
  have h1 : ((pauliDot a).toEuclideanLin zPlusVec).ofLp 1
       = ((a.vec 0 : ℝ) : ℂ) + Complex.I * ((a.vec 1 : ℝ) : ℂ) := by
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    simp [pauliDot, Matrix.mulVec, dotProduct,
          zPlusVec, EuclideanSpace.single]
  rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_two]
  -- Goal: ‖x 0‖² + ‖x 1‖² = 1; convert `x i` to `x.ofLp i` (defeq).
  show ‖((pauliDot a).toEuclideanLin zPlusVec).ofLp 0‖^2
     + ‖((pauliDot a).toEuclideanLin zPlusVec).ofLp 1‖^2 = 1
  rw [h0, h1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h_norm_xy :
      ‖((a.vec 0 : ℝ) : ℂ) + Complex.I * ((a.vec 1 : ℝ) : ℂ)‖ ^ 2
        = (a.vec 0) ^ 2 + (a.vec 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h_norm_xy]
  have h_unit := a.sum_sq_components_eq_one
  linarith

/-- Variance of `σ·â` on `|0⟩` is `1 − a_z²`. -/
lemma pauliDot_zPlus_spectralVariance (a : DetectorSetting) :
    spectralVariance (pauliDot_isHermitian a) zPlusVec = 1 - (a.vec 2) ^ 2 := by
  rw [spectralVariance_eq_hilbert_norm_sq_diff (pauliDot_isHermitian a) zPlusVec_norm,
      zPlus_expectation, pauliDot_zPlus_norm_sq]
  -- `pauliDot a 0 0 = ((a.vec 2 : ℝ) : ℂ)`; `re` collapses the cast.
  rw [show ((pauliDot a) 0 0 : ℂ) = ((a.vec 2 : ℝ) : ℂ) from by simp [pauliDot]]
  -- Goal: 1 − (RCLike.re ((a.vec 2 : ℝ) : ℂ))² = 1 − (a.vec 2)²
  rw [show (RCLike.re ((a.vec 2 : ℝ) : ℂ) : ℝ) = a.vec 2 from RCLike.ofReal_re _]

/-- Ontic-side integrated centered observable for `σ·â` on `|0⟩` is `1 − a_z²`. -/
lemma pauliDot_zPlus_ontic_integral (a : DetectorSetting) (p₀ : CPN 2) :
    ∫ σ, spectralOnticCentered (M := 2) (pauliDot_isHermitian a) zPlusVec σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus))
      = 1 - (a.vec 2) ^ 2 := by
  rw [integral_spectralOnticCentered_eq_variance (pauliDot_isHermitian a)
        zPlusVec_norm p₀, pauliDot_zPlus_spectralVariance]

/-! ### Matrix ↔ Module.End commutator bridge -/

lemma toEuclideanLin_mul_apply (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply,
      Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
      ← Matrix.mulVec_mulVec]

/-! ### Commutator matrix entry (0,0) -/

/-- The `(0,0)` entry of the matrix commutator `[σ·â, σ·b̂]` is
`2i · (a_x b_y − a_y b_x)`. -/
lemma pauliDot_commutator_matrix_00 (a b : DetectorSetting) :
    (pauliDot a * pauliDot b - pauliDot b * pauliDot a) 0 0
      = 2 * Complex.I * (((a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0 : ℝ)) : ℂ) := by
  simp [Matrix.sub_apply, pauliDot]
  ring

/-! ### Commutator inner product on |0⟩ -/

lemma pauliDot_commutator_inner_zPlus (a b : DetectorSetting) :
    inner ℂ zPlusVec
        (((pauliDot a).toEuclideanLin * (pauliDot b).toEuclideanLin
          - (pauliDot b).toEuclideanLin * (pauliDot a).toEuclideanLin) zPlusVec)
      = 2 * Complex.I * (((a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0 : ℝ)) : ℂ) := by
  -- Bridge the Module.End commutator to the matrix commutator's action.
  have h_bridge : ((pauliDot a).toEuclideanLin * (pauliDot b).toEuclideanLin
        - (pauliDot b).toEuclideanLin * (pauliDot a).toEuclideanLin) zPlusVec
      = (pauliDot a * pauliDot b - pauliDot b * pauliDot a).toEuclideanLin zPlusVec := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply,
               ← toEuclideanLin_mul_apply, map_sub]
  rw [h_bridge, zPlus_expectation, pauliDot_commutator_matrix_00]

/-! ### Commutator inner squared norm -/

lemma pauliDot_commutator_inner_zPlus_norm_sq (a b : DetectorSetting) :
    ‖inner ℂ zPlusVec
        (((pauliDot a).toEuclideanLin * (pauliDot b).toEuclideanLin
          - (pauliDot b).toEuclideanLin * (pauliDot a).toEuclideanLin) zPlusVec)‖ ^ 2
      = 4 * (a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0) ^ 2 := by
  rw [pauliDot_commutator_inner_zPlus]
  -- `‖2 * I * (x : ℂ)‖² = 4 · x²` for real `x` (here `x = a_x b_y - a_y b_x`).
  rw [show (2 : ℂ) * Complex.I * (((a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0 : ℝ)) : ℂ)
        = ((2 * (a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0) : ℝ) : ℂ) * Complex.I from by
      push_cast; ring,
      norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-! ### Headline: parametric Robertson on |0⟩ -/

/-- **Parametric Robertson uncertainty for spin-½ on `|0⟩`**. For any
unit-vector measurement axes `â, b̂`, the product of ontic-side variances
of `σ·â, σ·b̂` on the spin-up state `|0⟩` is bounded below by the squared
`z`-component of the cross product `â × b̂`:

  `(1 − a_z²) · (1 − b_z²) ≥ (a_x b_y − a_y b_x)²`.

A geometric inequality: both sides are explicit polynomial functions of
the axis components. Equality holds when both axes lie in the xy-plane
and are perpendicular — recovering `pauli_xy_robertson_saturation` as
the special case `â = x̂, b̂ = ŷ`.

Composes `kahler_robertson_ontic_variance` (the abstract LF4 ontic-
variance Robertson bound) with `pauliDot_zPlus_ontic_integral` (twice)
and `pauliDot_commutator_inner_zPlus_norm_sq`. -/
theorem pauliDot_robertson_zPlus (a b : DetectorSetting) (p₀ : CPN 2) :
    (1 - (a.vec 2) ^ 2) * (1 - (b.vec 2) ^ 2)
      ≥ (a.vec 0 * b.vec 1 - a.vec 1 * b.vec 0) ^ 2 := by
  have h := kahler_robertson_ontic_variance (pauliDot_isHermitian a)
              (pauliDot_isHermitian b) zPlusVec_norm p₀
  rw [pauliDot_zPlus_ontic_integral, pauliDot_zPlus_ontic_integral,
      pauliDot_commutator_inner_zPlus_norm_sq] at h
  linarith

end LF4
end CSD
