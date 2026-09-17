/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.SpecialFunctions.JapaneseBracketIntegral
public import CsdLean4.Mathlib.MeasureTheory.Measure.Haar.PiComplex

/-!
# The Japanese bracket integral on a Euclidean space of even dimension

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.SpecialFunctions.JapaneseBracket`).

`JapaneseBracketIntegral.lean` computes `∫_{ℂⁿ} (1 + ∑ⱼ |wⱼ|²)^{-(n+1)} dw = πⁿ / n!` against the
product Lebesgue measure on `Fin n → ℂ`, with the norm written as a coordinate sum. This module
carries the value to the spaces where the norm is the norm:

* ★ `Complex.lintegral_euclideanSpace_pow_inv_one_add_norm_sq` — the same integral on
  `EuclideanSpace ℂ (Fin n)`, `∫ (1 + ‖x‖²)^{-(n+1)} dx = πⁿ / n!`, against the volume of its real
  inner-product structure (`Complex.measurePreserving_ofLp`, `EuclideanSpace.norm_sq_eq`);
* ★★ `lintegral_pow_inv_one_add_norm_sq` — **on every real inner-product space of dimension
  `2n`**, `∫ (1 + ‖x‖²)^{-(n+1)} dx = πⁿ / n!`: any two such spaces are isometric through their
  orthonormal bases, and a linear isometry preserves the volume
  (`LinearIsometryEquiv.measurePreserving`).

Only the exponent `n + 1` in dimension `2n` is computed — the one the Fubini–Study mass needs — not
the general `(1 + ‖x‖²)^{-r/2}` of Mathlib's integrability statement.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal Real

noncomputable section

/-- The integrand, as a function of the squared norm; continuous, hence measurable. -/
theorem measurable_pow_inv_one_add_norm_sq {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
    [OpensMeasurableSpace F] (m : ℕ) :
    Measurable fun x : F => ENNReal.ofReal (((1 + ‖x‖ ^ 2)⁻¹) ^ m) :=
  (measurable_const.add ((measurable_norm).pow_const 2)).inv.pow_const m |>.ennreal_ofReal

namespace Complex

/-- ★ **`∫_{ℂⁿ} (1 + ‖x‖²)^{-(n+1)} dx = πⁿ / n!` on `EuclideanSpace ℂ (Fin n)`**, against the
volume of its real inner-product structure: `ofLp` is volume preserving and carries `‖x‖²` to the
coordinate sum `∑ⱼ ‖xⱼ‖²`. -/
theorem lintegral_euclideanSpace_pow_inv_one_add_norm_sq (n : ℕ) :
    ∫⁻ x : EuclideanSpace ℂ (Fin n), ENNReal.ofReal (((1 + ‖x‖ ^ 2)⁻¹) ^ (n + 1))
      = ENNReal.ofReal (π ^ n / n.factorial) := by
  have h := (measurePreserving_ofLp n).lintegral_comp (f := fun w : Fin n → ℂ =>
    ENNReal.ofReal (((1 + ∑ j, ‖w j‖ ^ 2)⁻¹) ^ (n + 1)))
    ((measurable_const.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).norm).pow_const 2)).inv.pow_const _ |>.ennreal_ofReal)
  rw [lintegral_pi_pow_inv_one_add_sum_norm_sq n] at h
  rw [← h]
  refine lintegral_congr fun x => ?_
  simp only [EuclideanSpace.norm_sq_eq]

end Complex

/-- ★★ **The Japanese bracket integral on a real inner-product space of dimension `2n`**:
`∫ (1 + ‖x‖²)^{-(n+1)} dx = πⁿ / n!`. Any two such spaces are isometric through orthonormal bases
indexed by `Fin (2n)` (`OrthonormalBasis.repr`), and a linear isometry preserves the volume. -/
theorem lintegral_pow_inv_one_add_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {n : ℕ}
    (h : finrank ℝ F = 2 * n) :
    ∫⁻ x : F, ENNReal.ofReal (((1 + ‖x‖ ^ 2)⁻¹) ^ (n + 1))
      = ENNReal.ofReal (π ^ n / n.factorial) := by
  -- `F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2n)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)`
  let bF : OrthonormalBasis (Fin (2 * n)) ℝ F := (stdOrthonormalBasis ℝ F).reindex (finCongr h)
  let e : F ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    bF.repr.trans (Complex.euclideanOrthonormalBasis n).repr.symm
  have he : MeasurePreserving e volume volume := e.measurePreserving
  have := he.lintegral_comp
    (measurable_pow_inv_one_add_norm_sq (F := EuclideanSpace ℂ (Fin n)) (n + 1))
  rw [Complex.lintegral_euclideanSpace_pow_inv_one_add_norm_sq] at this
  rw [← this]
  refine lintegral_congr fun x => ?_
  simp [e]
