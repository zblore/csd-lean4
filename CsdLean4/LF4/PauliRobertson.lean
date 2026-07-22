/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.UncertaintyKahler
public import CsdLean4.LF4.SingleQubitKahler

/-!
# LF4 §14.2 Robertson saturation: Pauli σ_x, σ_y on |0⟩ (N=2)

**Category:** 3-Local (LF4 §14.2 concrete instance — first witness of the
Kähler Robertson bound, demonstrating saturation on the canonical
two-non-commuting-Paulis-and-a-spin-z-eigenstate example).

**The classical textbook case.** For Pauli observables `σ_x, σ_y` acting
on the spin-up state `|0⟩ = (1, 0)`:

- `⟨0|σ_x|0⟩ = 0`, `⟨0|σ_y|0⟩ = 0` (off-diagonal expectations vanish on diagonal state).
- `Var(σ_x) = ‖σ_x |0⟩‖² − 0 = 1`, `Var(σ_y) = 1` (each Pauli is unitary and squares to I).
- `[σ_x, σ_y] = 2i·σ_z`, and `⟨0|σ_z|0⟩ = +1`, so `⟨0,[σ_x,σ_y]0⟩ = 2i`.
- Robertson: `1 · 1 ≥ ¼ · |2i|² = ¼ · 4 = 1`. **Saturated**.

Via `UncertaintyKahler.kahler_robertson_ontic_variance`, the Robertson
bound is realised at the **ontic level**:

  `(∫ σ, spectralOnticCentered σ_x σ ∂μψ) · (∫ σ, spectralOnticCentered σ_y σ ∂μψ)
    ≥ ¼ · ‖⟨0, [σ_x, σ_y] 0⟩‖²`.

This module computes both sides explicitly and proves the LHS = RHS = 1
saturation theorem `pauli_xy_robertson_saturation`.

## Module contents

- **Definitions**: `pauliX`, `pauliY` as raw `Matrix (Fin 2) (Fin 2) ℂ`.
- **Hermiticity**: `pauliX_isHermitian`, `pauliY_isHermitian`.
- **Action on |0⟩, |1⟩**: `pauliX_apply_zPlusVec`, `pauliX_apply_zMinusVec`,
  `pauliY_apply_zPlusVec`, `pauliY_apply_zMinusVec`.
- **Expectations**: `pauliX_zPlus_re_expectation = 0`, same for Y.
- **Norm-squareds**: `pauliX_zPlus_norm_sq = 1`, same for Y.
- **Variances**: `pauliX_zPlus_spectralVariance = 1`, same for Y.
- **Ontic integrals**: `pauliX_zPlus_ontic_integral = 1`, same for Y.
- **Commutator inner**: `commutator_inner_zPlus = 2 * Complex.I`.
- **Commutator norm-sq**: `commutator_inner_zPlus_norm_sq = 4`.
- **HEADLINE** `pauli_xy_robertson_saturation`:
  `(LHS) = (1/4) * (RHS) = 1`.

## Axiom posture

Foundational triple only.
-/

@[expose] public section

open MeasureTheory Matrix

namespace CSD
namespace LF4

/-! ### Pauli matrices and the spin-down state -/

/-- The Pauli X matrix `(0,1; 1,0)`. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix `(0,-i; i,0)`. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The spin-down state `|1⟩ = (0, 1)` in `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def zMinusVec : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 1 (1 : ℂ)

lemma zPlusVec_entry_0 : zPlusVec.ofLp 0 = (1 : ℂ) := by
  simp [zPlusVec, EuclideanSpace.single]

lemma zPlusVec_entry_1 : zPlusVec.ofLp 1 = (0 : ℂ) := by
  simp [zPlusVec, EuclideanSpace.single]

lemma zMinusVec_entry_0 : zMinusVec.ofLp 0 = (0 : ℂ) := by
  simp [zMinusVec, EuclideanSpace.single]

lemma zMinusVec_entry_1 : zMinusVec.ofLp 1 = (1 : ℂ) := by
  simp [zMinusVec, EuclideanSpace.single]

lemma zMinusVec_norm : ‖zMinusVec‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, zMinusVec_entry_0, zMinusVec_entry_1,
             norm_zero, norm_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
             zero_pow, one_pow, zero_add]
  exact Real.sqrt_one

/-! ### Hermiticity -/

lemma pauliX_isHermitian : pauliX.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply]

lemma pauliY_isHermitian : pauliY.IsHermitian := by
  show pauliYᴴ = pauliY
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, RCLike.star_def, Complex.conj_I, star_neg]

/-! ### Entry-level facts -/

lemma pauliX_00 : pauliX 0 0 = 0 := by simp [pauliX]
lemma pauliY_00 : pauliY 0 0 = 0 := by simp [pauliY]

/-! ### Pauli action on |0⟩ and |1⟩ -/

lemma pauliX_apply_zPlusVec :
    pauliX.toEuclideanLin zPlusVec = zMinusVec := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  ext i
  fin_cases i <;>
    simp [pauliX, zPlusVec, zMinusVec, EuclideanSpace.single]

lemma pauliX_apply_zMinusVec :
    pauliX.toEuclideanLin zMinusVec = zPlusVec := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  ext i
  fin_cases i <;>
    simp [pauliX, zPlusVec, zMinusVec, EuclideanSpace.single]

lemma pauliY_apply_zPlusVec :
    pauliY.toEuclideanLin zPlusVec = Complex.I • zMinusVec := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  ext i
  fin_cases i <;>
    simp [pauliY, zPlusVec, zMinusVec, EuclideanSpace.single,
          PiLp.smul_apply, smul_eq_mul]

lemma pauliY_apply_zMinusVec :
    pauliY.toEuclideanLin zMinusVec = -Complex.I • zPlusVec := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  ext i
  fin_cases i <;>
    simp [pauliY, zPlusVec, zMinusVec, EuclideanSpace.single,
          PiLp.smul_apply, smul_eq_mul]

/-! ### Expectations on |0⟩ -/

lemma pauliX_zPlus_re_expectation :
    RCLike.re (inner ℂ zPlusVec (pauliX.toEuclideanLin zPlusVec)) = 0 := by
  rw [zPlus_expectation, pauliX_00]; simp

lemma pauliY_zPlus_re_expectation :
    RCLike.re (inner ℂ zPlusVec (pauliY.toEuclideanLin zPlusVec)) = 0 := by
  rw [zPlus_expectation, pauliY_00]; simp

/-! ### Norm-squareds on |0⟩ -/

lemma pauliX_zPlus_norm_sq :
    ‖pauliX.toEuclideanLin zPlusVec‖ ^ 2 = 1 := by
  rw [pauliX_apply_zPlusVec, ← sq_abs, abs_of_nonneg (norm_nonneg _), zMinusVec_norm]
  norm_num

lemma pauliY_zPlus_norm_sq :
    ‖pauliY.toEuclideanLin zPlusVec‖ ^ 2 = 1 := by
  rw [pauliY_apply_zPlusVec, norm_smul, Complex.norm_I, one_mul,
      ← sq_abs, abs_of_nonneg (norm_nonneg _), zMinusVec_norm]
  norm_num

/-! ### Spectral variances = 1 -/

lemma pauliX_zPlus_spectralVariance :
    spectralVariance pauliX_isHermitian zPlusVec = 1 := by
  rw [spectralVariance_eq_hilbert_norm_sq_diff pauliX_isHermitian zPlusVec_norm,
      pauliX_zPlus_norm_sq, pauliX_zPlus_re_expectation]
  ring

lemma pauliY_zPlus_spectralVariance :
    spectralVariance pauliY_isHermitian zPlusVec = 1 := by
  rw [spectralVariance_eq_hilbert_norm_sq_diff pauliY_isHermitian zPlusVec_norm,
      pauliY_zPlus_norm_sq, pauliY_zPlus_re_expectation]
  ring

/-! ### Ontic integrals = 1 -/

lemma pauliX_zPlus_ontic_integral (p₀ : CPN 2) :
    ∫ σ, spectralOnticCentered (M := 2) pauliX_isHermitian zPlusVec σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)) = 1 := by
  rw [integral_spectralOnticCentered_eq_variance pauliX_isHermitian zPlusVec_norm p₀,
      pauliX_zPlus_spectralVariance]

lemma pauliY_zPlus_ontic_integral (p₀ : CPN 2) :
    ∫ σ, spectralOnticCentered (M := 2) pauliY_isHermitian zPlusVec σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)) = 1 := by
  rw [integral_spectralOnticCentered_eq_variance pauliY_isHermitian zPlusVec_norm p₀,
      pauliY_zPlus_spectralVariance]

/-! ### Commutator inner product = 2i, norm² = 4 -/

/-- `[σ_x, σ_y]·|0⟩ = (σ_x σ_y − σ_y σ_x)·|0⟩`. Compute by stepping through
each composition: `σ_x σ_y · |0⟩ = σ_x · (i·|1⟩) = i·|0⟩`, and `σ_y σ_x · |0⟩
= σ_y · |1⟩ = -i·|0⟩`. Subtraction gives `2i·|0⟩`. -/
lemma commutator_apply_zPlusVec :
    (pauliX.toEuclideanLin * pauliY.toEuclideanLin
      - pauliY.toEuclideanLin * pauliX.toEuclideanLin) zPlusVec
      = (2 * Complex.I) • zPlusVec := by
  -- σ_x σ_y · |0⟩
  have h_AB : (pauliX.toEuclideanLin * pauliY.toEuclideanLin) zPlusVec
      = Complex.I • zPlusVec := by
    show pauliX.toEuclideanLin (pauliY.toEuclideanLin zPlusVec) = _
    rw [pauliY_apply_zPlusVec, LinearMap.map_smul, pauliX_apply_zMinusVec]
  -- σ_y σ_x · |0⟩
  have h_BA : (pauliY.toEuclideanLin * pauliX.toEuclideanLin) zPlusVec
      = (-Complex.I) • zPlusVec := by
    show pauliY.toEuclideanLin (pauliX.toEuclideanLin zPlusVec) = _
    rw [pauliX_apply_zPlusVec, pauliY_apply_zMinusVec]
  rw [LinearMap.sub_apply, h_AB, h_BA, ← sub_smul]
  congr 1
  ring

lemma commutator_inner_zPlus :
    inner ℂ zPlusVec ((pauliX.toEuclideanLin * pauliY.toEuclideanLin
        - pauliY.toEuclideanLin * pauliX.toEuclideanLin) zPlusVec)
      = 2 * Complex.I := by
  rw [commutator_apply_zPlusVec, inner_smul_right (𝕜 := ℂ) zPlusVec zPlusVec (2 * Complex.I),
      inner_self_eq_norm_sq_to_K, zPlusVec_norm]
  push_cast
  ring

lemma commutator_inner_zPlus_norm_sq :
    ‖inner ℂ zPlusVec ((pauliX.toEuclideanLin * pauliY.toEuclideanLin
        - pauliY.toEuclideanLin * pauliX.toEuclideanLin) zPlusVec)‖ ^ 2 = 4 := by
  rw [commutator_inner_zPlus, norm_mul, Complex.norm_I, mul_one,
      show ((2 : ℂ) = ((2 : ℝ) : ℂ)) from by norm_cast,
      Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-! ### Headline: saturation -/

/-- **Robertson saturation for Pauli `σ_x, σ_y` on the spin-up state `|0⟩`**.

On the Kähler instance `KSigma 2` with preparation `(Dirac p₀) × vol_T²`,
the ontic-side product of integrated centered indicator-sums for `σ_x`
and `σ_y` on the spin-up state `|0⟩` equals exactly the Robertson lower
bound `¼ · |⟨0, [σ_x, σ_y] · 0⟩|²`, both equal to `1`. The state `|0⟩`
saturates Robertson — it is a minimum-uncertainty state for the pair
`(σ_x, σ_y)`. Combines with `kahler_robertson_ontic_variance` (which
gives `≥`) to give equality. -/
theorem pauli_xy_robertson_saturation (p₀ : CPN 2) :
    (∫ σ, spectralOnticCentered (M := 2) pauliX_isHermitian zPlusVec σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)))
      * (∫ σ, spectralOnticCentered (M := 2) pauliY_isHermitian zPlusVec σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)))
      = (1 / 4) * ‖inner ℂ zPlusVec
          ((pauliX.toEuclideanLin * pauliY.toEuclideanLin
            - pauliY.toEuclideanLin * pauliX.toEuclideanLin) zPlusVec)‖ ^ 2 := by
  rw [pauliX_zPlus_ontic_integral, pauliY_zPlus_ontic_integral,
      commutator_inner_zPlus_norm_sq]
  ring

end LF4
end CSD
