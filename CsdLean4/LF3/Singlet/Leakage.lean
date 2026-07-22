/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF3.Singlet.Kernel

/-!
# LF3 Singlet / Leakage: finite-leakage stability of kernel, correlation, marginals

**Category:** 3-Local (LF3 finite-leakage bounds on all four kernel quantities, parameterised by `εA`, `εB`).

Paper §7.

Each finite-leakage bound is a triangle inequality on the appropriate finite
sum over `Sign × Sign` or `Sign`, with the per-sector deviation supplied by
`sectorVolume_finite_leakage` and `LeakageCompat`. Composes
`sectorVolume_finite_leakage` from `Projectors/SectorVolume.lean` with the
`cst_squared_eq` algebraic core.
-/

open scoped BigOperators

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- **Singlet pointer-probability finite-leakage bound** (paper §7.5). The
    measured pointer-sector frequency deviates from `P_{st}(a, b)` by at most
    `εA + εB + εA · εB`. Composes `sectorVolume_finite_leakage` (operator
    layer) with `cst_squared_eq` (algebraic-core identity). -/
theorem singlet_pointer_probability_finite_leakage
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (a b : DetectorSetting)
    (L : LeakageCompat P M φA0 φB0) (s t : Sign) :
    |sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t - P_st a b s t|
      ≤ L.εA + L.εB + L.εA * L.εB := by
  have h_branch := sectorVolume_finite_leakage P M φA0 φB0 (cAmp a b) L s t
  have h_kernel : ‖cAmp a b s t‖ ^ 2 = P_st a b s t := cst_squared_eq a b s t
  rw [h_kernel] at h_branch
  exact h_branch

/-- **Singlet correlation finite-leakage bound** (paper §7.6). The measured
    correlation deviates from `−a·b` by at most `4(εA + εB + εA · εB)`.
    Triangle inequality on the four-term `Sign × Sign` sum, each term bounded
    by the per-sector leakage. -/
theorem correlation_finite_leakage_bound
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (a b : DetectorSetting)
    (L : LeakageCompat P M φA0 φB0) :
    |(∑ st : Sign × Sign,
        st.1.val * st.2.val
          * sectorVolume P (finalState M (cAmp a b) φA0 φB0) st.1 st.2)
      - (-(dotR a b))|
      ≤ 4 * (L.εA + L.εB + L.εA * L.εB) := by
  -- Substitute correlation_eq_neg_dot to rewrite -a·b as ∑ st · P_st:
  rw [show -(dotR a b) = ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2
       from (correlation_eq_neg_dot a b).symm]
  -- Now the difference is a sum of four (st-weighted) per-sector deviations.
  rw [← Finset.sum_sub_distrib]
  -- |∑ x| ≤ ∑ |x|, then bound each |xst| by the leakage.
  calc |∑ st : Sign × Sign,
            (st.1.val * st.2.val
                * sectorVolume P (finalState M (cAmp a b) φA0 φB0) st.1 st.2
              - st.1.val * st.2.val * P_st a b st.1 st.2)|
      ≤ ∑ st : Sign × Sign,
            |st.1.val * st.2.val
                * sectorVolume P (finalState M (cAmp a b) φA0 φB0) st.1 st.2
              - st.1.val * st.2.val * P_st a b st.1 st.2| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ st : Sign × Sign,
            |st.1.val * st.2.val|
              * |sectorVolume P (finalState M (cAmp a b) φA0 φB0) st.1 st.2
                  - P_st a b st.1 st.2| := by
        apply Finset.sum_congr rfl
        intro st _
        rw [← mul_sub]
        rw [abs_mul]
    _ ≤ ∑ st : Sign × Sign, 1 * (L.εA + L.εB + L.εA * L.εB) := by
        apply Finset.sum_le_sum
        intro st _
        apply mul_le_mul
        · cases st.1 <;> cases st.2 <;> simp [Sign.val_plus, Sign.val_minus]
        · exact singlet_pointer_probability_finite_leakage P M φA0 φB0 a b L st.1 st.2
        · exact abs_nonneg _
        · norm_num
    _ = 4 * (L.εA + L.εB + L.εA * L.εB) := by
        rw [Finset.sum_const]
        have h : (Finset.univ : Finset (Sign × Sign)).card = 4 := by decide
        rw [h]
        ring

/-- **Singlet A-side marginal finite-leakage bound** (paper §7.7). -/
theorem marginal_a_finite_leakage_bound
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (a b : DetectorSetting)
    (L : LeakageCompat P M φA0 φB0) (s : Sign) :
    |(∑ t : Sign, sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t) - 1/2|
      ≤ 2 * (L.εA + L.εB + L.εA * L.εB) := by
  rw [show (1/2 : ℝ) = ∑ t : Sign, P_st a b s t from (marginal_a_eq_half a b s).symm]
  rw [← Finset.sum_sub_distrib]
  calc |∑ t : Sign,
            (sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t - P_st a b s t)|
      ≤ ∑ t : Sign,
            |sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t - P_st a b s t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Sign, (L.εA + L.εB + L.εA * L.εB) := by
        apply Finset.sum_le_sum
        intro t _
        exact singlet_pointer_probability_finite_leakage P M φA0 φB0 a b L s t
    _ = 2 * (L.εA + L.εB + L.εA * L.εB) := by
        rw [Sign.sum_univ]; ring

/-- **Singlet B-side marginal finite-leakage bound** (paper §7.7). -/
theorem marginal_b_finite_leakage_bound
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (a b : DetectorSetting)
    (L : LeakageCompat P M φA0 φB0) (t : Sign) :
    |(∑ s : Sign, sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t) - 1/2|
      ≤ 2 * (L.εA + L.εB + L.εA * L.εB) := by
  rw [show (1/2 : ℝ) = ∑ s : Sign, P_st a b s t from (marginal_b_eq_half a b t).symm]
  rw [← Finset.sum_sub_distrib]
  calc |∑ s : Sign,
            (sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t - P_st a b s t)|
      ≤ ∑ s : Sign,
            |sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t - P_st a b s t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Sign, (L.εA + L.εB + L.εA * L.εB) := by
        apply Finset.sum_le_sum
        intro s _
        exact singlet_pointer_probability_finite_leakage P M φA0 φB0 a b L s t
    _ = 2 * (L.εA + L.εB + L.εA * L.εB) := by
        rw [Sign.sum_univ]; ring

end LF3
end CSD
