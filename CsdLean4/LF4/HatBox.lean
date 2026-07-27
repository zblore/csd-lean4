/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.MomentUniform

/-!
# LF4/HatBox: the Archimedes hat-box for the qubit (context-fixed measurement infra, A7)

**Category:** 2-LF4 (Kähler / moment-map layer — sphere-measure infrastructure).

The single-axis crux integral for the **context-fixed** qubit measurement (Paper C A7,
`specs/record-layer-plan.md` §2): the Fubini–Study average over `ℂℙ¹` of the Bloch height
`|λ·n| = |2·momentMap − 1|` is `½` — Archimedes' hat-box. This is the piece the qubit
context-fixed proof reduces to (via `ρ_m = 2(m·λ) + 2|m·λ|` and the hemisphere indicator
`= ½(1 + sign(λ·n))`).

It is **not** raw `S²` integration (Mathlib lacks that): it reduces to the proved fact that the
moment coordinate is `Uniform[0,1]` (`fs_moment_pushforward_uniform`, the ℂℙ¹ Duistermaat–Heckman /
Archimedes result) plus the elementary 1-D integral `∫_{[0,1]} |2t−1| dt = ½`. Foundational-triple,
no `sorry`.

## References
`LF4/MomentUniform.lean` (`fs_moment_pushforward_uniform` — the moment coordinate is Uniform[0,1]);
`LF4/MomentMap.lean` (`momentMap`); `specs/record-layer-plan.md` §2 (the qubit context-fixed crux).
-/

@[expose] public section

open MeasureTheory Set Matrix.UnitaryGroup

namespace CSD.LF4

/-- **The 1-D core of the hat-box:** `∫_{[0,1]} |2t − 1| dt = ½`. -/
theorem integral_abs_two_mul_sub_one :
    ∫ t in Set.Icc (0 : ℝ) 1, |2 * t - 1| = 1 / 2 := by
  have hcont : Continuous fun t : ℝ => |2 * t - 1| := by fun_prop
  have key : ∫ t in (0 : ℝ)..1, |2 * t - 1| = 1 / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (b := 1 / 2) (hcont.intervalIntegrable 0 (1 / 2)) (hcont.intervalIntegrable (1 / 2) 1)]
    have e1 : ∫ t in (0 : ℝ)..(1 / 2), |2 * t - 1| = ∫ t in (0 : ℝ)..(1 / 2), (1 - 2 * t) :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
        rw [abs_of_nonpos (by linarith [ht.2] : 2 * t - 1 ≤ 0)]; ring)
    have e2 : ∫ t in (1 / 2 : ℝ)..1, |2 * t - 1| = ∫ t in (1 / 2 : ℝ)..1, (2 * t - 1) :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at ht
        rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t - 1)])
    rw [e1, e2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => by simpa using (hasDerivAt_id x).sub (hasDerivAt_pow 2 x))
        ((by fun_prop : Continuous fun t : ℝ => 1 - 2 * t).intervalIntegrable 0 (1 / 2)),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => by simpa using (hasDerivAt_pow 2 x).sub (hasDerivAt_id x))
        ((by fun_prop : Continuous fun t : ℝ => 2 * t - 1).intervalIntegrable (1 / 2) 1)]
    simp only [Pi.sub_apply, id_eq]; norm_num
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact key

/-- **The Archimedes hat-box (qubit).** The Fubini–Study average over `ℂℙ¹` of the Bloch height
`|λ·n| = |2·momentMap p 0 − 1|` is `½`. Equivalent to the moment coordinate being `Uniform[0,1]`
(`fs_moment_pushforward_uniform`) plus the 1-D integral (`integral_abs_two_mul_sub_one`). The
single-axis crux for the context-fixed qubit measurement. -/
theorem hatBox_moment (p₀ : CPN 2) :
    ∫ p, |2 * momentMap p 0 - 1| ∂(fubiniStudyMeasure p₀) = 1 / 2 := by
  have hmap := MeasureTheory.integral_map (μ := fubiniStudyMeasure p₀)
    (φ := fun p => momentMap p 0) (f := fun t => |2 * t - 1|)
    (momentMap_measurable 0).aemeasurable (by fun_prop)
  rw [← hmap, fs_moment_pushforward_uniform]
  exact integral_abs_two_mul_sub_one

/-- **The 1-D core of the spread-density normalisation:** `∫_{[0,1]} max(2t − 1, 0) dt = ¼`. -/
theorem integral_max_two_mul_sub_one_zero :
    ∫ t in Set.Icc (0 : ℝ) 1, max (2 * t - 1) 0 = 1 / 4 := by
  have hcont : Continuous fun t : ℝ => max (2 * t - 1) 0 := by fun_prop
  have key : ∫ t in (0 : ℝ)..1, max (2 * t - 1) 0 = 1 / 4 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (b := 1 / 2) (hcont.intervalIntegrable 0 (1 / 2)) (hcont.intervalIntegrable (1 / 2) 1)]
    have e1 : ∫ t in (0 : ℝ)..(1 / 2), max (2 * t - 1) 0 = ∫ _t in (0 : ℝ)..(1 / 2), (0 : ℝ) :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
        rw [max_eq_right (by linarith [ht.2] : 2 * t - 1 ≤ 0)])
    have e2 : ∫ t in (1 / 2 : ℝ)..1, max (2 * t - 1) 0 = ∫ t in (1 / 2 : ℝ)..1, (2 * t - 1) :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at ht
        rw [max_eq_left (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t - 1)])
    rw [e1, e2, intervalIntegral.integral_zero,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => by simpa using (hasDerivAt_pow 2 x).sub (hasDerivAt_id x))
        ((by fun_prop : Continuous fun t : ℝ => 2 * t - 1).intervalIntegrable (1 / 2) 1)]
    simp only [Pi.sub_apply, id_eq]; norm_num
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact key

/-- **The spread density is a probability density.** For the reference (`e₀`) axis, the CSD spread
density `ρ = 4·max(2·momentMap − 1, 0)` (Bloch form `4(m·λ)₊`) integrates to `1` against the
Fubini–Study measure — the normalisation `∫ ρ dμ_FS = 1` of `record-layer-plan.md` §2. Via the moment
coordinate being `Uniform[0,1]` (`fs_moment_pushforward_uniform`) + `integral_max_two_mul_sub_one_zero`. -/
theorem spreadDensity_normalized (p₀ : CPN 2) :
    ∫ p, 4 * max (2 * momentMap p 0 - 1) 0 ∂(fubiniStudyMeasure p₀) = 1 := by
  rw [MeasureTheory.integral_const_mul]
  have hmap := MeasureTheory.integral_map (μ := fubiniStudyMeasure p₀)
    (φ := fun p => momentMap p 0) (f := fun t => max (2 * t - 1) 0)
    (momentMap_measurable 0).aemeasurable (by fun_prop)
  rw [← hmap, fs_moment_pushforward_uniform, integral_max_two_mul_sub_one_zero]
  norm_num

end CSD.LF4
