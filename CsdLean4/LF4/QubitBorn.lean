/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.QubitCrossTerm

/-!
# LF4/QubitBorn: the context-fixed qubit Born rule (A7)

**Category:** 2-LF4 (Kähler / moment-map layer — qubit context-fixed measurement).

**The qubit Born rule, derived from the CSD spread density and the context-fixed hemisphere.** For
unit preparation `ψ` and unit measurement axis `n`, the CSD spread density `ρ_ψ = 4·(2·blochProj ψ − 1)₊`
weighted by the context-fixed hemisphere indicator `½·(1 + rsign(2·blochProj n − 1))` integrates
against the Fubini–Study typicality measure to the **Born weight** `|⟨n|ψ⟩|²`:

  `∫ ½(1 + rsign(2·blochProj n − 1))·4(2·blochProj ψ − 1)₊ dμ_FS = |⟨n|ψ⟩|²`.

The integrand splits into four pieces evaluated in the preceding modules:
`∫(2s−1) = 0`, `∫|2s−1| = ½` (hat-box), `∫ rsign(2u−1)(2s−1) = (2c−1)/2` (dipole),
`∫ rsign(2u−1)|2s−1| = 0` (cross-term), summing to `c = |⟨n|ψ⟩|²`. Foundational-triple, no `sorry`.

## References
`LF4/AxisBridge.lean` (`hatBox_axis`, `blochProj_integral_bridge`); `LF4/QubitDipole.lean` (`dipole`,
`rsign`); `LF4/QubitCrossTerm.lean` (`crossTerm`); `LF4/HatBox.lean` (`fs_moment_pushforward_uniform`);
`specs/record-layer-plan.md` §2 (the qubit context-fixed crux — the payoff).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup Set
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- `∫_{[0,1]} t dt = ½`. -/
theorem integral_id_Icc : ∫ t in Set.Icc (0 : ℝ) 1, t = 1 / 2 := by
  have key : ∫ t in (0 : ℝ)..1, t = 1 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => x ^ 2 / 2)
      (fun x _ => by simpa using (hasDerivAt_pow 2 x).div_const 2)
      ((by fun_prop : Continuous (fun t : ℝ => t)).intervalIntegrable 0 1)]
    norm_num
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact key

/-- The Fubini–Study average of the reference moment coordinate is `½`. -/
theorem momentMap_integral_half (p₀ : CPN 2) :
    ∫ p, momentMap p 0 ∂(fubiniStudyMeasure p₀) = 1 / 2 := by
  have hmap := MeasureTheory.integral_map (μ := fubiniStudyMeasure p₀)
    (φ := fun p => momentMap p 0) (f := fun t => t)
    (momentMap_measurable 0).aemeasurable (by fun_prop)
  rw [← hmap, fs_moment_pushforward_uniform]
  exact integral_id_Icc

/-- **The Fubini–Study average of any Bloch projection is `½`** (general-axis, via the bridge). -/
theorem blochProj_integral_half (a : EuclideanSpace ℂ (Fin 2)) (ha0 : a ≠ 0) (ha : ‖a‖ = 1)
    (p₀ : CPN 2) :
    ∫ p, blochProj a p ∂(fubiniStudyMeasure p₀) = 1 / 2 := by
  rw [blochProj_integral_bridge a ha0 ha p₀ (f := fun t => t) measurable_id,
    momentMap_integral_half]

/-- `4·max(x,0) = 2x + 2|x|` (the `ρ = 2(m·λ) + 2|m·λ|` decomposition). -/
lemma four_max_eq (x : ℝ) : 4 * max x 0 = 2 * x + 2 * |x| := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · push_neg at h
    rw [max_eq_right h.le, abs_of_neg h]; ring

/-- **The context-fixed qubit Born rule.** The CSD spread density `4(2·blochProj ψ − 1)₊` weighted by
the context-fixed hemisphere indicator `½(1 + rsign(2·blochProj n − 1))` integrates against the
Fubini–Study typicality measure to the Born weight `|⟨n|ψ⟩|²`. -/
theorem qubitBorn (n ψ : EuclideanSpace ℂ (Fin 2)) (hn0 : n ≠ 0) (hn : ‖n‖ = 1)
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (p₀ : CPN 2) :
    ∫ p, (1 / 2 : ℝ) * (1 + rsign (2 * blochProj n p - 1))
        * (4 * max (2 * blochProj ψ p - 1) 0) ∂(fubiniStudyMeasure p₀)
      = ‖inner ℂ n ψ‖ ^ 2 := by
  set μ := fubiniStudyMeasure p₀ with hμ
  have hbnd : ∀ p : CPN 2, |2 * blochProj ψ p - 1| ≤ 1 := fun p => by
    have h0 := blochProj_nonneg ψ p
    have h1 := blochProj_le_one ψ hψ p
    rw [abs_le]; constructor <;> linarith
  have hmn : Measurable (fun p : CPN 2 => rsign (2 * blochProj n p - 1)) :=
    measurable_rsign.comp (((blochProj_measurable n).const_mul 2).sub_const 1)
  have hms : Measurable (fun p : CPN 2 => 2 * blochProj ψ p - 1) :=
    ((blochProj_measurable ψ).const_mul 2).sub_const 1
  -- integrabilities
  have hi_bp : Integrable (fun p => blochProj ψ p) μ :=
    Integrable.of_bound (blochProj_measurable ψ).aestronglyMeasurable 1
      (ae_of_all _ (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (blochProj_nonneg ψ p)]; exact blochProj_le_one ψ hψ p))
  have hi1 : Integrable (fun p => 2 * blochProj ψ p - 1) μ :=
    Integrable.of_bound hms.aestronglyMeasurable 1
      (ae_of_all _ (fun p => by rw [Real.norm_eq_abs]; exact hbnd p))
  have hi2 : Integrable (fun p => |2 * blochProj ψ p - 1|) μ :=
    Integrable.of_bound hms.abs.aestronglyMeasurable 1
      (ae_of_all _ (fun p => by rw [Real.norm_eq_abs, abs_abs]; exact hbnd p))
  have hi3 : Integrable (fun p => rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1)) μ :=
    Integrable.of_bound (hmn.mul hms).aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |rsign (2 * blochProj n p - 1)| * |2 * blochProj ψ p - 1|
          ≤ 1 * 1 := mul_le_mul (abs_rsign_le_one _) (hbnd p) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1))
  have hi4 : Integrable (fun p => rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1|) μ :=
    Integrable.of_bound (hmn.mul hms.abs).aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      calc |rsign (2 * blochProj n p - 1)| * |2 * blochProj ψ p - 1|
          ≤ 1 * 1 := mul_le_mul (abs_rsign_le_one _) (hbnd p) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1))
  -- the four component integrals
  have hI1 : ∫ p, (2 * blochProj ψ p - 1) ∂μ = 0 := by
    rw [integral_sub (hi_bp.const_mul 2) (integrable_const 1), integral_const_mul,
      blochProj_integral_half ψ hψ0 hψ p₀, integral_const, hμ]
    simp
  have hI2 : ∫ p, |2 * blochProj ψ p - 1| ∂μ = 1 / 2 := hatBox_axis ψ hψ0 hψ p₀
  have hI3 : ∫ p, rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1) ∂μ
      = (2 * ‖inner ℂ n ψ‖ ^ 2 - 1) / 2 := dipole n ψ hn hψ p₀
  have hI4 : ∫ p, rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1| ∂μ = 0 :=
    crossTerm n ψ hn hψ p₀
  -- pointwise: integrand = f1 + f2 + f3 + f4
  have hpt : ∀ p : CPN 2, (1 / 2 : ℝ) * (1 + rsign (2 * blochProj n p - 1))
        * (4 * max (2 * blochProj ψ p - 1) 0)
      = (2 * blochProj ψ p - 1) + |2 * blochProj ψ p - 1|
        + rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1)
        + rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1| := by
    intro p
    rw [four_max_eq (2 * blochProj ψ p - 1)]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_add (f := fun p => (2 * blochProj ψ p - 1) + |2 * blochProj ψ p - 1|
        + rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1))
      (g := fun p => rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1|)
      ((hi1.add hi2).add hi3) hi4]
  rw [integral_add (f := fun p => (2 * blochProj ψ p - 1) + |2 * blochProj ψ p - 1|)
      (g := fun p => rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1))
      (hi1.add hi2) hi3]
  rw [integral_add (f := fun p => 2 * blochProj ψ p - 1)
      (g := fun p => |2 * blochProj ψ p - 1|) hi1 hi2]
  rw [hI1, hI2, hI3, hI4]
  ring

end CSD.LF4
