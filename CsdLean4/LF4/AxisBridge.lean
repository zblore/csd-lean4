/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.BlochProjection
public import CsdLean4.LF4.HatBox

/-!
# LF4/AxisBridge: general axis ↦ reference axis for Fubini–Study integrals (context-fixed qubit, A7)

**Category:** 2-LF4 (Kähler / moment-map layer — sphere-measure infrastructure).

The **general-axis bridge**: for a unit axis `n`, any Fubini–Study integral of `f ∘ blochProj n`
equals the same integral with `blochProj n` replaced by the reference coordinate `momentMap · 0`
(`= blochProj e₀`):

  `∫ f(blochProj n p) dμ_FS = ∫ f(momentMap p 0) dμ_FS`.

The mechanism is the existing `U(2)`-invariance of the Fubini–Study measure
(`fubiniStudyMeasure_smul_invariant`): a unitary `U` with `U • [e₀] = [n]` moves the axis, and the
measure is unchanged. This is the workhorse that lifts the reference-axis results
(`hatBox_moment`, `spreadDensity_normalized`) to an **arbitrary** measurement axis — in particular
the general-axis hat-box `∫ |2·blochProj n − 1| dμ_FS = ½` and normalisation
`∫ 4·(2·blochProj n − 1)₊ dμ_FS = 1`. Foundational-triple, no `sorry`.

## References
`LF4/BlochProjection.lean` (`blochProj`, `blochProj_smul`, `blochProj_measurable`);
`LF4/HatBox.lean` (`hatBox_moment`, `spreadDensity_normalized` — the reference-axis integrals);
`Mathlib/.../FubiniStudy.lean` (`fubiniStudyMeasure_smul_invariant`); `specs/record-layer-plan.md` §2.
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- **Axis-alignment.** For a unit axis `n` in `ℂ²` there is a unitary `U` sending the reference
coordinate to the `n`-coordinate: `blochProj n (U • p) = momentMap p 0` for all `p`. Obtained from
transitivity of the `U(2)`-action on `ℂℙ¹` (`U • [e₀] = [n]`) plus unitary invariance of the inner
product. -/
lemma exists_unitary_moment_axis (n : EuclideanSpace ℂ (Fin 2)) (hn0 : n ≠ 0) (hn : ‖n‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ p : CPN 2, blochProj n (U • p) = momentMap p 0 := by
  have he0 : (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ≠ 0 := by
    intro h
    have hz : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 0 := by rw [h, norm_zero]
    rw [EuclideanSpace.norm_single, norm_one] at hz
    exact one_ne_zero hz
  obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin 2) ℂ)
    (Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) he0)
    (Projectivization.mk ℂ n hn0)
  -- From `U • [e₀] = [n]` extract the vector relation `c • n = U · e₀`.
  rw [smul_mk_eq_mk U _ he0] at hU
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ _ n (toEuclideanLin_unitary_ne_zero U he0) hn0).mp hU
  rw [Units.smul_def] at hc
  -- |c| = 1 from ‖c • n‖ = ‖U · e₀‖ = ‖e₀‖ = 1.
  have hcabs : ‖(c : ℂ)‖ = 1 := by
    have h1 : ‖(c : ℂ) • n‖
        = ‖(Matrix.toEuclideanLin U.val) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))‖ := by
      rw [hc]
    rw [norm_smul, hn, mul_one, toEuclideanLin_unitary_norm,
      EuclideanSpace.norm_single, norm_one] at h1
    exact h1
  have hn_eq : n
      = (c⁻¹ : ℂ) • (Matrix.toEuclideanLin U.val) (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
  refine ⟨U, fun p => ?_⟩
  have hkey : ‖inner ℂ n ((Matrix.toEuclideanLin U.val) p.rep)‖ = ‖(p.rep 0 : ℂ)‖ := by
    rw [hn_eq, inner_smul_left, norm_mul,
      Projectivization.inner_toEuclideanLin_unitary U
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) p.rep,
      RCLike.norm_conj, show ‖(c⁻¹ : ℂ)‖ = 1 from by rw [norm_inv, hcabs, inv_one], one_mul,
      EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [blochProj_smul, hkey]
  rfl

/-- **General-axis bridge.** For a unit axis `n`, a Fubini–Study integral of any measurable function
of `blochProj n` equals the same integral with `blochProj n` replaced by the reference coordinate
`momentMap · 0`. The axis is moved to `e₀` by unitary invariance of `μ_FS`. -/
theorem blochProj_integral_bridge (n : EuclideanSpace ℂ (Fin 2)) (hn0 : n ≠ 0) (hn : ‖n‖ = 1)
    (p₀ : CPN 2) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ p, f (blochProj n p) ∂(fubiniStudyMeasure p₀)
      = ∫ p, f (momentMap p 0) ∂(fubiniStudyMeasure p₀) := by
  obtain ⟨U, hU⟩ := exists_unitary_moment_axis n hn0 hn
  have hinv := fubiniStudyMeasure_smul_invariant U p₀
  have hmap : ∫ p, f (blochProj n p)
        ∂(Measure.map (fun q : CPN 2 => U • q) (fubiniStudyMeasure p₀))
      = ∫ p, f (blochProj n (U • p)) ∂(fubiniStudyMeasure p₀) :=
    MeasureTheory.integral_map (continuous_const_smul U).measurable.aemeasurable
      (hf.comp (blochProj_measurable n)).aestronglyMeasurable
  calc ∫ p, f (blochProj n p) ∂(fubiniStudyMeasure p₀)
      = ∫ p, f (blochProj n p)
          ∂(Measure.map (fun q => U • q) (fubiniStudyMeasure p₀)) := by rw [hinv]
    _ = ∫ p, f (blochProj n (U • p)) ∂(fubiniStudyMeasure p₀) := hmap
    _ = ∫ p, f (momentMap p 0) ∂(fubiniStudyMeasure p₀) := by simp_rw [hU]

/-- **General-axis hat-box.** The Fubini–Study average of the Bloch height `|2·blochProj n − 1|`
along an arbitrary unit axis `n` is `½` — Archimedes' hat-box for any axis (via the bridge to the
reference-axis `hatBox_moment`). -/
theorem hatBox_axis (n : EuclideanSpace ℂ (Fin 2)) (hn0 : n ≠ 0) (hn : ‖n‖ = 1) (p₀ : CPN 2) :
    ∫ p, |2 * blochProj n p - 1| ∂(fubiniStudyMeasure p₀) = 1 / 2 := by
  rw [blochProj_integral_bridge n hn0 hn p₀ (f := fun t => |2 * t - 1|) (by fun_prop),
    hatBox_moment]

/-- **General-axis spread-density normalisation.** The CSD spread density `4·(2·blochProj n − 1)₊`
along an arbitrary unit axis `n` integrates to `1` against the Fubini–Study measure. -/
theorem spreadDensity_normalized_axis (n : EuclideanSpace ℂ (Fin 2)) (hn0 : n ≠ 0) (hn : ‖n‖ = 1)
    (p₀ : CPN 2) :
    ∫ p, 4 * max (2 * blochProj n p - 1) 0 ∂(fubiniStudyMeasure p₀) = 1 := by
  rw [blochProj_integral_bridge n hn0 hn p₀ (f := fun t => 4 * max (2 * t - 1) 0) (by fun_prop),
    spreadDensity_normalized]

end CSD.LF4
