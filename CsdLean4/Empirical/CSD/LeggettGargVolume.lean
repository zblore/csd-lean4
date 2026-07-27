/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.LeggettGarg
public import CsdLean4.LF4.MomentUniform

/-!
# Empirical/CSD: the Leggett–Garg two-time survival probability as a Kähler typicality volume

**Category:** 3-Local (CSD-ontic layer).

The CSD twin of [`Empirical/QM/LeggettGarg.lean`]. The Leggett–Garg two-time correlation
`⟨Q(0)Q(Δ)⟩ = cos(2Δ)` is built (with intermediate collapse) from the qubit *survival probability*
`P(0→0) = cos²Δ = |⟨0, e^{-iΔσ_x}|0⟩⟩|²`. Here that Born weight is realised as a **Fubini–Study
typicality volume** on the ontic `Σ = ℂℙ¹`: for the precessed state `|Δ⟩ = cos Δ|0⟩ − i sin Δ|1⟩`,

  `μ_FS { [φ] : Φ₀([φ]) ≤ Φ₀([|Δ⟩]) } = cos²Δ`,

with `volume = Born` *computed* via the Duistermaat–Heckman theorem `fs_moment_pushforward_uniform`
(carving-free, `busch_effect_gleason`-free). So the LG transition statistics are ontic typicality
volumes, not a Born postulate.

## References
`Empirical/QM/LeggettGarg.lean` (`lgCorr_eq`); `LF4/MomentUniform.lean`
(`fs_born_volume_ratio_qubit_uncond`); `Empirical/CSD/MalusVolume.lean` (the same volume-frequency
pattern for the Malus law).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.CSDBridge.LeggettGargVolume

/-- The precessed qubit state `|Δ⟩ = e^{-iΔσ_x}|0⟩ = cos Δ|0⟩ − i sin Δ|1⟩`. -/
noncomputable def lgState (Δ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos Δ : ℂ), -(Complex.I * (Real.sin Δ : ℂ))]

@[simp] lemma lgState_zero (Δ : ℝ) : lgState Δ 0 = (Real.cos Δ : ℂ) := by
  simp [lgState, WithLp.ofLp_toLp]

@[simp] lemma lgState_one (Δ : ℝ) : lgState Δ 1 = -(Complex.I * (Real.sin Δ : ℂ)) := by
  simp [lgState, WithLp.ofLp_toLp]

lemma lgState_normsq (Δ : ℝ) : ∑ i, ‖lgState Δ i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_two, lgState_zero, lgState_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_neg, norm_mul, Complex.norm_I,
    one_mul]
  rw [add_comm]; exact Real.sin_sq_add_cos_sq Δ

lemma lgState_ne (Δ : ℝ) : lgState Δ ≠ 0 := by
  intro h; have hn := lgState_normsq Δ; rw [h] at hn; simp at hn

lemma lgState_norm (Δ : ℝ) : ‖lgState Δ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, lgState_normsq, Real.sqrt_one]

lemma lgState_born0 (Δ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (lgState Δ)‖ ^ 2 = Real.cos Δ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, lgState_zero, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- **The Leggett–Garg survival probability `cos²Δ` is a Fubini–Study typicality volume.** The
`P(0→0) = cos²Δ` transition weight of the two-time correlation equals the FS volume of the
moment-sublevel region cut by the precessed state `[|Δ⟩]` on the ontic `ℂℙ¹` — Born as Kähler
volume, via Duistermaat–Heckman. -/
theorem lg_survival_as_volume (Δ : ℝ) (p₀ : CPN 2) :
    fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ (lgState Δ) (lgState_ne Δ)) 0}
      = ENNReal.ofReal (Real.cos Δ ^ 2) := by
  rw [fs_born_volume_ratio_qubit_uncond p₀ (lgState Δ) (lgState_ne Δ) (lgState_norm Δ),
    lgState_born0]

end CSD.Empirical.CSDBridge.LeggettGargVolume
