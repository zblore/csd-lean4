/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.ElitzurVaidman
public import CsdLean4.LF4.MomentUniform

/-!
# Empirical/CSD: the Elitzur–Vaidman split probability as a Kähler typicality volume

**Category:** 3-Local (CSD-ontic layer).

The CSD twin of [`Empirical/QM/ElitzurVaidman.lean`]. In the bomb tester, after the first beam
splitter the photon is in `H|0⟩ = (|0⟩+|1⟩)/√2`, and the `1/2` weights (`survive`, and the
conditioned dark-port) are the Born weights `|⟨e, H|0⟩⟩|² = 1/2`. Here that `1/2` is realised as a
**Fubini–Study typicality volume** on the ontic `Σ = ℂℙ¹`: for the beam-splitter state
`|+⟩ = (|0⟩+|1⟩)/√2`,

  `μ_FS { [φ] : Φ₀([φ]) ≤ Φ₀([|+⟩]) } = 1/2`,

with `volume = Born` *computed* via Duistermaat–Heckman (carving-free, `busch_effect_gleason`-free).
So the interaction-free-measurement branch weights are ontic typicality volumes.

## References
`Empirical/QM/ElitzurVaidman.lean` (`bomb_safe_prob`); `LF4/MomentUniform.lean`
(`fs_born_volume_ratio_qubit_uncond`); `Empirical/CSD/MachZehnderVolume.lean` (the interferometer as
a Kähler volume).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD.Empirical.CSDBridge.ElitzurVaidmanVolume

/-- The beam-splitter state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def bsState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)]

@[simp] lemma bsState_zero : bsState 0 = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bsState, WithLp.ofLp_toLp]

@[simp] lemma bsState_one : bsState 1 = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bsState, WithLp.ofLp_toLp]

lemma norm_inv_sqrt2_sq : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma bsState_normsq : ∑ i, ‖bsState i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_two, bsState_zero, bsState_one, norm_inv_sqrt2_sq]; norm_num

lemma bsState_ne : bsState ≠ 0 := by
  intro h; have hn := bsState_normsq; rw [h] at hn; simp at hn

lemma bsState_norm : ‖bsState‖ = 1 := by
  rw [EuclideanSpace.norm_eq, bsState_normsq, Real.sqrt_one]

lemma bsState_born0 : ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) bsState‖ ^ 2 = 1 / 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, bsState_zero, norm_inv_sqrt2_sq]

/-- **The Elitzur–Vaidman `1/2` split probability is a Fubini–Study typicality volume.** The beam
splitter's Born weight `1/2` (the survival / conditioned-dark-port weight) equals the FS volume of
the moment-sublevel region cut by `[|+⟩]` on the ontic `ℂℙ¹` — Born as Kähler volume, via
Duistermaat–Heckman. -/
theorem ev_split_as_volume (p₀ : CPN 2) :
    fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ bsState bsState_ne) 0}
      = ENNReal.ofReal (1 / 2) := by
  rw [fs_born_volume_ratio_qubit_uncond p₀ bsState bsState_ne bsState_norm, bsState_born0]

end CSD.Empirical.CSDBridge.ElitzurVaidmanVolume
