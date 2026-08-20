/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.QubitDipole
public import CsdLean4.Empirical.CSD.UncertaintyVolume
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
-- Direct import of `Measurable.abs`'s provider (`to_additive` from `Measurable.mabs`).
-- The 2026-08-17 forward-compat canary failed here: the name arrived only transitively
-- through the pinned Mathlib's import closure, and Mathlib master's import trimming
-- dropped the path. A name a proof uses gets its providing module imported directly.
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# LF4/QubitCrossTerm: the cross-term vanishes (context-fixed qubit, A7)

**Category:** 2-LF4 (Kähler / moment-map layer — qubit context-fixed measurement).

The **cross-term** `T = ∫ rsign(2·blochProj n − 1)·|2·blochProj ψ − 1| dμ_FS = 0` — the vanishing of
the monopole–hemisphere correlation. The **antipode symmetry**: pushing the Haar integral by
right-multiplication `U ↦ U·W` (where `W` sends `[e₀]` to the orthogonal `[e₁]`) flips both
coordinates `u ↦ 1−u`, `s ↦ 1−s` via the orthonormal-complement Parseval flip
(`inner_unitary_flip`), so the integrand negates and `T = −T`.

Foundational-triple, no `sorry`.

## References
`LF4/QubitDipole.lean` (`rsign`, `blochProj_le_one`); `Empirical/CSD/UncertaintyVolume.lean`
(`context_vol_sum_two`); `Mathlib/.../FubiniStudyUnique.lean` (Haar right-invariance,
`fubiniStudyMeasure_unique`); `specs/record-layer-plan.md` §2 (the qubit context-fixed crux).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- The image of the standard basis of `ℂ²` under a unitary, packaged as an `OrthonormalBasis`
(orthonormal since `U` is an isometry; spans since cardinality = dimension). -/
noncomputable def unitaryONB (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) := by
  have horth : Orthonormal ℂ
      (fun i : Fin 2 => Matrix.toEuclideanLin U.val (EuclideanSpace.single i (1 : ℂ))) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Projectivization.inner_toEuclideanLin_unitary, EuclideanSpace.inner_single_left,
      map_one, one_mul]
    simp [PiLp.single_apply]
  refine OrthonormalBasis.mk horth ?_
  have hcard : Fintype.card (Fin 2) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [horth.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

@[simp] lemma unitaryONB_apply (U : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    unitaryONB U i = Matrix.toEuclideanLin U.val (EuclideanSpace.single i (1 : ℂ)) := by
  rw [unitaryONB, OrthonormalBasis.coe_mk]

/-- **Orthonormal-complement flip.** For a unit axis `a` and a unitary `U`, the Born weights along
the two image-basis directions sum to one: `|⟨a, U e₀⟩|² + |⟨a, U e₁⟩|² = 1`. Parseval over the
orthonormal basis `unitaryONB U`. -/
lemma inner_unitary_flip (a : EuclideanSpace ℂ (Fin 2)) (ha : ‖a‖ = 1)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖inner ℂ a (Matrix.toEuclideanLin U.val (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))‖ ^ 2
      + ‖inner ℂ a (Matrix.toEuclideanLin U.val (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))‖ ^ 2
      = 1 := by
  have h := CSD.Empirical.CSDBridge.UncertaintyVolume.context_vol_sum_two (unitaryONB U) a ha
  simp only [unitaryONB_apply] at h
  rw [norm_inner_comm a (Matrix.toEuclideanLin U.val (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))),
    norm_inner_comm a (Matrix.toEuclideanLin U.val (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))]
  exact h


/-- `rsign` is odd: `rsign (−x) = − rsign x`. -/
lemma rsign_neg (x : ℝ) : rsign (-x) = - rsign x := by
  unfold rsign
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos (by linarith : (0:ℝ) < -x), if_neg (by linarith : ¬ (0:ℝ) < x), if_pos h]; ring
  · subst h; simp
  · rw [if_neg (by linarith : ¬ (0:ℝ) < -x), if_pos (by linarith : -x < 0), if_pos h]

/-- The Fubini–Study measure is independent of the base point (uniqueness of the invariant law). -/
lemma fubiniStudy_eq (p₀ p₁ : CPN 2) : fubiniStudyMeasure p₀ = fubiniStudyMeasure p₁ :=
  fubiniStudyMeasure_unique p₁ (fubiniStudyMeasure p₀)
    (fun U => fubiniStudyMeasure_smul_invariant U p₀)

/-- The `e₀ ↔ e₁` swap matrix (Pauli-X). -/
noncomputable def swapMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma swapMat_mem : swapMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- The swap unitary as a group element. -/
noncomputable def swapU : Matrix.unitaryGroup (Fin 2) ℂ := ⟨swapMat, swapMat_mem⟩

lemma single_zero_ne : (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ≠ 0 := by
  intro h
  have : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 0 := by rw [h, norm_zero]
  rw [PiLp.norm_single, norm_one] at this; exact one_ne_zero this

lemma single_one_ne : (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) ≠ 0 := by
  intro h
  have : ‖EuclideanSpace.single (1 : Fin 2) (1 : ℂ)‖ = 0 := by rw [h, norm_zero]
  rw [PiLp.norm_single, norm_one] at this; exact one_ne_zero this

/-- The swap sends `e₀` to `e₁`. -/
lemma toEuclideanLin_swapMat_e0 :
    Matrix.toEuclideanLin swapMat (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      = EuclideanSpace.single (1 : Fin 2) (1 : ℂ) := by
  apply WithLp.ofLp_injective
  funext i
  rw [show (Matrix.toEuclideanLin swapMat (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))).ofLp i
        = Matrix.mulVec swapMat (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).ofLp i from rfl]
  fin_cases i <;>
    simp [swapMat, Matrix.mulVec, dotProduct, PiLp.single_apply]

/-- `swapU • [e₀] = [e₁]`. -/
lemma swapU_smul_e0 :
    swapU • Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne
      = Projectivization.mk ℂ (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) single_one_ne := by
  rw [Matrix.UnitaryGroup.smul_mk_eq_mk swapU _ single_zero_ne]
  exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ single_one_ne).mpr
    ⟨1, by rw [one_smul]; exact toEuclideanLin_swapMat_e0.symm⟩

/-- The Bloch projection at `U • [eᵢ]` is `|⟨a, U eᵢ⟩|²`. -/
lemma blochProj_smul_single (a : EuclideanSpace ℂ (Fin 2)) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (i : Fin 2) (hi : EuclideanSpace.single i (1 : ℂ) ≠ 0) :
    blochProj a (U • Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ)) hi)
      = ‖inner ℂ a (Matrix.toEuclideanLin U.val (EuclideanSpace.single i (1 : ℂ)))‖ ^ 2 := by
  rw [Matrix.UnitaryGroup.smul_mk_eq_mk U _ hi, blochProj_mk, toEuclideanLin_unitary_norm,
    PiLp.norm_single, norm_one, one_pow, div_one]

/-- Haar right-invariance in integral form. -/
lemma haar_integral_mul_right (h : Matrix.unitaryGroup (Fin 2) ℂ → ℝ) (hh : Measurable h)
    (W : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∫ U, h U ∂unitaryHaarProb = ∫ U, h (U * W) ∂unitaryHaarProb := by
  conv_lhs => rw [← MeasureTheory.map_mul_right_eq_self unitaryHaarProb W]
  exact MeasureTheory.integral_map (measurable_mul_const W).aemeasurable hh.aestronglyMeasurable

/-- **The cross-term vanishes.** `T = ∫ rsign(2·blochProj n − 1)·|2·blochProj ψ − 1| dμ_FS = 0`,
for unit `n, ψ`. The antipode symmetry: Haar right-multiplication by the swap flips both Born
coordinates (`inner_unitary_flip`), negating the integrand, so `T = −T`. -/
theorem crossTerm (n ψ : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (hψ : ‖ψ‖ = 1) (p₀ : CPN 2) :
    ∫ p, rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1| ∂(fubiniStudyMeasure p₀) = 0 := by
  set e0pt := Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne
    with he0pt
  rw [fubiniStudy_eq p₀ e0pt]
  set G : CPN 2 → ℝ :=
    fun p => rsign (2 * blochProj n p - 1) * |2 * blochProj ψ p - 1| with hG
  have hGmeas : Measurable G :=
    (measurable_rsign.comp (((blochProj_measurable n).const_mul 2).sub_const 1)).mul
      ((((blochProj_measurable ψ).const_mul 2).sub_const 1).abs)
  have hmap : ∫ p, G p ∂(fubiniStudyMeasure e0pt)
      = ∫ U : Matrix.unitaryGroup (Fin 2) ℂ, G (U • e0pt) ∂unitaryHaarProb := by
    rw [fubiniStudyMeasure]
    exact MeasureTheory.integral_map (orbit_map_measurable e0pt).aemeasurable
      hGmeas.aestronglyMeasurable
  rw [hmap]
  set h : Matrix.unitaryGroup (Fin 2) ℂ → ℝ := fun U => G (U • e0pt) with hh
  have hhmeas : Measurable h := hGmeas.comp (orbit_map_measurable e0pt)
  have hflip : ∀ U, h (U * swapU) = - h U := by
    intro U
    have hstep : (U * swapU) • e0pt = U • Projectivization.mk ℂ
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) single_one_ne := by
      rw [mul_smul, he0pt, swapU_smul_e0]
    have hfn : blochProj n (U • Projectivization.mk ℂ
          (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) single_one_ne)
        = 1 - blochProj n (U • Projectivization.mk ℂ
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne) := by
      rw [blochProj_smul_single n U 1 single_one_ne, blochProj_smul_single n U 0 single_zero_ne]
      linarith [inner_unitary_flip n hn U]
    have hfψ : blochProj ψ (U • Projectivization.mk ℂ
          (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) single_one_ne)
        = 1 - blochProj ψ (U • Projectivization.mk ℂ
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne) := by
      rw [blochProj_smul_single ψ U 1 single_one_ne, blochProj_smul_single ψ U 0 single_zero_ne]
      linarith [inner_unitary_flip ψ hψ U]
    simp only [hh, hG]
    rw [hstep, he0pt, hfn, hfψ]
    set u := blochProj n (U • Projectivization.mk ℂ
      (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne)
    set s := blochProj ψ (U • Projectivization.mk ℂ
      (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_ne)
    rw [show 2 * (1 - u) - 1 = -(2 * u - 1) by ring, show 2 * (1 - s) - 1 = -(2 * s - 1) by ring,
      rsign_neg, abs_neg]
    ring
  have hright : ∫ U, h U ∂unitaryHaarProb = ∫ U, h (U * swapU) ∂unitaryHaarProb :=
    haar_integral_mul_right h hhmeas swapU
  have hT : (∫ U, h U ∂unitaryHaarProb) = - ∫ U, h U ∂unitaryHaarProb := by
    conv_lhs => rw [hright]
    simp_rw [hflip]
    exact integral_neg h
  linarith [hT]

end CSD.LF4
