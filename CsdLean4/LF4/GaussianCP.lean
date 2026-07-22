/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.GaussianFS
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# LF4 plan B, Part 1 (Option 2): `gaussianCP = fubiniStudyMeasure` via `ℝ⁴`

**Category:** 3-Local (`gaussianCP = fubiniStudyMeasure` via `ℝ⁴`).

Identifies the Fubini–Study measure on `ℂℙ¹` with the projectivized standard
Gaussian, working through a hand-built real coordinate isometry
`coords : ℝ⁴ ≃ₗᵢ[ℝ] ℂ²` to keep `stdGaussian` on the clean real space (avoiding
the ℝ/ℂ typeclass diamond on `EuclideanSpace ℂ (Fin 2)`). See
`specs/plan-b-detail.md` Part 1 (Option 2).
-/

open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **C1.** The real coordinate isometry `ℝ⁴ ≃ₗᵢ[ℝ] ℂ²`:
`y ↦ (y₀ + y₁·i, y₂ + y₃·i)`. -/
noncomputable def coords :
    EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun y := (WithLp.equiv 2 (Fin 2 → ℂ)).symm
    ![(y 0 : ℂ) + (y 1 : ℂ) * Complex.I, (y 2 : ℂ) + (y 3 : ℂ) * Complex.I]
  invFun z := (WithLp.equiv 2 (Fin 4 → ℝ)).symm
    ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  map_add' x y := by
    ext i
    fin_cases i <;>
      · simp only [WithLp.equiv_symm_apply, WithLp.ofLp_add, PiLp.toLp_apply, Pi.add_apply,
          Fin.isValue]
        push_cast
        ring
  map_smul' c x := by
    ext i
    fin_cases i <;>
      · simp only [WithLp.equiv_symm_apply, WithLp.ofLp_smul, PiLp.toLp_apply, Pi.smul_apply,
          Fin.isValue, RingHom.id_apply, smul_eq_mul]
        change _ = (c : ℂ) * _
        push_cast
        ring
  left_inv y := by
    ext i
    fin_cases i <;>
      simp [WithLp.equiv_symm_apply, PiLp.toLp_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
  right_inv z := by
    ext i
    fin_cases i <;>
      simp [WithLp.equiv_symm_apply, PiLp.toLp_apply]
  norm_map' y := by
    show ‖(WithLp.equiv 2 (Fin 2 → ℂ)).symm
        ![(y 0 : ℂ) + (y 1 : ℂ) * Complex.I, (y 2 : ℂ) + (y 3 : ℂ) * Complex.I]‖ = ‖y‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_four]
    simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.norm_eq_abs, sq_abs]
    ring_nf

/-- **C2.** The standard Gaussian transported to `ℂ²` via the coordinate
isometry. A probability measure on `ℂ²` (kept off the diamond-prone direct
`stdGaussian (EuclideanSpace ℂ (Fin 2))`). -/
noncomputable def gaussianH : Measure (EuclideanSpace ℂ (Fin 2)) :=
  Measure.map coords (stdGaussian (EuclideanSpace ℝ (Fin 4)))

instance instProbGaussianH : IsProbabilityMeasure gaussianH := by
  unfold gaussianH
  exact Measure.isProbabilityMeasure_map coords.continuous.measurable.aemeasurable

/-- The projectivization map `ℂ² → ℂℙ¹`, with junk value `p₀` at `0` (which is
`gaussianH`-null). -/
noncomputable def gaussianProj (p₀ : CPN 2) (v : EuclideanSpace ℂ (Fin 2)) : CPN 2 :=
  if h : v = 0 then p₀ else Projectivization.mk ℂ v h

lemma measurable_gaussianProj (p₀ : CPN 2) : Measurable (gaussianProj p₀) := by
  refine measurable_of_measurable_on_compl_singleton 0 ?_
  -- On `{v | v ≠ 0}`, `gaussianProj p₀` agrees with `mk' ℂ` (no junk).
  have hrestr : {v : EuclideanSpace ℂ (Fin 2) | v ≠ 0}.domRestrict (gaussianProj p₀)
      = fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext v
    simp only [Set.domRestrict_apply, gaussianProj, dif_neg v.2,
      Projectivization.mk'_eq_mk]
  rw [hrestr]
  exact Projectivization.measurable_mk'.comp
    (measurable_subtype_coe.subtype_mk)

/-- **C3.** The projectivized Gaussian on `ℂℙ¹`. -/
noncomputable def gaussianCP (p₀ : CPN 2) : Measure (CPN 2) :=
  Measure.map (gaussianProj p₀) gaussianH

instance instProbGaussianCP (p₀ : CPN 2) : IsProbabilityMeasure (gaussianCP p₀) := by
  unfold gaussianCP
  exact Measure.isProbabilityMeasure_map (measurable_gaussianProj p₀).aemeasurable

/-! ### C4 — `U(2)`-invariance of `gaussianCP` -/

/-- The `ℂ`-linear matrix action `toEuclideanLin U.val` is measurable
(continuous on a finite-dimensional space). -/
lemma measurable_toEuclideanLin (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Measurable (Matrix.toEuclideanLin U.val) :=
  (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin U.val)).measurable

/-- A unitary's `toEuclideanLin` action sends nonzero vectors to nonzero
vectors (norm is preserved, via `unitary_norm_preserving`). -/
lemma toEuclideanLin_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ)
    {v : EuclideanSpace ℂ (Fin 2)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  have hnorm : ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := unitary_norm_preserving U v
  rw [h, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm.symm

/-- `Uᴴ * U = 1` for a unitary matrix. -/
lemma unitary_conjTranspose_mul (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    U.valᴴ * U.val = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `U * Uᴴ = 1` for a unitary matrix. -/
lemma unitary_mul_conjTranspose (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    U.val * U.valᴴ = 1 := by
  have h := U.2
  rw [Matrix.mem_unitaryGroup_iff] at h
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `toEuclideanLin U.val` is `ℝ`-linear for the scalar action (it is
`ℂ`-linear, and the `ℝ`-action commutes with `mulVec` componentwise). -/
lemma toEuclideanLin_real_smul (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (c : ℝ) (w : EuclideanSpace ℂ (Fin 2)) :
    (Matrix.toEuclideanLin U.val) (c • w) = c • (Matrix.toEuclideanLin U.val) w := by
  apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
  simp only [WithLp.equiv_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul]
  exact Matrix.mulVec_smul _ _ _

/-- The real conjugate isometry `conjR U : ℝ⁴ ≃ₗᵢ[ℝ] ℝ⁴`, conjugating the
unitary action `toEuclideanLin U.val` on `ℂ²` through the coordinate isometry
`coords`. Built by hand on `ℝ⁴` (the `restrictScalars ℝ` route diamonds in the
full LF4 import context — see `specs/plan-b-detail.md`). -/
noncomputable def conjR (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun y := coords.symm ((Matrix.toEuclideanLin U.val) (coords y))
  invFun z := coords.symm ((Matrix.toEuclideanLin U.valᴴ) (coords z))
  map_add' x y := by
    simp only [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, map_smul, toEuclideanLin_real_smul]
  left_inv y := by
    show coords.symm ((Matrix.toEuclideanLin U.valᴴ)
        (coords (coords.symm ((Matrix.toEuclideanLin U.val) (coords y))))) = y
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coords y]
    apply congrArg coords.symm
    apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_conjTranspose_mul, Matrix.one_mulVec]
  right_inv z := by
    show coords.symm ((Matrix.toEuclideanLin U.val)
        (coords (coords.symm ((Matrix.toEuclideanLin U.valᴴ) (coords z))))) = z
    rw [LinearIsometryEquiv.apply_symm_apply]
    rw [← LinearIsometryEquiv.symm_apply_apply coords z]
    apply congrArg coords.symm
    apply (WithLp.equiv 2 (Fin 2 → ℂ)).injective
    simp only [WithLp.equiv_apply, LinearIsometryEquiv.apply_symm_apply,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, unitary_mul_conjTranspose, Matrix.one_mulVec]
  norm_map' y := by
    show ‖coords.symm ((Matrix.toEuclideanLin U.val) (coords y))‖ = ‖y‖
    rw [LinearIsometryEquiv.norm_map, unitary_norm_preserving, LinearIsometryEquiv.norm_map]

/-- `coords ∘ conjR U = toEuclideanLin U.val ∘ coords` pointwise. -/
lemma coords_conjR (U : Matrix.unitaryGroup (Fin 2) ℂ) (y : EuclideanSpace ℝ (Fin 4)) :
    coords (conjR U y) = (Matrix.toEuclideanLin U.val) (coords y) := by
  show coords (coords.symm ((Matrix.toEuclideanLin U.val) (coords y))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- `gaussianH` is invariant under the unitary matrix action on `ℂ²`. -/
lemma gaussianH_map_unitary (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Measure.map (Matrix.toEuclideanLin U.val) gaussianH = gaussianH := by
  unfold gaussianH
  rw [Measure.map_map (measurable_toEuclideanLin U) coords.continuous.measurable]
  have hcomp : (Matrix.toEuclideanLin U.val) ∘ coords = coords ∘ (conjR U) := by
    funext y
    simp only [Function.comp_apply, coords_conjR]
  rw [hcomp, ← Measure.map_map coords.continuous.measurable (conjR U).continuous.measurable,
    stdGaussian_map (conjR U)]

/-- `stdGaussian (EuclideanSpace ℝ (Fin 4))` is not a Dirac measure: it has a
dual direction (`innerSL` against a unit coordinate vector) with variance
`1 ≠ 0`. -/
lemma stdGaussian_ne_dirac (x : EuclideanSpace ℝ (Fin 4)) :
    stdGaussian (EuclideanSpace ℝ (Fin 4)) ≠ Measure.dirac x := by
  intro hx
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin 4)) :=
    innerSL ℝ (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) with hLdef
  have hLnorm : ‖L‖ = 1 := by
    rw [hLdef, innerSL_apply_norm, PiLp.norm_single, norm_one]
  have hvar : Var[L; stdGaussian (EuclideanSpace ℝ (Fin 4))] = 1 := by
    rw [variance_dual_stdGaussian, hLnorm, one_pow]
  rw [hx, ProbabilityTheory.variance_dirac] at hvar
  exact zero_ne_one hvar

instance instNoAtomsStdGaussian4 : NullSingletonClass (stdGaussian (EuclideanSpace ℝ (Fin 4))) :=
  ProbabilityTheory.IsGaussian.nullSingletonClass stdGaussian_ne_dirac

/-- The origin is `gaussianH`-null (the junk value of `gaussianProj` at `0` is
therefore irrelevant a.e.). -/
lemma gaussianH_singleton_zero :
    gaussianH {(0 : EuclideanSpace ℂ (Fin 2))} = 0 := by
  unfold gaussianH
  rw [Measure.map_apply coords.continuous.measurable (measurableSet_singleton 0)]
  have : (coords ⁻¹' {(0 : EuclideanSpace ℂ (Fin 2))})
      = {(0 : EuclideanSpace ℝ (Fin 4))} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, map_eq_zero_iff coords coords.injective]
  rw [this, measure_singleton]

/-! ### C4 (invariance) and C5 (identification) -/

/-- **C4.** `gaussianCP p₀` is `U(2)`-invariant. -/
lemma gaussianCP_smul_invariant (p₀ : CPN 2) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Measure.map (fun p => U • p) (gaussianCP p₀) = gaussianCP p₀ := by
  unfold gaussianCP
  rw [Measure.map_map (continuous_const_smul U).measurable (measurable_gaussianProj p₀)]
  -- The two maps agree off `{0}` (a `gaussianH`-null set).
  have hae : ((fun p => U • p) ∘ gaussianProj p₀)
      =ᵐ[gaussianH] (gaussianProj p₀ ∘ (Matrix.toEuclideanLin U.val)) := by
    refine ae_iff.mpr ?_
    refine measure_mono_null ?_ gaussianH_singleton_zero
    intro v hv
    simp only [Set.mem_ofPred_eq, Function.comp_apply] at hv
    by_contra hv0
    simp only [Set.mem_singleton_iff] at hv0
    apply hv
    rw [gaussianProj, dif_neg hv0, gaussianProj,
      dif_neg (toEuclideanLin_ne_zero U hv0), smul_mk_eq_mk U v hv0]
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_gaussianProj p₀) (measurable_toEuclideanLin U),
    gaussianH_map_unitary U]

/-- **C5.** The projectivized Gaussian equals the Fubini–Study measure. -/
lemma gaussianCP_eq_fubiniStudy (p₀ : CPN 2) :
    gaussianCP p₀ = fubiniStudyMeasure p₀ :=
  fubiniStudyMeasure_unique p₀ (gaussianCP p₀) (gaussianCP_smul_invariant p₀)

end LF4
end CSD
