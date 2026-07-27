/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.AxisBridge
public import CsdLean4.LF4.QubitReflection
public import CsdLean4.LF2.BornWrapper

/-!
# LF4/QubitDipole: the dipole correlation for the context-fixed qubit (A7)

**Category:** 2-LF4 (Kähler / moment-map layer — qubit context-fixed measurement).

The **reflection `R_n = 2|n⟩⟨n| − I`** as a genuine unitary matrix (Hermitian involution), and the
resulting **dipole correlation**

  `D = ∫ sign(2·blochProj n − 1)·(2·blochProj ψ − 1) dμ_FS = (2c − 1)/2`,   `c = |⟨n|ψ⟩|²`.

Mechanism: `R_n` is a Hermitian unitary (`R_n² = I`, `outerProduct_mul_self_of_unit_norm`), so its
`ℂℙ¹`-action preserves `μ_FS` (`fubiniStudyMeasure_smul_invariant`) and fixes the `n`-coordinate.
Reflecting the density and averaging, `reflect_sq_add` (the `ℂ²` reflection identity) linearises
`2(s + s′) − 2 = 2(2c − 1)(2u − 1)`, and the general-axis hat-box `hatBox_axis` (`∫|2u − 1| = ½`)
closes it. Foundational-triple, no `sorry`.

## References
`LF4/QubitReflection.lean` (`reflect_sq_add`); `LF4/AxisBridge.lean` (`hatBox_axis`);
`LF2/BornWrapper.lean` (`outerProduct`, `outerProduct_mul_self_of_unit_norm`);
`specs/record-layer-plan.md` §2 (the qubit context-fixed crux, dipole term).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup CSD.LF2
open scoped LinearAlgebra.Projectivization

namespace CSD.LF4

/-- **The reflection matrix `R_n = 2|n⟩⟨n| − I`.** -/
noncomputable def reflMat (n : EuclideanSpace ℂ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ) • outerProduct n - 1

/-- `R_n` is Hermitian: `(2P − I)ᴴ = 2P − I` since `P = |n⟩⟨n|` is Hermitian and `star 2 = 2`. -/
lemma reflMat_conjTranspose (n : EuclideanSpace ℂ (Fin 2)) :
    (reflMat n).conjTranspose = reflMat n := by
  unfold reflMat
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    (outerProduct_isHermitian n)]
  norm_num

/-- `R_n` is an involution for a unit axis: `R_n · R_n = I`. Ring calculation
`(2P − I)² = 4P² − 4P + I = I` using idempotence `P² = P`. -/
lemma reflMat_mul_self (n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) :
    reflMat n * reflMat n = 1 := by
  have hP : outerProduct n * outerProduct n = outerProduct n :=
    outerProduct_mul_self_of_unit_norm n hn
  unfold reflMat
  rw [sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hP,
    one_mul, mul_one, smul_smul]
  norm_num
  module

/-- `R_n` lies in the unitary group (Hermitian involution ⇒ `star R_n · R_n = R_n² = I`). -/
lemma reflMat_mem_unitaryGroup (n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) :
    reflMat n ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, reflMat_conjTranspose]
  exact reflMat_mul_self n hn

/-- The reflection unitary `R_n` as an element of the unitary group. -/
noncomputable def reflU (n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) :
    Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨reflMat n, reflMat_mem_unitaryGroup n hn⟩

/-- The outer product `|n⟩⟨n|` acts as `w ↦ ⟨n,w⟩ • n`. Proved coordinatewise. -/
lemma toEuclideanLin_outerProduct (n w : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanLin (outerProduct n) w = (inner ℂ n w) • n := by
  apply WithLp.ofLp_injective
  funext i
  have hL : (Matrix.toEuclideanLin (outerProduct n) w).ofLp i
      = (outerProduct n) i 0 * w.ofLp 0 + (outerProduct n) i 1 * w.ofLp 1 := by
    rw [show (Matrix.toEuclideanLin (outerProduct n) w).ofLp i
          = ∑ j, (outerProduct n) i j * w.ofLp j from rfl, Fin.sum_univ_two]
  have hR : ((inner ℂ n w) • n).ofLp i = inner ℂ n w * n.ofLp i := rfl
  have hI : (inner ℂ n w : ℂ)
      = star (n.ofLp 0) * w.ofLp 0 + star (n.ofLp 1) * w.ofLp 1 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Fin.sum_univ_two]
    ring
  rw [hL, hR, hI]
  simp only [outerProduct, Matrix.vecMulVec_apply]
  fin_cases i <;> · simp only [Fin.isValue]; ring

/-- **`R_n` acts as the reflection map:** `toEuclideanLin R_n w = (2⟨n,w⟩)•n − w`, i.e.
`R_n = 2|n⟩⟨n| − I`. Follows from linearity of `toEuclideanLin` and `toEuclideanLin_outerProduct`. -/
lemma reflMat_toEuclideanLin (n w : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanLin (reflMat n) w = (2 * inner ℂ n w) • n - w := by
  unfold reflMat
  have h1 : (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ)) w = w := by
    apply WithLp.ofLp_injective; funext i
    rw [show (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ) w).ofLp i
          = Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℂ) w.ofLp i from rfl, Matrix.one_mulVec]
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, toEuclideanLin_outerProduct,
    h1, smul_smul]

/-- The Bloch projection along axis `a` after reflecting by `R_n`:
`blochProj a (R_n•p) = |⟨a, (2⟨n,rep⟩)•n − rep⟩|² / ‖rep‖²`. -/
lemma blochProj_reflU (a n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (p : CPN 2) :
    blochProj a (reflU n hn • p)
      = ‖inner ℂ a ((2 * inner ℂ n p.rep) • n - p.rep)‖ ^ 2 / ‖p.rep‖ ^ 2 := by
  rw [blochProj_smul, show (reflU n hn).val = reflMat n from rfl, reflMat_toEuclideanLin]

/-- **The reflection fixes the `n`-coordinate:** `blochProj n (R_n•p) = blochProj n p`. Since
`R_n n = n`, we have `⟨n, R_n φ⟩ = ⟨n, φ⟩`. -/
lemma blochProj_refl_fixes (n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (p : CPN 2) :
    blochProj n (reflU n hn • p) = blochProj n p := by
  have hval : (inner ℂ n ((2 * inner ℂ n p.rep) • n - p.rep) : ℂ) = inner ℂ n p.rep := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
    push_cast; ring
  rw [blochProj_reflU, hval]
  rfl

/-- Cauchy–Schwarz bound: `blochProj a p ≤ 1` for a unit axis `a`. -/
lemma blochProj_le_one (a : EuclideanSpace ℂ (Fin 2)) (ha : ‖a‖ = 1) (p : CPN 2) :
    blochProj a p ≤ 1 := by
  have hpos : (0 : ℝ) < ‖p.rep‖ ^ 2 := pow_pos (norm_pos_iff.mpr p.rep_nonzero) 2
  unfold blochProj
  rw [div_le_one hpos]
  have h := norm_inner_le_norm (𝕜 := ℂ) a p.rep
  rw [ha, one_mul] at h
  nlinarith [norm_nonneg (inner ℂ a p.rep : ℂ), norm_nonneg p.rep, h]

/-- **The reflection sum identity (projective form).** For unit `n, ψ`, the sum of the Born weight of
`ψ` and its `R_n`-reflection is a linear function of the `n`-coordinate:
`blochProj ψ p + blochProj ψ (R_n•p) = 2c·u + 2(1−c)(1−u)`, `c = |⟨n,ψ⟩|²`, `u = blochProj n p`.
The projective lift of `reflect_sq_add`, via a unit representative of `p`. -/
lemma reflSum (n ψ : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (hψ : ‖ψ‖ = 1) (p : CPN 2) :
    blochProj ψ p + blochProj ψ (reflU n hn • p)
      = 2 * (‖inner ℂ n ψ‖ ^ 2 * blochProj n p)
        + 2 * ((1 - ‖inner ℂ n ψ‖ ^ 2) * (1 - blochProj n p)) := by
  have hpr0 : p.rep ≠ 0 := p.rep_nonzero
  have hnorm0 : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr hpr0
  set φ : EuclideanSpace ℂ (Fin 2) := ((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep with hφdef
  have hc0 : ((‖p.rep‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]; exact hnorm0
  have hφ0 : φ ≠ 0 := smul_ne_zero hc0 hpr0
  have hφ1 : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), inv_mul_cancel₀ hnorm0]
  have hmkφ : Projectivization.mk ℂ φ hφ0 = p := by
    have hstep : Projectivization.mk ℂ φ hφ0 = Projectivization.mk ℂ p.rep hpr0 :=
      (Projectivization.mk_eq_mk_iff ℂ φ p.rep hφ0 hpr0).mpr
        ⟨Units.mk0 _ hc0, by rw [Units.smul_def, Units.val_mk0]⟩
    rw [hstep]; exact Projectivization.mk_rep p
  have e1 : blochProj ψ p = ‖inner ℂ ψ φ‖ ^ 2 := by
    rw [← hmkφ, blochProj_mk_unit ψ φ hφ0 hφ1]
  have e2 : blochProj n p = ‖inner ℂ n φ‖ ^ 2 := by
    rw [← hmkφ, blochProj_mk_unit n φ hφ0 hφ1]
  have e3 : blochProj ψ (reflU n hn • p) = ‖inner ℂ ψ ((2 * inner ℂ n φ) • n - φ)‖ ^ 2 := by
    rw [← hmkφ, smul_mk_eq_mk (reflU n hn) φ hφ0, blochProj_mk]
    show ‖inner ℂ ψ (Matrix.toEuclideanLin (reflMat n) φ)‖ ^ 2
        / ‖Matrix.toEuclideanLin (reflMat n) φ‖ ^ 2
      = ‖inner ℂ ψ ((2 * inner ℂ n φ) • n - φ)‖ ^ 2
    rw [show ‖Matrix.toEuclideanLin (reflMat n) φ‖ = ‖φ‖
          from toEuclideanLin_unitary_norm (reflU n hn) φ,
      hφ1, one_pow, div_one, reflMat_toEuclideanLin]
  rw [e1, e2, e3]
  linarith [reflect_sq_add n ψ φ hn hψ hφ1]

/-- Real-valued sign function `rsign x ∈ {−1,0,1}`. -/
noncomputable def rsign (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

/-- `rsign x * x = |x|`. -/
lemma rsign_mul_self (x : ℝ) : rsign x * x = |x| := by
  unfold rsign
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h, abs_of_neg h]; ring
  · subst h; simp
  · rw [if_pos h, abs_of_pos h]; ring

/-- `|rsign x| ≤ 1`. -/
lemma abs_rsign_le_one (x : ℝ) : |rsign x| ≤ 1 := by
  unfold rsign
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; norm_num
  · subst h; norm_num
  · rw [if_pos h]; norm_num

/-- `rsign` is measurable. -/
lemma measurable_rsign : Measurable rsign := by
  unfold rsign
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-- **The dipole correlation for the context-fixed qubit.** For unit `n, ψ`,
`∫ rsign(2·blochProj n − 1)·(2·blochProj ψ − 1) dμ_FS = (2c − 1)/2`, `c = |⟨n,ψ⟩|²`. The `R_n`
reflection (`μ_FS`-preserving, fixes the `n`-coordinate) plus `reflect_sq_add` linearises the paired
density, and the general-axis hat-box (`hatBox_axis`) closes it. -/
theorem dipole (n ψ : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (hψ : ‖ψ‖ = 1) (p₀ : CPN 2) :
    ∫ p, rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1) ∂(fubiniStudyMeasure p₀)
      = (2 * ‖inner ℂ n ψ‖ ^ 2 - 1) / 2 := by
  set μ := fubiniStudyMeasure p₀ with hμ
  set f : CPN 2 → ℝ :=
    fun p => rsign (2 * blochProj n p - 1) * (2 * blochProj ψ p - 1) with hf
  have hn0 : n ≠ 0 := by rw [← norm_pos_iff, hn]; norm_num
  have hfmeas : Measurable f :=
    (measurable_rsign.comp (((blochProj_measurable n).const_mul 2).sub_const 1)).mul
      (((blochProj_measurable ψ).const_mul 2).sub_const 1)
  have hbound : ∀ p, ‖f p‖ ≤ 1 := by
    intro p
    rw [hf]
    simp only [Real.norm_eq_abs, abs_mul]
    have hs2 : |2 * blochProj ψ p - 1| ≤ 1 := by
      have h0 := blochProj_nonneg ψ p
      have h1 := blochProj_le_one ψ hψ p
      rw [abs_le]; constructor <;> linarith
    calc |rsign (2 * blochProj n p - 1)| * |2 * blochProj ψ p - 1|
        ≤ 1 * 1 := mul_le_mul (abs_rsign_le_one _) hs2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hfint : Integrable f μ :=
    MeasureTheory.Integrable.of_bound hfmeas.aestronglyMeasurable 1 (ae_of_all _ hbound)
  have hrefl_meas : Measurable (fun p => f (reflU n hn • p)) :=
    hfmeas.comp (continuous_const_smul (reflU n hn)).measurable
  have hrefl_int : Integrable (fun p => f (reflU n hn • p)) μ :=
    MeasureTheory.Integrable.of_bound hrefl_meas.aestronglyMeasurable 1
      (ae_of_all _ (fun p => hbound (reflU n hn • p)))
  have hcov : ∫ p, f p ∂μ = ∫ p, f (reflU n hn • p) ∂μ := by
    have hinv := fubiniStudyMeasure_smul_invariant (reflU n hn) p₀
    calc ∫ p, f p ∂μ
        = ∫ p, f p ∂(Measure.map (fun q => reflU n hn • q) μ) := by rw [hinv]
      _ = ∫ p, f (reflU n hn • p) ∂μ :=
          MeasureTheory.integral_map
            (continuous_const_smul (reflU n hn)).measurable.aemeasurable
            hfmeas.aestronglyMeasurable
  have hpt : ∀ p : CPN 2, f p + f (reflU n hn • p)
      = 2 * (2 * ‖inner ℂ n ψ‖ ^ 2 - 1) * |2 * blochProj n p - 1| := by
    intro p
    have hfix := blochProj_refl_fixes n hn p
    have hsum := reflSum n ψ hn hψ p
    have hsgn := rsign_mul_self (2 * blochProj n p - 1)
    simp only [hf]
    rw [hfix]
    linear_combination (2 * rsign (2 * blochProj n p - 1)) * hsum
      + (2 * (2 * ‖inner ℂ n ψ‖ ^ 2 - 1)) * hsgn
  have hint_eq : ∫ p, (f p + f (reflU n hn • p)) ∂μ = 2 * ‖inner ℂ n ψ‖ ^ 2 - 1 := by
    rw [MeasureTheory.integral_congr_ae (ae_of_all _ hpt), MeasureTheory.integral_const_mul,
      hatBox_axis n hn0 hn p₀]
    ring
  have key : ∫ p, f p ∂μ + ∫ p, f (reflU n hn • p) ∂μ = 2 * ‖inner ℂ n ψ‖ ^ 2 - 1 := by
    rw [← integral_add hfint hrefl_int]; exact hint_eq
  rw [← hcov] at key
  linarith [key]

end CSD.LF4
