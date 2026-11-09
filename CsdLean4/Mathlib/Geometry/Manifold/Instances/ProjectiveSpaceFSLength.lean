/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceGeometricPhase
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFisherRao
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# The Fubini–Study speed of a curve, and how fast the transition probability can change

**TERM-SCOPE(Kahler)** — this module uses the restricted sense of "Kähler"; `specs/TERMS.md`
records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #330 (geometric QM, item 5 of the 2026-11-08 plan), first part.

The Fubini–Study metric written on homogeneous coordinates, `FisherRao.fsInnerHom ψ u v`, does not
change when a lift is rescaled and its velocities are changed by multiples of the lift
(`fsInnerHom_lift`, the metric twin of `studyForm_lift`), so the squared speed of a projected
curve `[ψ]` is `fsInnerHom ψ ψ' ψ'` whatever lift is used (★★ `fsMetric_mfderiv_projCurve`). The
transition probability to a fixed ray changes along a lift at most at the rate the metric allows:
★★ `sq_dTransProb_le` — `(dP)² ≤ P (1 − P) · fsInnerHom ψ U U` for the derivative `dP` of
`P = transProbVec φ ψ` in the direction `U`, by Cauchy–Schwarz on the components orthogonal to `ψ`.

* `fsInnerHom_add_smul_left`, `fsInnerHom_add_smul_right`, `fsInnerHom_smul`, ★★ `fsInnerHom_lift`;
  ★ `fsInnerHom_chartVelCLM`;
* ★★ `fsMetric_mfderiv_projCurve` — **the squared Fubini–Study speed of `t ↦ [ψ t]` is
  `fsInnerHom (ψ t) ψ' ψ'`**;
* `perpTo`, `inner_perpTo_self`, `norm_perpTo_sq`; `dTransProb`, ★ `hasDerivAt_transProbVec`
  (the derivative of `P` along a lift), `dTransProb_eq_perp`, ★★ `sq_dTransProb_le`.

## Honest scope

⚠️ **Projected curves only.** The statements start from a curve of representatives
`ψ : ℝ → ℂⁿ⁺¹ \ {0}`; `fsMetric_mfderiv_projCurve` reads the manifold curve `t ↦ [ψ t]`, but
the converse (lifting an arbitrary curve on `ℂℙⁿ`) is not stated here.

## References

J. Anandan, Y. Aharonov, Phys. Rev. Lett. 65 (1990) 1697;
`Instances/ProjectiveSpaceGeometricPhase.lean` (`studyForm_lift`, `chartVelCLM`,
`hasMFDerivAt_projCurve`), `Instances/ProjectiveSpaceFisherRao.lean` (`fsMetric_eq_fsInnerHom`);
`specs/BACKLOG.md` #330, #331; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Kahler DifferentialForm FisherRao

noncomputable section

namespace Projectivization

/-! ### The homogeneous metric does not see the choice of lift -/

section Lift

variable {ι : Type*} [Fintype ι]

theorem fsInnerHom_add_smul_left {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (u v : EuclideanSpace ℂ ι) (a : ℂ) : fsInnerHom ψ (u + a • ψ) v = fsInnerHom ψ u v := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hre : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have him : (inner ℂ ψ ψ : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ψ
  simp only [fsInnerHom, inner_add_left, inner_smul_left, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, hre, him]
  field_simp
  ring

theorem fsInnerHom_add_smul_right {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (u v : EuclideanSpace ℂ ι) (b : ℂ) : fsInnerHom ψ u (v + b • ψ) = fsInnerHom ψ u v := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hre : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have him : (inner ℂ ψ ψ : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ψ
  simp only [fsInnerHom, inner_add_right, inner_smul_right, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, hre, him]
  field_simp
  ring

theorem fsInnerHom_smul {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) {c : ℂ} (hc : c ≠ 0)
    (u v : EuclideanSpace ℂ ι) : fsInnerHom (c • ψ) (c • u) (c • v) = fsInnerHom ψ u v := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hcc : ((starRingEnd ℂ) c) * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : (inner ℂ (c • u) (c • v) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ u v := by
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hcc]
  have h2 : (inner ℂ (c • u) (c • ψ) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ u ψ := by
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hcc]
  have h3 : (inner ℂ (c • ψ) (c • v) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ ψ v := by
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hcc]
  have h4 : (((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ u ψ * (((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ ψ v))
      = ((‖c‖ ^ 4 : ℝ) : ℂ) * (inner ℂ u ψ * inner ℂ ψ v) := by
    push_cast
    ring
  simp only [fsInnerHom, h1, h2, h3, h4, norm_smul, Complex.re_ofReal_mul]
  field_simp

/-- ★★ **The homogeneous metric depends only on the curve of rays**: rescaling the lift and
changing the velocities by multiples of the lift leaves it unchanged. -/
theorem fsInnerHom_lift {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) {c : ℂ} (hc : c ≠ 0)
    (u v : EuclideanSpace ℂ ι) (a b : ℂ) :
    fsInnerHom (c • ψ) (c • u + a • ψ) (c • v + b • ψ) = fsInnerHom ψ u v := by
  have hcψ : c • ψ ≠ 0 := smul_ne_zero hc hψ
  have ha : a • ψ = (a / c) • (c • ψ) := by
    rw [smul_smul, div_mul_cancel₀ _ hc]
  have hb : b • ψ = (b / c) • (c • ψ) := by
    rw [smul_smul, div_mul_cancel₀ _ hc]
  rw [ha, hb, fsInnerHom_add_smul_left hcψ, fsInnerHom_add_smul_right hcψ, fsInnerHom_smul hψ hc]

end Lift

variable {n : ℕ}

/-- ★ **The chart metric on the chart velocities is the homogeneous metric on the
representative.** -/
theorem fsInnerHom_chartVelCLM (i : Fin (n + 1)) {v : Ambient n} (hvi : v i ≠ 0)
    (d e : Ambient n) :
    fsInnerHom (insertOne i (coordRatio i v)) (insertZero i (chartVelCLM i v d))
        (insertZero i (chartVelCLM i v e)) = fsInnerHom v d e := by
  rw [insertOne_coordRatio i hvi, insertZero_chartVelCLM i hvi, insertZero_chartVelCLM i hvi,
    add_comm ((-(d i) / v i ^ 2) • v) ((v i)⁻¹ • d),
    add_comm ((-(e i) / v i ^ 2) • v) ((v i)⁻¹ • e)]
  exact fsInnerHom_lift (fun h => hvi (by simp [h])) (inv_ne_zero hvi) d e _ _

/-- ★★ **The squared Fubini–Study speed of a projected curve** `t ↦ [ψ t]` is
`fsInnerHom (ψ t) ψ' ψ'`, whatever lift is used. -/
theorem fsMetric_mfderiv_projCurve {γ : ℝ → Ambient n} (h : ∀ y, γ y ≠ 0) {D : Ambient n} {x : ℝ}
    (hγ : HasDerivAt γ D x) :
    fsMetric (projFamily γ h x)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily γ h) x (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily γ h) x (1 : ℝ))
      = fsInnerHom (γ x) D D := by
  have hm : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily γ h) x (1 : ℝ)
      = chartVelCLM (idx (projFamily γ h x)) (γ x) D := by
    rw [(hasMFDerivAt_projCurve h hγ).mfderiv]
    change (1 : ℝ) • chartVelCLM (idx (projFamily γ h x)) (γ x) D = _
    rw [one_smul]
  rw [hm, fsMetric_eq_fsInnerHom]
  have hc : chartFun (idx (projFamily γ h x)) (projFamily γ h x)
      = coordRatio (idx (projFamily γ h x)) (γ x) := chartFun_mk _ _ _
  rw [hc]
  exact fsInnerHom_chartVelCLM _ (idx_ne_zero h x) D D

/-! ### How fast the transition probability can change -/

/-- The component of `v` orthogonal to `ψ`. -/
def perpTo (ψ v : Ambient n) : Ambient n :=
  v - (inner ℂ ψ v / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) • ψ

theorem ofReal_norm_sq_ne_zero' {ψ : Ambient n} (hψ : ψ ≠ 0) : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hψ)

theorem inner_self_eq_ofReal (ψ : Ambient n) : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  simp [inner_self_eq_norm_sq_to_K]

theorem inner_perpTo_self {ψ : Ambient n} (hψ : ψ ≠ 0) (v : Ambient n) :
    inner ℂ ψ (perpTo ψ v) = 0 := by
  unfold perpTo
  rw [inner_sub_right, inner_smul_right, inner_self_eq_ofReal,
    div_mul_cancel₀ _ (ofReal_norm_sq_ne_zero' hψ), sub_self]

theorem norm_perpTo_sq {ψ : Ambient n} (hψ : ψ ≠ 0) (v : Ambient n) :
    ‖perpTo ψ v‖ ^ 2 = ‖v‖ ^ 2 - ‖inner ℂ ψ v‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.2 hψ
  unfold perpTo
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, ← inner_conj_symm v ψ]
  set b := inner ℂ ψ v
  have h1 : RCLike.re (b / ((‖ψ‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) b) = ‖b‖ ^ 2 / ‖ψ‖ ^ 2 := by
    rw [RCLike.re_to_complex, div_mul_eq_mul_div, Complex.mul_conj', Complex.div_ofReal_re]
    norm_cast
  have h2 : ‖b / ((‖ψ‖ ^ 2 : ℝ) : ℂ)‖ = ‖b‖ / ‖ψ‖ ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h1, h2]
  field_simp
  ring

/-- The derivative of `P(φ, ψ) = ‖⟪φ, ψ⟫‖² / (‖φ‖² ‖ψ‖²)` in the direction `U`. -/
def dTransProb (φ ψ U : Ambient n) : ℝ :=
  2 * ((starRingEnd ℂ) (inner ℂ φ ψ) * inner ℂ φ U).re / (‖φ‖ ^ 2 * ‖ψ‖ ^ 2)
    - ‖inner ℂ φ ψ‖ ^ 2 * (2 * (inner ℂ ψ U).re) / (‖φ‖ ^ 2 * (‖ψ‖ ^ 2) ^ 2)

/-- ★ **The derivative of the transition probability along a lift.** -/
theorem hasDerivAt_transProbVec (φ : Ambient n) {ψ : ℝ → Ambient n} {U : Ambient n} {t : ℝ}
    (hψ : HasDerivAt ψ U t) (h0 : ψ t ≠ 0) :
    HasDerivAt (fun s => transProbVec φ (ψ s)) (dTransProb φ (ψ t) U) t := by
  have hnum : HasDerivAt (fun s => ‖inner ℂ φ (ψ s)‖ ^ 2)
      (2 * ((starRingEnd ℂ) (inner ℂ φ (ψ t)) * inner ℂ φ U).re) t := by
    have hz : HasDerivAt (fun s => inner ℂ φ (ψ s)) (inner ℂ φ U) t := by
      have := (hasDerivAt_const t φ).inner ℂ hψ
      simpa using this
    have := hz.norm_sq
    simpa [Complex.inner, mul_comm] using this
  have hden : HasDerivAt (fun s => ‖ψ s‖ ^ 2) (2 * (inner ℂ (ψ t) U).re) t := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hψ.inner ℂ hψ)
    have hfun : (fun s => ‖ψ s‖ ^ 2) = fun s => Complex.reCLM (inner ℂ (ψ s) (ψ s)) := by
      funext s
      rw [Complex.reCLM_apply, inner_self_eq_ofReal, Complex.ofReal_re]
    rw [hfun]
    refine h1.congr_deriv ?_
    rw [Complex.reCLM_apply, Complex.add_re, ← inner_conj_symm U (ψ t), Complex.conj_re]
    ring
  have hden' : HasDerivAt (fun s => ‖φ‖ ^ 2 * ‖ψ s‖ ^ 2)
      (‖φ‖ ^ 2 * (2 * (inner ℂ (ψ t) U).re)) t := hden.const_mul _
  by_cases hφ : φ = 0
  · subst hφ
    have : (fun s => transProbVec (0 : Ambient n) (ψ s)) = fun _ => 0 := by
      funext s
      simp [transProbVec]
    rw [this]
    simpa [dTransProb] using hasDerivAt_const t (0 : ℝ)
  have hpos : ‖φ‖ ^ 2 * ‖ψ t‖ ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.2 hφ)) (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))
  have hq := hnum.div hden' hpos
  have hfun : (fun s => transProbVec φ (ψ s))
      = fun s => ‖inner ℂ φ (ψ s)‖ ^ 2 / (‖φ‖ ^ 2 * ‖ψ s‖ ^ 2) := by
    funext s
    rfl
  rw [hfun]
  refine hq.congr_deriv ?_
  unfold dTransProb
  field_simp

/-- `dP = 2 Re(conj⟪φ, ψ⟫ ⟪φ⊥, U⊥⟫) / (‖φ‖² ‖ψ‖²)` with `⊥` the components orthogonal to `ψ`. -/
theorem dTransProb_eq_perp {ψ : Ambient n} (hψ : ψ ≠ 0) (φ U : Ambient n) :
    dTransProb φ ψ U
      = 2 * ((starRingEnd ℂ) (inner ℂ φ ψ) * inner ℂ (perpTo ψ φ) (perpTo ψ U)).re
        / (‖φ‖ ^ 2 * ‖ψ‖ ^ 2) := by
  have hN : (‖ψ‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hψ)
  have hNc := ofReal_norm_sq_ne_zero' hψ
  have hpp : inner ℂ (perpTo ψ φ) (perpTo ψ U) = inner ℂ φ (perpTo ψ U) := by
    conv_lhs => rw [perpTo]
    rw [inner_sub_left, inner_smul_left, inner_perpTo_self hψ, mul_zero, sub_zero]
  rw [hpp, perpTo, inner_sub_right, inner_smul_right]
  unfold dTransProb
  by_cases hφ : φ = 0
  · subst hφ
    simp
  have hM : (‖φ‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hφ)
  have hconj : (starRingEnd ℂ) (inner ℂ φ ψ) * inner ℂ φ ψ = ((‖inner ℂ φ ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  rw [mul_sub, show (starRingEnd ℂ) (inner ℂ φ ψ) * (inner ℂ ψ U / ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      * inner ℂ φ ψ) = ((‖inner ℂ φ ψ‖ ^ 2 : ℝ) : ℂ) * inner ℂ ψ U / ((‖ψ‖ ^ 2 : ℝ) : ℂ) by
    rw [← hconj]; ring]
  rw [Complex.sub_re, Complex.div_ofReal_re, Complex.re_ofReal_mul]
  field_simp

/-- ★★ **The transition probability changes at most at the rate the metric allows**:
`(dP)² ≤ P (1 − P) · fsInnerHom ψ U U`. -/
theorem sq_dTransProb_le {φ ψ : Ambient n} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (U : Ambient n) :
    dTransProb φ ψ U ^ 2
      ≤ transProbVec φ ψ * (1 - transProbVec φ ψ) * fsInnerHom ψ U U := by
  set M := ‖φ‖ ^ 2 with hMdef
  set N := ‖ψ‖ ^ 2 with hNdef
  have hM : 0 < M := pow_pos (norm_pos_iff.2 hφ) 2
  have hN : 0 < N := pow_pos (norm_pos_iff.2 hψ) 2
  set a := inner ℂ φ ψ
  set z := (starRingEnd ℂ) a * inner ℂ (perpTo ψ φ) (perpTo ψ U)
  have hz : ‖z‖ ≤ ‖a‖ * (‖perpTo ψ φ‖ * ‖perpTo ψ U‖) := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hφp := norm_perpTo_sq hψ φ
  have hUp := norm_perpTo_sq hψ U
  have hP : transProbVec φ ψ = ‖a‖ ^ 2 / (M * N) := rfl
  have hf : fsInnerHom ψ U U = 4 * (‖perpTo ψ U‖ ^ 2 / N) := by
    rw [hUp]
    unfold fsInnerHom
    rw [← hNdef]
    have h1 : (inner ℂ U U).re = ‖U‖ ^ 2 := by
      rw [inner_self_eq_ofReal]
      exact Complex.ofReal_re _
    have h2 : (inner ℂ U ψ * inner ℂ ψ U).re = ‖inner ℂ ψ U‖ ^ 2 := by
      rw [← inner_conj_symm U ψ, mul_comm, Complex.mul_conj']
      norm_cast
    rw [h1, h2]
    field_simp
    ring
  have hφ' : ‖inner ℂ ψ φ‖ = ‖a‖ := by rw [← inner_conj_symm, Complex.norm_conj]
  rw [hφ'] at hφp
  rw [dTransProb_eq_perp hψ, hP, hf]
  have key : (2 * z.re / (M * N)) ^ 2
      ≤ 4 * ‖a‖ ^ 2 * (‖perpTo ψ φ‖ ^ 2 * ‖perpTo ψ U‖ ^ 2) / (M * N) ^ 2 := by
    rw [div_pow, mul_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h3 : ‖z‖ ^ 2 ≤ (‖a‖ * (‖perpTo ψ φ‖ * ‖perpTo ψ U‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith [hre, h3]
  refine key.trans (le_of_eq ?_)
  rw [hφp]
  field_simp
  ring

end Projectivization
