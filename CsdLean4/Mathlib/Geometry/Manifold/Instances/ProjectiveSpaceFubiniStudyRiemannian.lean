/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.RiemannianVolume
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudySymplectic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The Riemannian volume of the Fubini–Study metric is the symplectic volume over `n!`

**Category:** 1-Mathlib (the Kähler identity `vol_g = ω^{∧n}/n!` on `ℂℙⁿ`; G17 of
`specs/generator-layer-scoping.md` §9).

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Liouville)** — this module identifies the Riemannian and
symplectic readings of the Fubini–Study volume; `specs/TERMS.md` records what is backed.

The compatible metric of the almost Kähler structure of `ℂℙⁿ` (G7) is the Fubini–Study metric
`g = ω(J·,·)`. Its Riemannian volume (`RiemannianVolume.lean`: the chart densities `√det G` glued
along the affine cover) is identified with the measure of the top power of the Fubini–Study form:

* `fsMetric` — **the Fubini–Study metric** `g x u v = fsForm x (J u, v)`, definitionally the metric of
  `fsForm_isAlmostKahler`;
* `fsModelMetric w` — the model metric `g_w(u, v) = ω_w(i·u, v)` on `Fin n → ℂ`, as a real bilinear
  form; ★ `localRep_fsMetric` — **in every affine chart the Fubini–Study metric reads as the model
  metric** (`J = i·` in every chart, `fsJ_symmL`, and the form reads as the model form,
  `localRep_fsSection`);
* ★★ `det_toMatrix_fsModelMetric` — **the Gram determinant of the model metric against the standard
  basis is `(4ⁿ (1 + ‖w‖²)^{-(n+1)})²`**, by the route of `wedgePow_fsModelForm_stdBasis`: rotate `w`
  to the first axis by a unitary (`fsModelMetric_mulVec`; the real determinant of a unitary is `1`),
  where the metric is the pullback of the metric at the origin along the diagonal scaling
  (`fsModelMetric_single`, `normSq_det_fsScale`), and at the origin the Gram matrix is `4·1`
  (`toMatrix_fsModelMetric_zero`);
* ★★ `chartDensity_fsMetric` — **the Riemannian chart density is `1/n!` times the density of
  `ω_FS^{∧n}`**, in every chart (`√det G = 4ⁿ (1 + ‖w‖²)^{-(n+1)}` against `|coeff| = 4ⁿ n!
  (1 + ‖w‖²)^{-(n+1)}`);
* ★★★ `riemannianVolume_fsMetric` — **the Riemannian volume of the Fubini–Study metric IS
  `fsVolume n / n!`**, the Kähler identity `vol_g = ω^{∧n}/n!` at the level of measures; and ★★★
  `riemannianVolume_fsMetric_eq_smul_fubiniStudyMeasure` — with the constant, `vol_g = ((4π)ⁿ/n!) ·
  μ_FS`: **the Fubini–Study measure is the normalised Riemannian volume of the Fubini–Study metric**,
  the reading `TERMS.md` had listed as not established;
* **Q30 / G17b (2026-09-11).** `isBilinear_fsMetric` and ★ `riemannianVolume_fsMetric_congr_cover` —
  the identification holds for **every** chart cover, not only the affine one: the Riemannian volume
  of the Fubini–Study metric is canonical (`RiemannianMetric.riemannianVolume_congr_cover`).

## Honest scope

⚠️ **Densities, against the standard basis.** `RiemannianVolume.lean` defines the Riemannian volume
through Gram densities against a basis of the model; since Q30 it proves the construction is
cover-independent for bilinear families, and `isBilinear_fsMetric` supplies bilinearity here, so
`riemannianVolume_fsMetric_congr_cover` holds for every cover. Basis-independence of the Gram
construction (a change of basis rescales `√det G` by `|det|` of the change-of-basis matrix, which
`μ.IsAddHaarMeasure` absorbs) is not stated: nothing consumes it. The identity `vol_g = ω^{∧n}/n!`
is proved at the level of chart densities, not as an identity of volume *forms* (no orientation is
chosen).

⚠️ **Conventions.** The `(4π)ⁿ` and the `n!` are `fsChartForm = dd^c log(1 + ‖z‖²)`'s `-4` and the
top power's `n!` (`fsVolume_eq_smul_fubiniStudyMeasure`); the textbook `ω^{∧n}/n!` is a renormalisation.

References: `specs/generator-layer-scoping.md` (G17); `specs/TERMS.md` (Fubini–Study, Kähler,
Liouville); `Geometry/Manifold/RiemannianVolume.lean`; `Instances/ProjectiveSpaceFubiniStudyMass.lean`
(the rotation route, `det_mulVecCLM`, `fsScale`); `Instances/ProjectiveSpaceFubiniStudySymplectic.lean`
(`fsJ`, `fsJ_symmL`, `fsForm_isAlmostKahler`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix ENNReal Real
open Kahler Matrix.UnitaryGroup DifferentialForm

namespace Projectivization

variable {n : ℕ}

/-! ### The Fubini–Study metric and its model -/

/-- **The Fubini–Study metric** `g x u v = ω_FS (J u, v)`: the compatible metric of the almost Kähler
structure of `ℂℙⁿ`. -/
def fsMetric (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    ℝ :=
  fsForm x ![fsJ x u, v]

theorem fsMetric_eq_metric : fsMetric (n := n) = (fsForm_isAlmostKahler n).metric := rfl

/-- The model metric `g_w(u, v) = ω_w(i·u, v)` on `Fin n → ℂ`, as a real bilinear form. -/
noncomputable def fsModelMetric (w : Fin n → ℂ) : LinearMap.BilinForm ℝ (Fin n → ℂ) :=
  LinearMap.mk₂ ℝ (fun u v => fsModelForm w ![Complex.I • u, v])
    (fun u u' v => by
      rw [smul_add]
      exact apply_add_left (flatFamily (fsModelForm w)) 0 _ _ _)
    (fun c u v => by
      rw [smul_comm]
      exact apply_smul_left (flatFamily (fsModelForm w)) 0 c _ _)
    (fun u v v' => apply_add_right (flatFamily (fsModelForm w)) 0 _ _ _)
    (fun c u v => apply_smul_right (flatFamily (fsModelForm w)) 0 c _ _)

@[simp] theorem fsModelMetric_apply (w u v : Fin n → ℂ) :
    fsModelMetric w u v = fsModelForm w ![Complex.I • u, v] := rfl

/-- The form read through the tangent trivialisation of the chart at `x₀` is the model form: the
pointwise content of `localRep_fsSection`. -/
theorem fsForm_symmL_symmL (x₀ y : ℙ ℂ (Ambient n)) (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source)
    (a b : Fin n → ℂ) :
    fsForm y ![(trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL
        ℝ y a,
      (trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL ℝ y b]
      = fsModelForm (chartAt (Fin n → ℂ) x₀ y) ![a, b] := by
  have h2 := trivializationAt_snd fsSection x₀ y hy
  rw [localRep_fsSection x₀ y hy] at h2
  have h3 := congrArg (fun ξ => ξ ![a, b]) h2
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h3
  rw [show chartAt (Fin n → ℂ) x₀ y = chartFun (idx x₀) y from rfl, h3]
  refine congrArg (toFlat (fsSection y)) ?_
  funext i
  fin_cases i
  · show (trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL
        ℝ y a
      = fderiv ℝ (chartAt (Fin n → ℂ) y ∘ (chartAt (Fin n → ℂ) x₀).symm) (chartAt (Fin n → ℂ) x₀ y) a
    exact congrArg (fun L => L a) (tangent_symmL_eq_fderiv x₀ y hy)
  · show (trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL
        ℝ y b
      = fderiv ℝ (chartAt (Fin n → ℂ) y ∘ (chartAt (Fin n → ℂ) x₀).symm) (chartAt (Fin n → ℂ) x₀ y) b
    exact congrArg (fun L => L b) (tangent_symmL_eq_fderiv x₀ y hy)

/-- ★ **In every affine chart the Fubini–Study metric reads as the model metric**: `J = i·` in the
chart (`fsJ_symmL`) and the form reads as the model form. -/
theorem localRep_fsMetric (x₀ : ℙ ℂ (Ambient n)) {w : Fin n → ℂ}
    (hw : w ∈ (chartAt (Fin n → ℂ) x₀).target) (u v : Fin n → ℂ) :
    RiemannianMetric.localRep fsMetric x₀ w u v = fsModelMetric w u v := by
  have hy : (chartAt (Fin n → ℂ) x₀).symm w ∈ (chartAt (Fin n → ℂ) x₀).source :=
    (chartAt (Fin n → ℂ) x₀).map_target hw
  have hwy : chartAt (Fin n → ℂ) x₀ ((chartAt (Fin n → ℂ) x₀).symm w) = w :=
    (chartAt (Fin n → ℂ) x₀).right_inv hw
  show fsForm _ ![fsJ _ _, _] = fsModelForm w ![Complex.I • u, v]
  rw [fsJ_symmL x₀ _ hy u, fsForm_symmL_symmL x₀ _ hy, hwy]

theorem gram_fsMetric (x₀ : ℙ ℂ (Ambient n)) {w : Fin n → ℂ}
    (hw : w ∈ (chartAt (Fin n → ℂ) x₀).target) :
    RiemannianMetric.gram (stdBasis n) fsMetric x₀ w
      = LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric w) := by
  ext i j
  rw [RiemannianMetric.gram, Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply,
    localRep_fsMetric x₀ hw]

/-! ### The Gram determinant, by rotation to the first axis -/

/-- A complex matrix acting on the pi model, as a real linear map (`mulVecCLM`, forgotten). -/
def mulVecL (A : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
  (mulVecCLM A).toLinearMap

theorem mulVecL_apply (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : mulVecL A v = A *ᵥ v :=
  mulVecCLM_apply A v

theorem det_mulVecL (A : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (mulVecL A) = Complex.normSq A.det :=
  det_mulVecCLM A

/-- The unitary action commutes with `i·`, so the rotation invariance of the form
(`fsModelForm_mulVec`) is a rotation invariance of the metric. -/
theorem fsModelMetric_mulVec (U : Matrix.unitaryGroup (Fin n) ℂ) (w : Fin n → ℂ) :
    (fsModelMetric (U.val *ᵥ w)).comp (mulVecL U.val) (mulVecL U.val) = fsModelMetric w := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp only [LinearMap.BilinForm.comp_apply, fsModelMetric_apply, mulVecL_apply]
  have h := congrArg (fun ξ => ξ ![Complex.I • u, v]) (fsModelForm_mulVec U w)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  rw [← h, ← Matrix.mulVec_smul]
  congr 1
  funext i
  fin_cases i <;> simp [mulVecCLM_apply]

theorem det_toMatrix_fsModelMetric_mulVec (U : Matrix.unitaryGroup (Fin n) ℂ) (w : Fin n → ℂ) :
    (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric w)).det
      = (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric (U.val *ᵥ w))).det := by
  rw [← fsModelMetric_mulVec U w,
    LinearMap.BilinForm.toMatrix_comp (stdBasis n) (stdBasis n) (fsModelMetric (U.val *ᵥ w))
      (mulVecL U.val) (mulVecL U.val),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, det_mulVecL,
    normSq_det_unitary]
  ring

section Scale

variable [NeZero n]

/-- At `r e₀` the model metric is the pullback of the model metric at the origin along the diagonal
scaling (`fsModelForm_single`; the scaling is real-diagonal, so it commutes with `i·`). -/
theorem fsModelMetric_single (r : ℝ) :
    fsModelMetric (Pi.single (0 : Fin n) (r : ℂ))
      = (fsModelMetric 0).comp (mulVecL (fsScale (n := n) r)) (mulVecL (fsScale (n := n) r)) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp only [LinearMap.BilinForm.comp_apply, fsModelMetric_apply, mulVecL_apply]
  rw [fsModelForm_single, ContinuousAlternatingMap.compContinuousLinearMap_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  fin_cases i <;> simp [mulVecCLM_apply]

theorem det_toMatrix_fsModelMetric_single (r : ℝ) :
    (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric (Pi.single (0 : Fin n) (r : ℂ)))).det
      = (((1 + r ^ 2)⁻¹) ^ (n + 1)) ^ 2
        * (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric 0)).det := by
  rw [fsModelMetric_single,
    LinearMap.BilinForm.toMatrix_comp (stdBasis n) (stdBasis n) (fsModelMetric 0)
      (mulVecL (fsScale (n := n) r)) (mulVecL (fsScale (n := n) r)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, det_mulVecL,
    normSq_det_fsScale]
  ring

end Scale

/-! ### The Gram matrix at the origin is `4·1` -/

/-- At the origin the model metric is four times the real part of the inner product. -/
theorem fsModelMetric_zero_apply (u v : Fin n → ℂ) :
    fsModelMetric 0 u v = 4 * (inner ℂ (toLpCLM u) (toLpCLM v)).re := by
  have hu : toLpCLM (Complex.I • u) = Complex.I • toLpCLM u := by
    ext k
    simp
  rw [fsModelMetric_apply, fsModelForm_apply, hu, inner_smul_left, Complex.conj_I]
  simp only [map_zero, norm_zero, inner_zero_right, inner_zero_left, Complex.zero_im,
    Complex.zero_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- The standard basis is orthonormal for the real part of the inner product: `p = 2·(p/2) + p%2`. -/
theorem stdBasis_inner_re (p q : Fin (2 * n)) :
    (inner ℂ (toLpCLM (stdBasis n p)) (toLpCLM (stdBasis n q))).re = if p = q then 1 else 0 := by
  rw [stdBasis_eq_pairFamily, stdBasis_eq_pairFamily]
  simp only [pairFamily, id]
  rw [show toLpCLM (Pi.single (pairIdx p) (![1, Complex.I] (memIdx p)))
      = EuclideanSpace.single (pairIdx p) (![1, Complex.I] (memIdx p)) from rfl,
    show toLpCLM (Pi.single (pairIdx q) (![1, Complex.I] (memIdx q)))
      = EuclideanSpace.single (pairIdx q) (![1, Complex.I] (memIdx q)) from rfl,
    EuclideanSpace.inner_single_left, PiLp.single_apply]
  have hpq : p = q ↔ pairIdx p = pairIdx q ∧ memIdx p = memIdx q := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      have h1' := congrArg Fin.val h1
      have h2' := congrArg Fin.val h2
      simp only [pairIdx, memIdx] at h1' h2'
      exact Fin.ext (by omega)
  obtain ⟨mp, hmp⟩ : ∃ m, memIdx p = m := ⟨_, rfl⟩
  obtain ⟨mq, hmq⟩ : ∃ m, memIdx q = m := ⟨_, rfl⟩
  rw [hmp, hmq] at hpq ⊢
  by_cases h1 : pairIdx p = pairIdx q
  · rw [if_pos h1]
    by_cases h2 : mp = mq
    · rw [if_pos (hpq.2 ⟨h1, h2⟩), h2]
      fin_cases mq <;> simp [Complex.conj_I]
    · rw [if_neg (fun h => h2 (hpq.1 h).2)]
      fin_cases mp <;> fin_cases mq <;> simp_all [Complex.conj_I]
  · rw [if_neg h1, if_neg (fun h => h1 (hpq.1 h).1)]
    simp

theorem toMatrix_fsModelMetric_zero :
    LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric 0)
      = (4 : ℝ) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) := by
  ext p q
  rw [LinearMap.BilinForm.toMatrix_apply, fsModelMetric_zero_apply, stdBasis_inner_re,
    Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_toMatrix_fsModelMetric_zero :
    (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric 0)).det = (4 : ℝ) ^ (2 * n) := by
  rw [toMatrix_fsModelMetric_zero, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

/-! ### The Gram determinant everywhere -/

/-- ★★ **The Gram determinant of the model metric against the standard basis is
`(4ⁿ (1 + ‖w‖²)^{-(n+1)})²`**, everywhere on the chart. -/
theorem det_toMatrix_fsModelMetric (w : Fin n → ℂ) :
    (LinearMap.BilinForm.toMatrix (stdBasis n) (fsModelMetric w)).det
      = (4 ^ n * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1)) ^ 2 := by
  by_cases hw : w = 0
  · subst hw
    rw [det_toMatrix_fsModelMetric_zero, map_zero, norm_zero]
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, inv_one, one_pow,
      mul_one]
    ring
  · have : NeZero n := ⟨fun h => hw (by subst h; exact Subsingleton.elim _ _)⟩
    have hx : toLpCLM w ≠ 0 := fun h => hw (by
      have := congrArg WithLp.ofLp h
      simpa using this)
    obtain ⟨U, hU⟩ := Matrix.UnitaryGroup.exists_unitary_map_unit (‖toLpCLM w‖⁻¹ • toLpCLM w)
      (EuclideanSpace.single 0 (1 : ℂ)) (norm_smul_inv_norm hx) (by simp)
    have h1 : Matrix.toEuclideanLin U.val (toLpCLM w)
        = ‖toLpCLM w‖ • EuclideanSpace.single 0 (1 : ℂ) := by
      have hsm : toLpCLM w = ‖toLpCLM w‖ • (‖toLpCLM w‖⁻¹ • toLpCLM w) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
      conv_lhs => rw [hsm]
      rw [LinearMap.map_smul_of_tower, hU]
    have hUw : U.val *ᵥ w = Pi.single 0 ((‖toLpCLM w‖ : ℝ) : ℂ) := by
      have h2 : toLpCLM (U.val *ᵥ w) = ‖toLpCLM w‖ • EuclideanSpace.single 0 (1 : ℂ) := by
        rw [toLpCLM_mulVec, h1]
      funext j
      have hj := congrArg (fun z => z j) h2
      simpa [toLpCLM_apply, PiLp.single_apply, Pi.single_apply] using hj
    rw [det_toMatrix_fsModelMetric_mulVec U w, hUw, det_toMatrix_fsModelMetric_single,
      det_toMatrix_fsModelMetric_zero]
    ring

/-! ### The Riemannian density is the top-form density over `n!` -/

/-- ★★ **The Riemannian chart density of the Fubini–Study metric is `1/n!` times the density of
`ω_FS^{∧n}`**, in every affine chart. -/
theorem chartDensity_fsMetric (x₀ : ℙ ℂ (Ambient n)) {w : Fin n → ℂ}
    (hw : w ∈ (chartAt (Fin n → ℂ) x₀).target) :
    RiemannianMetric.chartDensity (stdBasis n) fsMetric x₀ w
      = ((n.factorial : ℝ≥0∞))⁻¹ * chartDensity (stdBasis n) (fun x => fsTopForm n x) x₀ w := by
  have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.2 n.factorial_pos
  have hpos : (0 : ℝ) ≤ 4 ^ n * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1) := by positivity
  rw [RiemannianMetric.chartDensity, gram_fsMetric x₀ hw, det_toMatrix_fsModelMetric,
    Real.sqrt_sq hpos, chartDensity, localRep_fsTopForm, wedgePow_fsModelForm_stdBasis,
    show (-4 : ℝ) ^ n * n.factorial * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1)
      = n.factorial * ((-4 : ℝ) ^ n * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1)) by ring,
    abs_mul, abs_of_pos hfac, ENNReal.ofReal_mul hfac.le, ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast n.factorial_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by positivity)]

/-- ★★★ **The Riemannian volume of the Fubini–Study metric IS the symplectic volume over `n!`**:
`vol_g = fsVolume n / n!` — the Kähler identity `vol_g = ω^{∧n}/n!` at the level of measures. -/
theorem riemannianVolume_fsMetric :
    RiemannianMetric.riemannianVolume volume (stdBasis n) fsMetric (affineChartCover n)
      = ((n.factorial : ℝ≥0∞))⁻¹ • fsVolume n :=
  RiemannianMetric.riemannianVolume_eq_smul_topFormMeasure volume (stdBasis n) fsMetric
    (affineChartCover n) (fun x => fsTopForm n x) _
    (ENNReal.inv_ne_top.2 (by exact_mod_cast n.factorial_ne_zero))
    (fun _ w hw => chartDensity_fsMetric _ hw)

/-- ★★★ **The Fubini–Study measure is the normalised Riemannian volume of the Fubini–Study
metric**: `vol_g = ((4π)ⁿ/n!) · μ_FS`. -/
theorem riemannianVolume_fsMetric_eq_smul_fubiniStudyMeasure
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    RiemannianMetric.riemannianVolume volume (stdBasis n) fsMetric (affineChartCover n)
      = ENNReal.ofReal ((4 * π) ^ n / n.factorial) • fubiniStudyMeasure p₀ := by
  rw [riemannianVolume_fsMetric, fsVolume_eq_smul_fubiniStudyMeasure p₀, smul_smul]
  congr 1
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
    (Nat.cast_pos.2 n.factorial_pos), ENNReal.ofReal_natCast, mul_comm]

/-! ### The Fubini–Study metric is bilinear, so its Riemannian volume is canonical (Q30) -/

/-- The Fubini–Study metric is bilinear at every point: `fsJ` is `ℝ`-linear (it is `i·`) and
`fsForm x` is bilinear (`apply_add_left` and friends). -/
theorem isBilinear_fsMetric : RiemannianMetric.IsBilinear (fsMetric (n := n)) where
  add_left := fun x a b v => by
    show fsForm x ![fsJ x (a + b), v] = fsForm x ![fsJ x a, v] + fsForm x ![fsJ x b, v]
    have h : fsJ x (a + b) = fsJ x a + fsJ x b := by
      show Complex.I • tangentToModel (a + b) = Complex.I • tangentToModel a + Complex.I • tangentToModel b
      exact smul_add _ _ _
    rw [h]
    exact apply_add_left (fun x => fsForm x) x _ _ _
  smul_left := fun x c a v => by
    show fsForm x ![fsJ x (c • a), v] = c * fsForm x ![fsJ x a, v]
    have h : fsJ x (c • a) = c • fsJ x a := by
      show Complex.I • tangentToModel (c • a) = c • (Complex.I • tangentToModel a)
      funext k
      show Complex.I * (c • tangentToModel a k) = c • (Complex.I * tangentToModel a k)
      rw [Complex.real_smul, Complex.real_smul]
      ring
    rw [h]
    exact apply_smul_left (fun x => fsForm x) x c _ _
  add_right := fun x v a b => apply_add_right (fun x => fsForm x) x _ _ _
  smul_right := fun x c v a => apply_smul_right (fun x => fsForm x) x c _ _

/-- ★ **The Riemannian volume of the Fubini–Study metric is canonical**: it does not depend on the
chart cover (`riemannianVolume_congr_cover`, from bilinearity) — so `riemannianVolume_fsMetric` is
a statement about *the* Riemannian volume, not about the affine cover's. -/
theorem riemannianVolume_fsMetric_congr_cover (c : ChartCover (Fin n → ℂ) (ℙ ℂ (Ambient n))) :
    RiemannianMetric.riemannianVolume volume (stdBasis n) fsMetric c
      = ((n.factorial : ℝ≥0∞))⁻¹ • fsVolume n := by
  rw [RiemannianMetric.riemannianVolume_congr_cover volume (stdBasis n) fsMetric isBilinear_fsMetric
    c (affineChartCover n)]
  exact riemannianVolume_fsMetric

end Projectivization

end
