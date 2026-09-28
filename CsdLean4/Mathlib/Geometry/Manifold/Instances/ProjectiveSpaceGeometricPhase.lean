/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFisherRao
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.GeometricPhaseCurvature

/-!
# The curvature of the geometric phase is the Fubini–Study form

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #65, the residue of #54 (brick
BP-3 of `specs/berry-phase-scoping.md`).

`GeometricPhaseCurvature.lean` proves the curvature formula `β = −∫∫ 2 Im⟪∂_sΨ, ∂_tΨ⟫` for a `C²`
family of unit vectors, and says in its honest scope that identifying that integrand with the
corpus's Fubini–Study form is open. This module closes it:

`2 Im⟪∂_sΨ, ∂_tΨ⟫ = −(1/2) · ω_FS` on the velocities of the projected family `[Ψ]`,

so `β = (1/2) ∫∫ [Ψ]^* ω_FS` — Berry's phase as the integral of the Kähler form over the disc.

## The route

* ★ `studyForm ψ u v = Im⟪u,v⟫/‖ψ‖² − Im(⟪u,ψ⟫⟪ψ,v⟫)/‖ψ‖⁴` — the Fubini–Study form written on
  homogeneous coordinates, the `Im` twin of `FisherRao.fsInnerHom`. Its two properties are the
  whole geometry: ★★ `studyForm_lift` — it does not change when the lift is rescaled by a scalar
  and the velocities are changed by multiples of the lift (`ψ ↦ cψ`, `u ↦ cu + aψ`), which is
  exactly the freedom in choosing a lift of a curve of rays; and ★ `studyForm_of_unit` — for a
  *unit* lift it is plainly `Im⟪u,v⟫`, because the correction term is real (the fibre direction is
  imaginary).
* ★★ `fsModelForm_eq_studyForm` — the model form at `w` is `−4 studyForm` of the lifts
  `insertOne i w`, `insertZero i u` (the form twin of `fsMetric_eq_fsInnerHom`).
* `chartVelCLM i v` — the differential of the affine chart on representatives, and
  ★ `hasFDerivAt_coordRatio`: the chart coordinates of a differentiable family of lifts are
  differentiable, with that velocity. `insertZero_chartVelCLM` expresses the lifted chart velocity
  as `a • v + (v i)⁻¹ • d`, which is what `studyForm_lift` consumes, giving ★★
  `studyForm_chartVelCLM` — the chart form on the chart velocities is the homogeneous form on the
  original lift and its velocities.
* ★★★ `fsModelForm_eq_neg_two_mul_curvature` (chart level, any chart containing the point) and
  ★★★ `fsForm_eq_neg_two_mul_curvature` (the form of `ProjectiveSpaceFubiniStudyForm.lean` at the
  ray `[Ψ p]`, in the atlas's own chart) — **the curvature is `−1/2` of the Fubini–Study form on
  the velocities of the projected family**.
* ★★ `hasMFDerivAt_projFamily` — those velocities *are* the pushforward: the manifold derivative
  of `q ↦ [Ψ q]` is the derivative of the chart path, so the two theorems above are the pullback
  `[Ψ]^* ω_FS` and not merely a formula in a chart.
* ★★★ `geometricPhase_eq_half_integral_fsPullback` — the curvature formula of #54 restated:
  `β = (1/2) ∫₀¹ ∫₀ᵀ [Ψ]^* ω_FS`.

## The normalisation

None is chosen here: `fsForm` is the `dd^c` form of `log(1 + ‖z‖²)` (`fsChartForm`), whose value at
a chart origin is `−4` times `Im⟪·,·⟫` (`fsChartForm_zero`), and the `−1/2` above is what that
convention forces. The check is BP-2: on `ℂℙ¹` the cone's disc gives `β = −Ω/2` for the solid angle
`Ω` (`Empirical/QM/BerryPhaseCurvature.lean`), and `fsForm` has total mass `4π` on `ℂℙ¹`
(`fsVolume_eq_smul_fsMeasure`), the solid angle of the whole sphere.

## Honest scope

⚠️ The disc is a rectangle, as in #54: this is Green's theorem in a chart, not Stokes on a
manifold. What is proved here is the *integrand* — the pointwise identification of the curvature
with `ω_FS` on the pushed-forward velocities — and the integral in
`geometricPhase_eq_half_integral_fsPullback` is the iterated interval integral of that function,
which is the same number as `∫∫ [Ψ]^* ω_FS` would be. The corpus integrates a *top-degree* form as a
measure (`topFormMeasure`, `riemannianVolume`); integration of a `2`-form over a `2`-chain is not
defined here and is not claimed.

⚠️ The pushforward statement `hasMFDerivAt_projCurve` is for *curves*, which is what the two
coordinate directions are; the bundled manifold derivative of the two-parameter map
`ℝ × ℝ → ℂℙⁿ` is not stated, because Mathlib has no quotient rule for `HasFDerivAt` at the pin
(MATHLIB-ABSENT(HasFDerivAt.div); only `HasDerivAt.div` exists) — BACKLOG #89.

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45, §3; B. Simon, PRL 51 (1983) 2167;
Y. Aharonov, J. Anandan, PRL 58 (1987) 1593; `specs/berry-phase-scoping.md` BP-3;
`specs/BACKLOG.md` #65; `specs/future-work.md`.
-/

@[expose] public section

open Bundle Projectivization GeometricPhase
open scoped Manifold ComplexConjugate LinearAlgebra.Projectivization

noncomputable section

namespace Projectivization

/-! ### The Fubini–Study form on homogeneous coordinates -/

section StudyForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The Fubini–Study form written on homogeneous coordinates**: for a lift `ψ ≠ 0` and
velocities `u`, `v`,
`studyForm ψ u v = Im⟪u,v⟫/‖ψ‖² − Im(⟪u,ψ⟫⟪ψ,v⟫)/‖ψ‖⁴`.
This is the `Im` twin of `FisherRao.fsInnerHom`, the Fubini–Study metric in the same coordinates. -/
def studyForm (ψ u v : E) : ℝ :=
  (inner ℂ u v).im / ‖ψ‖ ^ 2 - (inner ℂ u ψ * inner ℂ ψ v).im / ‖ψ‖ ^ 4

/-- Adding a multiple of the lift to the first velocity does not change the form: the fibre
direction is in the kernel. -/
theorem studyForm_add_smul_left {ψ : E} (hψ : ψ ≠ 0) (u v : E) (a : ℂ) :
    studyForm ψ (u + a • ψ) v = studyForm ψ u v := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hre : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have him : (inner ℂ ψ ψ : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ψ
  simp only [studyForm, inner_add_left, inner_smul_left, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, hre, him]
  field_simp
  ring

/-- Adding a multiple of the lift to the second velocity does not change the form. -/
theorem studyForm_add_smul_right {ψ : E} (hψ : ψ ≠ 0) (u v : E) (b : ℂ) :
    studyForm ψ u (v + b • ψ) = studyForm ψ u v := by
  have hN : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hre : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have him : (inner ℂ ψ ψ : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ψ
  simp only [studyForm, inner_add_right, inner_smul_right, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, hre, him]
  field_simp
  ring

/-- Rescaling the lift and the velocities together does not change the form. -/
theorem studyForm_smul {ψ : E} (hψ : ψ ≠ 0) {c : ℂ} (hc : c ≠ 0) (u v : E) :
    studyForm (c • ψ) (c • u) (c • v) = studyForm ψ u v := by
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
  simp only [studyForm, h1, h2, h3, h4, norm_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  field_simp

/-- ★★ **The form depends only on the curve of rays.** Rescaling the lift by `c ≠ 0` and changing
the velocities by arbitrary multiples of the lift — which is exactly the freedom in lifting a curve
of rays — leaves `studyForm` unchanged. -/
theorem studyForm_lift {ψ : E} (hψ : ψ ≠ 0) {c : ℂ} (hc : c ≠ 0) (u v : E) (a b : ℂ) :
    studyForm (c • ψ) (c • u + a • ψ) (c • v + b • ψ) = studyForm ψ u v := by
  have hcψ : c • ψ ≠ 0 := smul_ne_zero hc hψ
  have ha : a • ψ = (a / c) • (c • ψ) := by
    rw [smul_smul, div_mul_cancel₀ _ hc]
  have hb : b • ψ = (b / c) • (c • ψ) := by
    rw [smul_smul, div_mul_cancel₀ _ hc]
  rw [ha, hb, studyForm_add_smul_left hcψ, studyForm_add_smul_right hcψ, studyForm_smul hψ hc]

/-- ★ **For a unit lift the form is plainly `Im⟪u,v⟫`**: the correction term is real, because
`⟪ψ, u⟫` and `⟪ψ, v⟫` are purely imaginary along a family of unit vectors. -/
theorem studyForm_of_unit {ψ u v : E} (h1 : ‖ψ‖ = 1) (hu : (inner ℂ ψ u : ℂ).re = 0)
    (hv : (inner ℂ ψ v : ℂ).re = 0) : studyForm ψ u v = (inner ℂ u v : ℂ).im := by
  have hu' : (inner ℂ u ψ : ℂ).re = 0 := by
    rw [← inner_conj_symm u ψ, Complex.conj_re, hu]
  have hzero : (inner ℂ u ψ * inner ℂ ψ v : ℂ).im = 0 := by
    rw [Complex.mul_im, hu', hv]
    ring
  rw [studyForm, h1, hzero]
  norm_num

/-- Along a family of unit vectors the inner product of the value with the velocity is purely
imaginary: differentiating `‖γ‖² = 1`. -/
theorem re_inner_deriv_eq_zero {γ : ℝ → E} {D : E} {x : ℝ} (hγ : HasDerivAt γ D x)
    (hunit : ∀ y, ‖γ y‖ = 1) : (inner ℂ (γ x) D : ℂ).re = 0 := by
  have hconst : (fun y => (inner ℂ (γ y) (γ y) : ℂ)) = fun _ => (1 : ℂ) := by
    funext y
    rw [inner_self_eq_norm_sq_to_K, hunit y]
    norm_num
  have h1 : HasDerivAt (fun y => (inner ℂ (γ y) (γ y) : ℂ))
      (inner ℂ (γ x) D + inner ℂ D (γ x)) x := hγ.inner ℂ hγ
  rw [hconst] at h1
  have h2 : (inner ℂ (γ x) D + inner ℂ D (γ x) : ℂ) = 0 :=
    h1.unique (hasDerivAt_const x (1 : ℂ))
  have h3 : (inner ℂ D (γ x) : ℂ) = conj (inner ℂ (γ x) D : ℂ) := (inner_conj_symm _ _).symm
  rw [h3] at h2
  have h4 := congrArg Complex.re h2
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at h4
  linarith

end StudyForm

/-! ### The model form on the lifts -/

section Chart

variable {n : ℕ}

/-- ★★ **The model form is `−4` times the homogeneous form on the lifts** — the `Im` twin of
`fsMetric_eq_fsInnerHom`: the Fubini–Study form of the `i`-th affine chart at `w`, evaluated on
chart directions `u`, `v`, is `studyForm` of the lifts `insertOne i w`, `insertZero i u`,
`insertZero i v`. -/
theorem fsModelForm_eq_studyForm (i : Fin (n + 1)) (w u v : Fin n → ℂ) :
    fsModelForm w ![u, v]
      = -4 * studyForm (insertOne i w) (insertZero i u) (insertZero i v) := by
  have h4 : ‖insertOne i w‖ ^ 4 = (‖insertOne i w‖ ^ 2) ^ 2 := by ring
  have hD : 1 + ‖toLpCLM w‖ ^ 2 ≠ 0 := by positivity
  rw [fsModelForm_apply, studyForm, inner_insertZero_insertZero, inner_insertZero_insertOne,
    inner_insertOne_insertZero, h4, norm_insertOne_sq]
  field_simp

/-! ### The differential of the affine chart, on representatives -/

/-- The differential of `coordRatio i` at `v`: the velocity of the affine chart coordinates, a
`ℂ`-linear map of the velocity of the representative. -/
def chartVelCLM (i : Fin (n + 1)) (v : Ambient n) : Ambient n →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (v i / v i ^ 2) • EuclideanSpace.proj (i.succAbove j)
      - (v (i.succAbove j) / v i ^ 2) • EuclideanSpace.proj i

theorem chartVelCLM_apply (i : Fin (n + 1)) (v d : Ambient n) (j : Fin n) :
    chartVelCLM i v d j = (d (i.succAbove j) * v i - v (i.succAbove j) * d i) / v i ^ 2 := by
  simp only [chartVelCLM, ContinuousLinearMap.pi_apply, FunLike.coe_sub, FunLike.coe_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [PiLp.proj_apply, PiLp.proj_apply]
  ring

/-- ★ **The chart coordinates of a differentiable curve of representatives are differentiable**,
with velocity `chartVelCLM`: the quotient rule, coordinate by coordinate. -/
theorem hasDerivAt_coordRatio {γ : ℝ → Ambient n} {D : Ambient n} {x : ℝ} (hγ : HasDerivAt γ D x)
    (i : Fin (n + 1)) (hi : γ x i ≠ 0) :
    HasDerivAt (fun y => coordRatio i (γ y)) (chartVelCLM i (γ x) D) x := by
  have hcoord : ∀ k : Fin (n + 1), HasDerivAt (fun y => γ y k) (D k) x := fun k =>
    (((EuclideanSpace.proj k : Ambient n →L[ℂ] ℂ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      x hγ
  refine hasDerivAt_pi.2 fun j => ?_
  refine ((hcoord (i.succAbove j)).div (hcoord i) hi).congr_deriv ?_
  rw [chartVelCLM_apply]

/-! ### The lifted chart velocity -/

/-- The affine section applied to the chart coordinates rescales the representative. -/
theorem insertOne_coordRatio (i : Fin (n + 1)) {v : Ambient n} (hv : v i ≠ 0) :
    insertOne i (coordRatio i v) = (v i)⁻¹ • v := by
  apply WithLp.ofLp_injective
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · show insertOne i (coordRatio i v) i = ((v i)⁻¹ • v) i
    rw [insertOne_apply_same, smul_ofLp, inv_mul_cancel₀ hv]
  · intro j
    show insertOne i (coordRatio i v) (i.succAbove j) = ((v i)⁻¹ • v) (i.succAbove j)
    rw [insertOne_apply_succAbove, smul_ofLp, coordRatio, div_eq_inv_mul]

/-- ★ **The lifted chart velocity is the velocity of the rescaled representative**: the lift of
`chartVelCLM i v d` differs from `(v i)⁻¹ • d` by a multiple of `v` — which is exactly the freedom
`studyForm_lift` absorbs. -/
theorem insertZero_chartVelCLM (i : Fin (n + 1)) {v : Ambient n} (hv : v i ≠ 0) (d : Ambient n) :
    insertZero i (chartVelCLM i v d) = (-(d i) / v i ^ 2) • v + (v i)⁻¹ • d := by
  apply WithLp.ofLp_injective
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · show insertZero i (chartVelCLM i v d) i = ((-(d i) / v i ^ 2) • v + (v i)⁻¹ • d) i
    rw [insertZero_apply_same]
    show (0 : ℂ) = (-(d i) / v i ^ 2) * v i + (v i)⁻¹ * d i
    field_simp
    ring
  · intro j
    show insertZero i (chartVelCLM i v d) (i.succAbove j)
      = ((-(d i) / v i ^ 2) • v + (v i)⁻¹ • d) (i.succAbove j)
    rw [insertZero_apply_succAbove, chartVelCLM_apply]
    show (d (i.succAbove j) * v i - v (i.succAbove j) * d i) / v i ^ 2
      = (-(d i) / v i ^ 2) * v (i.succAbove j) + (v i)⁻¹ * d (i.succAbove j)
    field_simp
    ring

/-- ★★ **The chart form on the chart velocities is the homogeneous form on the representative.**
Every trace of the chart is gone from the right-hand side: this is where the projective invariance
of `studyForm` is spent. -/
theorem studyForm_chartVelCLM (i : Fin (n + 1)) {v : Ambient n} (hv0 : v ≠ 0) (hvi : v i ≠ 0)
    (d e : Ambient n) :
    studyForm (insertOne i (coordRatio i v)) (insertZero i (chartVelCLM i v d))
        (insertZero i (chartVelCLM i v e)) = studyForm v d e := by
  rw [insertOne_coordRatio i hvi, insertZero_chartVelCLM i hvi, insertZero_chartVelCLM i hvi,
    add_comm ((-(d i) / v i ^ 2) • v) ((v i)⁻¹ • d),
    add_comm ((-(e i) / v i ^ 2) • v) ((v i)⁻¹ • e)]
  exact studyForm_lift hv0 (inv_ne_zero hvi) d e _ _

end Chart

/-! ### The curvature is the Fubini–Study form -/

section Curvature

variable {n : ℕ}

/-- The `s`-edge of a family, as a curve with the partial derivative as its velocity. -/
theorem hasDerivAt_edgeS {Ψ : ℝ × ℝ → Ambient n} {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    HasDerivAt (fun s => Ψ (s, t)) (fderiv ℝ Ψ (s, t) (1, 0)) s :=
  HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun s => (s, t)) (x := s) hΨ.hasFDerivAt
    ((hasDerivAt_id' (x := s)).prodMk (hasDerivAt_const s t))

/-- The `t`-edge of a family, as a curve with the partial derivative as its velocity. -/
theorem hasDerivAt_edgeT {Ψ : ℝ × ℝ → Ambient n} {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    HasDerivAt (fun t => Ψ (s, t)) (fderiv ℝ Ψ (s, t) (0, 1)) t :=
  HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun t => (s, t)) (x := t) hΨ.hasFDerivAt
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id' (x := t)))

theorem ne_zero_of_norm_eq_one {v : Ambient n} (h : ‖v‖ = 1) : v ≠ 0 := by
  intro hv
  rw [hv, norm_zero] at h
  exact zero_ne_one h

/-- ★★★ **The curvature of the geometric phase is the Fubini–Study form**, in any affine chart
containing the ray: for a family of unit vectors differentiable at `(s, t)`, the chart form at the
chart point, evaluated on the velocities of the chart path, is `−2` times the curvature
`2 Im⟪∂_sΨ, ∂_tΨ⟫`. -/
theorem fsModelForm_eq_neg_two_mul_curvature {Ψ : ℝ × ℝ → Ambient n} {s t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (s, t)) (hunit : ∀ q, ‖Ψ q‖ = 1) (i : Fin (n + 1))
    (hi : Ψ (s, t) i ≠ 0) :
    fsModelForm (coordRatio i (Ψ (s, t)))
        ![deriv (fun s => coordRatio i (Ψ (s, t))) s, deriv (fun t => coordRatio i (Ψ (s, t))) t]
      = -2 * curvature Ψ (s, t) := by
  have hS := hasDerivAt_edgeS hΨ
  have hT := hasDerivAt_edgeT hΨ
  rw [(hasDerivAt_coordRatio hS i hi).deriv, (hasDerivAt_coordRatio hT i hi).deriv,
    fsModelForm_eq_studyForm i, studyForm_chartVelCLM i (ne_zero_of_norm_eq_one (hunit (s, t))) hi,
    studyForm_of_unit (hunit (s, t)) (re_inner_deriv_eq_zero hS fun y => hunit (y, t))
      (re_inner_deriv_eq_zero hT fun y => hunit (s, y)), curvature]
  ring

/-! ### The projected family -/

/-- The projection of a family of nonzero representatives to `ℂℙⁿ`. -/
def projFamily {ι : Type*} (Ψ : ι → Ambient n) (h : ∀ q, Ψ q ≠ 0) (q : ι) : ℙ ℂ (Ambient n) :=
  mk ℂ (Ψ q) (h q)

/-- The atlas's chart at the projected point contains it: the representative's coordinate there
does not vanish. -/
theorem idx_ne_zero {ι : Type*} {Ψ : ι → Ambient n} (h : ∀ q, Ψ q ≠ 0) (q : ι) :
    Ψ q (idx (projFamily Ψ h q)) ≠ 0 := by
  have hrep := idx_spec (projFamily Ψ h q)
  rwa [projFamily, rep_ne_zero_iff] at hrep

/-- ★★ **The chart velocity is the pushforward.** The manifold derivative of the projected curve
`y ↦ [γ y]` is the derivative of its chart path, so the tangent vectors of
`fsForm_eq_neg_two_mul_curvature` are the pushforwards of the coordinate directions and the
identification is the pullback `[Ψ]^* ω_FS`. -/
theorem hasMFDerivAt_projCurve {γ : ℝ → Ambient n} (h : ∀ y, γ y ≠ 0) {D : Ambient n} {x : ℝ}
    (hγ : HasDerivAt γ D x) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily γ h) x
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (chartVelCLM (idx (projFamily γ h x)) (γ x) D)) := by
  have hi := idx_ne_zero h x
  have hsub : ContinuousAt (fun y => (⟨γ y, h y⟩ : {v : Ambient n // v ≠ 0})) x := by
    rw [ContinuousAt, nhds_subtype_eq_comap, Filter.tendsto_comap_iff]
    exact hγ.continuousAt
  refine ⟨(continuous_mk' (K := ℂ)).continuousAt.comp hsub, ?_⟩
  have hw : writtenInExtChartAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) x (projFamily γ h)
      = fun y => coordRatio (idx (projFamily γ h x)) (γ y) := by
    funext y
    simp only [writtenInExtChartAt, Function.comp, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    exact chartFun_mk _ _ _
  rw [hw]
  simp only [modelWithCornersSelf_coe, Set.range_id, extChartAt_coe, Function.comp_apply, id]
  exact (hasDerivAt_iff_hasFDerivAt.mp (hasDerivAt_coordRatio hγ _ hi)).hasFDerivWithinAt

/-- ★★★ **The curvature is `−1/2` of the Fubini–Study form of `ℂℙⁿ`** on the velocities of the
projected family, in the atlas's own chart at the point — the identification the honest scope of
`GeometricPhaseCurvature.lean` left open. -/
theorem fsForm_eq_neg_two_mul_curvature {Ψ : ℝ × ℝ → Ambient n} (h : ∀ q, Ψ q ≠ 0)
    (hunit : ∀ q, ‖Ψ q‖ = 1) {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    fsForm (projFamily Ψ h (s, t))
        ![deriv (fun a => coordRatio (idx (projFamily Ψ h (s, t))) (Ψ (a, t))) s,
          deriv (fun b => coordRatio (idx (projFamily Ψ h (s, t))) (Ψ (s, b))) t]
      = -2 * curvature Ψ (s, t) := by
  have hi := idx_ne_zero h (s, t)
  have hchart : chartFun (idx (projFamily Ψ h (s, t))) (projFamily Ψ h (s, t))
      = coordRatio (idx (projFamily Ψ h (s, t))) (Ψ (s, t)) := chartFun_mk _ _ _
  show fsModelForm (chartFun (idx (projFamily Ψ h (s, t))) (projFamily Ψ h (s, t))) ![_, _] = _
  rw [hchart]
  exact fsModelForm_eq_neg_two_mul_curvature hΨ hunit _ hi

/-! ### The curvature formula as an integral of the Fubini–Study form -/

/-- The pullback of the Fubini–Study form along the projected family, on the coordinate
directions: `([Ψ])^* ω_FS (∂_s, ∂_t)`. -/
def fsPullback (Ψ : ℝ × ℝ → Ambient n) (h : ∀ q, Ψ q ≠ 0) (p : ℝ × ℝ) : ℝ :=
  fsForm (projFamily Ψ h p)
    ![deriv (fun s => coordRatio (idx (projFamily Ψ h p)) (Ψ (s, p.2))) p.1,
      deriv (fun t => coordRatio (idx (projFamily Ψ h p)) (Ψ (p.1, t))) p.2]

/-- ★★★ The pointwise identification, in the form the integral consumes. -/
theorem curvature_eq_neg_half_fsPullback {Ψ : ℝ × ℝ → Ambient n} (h : ∀ q, Ψ q ≠ 0)
    (hunit : ∀ q, ‖Ψ q‖ = 1) {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    curvature Ψ (s, t) = -(1 / 2) * fsPullback Ψ h (s, t) := by
  have hval : fsPullback Ψ h (s, t) = -2 * curvature Ψ (s, t) :=
    fsForm_eq_neg_two_mul_curvature h hunit hΨ
  rw [hval]
  ring

/-- ★★★ **Berry's phase is half the integral of the Fubini–Study form over the disc.** The
curvature formula of `GeometricPhaseCurvature.lean` with its integrand identified: for a `C²` family
of unit vectors on `[0,1] × [0,T]` — the disc in polar form, the inner edge collapsed, the cut
carrying the total phase `φ 1` — the geometric phase of the loop is
`(1/2) ∫∫ [Ψ]^* ω_FS`. -/
theorem geometricPhase_eq_half_integral_fsPullback {Ψ : ℝ × ℝ → Ambient n} (h : ∀ q, Ψ q ≠ 0)
    (hΨ : ContDiff ℝ 2 Ψ) (hunit : ∀ p, ‖Ψ p‖ = 1) {T : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφ0 : φ 0 = 0) (hleft : ∀ t, Ψ (0, t) = Ψ (0, 0))
    (htop : ∀ s, Ψ (s, T) = Complex.exp ((φ s : ℂ) * Complex.I) • Ψ (s, 0)) :
    geometricPhase (fun t => Ψ (1, t)) T (φ 1)
      = 1 / 2 * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..T, fsPullback Ψ h (s, t) := by
  have hdiff : ∀ p, DifferentiableAt ℝ Ψ p := fun p => hΨ.differentiable (by norm_num) p
  have hinner : ∀ s : ℝ, ∫ t in (0 : ℝ)..T, curvature Ψ (s, t)
      = -(1 / 2) * ∫ t in (0 : ℝ)..T, fsPullback Ψ h (s, t) := by
    intro s
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ =>
      curvature_eq_neg_half_fsPullback h hunit (hdiff (s, t))
  rw [geometricPhase_eq_neg_integral_curvature hΨ hunit hφ hφ0 hleft htop,
    intervalIntegral.integral_congr fun s _ => hinner s, intervalIntegral.integral_const_mul]
  ring

end Curvature

end Projectivization

end
