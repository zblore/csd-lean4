/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceMomentMap
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannian
public import CsdLean4.Mathlib.Analysis.InformationGeometry.FubiniStudyFisherRao
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The Fubini–Study metric of `ℂℙⁿ` pushes forward to Fisher–Rao along the moment map

**Category:** 1-Mathlib (CSD-free; the Kähler manifold `ℂℙⁿ`, its torus moment map and the
open simplex of `FisherRao.lean`).

The torus moment map `Φ : ℂℙⁿ → Δⁿ`, `Φ([z])ₖ = ‖zₖ‖²/‖z‖²`, sends the **regular stratum**
(every coordinate positive) into the open simplex. Its differential kills the orbit directions
of the coordinate-phase torus — the **vertical space** at `x` — and on the Fubini–Study
orthogonal complement, the **horizontal space**, it is an isometry onto Fisher–Rao:

    `g_FS(u, v) = g_FR(dΦₓ u, dΦₓ v)`   for `u` horizontal at `x` and any `v`,

with constant one in the normalisation of `Projectivization.fsMetric` (the round unit sphere
for `ℂℙ¹`, Gram matrix `4 • 1` at a chart origin). The manifold statement is the vector-level
identity of `Analysis/InformationGeometry/FubiniStudyFisherRao.lean` read in an affine chart:
the point is the ray of `ψ = insertOne i w`, a chart direction `u` lifts to `insertZero i u`,
and `fsMetric` at the point is `fsInnerHom ψ` on the lifts (★ `fsMetric_eq_fsInnerHom`, the
standard formula `4 (Re ⟪δψ, δψ'⟫/‖ψ‖² − Re(⟪δψ, ψ⟫⟪ψ, δψ'⟫)/‖ψ‖⁴)`).

## Main declarations

* `Projectivization.insertZero i u` — the lift of a chart direction; `momentMap_chartInv` — the
  moment map in the chart is `bornWeight (normalize (insertOne i w))`.
* ★ `fsMetric_eq_fsInnerHom` — the Fubini–Study metric at `x` is the homogeneous formula on the
  lifts to `insertOne (idx x) (chartFun (idx x) x)`.
* `momentDeriv x` — the differential of the moment map at `x`, with `hasMFDerivAt_momentMap` and
  `mfderiv_momentMap`; `momentDeriv_apply` — it is the Born displacement of the horizontal lift;
  `sum_momentDeriv` — it is tangent to the simplex; `momentDeriv_torusField` and
  `momentDeriv_eq_zero_of_mem_verticalSpace` — it kills the vertical space.
* `verticalSpace x`, `horizontalSpace x` — the torus-orbit directions and their `fsMetric`-orthogonal
  complement; ★ `mem_horizontalSpace_iff` — horizontal means every `conj (wⱼ) uⱼ` is real in the
  chart, i.e. the direction moves moduli and not phases.
* `regularStratum`, `toOpenSimplex` — the moment map into `OpenSimplex (Fin (n + 1))`.
* ★★ `fsMetric_eq_fisherRaoInner` — **the bridge**: on the regular stratum, for `u` horizontal,
  `fsMetric x u v = fisherRaoInner (toOpenSimplex x) (momentDeriv x u) (momentDeriv x v)`.

## The constant

None is assumed: `fsMetric` is `ω_FS(J·, ·)` for the repository's Fubini–Study form, whose Gram
matrix at a chart origin is `4 • 1` (`toMatrix_fsModelMetric_zero`), and the `4` on the Fisher–Rao
side is the derivative of `‖·‖²`. They agree, so the constant is `1`. In the normalisation
`‖δψ‖² − ‖⟪ψ, δψ⟫‖²` of Bengtsson–Życzkowski the same statement reads `4 g_FS = g_FR ∘ dΦ`.

## Implementation notes

The tangent space of `ℂℙⁿ` at `x` is the model `Fin n → ℂ` (the chart's own coordinates), and
`fsMetric x` is by definition `fsModelMetric (chartFun (idx x) x)`. The differential
`momentDeriv x` and the vertical/horizontal spaces are therefore stated on the model space; a
tangent vector `u : TangentSpace 𝓘(ℝ, Fin n → ℂ) x` is used in them directly, as
`torusField` already is.

## References

* S. L. Braunstein, C. M. Caves, Phys. Rev. Lett. 72, 3439 (1994).
* I. Bengtsson, K. Życzkowski, *Geometry of Quantum States*, 2nd ed., §§4.4, 14.2.
* `Analysis/InformationGeometry/FubiniStudyFisherRao.lean` (the vector-level bridge);
  `Instances/ProjectiveSpaceMomentMap.lean` (`torusField`, the chart derivatives);
  `Instances/ProjectiveSpaceFubiniStudyRiemannian.lean` (`fsMetric`, `fsModelMetric`);
  Physlib PR #1652; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Kahler DifferentialForm ComplexConjugate FisherRao

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-! ### Lifts of chart directions -/

/-- Insert `0` in slot `i`: the lift of a direction in the `i`-th affine chart. -/
def insertZero (i : Fin (n + 1)) (u : Fin n → ℂ) : Ambient n :=
  WithLp.toLp 2 (i.insertNth 0 u)

@[simp]
lemma insertZero_apply_same (i : Fin (n + 1)) (u : Fin n → ℂ) : insertZero i u i = 0 := by
  simp [insertZero]

@[simp]
lemma insertZero_apply_succAbove (i : Fin (n + 1)) (u : Fin n → ℂ) (j : Fin n) :
    insertZero i u (i.succAbove j) = u j := by
  simp [insertZero]

theorem inner_insertZero_insertZero (i : Fin (n + 1)) (u v : Fin n → ℂ) :
    inner ℂ (insertZero i u) (insertZero i v) = inner ℂ (toLpCLM u) (toLpCLM v) := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem inner_insertZero_insertOne (i : Fin (n + 1)) (u w : Fin n → ℂ) :
    inner ℂ (insertZero i u) (insertOne i w) = inner ℂ (toLpCLM u) (toLpCLM w) := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem inner_insertOne_insertZero (i : Fin (n + 1)) (w u : Fin n → ℂ) :
    inner ℂ (insertOne i w) (insertZero i u) = inner ℂ (toLpCLM w) (toLpCLM u) := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem norm_insertOne_sq (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ‖insertOne i w‖ ^ 2 = 1 + ‖toLpCLM w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp

theorem norm_insertOne_sq_eq_chartDen (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ‖insertOne i w‖ ^ 2 = chartDen w := by
  rw [norm_insertOne_sq, chartDen, EuclideanSpace.norm_sq_eq]
  simp

/-- The moment map in the `i`-th chart is the Born weight of the normalised lift. -/
theorem momentMap_chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    momentMap (chartInv i w) k = bornWeight (normalize (insertOne i w)) k := by
  rw [chartInv, momentMap_mk, bornWeight_normalize]

/-! ### ★ The Fubini–Study metric on the lifts -/

/-- The model metric at `w` is the homogeneous Fubini–Study formula on the lifts to
`insertOne i w`. -/
theorem fsModelMetric_eq_fsInnerHom (i : Fin (n + 1)) (w u v : Fin n → ℂ) :
    fsModelMetric w u v = fsInnerHom (insertOne i w) (insertZero i u) (insertZero i v) := by
  have hu : toLpCLM (Complex.I • u) = Complex.I • toLpCLM u := by
    ext k
    simp
  have h4 : ‖insertOne i w‖ ^ 4 = (‖insertOne i w‖ ^ 2) ^ 2 := by ring
  have hD : 1 + ‖toLpCLM w‖ ^ 2 ≠ 0 := by positivity
  rw [fsModelMetric_apply, fsModelForm_apply, hu, inner_smul_left, inner_smul_left,
    Complex.conj_I, fsInnerHom, inner_insertZero_insertZero, inner_insertZero_insertOne,
    inner_insertOne_insertZero, h4, norm_insertOne_sq]
  simp only [neg_mul, Complex.mul_im, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.mul_re]
  field_simp
  ring

/-- ★ **The Fubini–Study metric at `x` is the homogeneous formula on the lifts**: with
`ψ = insertOne (idx x) (chartFun (idx x) x)` a representative of `x` and `insertZero (idx x) u`
the lift of a tangent vector `u`,

    `fsMetric x u v = 4 (Re ⟪δu, δv⟫ / ‖ψ‖² − Re(⟪δu, ψ⟫ ⟪ψ, δv⟫) / ‖ψ‖⁴)`.

This identifies `fsMetric` with the Fubini–Study metric as usually written on lifts. -/
theorem fsMetric_eq_fsInnerHom (x : ℙ ℂ (Ambient n)) (u v : Fin n → ℂ) :
    fsMetric x u v
      = fsInnerHom (insertOne (idx x) (chartFun (idx x) x)) (insertZero (idx x) u)
          (insertZero (idx x) v) :=
  fsModelMetric_eq_fsInnerHom (idx x) (chartFun (idx x) x) u v

/-! ### The differential of the moment map -/

/-- The derivative of the numerator `‖insertOne i w k‖²` of the `k`-th moment coordinate in the
`i`-th chart: `0` for `k = i` and `normSqCoordDeriv j w` for `k = i.succAbove j`. -/
def momentNumDeriv (i : Fin (n + 1)) (w : Fin n → ℂ) : Fin (n + 1) → (Fin n → ℂ) →L[ℝ] ℝ :=
  i.insertNth 0 fun j => normSqCoordDeriv j w

theorem momentNumDeriv_apply (i : Fin (n + 1)) (w u : Fin n → ℂ) (k : Fin (n + 1)) :
    momentNumDeriv i w k u = 2 * (conj (insertOne i w k) * insertZero i u k).re := by
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [momentNumDeriv]
  · intro j
    simp only [momentNumDeriv, Fin.insertNth_apply_succAbove, insertOne_apply_succAbove,
      insertZero_apply_succAbove, normSqCoordDeriv_apply, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring

theorem hasFDerivAt_momentNum (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    HasFDerivAt (fun w : Fin n → ℂ => ‖insertOne i w k‖ ^ 2) (momentNumDeriv i w k) w := by
  refine Fin.succAboveCases i ?_ ?_ k
  · have : (fun w : Fin n → ℂ => ‖insertOne i w i‖ ^ 2) = fun _ => (1 : ℝ) := by
      funext w
      simp
    rw [this]
    simpa [momentNumDeriv] using hasFDerivAt_const (1 : ℝ) w
  · intro j
    have : (fun w : Fin n → ℂ => ‖insertOne i w (i.succAbove j)‖ ^ 2)
        = fun w : Fin n → ℂ => ‖w j‖ ^ 2 := by
      funext w
      simp
    rw [this]
    simpa [momentNumDeriv] using hasFDerivAt_normSq_coord j w

/-- The derivative of the `k`-th moment coordinate in the `i`-th chart, from the product rule
for `‖insertOne i w k‖² · (chartDen w)⁻¹`. -/
def momentChartCoordDeriv (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    (Fin n → ℂ) →L[ℝ] ℝ :=
  ‖insertOne i w k‖ ^ 2
      • ((ContinuousLinearMap.toSpanSingleton ℝ (-(chartDen w ^ 2)⁻¹)).comp (chartDenDeriv w))
    + (chartDen w)⁻¹ • momentNumDeriv i w k

theorem momentMap_chartInv_eq_mul_inv (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    momentMap (chartInv i w) k = ‖insertOne i w k‖ ^ 2 * (chartDen w)⁻¹ := by
  rw [chartInv, momentMap_mk, norm_insertOne_sq_eq_chartDen, div_eq_mul_inv]

theorem hasFDerivAt_momentMap_chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    HasFDerivAt (fun w : Fin n → ℂ => momentMap (chartInv i w) k) (momentChartCoordDeriv i w k)
      w := by
  simp only [momentMap_chartInv_eq_mul_inv]
  have hinv : HasFDerivAt (fun w : Fin n → ℂ => (chartDen w)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(chartDen w ^ 2)⁻¹)).comp (chartDenDeriv w)) w :=
    (hasFDerivAt_inv (chartDen_pos w).ne').comp w (hasFDerivAt_chartDen w)
  exact (hasFDerivAt_momentNum i w k).mul hinv

theorem chartDenDeriv_apply' (i : Fin (n + 1)) (w u : Fin n → ℂ) :
    chartDenDeriv w u = 2 * (inner ℂ (insertOne i w) (insertZero i u) : ℂ).re := by
  rw [inner_insertOne_insertZero, PiLp.inner_apply, Complex.re_sum, Finset.mul_sum, chartDenDeriv,
    sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normSqCoordDeriv_apply, toLpCLM_apply, toLpCLM_apply, RCLike.inner_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The `k`-th coordinate of the chart derivative is the Born displacement of the horizontal
lift. -/
theorem momentChartCoordDeriv_apply (i : Fin (n + 1)) (w u : Fin n → ℂ) (k : Fin (n + 1)) :
    momentChartCoordDeriv i w k u
      = bornDeriv (normalize (insertOne i w)) (horizontalLift (insertOne i w) (insertZero i u))
          k := by
  rw [bornDeriv_normalize_horizontalLift, momentChartCoordDeriv, add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, momentNumDeriv_apply,
    chartDenDeriv_apply' i, ← norm_insertOne_sq_eq_chartDen]
  have hD : 0 < ‖insertOne i w‖ ^ 2 := by
    rw [norm_insertOne_sq_eq_chartDen]; exact chartDen_pos w
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The differential of the moment map at `x`, as a continuous linear map from the model tangent
space `Fin n → ℂ` to `Fin (n + 1) → ℝ`: coordinatewise the chart derivatives at
`chartFun (idx x) x`. -/
def momentDeriv (x : ℙ ℂ (Ambient n)) : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun k => momentChartCoordDeriv (idx x) (chartFun (idx x) x) k

theorem continuous_momentMap_pi : Continuous (momentMap (N := n + 1)) :=
  continuous_pi fun k => continuous_momentMap k

/-- **The moment map is differentiable, with differential `momentDeriv`.** -/
theorem hasMFDerivAt_momentMap (x : ℙ ℂ (Ambient n)) :
    HasMFDerivAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin (n + 1) → ℝ))
      momentMap x (momentDeriv x) := by
  refine ⟨continuous_momentMap_pi.continuousAt, ?_⟩
  have hw : writtenInExtChartAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ (Fin (n + 1) → ℝ)) x momentMap
      = fun w => fun k => momentMap (chartInv (idx x) w) k := by
    funext w
    simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id, extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    rfl
  rw [hw]
  exact (hasFDerivAt_pi.mpr fun k =>
    hasFDerivAt_momentMap_chartInv (idx x) (chartFun (idx x) x) k).hasFDerivWithinAt

theorem mfderiv_momentMap (x : ℙ ℂ (Ambient n)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin (n + 1) → ℝ))
      momentMap x = momentDeriv x :=
  (hasMFDerivAt_momentMap x).mfderiv

/-- The differential of the moment map is the Born displacement of the horizontal lift of the
direction. -/
theorem momentDeriv_apply (x : ℙ ℂ (Ambient n)) (u : Fin n → ℂ) (k : Fin (n + 1)) :
    momentDeriv x u k
      = bornDeriv (normalize (insertOne (idx x) (chartFun (idx x) x)))
          (horizontalLift (insertOne (idx x) (chartFun (idx x) x)) (insertZero (idx x) u)) k := by
  rw [momentDeriv, ContinuousLinearMap.pi_apply, momentChartCoordDeriv_apply]

/-- The differential of the moment map is tangent to the simplex: its coordinates sum to zero. -/
theorem sum_momentDeriv (x : ℙ ℂ (Ambient n)) (u : Fin n → ℂ) :
    ∑ k, momentDeriv x u k = 0 := by
  simp only [momentDeriv_apply]
  rw [sum_bornDeriv, inner_normalize_horizontalLift (insertOne_ne_zero _ _), Complex.zero_re,
    mul_zero]

/-! ### The vertical and horizontal spaces -/

/-- The vertical space at `x`: the span of the torus-orbit directions, in the model tangent
space. -/
def verticalSpace (x : ℙ ℂ (Ambient n)) : Submodule ℝ (Fin n → ℂ) :=
  Submodule.span ℝ (Set.range fun θ : Fin (n + 1) → ℝ => tangentToModel (torusField θ x))

/-- The horizontal space at `x`: the `fsMetric`-orthogonal complement of the vertical space.
`fsMetric x` is, by definition, the model metric at the chart coordinate of `x`, so the
orthogonal complement is taken for `fsModelMetric (chartFun (idx x) x)`. -/
def horizontalSpace (x : ℙ ℂ (Ambient n)) : Submodule ℝ (Fin n → ℂ) :=
  LinearMap.BilinForm.orthogonal (fsModelMetric (chartFun (idx x) x)) (verticalSpace x)

theorem torusField_mem_verticalSpace (θ : Fin (n + 1) → ℝ) (x : ℙ ℂ (Ambient n)) :
    tangentToModel (torusField θ x) ∈ verticalSpace x :=
  Submodule.subset_span ⟨θ, rfl⟩

/-- A tangent vector is horizontal iff it is `fsMetric`-orthogonal to every torus-orbit
direction. -/
theorem mem_horizontalSpace_iff_forall (x : ℙ ℂ (Ambient n)) (u : Fin n → ℂ) :
    u ∈ horizontalSpace x ↔ ∀ θ : Fin (n + 1) → ℝ, fsMetric x (torusField θ x) u = 0 := by
  rw [horizontalSpace, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h θ
    exact h _ (torusField_mem_verticalSpace θ x)
  · intro h v hv
    refine Submodule.span_induction (p := fun v _ => fsModelMetric (chartFun (idx x) x) v u = 0)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨θ, rfl⟩
      exact h θ
    · simp
    · intro a b _ _ ha hb
      simp [ha, hb]
    · intro c a _ ha
      simp [ha]

/-- The metric of a torus-orbit direction against `u` is minus the derivative of the chart
Hamiltonian along `i·u`: `g(X_θ, u) = ω(J X_θ, u) = −ω(X_θ, J u) = −dH_θ(J u)`, by the
`J`-invariance of `ω`. -/
theorem fsModelMetric_torusChartField (i : Fin (n + 1)) (θ : Fin (n + 1) → ℝ) (w u : Fin n → ℂ) :
    fsModelMetric w (torusChartField i θ w) u = -torusChartHamDeriv i θ w (Complex.I • u) := by
  have hneg : fsModelForm w ![-torusChartField i θ w, Complex.I • u]
      = -fsModelForm w ![torusChartField i θ w, Complex.I • u] :=
    apply_neg_left (flatFamily (fsModelForm w)) 0 _ _
  rw [fsModelMetric_apply, ← fsModelForm_smul_I_smul_I w (Complex.I • torusChartField i θ w) u,
    smul_smul, Complex.I_mul_I, neg_one_smul, hneg, fsModelForm_torusChartField]

/-- The pairing `2 (Re wⱼ Re (i uⱼ) + Im wⱼ Im (i uⱼ))` is `−2 Im (conj wⱼ · uⱼ)`. -/
theorem two_mul_re_add_im_I (a b : ℂ) :
    2 * (a.re * (Complex.I * b).re + a.im * (Complex.I * b).im) = -2 * (conj a * b).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The metric of a torus-orbit direction against `u`, in the chart: with `Iⱼ = Im (conj wⱼ · uⱼ)`
and `N = θᵢ + Σⱼ θ_{s j} ‖wⱼ‖²`, it is `4 (D⁻¹ Σⱼ θ_{s j} Iⱼ − N D⁻² Σⱼ Iⱼ)`. -/
theorem fsModelMetric_torusChartField_eq (i : Fin (n + 1)) (θ : Fin (n + 1) → ℝ)
    (w u : Fin n → ℂ) :
    fsModelMetric w (torusChartField i θ w) u
      = 4 * ((chartDen w)⁻¹ * ∑ j, θ (i.succAbove j) * (conj (w j) * u j).im
          - torusChartNum i θ w * (chartDen w ^ 2)⁻¹ * ∑ j, (conj (w j) * u j).im) := by
  have hA : ∑ j, θ (i.succAbove j)
      * (2 * ((w j).re * ((Complex.I • u) j).re + (w j).im * ((Complex.I • u) j).im))
      = -2 * ∑ j, θ (i.succAbove j) * (conj (w j) * u j).im := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, two_mul_re_add_im_I]
    ring
  have hB : ∑ j, 2 * ((w j).re * ((Complex.I • u) j).re + (w j).im * ((Complex.I • u) j).im)
      = -2 * ∑ j, (conj (w j) * u j).im := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, two_mul_re_add_im_I]
  rw [fsModelMetric_torusChartField, torusChartHamDeriv_apply, hA, hB]
  ring

/-- ★ **Horizontal means moduli-only.** A tangent vector `u` at `x` is `fsMetric`-orthogonal to
every torus-orbit direction iff, in the chart at `x`, every product `conj (wⱼ) uⱼ` is real — the
direction changes the moduli of the homogeneous coordinates and none of their phases. -/
theorem mem_horizontalSpace_iff (x : ℙ ℂ (Ambient n)) (u : Fin n → ℂ) :
    u ∈ horizontalSpace x ↔ ∀ j, (conj (chartFun (idx x) x j) * u j).im = 0 := by
  rw [mem_horizontalSpace_iff_forall]
  have key : ∀ θ, fsMetric x (torusField θ x) u
      = 4 * ((chartDen (chartFun (idx x) x))⁻¹
            * ∑ j, θ ((idx x).succAbove j) * (conj (chartFun (idx x) x j) * u j).im
          - torusChartNum (idx x) θ (chartFun (idx x) x) * (chartDen (chartFun (idx x) x) ^ 2)⁻¹
            * ∑ j, (conj (chartFun (idx x) x j) * u j).im) :=
    fun θ => fsModelMetric_torusChartField_eq (idx x) θ (chartFun (idx x) x) u
  simp only [key]
  set i := idx x
  set w := chartFun i x
  have hD : chartDen w ≠ 0 := (chartDen_pos w).ne'
  constructor
  · intro h
    -- `θ = Pi.single i 1` gives `Σⱼ Iⱼ = 0`
    have hS : ∑ j, (conj (w j) * u j).im = 0 := by
      have h0 := h (Pi.single i 1)
      have hθ : ∀ j, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) (i.succAbove j) = 0 :=
        fun j => Pi.single_eq_of_ne (Fin.succAbove_ne i j) 1
      have hN : torusChartNum i (Pi.single i 1) w = 1 := by
        simp [torusChartNum]
      simp only [hθ, zero_mul, Finset.sum_const_zero, mul_zero, zero_sub, hN, one_mul,
        mul_eq_zero, neg_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (pow_ne_zero 2 hD)
      · exact h0
    intro j
    have hj := h (Pi.single (i.succAbove j) 1)
    have hθ : ∀ j', (Pi.single (i.succAbove j) (1 : ℝ) : Fin (n + 1) → ℝ) (i.succAbove j')
        = if j' = j then 1 else 0 := by
      intro j'
      by_cases hjj : j' = j
      · subst hjj; simp
      · rw [Pi.single_eq_of_ne (fun h => hjj (Fin.succAbove_right_injective h)), if_neg hjj]
    simp only [hθ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hS,
      mul_zero, sub_zero, mul_eq_zero, inv_eq_zero, hD, OfNat.ofNat_ne_zero, false_or] at hj
    exact hj
  · intro h θ
    simp [h]

/-- The differential of the moment map kills every torus-orbit direction. -/
theorem momentDeriv_torusField (θ : Fin (n + 1) → ℝ) (x : ℙ ℂ (Ambient n)) :
    momentDeriv x (tangentToModel (torusField θ x)) = 0 := by
  funext k
  rw [momentDeriv_apply, bornDeriv_normalize_horizontalLift, Pi.zero_apply]
  -- both real parts vanish: `conj (wⱼ) · (i c wⱼ)` is purely imaginary
  have hre : ∀ k, (conj (insertOne (idx x) (chartFun (idx x) x) k)
      * insertZero (idx x) (tangentToModel (torusField θ x)) k).re = 0 := by
    intro k
    refine Fin.succAboveCases (idx x) ?_ ?_ k
    · simp
    · intro j
      simp only [insertOne_apply_succAbove, insertZero_apply_succAbove, tangentToModel, torusField,
        torusChartField]
      have hk : conj (chartFun (idx x) x j) * chartFun (idx x) x j
          = (‖chartFun (idx x) x j‖ : ℂ) ^ 2 := RCLike.conj_mul _
      rw [show conj (chartFun (idx x) x j)
            * (Complex.I * ((θ ((idx x).succAbove j) - θ (idx x) : ℝ) : ℂ) * chartFun (idx x) x j)
          = Complex.I * ((θ ((idx x).succAbove j) - θ (idx x) : ℝ) : ℂ)
            * (conj (chartFun (idx x) x j) * chartFun (idx x) x j) by ring, hk, mul_assoc,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.I_mul_re, Complex.ofReal_im, neg_zero]
  have hsum : (inner ℂ (insertOne (idx x) (chartFun (idx x) x))
      (insertZero (idx x) (tangentToModel (torusField θ x))) : ℂ).re = 0 := by
    rw [PiLp.inner_apply, Complex.re_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [RCLike.inner_apply, mul_comm]; exact hre k
  rw [hre, hsum]
  simp

/-- The differential of the moment map vanishes on the vertical space. -/
theorem momentDeriv_eq_zero_of_mem_verticalSpace (x : ℙ ℂ (Ambient n)) {v : Fin n → ℂ}
    (hv : v ∈ verticalSpace x) : momentDeriv x v = 0 := by
  refine Submodule.span_induction (p := fun v _ => momentDeriv x v = 0) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨θ, rfl⟩
    exact momentDeriv_torusField θ x
  · simp
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c a _ ha
    simp [ha]

/-! ### The regular stratum and the bridge -/

/-- The regular stratum: the points at which every moment coordinate is positive, i.e. no
homogeneous coordinate vanishes. The moment map sends it into the open simplex. -/
def regularStratum : Set (ℙ ℂ (Ambient n)) := {x | ∀ k, 0 < momentMap x k}

/-- The moment map on the regular stratum, as a point of the open simplex. -/
def toOpenSimplex (x : ℙ ℂ (Ambient n)) (hx : x ∈ regularStratum) : OpenSimplex (Fin (n + 1)) where
  val := momentMap x
  pos := hx
  sum_one := momentMap_sum_eq_one x

@[simp]
theorem toOpenSimplex_val (x : ℙ ℂ (Ambient n)) (hx : x ∈ regularStratum) :
    (toOpenSimplex x hx).val = momentMap x :=
  rfl

theorem chartInv_idx_chartFun (x : ℙ ℂ (Ambient n)) :
    chartInv (idx x) (chartFun (idx x) x) = x :=
  chartInv_chartFun (idx x) x (idx_spec x)

/-- On the regular stratum, no coordinate of the chart representative vanishes. -/
theorem insertOne_chartFun_ne_zero {x : ℙ ℂ (Ambient n)} (hx : x ∈ regularStratum)
    (k : Fin (n + 1)) : insertOne (idx x) (chartFun (idx x) x) k ≠ 0 := by
  intro h0
  have h := hx k
  have hmx : momentMap x k = momentMap (chartInv (idx x) (chartFun (idx x) x)) k := by
    rw [chartInv_idx_chartFun]
  rw [hmx, momentMap_chartInv, bornWeight_normalize, h0] at h
  simp at h

/-- ★★ **The bridge.** On the regular stratum, for `u` horizontal at `x` and any `v`, the
Fubini–Study metric of `u` and `v` is the Fisher–Rao inner product of their images under the
differential of the moment map:

    `fsMetric x u v = fisherRaoInner (toOpenSimplex x) (momentDeriv x u) (momentDeriv x v)`.

The constant is one: `fsMetric` is normalised so that `ℂℙ¹` is the unit round sphere, and in
that normalisation `4 g_FS` is the quantum Fisher information, which the coordinate readout
attains exactly on the horizontal directions. -/
theorem fsMetric_eq_fisherRaoInner {x : ℙ ℂ (Ambient n)} (hx : x ∈ regularStratum)
    {u : Fin n → ℂ} (hu : u ∈ horizontalSpace x) (v : Fin n → ℂ) :
    fsMetric x u v
      = (toOpenSimplex x hx).fisherRaoInner (momentDeriv x u) (momentDeriv x v) := by
  have hψ0 : insertOne (idx x) (chartFun (idx x) x) ≠ 0 := insertOne_ne_zero _ _
  have hk : ∀ k, insertOne (idx x) (chartFun (idx x) x) k ≠ 0 := insertOne_chartFun_ne_zero hx
  have hval : (toOpenSimplex x hx).val
      = bornWeight (normalize (insertOne (idx x) (chartFun (idx x) x))) := by
    funext k
    have hmx : momentMap x k = momentMap (chartInv (idx x) (chartFun (idx x) x)) k := by
      rw [chartInv_idx_chartFun]
    rw [toOpenSimplex_val, hmx, momentMap_chartInv]
  have hu' : ∀ k, (conj (insertOne (idx x) (chartFun (idx x) x) k) * insertZero (idx x) u k).im
      = 0 := by
    intro k
    refine Fin.succAboveCases (idx x) ?_ ?_ k
    · simp
    · intro j
      simp only [insertOne_apply_succAbove, insertZero_apply_succAbove]
      exact (mem_horizontalSpace_iff x u).mp hu j
  have hderiv : ∀ z : Fin n → ℂ, momentDeriv x z
      = bornDeriv (normalize (insertOne (idx x) (chartFun (idx x) x)))
          (horizontalLift (insertOne (idx x) (chartFun (idx x) x)) (insertZero (idx x) z)) := by
    intro z
    funext k
    exact momentDeriv_apply x z k
  rw [fsMetric_eq_fsInnerHom, hderiv, hderiv,
    ← fisherRaoInner_bornDeriv_normalize hψ0 hk hu' (insertZero (idx x) v)]
  simp only [OpenSimplex.fisherRaoInner, hval, bornSimplex_val]

end Projectivization
