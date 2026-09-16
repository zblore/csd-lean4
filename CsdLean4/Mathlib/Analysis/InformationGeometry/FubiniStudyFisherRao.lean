/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InformationGeometry.FisherRao
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Born map is an isometry from the horizontal Fubini–Study directions to Fisher–Rao

**Category:** 1-Mathlib (CSD-free; finite-dimensional inner-product algebra on `EuclideanSpace ℂ ι`
and the open simplex of `FisherRao.lean`).

A unit vector `ψ : ℂ^ι` has Born weights `pᵢ = ‖ψᵢ‖²`, a point of the open probability simplex
when no coordinate vanishes. Moving `ψ` in a direction `u` moves the weights by
`dpᵢ = 2 Re(ψ̄ᵢ uᵢ)`, and the Fisher–Rao inner product of two such displacements is

    `Σᵢ dpᵢ dp'ᵢ / pᵢ`.

Write `u` as `uᵢ = aᵢ ψᵢ` coordinate by coordinate. When every `aᵢ` is real (the direction is
**horizontal**: it changes moduli, not phases), `dpᵢ = 2 aᵢ pᵢ` and the sum collapses to
`4 Σᵢ ūᵢ vᵢ = 4 ⟪u, v⟫`. This is the Fubini–Study inner product of the two directions, in the
normalisation where the metric of `ℂℙ¹` is the unit round sphere and `4·g_FS` is the quantum
Fisher information. So along horizontal directions the Born map is an isometry from Fubini–Study
to Fisher–Rao, with constant one.

Along a general direction the phases also move, Fisher–Rao only sees the moduli, and the
inequality `Σᵢ dpᵢ²/pᵢ ≤ 4 ‖u‖²` records what is lost: the classical Fisher information of the
coordinate readout is at most the quantum Fisher information, with equality exactly on the
horizontal directions (Braunstein–Caves for the computational-basis measurement).

## Main declarations

* `FisherRao.bornWeight ψ i = ‖ψ i‖ ^ 2`, `FisherRao.bornSimplex` — the Born weights as a point of
  `OpenSimplex ι` for a unit vector with no vanishing coordinate.
* `FisherRao.bornDeriv ψ u i = 2 Re(ψ̄ᵢ uᵢ)` and `hasFDerivAt_bornWeight` — it is the differential of
  `ψ ↦ ‖ψ i‖ ^ 2`; `sum_bornDeriv` — the displacement sums to `2 Re ⟪ψ, u⟫`, so it is tangent to the
  simplex whenever `u` is tangent to the unit sphere.
* `FisherRao.IsHorizontal ψ u` — every `ψ̄ᵢ uᵢ` is real.
* ★ `fisherRaoInner_bornDeriv` — for horizontal `u` and any `v`,
  `fisherRaoInner (bornSimplex ψ) (bornDeriv ψ u) (bornDeriv ψ v) = 4 * Re ⟪u, v⟫`.
* ★ `fisherInfo_bornDeriv_le` — `fisherInfo (bornWeight ψ) (bornDeriv ψ u) ≤ 4 * ‖u‖ ^ 2` for every
  `u`, and `fisherInfo_bornDeriv_eq_iff` — with equality iff `u` is horizontal.
* Homogeneous coordinates, for the affine charts of `ℂℙⁿ`: `normalize ψ`, `horizontalLift ψ u`,
  `fsInnerHom ψ u v` (the Fubini–Study inner product at a nonzero `ψ`), ★ `inner_horizontalLift`
  (`fsInnerHom` is `4 Re ⟪·,·⟫` of the horizontal lifts) and ★ `fisherRaoInner_bornDeriv_normalize`,
  the bridge stated at `normalize ψ`.

## The constant

The right-hand side `4 * Re ⟪u, v⟫` is the Fubini–Study metric of the projective space in the
normalisation of `Projectivization.fsMetric` (`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`,
where the Gram matrix at a chart origin is `4 • 1`), evaluated on horizontal lifts. In the
normalisation `‖u‖² − ‖⟪ψ, u⟫‖²` of Bengtsson–Życzkowski the constant is `4`, and that quantity
times `4` is the quantum Fisher information of a pure-state family. No constant is assumed here;
the `4` is the derivative of `‖·‖²`.

## References

* S. L. Braunstein, C. M. Caves, *Statistical distance and the geometry of quantum states*,
  Phys. Rev. Lett. 72, 3439 (1994).
* I. Bengtsson, K. Życzkowski, *Geometry of Quantum States*, 2nd ed., §§4.4, 14.2.
* Physlib PR #1652 (`FisherRao.lean`, mirrored in this directory); the completed-work ledger.
-/

@[expose] public section

noncomputable section

open Finset ComplexConjugate

namespace FisherRao

variable {ι : Type*}

/-! ## The Born weights of a vector, coordinate by coordinate -/

/-- The Born weight of the `i`-th coordinate: `‖ψ i‖ ^ 2`. -/
def bornWeight (ψ : EuclideanSpace ℂ ι) (i : ι) : ℝ := ‖ψ i‖ ^ 2

theorem bornWeight_nonneg (ψ : EuclideanSpace ℂ ι) (i : ι) : 0 ≤ bornWeight ψ i :=
  sq_nonneg _

theorem bornWeight_pos (ψ : EuclideanSpace ℂ ι) {i : ι} (h : ψ i ≠ 0) : 0 < bornWeight ψ i :=
  pow_pos (norm_pos_iff.mpr h) 2

/-! ## The differential of the Born map -/

/-- The displacement of the `i`-th Born weight along `u`: `2 Re(ψ̄ᵢ uᵢ)`. -/
def bornDeriv (ψ u : EuclideanSpace ℂ ι) (i : ι) : ℝ := 2 * (conj (ψ i) * u i).re

/-! ## Horizontal directions -/

/-- A direction `u` at `ψ` is **horizontal** when every `ψ̄ᵢ uᵢ` is real: it changes the moduli of
the coordinates and none of their phases. This is the Fubini–Study-orthogonal complement of the
orbit of the coordinate-phase torus. -/
def IsHorizontal (ψ u : EuclideanSpace ℂ ι) : Prop := ∀ i, (conj (ψ i) * u i).im = 0

/-- A direction whose coordinates are real multiples of those of `ψ` is horizontal. -/
theorem isHorizontal_of_forall_eq (ψ u : EuclideanSpace ℂ ι) (a : ι → ℝ)
    (hu : ∀ i, u i = (a i : ℂ) * ψ i) : IsHorizontal ψ u := by
  intro i
  rw [hu i]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The pointwise identity behind the bridge: for `ψᵢ ≠ 0` and `ψ̄ᵢ uᵢ` real,
`(2 Re(ψ̄ᵢ uᵢ)) (2 Re(ψ̄ᵢ vᵢ)) / ‖ψᵢ‖² = 4 Re(ūᵢ vᵢ)`. -/
theorem bornDeriv_mul_div_bornWeight (ψ u v : EuclideanSpace ℂ ι) {i : ι} (h0 : ψ i ≠ 0)
    (hu : (conj (ψ i) * u i).im = 0) :
    bornDeriv ψ u i * bornDeriv ψ v i / bornWeight ψ i = 4 * (inner ℂ (u i) (v i) : ℂ).re := by
  have hns : bornWeight ψ i = (ψ i).re ^ 2 + (ψ i).im ^ 2 := by
    rw [bornWeight, Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < (ψ i).re ^ 2 + (ψ i).im ^ 2 := by
    rw [← hns]; exact bornWeight_pos ψ h0
  simp only [bornDeriv, RCLike.inner_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at hu ⊢
  rw [hns, div_eq_iff hpos.ne']
  linear_combination (4 * ((ψ i).im * (v i).re - (ψ i).re * (v i).im)) * hu

/-- Pointwise: `(2 Re(ψ̄ᵢ uᵢ))² / ‖ψᵢ‖² ≤ 4 ‖uᵢ‖²`, since `Re z ≤ ‖z‖` and
`‖ψ̄ᵢ uᵢ‖ = ‖ψᵢ‖ ‖uᵢ‖`. -/
theorem bornDeriv_sq_div_bornWeight_le (ψ u : EuclideanSpace ℂ ι) {i : ι} (h0 : ψ i ≠ 0) :
    bornDeriv ψ u i ^ 2 / bornWeight ψ i ≤ 4 * ‖u i‖ ^ 2 := by
  have hpos : 0 < bornWeight ψ i := bornWeight_pos ψ h0
  rw [div_le_iff₀ hpos, bornDeriv, bornWeight, mul_pow]
  have h := abs_le.mp (Complex.abs_re_le_norm (conj (ψ i) * u i))
  have h2 : (conj (ψ i) * u i).re ^ 2 ≤ ‖ψ i‖ ^ 2 * ‖u i‖ ^ 2 := by
    rw [← mul_pow, ← Complex.norm_conj (ψ i), ← norm_mul]
    exact sq_le_sq' h.1 h.2
  nlinarith [h2]

/-- Pointwise equality in `bornDeriv_sq_div_bornWeight_le` forces `ψ̄ᵢ uᵢ` to be real. -/
theorem im_eq_zero_of_bornDeriv_sq_div_bornWeight_eq (ψ u : EuclideanSpace ℂ ι) {i : ι}
    (h0 : ψ i ≠ 0) (h : bornDeriv ψ u i ^ 2 / bornWeight ψ i = 4 * ‖u i‖ ^ 2) :
    (conj (ψ i) * u i).im = 0 := by
  have hpos : 0 < bornWeight ψ i := bornWeight_pos ψ h0
  rw [div_eq_iff hpos.ne', bornDeriv, bornWeight, mul_pow] at h
  have hz : ‖conj (ψ i) * u i‖ ^ 2 = ‖ψ i‖ ^ 2 * ‖u i‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, mul_pow]
  have hre : (conj (ψ i) * u i).re ^ 2 + (conj (ψ i) * u i).im ^ 2 = ‖conj (ψ i) * u i‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [sq_nonneg ((conj (ψ i) * u i).im)]

/-! ## Sums over the coordinates -/

variable [Fintype ι]

/-- The Born weights sum to `‖ψ‖ ^ 2`. -/
theorem sum_bornWeight (ψ : EuclideanSpace ℂ ι) : ∑ i, bornWeight ψ i = ‖ψ‖ ^ 2 :=
  (EuclideanSpace.norm_sq_eq ψ).symm

/-- The Born weights of a unit vector with no vanishing coordinate, as a point of the open
probability simplex. -/
def bornSimplex (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0) : OpenSimplex ι where
  val := bornWeight ψ
  pos i := bornWeight_pos ψ (h0 i)
  sum_one := by rw [sum_bornWeight, hψ, one_pow]

@[simp]
theorem bornSimplex_val (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0) :
    (bornSimplex ψ hψ h0).val = bornWeight ψ :=
  rfl

/-- `bornDeriv ψ · i` as a real continuous linear map: `2 ⟪ψ i, · i⟫_ℝ`. -/
def bornDerivCLM (ψ : EuclideanSpace ℂ ι) (i : ι) : EuclideanSpace ℂ ι →L[ℝ] ℝ :=
  2 • (innerSL ℝ (ψ i)).comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)

omit [Fintype ι] in
theorem bornDerivCLM_apply (ψ u : EuclideanSpace ℂ ι) (i : ι) :
    bornDerivCLM ψ i u = bornDeriv ψ u i := by
  simp [bornDerivCLM, bornDeriv, Complex.inner]
  ring

/-- **`bornDeriv` is the differential of the Born map**: `ψ ↦ ‖ψ i‖ ^ 2` has derivative
`bornDerivCLM ψ i` at `ψ`. -/
theorem hasFDerivAt_bornWeight (ψ : EuclideanSpace ℂ ι) (i : ι) :
    HasFDerivAt (fun φ : EuclideanSpace ℂ ι => bornWeight φ i) (bornDerivCLM ψ i) ψ :=
  ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).hasFDerivAt.norm_sq

/-- The displacement of the weights sums to `2 Re ⟪ψ, u⟫`; in particular it sums to zero — it is
tangent to the simplex — whenever `u` is tangent to the unit sphere at `ψ`. -/
theorem sum_bornDeriv (ψ u : EuclideanSpace ℂ ι) :
    ∑ i, bornDeriv ψ u i = 2 * (inner ℂ ψ u : ℂ).re := by
  simp only [bornDeriv, ← Finset.mul_sum, PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum,
    mul_comm]

/-- ★ **The bridge, at the vector level.** For a horizontal direction `u` and any direction `v`,
the Fisher–Rao inner product of the Born displacements is four times the real inner product of
the directions:

    `g_FR(dΦ u, dΦ v) = 4 Re ⟪u, v⟫`.

Only `u` needs to be horizontal; `v` is arbitrary. The `4` is the derivative of `‖·‖²`, and
`4 Re ⟪u, v⟫` is the Fubini–Study metric in the round-sphere normalisation. -/
theorem fisherRaoInner_bornDeriv (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0)
    {u : EuclideanSpace ℂ ι} (hu : IsHorizontal ψ u) (v : EuclideanSpace ℂ ι) :
    (bornSimplex ψ hψ h0).fisherRaoInner (bornDeriv ψ u) (bornDeriv ψ v)
      = 4 * (inner ℂ u v : ℂ).re := by
  simp only [OpenSimplex.fisherRaoInner, bornSimplex_val, PiLp.inner_apply, Complex.re_sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => bornDeriv_mul_div_bornWeight ψ u v (h0 i) (hu i)

/-- The Fisher–Rao quadratic form of a horizontal Born displacement is `4 ‖u‖ ^ 2`. -/
theorem fisherRaoSq_bornDeriv (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0)
    {u : EuclideanSpace ℂ ι} (hu : IsHorizontal ψ u) :
    (bornSimplex ψ hψ h0).fisherRaoSq (bornDeriv ψ u) = 4 * ‖u‖ ^ 2 := by
  rw [OpenSimplex.fisherRaoSq, fisherRaoInner_bornDeriv ψ hψ h0 hu u]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

/-! ## Braunstein–Caves for the coordinate readout -/

/-- ★ **The classical Fisher information of the coordinate readout is at most the quantum Fisher
information** `4 ‖u‖ ^ 2`, for every direction `u` (Braunstein–Caves, computational basis). -/
theorem fisherInfo_bornDeriv_le (ψ u : EuclideanSpace ℂ ι) (h0 : ∀ i, ψ i ≠ 0) :
    fisherInfo (bornWeight ψ) (bornDeriv ψ u) ≤ 4 * ‖u‖ ^ 2 := by
  rw [fisherInfo, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => bornDeriv_sq_div_bornWeight_le ψ u (h0 i)

/-- ★ **Equality in Braunstein–Caves holds exactly on the horizontal directions**: the coordinate
readout extracts the full quantum Fisher information of the direction `u` iff `u` changes only
the moduli of the coordinates. -/
theorem fisherInfo_bornDeriv_eq_iff (ψ u : EuclideanSpace ℂ ι) (h0 : ∀ i, ψ i ≠ 0) :
    fisherInfo (bornWeight ψ) (bornDeriv ψ u) = 4 * ‖u‖ ^ 2 ↔ IsHorizontal ψ u := by
  constructor
  · intro h
    rw [fisherInfo, EuclideanSpace.norm_sq_eq, Finset.mul_sum] at h
    have hle : ∀ i ∈ Finset.univ, bornDeriv ψ u i ^ 2 / bornWeight ψ i ≤ 4 * ‖u i‖ ^ 2 :=
      fun i _ => bornDeriv_sq_div_bornWeight_le ψ u (h0 i)
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp h
    exact fun i => im_eq_zero_of_bornDeriv_sq_div_bornWeight_eq ψ u (h0 i) (heq i (mem_univ i))
  · intro hu
    rw [fisherInfo, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := bornDeriv_mul_div_bornWeight ψ u u (h0 i) (hu i)
    rw [← pow_two] at this
    rw [this]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (u i)

/-! ## Homogeneous coordinates

A point of projective space is a ray `[ψ]` with `ψ ≠ 0`, and a direction at it is any vector
`u`; the pairs `(ψ, u)` and `(ψ, u + c ψ)` describe the same tangent vector. The unit vector on the
ray is `normalize ψ = ‖ψ‖⁻¹ • ψ`, and the **horizontal lift** of `u` removes the component of `u`
along `ψ` and rescales: `horizontalLift ψ u = ‖ψ‖⁻¹ • (u − (⟪ψ, u⟫/‖ψ‖²) ψ)`. In these terms the
Fubini–Study inner product of two directions is

    `fsInnerHom ψ u v = 4 (Re ⟪u, v⟫ / ‖ψ‖² − Re(⟪u, ψ⟫ ⟪ψ, v⟫) / ‖ψ‖⁴)`,

which is `4 Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫` (`inner_horizontalLift`), and the Born
weights of the ray are `‖ψ k‖² / ‖ψ‖²` with displacement
`2 (Re(ψ̄ₖ uₖ) / ‖ψ‖² − ‖ψ k‖² Re ⟪ψ, u⟫ / ‖ψ‖⁴)`. The bridge in this form
(`fisherRaoInner_bornDeriv_normalize`) is what the affine charts of `ℂℙⁿ` meet. -/

/-- The unit vector on the ray of `ψ`. -/
def normalize (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := (‖ψ‖ : ℂ)⁻¹ • ψ

theorem norm_normalize {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) : ‖normalize ψ‖ = 1 :=
  norm_smul_inv_norm hψ

theorem normalize_apply (ψ : EuclideanSpace ℂ ι) (k : ι) :
    normalize ψ k = (‖ψ‖ : ℂ)⁻¹ * ψ k :=
  rfl

theorem normalize_apply_ne_zero {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) {k : ι} (hk : ψ k ≠ 0) :
    normalize ψ k ≠ 0 := by
  rw [normalize_apply]
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hψ))) hk

/-- The Born weights of the ray of `ψ`: `‖ψ k‖² / ‖ψ‖²`. -/
theorem bornWeight_normalize (ψ : EuclideanSpace ℂ ι) (k : ι) :
    bornWeight (normalize ψ) k = ‖ψ k‖ ^ 2 / ‖ψ‖ ^ 2 := by
  rw [bornWeight, normalize_apply, norm_mul, norm_inv, Complex.norm_real, norm_norm, mul_pow,
    inv_pow, div_eq_inv_mul]

/-- The horizontal lift of a direction `u` at `ψ`: the component of `u` orthogonal to `ψ`, scaled
by `‖ψ‖⁻¹`. -/
def horizontalLift (ψ u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (‖ψ‖ : ℂ)⁻¹ • (u - (inner ℂ ψ u / (‖ψ‖ : ℂ) ^ 2) • ψ)

theorem horizontalLift_apply (ψ u : EuclideanSpace ℂ ι) (k : ι) :
    horizontalLift ψ u k = (‖ψ‖ : ℂ)⁻¹ * (u k - (inner ℂ ψ u / (‖ψ‖ : ℂ) ^ 2) * ψ k) :=
  rfl

/-- The horizontal lift is orthogonal to `ψ`, so it is tangent to the unit sphere at
`normalize ψ`. -/
theorem inner_normalize_horizontalLift {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (u : EuclideanSpace ℂ ι) : inner ℂ (normalize ψ) (horizontalLift ψ u) = 0 := by
  have hN : (‖ψ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hψ)
  have hself : inner ℂ ψ ψ = (‖ψ‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K ψ
  simp only [normalize, horizontalLift, inner_smul_left, inner_smul_right, inner_sub_right, hself,
    map_inv₀, Complex.conj_ofReal]
  field_simp
  ring

/-- The Fubini–Study inner product of two directions at `ψ`, in homogeneous coordinates:
`4 (Re ⟪u, v⟫ / ‖ψ‖² − Re(⟪u, ψ⟫ ⟪ψ, v⟫) / ‖ψ‖⁴)`. -/
def fsInnerHom (ψ u v : EuclideanSpace ℂ ι) : ℝ :=
  4 * ((inner ℂ u v : ℂ).re / ‖ψ‖ ^ 2 - (inner ℂ u ψ * inner ℂ ψ v : ℂ).re / ‖ψ‖ ^ 4)

/-- The inner product of two horizontal lifts, as a complex number. -/
theorem inner_horizontalLift_eq {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) (u v : EuclideanSpace ℂ ι) :
    inner ℂ (horizontalLift ψ u) (horizontalLift ψ v)
      = (inner ℂ u v - inner ℂ u ψ * inner ℂ ψ v / (‖ψ‖ : ℂ) ^ 2) / (‖ψ‖ : ℂ) ^ 2 := by
  have hN : (‖ψ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hψ)
  have hc : conj (inner ℂ ψ u / (‖ψ‖ : ℂ) ^ 2) = inner ℂ u ψ / (‖ψ‖ : ℂ) ^ 2 := by
    rw [map_div₀, inner_conj_symm, map_pow, Complex.conj_ofReal]
  have hself : inner ℂ ψ ψ = (‖ψ‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K ψ
  simp only [horizontalLift, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    hself, map_inv₀, Complex.conj_ofReal, hc]
  field_simp
  ring

/-- ★ **The Fubini–Study inner product is the inner product of the horizontal lifts**:
`4 Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫ = fsInnerHom ψ u v`. -/
theorem inner_horizontalLift {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) (u v : EuclideanSpace ℂ ι) :
    4 * (inner ℂ (horizontalLift ψ u) (horizontalLift ψ v) : ℂ).re = fsInnerHom ψ u v := by
  rw [inner_horizontalLift_eq hψ, fsInnerHom, ← Complex.ofReal_pow, Complex.div_ofReal_re,
    Complex.sub_re, Complex.div_ofReal_re]
  ring

/-- The product `conj (normalize ψ k) * horizontalLift ψ u k`, as a complex number. -/
theorem conj_normalize_mul_horizontalLift (ψ u : EuclideanSpace ℂ ι) (k : ι) :
    conj (normalize ψ k) * horizontalLift ψ u k
      = (conj (ψ k) * u k - ((‖ψ k‖ ^ 2 : ℝ) : ℂ) * inner ℂ ψ u / ((‖ψ‖ ^ 2 : ℝ) : ℂ))
          / ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [normalize_apply, horizontalLift_apply, map_mul, map_inv₀, Complex.conj_ofReal]
  have hk : conj (ψ k) * ψ k = (‖ψ k‖ : ℂ) ^ 2 := RCLike.conj_mul (ψ k)
  push_cast
  linear_combination (-((‖ψ‖ : ℂ)⁻¹ ^ 4) * inner ℂ ψ u) * hk

/-- The Born displacement of the ray along `u`, in homogeneous coordinates. -/
theorem bornDeriv_normalize_horizontalLift (ψ u : EuclideanSpace ℂ ι) (k : ι) :
    bornDeriv (normalize ψ) (horizontalLift ψ u) k
      = 2 * ((conj (ψ k) * u k).re / ‖ψ‖ ^ 2
          - ‖ψ k‖ ^ 2 * (inner ℂ ψ u : ℂ).re / ‖ψ‖ ^ 4) := by
  rw [bornDeriv, conj_normalize_mul_horizontalLift, Complex.div_ofReal_re, Complex.sub_re,
    Complex.div_ofReal_re, Complex.re_ofReal_mul]
  ring

/-- If every `ψ̄ₖ uₖ` is real then the horizontal lift of `u` is a horizontal direction at
`normalize ψ`: the projection off `ψ` and the rescaling preserve the reality of every coordinate
product, because `⟪ψ, u⟫ = Σ ψ̄ₖ uₖ` is then real as well. -/
theorem isHorizontal_normalize_horizontalLift {ψ u : EuclideanSpace ℂ ι}
    (hu : ∀ k, (conj (ψ k) * u k).im = 0) :
    IsHorizontal (normalize ψ) (horizontalLift ψ u) := by
  have hin : (inner ℂ ψ u : ℂ).im = 0 := by
    rw [PiLp.inner_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [RCLike.inner_apply, mul_comm]; exact hu k
  intro k
  rw [conj_normalize_mul_horizontalLift, Complex.div_ofReal_im, Complex.sub_im,
    Complex.div_ofReal_im, Complex.im_ofReal_mul, hu k, hin]
  simp

/-- ★ **The bridge in homogeneous coordinates.** For `ψ ≠ 0` with no vanishing coordinate, a
direction `u` with every `ψ̄ₖ uₖ` real, and any direction `v`, the Fisher–Rao inner product of
the Born displacements of the ray equals the Fubini–Study inner product of the directions:

    `g_FR(dΦ u, dΦ v) = fsInnerHom ψ u v = 4 (Re ⟪u, v⟫ / ‖ψ‖² − Re(⟪u, ψ⟫ ⟪ψ, v⟫) / ‖ψ‖⁴)`.

This is `fisherRaoInner_bornDeriv` at `normalize ψ` along the horizontal lifts. -/
theorem fisherRaoInner_bornDeriv_normalize {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (h0 : ∀ k, ψ k ≠ 0) {u : EuclideanSpace ℂ ι} (hu : ∀ k, (conj (ψ k) * u k).im = 0)
    (v : EuclideanSpace ℂ ι) :
    OpenSimplex.fisherRaoInner
        (bornSimplex (normalize ψ) (norm_normalize hψ) (fun k => normalize_apply_ne_zero hψ (h0 k)))
        (bornDeriv (normalize ψ) (horizontalLift ψ u)) (bornDeriv (normalize ψ) (horizontalLift ψ v))
      = fsInnerHom ψ u v := by
  rw [fisherRaoInner_bornDeriv _ _ _ (isHorizontal_normalize_horizontalLift hu),
    inner_horizontalLift hψ]

end FisherRao
