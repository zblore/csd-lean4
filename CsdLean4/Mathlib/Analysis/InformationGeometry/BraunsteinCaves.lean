/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InformationGeometry.FubiniStudyFisherRao

/-!
# Braunstein–Caves for the coordinate readout, algebraically and projectively

**Category:** 1-Mathlib (CSD-free; `FubiniStudyFisherRao.lean` and the open simplex of
`FisherRao.lean`).

Along a general direction the phases of the coordinates also move and Fisher–Rao only sees the
moduli. The inequality `Σᵢ dpᵢ²/pᵢ ≤ 4 ‖u‖²` holds for every direction `u` with equality exactly
on the torus-horizontal directions (`FubiniStudyFisherRao.lean`); read on the projective
horizontal lift it is Braunstein–Caves for the computational-basis measurement: the classical
Fisher information of the coordinate readout is at most the quantum Fisher information
`4 (‖u‖² − ‖⟪ψ, u⟫‖²)`, with equality exactly when the projected direction is
torus-horizontal.

The projective form needs homogeneous coordinates. A point of the state space is a ray `[ψ]`
with `ψ ≠ 0` and a direction at it is any vector `u`; the pairs `(ψ, u)` and `(ψ, u + c ψ)`
describe the same tangent vector. The unit vector on the ray is `normalize ψ = ‖ψ‖⁻¹ • ψ`, the
**horizontal lift** of `u` removes the component of `u` along `ψ` and rescales, and the
Fubini–Study inner product of two directions is `fsInnerHom ψ u v`, which is
`4 Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫`. This is the form the affine charts of `ℂℙⁿ`
meet (`Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean`).

## Main declarations

* `fisherInfo_bornDeriv_le` — `fisherInfo (bornWeight ψ) (bornDeriv ψ u) ≤ 4 * ‖u‖ ^ 2` for every
  `u`, and `fisherInfo_bornDeriv_eq_iff` — with equality iff `u` is torus-horizontal. These are
  the algebraic form; `4 ‖u‖²` is the quantum Fisher information only for `u` tangent to the
  sphere.
* Homogeneous coordinates: `normalize ψ`, `horizontalLift ψ u`, `fsInnerHom ψ u v` (the
  Fubini–Study inner product at a nonzero `ψ`), ★ `inner_horizontalLift` (`fsInnerHom` is
  `4 Re ⟪·,·⟫` of the horizontal lifts), `fsInnerHom_self_of_norm_eq_one`
  (`fsInnerHom ψ u u = 4 (‖u‖² − ‖⟪ψ, u⟫‖²)`, the quantum Fisher information, for unit `ψ`) and
  ★ `fisherRaoInner_bornDeriv_normalize`, the bridge stated at `normalize ψ`.
* ★ `fisherInfo_bornDeriv_horizontalLift_le` and `fisherInfo_bornDeriv_horizontalLift_eq_iff` —
  **Braunstein–Caves, projectively**: the coordinate readout's Fisher information along the
  horizontal lift of `u` is at most `fsInnerHom ψ u u`, the quantum Fisher information, with
  equality iff the lift is torus-horizontal.

## References

* S. L. Braunstein, C. M. Caves, *Statistical distance and the geometry of quantum states*,
  Phys. Rev. Lett. 72, 3439 (1994).
* I. Bengtsson, K. Życzkowski, *Geometry of Quantum States*, 2nd ed., §§4.4, 14.2.
* Physlib PR #1652 (`FisherRao.lean`, mirrored in this directory).

## Provenance

Split 2026-09-18 from `FubiniStudyFisherRao.lean` (built 2026-09-16 for Physlib PR #1652) so
that each file is one Physlib-sized pull request; recorded in this repository's completed-work
ledger (`specs/future-work.md`, KG-4).
-/

@[expose] public section

noncomputable section

open Finset ComplexConjugate

namespace FisherRao

variable {ι : Type*}

/-! ## Pointwise bounds on one coordinate -/

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

variable [Fintype ι]

/-! ## Braunstein–Caves for the coordinate readout -/

/-- **The algebraic Braunstein–Caves bound**: the classical Fisher information of the coordinate
readout along `u` is at most `4 ‖u‖ ^ 2`, for every direction `u`. For `u` tangent to the unit
sphere at `ψ` that bound is the quantum Fisher information; for a general `u` it is not (the
radial direction has `4 ‖ψ‖² = 4` and quantum Fisher information `0`), and the projective form
is `fisherInfo_bornDeriv_horizontalLift_le`. -/
theorem fisherInfo_bornDeriv_le (ψ u : EuclideanSpace ℂ ι) (h0 : ∀ i, ψ i ≠ 0) :
    fisherInfo (bornWeight ψ) (bornDeriv ψ u) ≤ 4 * ‖u‖ ^ 2 := by
  rw [fisherInfo, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => bornDeriv_sq_div_bornWeight_le ψ u (h0 i)

/-- Equality in the algebraic bound holds exactly on the torus-horizontal directions. The
projective form, where the right-hand side is the quantum Fisher information, is
`fisherInfo_bornDeriv_horizontalLift_eq_iff`. -/
theorem fisherInfo_bornDeriv_eq_iff (ψ u : EuclideanSpace ℂ ι) (h0 : ∀ i, ψ i ≠ 0) :
    fisherInfo (bornWeight ψ) (bornDeriv ψ u) = 4 * ‖u‖ ^ 2 ↔ IsTorusHorizontal ψ u := by
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
theorem isTorusHorizontal_normalize_horizontalLift {ψ u : EuclideanSpace ℂ ι}
    (hu : ∀ k, (conj (ψ k) * u k).im = 0) :
    IsTorusHorizontal (normalize ψ) (horizontalLift ψ u) := by
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
        (bornDeriv (normalize ψ) (horizontalLift ψ u)) (bornDeriv (normalize ψ) (horizontalLift ψ
            v))
      = fsInnerHom ψ u v := by
  rw [fisherRaoInner_bornDeriv _ _ _ (isTorusHorizontal_normalize_horizontalLift hu),
    inner_horizontalLift hψ]

/-! ## Braunstein–Caves, projectively

`fisherInfo_bornDeriv_le` bounds the readout's Fisher information by `4 ‖u‖²`, which is the quantum
Fisher information only when `u` is tangent to the unit sphere. The projective statement takes an
arbitrary direction `u` at `ψ ≠ 0`, replaces it by its horizontal lift (the component orthogonal
to `ψ`, rescaled), and compares with `fsInnerHom ψ u u` — which for unit `ψ` is
`4 (‖u‖² − ‖⟪ψ, u⟫‖²)`, the quantum Fisher information of the family. -/

/-- For a unit vector, the Fubini–Study quadratic form is the quantum Fisher information of a
pure-state family: `fsInnerHom ψ u u = 4 (‖u‖² − ‖⟪ψ, u⟫‖²)`. -/
theorem fsInnerHom_self_of_norm_eq_one {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1)
    (u : EuclideanSpace ℂ ι) :
    fsInnerHom ψ u u = 4 * (‖u‖ ^ 2 - ‖(inner ℂ ψ u : ℂ)‖ ^ 2) := by
  have h1 : (inner ℂ u u : ℂ).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h2 : (inner ℂ u ψ * inner ℂ ψ u : ℂ).re = ‖(inner ℂ ψ u : ℂ)‖ ^ 2 := by
    have hc : conj (inner ℂ ψ u : ℂ) * inner ℂ ψ u = (‖(inner ℂ ψ u : ℂ)‖ : ℂ) ^ 2 :=
      RCLike.conj_mul _
    rw [← inner_conj_symm u ψ, hc, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [fsInnerHom, hψ, h1, h2]
  ring

/-- The Fisher–Rao quadratic form of the lift's displacement, as `4 ‖horizontalLift ψ u‖²`. -/
theorem fsInnerHom_self_eq_norm_horizontalLift {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (u : EuclideanSpace ℂ ι) : fsInnerHom ψ u u = 4 * ‖horizontalLift ψ u‖ ^ 2 := by
  rw [← inner_horizontalLift hψ u u]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (horizontalLift ψ u)

/-- ★ **Braunstein–Caves for the coordinate readout, projectively.** For `ψ ≠ 0` with no vanishing
coordinate and any direction `u`, the classical Fisher information of the coordinate readout
along the horizontal lift of `u` is at most the Fubini–Study quadratic form `fsInnerHom ψ u u`,
i.e. the quantum Fisher information of the family (`fsInnerHom_self_of_norm_eq_one`). -/
theorem fisherInfo_bornDeriv_horizontalLift_le {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (h0 : ∀ k, ψ k ≠ 0) (u : EuclideanSpace ℂ ι) :
    fisherInfo (bornWeight (normalize ψ)) (bornDeriv (normalize ψ) (horizontalLift ψ u))
      ≤ fsInnerHom ψ u u := by
  rw [fsInnerHom_self_eq_norm_horizontalLift hψ]
  exact fisherInfo_bornDeriv_le (normalize ψ) (horizontalLift ψ u)
    fun k => normalize_apply_ne_zero hψ (h0 k)

/-- ★ **Equality in projective Braunstein–Caves holds exactly when the horizontal lift is
torus-horizontal**: the coordinate readout extracts the full quantum Fisher information of a
direction iff, after the radial component is removed, the direction changes only the moduli of
the coordinates. -/
theorem fisherInfo_bornDeriv_horizontalLift_eq_iff {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0)
    (h0 : ∀ k, ψ k ≠ 0) (u : EuclideanSpace ℂ ι) :
    fisherInfo (bornWeight (normalize ψ)) (bornDeriv (normalize ψ) (horizontalLift ψ u))
        = fsInnerHom ψ u u
      ↔ IsTorusHorizontal (normalize ψ) (horizontalLift ψ u) := by
  rw [fsInnerHom_self_eq_norm_horizontalLift hψ]
  exact fisherInfo_bornDeriv_eq_iff (normalize ψ) (horizontalLift ψ u)
    fun k => normalize_apply_ne_zero hψ (h0 k)

end FisherRao
