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
# The Born map is an isometry from the torus-horizontal directions to Fisher–Rao

**Category:** 1-Mathlib (CSD-free; finite-dimensional inner-product algebra on `EuclideanSpace ℂ ι`
and the open simplex of `FisherRao.lean`).

A unit vector `ψ : ℂ^ι` has Born weights `pᵢ = ‖ψᵢ‖²`, a point of the open probability simplex
when no coordinate vanishes. Moving `ψ` in a direction `u` moves the weights by
`dpᵢ = 2 Re(ψ̄ᵢ uᵢ)`, and the Fisher–Rao inner product of two such displacements is

    `Σᵢ dpᵢ dp'ᵢ / pᵢ`.

Write `u` as `uᵢ = aᵢ ψᵢ` coordinate by coordinate. When every `aᵢ` is real (the direction is
**torus-horizontal**: it changes moduli, not phases), `dpᵢ = 2 aᵢ pᵢ` and the sum collapses to
`4 Σᵢ ūᵢ vᵢ = 4 ⟪u, v⟫`. That is an identity between vectors, and it reads as a statement about
the state space once `u` is also tangent to the unit sphere at `ψ` (`⟪ψ, u⟫ = 0`): then
`4 Re ⟪u, v⟫` is the Fubini–Study inner product of the two directions, in the normalisation
where the state space of a qubit is the unit round sphere and the Fubini–Study metric *is* the
quantum Fisher information of a pure-state family (the Bengtsson–Życzkowski normalisation is a
quarter of it). The radial direction `u = ψ` is torus-horizontal but not tangent, and moves no
state; the projective form of everything here (`BraunsteinCaves.lean`, `horizontalLift`)
projects that component off before anything is said.

Along a general direction the phases also move and Fisher–Rao only sees the moduli; the
resulting inequality, Braunstein–Caves for the computational-basis measurement, is
`BraunsteinCaves.lean`.

## Main declarations

* `FisherRao.bornWeight ψ i = ‖ψ i‖ ^ 2`, `FisherRao.bornSimplex` — the Born weights as a point of
  `OpenSimplex ι` for a unit vector with no vanishing coordinate.
* `FisherRao.bornDeriv ψ u i = 2 Re(ψ̄ᵢ uᵢ)` and `hasFDerivAt_bornWeight` — it is the differential
  of `ψ ↦ ‖ψ i‖ ^ 2`; `sum_bornDeriv` — the displacement sums to `2 Re ⟪ψ, u⟫`, so it is tangent
  to the simplex whenever `u` is tangent to the unit sphere.
* `FisherRao.IsTorusHorizontal ψ u` — every `ψ̄ᵢ uᵢ` is real (orthogonal to the torus orbit;
  not the same as the projective horizontal lift of `BraunsteinCaves.lean`, which also projects
  off `ψ`).
* ★ `fisherRaoInner_bornDeriv` — for torus-horizontal `u` and any `v`,
  `fisherRaoInner (bornSimplex ψ) (bornDeriv ψ u) (bornDeriv ψ v) = 4 * Re ⟪u, v⟫`;
  `fisherRaoSq_bornDeriv` — the quadratic form of a torus-horizontal displacement is `4 ‖u‖²`.

## The constant

The right-hand side `4 * Re ⟪u, v⟫` is the Fubini–Study metric of the projective space in the
normalisation of `Projectivization.fsMetric`
(`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`,
where the Gram matrix at a chart origin is `4 • 1`), evaluated on horizontal lifts. In that
normalisation the Fubini–Study metric of a pure-state family is its quantum Fisher information,
`4 (‖u‖² − ‖⟪ψ, u⟫‖²)` for unit `ψ` (`BraunsteinCaves.lean`, `fsInnerHom_self_of_norm_eq_one`).
In the normalisation `‖u‖² − ‖⟪ψ, u⟫‖²` of Bengtsson–Życzkowski, which
`Empirical/Metrology/QuantumFisher.lean`'s vector-level `fsMetric` uses, the bridge constant is
`4` and the quantum Fisher information is `4 g_FS`. No constant is assumed here; the `4` is the
derivative of `‖·‖²`.

## References

* S. L. Braunstein, C. M. Caves, *Statistical distance and the geometry of quantum states*,
  Phys. Rev. Lett. 72, 3439 (1994).
* I. Bengtsson, K. Życzkowski, *Geometry of Quantum States*, 2nd ed., §§4.4, 14.2.
* Physlib PR #1652 (`FisherRao.lean`, mirrored in this directory).

## Provenance

Built 2026-09-16 for Physlib PR #1652; split 2026-09-18 (the homogeneous coordinates and the
Braunstein–Caves inequality moved to `BraunsteinCaves.lean`, so that each file is one
Physlib-sized pull request); recorded in this repository's completed-work ledger
(`specs/future-work.md`, KG-4) and claims ledger (CL-076).
-/

@[expose] public section

noncomputable section

open Finset ComplexConjugate

namespace FisherRao

variable {ι : Type*}

/-! ## The Born weights of a vector, coordinate by coordinate -/

/-- The Born weight of the `i`-th coordinate: `‖ψ i‖ ^ 2`. -/
def bornWeight (ψ : EuclideanSpace ℂ ι) (i : ι) : ℝ := ‖ψ i‖ ^ 2

/-- `bornWeight`, unfolded: the definitional equation. -/
theorem bornWeight_def (ψ : EuclideanSpace ℂ ι) (i : ι) : bornWeight ψ i = ‖ψ i‖ ^ 2 := rfl

theorem bornWeight_nonneg (ψ : EuclideanSpace ℂ ι) (i : ι) : 0 ≤ bornWeight ψ i :=
  sq_nonneg _

theorem bornWeight_pos (ψ : EuclideanSpace ℂ ι) {i : ι} (h : ψ i ≠ 0) : 0 < bornWeight ψ i :=
  pow_pos (norm_pos_iff.mpr h) 2

/-! ## The differential of the Born map -/

/-- The displacement of the `i`-th Born weight along `u`: `2 Re(ψ̄ᵢ uᵢ)`. -/
def bornDeriv (ψ u : EuclideanSpace ℂ ι) (i : ι) : ℝ := 2 * (conj (ψ i) * u i).re

/-- `bornDeriv`, unfolded: the definitional equation. -/
theorem bornDeriv_def (ψ u : EuclideanSpace ℂ ι) (i : ι) :
    bornDeriv ψ u i = 2 * (conj (ψ i) * u i).re := rfl

/-! ## Horizontal directions -/

/-- A direction `u` at `ψ` is **torus-horizontal** when every `ψ̄ᵢ uᵢ` is real: it changes the
moduli of the coordinates and none of their phases, so it is orthogonal to the orbit of the
coordinate-phase torus. It need not be tangent to the unit sphere (the radial direction `ψ`
qualifies); the projective horizontal lift (`horizontalLift`, `BraunsteinCaves.lean`) removes the
radial component. -/
def IsTorusHorizontal (ψ u : EuclideanSpace ℂ ι) : Prop := ∀ i, (conj (ψ i) * u i).im = 0

/-- A direction whose coordinates are real multiples of those of `ψ` is horizontal. -/
theorem isTorusHorizontal_of_forall_eq (ψ u : EuclideanSpace ℂ ι) (a : ι → ℝ)
    (hu : ∀ i, u i = (a i : ℂ) * ψ i) : IsTorusHorizontal ψ u := by
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

/-- ★ **The bridge, at the vector level.** For a torus-horizontal direction `u` and any direction
`v`, the Fisher–Rao inner product of the Born displacements is four times the real inner product
of the directions:

    `g_FR(dΦ u, dΦ v) = 4 Re ⟪u, v⟫`.

Only `u` needs to be torus-horizontal; `v` is arbitrary. The `4` is the derivative of `‖·‖²`.
When `u` and `v` are also tangent to the unit sphere at `ψ`, `4 Re ⟪u, v⟫` is the Fubini–Study
inner product in the round-sphere normalisation; the projective statement that builds the
tangency in is `fisherRaoInner_bornDeriv_normalize` (`BraunsteinCaves.lean`). -/
theorem fisherRaoInner_bornDeriv (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0)
    {u : EuclideanSpace ℂ ι} (hu : IsTorusHorizontal ψ u) (v : EuclideanSpace ℂ ι) :
    (bornSimplex ψ hψ h0).fisherRaoInner (bornDeriv ψ u) (bornDeriv ψ v)
      = 4 * (inner ℂ u v : ℂ).re := by
  simp only [OpenSimplex.fisherRaoInner, bornSimplex_val, PiLp.inner_apply, Complex.re_sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => bornDeriv_mul_div_bornWeight ψ u v (h0 i) (hu i)

/-- The Fisher–Rao quadratic form of a torus-horizontal Born displacement is `4 ‖u‖ ^ 2`. -/
theorem fisherRaoSq_bornDeriv (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (h0 : ∀ i, ψ i ≠ 0)
    {u : EuclideanSpace ℂ ι} (hu : IsTorusHorizontal ψ u) :
    (bornSimplex ψ hψ h0).fisherRaoSq (bornDeriv ψ u) = 4 * ‖u‖ ^ 2 := by
  rw [OpenSimplex.fisherRaoSq, fisherRaoInner_bornDeriv ψ hψ h0 hu u]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

end FisherRao
