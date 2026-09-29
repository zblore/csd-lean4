/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Core

/-!
# Gleason's theorem for real Hilbert spaces

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #58, the **A4** reduction of
`specs/gleason-feasibility.md`: the real-space corollary of the core lemma proved in #57.

★★★ `RealProjectionPackage.real_gleason_representation`: for `N ≥ 3`, every assignment `p` on the
orthogonal projections of `ℝᴺ` that is nonnegative, normalised and additive on orthogonal pairs is
`P ↦ Tr(ρ P)` for a **unique** real density matrix `ρ`. The complex theorem
(`Gleason/Core.lean`, #57) does not contain this one: a real inner product space is not a complex
one, and the reduction runs through real `3`-spaces rather than completely real planes.

## The route

The real side mirrors the complex layers, which is cheaper than it looks because the Gram section of
`Gleason/ProjectionPackage.lean` is already generic over `RCLike`:

* `rankOneR`, `RealProjectionPackage`, `p_sum`, `frame` and **A1**
  (`sum_frame_orthonormalBasis`: the frame function sums to `1` over every real orthonormal basis);
* **A2**, `isFrameFunction_restrictR`: for an orthonormal family `e` in `ℝᴺ` the restriction
  `x ↦ frame (∑ᵢ xᵢ eᵢ)` is a frame function on `ℝᵏ` of weight `p (∑ᵢ |eᵢ⟩⟨eᵢ|)` — the weight is
  basis independent because the rank-one projections of a transported orthonormal basis sum to the
  same matrix (`sum_rankOneR_combR`, the Gram identity `E B Bᵀ Eᵀ = E Eᵀ`). For `k = 3` the core
  lemma applies: ★ `exists_isSymm_restrictR`;
* the degree-2 extension `extOf f v = ‖v‖² f (v/‖v‖)`, which is the quadratic form of the core
  lemma's matrix on the whole span of a triple (`extOf_combR`), hence a quadratic form on every plane
  (★ `exists_extOf_plane`, extending the plane's orthonormal pair to a triple with
  `exists_orthonormal_tripleR`), hence ★★ `extOf_parallelogramR` — **the parallelogram law on `ℝᴺ`**,
  by Gram–Schmidt on any two vectors;
* the **real Jordan–von Neumann engine** (`IsQuadraticLikeR`, `polarR`, `polarMatrixR`,
  ★ `IsQuadraticLikeR.eq_dotProduct`), giving ★★ `exists_isSymm_sphere`: **A4**, the frame function
  is the quadratic form of a symmetric matrix on the unit sphere;
* the descent: `posSemidef_of_sphere_nonnegR`, `trace_eq_sum_sphereR`,
  `eq_of_sphere_quadForm_eqR`, packaged as ★ `quadraticForm_on_sphere_to_densityR`, and the spectral
  step ★ `p_eq_trace` (`eq_sum_eigenvalues_smul_rankOneR`, `eigenvalues_eq_zero_or_oneR`), giving
  ★★ `existsUnique_density_of_frame_quadraticR` and the theorem.

**Done differently from the plan's sketch.** `gleason-feasibility.md` §2 priced A4 as "any `u, u', v`
lie in a `3`-space, so the polarisation is bilinear without any Cauchy equation". The proof here
does *not* take that route: it mirrors the complex assembly, where the Cauchy step
(`additive_bounded_linear`, whose local bound is `0 ≤ q ≤ ‖·‖²`) is already proved and generic, and
where only **pairs** — not triples — need to be placed inside an orthonormal triple. Reusing the
engine is shorter than a locality argument for every instance of bilinearity, and the three-vector
observation is not needed at all.

## Honest scope

⚠️ The statement is for a **projection package**, as in the complex theorem. Gleason's own
formulation is for a bare *frame function*; that version landed 2026-09-28 in `Gleason/RealFrame.lean`
(BACKLOG #87), where the weight of a `3`-space is shown basis-independent without a `p` on
projections, by completing the triple with a fixed family of the orthogonal complement. The middle
layer of this file is stated for any function quadratic on triples
(`exists_isSymm_sphere_of_quad`) precisely so that both consumers share it.
⚠️ Finite dimensions only, `N ≥ 3`, as in #57. `N = 2` is false for Gleason's theorem (the
counterexamples are the classic ones) and nothing here suggests otherwise.
⚠️ The real layer duplicates the shape of the complex one rather than generalising it over
`RCLike`: the complex `ProjectionPackage` and its twelve modules are pinned and consumed by `LF2`,
and genericising them would ripple through the whole directory. The genuinely shared parts (the
Gram section, `additive_bounded_linear`) are *used*, not copied.

## Source

A. Gleason, *Measures on the closed subspaces of a Hilbert space*, J. Math. Mech. **6** (1957) 885
(§1 frame functions, the real theorem); R. Cooke, M. Keane, W. Moran, *Math. Proc. Cambridge
Philos. Soc.* **98** (1985) 117; `Gleason/Core.lean` (#57, the core lemma),
`Gleason/ProjectionPackage.lean` (the Gram section and `IsFrameFunction`),
`Gleason/Polarization.lean` (`additive_bounded_linear`); `specs/gleason-feasibility.md` §2 (A4);
`specs/BACKLOG.md` #58; `specs/future-work.md`.
-/

@[expose] public section

open Matrix
open scoped InnerProductSpace

namespace Gleason

variable {N : ℕ}

/-! ### Rank-one projections over `ℝ` -/

/-- **The real rank-one projection** onto `v` (a projection when `‖v‖ = 1`). -/
def rankOneR (v : EuclideanSpace ℝ (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  vecMulVec (⇑v) (star ⇑v)

lemma rankOneR_apply (v : EuclideanSpace ℝ (Fin N)) (a c : Fin N) :
    rankOneR v a c = v a * v c := rfl

lemma rankOneR_isHermitian (v : EuclideanSpace ℝ (Fin N)) : (rankOneR v).IsHermitian := by
  ext a c
  rw [Matrix.conjTranspose_apply, rankOneR_apply, rankOneR_apply, star_trivial, mul_comm]

lemma rankOneR_isSymm (v : EuclideanSpace ℝ (Fin N)) : (rankOneR v).IsSymm := by
  ext a c
  rw [Matrix.transpose_apply, rankOneR_apply, rankOneR_apply, mul_comm]

/-- `|v⟩⟨v| |w⟩⟨w| = ⟪v, w⟫ |v⟩⟨w|`. -/
lemma rankOneR_mul_rankOneR (v w : EuclideanSpace ℝ (Fin N)) :
    rankOneR v * rankOneR w = ⟪v, w⟫_ℝ • vecMulVec (⇑v) (star ⇑w) := by
  rw [rankOneR, rankOneR, vecMulVec_mul_vecMulVec, vecMulVec_smul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma rankOneR_mul_self {v : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1) :
    rankOneR v * rankOneR v = rankOneR v := by
  rw [rankOneR_mul_rankOneR, real_inner_self_eq_norm_sq, hv]
  simp [rankOneR]

lemma rankOneR_mul_rankOneR_of_inner_eq_zero {v w : EuclideanSpace ℝ (Fin N)}
    (h : ⟪v, w⟫_ℝ = 0) : rankOneR v * rankOneR w = 0 := by
  rw [rankOneR_mul_rankOneR, h, zero_smul]

/-- The real rank-one projection is an orthogonal projection for every unit vector. -/
lemma isStarProjection_rankOneR {v : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1) :
    IsStarProjection (rankOneR v) where
  isIdempotentElem := rankOneR_mul_self hv
  isSelfAdjoint := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
    exact (rankOneR_isHermitian v)

/-- Scaling the vector scales the rank-one matrix by the square. -/
lemma rankOneR_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    rankOneR (c • v) = (c ^ 2) • rankOneR v := by
  rw [rankOneR, rankOneR]
  change vecMulVec (c • ⇑v) (star (c • ⇑v)) = _
  rw [star_smul, star_trivial, smul_vecMulVec, vecMulVec_smul, smul_smul, sq]

lemma rankOneR_neg (v : EuclideanSpace ℝ (Fin N)) : rankOneR (-v) = rankOneR v := by
  rw [show -v = (-1 : ℝ) • v from by rw [neg_smul, one_smul], rankOneR_smul]
  norm_num

lemma rankOneR_mul_rankOneR_of_orthonormal {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)}
    (he : Orthonormal ℝ e) {i j : Fin k} (hij : i ≠ j) : rankOneR (e i) * rankOneR (e j) = 0 :=
  rankOneR_mul_rankOneR_of_inner_eq_zero (he.inner_eq_zero hij)

lemma sum_rankOneR_eq {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N)) :
    ∑ i, rankOneR (e i) = colMatrix e * (colMatrix e)ᴴ :=
  sum_vecMulVec_eq_colMatrix_mul e

/-- **Resolution of the identity** over a real orthonormal basis. -/
lemma sum_rankOneR_orthonormalBasis
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∑ i, rankOneR (b i) = 1 := by
  rw [sum_rankOneR_eq, colMatrix_mul_conjTranspose_of_orthonormalBasis]

/-! ### The real projection package -/

/-- **A real projection package** on `ℝᴺ`: a nonnegative, normalised, orthogonally additive
assignment on the orthogonal projections of a *real* inner product space. -/
structure RealProjectionPackage (N : ℕ) where
  /-- The assignment. -/
  p : Matrix (Fin N) (Fin N) ℝ → ℝ
  /-- `0 ≤ p P` for every projection. -/
  nonneg : ∀ P, IsStarProjection P → 0 ≤ p P
  /-- `p 1 = 1`. -/
  total_one : p 1 = 1
  /-- `p (P + Q) = p P + p Q` for orthogonal projections. -/
  additive : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 → p (P + Q) = p P + p Q

namespace RealProjectionPackage

variable (OP : RealProjectionPackage N)

theorem p_zero : OP.p 0 = 0 := by
  have h := OP.additive 0 0 (IsStarProjection.zero _) (IsStarProjection.zero _) (by simp)
  rw [add_zero] at h
  linarith

theorem p_le_one {P : Matrix (Fin N) (Fin N) ℝ} (hP : IsStarProjection P) : OP.p P ≤ 1 := by
  have h := OP.additive P (1 - P) hP hP.one_sub hP.mul_one_sub_self
  rw [add_sub_cancel, OP.total_one] at h
  have := OP.nonneg (1 - P) hP.one_sub
  linarith

/-- A finite sum of pairwise-orthogonal projections is a projection. -/
theorem isStarProjection_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℝ)
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) (s : Finset ι) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (hP a).add ih ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => horth a j (fun h => ha (h ▸ hj))

/-- **Additivity over any finite family of pairwise-orthogonal projections.** -/
theorem p_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℝ)
    (hP : ∀ i, IsStarProjection (P i)) (horth : ∀ i j, i ≠ j → P i * P j = 0) (s : Finset ι) :
    OP.p (∑ i ∈ s, P i) = ∑ i ∈ s, OP.p (P i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [OP.p_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    refine OP.additive _ _ (hP a) (isStarProjection_sum P hP horth s) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => horth a j (fun h => ha (h ▸ hj))

/-- **The frame function of a real package.** -/
def frame (v : EuclideanSpace ℝ (Fin N)) : ℝ := OP.p (rankOneR v)

theorem frame_nonneg {v : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1) : 0 ≤ OP.frame v :=
  OP.nonneg _ (isStarProjection_rankOneR hv)

theorem frame_le_one {v : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1) : OP.frame v ≤ 1 :=
  OP.p_le_one (isStarProjection_rankOneR hv)

theorem frame_neg (v : EuclideanSpace ℝ (Fin N)) : OP.frame (-v) = OP.frame v := by
  rw [frame, frame, rankOneR_neg]

/-- Additivity over the rank-one projections of an orthonormal family. -/
theorem p_sum_rankOneR {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)} (he : Orthonormal ℝ e) :
    OP.p (∑ i, rankOneR (e i)) = ∑ i, OP.frame (e i) :=
  OP.p_sum _ (fun i => isStarProjection_rankOneR (he.norm_eq_one i))
    (fun _ _ hij => rankOneR_mul_rankOneR_of_orthonormal he hij) Finset.univ

/-- **A1 over `ℝ`.** The frame function sums to `1` over every real orthonormal basis. -/
theorem sum_frame_orthonormalBasis
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∑ i, OP.frame (b i) = 1 := by
  rw [← OP.p_sum_rankOneR b.orthonormal, sum_rankOneR_orthonormalBasis, OP.total_one]

theorem isFrameFunction_frame : IsFrameFunction ℝ OP.frame 1 :=
  OP.sum_frame_orthonormalBasis

/-! ### Restriction to the span of an orthonormal family -/

/-- The point of `ℝᴺ` with coordinates `x` in the family `e`. -/
def _root_.Gleason.combR {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin N) :=
  ∑ i, x i • e i

lemma _root_.Gleason.colMatrix_combR {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N))
    (b : Fin k → EuclideanSpace ℝ (Fin k)) :
    colMatrix (fun j => combR e (b j)) = colMatrix e * colMatrix b := by
  ext a j
  simp [combR, colMatrix_apply, Matrix.mul_apply, mul_comm]

/-- Transporting a real orthonormal family through an orthonormal `e` gives an orthonormal
family: `Gram = Bᵀ (Eᵀ E) B = Bᵀ B = 1`. -/
lemma _root_.Gleason.orthonormal_combR {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)}
    (he : Orthonormal ℝ e) {b : Fin k → EuclideanSpace ℝ (Fin k)} (hb : Orthonormal ℝ b) :
    Orthonormal ℝ fun j => combR e (b j) := by
  rw [orthonormal_iff_ite]
  intro j l
  have hgram := conjTranspose_mul_colMatrix_apply (fun j => combR e (b j)) j l
  rw [colMatrix_combR, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (colMatrix e)ᴴ, conjTranspose_mul_colMatrix_of_orthonormal he,
    Matrix.one_mul, conjTranspose_mul_colMatrix_of_orthonormal hb] at hgram
  rw [← hgram, Matrix.one_apply]

/-- The rank-one projections of a transported orthonormal basis sum to those of `e`. -/
lemma _root_.Gleason.sum_rankOneR_combR {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N))
    (b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    ∑ j, rankOneR (combR e (b j)) = ∑ i, rankOneR (e i) := by
  rw [sum_rankOneR_eq, sum_rankOneR_eq, colMatrix_combR, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (colMatrix (b : Fin k → EuclideanSpace ℝ (Fin k))),
    colMatrix_mul_conjTranspose_of_orthonormalBasis, Matrix.one_mul]

/-- A unit vector of coordinates gives a unit vector of `ℝᴺ`. -/
lemma _root_.Gleason.norm_combR {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)}
    (he : Orthonormal ℝ e) {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    ‖combR e x‖ = 1 := by
  have hsq : ‖combR e x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, combR, he.inner_sum]
    have hx2 := hx
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hx2
    rw [← hx2]
    exact Finset.sum_congr rfl fun i _ => by
      rw [starRingEnd_apply, star_trivial, Real.norm_eq_abs, sq_abs, sq]
  have := norm_nonneg (combR e x)
  nlinarith

/-- **The restriction of the frame function** to the span of an orthonormal family. -/
def restrictR {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N)) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  OP.frame (combR e x)

/-- **A2 over `ℝ`.** The restriction is a real frame function of weight `p (∑ᵢ |eᵢ⟩⟨eᵢ|)`. -/
theorem isFrameFunction_restrictR {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)}
    (he : Orthonormal ℝ e) :
    IsFrameFunction ℝ (OP.restrictR e) (OP.p (∑ i, rankOneR (e i))) := by
  intro b
  rw [← sum_rankOneR_combR e b, OP.p_sum_rankOneR (orthonormal_combR he b.orthonormal)]
  rfl

theorem restrictR_nonneg {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)} (he : Orthonormal ℝ e)
    {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) : 0 ≤ OP.restrictR e x :=
  OP.frame_nonneg (norm_combR he hx)

/-- ★ **The core lemma, applied to a triple**: the frame function of a real package is a symmetric
quadratic form on the unit sphere of the span of every orthonormal triple. -/
theorem exists_isSymm_restrictR {e : Fin 3 → EuclideanSpace ℝ (Fin N)} (he : Orthonormal ℝ e) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → OP.frame (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x) :=
  coreLemma (OP.restrictR e) _ (OP.isFrameFunction_restrictR he)
    fun _ hx => OP.restrictR_nonneg he hx

end RealProjectionPackage

/-! ### The real polarisation engine -/

/-- **A real quadratic-like function** on `ℝᴺ`: degree-2 homogeneous, obeying the parallelogram
law, and squeezed between `0` and `‖·‖²`. The last two conditions replace continuity in the
Jordan–von Neumann argument (`polarR_smul_left`). -/
structure IsQuadraticLikeR (q : EuclideanSpace ℝ (Fin N) → ℝ) : Prop where
  /-- `q (c • v) = c² q v`. -/
  smul : ∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin N)), q (c • v) = c ^ 2 * q v
  /-- The parallelogram law. -/
  parallelogram : ∀ u v : EuclideanSpace ℝ (Fin N), q (u + v) + q (u - v) = 2 * q u + 2 * q v
  /-- `0 ≤ q`. -/
  nonneg : ∀ v : EuclideanSpace ℝ (Fin N), 0 ≤ q v
  /-- `q v ≤ ‖v‖²`. -/
  le_normSq : ∀ v : EuclideanSpace ℝ (Fin N), q v ≤ ‖v‖ ^ 2

/-- **The real polarisation difference** `polarR q u v = q (u + v) − q (u − v)`, four times the
symmetric bilinear form being reconstructed. -/
def polarR (q : EuclideanSpace ℝ (Fin N) → ℝ) (u v : EuclideanSpace ℝ (Fin N)) : ℝ :=
  q (u + v) - q (u - v)

/-- **The matrix of the polarised form** on the standard basis. -/
noncomputable def polarMatrixR (q : EuclideanSpace ℝ (Fin N) → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun j k =>
    polarR q (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ)) / 4

/-- **Standard-basis expansion in a real `EuclideanSpace`.** -/
theorem euclidean_sum_singleR (v : EuclideanSpace ℝ (Fin N)) :
    ∑ i, (v i) • (EuclideanSpace.single i (1 : ℝ)) = v := by
  ext j
  simp
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

namespace IsQuadraticLikeR

variable {q : EuclideanSpace ℝ (Fin N) → ℝ} (hq : IsQuadraticLikeR q)
include hq

theorem zero : q 0 = 0 := by
  have h := hq.smul 0 0
  simpa using h

theorem neg (v : EuclideanSpace ℝ (Fin N)) : q (-v) = q v := by
  have h := hq.smul (-1) v
  simpa using h

theorem polarR_symm (u v : EuclideanSpace ℝ (Fin N)) : polarR q u v = polarR q v u := by
  have h : v - u = -(u - v) := by abel
  rw [polarR, polarR, h, hq.neg, add_comm]

theorem polarR_zero_left (v : EuclideanSpace ℝ (Fin N)) : polarR q 0 v = 0 := by
  rw [polarR, zero_add, zero_sub, hq.neg, sub_self]

/-- **The halving identity (Jordan–von Neumann core).** -/
theorem polarR_add_half (u w v : EuclideanSpace ℝ (Fin N)) :
    polarR q u v + polarR q w v = 2 * polarR q ((2 : ℝ)⁻¹ • (u + w)) v := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  set a : EuclideanSpace ℝ (Fin N) := (2 : ℝ)⁻¹ • (u + w) with ha
  set b : EuclideanSpace ℝ (Fin N) := (2 : ℝ)⁻¹ • (u - w) with hb
  have hab1 : a + b = u := by
    rw [ha, hb, ← smul_add, show (u + w) + (u - w) = (2 : ℝ) • u from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hab2 : a - b = w := by
    rw [ha, hb, ← smul_sub, show (u + w) - (u - w) = (2 : ℝ) • w from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have par1 := hq.parallelogram (a + v) b
  have par2 := hq.parallelogram (a - v) b
  rw [show a + v + b = u + v from by rw [← hab1]; abel,
    show a + v - b = w + v from by rw [← hab2]; abel] at par1
  rw [show a - v + b = u - v from by rw [← hab1]; abel,
    show a - v - b = w - v from by rw [← hab2]; abel] at par2
  simp only [polarR]
  linarith

/-- **Additivity of `polarR` in the first slot.** -/
theorem polarR_add_left (u w v : EuclideanSpace ℝ (Fin N)) :
    polarR q (u + w) v = polarR q u v + polarR q w v := by
  have h1 := hq.polarR_add_half u w v
  have h2 := hq.polarR_add_half (u + w) 0 v
  simp only [hq.polarR_zero_left, add_zero] at h2
  linarith

/-- **Real homogeneity of `polarR` in the first slot**, through `additive_bounded_linear`. -/
theorem polarR_smul_left (t : ℝ) (u v : EuclideanSpace ℝ (Fin N)) :
    polarR q (t • u) v = t * polarR q u v := by
  have hadd : ∀ s r : ℝ, polarR q ((s + r) • u) v
      = polarR q (s • u) v + polarR q (r • u) v := by
    intro s r
    rw [add_smul, hq.polarR_add_left]
  have hbound : ∀ s : ℝ, |s| ≤ 1 → |polarR q (s • u) v| ≤ (‖u‖ + ‖v‖) ^ 2 := by
    intro s hs
    have hsn : ‖s • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg u, abs_nonneg s]
    have hp : ‖s • u + v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_add_le _ _) (by linarith)
    have hm : ‖s • u - v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_sub_le _ _) (by linarith)
    have h1 := hq.nonneg (s • u + v)
    have h2 := hq.nonneg (s • u - v)
    have h3 := hq.le_normSq (s • u + v)
    have h4 := hq.le_normSq (s • u - v)
    rw [abs_le, polarR]
    constructor
    · nlinarith [norm_nonneg (s • u - v), norm_nonneg u, norm_nonneg v]
    · nlinarith [norm_nonneg (s • u + v), norm_nonneg u, norm_nonneg v]
  have hlin := additive_bounded_linear (fun s : ℝ => polarR q (s • u) v) hadd hbound t
  simpa using hlin

theorem polarR_add_right (u v w : EuclideanSpace ℝ (Fin N)) :
    polarR q u (v + w) = polarR q u v + polarR q u w := by
  rw [hq.polarR_symm u (v + w), hq.polarR_add_left, hq.polarR_symm v u, hq.polarR_symm w u]

theorem polarR_smul_right (t : ℝ) (u v : EuclideanSpace ℝ (Fin N)) :
    polarR q u (t • v) = t * polarR q u v := by
  rw [hq.polarR_symm u (t • v), hq.polarR_smul_left, hq.polarR_symm v u]

/-- `polarR q v v = 4 q v`. -/
theorem polarR_self (v : EuclideanSpace ℝ (Fin N)) : polarR q v v = 4 * q v := by
  rw [polarR, show v + v = (2 : ℝ) • v from by rw [two_smul], sub_self, hq.smul, hq.zero]
  ring

theorem polarR_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin N)) (v : EuclideanSpace ℝ (Fin N)) :
    polarR q (∑ i ∈ s, c i • f i) v = ∑ i ∈ s, c i * polarR q (f i) v := by
  classical
  induction s using Finset.induction with
  | empty => simp [hq.polarR_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hq.polarR_add_left, hq.polarR_smul_left, ih]

theorem polarR_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin N)) (v : EuclideanSpace ℝ (Fin N)) :
    polarR q v (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * polarR q v (f i) := by
  rw [hq.polarR_symm v, hq.polarR_sum_left]
  exact Finset.sum_congr rfl fun i _ => by rw [hq.polarR_symm (f i) v]

theorem polarMatrixR_isSymm : (polarMatrixR q).IsSymm := by
  ext j k
  rw [Matrix.transpose_apply, polarMatrixR, Matrix.of_apply, Matrix.of_apply,
    hq.polarR_symm (EuclideanSpace.single k (1 : ℝ))]

/-- ★ **`q` is the quadratic form of `polarMatrixR q`.** -/
theorem eq_dotProduct (v : EuclideanSpace ℝ (Fin N)) :
    q v = ⇑v ⬝ᵥ (polarMatrixR q *ᵥ ⇑v) := by
  have hexp : polarR q v v
      = ∑ i, ∑ j, v i * (v j * polarR q (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single j (1 : ℝ))) := by
    conv_lhs => rw [← euclidean_sum_singleR v]
    rw [hq.polarR_sum_left]
    exact Finset.sum_congr rfl fun i _ => by rw [hq.polarR_sum_right, Finset.mul_sum]
  rw [show q v = polarR q v v / 4 from by rw [hq.polarR_self]; ring, hexp]
  simp only [dotProduct, Matrix.mulVec, polarMatrixR, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end IsQuadraticLikeR

namespace RealProjectionPackage

variable (OP : RealProjectionPackage N)

end RealProjectionPackage

/-! ### The degree-2 extension of a function quadratic on triples

This layer is stated for a bare function `f` on the sphere and a hypothesis `hquad` saying that `f`
is a symmetric quadratic form on the span of every orthonormal triple. Both consumers of the layer
supply `hquad` from Gleason's core lemma: `RealProjectionPackage.exists_isSymm_sphere` for a
projection package (`exists_isSymm_restrictR`), and `Gleason/RealFrame.lean` for a bare frame
function (BACKLOG #87). -/

/-- **The degree-2 extension** of a function on the sphere: `extOf f v = ‖v‖² f (v / ‖v‖)`, and `0`
at `0` (the factor `‖v‖²` kills it). -/
noncomputable def extOf (f : EuclideanSpace ℝ (Fin N) → ℝ) (v : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v)

lemma extOf_of_norm_one (f : EuclideanSpace ℝ (Fin N) → ℝ) {v : EuclideanSpace ℝ (Fin N)}
    (hv : ‖v‖ = 1) : extOf f v = f v := by
  simp [extOf, hv]

@[simp] lemma extOf_zero (f : EuclideanSpace ℝ (Fin N) → ℝ) : extOf f 0 = 0 := by simp [extOf]

lemma norm_inv_smul_selfR {v : EuclideanSpace ℝ (Fin N)} (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

/-- `extOf f` is degree-2 homogeneous, given that `f` is even on the sphere. -/
lemma extOf_smul {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin N)) : extOf f (c • v) = c ^ 2 * extOf f v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hcn : ‖c • v‖ = |c| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hunit : (‖c • v‖⁻¹ : ℝ) • (c • v) = (|c|⁻¹ * c) • ((‖v‖⁻¹ : ℝ) • v) := by
    rw [smul_smul, smul_smul, hcn, mul_inv]
    ring_nf
  rw [extOf, extOf, hunit, hcn]
  have hframe : f ((|c|⁻¹ * c) • ((‖v‖⁻¹ : ℝ) • v)) = f ((‖v‖⁻¹ : ℝ) • v) := by
    rcases abs_cases c with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs, inv_mul_cancel₀ hc, one_smul]
    · rw [habs, show (-c)⁻¹ * c = -1 from by field_simp, neg_one_smul,
        hneg _ (norm_inv_smul_selfR hv)]
  rw [hframe]
  have hsq : (|c| * ‖v‖) ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hsq]
  ring

lemma extOf_nonneg {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v) (v : EuclideanSpace ℝ (Fin N)) :
    0 ≤ extOf f v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  exact mul_nonneg (sq_nonneg _) (h0 _ (norm_inv_smul_selfR hv))

lemma extOf_le_normSq {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hub : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v ≤ 1) (v : EuclideanSpace ℝ (Fin N)) :
    extOf f v ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have h := hub _ (norm_inv_smul_selfR hv)
  rw [extOf]
  exact mul_le_of_le_one_right (sq_nonneg ‖v‖) h

/-! ### The extension on the span of an orthonormal triple -/

lemma combR_smul {k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin N)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : combR e (c • x) = c • combR e x := by
  rw [combR, combR, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show (c • x) i = c * x i from rfl, smul_smul]

lemma dotProduct_mulVec_smulR {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (c : ℝ)
    (x : Fin k → ℝ) : (c • x) ⬝ᵥ (A *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The extension on the span of an orthonormal family is the quadratic form the core lemma gives,
now at *every* point and not only on the sphere. -/
theorem extOf_combR {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u)
    {k : ℕ} {e : Fin k → EuclideanSpace ℝ (Fin N)} (he : Orthonormal ℝ e)
    {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 → f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (x : EuclideanSpace ℝ (Fin k)) : extOf f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [show combR e (0 : EuclideanSpace ℝ (Fin k)) = 0 from by
      rw [combR]
      exact Finset.sum_eq_zero fun i _ => by
        rw [show (0 : EuclideanSpace ℝ (Fin k)) i = 0 from rfl, zero_smul], extOf_zero,
      show (⇑(0 : EuclideanSpace ℝ (Fin k)) : Fin k → ℝ) = 0 from rfl, Matrix.mulVec_zero,
      dotProduct_zero]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖x‖ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin k), y = (r⁻¹ : ℝ) • x := ⟨_, rfl⟩
  have hrpos : 0 < r := hr ▸ hn
  have hyn : ‖y‖ = 1 := by
    rw [hy, hr]
    exact norm_inv_smul_selfR hx
  have hxy : x = r • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have hcomb : combR e x = r • combR e y := by rw [← combR_smul, hxy]
  have hrhs : (⇑x : Fin k → ℝ) ⬝ᵥ (A *ᵥ ⇑x) = r ^ 2 * ((⇑y : Fin k → ℝ) ⬝ᵥ (A *ᵥ ⇑y)) := by
    rw [show (⇑x : Fin k → ℝ) = r • (⇑y : Fin k → ℝ) from by rw [hxy]; rfl,
      dotProduct_mulVec_smulR]
  rw [hcomb, extOf_smul hneg, extOf_of_norm_one f (norm_combR he hyn), hA y hyn, hrhs, hr]

/-! ### Extending an orthonormal pair to a triple -/

/-- An orthonormal pair in `ℝᴺ`, `N ≥ 3`, extends to an orthonormal triple. -/
lemma exists_orthonormal_tripleR (hN : 3 ≤ N)
    {x y : EuclideanSpace ℝ (Fin N)}
    (hxy : Orthonormal ℝ ![x, y]) :
    ∃ z : EuclideanSpace ℝ (Fin N), Orthonormal ℝ ![x, y, z] := by
  classical
  have hx : ‖x‖ = 1 := by
    have := hxy.norm_eq_one 0
    simpa using this
  have hy : ‖y‖ = 1 := by
    have := hxy.norm_eq_one 1
    simpa using this
  have hxy' : ⟪x, y⟫_ℝ = 0 := by
    have := hxy.inner_eq_zero (show (0 : Fin 2) ≠ 1 by decide)
    simpa using this
  have hyx : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy']
  have hne : x ≠ y := by
    intro h
    rw [h, real_inner_self_eq_norm_sq, hy] at hxy'
    simp at hxy'
  have hset : Orthonormal ℝ ((↑) : ({x, y} : Set (EuclideanSpace ℝ (Fin N))) →
      EuclideanSpace ℝ (Fin N)) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · simp [hx]
    · simp [hxy', hne]
    · simp [hyx, hne.symm]
    · simp [hy]
  obtain ⟨u, b, hsub, hb⟩ := hset.exists_orthonormalBasis_extension
  have hcard : u.card = N := by
    have := Module.finrank_eq_card_basis b.toBasis
    rw [finrank_euclideanSpace_fin, Fintype.card_coe] at this
    exact this.symm
  have hxu : x ∈ u := hsub (by simp)
  have hyu : y ∈ u := hsub (by simp)
  have hrest : (u \ {x, y}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption)]
    have : ({x, y} : Finset (EuclideanSpace ℝ (Fin N))).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨z, hz⟩ := hrest
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hzu, hzx, hzy⟩ := hz
  have hbo := b.orthonormal
  rw [hb, orthonormal_subtype_iff_ite] at hbo
  refine ⟨z, ?_⟩
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.mk_one, Fin.zero_eta, Fin.isValue, Fin.reduceFinMk]
  · simp [hx]
  · simpa using hxy'
  · have := hbo x hxu z hzu
    simpa [Ne.symm hzx] using this
  · simpa [hne.symm] using hyx
  · simp [hy]
  · have := hbo y hyu z hzu
    simpa [Ne.symm hzy] using this
  · have := hbo z hzu x hxu
    simpa [hzx] using this
  · have := hbo z hzu y hyu
    simpa [hzy] using this
  · have := hbo z hzu z hzu
    simpa using this

/-- The coordinates `(a, b, 0)` of a plane vector inside a triple. -/
lemma combR_two (e : Fin 3 → EuclideanSpace ℝ (Fin N)) (a b : ℝ) :
    combR e (WithLp.toLp 2 ![a, b, 0]) = a • e 0 + b • e 1 := by
  simp [combR, Fin.sum_univ_three]

/-- **The extension is a quadratic form on every plane** spanned by an orthonormal pair: extend the
pair to a triple (`N ≥ 3`) and read off the core lemma's matrix. -/
theorem exists_extOf_plane {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hquad : ∀ e : Fin 3 → EuclideanSpace ℝ (Fin N), Orthonormal ℝ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u)
    (hN : 3 ≤ N) {x y : EuclideanSpace ℝ (Fin N)} (hxy : Orthonormal ℝ ![x, y]) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ a b : ℝ,
      extOf f (a • x + b • y) = c₀ * a ^ 2 + c₁ * a * b + c₂ * b ^ 2 := by
  obtain ⟨z, hxyz⟩ := exists_orthonormal_tripleR hN hxy
  obtain ⟨A, hA, hAf⟩ := hquad _ hxyz
  refine ⟨A 0 0, 2 * A 0 1, A 1 1, fun a b => ?_⟩
  have hcomb := extOf_combR hneg hxyz hAf (WithLp.toLp 2 ![a, b, 0])
  rw [combR_two] at hcomb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcomb
  rw [hcomb]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show A 1 0 = A 0 1 from by rw [← hA.apply 0 1]]
  ring

/-- **The parallelogram law on `ℝᴺ`.** Any two vectors lie in a plane spanned by an orthonormal
pair (Gram–Schmidt), and every such plane sits inside an orthonormal triple, where the core lemma
makes the extension a quadratic form. -/
theorem extOf_parallelogramR {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hquad : ∀ e : Fin 3 → EuclideanSpace ℝ (Fin N), Orthonormal ℝ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u)
    (hN : 3 ≤ N) (u v : EuclideanSpace ℝ (Fin N)) :
    extOf f (u + v) + extOf f (u - v) = 2 * extOf f u + 2 * extOf f v := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hev : extOf f (-v) = extOf f v := by
      have := extOf_smul hneg (-1) v
      simpa using this
    rw [zero_add, zero_sub, hev, extOf_zero]
    ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖u‖ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℝ (Fin N), x = (r⁻¹ : ℝ) • u := ⟨_, rfl⟩
  have hun : 0 < r := hr ▸ norm_pos_iff.mpr hu
  have hxn : ‖x‖ = 1 := by rw [hx, hr]; exact norm_inv_smul_selfR hu
  have hux : u = r • x := by
    rw [hx, smul_smul, mul_inv_cancel₀ hun.ne', one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ⟪x, v⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin N), w = v - c • x := ⟨_, rfl⟩
  have hxw : ⟪x, w⟫_ℝ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hxn, hc]
    ring
  rcases eq_or_ne w 0 with hw0 | hw0
  · have hv : v = c • x := by
      rw [hw] at hw0
      exact sub_eq_zero.mp hw0
    have e1 : u + v = (r + c) • x := by rw [hv, hux, add_smul]
    have e2 : u - v = (r - c) • x := by rw [hv, hux, sub_smul]
    rw [e1, e2, hv, hux, extOf_smul hneg, extOf_smul hneg, extOf_smul hneg, extOf_smul hneg]
    ring
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖w‖ := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin N), y = (t⁻¹ : ℝ) • w := ⟨_, rfl⟩
    have hwn : 0 < t := ht ▸ norm_pos_iff.mpr hw0
    have hyn : ‖y‖ = 1 := by rw [hy, ht]; exact norm_inv_smul_selfR hw0
    have hxy0 : ⟪x, y⟫_ℝ = 0 := by
      rw [hy, real_inner_smul_right, hxw, mul_zero]
    have hyx0 : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy0]
    have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hxn]; norm_num
    have hyy : ⟪y, y⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hyn]; norm_num
    have hxy : Orthonormal ℝ ![x, y] := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
      · simpa using hxx
      · simpa using hxy0
      · simpa using hyx0
      · simpa using hyy
    have hwy : w = t • y := by
      rw [hy, smul_smul, mul_inv_cancel₀ hwn.ne', one_smul]
    have hv : v = c • x + t • y := by
      rw [← hwy, hw]; abel
    have e1 : u + v = (r + c) • x + t • y := by
      rw [hux, hv, add_smul]; abel
    have e2 : u - v = (r - c) • x + (-t) • y := by
      rw [hux, hv, sub_smul, neg_smul]; abel
    obtain ⟨c₀, c₁, c₂, hplane⟩ := exists_extOf_plane hquad hneg hN hxy
    have hu' : extOf f u = c₀ * r ^ 2 + c₁ * r * 0 + c₂ * 0 ^ 2 := by
      rw [show u = r • x + (0 : ℝ) • y from by rw [zero_smul, add_zero, hux], hplane]
    rw [e1, e2, hplane, hplane, hu', hv, hplane]
    ring

/-- The extension is quadratic-like: the four hypotheses of the Jordan–von Neumann engine. -/
theorem isQuadraticLikeR_extOf {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hquad : ∀ e : Fin 3 → EuclideanSpace ℝ (Fin N), Orthonormal ℝ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u)
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v)
    (hub : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v ≤ 1)
    (hN : 3 ≤ N) : IsQuadraticLikeR (extOf f) :=
  ⟨extOf_smul hneg, extOf_parallelogramR hquad hneg hN, extOf_nonneg h0, extOf_le_normSq hub⟩

/-- ★★ **A4, the real reduction.** A function on the unit sphere of `ℝᴺ` (`N ≥ 3`) that is even,
between `0` and `1`, and a symmetric quadratic form on the span of every orthonormal triple, is the
quadratic form of a single symmetric matrix. -/
theorem exists_isSymm_sphere_of_quad {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hquad : ∀ e : Fin 3 → EuclideanSpace ℝ (Fin N), Orthonormal ℝ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f (combR e x) = ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (hneg : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → f (-u) = f u)
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v)
    (hub : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v ≤ 1)
    (hN : 3 ≤ N) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ, A.IsSymm ∧
      ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) := by
  have hq := isQuadraticLikeR_extOf hquad hneg h0 hub hN
  exact ⟨polarMatrixR (extOf f), hq.polarMatrixR_isSymm, fun v hv => by
    rw [← extOf_of_norm_one f hv, hq.eq_dotProduct v]⟩

namespace RealProjectionPackage

variable (OP : RealProjectionPackage N)

/-- ★★ **A4 for a projection package.** For `N ≥ 3` the frame function of a real projection package
is the quadratic form of a symmetric matrix on the unit sphere. -/
theorem exists_isSymm_sphere (hN : 3 ≤ N) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ, A.IsSymm ∧
      ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → OP.frame v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) :=
  exists_isSymm_sphere_of_quad (fun _ he => OP.exists_isSymm_restrictR he)
    (fun u _ => OP.frame_neg u) (fun _ hv => OP.frame_nonneg hv) (fun _ hv => OP.frame_le_one hv) hN

end RealProjectionPackage

/-! ### Matrix facts for the real descent -/

lemma isHermitian_of_isSymmR {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact hA.apply i j

lemma isSymm_of_isHermitianR {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) : A.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  have h := congrFun (congrFun hA i) j
  rwa [Matrix.conjTranspose_apply, star_trivial] at h

/-- The quadratic form at a standard basis vector is the diagonal entry. -/
lemma dotProduct_mulVec_singleR (A : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    (⇑(EuclideanSpace.single i (1 : ℝ)) : Fin N → ℝ)
        ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℝ))) = A i i := by
  simp [dotProduct, Matrix.mulVec]

/-- **The trace is the sum of the quadratic form over the standard basis.** -/
theorem trace_eq_sum_sphereR (A : Matrix (Fin N) (Fin N) ℝ) :
    A.trace = ∑ i, (⇑(EuclideanSpace.single i (1 : ℝ)) : Fin N → ℝ)
      ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℝ))) := by
  simp only [dotProduct_mulVec_singleR, Matrix.trace, Matrix.diag_apply]

/-- A nonzero real coordinate vector is a positive multiple of a unit vector. -/
lemma exists_norm_one_smul_eqR {x : Fin N → ℝ} (hx : x ≠ 0) :
    ∃ (r : ℝ) (v : EuclideanSpace ℝ (Fin N)), 0 < r ∧ ‖v‖ = 1 ∧ x = r • (⇑v : Fin N → ℝ) := by
  obtain ⟨X, hX⟩ : ∃ X : EuclideanSpace ℝ (Fin N), X = WithLp.toLp 2 x := ⟨_, rfl⟩
  have hX0 : X ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun y : EuclideanSpace ℝ (Fin N) => (⇑y : Fin N → ℝ)) h
    simpa [hX] using this
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  refine ⟨‖X‖, (‖X‖⁻¹ : ℝ) • X, hn, norm_inv_smul_selfR hX0, ?_⟩
  rw [show (⇑((‖X‖⁻¹ : ℝ) • X) : Fin N → ℝ) = (‖X‖⁻¹ : ℝ) • (⇑X : Fin N → ℝ) from rfl,
    smul_smul, mul_inv_cancel₀ hn.ne', one_smul, hX]

/-- **A symmetric matrix with nonnegative quadratic form on the unit sphere is positive
semidefinite.** -/
theorem posSemidef_of_sphere_nonnegR {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (h : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ (⇑v : Fin N → ℝ) ⬝ᵥ (A *ᵥ ⇑v)) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
  rw [star_trivial]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨r, v, hr, hv, rfl⟩ := exists_norm_one_smul_eqR hx
  rw [dotProduct_mulVec_smulR]
  exact mul_nonneg (by positivity) (h v hv)

/-- **A real symmetric matrix is determined by its quadratic form on the unit sphere.** -/
theorem eq_of_sphere_quadForm_eqR {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm)
    (hB : B.IsSymm)
    (h : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 →
      (⇑v : Fin N → ℝ) ⬝ᵥ (A *ᵥ ⇑v) = (⇑v : Fin N → ℝ) ⬝ᵥ (B *ᵥ ⇑v)) : A = B := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin N) (Fin N) ℝ, D = A - B := ⟨_, rfl⟩
  have hDsymm : D.IsSymm := by
    rw [hD]
    exact hA.sub hB
  have hall : ∀ x : Fin N → ℝ, x ⬝ᵥ (D *ᵥ x) = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    obtain ⟨r, v, _, hv, rfl⟩ := exists_norm_one_smul_eqR hx
    rw [dotProduct_mulVec_smulR, hD, Matrix.sub_mulVec, dotProduct_sub, h v hv, sub_self, mul_zero]
  have hentry : ∀ i j, D i j = 0 := by
    intro i j
    have hii := hall (⇑(EuclideanSpace.single i (1 : ℝ)))
    have hjj := hall (⇑(EuclideanSpace.single j (1 : ℝ)))
    have hij := hall (⇑(EuclideanSpace.single i (1 : ℝ)) + ⇑(EuclideanSpace.single j (1 : ℝ)))
    rw [dotProduct_mulVec_singleR] at hii hjj
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_mulVec_singleR, dotProduct_mulVec_singleR] at hij
    have hcross : (⇑(EuclideanSpace.single i (1 : ℝ)) : Fin N → ℝ)
        ⬝ᵥ (D *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ))) = D i j := by
      simp [dotProduct, Matrix.mulVec]
    have hcross' : (⇑(EuclideanSpace.single j (1 : ℝ)) : Fin N → ℝ)
        ⬝ᵥ (D *ᵥ ⇑(EuclideanSpace.single i (1 : ℝ))) = D j i := by
      simp [dotProduct, Matrix.mulVec]
    rw [hcross, hcross', hii, hjj, hDsymm.apply i j] at hij
    linarith
  rw [← sub_eq_zero, ← hD]
  ext i j
  rw [hentry i j, Matrix.zero_apply]

/-- ★ **From a quadratic form on the sphere to a real density matrix.** -/
theorem quadraticForm_on_sphere_to_densityR {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : ∀ v, ‖v‖ = 1 → f v = (⇑v : Fin N → ℝ) ⬝ᵥ (A *ᵥ ⇑v))
    (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) (h1 : ∑ i, f (EuclideanSpace.single i (1 : ℝ)) = 1) :
    A.PosSemidef ∧ A.trace = 1 ∧ ∀ B : Matrix (Fin N) (Fin N) ℝ, B.IsSymm →
      (∀ v, ‖v‖ = 1 → f v = (⇑v : Fin N → ℝ) ⬝ᵥ (B *ᵥ ⇑v)) → B = A := by
  have hsingle : ∀ i : Fin N, ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := fun i => by
    rw [PiLp.norm_single]
    exact norm_one
  refine ⟨posSemidef_of_sphere_nonnegR (isHermitian_of_isSymmR hA) fun v hv =>
      (hf v hv) ▸ h0 v hv, ?_, ?_⟩
  · rw [trace_eq_sum_sphereR,
      show (∑ i, (⇑(EuclideanSpace.single i (1 : ℝ)) : Fin N → ℝ)
            ⬝ᵥ (A *ᵥ ⇑(EuclideanSpace.single i (1 : ℝ))))
          = ∑ i, f (EuclideanSpace.single i (1 : ℝ)) from
        Finset.sum_congr rfl fun i _ => (hf _ (hsingle i)).symm]
    exact h1
  · intro B hB hfB
    exact eq_of_sphere_quadForm_eqR hB hA fun v hv => by rw [← hfB v hv, hf v hv]

/-- **Spectral resolution as a sum of real rank-ones.** -/
theorem _root_.Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOneR
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    A = ∑ i, hA.eigenvalues i • rankOneR (hA.eigenvectorBasis i) := by
  calc A = A * ∑ i, rankOneR (hA.eigenvectorBasis i) := by
        rw [sum_rankOneR_orthonormalBasis, Matrix.mul_one]
    _ = ∑ i, hA.eigenvalues i • rankOneR (hA.eigenvectorBasis i) := by
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [rankOneR, mul_vecMulVec, hA.mulVec_eigenvectorBasis, smul_vecMulVec]

/-- The eigenvalues of a real orthogonal projection are `0` or `1`. -/
theorem eigenvalues_eq_zero_or_oneR {P : Matrix (Fin N) (Fin N) ℝ} (hP : IsStarProjection P)
    (hPh : P.IsHermitian) (i : Fin N) : hPh.eigenvalues i = 0 ∨ hPh.eigenvalues i = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, b = hPh.eigenvectorBasis := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = hPh.eigenvalues i := ⟨_, rfl⟩
  have h1 : P *ᵥ (P *ᵥ (⇑(b i) : Fin N → ℝ)) = (l * l) • (⇑(b i) : Fin N → ℝ) := by
    rw [hb, hl, hPh.mulVec_eigenvectorBasis, Matrix.mulVec_smul, hPh.mulVec_eigenvectorBasis,
      smul_smul]
  have h2 : P *ᵥ (P *ᵥ (⇑(b i) : Fin N → ℝ)) = l • (⇑(b i) : Fin N → ℝ) := by
    rw [Matrix.mulVec_mulVec, hP.isIdempotentElem.eq, hb, hl, hPh.mulVec_eigenvectorBasis]
  have hne : (⇑(b i) : Fin N → ℝ) ≠ 0 := by
    intro h
    have hn := b.orthonormal.norm_eq_one i
    rw [show b i = 0 from by ext j; exact congrFun h j] at hn
    simp at hn
  have h3 : (l * l - l) • (⇑(b i) : Fin N → ℝ) = 0 := by
    rw [sub_smul, h1.symm.trans h2, sub_self]
  have h4 : l * l - l = 0 := (smul_eq_zero.mp h3).resolve_right hne
  have h5 : l * (l - 1) = 0 := by rw [← h4]; ring
  rcases mul_eq_zero.mp h5 with h | h
  · exact Or.inl (hl ▸ h)
  · exact Or.inr (hl ▸ sub_eq_zero.mp h)

/-- **`Tr(R · |v⟩⟨v|) = ⟪v, R v⟫`** over `ℝ`. -/
theorem trace_mul_rankOneR (R : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    (R * rankOneR v).trace = (⇑v : Fin N → ℝ) ⬝ᵥ (R *ᵥ ⇑v) := by
  simp only [rankOneR, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

namespace RealProjectionPackage

variable (OP : RealProjectionPackage N)

/-- The weighted rank-one `λ • |b⟩⟨b|` with `λ ∈ {0, 1}` is a projection. -/
lemma isStarProjection_smul_rankOneR {l : ℝ} (hl : l = 0 ∨ l = 1)
    {b : EuclideanSpace ℝ (Fin N)} (hb : ‖b‖ = 1) : IsStarProjection (l • rankOneR b) := by
  rcases hl with rfl | rfl
  · simp
  · simpa using isStarProjection_rankOneR hb

/-- `p (λ • |b⟩⟨b|) = λ · frame b` for `λ ∈ {0, 1}`. -/
lemma p_smul_rankOneR {l : ℝ} (hl : l = 0 ∨ l = 1) (b : EuclideanSpace ℝ (Fin N)) :
    OP.p (l • rankOneR b) = l * OP.frame b := by
  rcases hl with rfl | rfl
  · simp [OP.p_zero]
  · simp [frame]

/-- **The projection descent over `ℝ`.** If the frame function is the quadratic form of `A` on the
unit sphere, then `p P = Tr(A P)` for every orthogonal projection `P`. -/
theorem p_eq_trace {A : Matrix (Fin N) (Fin N) ℝ}
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (⇑v : Fin N → ℝ) ⬝ᵥ (A *ᵥ ⇑v))
    {P : Matrix (Fin N) (Fin N) ℝ} (hP : IsStarProjection P) :
    OP.p P = (A * P).trace := by
  have hPh : P.IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  obtain ⟨b, hb⟩ : ∃ b, b = hPh.eigenvectorBasis := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = hPh.eigenvalues := ⟨_, rfl⟩
  have hspec : P = ∑ i, l i • rankOneR (b i) := by
    rw [hb, hl]
    exact hPh.eq_sum_eigenvalues_smul_rankOneR
  have hl01 : ∀ i, l i = 0 ∨ l i = 1 := by
    rw [hl]
    exact eigenvalues_eq_zero_or_oneR hP hPh
  have hunit : ∀ i, ‖b i‖ = 1 := b.orthonormal.norm_eq_one
  have hsum : OP.p P = ∑ i, l i * OP.frame (b i) := by
    rw [hspec, OP.p_sum _ (fun i => isStarProjection_smul_rankOneR (hl01 i) (hunit i))
      (fun i j hij => by
        rw [smul_mul_smul_comm, rankOneR_mul_rankOneR_of_orthonormal b.orthonormal hij,
          smul_zero])]
    exact Finset.sum_congr rfl fun i _ => OP.p_smul_rankOneR (hl01 i) (b i)
  rw [hsum]
  conv_rhs => rw [hspec, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf _ (hunit i), Matrix.mul_smul, Matrix.trace_smul, trace_mul_rankOneR, smul_eq_mul]

/-- ★★ **Gleason's conclusion over `ℝ` from the quadratic-form hypothesis.** -/
theorem existsUnique_density_of_frame_quadraticR {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm)
    (hf : ∀ v, ‖v‖ = 1 → OP.frame v = (⇑v : Fin N → ℝ) ⬝ᵥ (A *ᵥ ⇑v)) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = (ρ * P).trace := by
  obtain ⟨hpsd, htr, huniq⟩ := quadraticForm_on_sphere_to_densityR hA hf
    (fun v hv => OP.frame_nonneg hv)
    (by
      have h := OP.sum_frame_orthonormalBasis (EuclideanSpace.basisFun (Fin N) ℝ)
      simpa [EuclideanSpace.basisFun_apply] using h)
  refine ⟨A, ⟨hpsd, htr, fun P hP => OP.p_eq_trace hf hP⟩, ?_⟩
  rintro ρ ⟨hρ, -, hρp⟩
  refine huniq ρ (isSymm_of_isHermitianR hρ.isHermitian) fun v hv => ?_
  rw [frame, hρp _ (isStarProjection_rankOneR hv), trace_mul_rankOneR]

/-- ★★★ **Gleason's theorem for real Hilbert spaces, `N ≥ 3`.** Every real projection package is
`P ↦ Tr(ρ P)` for a unique real density matrix `ρ`. The reduction to the core lemma is the
three-vector argument: any two vectors lie in a plane, every plane sits inside an orthonormal
triple, and the frame function restricted to the span of a triple is a frame function on `ℝ³`
(`isFrameFunction_restrictR`), where the core lemma of #57 applies. -/
theorem real_gleason_representation (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = (ρ * P).trace := by
  obtain ⟨A, hA, hf⟩ := OP.exists_isSymm_sphere hN
  exact OP.existsUnique_density_of_frame_quadraticR hA hf

end RealProjectionPackage

end Gleason
