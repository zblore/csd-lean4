/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Gleason's theorem, finite-dimensional: the projection package and its frame function

**Category:** 1-Mathlib (CSD-free; staged for upstream). The statement side of the
finite-dimensional Gleason theorem, and the reductions of its "Layer A" that are pure linear
algebra (`specs/gleason-feasibility.md`).

A **projection package** on `ℂᴺ` assigns to every orthogonal projection `P` (an `IsStarProjection`
matrix — self-adjoint idempotent) a number `p P` with `0 ≤ p P`, `p 1 = 1`, and
`p (P + Q) = p P + p Q` whenever `P * Q = 0`. Gleason's theorem says that for `N ≥ 3` such a
`p` is `P ↦ Tr(ρ P)` for a unique density matrix `ρ`; this file does not prove it (the core
lemma on the real sphere `S²` is open, see `specs/gleason-feasibility.md`) but sets up:

* `rankOne v = |v⟩⟨v|`, a star projection for `‖v‖ = 1` (`isStarProjection_rankOne`), phase
  invariant (`rankOne_smul_of_norm_one`), with `∑ᵢ rankOne (bᵢ) = 1` over every orthonormal basis
  (`sum_rankOne_orthonormalBasis`) and pairwise-orthogonal products over orthonormal families;
* `ProjectionPackage.p_sum` — additivity over any finite family of pairwise-orthogonal
  projections (induction on `IsStarProjection.add`), `p_zero`, `p_le_one`;
* **A1**, the frame function `frame v = p (rankOne v)`: nonnegative, at most `1`, constant on
  phases (`frame_smul`), summing to `1` over every orthonormal basis
  (`sum_frame_orthonormalBasis`), i.e. `IsFrameFunction ℂ OP.frame 1`;
* **A2**, restriction: for a complex-orthonormal family `e : Fin k → ℂᴺ`, the function
  `realRestrict OP e x = frame (∑ᵢ xᵢ eᵢ)` on `ℝᵏ` is a real frame function with weight
  `p (∑ᵢ rankOne (eᵢ))` (`isFrameFunction_realRestrict`) — for `k = 3` a frame function on the
  real sphere `S²`, the input of Gleason's core lemma.

## Design

Projections are matrices with `IsStarProjection` (Mathlib's self-adjoint idempotents), and `p`
is a total function on matrices whose values off the projections are never constrained: this
keeps every statement free of subtypes, and Mathlib's `IsStarProjection.add` is exactly the
closure property the additivity axiom needs. Vectors live in `EuclideanSpace ℂ (Fin N)` and
rank-one projections are `vecMulVec v (star v)`, so `Matrix.posSemidef_vecMulVec_self_star` and
the `vecMulVec` calculus apply verbatim.

## Source

Gleason 1957, *J. Math. Mech.* **6**, 885 (§1 frame functions, §3 the complex reduction);
Cooke–Keane–Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117 (the elementary proof
of the core lemma).
-/

@[expose] public section

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace Gleason

/-! ### Column matrices and Gram identities, over any `RCLike` field -/

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {N k : ℕ}

/-- The matrix whose `i`-th column is `e i`. -/
def colMatrix (e : Fin k → EuclideanSpace 𝕜 (Fin N)) : Matrix (Fin N) (Fin k) 𝕜 :=
  Matrix.of fun a i => e i a

omit [RCLike 𝕜] in
@[simp] lemma colMatrix_apply (e : Fin k → EuclideanSpace 𝕜 (Fin N)) (a : Fin N) (i : Fin k) :
    colMatrix e a i = e i a := rfl

/-- The Gram matrix of a family: `(Eᴴ E) i j = ⟪e i, e j⟫`. -/
lemma conjTranspose_mul_colMatrix_apply (e : Fin k → EuclideanSpace 𝕜 (Fin N)) (i j : Fin k) :
    ((colMatrix e)ᴴ * colMatrix e) i j = ⟪e i, e j⟫_𝕜 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colMatrix_apply, PiLp.inner_apply,
    RCLike.inner_apply', RCLike.star_def]

/-- An orthonormal family has Gram matrix `1`. -/
lemma conjTranspose_mul_colMatrix_of_orthonormal {e : Fin k → EuclideanSpace 𝕜 (Fin N)}
    (he : Orthonormal 𝕜 e) : (colMatrix e)ᴴ * colMatrix e = 1 := by
  ext i j
  rw [conjTranspose_mul_colMatrix_apply, orthonormal_iff_ite.mp he, Matrix.one_apply]

/-- An orthonormal basis has `E Eᴴ = 1` as well (square matrices). -/
lemma colMatrix_mul_conjTranspose_of_orthonormalBasis
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N))) :
    colMatrix b * (colMatrix b)ᴴ = 1 :=
  mul_eq_one_comm.mp (conjTranspose_mul_colMatrix_of_orthonormal b.orthonormal)

/-- `E *ᵥ c = ∑ᵢ cᵢ • eᵢ`. -/
lemma colMatrix_mulVec (e : Fin k → EuclideanSpace 𝕜 (Fin N)) (c : Fin k → 𝕜) :
    colMatrix e *ᵥ c = ⇑(∑ i, c i • e i) := by
  ext a
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- `∑ᵢ |eᵢ⟩⟨eᵢ| = E Eᴴ`. -/
lemma sum_vecMulVec_eq_colMatrix_mul (e : Fin k → EuclideanSpace 𝕜 (Fin N)) :
    ∑ i, vecMulVec (⇑(e i)) (star ⇑(e i)) = colMatrix e * (colMatrix e)ᴴ := by
  ext a c
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]

end Gram

/-! ### Rank-one projections -/

variable {N : ℕ}

/-- **The rank-one projection** `|v⟩⟨v|` onto `v` (a projection when `‖v‖ = 1`). -/
def rankOne (v : EuclideanSpace ℂ (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  vecMulVec (⇑v) (star ⇑v)

lemma rankOne_apply (v : EuclideanSpace ℂ (Fin N)) (a c : Fin N) :
    rankOne v a c = v a * conj (v c) := rfl

lemma rankOne_posSemidef (v : EuclideanSpace ℂ (Fin N)) : (rankOne v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (R := ℂ) (⇑v)

lemma rankOne_isHermitian (v : EuclideanSpace ℂ (Fin N)) : (rankOne v).IsHermitian :=
  (rankOne_posSemidef v).isHermitian

/-- `|v⟩⟨v| |w⟩⟨w| = ⟪v, w⟫ |v⟩⟨w|`. -/
lemma rankOne_mul_rankOne (v w : EuclideanSpace ℂ (Fin N)) :
    rankOne v * rankOne w = ⟪v, w⟫_ℂ • vecMulVec (⇑v) (star ⇑w) := by
  rw [rankOne, rankOne, vecMulVec_mul_vecMulVec, vecMulVec_smul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma rankOne_mul_self {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) :
    rankOne v * rankOne v = rankOne v := by
  rw [rankOne_mul_rankOne, inner_self_eq_norm_sq_to_K, hv]
  simp [rankOne]

lemma rankOne_mul_rankOne_of_inner_eq_zero {v w : EuclideanSpace ℂ (Fin N)}
    (h : ⟪v, w⟫_ℂ = 0) : rankOne v * rankOne w = 0 := by
  rw [rankOne_mul_rankOne, h, zero_smul]

/-- `|v⟩⟨v|` is an orthogonal projection for every unit vector `v`. -/
lemma isStarProjection_rankOne {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) :
    IsStarProjection (rankOne v) where
  isIdempotentElem := rankOne_mul_self hv
  isSelfAdjoint := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
    exact (rankOne_isHermitian v).eq

/-- Phase invariance: `|c v⟩⟨c v| = |v⟩⟨v|` for `‖c‖ = 1`. -/
lemma rankOne_smul_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    rankOne (c • v) = rankOne v := by
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  rw [rankOne, rankOne]
  change vecMulVec (c • ⇑v) (star (c • ⇑v)) = _
  rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, Complex.star_def, hcc, one_smul]

/-- The rank-one projections of an orthonormal family are pairwise orthogonal. -/
lemma rankOne_mul_rankOne_of_orthonormal {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {i j : Fin k} (hij : i ≠ j) : rankOne (e i) * rankOne (e j) = 0 :=
  rankOne_mul_rankOne_of_inner_eq_zero (he.inner_eq_zero hij)

/-- `∑ᵢ |eᵢ⟩⟨eᵢ| = E Eᴴ` for the column matrix `E` of the family. -/
lemma sum_rankOne_eq (e : Fin N → EuclideanSpace ℂ (Fin N)) :
    ∑ i, rankOne (e i) = colMatrix e * (colMatrix e)ᴴ :=
  sum_vecMulVec_eq_colMatrix_mul e

/-- **Resolution of the identity:** `∑ᵢ |bᵢ⟩⟨bᵢ| = 1` over an orthonormal basis. -/
lemma sum_rankOne_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, rankOne (b i) = 1 := by
  rw [sum_rankOne_eq, colMatrix_mul_conjTranspose_of_orthonormalBasis]

/-! ### Frame functions -/

/-- **A frame function** on `𝕜ⁿ` with weight `W`: `∑ᵢ f (bᵢ) = W` over every orthonormal basis
(Gleason 1957, §1). -/
def IsFrameFunction (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (f : EuclideanSpace 𝕜 (Fin n) → ℝ)
    (W : ℝ) : Prop :=
  ∀ b : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)), ∑ i, f (b i) = W

/-! ### The projection package -/

/-- **A projection package** on `ℂᴺ`: a nonnegative, normalised, orthogonally additive
assignment on the orthogonal projections. The values of `p` off the projections are
unconstrained and never used. -/
structure ProjectionPackage (N : ℕ) where
  /-- The assignment. -/
  p : Matrix (Fin N) (Fin N) ℂ → ℝ
  /-- `0 ≤ p P` for every projection. -/
  nonneg : ∀ P, IsStarProjection P → 0 ≤ p P
  /-- `p 1 = 1`. -/
  total_one : p 1 = 1
  /-- `p (P + Q) = p P + p Q` for orthogonal projections (`P * Q = 0`). -/
  additive : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 → p (P + Q) = p P + p Q

namespace ProjectionPackage

variable (OP : ProjectionPackage N)

/-- `p 0 = 0`: `0 = 0 + 0` with `0 * 0 = 0`. -/
theorem p_zero : OP.p 0 = 0 := by
  have h := OP.additive 0 0 (IsStarProjection.zero _) (IsStarProjection.zero _) (by simp)
  rw [add_zero] at h
  linarith

/-- `p P ≤ 1`: `P + (1 − P) = 1` and `p (1 − P) ≥ 0`. -/
theorem p_le_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsStarProjection P) : OP.p P ≤ 1 := by
  have h := OP.additive P (1 - P) hP hP.one_sub hP.mul_one_sub_self
  rw [add_sub_cancel, OP.total_one] at h
  have := OP.nonneg (1 - P) hP.one_sub
  linarith

/-- A finite sum of pairwise-orthogonal projections is a projection. -/
theorem isStarProjection_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ)
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
theorem p_sum {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ)
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

/-- **The frame function of the package:** `frame v = p |v⟩⟨v|`. -/
def frame (v : EuclideanSpace ℂ (Fin N)) : ℝ := OP.p (rankOne v)

theorem frame_nonneg {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : 0 ≤ OP.frame v :=
  OP.nonneg _ (isStarProjection_rankOne hv)

theorem frame_le_one {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : OP.frame v ≤ 1 :=
  OP.p_le_one (isStarProjection_rankOne hv)

/-- The frame function is constant on phases. -/
theorem frame_smul {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    OP.frame (c • v) = OP.frame v := by
  rw [frame, frame, rankOne_smul_of_norm_one hc]

/-- Additivity over the rank-one projections of an orthonormal family. -/
theorem p_sum_rankOne {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)} (he : Orthonormal ℂ e) :
    OP.p (∑ i, rankOne (e i)) = ∑ i, OP.frame (e i) :=
  OP.p_sum _ (fun i => isStarProjection_rankOne (he.norm_eq_one i))
    (fun _ _ hij => rankOne_mul_rankOne_of_orthonormal he hij) Finset.univ

/-- **A1.** The frame function sums to `1` over every orthonormal basis. -/
theorem sum_frame_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, OP.frame (b i) = 1 := by
  rw [← OP.p_sum_rankOne b.orthonormal, sum_rankOne_orthonormalBasis, OP.total_one]

/-- **A1, packaged:** `frame` is a complex frame function of weight `1`. -/
theorem isFrameFunction_frame : IsFrameFunction ℂ OP.frame 1 :=
  OP.sum_frame_orthonormalBasis

/-! ### A2 — restriction to a completely real subspace -/

/-- The vectors of `ℂᴺ` with real coordinates in a complex-orthonormal family `e`: the
completely real subspace `span_ℝ {e₁, …, eₖ}`, parametrised by `ℝᵏ`. -/
def realCombination {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N))
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℂ (Fin N) :=
  ∑ i, ((x i : ℝ) : ℂ) • e i

/-- The complex column matrix of a real vector family. -/
lemma colMatrix_map_ofReal {k : ℕ} (b : Fin k → EuclideanSpace ℝ (Fin k)) :
    colMatrix (fun j => WithLp.toLp 2 fun i => ((b j i : ℝ) : ℂ))
      = (colMatrix b).map ((↑) : ℝ → ℂ) := by
  ext a i
  rfl

/-- Transporting a real orthonormal family through a complex-orthonormal `e` gives a
complex-orthonormal family: `Gram = Bᴴ (Eᴴ E) B = Bᴴ B = 1`. -/
lemma orthonormal_realCombination {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {b : Fin k → EuclideanSpace ℝ (Fin k)} (hb : Orthonormal ℝ b) :
    Orthonormal ℂ fun j => realCombination e (b j) := by
  rw [orthonormal_iff_ite]
  intro j l
  have hcol : colMatrix (fun j => realCombination e (b j))
      = colMatrix e * (colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext a j
    simp [realCombination, colMatrix_apply, Matrix.mul_apply, mul_comm]
  have hgram := conjTranspose_mul_colMatrix_apply (fun j => realCombination e (b j)) j l
  rw [hcol, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (colMatrix e)ᴴ,
    conjTranspose_mul_colMatrix_of_orthonormal he, Matrix.one_mul] at hgram
  rw [← hgram]
  have hB := conjTranspose_mul_colMatrix_of_orthonormal hb
  have hBc : ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ * (colMatrix b).map ((↑) : ℝ → ℂ)
      = ((colMatrix b)ᴴ * colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext i i'
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  rw [hBc, hB]
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The rank-one projections of a transported orthonormal basis sum to those of `e`:
`∑ⱼ |wⱼ⟩⟨wⱼ| = E (B Bᴴ) Eᴴ = E Eᴴ = ∑ᵢ |eᵢ⟩⟨eᵢ|`. -/
lemma sum_rankOne_realCombination {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N))
    (b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    ∑ j, rankOne (realCombination e (b j)) = ∑ i, rankOne (e i) := by
  have hcol : colMatrix (fun j => realCombination e (b j))
      = colMatrix e * (colMatrix b).map ((↑) : ℝ → ℂ) := by
    ext a j
    simp [realCombination, colMatrix_apply, Matrix.mul_apply, mul_comm]
  have hBB : (colMatrix b).map ((↑) : ℝ → ℂ) * ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ = 1 := by
    have h := colMatrix_mul_conjTranspose_of_orthonormalBasis b
    have hmap : (colMatrix b).map ((↑) : ℝ → ℂ) * ((colMatrix b).map ((↑) : ℝ → ℂ))ᴴ
        = (colMatrix b * (colMatrix b)ᴴ).map ((↑) : ℝ → ℂ) := by
      ext i i'
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_ofReal]
    rw [hmap, h]
    ext i i'
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [show ∑ j, rankOne (realCombination e (b j))
      = colMatrix (fun j => realCombination e (b j))
        * (colMatrix (fun j => realCombination e (b j)))ᴴ from
      sum_vecMulVec_eq_colMatrix_mul _,
    show ∑ i, rankOne (e i) = colMatrix e * (colMatrix e)ᴴ from
      sum_vecMulVec_eq_colMatrix_mul _,
    hcol, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (colMatrix e)ᴴ,
    hBB, Matrix.one_mul]

/-- A real unit vector transports to a complex unit vector. -/
lemma norm_realCombination {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    ‖realCombination e x‖ = 1 := by
  have hsq : ‖realCombination e x‖ ^ 2 = 1 := by
    rw [← @inner_self_eq_norm_sq ℂ, realCombination, he.inner_sum]
    have hc : ∑ i, conj ((x i : ℝ) : ℂ) * ((x i : ℝ) : ℂ) = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_ofReal, sq]
    rw [hc]
    change ((∑ i, x i ^ 2 : ℝ) : ℂ).re = 1
    rw [Complex.ofReal_re]
    have hx2 := hx
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hx2
    simpa [Real.norm_eq_abs, sq_abs] using hx2
  have := norm_nonneg (realCombination e x)
  nlinarith

/-- **The restriction of the frame function to a completely real subspace**, as a function on
`ℝᵏ`: `realRestrict OP e x = frame (∑ᵢ xᵢ eᵢ)`. -/
def realRestrict {k : ℕ} (e : Fin k → EuclideanSpace ℂ (Fin N)) (x : EuclideanSpace ℝ (Fin k)) :
    ℝ :=
  OP.frame (realCombination e x)

/-- **A2.** For a complex-orthonormal `e : Fin k → ℂᴺ`, the restriction is a real frame function
on `ℝᵏ` with weight `p (∑ᵢ |eᵢ⟩⟨eᵢ|)` — for `k = 3`, a frame function on the sphere `S²`. -/
theorem isFrameFunction_realRestrict {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) :
    IsFrameFunction ℝ (OP.realRestrict e) (OP.p (∑ i, rankOne (e i))) := by
  intro b
  rw [← sum_rankOne_realCombination e b, OP.p_sum_rankOne (orthonormal_realCombination he
    b.orthonormal)]
  rfl

/-- The restriction is nonnegative on the real unit sphere. -/
theorem realRestrict_nonneg {k : ℕ} {e : Fin k → EuclideanSpace ℂ (Fin N)}
    (he : Orthonormal ℂ e) {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    0 ≤ OP.realRestrict e x := by
  exact OP.frame_nonneg (norm_realCombination he hx)

end ProjectionPackage

end Gleason

end
