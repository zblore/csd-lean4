/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Descent
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Gleason's theorem, finite-dimensional: the complex reduction (Layer A3)

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, Layer
A3: **a frame function on `ℂᴺ` that is a quadratic form on every completely real plane is the
quadratic form of a Hermitian matrix.** This is Gleason's §3 reduction of the complex case to
the real one, done without spherical harmonics.

For a projection package `OP` with frame function `f = OP.frame`:

* `IsRealPlaneRegular f` — for every complex-orthonormal pair `(x, y)` and real unit `(α, β)`,
  `f (α x + β y) = f x α² + f y β² + 2 α β · crossTerm f x y`, where
  `crossTerm f x y = f ((x + y)/√2) − (f x + f y)/2` (the off-diagonal entry of the `2 × 2`
  form; this is what "quadratic on the completely real plane `span_ℝ {x, y}`" means once the
  diagonal is pinned by `f x` and `f y`);
* `ProjectionPackage.frame_add_frame_eq` — two orthonormal pairs spanning the same complex
  plane have the same weight (additivity, through a matrix identity);
* `ProjectionPackage.crossTerm_phase` — the key computation: on the "equator" pair
  `w = (x + y)/√2`, `w' = i(x − y)/√2` regularity forces
  `crossTerm f x (e • y) = β₁ Re e + β₂ Im e` for every unit phase `e`, so the phase dependence
  of the cross term is a first-degree trigonometric polynomial;
* `ProjectionPackage.frame_plane_unit`, `ProjectionPackage.ext_plane` — hence on the complex
  plane `span_ℂ {x, y}` the frame function is a Hermitian form:
  `f (a x + b y) = f x |a|² + f y |b|² + 2 Re (conj a · b · S)`;
* `ProjectionPackage.isQuadraticLike_ext` — the degree-2 extension `ext f v = ‖v‖² f (v/‖v‖)`
  satisfies the parallelogram law on all of `ℂᴺ` (any two vectors lie in a complex plane), so
  the Jordan–von Neumann engine (`Gleason/Polarization.lean`) applies;
* ★ `ProjectionPackage.exists_isHermitian_of_isRealPlaneRegular` — **A3**: a Hermitian `A` with
  `f v = Re ⟪v, A v⟫` on the unit sphere;
* `ProjectionPackage.isRealPlaneRegular_of_triples` — the bridge from what Gleason's core lemma
  delivers through A2 (a symmetric `3 × 3` form on every completely real `3`-space, `N ≥ 3`) to
  the plane hypothesis.

With `Gleason/Descent.lean` this reduces Gleason's theorem for `ℂᴺ`, `N ≥ 3`, to the core lemma
on the real sphere `S²` (`specs/gleason-feasibility.md`, Layer B).

## Source

Gleason 1957, *J. Math. Mech.* **6**, 885, §3 (the completely real subspaces); the equator
computation is the one Gleason makes for Lemma 3.3 read through Bloch coordinates.
-/

@[expose] public section

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace Gleason

variable {N : ℕ}

/-- The real scalar `1/√2`, as a complex number. -/
noncomputable def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

@[simp] lemma invSqrtTwo_re : invSqrtTwo.re = (Real.sqrt 2)⁻¹ := rfl
@[simp] lemma invSqrtTwo_im : invSqrtTwo.im = 0 := rfl
@[simp] lemma conj_invSqrtTwo : conj invSqrtTwo = invSqrtTwo := Complex.conj_ofReal _

lemma invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma norm_invSqrtTwo : ‖invSqrtTwo‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrtTwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-! ### Regularity on completely real planes -/

/-- The off-diagonal entry of the `2 × 2` form of `f` on the completely real plane of an
orthonormal pair: `crossTerm f x y = f ((x + y)/√2) − (f x + f y)/2`. -/
noncomputable def crossTerm (f : EuclideanSpace ℂ (Fin N) → ℝ) (x y : EuclideanSpace ℂ (Fin N)) :
    ℝ :=
  f (invSqrtTwo • (x + y)) - (f x + f y) / 2

/-- **Regularity on completely real planes:** for every complex-orthonormal pair and real unit
`(α, β)`, `f (α x + β y) = f x α² + f y β² + 2 α β · crossTerm f x y`. -/
def IsRealPlaneRegular (f : EuclideanSpace ℂ (Fin N) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℂ (Fin N), Orthonormal ℂ ![x, y] → ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 →
    f ((α : ℂ) • x + (β : ℂ) • y) = f x * α ^ 2 + f y * β ^ 2 + 2 * α * β * crossTerm f x y

/-! ### Orthonormal pairs -/

/-- A vector with `⟪v, v⟫ = 1` is a unit vector. -/
lemma norm_eq_one_of_inner_self {v : EuclideanSpace ℂ (Fin N)} (h : ⟪v, v⟫_ℂ = 1) : ‖v‖ = 1 := by
  have h1 : ‖v‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    simp
  nlinarith [norm_nonneg v]

/-- An orthonormal pair, unpacked. -/
lemma orthonormal_pair_iff {x y : EuclideanSpace ℂ (Fin N)} :
    Orthonormal ℂ ![x, y] ↔ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ⟪x, y⟫_ℂ = 0 := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0 0
      simp only [Matrix.cons_val_zero, if_true] at this
      exact norm_eq_one_of_inner_self this
    · have := h 1 1
      simp only [Matrix.cons_val_one, if_true] at this
      exact norm_eq_one_of_inner_self this
    · have := h 0 1
      simpa using this
  · rintro ⟨hx, hy, hxy⟩ i j
    fin_cases i <;> fin_cases j
    · simp [inner_self_eq_norm_sq_to_K, hx]
    · simpa using hxy
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Fin.zero_eta,
        Matrix.cons_val_zero, one_ne_zero, if_false]
      rw [← inner_conj_symm, hxy, map_zero]
    · simp [inner_self_eq_norm_sq_to_K, hy]

/-- Rotating the second vector of an orthonormal pair by a phase keeps it orthonormal. -/
lemma orthonormal_pair_smul {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y])
    {e : ℂ} (he : ‖e‖ = 1) : Orthonormal ℂ ![x, e • y] := by
  rw [orthonormal_pair_iff] at h ⊢
  refine ⟨h.1, ?_, ?_⟩
  · rw [norm_smul, he, one_mul, h.2.1]
  · rw [inner_smul_right, h.2.2, mul_zero]

/-- The "equator" pair `w = (x + y)/√2`, `w' = i (x − y)/√2` of an orthonormal pair. -/
lemma orthonormal_equator {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y]) :
    Orthonormal ℂ ![invSqrtTwo • (x + y),
      invSqrtTwo • (Complex.I • (x - y))] := by
  rw [orthonormal_pair_iff] at h ⊢
  obtain ⟨hx, hy, hxy⟩ := h
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have hs : invSqrtTwo * invSqrtTwo = 1 / 2 := invSqrtTwo_mul_self
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
  have hyy : ⟪y, y⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hy]; simp
  refine ⟨norm_eq_one_of_inner_self ?_, norm_eq_one_of_inner_self ?_, ?_⟩
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo]
    linear_combination (2 : ℂ) * hs
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo, Complex.conj_I]
    linear_combination (2 : ℂ) * hs - (2 * invSqrtTwo * invSqrtTwo) * hI
  · simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right, hxx, hyy, hxy,
      hyx, conj_invSqrtTwo]
    ring

/-! ### The weight of a complex plane is basis independent -/

/-- The parallelogram identity for rank-one projectors:
`|u+v⟩⟨u+v| + |u−v⟩⟨u−v| = 2 |u⟩⟨u| + 2 |v⟩⟨v|`. -/
lemma rankOne_add_add_rankOne_sub (u v : EuclideanSpace ℂ (Fin N)) :
    rankOne (u + v) + rankOne (u - v) = (2 : ℂ) • rankOne u + (2 : ℂ) • rankOne v := by
  ext a c
  simp only [rankOne, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    PiLp.add_apply, PiLp.sub_apply, star_add, star_sub, smul_eq_mul]
  ring

/-- Real scaling of a rank-one projector: `|r v⟩⟨r v| = r² |v⟩⟨v|`. -/
lemma rankOne_real_smul (r : ℝ) (v : EuclideanSpace ℂ (Fin N)) :
    rankOne ((r : ℂ) • v) = ((r ^ 2 : ℝ) : ℂ) • rankOne v := by
  ext a c
  simp only [rankOne, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, PiLp.smul_apply,
    smul_eq_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The equator pair spans the same projector as `(x, y)`:
`|w⟩⟨w| + |w'⟩⟨w'| = |x⟩⟨x| + |y⟩⟨y|`. -/
lemma rankOne_equator (x y : EuclideanSpace ℂ (Fin N)) :
    rankOne (invSqrtTwo • (x + y))
        + rankOne (invSqrtTwo • (Complex.I • (x - y)))
      = rankOne x + rankOne y := by
  have hI : rankOne (invSqrtTwo • (Complex.I • (x - y)))
      = rankOne (invSqrtTwo • (x - y)) := by
    rw [smul_comm, rankOne_smul_of_norm_one (by simp)]
  have hs : ((((Real.sqrt 2)⁻¹ : ℝ) ^ 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring
  rw [hI, invSqrtTwo, rankOne_real_smul, rankOne_real_smul, ← smul_add,
    rankOne_add_add_rankOne_sub, hs, smul_add, smul_smul, smul_smul]
  norm_num

namespace ProjectionPackage

variable (OP : ProjectionPackage N)

/-- `p (|x⟩⟨x| + |y⟩⟨y|) = f x + f y` for an orthonormal pair. -/
lemma p_rankOne_add_rankOne {x y : EuclideanSpace ℂ (Fin N)} (h : Orthonormal ℂ ![x, y]) :
    OP.p (rankOne x + rankOne y) = OP.frame x + OP.frame y := by
  obtain ⟨hx, hy, hxy⟩ := orthonormal_pair_iff.mp h
  exact OP.additive _ _ (isStarProjection_rankOne hx) (isStarProjection_rankOne hy)
    (rankOne_mul_rankOne_of_inner_eq_zero hxy)

/-- **Two orthonormal pairs with the same projector have the same weight.** -/
lemma frame_add_frame_eq {x y w w' : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y])
    (hww : Orthonormal ℂ ![w, w']) (h : rankOne w + rankOne w' = rankOne x + rankOne y) :
    OP.frame w + OP.frame w' = OP.frame x + OP.frame y := by
  rw [← OP.p_rankOne_add_rankOne hxy, ← OP.p_rankOne_add_rankOne hww, h]

/-! ### The phase dependence of the cross term -/

/-- A unit complex number has a unit square root. -/
lemma exists_sq_eq_of_norm_one {e : ℂ} (he : ‖e‖ = 1) : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 = e := by
  refine ⟨e ^ ((2 : ℕ)⁻¹ : ℂ), ?_, Complex.cpow_nat_inv_pow e two_ne_zero⟩
  have h2 : ‖e ^ ((2 : ℕ)⁻¹ : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, Complex.cpow_nat_inv_pow e two_ne_zero, he]
  have := norm_nonneg (e ^ ((2 : ℕ)⁻¹ : ℂ))
  nlinarith

/-- The vector identity behind the equator computation: for `z = α + iβ` of modulus one and
`e = conj z ^ 2`, `α w + β w' = z • ((x + e y)/√2)`. -/
lemma equator_combination (x y : EuclideanSpace ℂ (Fin N)) {z : ℂ} (hz : ‖z‖ = 1) :
    ((z.re : ℝ) : ℂ) • (invSqrtTwo • (x + y))
        + ((z.im : ℝ) : ℂ) • (invSqrtTwo • (Complex.I • (x - y)))
      = z • (invSqrtTwo • (x + (conj z ^ 2) • y)) := by
  have hzz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      invSqrtTwo_re, invSqrtTwo_im, Complex.conj_re, Complex.conj_im, sq]
    linear_combination (-(Real.sqrt 2)⁻¹ * (z.re * (y i).re + z.im * (y i).im)) * hzz
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      invSqrtTwo_re, invSqrtTwo_im, Complex.conj_re, Complex.conj_im, sq]
    linear_combination (-(Real.sqrt 2)⁻¹ * (z.re * (y i).im - z.im * (y i).re)) * hzz

/-- **The cross term is a first-degree trigonometric polynomial in the phase:** for a unit `e`,
`crossTerm f x (e • y) = β₁ Re e + β₂ Im e` with `β₁ = (f w − f w')/2`,
`β₂ = − crossTerm f w w'` for the equator pair `(w, w')`. -/
theorem crossTerm_phase (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) {e : ℂ} (he : ‖e‖ = 1) :
    crossTerm OP.frame x (e • y)
      = (OP.frame (invSqrtTwo • (x + y))
          - OP.frame (invSqrtTwo • (Complex.I • (x - y)))) / 2 * e.re
        - crossTerm OP.frame (invSqrtTwo • (x + y))
          (invSqrtTwo • (Complex.I • (x - y))) * e.im := by
  set w := invSqrtTwo • (x + y) with hw
  set w' := invSqrtTwo • (Complex.I • (x - y)) with hw'
  obtain ⟨z, hz, hz2⟩ := exists_sq_eq_of_norm_one (e := conj e) (by simpa using he)
  have hzconj : conj z ^ 2 = e := by
    rw [← Complex.conj_conj e, ← hz2, map_pow]
  have hzz : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have hcomb := equator_combination x y hz
  rw [hzconj] at hcomb
  have hval : OP.frame (invSqrtTwo • (x + e • y))
      = OP.frame w * z.re ^ 2 + OP.frame w' * z.im ^ 2
        + 2 * z.re * z.im * crossTerm OP.frame w w' := by
    rw [← OP.frame_smul hz, ← hcomb]
    exact hreg w w' (orthonormal_equator hxy) z.re z.im hzz
  have hweight := OP.frame_add_frame_eq hxy (orthonormal_equator hxy) (rankOne_equator x y)
  have hey : OP.frame (e • y) = OP.frame y := OP.frame_smul he y
  -- `e = conj z ^ 2`: `Re e = re² − im²`, `Im e = −2 re im`
  have hre : e.re = z.re ^ 2 - z.im ^ 2 := by
    rw [← hzconj]; simp [sq, Complex.mul_re]
  have him : e.im = -(2 * z.re * z.im) := by
    rw [← hzconj]; simp [sq, Complex.mul_im]; ring
  rw [crossTerm, hval, hey, hre, him]
  have hw2 : OP.frame w' = OP.frame x + OP.frame y - OP.frame w := by linarith
  rw [hw2]
  linear_combination (OP.frame x + OP.frame y) / 2 * hzz

/-! ### The frame function on a complex plane is a Hermitian form -/

/-- The off-diagonal coefficient of the Hermitian form on the plane of `(x, y)`. -/
noncomputable def planeCoeff (x y : EuclideanSpace ℂ (Fin N)) : ℂ :=
  (((OP.frame (invSqrtTwo • (x + y))
      - OP.frame (invSqrtTwo • (Complex.I • (x - y)))) / 2 : ℝ) : ℂ)
    + Complex.I * ((crossTerm OP.frame (invSqrtTwo • (x + y))
      (invSqrtTwo • (Complex.I • (x - y))) : ℝ) : ℂ)

/-- **The frame function on the unit circle of a complex plane:** for `|a|² + |b|² = 1`,
`f (a x + b y) = f x |a|² + f y |b|² + 2 Re (conj a · b · S)`. -/
theorem frame_plane_unit (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) {a b : ℂ} (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    OP.frame (a • x + b • y)
      = OP.frame x * ‖a‖ ^ 2 + OP.frame y * ‖b‖ ^ 2 + 2 * (conj a * b * OP.planeCoeff x y).re := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : ‖b‖ = 1 := by
      have : ‖b‖ ^ 2 = 1 := by simpa using hab
      nlinarith [norm_nonneg b]
    simp [OP.frame_smul hb, hb]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha1 : ‖a‖ = 1 := by
      have : ‖a‖ ^ 2 = 1 := by simpa using hab
      nlinarith [norm_nonneg a]
    simp [OP.frame_smul ha1, ha1]
  -- the phase `c = conj a / |a|` normalises `a`; `e = conj a b / (|a| |b|)` is the relative phase
  set c : ℂ := conj a / (‖a‖ : ℂ) with hc
  set e : ℂ := (conj a * b) / ((‖a‖ : ℂ) * (‖b‖ : ℂ)) with he
  have ha0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hb0 : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  have hca : c * a = (‖a‖ : ℂ) := by
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff ha0]
    ring
  have hcb : c * b = (‖b‖ : ℂ) * e := by
    rw [hc, he]
    field_simp
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr ha)]
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm,
      div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))]
  have hvec : c • (a • x + b • y) = ((‖a‖ : ℝ) : ℂ) • x + ((‖b‖ : ℝ) : ℂ) • (e • y) := by
    rw [smul_add, smul_smul, smul_smul, hca, hcb, ← smul_smul]
  have hmer := hreg x (e • y) (orthonormal_pair_smul hxy hen) ‖a‖ ‖b‖ hab
  rw [← OP.frame_smul hcn, hvec, hmer, OP.frame_smul hen, OP.crossTerm_phase hreg hxy hen]
  -- `|a| |b| e = conj a b`
  set q : ℂ := conj a * b with hq
  have hab' : ((‖a‖ : ℝ) : ℂ) * ((‖b‖ : ℝ) : ℂ) * e = q := by
    rw [he]; field_simp
  have hqre : q.re = ‖a‖ * ‖b‖ * e.re := by
    rw [← hab']; simp [Complex.mul_re]
  have hqim : q.im = ‖a‖ * ‖b‖ * e.im := by
    rw [← hab']; simp [Complex.mul_im]
  rw [planeCoeff]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [hqre, hqim]
  ring

/-! ### The degree-2 extension and the parallelogram law on `ℂᴺ` -/

/-- **The degree-2 extension** of the frame function off the unit sphere:
`ext v = ‖v‖² f (v/‖v‖)`, with `ext 0 = 0`. -/
noncomputable def ext (v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  ‖v‖ ^ 2 * OP.frame (((‖v‖⁻¹ : ℝ) : ℂ) • v)

lemma ext_of_norm_one {v : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) : OP.ext v = OP.frame v := by
  simp [ext, hv]

@[simp] lemma ext_zero : OP.ext 0 = 0 := by simp [ext]

/-- The normalisation of a nonzero vector is a unit vector. -/
lemma norm_inv_smul_self {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
    inv_mul_cancel₀ hn.ne']

/-- Degree-2 homogeneity of the extension under complex scaling. -/
lemma ext_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin N)) : OP.ext (c • v) = ‖c‖ ^ 2 * OP.ext v := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hphase : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hcn.ne']
  have hvec : ((‖c • v‖⁻¹ : ℝ) : ℂ) • (c • v) = (c / (‖c‖ : ℂ)) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) := by
    rw [smul_smul, smul_smul, norm_smul, mul_inv]
    congr 1
    push_cast
    field_simp
  rw [ext, ext, hvec, OP.frame_smul hphase, norm_smul, mul_pow]
  ring

lemma ext_nonneg (v : EuclideanSpace ℂ (Fin N)) : 0 ≤ OP.ext v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  exact mul_nonneg (by positivity) (OP.frame_nonneg (norm_inv_smul_self hv))

lemma ext_le_normSq (v : EuclideanSpace ℂ (Fin N)) : OP.ext v ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  calc OP.ext v ≤ ‖v‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (OP.frame_le_one (norm_inv_smul_self hv)) (by positivity)
    _ = ‖v‖ ^ 2 := mul_one _

/-- `‖a x + b y‖² = |a|² + |b|²` for an orthonormal pair. -/
lemma norm_sq_smul_add_smul {x y : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y])
    (a b : ℂ) : ‖a • x + b • y‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  obtain ⟨hx, hy, hxy'⟩ := orthonormal_pair_iff.mp hxy
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy', map_zero]
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
  have hyy : ⟪y, y⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hy]; simp
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (a • x + b • y)
  rw [← h]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hxx, hyy, hxy',
    hyx, mul_zero, zero_add, add_zero, mul_one, Complex.sq_norm]
  simp [Complex.normSq_apply]

/-- **The extension on a complex plane is a Hermitian form:** for an orthonormal pair `(x, y)`
and all `a b : ℂ`, `ext (a x + b y) = f x |a|² + f y |b|² + 2 Re (conj a · b · S)`. -/
theorem ext_plane (hreg : IsRealPlaneRegular OP.frame) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) (a b : ℂ) :
    OP.ext (a • x + b • y)
      = OP.frame x * ‖a‖ ^ 2 + OP.frame y * ‖b‖ ^ 2 + 2 * (conj a * b * OP.planeCoeff x y).re := by
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp
  have hr2 : 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rcases not_and_or.mp h0 with ha | hb
    · have := norm_pos_iff.mpr ha; positivity
    · have := norm_pos_iff.mpr hb; positivity
  set r : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hr2
  have hrsq : r ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := Real.sq_sqrt hr2.le
  have hnorm : ‖a • x + b • y‖ = r := by
    rw [hr, ← norm_sq_smul_add_smul hxy a b, Real.sqrt_sq (norm_nonneg _)]
  have hunit : ‖a / (r : ℂ)‖ ^ 2 + ‖b / (r : ℂ)‖ ^ 2 = 1 := by
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow,
      div_pow, ← add_div, ← hrsq, div_self (pow_pos hrpos 2).ne']
  have hvec : ((‖a • x + b • y‖⁻¹ : ℝ) : ℂ) • (a • x + b • y)
      = (a / (r : ℂ)) • x + (b / (r : ℂ)) • y := by
    rw [hnorm, smul_add, smul_smul, smul_smul]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hpl := OP.frame_plane_unit hreg hxy hunit
  rw [ext, hvec, hpl, hnorm]
  have hra : ‖a / (r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow]
  have hrb : ‖b / (r : ℂ)‖ ^ 2 = ‖b‖ ^ 2 / r ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_pow]
  have hq : (conj (a / (r : ℂ)) * (b / (r : ℂ)) * OP.planeCoeff x y).re
      = (conj a * b * OP.planeCoeff x y).re / r ^ 2 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, div_mul_eq_mul_div, ← sq,
      ← Complex.ofReal_pow, Complex.div_ofReal_re]
  rw [hra, hrb, hq]
  field_simp

/-- The parallelogram law on a complex plane. -/
lemma ext_parallelogram_plane (hreg : IsRealPlaneRegular OP.frame)
    {x y : EuclideanSpace ℂ (Fin N)} (hxy : Orthonormal ℂ ![x, y]) (a b a' b' : ℂ) :
    OP.ext ((a + a') • x + (b + b') • y) + OP.ext ((a - a') • x + (b - b') • y)
      = 2 * OP.ext (a • x + b • y) + 2 * OP.ext (a' • x + b' • y) := by
  simp only [OP.ext_plane hreg hxy, Complex.sq_norm, Complex.normSq_apply, map_add, map_sub,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- **The parallelogram law on `ℂᴺ`.** Any two vectors lie in a complex plane spanned by an
orthonormal pair (Gram–Schmidt), where `ext` is a Hermitian form. -/
theorem ext_parallelogram (hreg : IsRealPlaneRegular OP.frame) (u v : EuclideanSpace ℂ (Fin N)) :
    OP.ext (u + v) + OP.ext (u - v) = 2 * OP.ext u + 2 * OP.ext v := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hneg : OP.ext (-v) = OP.ext v := by
      have := OP.ext_smul (-1) v
      simpa using this
    simp [hneg]
    ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖u‖ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : EuclideanSpace ℂ (Fin N), x = ((r⁻¹ : ℝ) : ℂ) • u := ⟨_, rfl⟩
  have hun : 0 < r := hr ▸ norm_pos_iff.mpr hu
  have hxn : ‖x‖ = 1 := by rw [hx, hr]; exact norm_inv_smul_self hu
  have hux : u = ((r : ℝ) : ℂ) • x := by
    rw [hx, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hun.ne', Complex.ofReal_one,
      one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ⟪x, v⟫_ℂ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin N), w = v - c • x := ⟨_, rfl⟩
  have hxw : ⟪x, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hxn, hc]
    simp
  rcases eq_or_ne w 0 with hw0 | hw0
  · -- `v` is a multiple of `u`: pure homogeneity
    have hv : v = c • x := by
      rw [hw] at hw0
      exact sub_eq_zero.mp hw0
    have e1 : u + v = (((r : ℝ) : ℂ) + c) • x := by rw [hv, hux, add_smul]
    have e2 : u - v = (((r : ℝ) : ℂ) - c) • x := by rw [hv, hux, sub_smul]
    rw [e1, e2, hv, hux, OP.ext_smul, OP.ext_smul, OP.ext_smul, OP.ext_smul]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · obtain ⟨s', hs'⟩ : ∃ s' : ℝ, s' = ‖w‖ := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℂ (Fin N), y = ((s'⁻¹ : ℝ) : ℂ) • w := ⟨_, rfl⟩
    have hwn : 0 < s' := hs' ▸ norm_pos_iff.mpr hw0
    have hyn : ‖y‖ = 1 := by rw [hy, hs']; exact norm_inv_smul_self hw0
    have hxy : Orthonormal ℂ ![x, y] := by
      rw [orthonormal_pair_iff]
      refine ⟨hxn, hyn, ?_⟩
      rw [hy, inner_smul_right, hxw, mul_zero]
    have hwy : w = ((s' : ℝ) : ℂ) • y := by
      rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hwn.ne', Complex.ofReal_one,
        one_smul]
    have hv : v = c • x + ((s' : ℝ) : ℂ) • y := by
      rw [← hwy, hw]; abel
    have e1 : u + v = (((r : ℝ) : ℂ) + c) • x + ((s' : ℝ) : ℂ) • y := by
      rw [hux, hv, add_smul]; abel
    have e2 : u - v = (((r : ℝ) : ℂ) - c) • x + (-((s' : ℝ) : ℂ)) • y := by
      rw [hux, hv, sub_smul, neg_smul]; abel
    have key := OP.ext_parallelogram_plane hreg hxy ((r : ℝ) : ℂ) 0 c ((s' : ℝ) : ℂ)
    rw [zero_add, zero_sub, zero_smul, add_zero] at key
    rw [e1, e2, key]
    conv_rhs => rw [hux, hv]

/-- **`ext` is quadratic-like:** the four hypotheses of the Jordan–von Neumann engine. -/
theorem isQuadraticLike_ext (hreg : IsRealPlaneRegular OP.frame) : IsQuadraticLike OP.ext :=
  ⟨OP.ext_smul, OP.ext_parallelogram hreg, OP.ext_nonneg, OP.ext_le_normSq⟩

/-- ★ **A3 — the complex reduction.** A frame function that is regular on every completely
real plane is the quadratic form of a Hermitian matrix on the unit sphere. -/
theorem exists_isHermitian_of_isRealPlaneRegular (hreg : IsRealPlaneRegular OP.frame) :
    ∃ A : Matrix (Fin N) (Fin N) ℂ, A.IsHermitian ∧
      ∀ v, ‖v‖ = 1 → OP.frame v = (star (⇑v) ⬝ᵥ (A *ᵥ ⇑v)).re := by
  have hq := OP.isQuadraticLike_ext hreg
  refine ⟨polarMatrix OP.ext, hq.polarMatrix_isHermitian, fun v hv => ?_⟩
  rw [← OP.ext_of_norm_one hv, ← Complex.ofReal_re (OP.ext v), hq.eq_dotProduct v]

/-! ### From completely real `3`-spaces to planes -/

/-- An orthonormal pair in `ℂᴺ`, `N ≥ 3`, extends to an orthonormal triple. -/
lemma exists_orthonormal_triple (hN : 3 ≤ N) {x y : EuclideanSpace ℂ (Fin N)}
    (hxy : Orthonormal ℂ ![x, y]) :
    ∃ z : EuclideanSpace ℂ (Fin N), Orthonormal ℂ ![x, y, z] := by
  classical
  obtain ⟨hx, hy, hxy'⟩ := orthonormal_pair_iff.mp hxy
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy', map_zero]
  have hne : x ≠ y := by
    intro h
    rw [h, inner_self_eq_norm_sq_to_K, hy] at hxy'
    simp at hxy'
  have hset : Orthonormal ℂ ((↑) : ({x, y} : Set (EuclideanSpace ℂ (Fin N))) →
      EuclideanSpace ℂ (Fin N)) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · simp [inner_self_eq_norm_sq_to_K, hx]
    · simp [hxy', hne]
    · simp [hyx, hne.symm]
    · simp [inner_self_eq_norm_sq_to_K, hy]
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
    have : ({x, y} : Finset (EuclideanSpace ℂ (Fin N))).card ≤ 2 := Finset.card_le_two
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
  · simp [inner_self_eq_norm_sq_to_K, hx]
  · simpa using hxy'
  · have := hbo x hxu z hzu
    simpa [Ne.symm hzx] using this
  · simpa [hne.symm] using hyx
  · simp [inner_self_eq_norm_sq_to_K, hy]
  · have := hbo y hyu z hzu
    simpa [Ne.symm hzy] using this
  · have := hbo z hzu x hxu
    simpa [hzx] using this
  · have := hbo z hzu y hyu
    simpa [hzy] using this
  · have := hbo z hzu z hzu
    simpa using this

/-- The real vector `(α, β, 0)` of `ℝ³`, transported. -/
lemma realCombination_two (e : Fin 3 → EuclideanSpace ℂ (Fin N)) (α β : ℝ) :
    realCombination e (WithLp.toLp 2 ![α, β, 0]) = (α : ℂ) • e 0 + (β : ℂ) • e 1 := by
  simp [realCombination, Fin.sum_univ_three]

/-- **The bridge from Gleason's core lemma to the plane hypothesis.** If, for every
complex-orthonormal triple `e`, the restriction of the frame function to the completely real
`3`-space of `e` is a symmetric quadratic form on the sphere of `ℝ³`, then the frame function is
regular on every completely real plane (`N ≥ 3`). -/
theorem isRealPlaneRegular_of_triples (hN : 3 ≤ N)
    (h : ∀ e : Fin 3 → EuclideanSpace ℂ (Fin N), Orthonormal ℂ e →
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → OP.realRestrict e x = ⇑x ⬝ᵥ (A *ᵥ ⇑x)) :
    IsRealPlaneRegular OP.frame := by
  intro x y hxy α β hαβ
  obtain ⟨z, hxyz⟩ := exists_orthonormal_triple hN hxy
  obtain ⟨A, hA, hAf⟩ := h ![x, y, z] hxyz
  have hval : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      OP.frame ((a : ℂ) • x + (b : ℂ) • y)
        = A 0 0 * a ^ 2 + 2 * A 0 1 * a * b + A 1 1 * b ^ 2 := by
    intro a b hab
    have hn : ‖(WithLp.toLp 2 ![a, b, 0] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hab]
    have := hAf _ hn
    rw [realRestrict, realCombination_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, hA.apply 0 1]
    ring
  have h10 : OP.frame x = A 0 0 := by
    have := hval 1 0 (by norm_num)
    simpa using this
  have h01 : OP.frame y = A 1 1 := by
    have := hval 0 1 (by norm_num)
    simpa using this
  have hcross : crossTerm OP.frame x y = A 0 1 := by
    have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 + ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have := hval ((Real.sqrt 2)⁻¹) ((Real.sqrt 2)⁻¹) hs
    rw [crossTerm, invSqrtTwo, smul_add, this, h10, h01]
    linear_combination (A 0 0 + A 1 1 + 2 * A 0 1) / 2 * hs
  rw [hval α β hαβ, h10, h01, hcross]
  ring

end ProjectionPackage

end Gleason

end
