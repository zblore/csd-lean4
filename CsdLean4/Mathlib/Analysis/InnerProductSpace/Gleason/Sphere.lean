/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.ProjectionPackage
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Gleason's theorem, finite-dimensional: frame functions on the sphere `S² ⊂ ℝ³`

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(a), first half: Cooke–Keane–Moran §2 — the elementary properties of frame functions on the
unit sphere of `ℝ³` that every later stage of the core lemma uses.

A *frame* is an orthonormal triple `(p, q, r)`; a *frame function* has `f p + f q + f r = W` on
every frame (`IsFrameFunction ℝ f W`, `Gleason/ProjectionPackage.lean`). This file:

* the tools of `ℝ³`: `cross x y` (the cross product, as a vector of `EuclideanSpace ℝ (Fin 3)`),
  `orthonormal_triple_iff`, `orthonormal_cross` (an orthonormal pair extends to a frame by its
  cross product), `exists_unit_orthogonal_pair` (a unit vector orthogonal to any two vectors —
  the orthogonal complement of a plane is nontrivial in `ℝ³`), and `IsFrameFunction.sum_triple`
  — the frame identity for **any** orthonormal triple, because an orthonormal triple of `ℝ³` is
  an orthonormal basis (`orthonormalBasisOfTriple`);
* **P1** `IsFrameFunction.add/smul/const/neg/sub` — frame functions form a vector space with
  additive weights;
* **P2** `IsFrameFunction.neg_apply` — `f (−s) = f s`;
* **P3** `IsFrameFunction.four_point` — if `s ⟂ t` and `s' ⟂ t'` lie on one great circle (all
  four orthogonal to a unit `w`) then `f s + f t = f s' + f t'`;
* **P4** `IsFrameFunction.exists_orthogonal_lt` — if `f s > M − ξ` (with `M` an upper bound and
  `m` an approximate lower bound) there is `t ⟂ s` with `f t < m + ξ`; and the `sphereSup` /
  `sphereInf` form `exists_orthogonal_lt_sphereInf_add`;
* boundedness: a nonnegative frame function takes values in `[0, W]`
  (`IsFrameFunction.le_weight_of_nonneg`, `weight_nonneg`);
* the examples: constants, `s ↦ ⟪p₀, s⟫²` (weight `1`, Parseval), and every quadratic form
  `s ↦ s ⬝ᵥ A s` (weight `Tr A`, `isFrameFunction_quadForm`) — the *regular* frame functions,
  which Gleason's core lemma says are all of them.

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §2 (P1–P4 and
the examples); Gleason 1957, §1.
-/

@[expose] public section

open Matrix
open scoped Matrix InnerProductSpace

namespace Gleason

/-! ### `ℝ³`: inner products, the cross product, orthonormal triples -/

/-- The real inner product of `EuclideanSpace ℝ (Fin 3)` is the dot product. -/
lemma real_inner_eq_dotProduct (x y : EuclideanSpace ℝ (Fin 3)) : ⟪x, y⟫_ℝ = ⇑x ⬝ᵥ ⇑y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The cross product of two vectors of `ℝ³`. -/
def cross (x y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (⇑x ⨯₃ ⇑y)

@[simp] lemma coe_cross (x y : EuclideanSpace ℝ (Fin 3)) : ⇑(cross x y) = ⇑x ⨯₃ ⇑y := rfl

lemma inner_cross_left (x y : EuclideanSpace ℝ (Fin 3)) : ⟪x, cross x y⟫_ℝ = 0 := by
  rw [real_inner_eq_dotProduct, coe_cross, dot_self_cross]

lemma inner_cross_right (x y : EuclideanSpace ℝ (Fin 3)) : ⟪y, cross x y⟫_ℝ = 0 := by
  rw [real_inner_eq_dotProduct, coe_cross, dot_cross_self]

/-- Lagrange's identity `⟪u × v, w × x⟫ = ⟪u, w⟫⟪v, x⟫ − ⟪u, x⟫⟪v, w⟫`. -/
lemma inner_cross_cross (u v w x : EuclideanSpace ℝ (Fin 3)) :
    ⟪cross u v, cross w x⟫_ℝ = ⟪u, w⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, x⟫_ℝ * ⟪v, w⟫_ℝ := by
  simp only [real_inner_eq_dotProduct, coe_cross, cross_dot_cross]

/-- The cross product of an orthonormal pair is a unit vector. -/
lemma norm_cross_of_orthonormal {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) : ‖cross x y‖ = 1 := by
  have h : ⟪cross x y, cross x y⟫_ℝ = 1 := by
    rw [inner_cross_cross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy, hxy,
      real_inner_comm, hxy]
    norm_num
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (cross x y)]

/-- An orthonormal triple of `ℝ³`, unpacked. -/
lemma orthonormal_triple_iff {x y z : EuclideanSpace ℝ (Fin 3)} :
    Orthonormal ℝ ![x, y, z] ↔ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ‖z‖ = 1 ∧
      ⟪x, y⟫_ℝ = 0 ∧ ⟪x, z⟫_ℝ = 0 ∧ ⟪y, z⟫_ℝ = 0 := by
  have hn : ∀ v : EuclideanSpace ℝ (Fin 3), ⟪v, v⟫_ℝ = 1 ↔ ‖v‖ = 1 := by
    intro v
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h; nlinarith [norm_nonneg v]
    · intro h; rw [h]; norm_num
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    refine ⟨(hn x).mp (by simpa using h 0 0), (hn y).mp (by simpa using h 1 1),
      (hn z).mp (by simpa using h 2 2), by simpa using h 0 1, by simpa using h 0 2,
      by simpa using h 1 2⟩
  · rintro ⟨hx, hy, hz, hxy, hxz, hyz⟩ i j
    have hyx : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy]
    have hzx : ⟪z, x⟫_ℝ = 0 := by rw [real_inner_comm, hxz]
    have hzy : ⟪z, y⟫_ℝ = 0 := by rw [real_inner_comm, hyz]
    fin_cases i <;> fin_cases j <;> simp [hx, hy, hz, hxy, hxz, hyz, hyx, hzx, hzy]

/-- An orthonormal pair extends to a frame by its cross product. -/
lemma orthonormal_cross {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) : Orthonormal ℝ ![x, y, cross x y] :=
  orthonormal_triple_iff.mpr ⟨hx, hy, norm_cross_of_orthonormal hx hy hxy, hxy,
    inner_cross_left x y, inner_cross_right x y⟩

/-- In `ℝ³` there is a unit vector orthogonal to any two given vectors. -/
lemma exists_unit_orthogonal_pair (s t : EuclideanSpace ℝ (Fin 3)) :
    ∃ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 ∧ ⟪s, w⟫_ℝ = 0 ∧ ⟪t, w⟫_ℝ = 0 := by
  classical
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ (({s, t} : Finset (EuclideanSpace ℝ (Fin 3))) : Set _) with hK
  have hKle : Module.finrank ℝ K ≤ 2 :=
    (finrank_span_finset_le_card ({s, t} : Finset _)).trans Finset.card_le_two
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    have := Submodule.finrank_add_finrank_orthogonal K
    rw [h, finrank_bot, finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨w₀, hw₀K, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  refine ⟨(‖w₀‖⁻¹ : ℝ) • w₀, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
      (by simp)) hw₀K, mul_zero]
  · rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
      (by simp)) hw₀K, mul_zero]

/-- A unit vector of `ℝ³` has a unit orthogonal vector. -/
lemma exists_unit_orthogonal (s : EuclideanSpace ℝ (Fin 3)) :
    ∃ t : EuclideanSpace ℝ (Fin 3), ‖t‖ = 1 ∧ ⟪s, t⟫_ℝ = 0 := by
  obtain ⟨w, hw, hsw, -⟩ := exists_unit_orthogonal_pair s s
  exact ⟨w, hw, hsw⟩

/-- An orthonormal triple of `ℝ³` is an orthonormal basis. -/
noncomputable def orthonormalBasisOfTriple {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  OrthonormalBasis.mk hv (by
    have h := (basisOfOrthonormalOfCardEqFinrank hv (by simp)).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at h
    exact h.ge)

@[simp] lemma coe_orthonormalBasisOfTriple {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : ⇑(orthonormalBasisOfTriple hv) = v :=
  OrthonormalBasis.coe_mk hv _

/-! ### Frame functions: P1 (a vector space), the frame identity for triples -/

namespace IsFrameFunction

section Linear

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {f g : EuclideanSpace 𝕜 (Fin n) → ℝ} {W W' : ℝ}

/-- **P1.** Constants are frame functions, with weight `n · c`. -/
theorem const (c : ℝ) : IsFrameFunction 𝕜 (fun _ : EuclideanSpace 𝕜 (Fin n) => c) (n * c) :=
  fun _ => by simp

theorem add (hf : IsFrameFunction 𝕜 f W) (hg : IsFrameFunction 𝕜 g W') :
    IsFrameFunction 𝕜 (fun s => f s + g s) (W + W') :=
  fun b => by rw [Finset.sum_add_distrib, hf b, hg b]

theorem smul (hf : IsFrameFunction 𝕜 f W) (c : ℝ) :
    IsFrameFunction 𝕜 (fun s => c * f s) (c * W) :=
  fun b => by rw [← Finset.mul_sum, hf b]

theorem neg (hf : IsFrameFunction 𝕜 f W) : IsFrameFunction 𝕜 (fun s => -f s) (-W) :=
  fun b => by rw [Finset.sum_neg_distrib, hf b]

theorem sub (hf : IsFrameFunction 𝕜 f W) (hg : IsFrameFunction 𝕜 g W') :
    IsFrameFunction 𝕜 (fun s => f s - g s) (W - W') :=
  fun b => by rw [Finset.sum_sub_distrib, hf b, hg b]

end Linear

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W : ℝ}

/-- **The frame identity for any orthonormal triple** (not only for `OrthonormalBasis`
values). -/
theorem sum_triple (hf : IsFrameFunction ℝ f W) {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Orthonormal ℝ v) : ∑ i, f (v i) = W := by
  have h := hf (orthonormalBasisOfTriple hv)
  simpa only [coe_orthonormalBasisOfTriple] using h

/-- The frame identity, unfolded: `f p + f q + f r = W`. -/
theorem eq_of_triple (hf : IsFrameFunction ℝ f W) {p q r : EuclideanSpace ℝ (Fin 3)}
    (h : Orthonormal ℝ ![p, q, r]) : f p + f q + f r = W := by
  have := hf.sum_triple h
  simpa [Fin.sum_univ_three] using this

/-! ### P2, P3, P4 -/

/-- **P2.** `f (−s) = f s` on the sphere. -/
theorem neg_apply (hf : IsFrameFunction ℝ f W) {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) :
    f (-s) = f s := by
  obtain ⟨t, ht, hst⟩ := exists_unit_orthogonal s
  have h1 := hf.eq_of_triple (orthonormal_cross hs ht hst)
  have h2 := hf.eq_of_triple (p := -s) (q := t) (r := cross s t)
    (orthonormal_triple_iff.mpr ⟨by rw [norm_neg, hs], ht, norm_cross_of_orthonormal hs ht hst,
      by rw [inner_neg_left, hst, neg_zero], by rw [inner_neg_left, inner_cross_left, neg_zero],
      inner_cross_right s t⟩)
  linarith

/-- **P3, the four-point identity.** If `s ⟂ t` and `s' ⟂ t'` are two orthonormal pairs on one
great circle — all four orthogonal to a unit vector `w` — then `f s + f t = f s' + f t'`. -/
theorem four_point (hf : IsFrameFunction ℝ f W) {w s t s' t' : EuclideanSpace ℝ (Fin 3)}
    (hw : ‖w‖ = 1) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hs' : ‖s'‖ = 1) (ht' : ‖t'‖ = 1)
    (hsw : ⟪s, w⟫_ℝ = 0) (htw : ⟪t, w⟫_ℝ = 0) (hs'w : ⟪s', w⟫_ℝ = 0) (ht'w : ⟪t', w⟫_ℝ = 0)
    (hst : ⟪s, t⟫_ℝ = 0) (hs't' : ⟪s', t'⟫_ℝ = 0) : f s + f t = f s' + f t' := by
  have h1 := hf.eq_of_triple (orthonormal_triple_iff.mpr ⟨hs, ht, hw, hst, hsw, htw⟩)
  have h2 := hf.eq_of_triple (orthonormal_triple_iff.mpr ⟨hs', ht', hw, hs't', hs'w, ht'w⟩)
  linarith

/-- **P4.** Let `M` bound `f` above on the sphere and let `m` be approached from above by
values of `f` (for instance `M = sup f`, `m = inf f`). If `f s > M − ξ`, then some unit `t ⟂ s`
has `f t < m + ξ`. -/
theorem exists_orthogonal_lt (hf : IsFrameFunction ℝ f W) {M m : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    (hm : ∀ δ : ℝ, 0 < δ → ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ f u < m + δ)
    {ξ : ℝ} {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) (hfs : M - ξ < f s) :
    ∃ t : EuclideanSpace ℝ (Fin 3), ‖t‖ = 1 ∧ ⟪s, t⟫_ℝ = 0 ∧ f t < m + ξ := by
  -- `δ` leaves room on both sides
  set δ : ℝ := (f s - (M - ξ)) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hsδ : M - ξ + δ < f s := by rw [hδ]; linarith
  obtain ⟨t', ht', hft'⟩ := hm δ hδpos
  -- a great circle through `s` and `t'`: its unit normal `w`
  obtain ⟨w, hw, hsw, ht'w⟩ := exists_unit_orthogonal_pair s t'
  -- `t ⟂ s` and `s' ⟂ t'` on that great circle
  refine ⟨cross s w, norm_cross_of_orthonormal hs hw hsw, inner_cross_left s w, ?_⟩
  have hcw : ⟪cross s w, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_cross_right s w
  have hs'w : ⟪cross t' w, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_cross_right t' w
  have h4 := hf.four_point hw hs (norm_cross_of_orthonormal hs hw hsw)
    (norm_cross_of_orthonormal ht' hw ht'w) ht' hsw hcw hs'w ht'w (inner_cross_left s w)
    (by rw [real_inner_comm]; exact inner_cross_left t' w)
  have hs'M := hM (cross t' w) (norm_cross_of_orthonormal ht' hw ht'w)
  linarith

/-! ### Boundedness -/

/-- A nonnegative frame function is at most its weight on the sphere. -/
theorem le_weight_of_nonneg (hf : IsFrameFunction ℝ f W)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : f s ≤ W := by
  obtain ⟨t, ht, hst⟩ := exists_unit_orthogonal s
  have h := hf.eq_of_triple (orthonormal_cross hs ht hst)
  have := h0 t ht
  have := h0 _ (norm_cross_of_orthonormal hs ht hst)
  linarith

/-- The weight of a nonnegative frame function is nonnegative. -/
theorem weight_nonneg (hf : IsFrameFunction ℝ f W)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u) : 0 ≤ W := by
  have hs : ‖(EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    rw [PiLp.norm_single]; exact norm_one
  exact (h0 _ hs).trans (hf.le_weight_of_nonneg h0 hs)

end IsFrameFunction

/-! ### Supremum and infimum over the sphere -/

/-- The supremum of `f` over the unit sphere. -/
noncomputable def sphereSup (f : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  sSup (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The infimum of `f` over the unit sphere. -/
noncomputable def sphereInf (f : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  sInf (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

section SupInf

variable {f : EuclideanSpace ℝ (Fin 3) → ℝ}

lemma sphere_nonempty : (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
  ⟨f (EuclideanSpace.single 0 1), EuclideanSpace.single 0 (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]; exact norm_one, rfl⟩

lemma bddAbove_sphere {M : ℝ} (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) :
    BddAbove (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hM u (mem_sphere_zero_iff_norm.mp hu)

lemma bddBelow_sphere {m : ℝ} (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    BddBelow (f '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  refine ⟨m, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hm u (mem_sphere_zero_iff_norm.mp hu)

lemma le_sphereSup {M : ℝ} (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : f s ≤ sphereSup f :=
  le_csSup (bddAbove_sphere hM) ⟨s, mem_sphere_zero_iff_norm.mpr hs, rfl⟩

lemma sphereSup_le {M : ℝ} (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) :
    sphereSup f ≤ M := by
  refine csSup_le sphere_nonempty ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hM u (mem_sphere_zero_iff_norm.mp hu)

lemma sphereInf_le {m : ℝ} (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) : sphereInf f ≤ f s :=
  csInf_le (bddBelow_sphere hm) ⟨s, mem_sphere_zero_iff_norm.mpr hs, rfl⟩

lemma le_sphereInf {m : ℝ} (hm : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u) :
    m ≤ sphereInf f := by
  refine le_csInf sphere_nonempty ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hm u (mem_sphere_zero_iff_norm.mp hu)

/-- Values of `f` come within any `δ > 0` of `sphereSup f`. -/
lemma exists_sphereSup_sub_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ sphereSup f - δ < f u := by
  obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := exists_lt_of_lt_csSup (sphere_nonempty (f := f))
    (show sphereSup f - δ < sphereSup f by linarith)
  exact ⟨u, mem_sphere_zero_iff_norm.mp hu, h⟩

/-- Values of `f` come within any `δ > 0` of `sphereInf f`. -/
lemma exists_lt_sphereInf_add {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ f u < sphereInf f + δ := by
  obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := exists_lt_of_csInf_lt (sphere_nonempty (f := f))
    (show sphereInf f < sphereInf f + δ by linarith)
  exact ⟨u, mem_sphere_zero_iff_norm.mp hu, h⟩

/-- **P4 in `sup`/`inf` form.** For a bounded frame function, `f s > sup f − ξ` gives a unit
`t ⟂ s` with `f t < inf f + ξ`. -/
theorem IsFrameFunction.exists_orthogonal_lt_sphereInf_add {W M : ℝ}
    (hf : IsFrameFunction ℝ f W) (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M)
    {ξ : ℝ} {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1) (hfs : sphereSup f - ξ < f s) :
    ∃ t : EuclideanSpace ℝ (Fin 3), ‖t‖ = 1 ∧ ⟪s, t⟫_ℝ = 0 ∧ f t < sphereInf f + ξ :=
  hf.exists_orthogonal_lt (fun _ hu => le_sphereSup hM hu)
    (fun _ hδ => exists_lt_sphereInf_add hδ) hs hfs

end SupInf

/-! ### The regular frame functions -/

/-- `s ↦ ⟪p₀, s⟫²` is a frame function of weight `1` (Parseval). -/
theorem isFrameFunction_inner_sq {p₀ : EuclideanSpace ℝ (Fin 3)} (hp₀ : ‖p₀‖ = 1) :
    IsFrameFunction ℝ (fun s => ⟪p₀, s⟫_ℝ ^ 2) 1 := by
  intro b
  have h := b.sum_inner_mul_inner p₀ p₀
  rw [real_inner_self_eq_norm_sq, hp₀] at h
  simp only [one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ⟪p₀, b i⟫_ℝ ^ 2 = ⟪p₀, b i⟫_ℝ * ⟪b i, p₀⟫_ℝ
  rw [real_inner_comm p₀ (b i), sq]

/-- `s ⬝ᵥ A s = Tr(A · s sᵀ)`. -/
lemma dotProduct_mulVec_eq_trace (A : Matrix (Fin 3) (Fin 3) ℝ) (s : Fin 3 → ℝ) :
    s ⬝ᵥ (A *ᵥ s) = (A * vecMulVec s s).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Every quadratic form is a frame function**, with weight the trace of its matrix
(CKM §2, Proposition). -/
theorem isFrameFunction_quadForm (A : Matrix (Fin 3) (Fin 3) ℝ) :
    IsFrameFunction ℝ (fun s : EuclideanSpace ℝ (Fin 3) => ⇑s ⬝ᵥ (A *ᵥ ⇑s)) A.trace := by
  intro b
  simp only [dotProduct_mulVec_eq_trace]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum]
  have h : ∑ i, vecMulVec (⇑(b i)) (⇑(b i)) = 1 := by
    have := sum_vecMulVec_eq_colMatrix_mul (𝕜 := ℝ) b
    simp only [star_trivial] at this
    rw [this, colMatrix_mul_conjTranspose_of_orthonormalBasis]
  rw [h, Matrix.mul_one]

end Gleason

end
