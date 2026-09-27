/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Real

/-!
# Gleason's theorem for real frame functions

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #87, the last generality gap of the
Gleason development: #58 proved the real theorem for a projection *package*, and this file proves it
for a bare **frame function**, which is the object Gleason's paper is about.

★★★ `existsUnique_density_of_frameFunction`: for `N ≥ 3`, a nonnegative frame function of weight `W`
on `ℝᴺ` — a map on the unit sphere with `∑ᵢ f(bᵢ) = W` over **every** orthonormal basis — is the
quadratic form of a unique positive semidefinite matrix of trace `W`.

## What the package gave for free, and what a frame function has to earn

The core lemma of #57 is about `ℝ³`, so every route to `ℝᴺ` needs the restriction of `f` to the span
of an orthonormal triple to be a frame function *there* — that is, the weight of a `3`-space must not
depend on which orthonormal basis of it is used. A projection package reads that weight off
`p (∑ᵢ |eᵢ⟩⟨eᵢ|)`, which is manifestly basis independent (#58's `isFrameFunction_restrictR`). A bare
frame function has no `p`, so the fact has to be earned by completing the triple:

* `orthonormalBasisOfCardR` — an orthonormal family indexed by a type of cardinality `N` **is** an
  orthonormal basis (`basisOfOrthonormalOfCardEqFinrank`), so no span argument is needed;
* `orthonormal_sum_elim` — two orthonormal families that are mutually orthogonal glue along `⊕`;
* ★ `IsFrameFunction.sum_eq_of_basis` — the frame sum is the weight over an orthonormal basis indexed
  by *any* finite type (reindex to `Fin N`), and ★ `IsFrameFunction.sum_elim_eq` splits it along a
  completion;
* `exists_orthonormal_complement` — the orthogonal complement carries an orthonormal family of the
  complementary size (`stdOrthonormalBasis` of `Sᴿ`, `finrank_add_finrank_orthogonal`);
* hence ★★ `IsFrameFunction.exists_weight_restrict`: **the weight of a `3`-space is basis
  independent**, because a *fixed* complement family completes every triple of that space and the
  frame sums add to `W`.

Two more consequences of the same completion, both needed by the middle layer of `Gleason/Real.lean`
and neither available for a bare `f` before now: ★ `IsFrameFunction.le_weight` (`f ≤ W` on the sphere
in **any** dimension — `Gleason/Sphere.lean` proves it for `ℝ³` through the cross product) and
★ `IsFrameFunction.neg_eq` (`f` is **even** on the sphere: flipping one vector of a basis gives
another basis with the same tail).

With those three, `exists_isSymm_sphere_of_quad` — the layer #58 was refactored to state for any
function quadratic on triples — gives ★★ `exists_isSymm_sphere_of_frameFunction_one` at weight `1`,
and the theorem follows after normalising by `W` and running the descent
(`quadraticForm_on_sphere_to_densityR`).

## Honest scope

⚠️ `N ≥ 3` and finite dimensions, as in #57 and #58. `N = 2` is false for Gleason's theorem, and
`N ≤ 1` is only the trivial statement.
⚠️ The weight-`W` statement is reduced to the weight-`1` one by dividing, which needs `W > 0`; the
`W = 0` case is handled separately (`f` vanishes on the sphere, the matrix is `0`).
⚠️ Nothing in the corpus consumes this file: `LF2` and the CSD layers use the *complex* theorem, and
#58's package form is what a real application would use. It exists because it is the statement
Gleason wrote, and because an upstream PR would be asked for it.

## Source

A. Gleason, *Measures on the closed subspaces of a Hilbert space*, J. Math. Mech. **6** (1957) 885,
§1 (frame functions; the real theorem); `Gleason/Core.lean` (#57, the core lemma),
`Gleason/Real.lean` (#58, the real reduction and the descent); `specs/gleason-feasibility.md` §2;
`specs/BACKLOG.md` #87; `specs/future-work.md`.
-/

@[expose] public section

open Matrix Module
open scoped InnerProductSpace

namespace Gleason

variable {N : ℕ}

/-! ### An orthonormal family of the right size is an orthonormal basis -/

/-- An orthonormal family indexed by a type of the right cardinality **is** an orthonormal basis. -/
noncomputable def orthonormalBasisOfCardR {ι : Type*} [Fintype ι] [Nonempty ι]
    {v : ι → EuclideanSpace ℝ (Fin N)} (hv : Orthonormal ℝ v) (hcard : Fintype.card ι = N) :
    OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin N)) :=
  (basisOfOrthonormalOfCardEqFinrank hv
      (by rw [hcard, finrank_euclideanSpace_fin])).toOrthonormalBasis (by
    rw [coe_basisOfOrthonormalOfCardEqFinrank]
    exact hv)

@[simp] lemma coe_orthonormalBasisOfCardR {ι : Type*} [Fintype ι] [Nonempty ι]
    {v : ι → EuclideanSpace ℝ (Fin N)} (hv : Orthonormal ℝ v) (hcard : Fintype.card ι = N) :
    ⇑(orthonormalBasisOfCardR hv hcard) = v := by
  rw [orthonormalBasisOfCardR, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank]

/-- Two families glued along a sum type are orthonormal when each is and they are orthogonal. -/
theorem orthonormal_sum_elim {k m : ℕ} {v : Fin k → EuclideanSpace ℝ (Fin N)}
    {g : Fin m → EuclideanSpace ℝ (Fin N)} (hv : Orthonormal ℝ v) (hg : Orthonormal ℝ g)
    (hvg : ∀ j i, ⟪v j, g i⟫_ℝ = 0) : Orthonormal ℝ (Sum.elim v g) := by
  rw [orthonormal_iff_ite] at hv hg ⊢
  intro a b
  cases a with
  | inl j =>
      cases b with
      | inl j' =>
          rw [Sum.elim_inl, Sum.elim_inl, hv j j']
          by_cases h : j = j'
          · rw [if_pos h, if_pos (by rw [h])]
          · rw [if_neg h, if_neg (by simpa using h)]
      | inr i =>
          rw [Sum.elim_inl, Sum.elim_inr, hvg j i, if_neg (by simp)]
  | inr i =>
      cases b with
      | inl j =>
          rw [Sum.elim_inr, Sum.elim_inl, real_inner_comm, hvg j i, if_neg (by simp)]
      | inr i' =>
          rw [Sum.elim_inr, Sum.elim_inr, hg i i']
          by_cases h : i = i'
          · rw [if_pos h, if_pos (by rw [h])]
          · rw [if_neg h, if_neg (by simpa using h)]

/-! ### The frame sum over any orthonormal basis -/

/-- **The frame sum is the weight over every orthonormal basis**, whatever it is indexed by: reindex
along an equivalence to `Fin N`. -/
theorem IsFrameFunction.sum_eq_of_basis {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}
    (hf : IsFrameFunction ℝ f W) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin N))) : ∑ i, f (b i) = W := by
  have hcard : Fintype.card ι = N := by
    have h := Module.finrank_eq_card_basis b.toBasis
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  obtain ⟨g⟩ : Nonempty (ι ≃ Fin N) := ⟨Fintype.equivFinOfCardEq hcard⟩
  have h := hf (b.reindex g)
  rw [← h]
  refine Fintype.sum_equiv g (fun i => f (b i)) (fun i => f ((b.reindex g) i)) ?_
  intro i
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]

/-- **The frame sum splits along a completion**: an orthonormal family and an orthogonal family of
the complementary size form an orthonormal basis, so the two frame sums add to the weight. -/
theorem IsFrameFunction.sum_elim_eq {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}
    (hf : IsFrameFunction ℝ f W) {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    {v : Fin k → EuclideanSpace ℝ (Fin N)} {g : Fin m → EuclideanSpace ℝ (Fin N)}
    (h : Orthonormal ℝ (Sum.elim v g)) (hcard : k + m = N) :
    (∑ j, f (v j)) + ∑ i, f (g i) = W := by
  have hc : Fintype.card (Fin k ⊕ Fin m) = N := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hcard]
  have hsum := hf.sum_eq_of_basis (orthonormalBasisOfCardR h hc)
  rw [show (fun x : Fin k ⊕ Fin m => f ((orthonormalBasisOfCardR h hc) x))
      = fun x => f (Sum.elim v g x) from by rw [coe_orthonormalBasisOfCardR]] at hsum
  rw [Fintype.sum_sum_type] at hsum
  exact hsum

/-! ### Completing an orthonormal family -/

/-- **The orthogonal complement carries an orthonormal family of the complementary size.** -/
theorem exists_orthonormal_complement (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ (m : ℕ) (g : Fin m → EuclideanSpace ℝ (Fin N)), Orthonormal ℝ g ∧
      (∀ i, g i ∈ Sᗮ) ∧ finrank ℝ S + m = N := by
  obtain ⟨t, ht⟩ : ∃ t, t = stdOrthonormalBasis ℝ Sᗮ := ⟨_, rfl⟩
  refine ⟨finrank ℝ Sᗮ, fun i => ((t i : Sᗮ) : EuclideanSpace ℝ (Fin N)), ?_,
    fun i => (t i).2, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    have h := orthonormal_iff_ite.mp t.orthonormal i j
    rw [← h]
    rfl
  · rw [S.finrank_add_finrank_orthogonal, finrank_euclideanSpace_fin]

/-! ### What a bare frame function inherits from the completion -/

variable {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}

/-- A unit vector, completed: the frame sum splits as `f v` plus a tail orthogonal to `v`. -/
theorem IsFrameFunction.exists_tail (hf : IsFrameFunction ℝ f W) {v : EuclideanSpace ℝ (Fin N)}
    (hv : ‖v‖ = 1) :
    ∃ (m : ℕ) (g : Fin m → EuclideanSpace ℝ (Fin N)), Orthonormal ℝ g ∧
      (∀ i, ⟪v, g i⟫_ℝ = 0) ∧ 1 + m = N ∧ f v + ∑ i, f (g i) = W := by
  obtain ⟨m, g, hg, hgmem, hcard⟩ := exists_orthonormal_complement (Submodule.span ℝ {v})
  have hvmem : v ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin N))) :=
    Submodule.mem_span_singleton_self v
  have hvg : ∀ i, ⟪v, g i⟫_ℝ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal hvmem (hgmem i)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact one_ne_zero hv.symm
  have hrank : finrank ℝ (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin N)))) = 1 :=
    finrank_span_singleton hv0
  have hcard' : 1 + m = N := by rw [← hcard, hrank]
  have hv1 : Orthonormal ℝ (fun _ : Fin 1 => v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_self_eq_norm_sq, hv, if_pos (Subsingleton.elim i j)]
    norm_num
  have hone : Orthonormal ℝ (Sum.elim (fun _ : Fin 1 => v) g) :=
    orthonormal_sum_elim hv1 hg fun _ i => hvg i
  have hsum := hf.sum_elim_eq hone hcard'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul] at hsum
  exact ⟨m, g, hg, hvg, hcard', hsum⟩

/-- **A nonnegative frame function is bounded by its weight**, in any dimension (the `Fin 3` proof
in `Gleason/Sphere.lean` goes through the cross product). -/
theorem IsFrameFunction.le_weight (hf : IsFrameFunction ℝ f W)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → 0 ≤ f u) {v : EuclideanSpace ℝ (Fin N)}
    (hv : ‖v‖ = 1) : f v ≤ W := by
  obtain ⟨m, g, hg, -, -, hsum⟩ := hf.exists_tail hv
  have hnn : 0 ≤ ∑ i, f (g i) :=
    Finset.sum_nonneg fun i _ => h0 (g i) (hg.norm_eq_one i)
  linarith

/-- **A frame function is even on the sphere**: flipping one vector of a basis gives another
basis, with the same tail. -/
theorem IsFrameFunction.neg_eq (hf : IsFrameFunction ℝ f W) {v : EuclideanSpace ℝ (Fin N)}
    (hv : ‖v‖ = 1) : f (-v) = f v := by
  obtain ⟨m, g, hg, hvg, hcard, hsum⟩ := hf.exists_tail hv
  have hvn : ‖(-v)‖ = 1 := by rw [norm_neg, hv]
  have hneg1 : Orthonormal ℝ (fun _ : Fin 1 => -v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_self_eq_norm_sq, hvn, if_pos (Subsingleton.elim i j)]
    norm_num
  have hone : Orthonormal ℝ (Sum.elim (fun _ : Fin 1 => -v) g) :=
    orthonormal_sum_elim hneg1 hg fun _ i => by
      rw [inner_neg_left, hvg i, neg_zero]
  have hsum' := hf.sum_elim_eq hone hcard
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul] at hsum'
  linarith

/-! ### The restriction to the span of an orthonormal triple -/

/-- ★★ **The step #58 got from the projection package and a bare frame function has to earn.** The
weight of a `3`-space is basis independent: complete an orthonormal triple of that space by a *fixed*
orthonormal family of the orthogonal complement, and the frame sum of the triple is the total weight
minus the tail's — the same for every triple of the space. So the restriction to the span is a frame
function on `ℝ³`, which is what Gleason's core lemma consumes. -/
theorem IsFrameFunction.exists_weight_restrict (hf : IsFrameFunction ℝ f W)
    {e : Fin 3 → EuclideanSpace ℝ (Fin N)} (he : Orthonormal ℝ e) :
    ∃ W' : ℝ, IsFrameFunction ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (combR e x)) W' := by
  obtain ⟨m, g, hg, hgmem, hcard⟩ :=
    exists_orthonormal_complement (Submodule.span ℝ (Set.range e))
  have hrank : finrank ℝ (Submodule.span ℝ (Set.range e)) = 3 := by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  have hc3 : 3 + m = N := by rw [← hcard, hrank]
  refine ⟨W - ∑ i, f (g i), fun c => ?_⟩
  have hv : Orthonormal ℝ (fun j => combR e (c j)) := orthonormal_combR he c.orthonormal
  have hmem : ∀ j, combR e (c j) ∈ Submodule.span ℝ (Set.range e) := by
    intro j
    rw [combR]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hone : Orthonormal ℝ (Sum.elim (fun j => combR e (c j)) g) :=
    orthonormal_sum_elim hv hg fun j i =>
      Submodule.inner_right_of_mem_orthogonal (hmem j) (hgmem i)
  have hsum := hf.sum_elim_eq hone hc3
  show (∑ j, f (combR e (c j))) = W - ∑ i, f (g i)
  linarith

/-! ### Gleason's theorem for real frame functions -/

/-- ★★ A nonnegative frame function of weight `1` is a symmetric quadratic form on the sphere. -/
theorem exists_isSymm_sphere_of_frameFunction_one (hf : IsFrameFunction ℝ f 1) (hN : 3 ≤ N)
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ, A.IsSymm ∧
      ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) :=
  exists_isSymm_sphere_of_quad
    (fun e he => by
      obtain ⟨W', hW'⟩ := hf.exists_weight_restrict he
      exact coreLemma _ W' hW' fun x hx => h0 _ (norm_combR he hx))
    (fun _ hu => hf.neg_eq hu) h0 (fun _ hv => hf.le_weight h0 hv) hN

/-- The weight of a nonnegative frame function is nonnegative. -/
theorem IsFrameFunction.zero_le_weight (hf : IsFrameFunction ℝ f W)
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v) : 0 ≤ W := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := hf (EuclideanSpace.basisFun (Fin 0) ℝ)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact h.le
  have h := hf (EuclideanSpace.basisFun (Fin N) ℝ)
  rw [← h]
  refine Finset.sum_nonneg fun i _ => h0 _ ?_
  rw [EuclideanSpace.basisFun_apply, PiLp.norm_single]
  exact norm_one

/-- ★★★ **Gleason's theorem for real frame functions, `N ≥ 3`** — the statement Gleason wrote. A
nonnegative frame function of weight `W` on `ℝᴺ` is the quadratic form of a unique positive
semidefinite matrix of trace `W`. #58 proved this for a projection package, whose `p` on the
projections makes the weight of a `3`-space manifestly basis independent; here that step is earned by
completing the triple (`exists_weight_restrict`). -/
theorem existsUnique_density_of_frameFunction (hf : IsFrameFunction ℝ f W) (hN : 3 ≤ N)
    (h0 : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v) :
    ∃! A : Matrix (Fin N) (Fin N) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) := by
  have hW0 : 0 ≤ W := hf.zero_le_weight h0
  rcases eq_or_lt_of_le hW0 with hW | hWpos
  · -- weight zero: the function vanishes on the sphere
    have hzero : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → f v = 0 := fun v hv =>
      le_antisymm (by rw [hW]; exact hf.le_weight h0 hv) (h0 v hv)
    refine ⟨0, ⟨Matrix.PosSemidef.zero, by rw [Matrix.trace_zero, hW], fun v hv => ?_⟩, ?_⟩
    · rw [hzero v hv, Matrix.zero_mulVec, dotProduct_zero]
    · rintro B ⟨hB, -, hBf⟩
      refine eq_of_sphere_quadForm_eqR (isSymm_of_isHermitianR hB.isHermitian)
        (isSymm_of_isHermitianR Matrix.PosSemidef.zero.isHermitian) fun v hv => ?_
      rw [← hBf v hv, hzero v hv, Matrix.zero_mulVec, dotProduct_zero]
  · -- positive weight: normalise
    have hf' : IsFrameFunction ℝ (fun v => f v / W) 1 := by
      intro b
      show (∑ i, f (b i) / W) = 1
      rw [← Finset.sum_div, hf b, div_self hWpos.ne']
    have h0' : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 ≤ f v / W := fun v hv =>
      div_nonneg (h0 v hv) hW0
    obtain ⟨A', hA'symm, hA'f⟩ := exists_isSymm_sphere_of_frameFunction_one hf' hN h0'
    have hsum1 : ∑ i, (fun v => f v / W) (EuclideanSpace.single i (1 : ℝ)) = 1 := by
      have h := hf' (EuclideanSpace.basisFun (Fin N) ℝ)
      simpa [EuclideanSpace.basisFun_apply] using h
    obtain ⟨hpsd, htr, huniq⟩ := quadraticForm_on_sphere_to_densityR hA'symm hA'f h0' hsum1
    have hWA : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 →
        f v = (⇑v : Fin N → ℝ) ⬝ᵥ ((W • A') *ᵥ ⇑v) := by
      intro v hv
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← hA'f v hv]
      field_simp
    have hHerm : (W • A').IsHermitian := by
      ext i j
      rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_trivial,
        smul_eq_mul, smul_eq_mul, hA'symm.apply i j]
    have hPSD : (W • A').PosSemidef :=
      posSemidef_of_sphere_nonnegR hHerm fun v hv => by
        rw [← hWA v hv]
        exact h0 v hv
    refine ⟨W • A', ⟨hPSD, ?_, hWA⟩, ?_⟩
    · rw [Matrix.trace_smul, htr, smul_eq_mul, mul_one]
    · rintro B ⟨hB, -, hBf⟩
      refine eq_of_sphere_quadForm_eqR (isSymm_of_isHermitianR hB.isHermitian) ?_ fun v hv => ?_
      · rw [Matrix.IsSymm, Matrix.transpose_smul, hA'symm]
      · rw [← hBf v hv, hWA v hv]

end Gleason
