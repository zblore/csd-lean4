/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Symplectic bases of alternating bilinear forms

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #50, the
linear-algebra half of the standard form of Darboux's theorem.

Every non-degenerate alternating bilinear form on a finite-dimensional vector space, over any
field, has a **symplectic basis** `p₁, …, pₙ, q₁, …, qₙ`: `B pᵢ pⱼ = 0`, `B qᵢ qⱼ = 0`,
`B pᵢ qⱼ = δᵢⱼ`. So the dimension is even, and in the coordinates of the basis the form is the
standard one, `B u v = ∑ᵢ (u_{pᵢ} v_{qᵢ} − u_{qᵢ} v_{pᵢ})`.

* `LinearMap.BilinForm.IsSymplecticBasis` — the predicate on a basis indexed by `ι ⊕ ι`
  (`inl` = the `p`'s, `inr` = the `q`'s); `IsSymplecticBasis.reindex`, `.inl_inr`, `.inr_inl`;
* ★★ `LinearMap.BilinForm.IsAlt.exists_isSymplecticBasis` — **existence**, by induction on the
  dimension (Gram–Schmidt for alternating forms): pick `p ≠ 0` and `q` with `B p q = 1`, split
  off the symplectic plane `span {p, q}` against its `B`-orthogonal complement
  (`isCompl_orthogonal_of_restrict_nondegenerate`), on which the form stays non-degenerate, and
  recurse; the basis is indexed by `Fin n ⊕ Fin n`;
* ★ `LinearMap.BilinForm.IsAlt.even_finrank` — **the dimension is even**;
* ★ `LinearMap.BilinForm.IsSymplecticBasis.apply_eq_sum` — **the standard form in symplectic
  coordinates**.

Mathlib at the pin has orthogonal bases for symmetric forms only (`LinearMap.BilinForm.iIsOrtho`)
and the symplectic *group* of matrices (`Matrix.J`), not the normal form of an alternating form.
The consumer is `Geometry/Manifold/DarbouxStandardForm.lean` (the `∑ dpᵢ ∧ dqᵢ` form of Darboux's
theorem); `specs/BACKLOG.md` #50; `specs/generator-layer-scoping.md` Q31.
-/

@[expose] public section

open Module Submodule
open LinearMap (BilinForm)

universe u v

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A basis `e` indexed by `ι ⊕ ι` is **symplectic** for `B` when the `inl`-vectors (the `p`'s)
are pairwise `B`-orthogonal, so are the `inr`-vectors (the `q`'s), and `B pᵢ qⱼ = δᵢⱼ`. -/
structure IsSymplecticBasis (B : BilinForm K V) {ι : Type*} (e : Basis (ι ⊕ ι) K V) :
    Prop where
  inl_inl : ∀ i j, B (e (Sum.inl i)) (e (Sum.inl j)) = 0
  inr_inr : ∀ i j, B (e (Sum.inr i)) (e (Sum.inr j)) = 0
  inl_inr_self : ∀ i, B (e (Sum.inl i)) (e (Sum.inr i)) = 1
  inl_inr_of_ne : ∀ i j, i ≠ j → B (e (Sum.inl i)) (e (Sum.inr j)) = 0

namespace IsSymplecticBasis

variable {B : BilinForm K V} {ι : Type*} {e : Basis (ι ⊕ ι) K V}

theorem inl_inr [DecidableEq ι] (h : B.IsSymplecticBasis e) (i j : ι) :
    B (e (Sum.inl i)) (e (Sum.inr j)) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    exact h.inl_inr_self i
  · exact h.inl_inr_of_ne i j hij

theorem inr_inl [DecidableEq ι] (hB : B.IsAlt) (h : B.IsSymplecticBasis e) (i j : ι) :
    B (e (Sum.inr i)) (e (Sum.inl j)) = if j = i then -1 else 0 := by
  rw [← hB.neg_eq (e (Sum.inl j)) (e (Sum.inr i)), h.inl_inr]
  split_ifs <;> simp

/-- A symplectic basis stays symplectic under a re-indexing applied to both halves. -/
theorem reindex (h : B.IsSymplecticBasis e) {ι' : Type*} (σ : ι ≃ ι') :
    B.IsSymplecticBasis (e.reindex (σ.sumCongr σ)) where
  inl_inl i j := by
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]
    exact h.inl_inl _ _
  inr_inr i j := by
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]
    exact h.inr_inr _ _
  inl_inr_self i := by
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr]
    exact h.inl_inr_self _
  inl_inr_of_ne i j hij := by
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr]
    exact h.inl_inr_of_ne _ _ (σ.symm.injective.ne hij)

/-- ★ **The standard form in symplectic coordinates**:
`B u v = ∑ᵢ (u_{pᵢ} v_{qᵢ} − u_{qᵢ} v_{pᵢ})`. -/
theorem apply_eq_sum [Fintype ι] [DecidableEq ι] (hB : B.IsAlt) (h : B.IsSymplecticBasis e)
    (u v : V) :
    B u v = ∑ i, (e.repr u (Sum.inl i) * e.repr v (Sum.inr i)
      - e.repr u (Sum.inr i) * e.repr v (Sum.inl i)) := by
  conv_lhs => rw [← e.sum_repr u, ← e.sum_repr v]
  simp only [sum_left, sum_right, smul_left, smul_right]
  simp only [Fintype.sum_sum_type, h.inl_inl, h.inr_inr, h.inl_inr, h.inr_inl hB, mul_zero,
    Finset.sum_const_zero, mul_ite, mul_one, mul_neg, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, zero_add, add_zero, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  simp only [mul_comm]
  ring

end IsSymplecticBasis

/-- The index re-shuffle joining a symplectic plane (indexed by `Fin 2`: `0` the `p`, `1` the
`q`) to a symplectic basis indexed by `ι ⊕ ι`, giving one indexed by `Option ι ⊕ Option ι` with
the plane at `none`. -/
def planeSumEquiv (ι : Type*) : Fin 2 ⊕ (ι ⊕ ι) ≃ Option ι ⊕ Option ι where
  toFun
    | Sum.inl i => ![Sum.inl none, Sum.inr none] i
    | Sum.inr (Sum.inl i) => Sum.inl (some i)
    | Sum.inr (Sum.inr i) => Sum.inr (some i)
  invFun
    | Sum.inl none => Sum.inl 0
    | Sum.inl (some i) => Sum.inr (Sum.inl i)
    | Sum.inr none => Sum.inl 1
    | Sum.inr (some i) => Sum.inr (Sum.inr i)
  left_inv := by
    rintro (i | i | i)
    · fin_cases i <;> rfl
    · rfl
    · rfl
  right_inv := by rintro ((_ | i) | (_ | i)) <;> rfl

section Existence

variable {K : Type u} [Field K]

/-- The induction behind `exists_isSymplecticBasis`, on the dimension, generalised over the
space: a non-degenerate alternating form on a space of dimension `n` has a symplectic basis
indexed by some finite `ι ⊕ ι`. -/
theorem IsAlt.exists_isSymplecticBasis_aux (n : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V),
      B.IsAlt → B.Nondegenerate → finrank K V = n →
      ∃ (ι : Type v) (_ : Fintype ι) (e : Basis (ι ⊕ ι) K V), B.IsSymplecticBasis e := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ B hB hnd hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- the trivial space
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact ⟨PEmpty, inferInstance, Basis.empty V,
      ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩⟩
  · have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hpos)
    obtain ⟨p, hp⟩ := exists_ne (0 : V)
    -- a partner `q` with `B p q = 1`
    obtain ⟨q', hq'⟩ : ∃ q', B p q' ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (hnd.1 p h)
    set q : V := (B p q')⁻¹ • q' with hq
    have hpq : B p q = 1 := by
      rw [hq, smul_right, inv_mul_cancel₀ hq']
    have hpp : B p p = 0 := hB.self_eq_zero p
    have hqq : B q q = 0 := hB.self_eq_zero q
    have hqp : B q p = -1 := by
      rw [← hB.neg_eq p q, hpq]
    have hrefl : B.IsRefl := hB.isRefl
    -- the symplectic plane `W = span {p, q}`
    have hli : LinearIndependent K ![p, q] := by
      rw [LinearIndependent.pair_iff' hp]
      intro a ha
      have h := congrArg (B p) ha
      rw [smul_right, hpp, mul_zero, hpq] at h
      exact zero_ne_one h
    set W : Submodule K V := span K (Set.range ![p, q]) with hW
    have hpW : p ∈ W := subset_span ⟨0, rfl⟩
    have hqW : q ∈ W := subset_span ⟨1, rfl⟩
    have hWrank : finrank K W = 2 := by
      rw [hW, finrank_span_eq_card hli, Fintype.card_fin]
    -- the form is non-degenerate on the plane
    have hWnd : (B.restrict W).Nondegenerate := by
      refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W)
        (hrefl.domRestrict W)).mpr ?_
      intro w hw
      obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun K).mp w.2
      have h0 : c 0 = 0 := by
        have h := hw ⟨q, hqW⟩
        rw [restrict_apply, ← hc] at h
        simpa [Fin.sum_univ_two, hpq, hqq] using h
      have h1 : c 1 = 0 := by
        have h := hw ⟨p, hpW⟩
        rw [restrict_apply, ← hc] at h
        simpa [Fin.sum_univ_two, hpp, hqp] using h
      ext
      rw [← hc]
      simp [Fin.sum_univ_two, h0, h1]
    have hc : IsCompl W (B.orthogonal W) :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl hWnd
    set W' : Submodule K V := B.orthogonal W with hW'
    have horth : ∀ (w : W') (x : V), x ∈ W → B x w = 0 := fun w x hx =>
      mem_orthogonal_iff.mp w.2 x hx
    have horth' : ∀ (w : W') (x : V), x ∈ W → B w x = 0 := fun w x hx =>
      hrefl.eq_zero (horth w x hx)
    -- the form is non-degenerate on the complement
    have hW'nd : (B.restrict W').Nondegenerate := by
      refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W')
        (hrefl.domRestrict W')).mpr ?_
      intro w hw
      ext
      rw [Submodule.coe_zero]
      refine hnd.1 (w : V) fun z => ?_
      have hz : z ∈ W ⊔ W' := by
        rw [hc.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      rw [map_add, horth' w y hy]
      have h2 : B (w : V) z' = 0 := by simpa using hw ⟨z', hz'⟩
      rw [h2, add_zero]
    have hW'alt : (B.restrict W').IsAlt := fun x => by
      rw [restrict_apply]
      exact hB.self_eq_zero _
    have hW'rank : finrank K W' = n - 2 := by
      rw [hW', finrank_orthogonal hnd W, hWrank, hn]
    obtain ⟨ι, _, f, hf⟩ :=
      ih (n - 2) (by omega) W' (B.restrict W') hW'alt hW'nd hW'rank
    -- assemble the basis of `V` from the plane and the complement
    let bW : Basis (Fin 2) K W := Basis.span hli
    have hbW : ∀ i, (bW i : V) = ![p, q] i := fun i =>
      congrArg Subtype.val (Basis.span_apply hli i)
    let e : Basis (Option ι ⊕ Option ι) K V :=
      ((bW.prod f).map (Submodule.prodEquivOfIsCompl W W' hc)).reindex (planeSumEquiv ι)
    have he_p : e (Sum.inl none) = p := by
      simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply, hbW]
    have he_q : e (Sum.inr none) = q := by
      simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply, hbW]
    have he_l : ∀ i, e (Sum.inl (some i)) = (f (Sum.inl i) : V) := by
      intro i
      simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply]
    have he_r : ∀ i, e (Sum.inr (some i)) = (f (Sum.inr i) : V) := by
      intro i
      simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply]
    refine ⟨Option ι, inferInstance, e, ⟨?_, ?_, ?_, ?_⟩⟩
    · rintro (_ | i) (_ | j)
      · rw [he_p]
        exact hpp
      · rw [he_p, he_l]
        exact horth _ _ hpW
      · rw [he_l, he_p]
        exact horth' _ _ hpW
      · rw [he_l, he_l]
        simpa using hf.inl_inl i j
    · rintro (_ | i) (_ | j)
      · rw [he_q]
        exact hqq
      · rw [he_q, he_r]
        exact horth _ _ hqW
      · rw [he_r, he_q]
        exact horth' _ _ hqW
      · rw [he_r, he_r]
        simpa using hf.inr_inr i j
    · rintro (_ | i)
      · rw [he_p, he_q]
        exact hpq
      · rw [he_l, he_r]
        simpa using hf.inl_inr_self i
    · rintro (_ | i) (_ | j) hij
      · exact absurd rfl hij
      · rw [he_p, he_r]
        exact horth _ _ hpW
      · rw [he_l, he_q]
        exact horth' _ _ hqW
      · rw [he_l, he_r]
        exact (by simpa using hf.inl_inr_of_ne i j fun h => hij (h ▸ rfl))

end Existence

variable [FiniteDimensional K V] {B : BilinForm K V}

/-- ★★ **Every non-degenerate alternating form has a symplectic basis** (Gram–Schmidt for
alternating forms): a basis `p₁, …, pₙ, q₁, …, qₙ` with `B pᵢ pⱼ = 0`, `B qᵢ qⱼ = 0`,
`B pᵢ qⱼ = δᵢⱼ`. -/
theorem IsAlt.exists_isSymplecticBasis (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ (n : ℕ) (e : Basis (Fin n ⊕ Fin n) K V), B.IsSymplecticBasis e := by
  obtain ⟨ι, _, e, he⟩ := IsAlt.exists_isSymplecticBasis_aux (finrank K V) V B hB hnd rfl
  exact ⟨Fintype.card ι, e.reindex ((Fintype.equivFin ι).sumCongr (Fintype.equivFin ι)),
    he.reindex _⟩

/-- ★ **A space carrying a non-degenerate alternating form has even dimension.** -/
theorem IsAlt.even_finrank (hB : B.IsAlt) (hnd : B.Nondegenerate) : Even (finrank K V) := by
  obtain ⟨n, e, -⟩ := hB.exists_isSymplecticBasis hnd
  exact ⟨n, by rw [Module.finrank_eq_card_basis e, Fintype.card_sum, Fintype.card_fin]⟩

end LinearMap.BilinForm

end
