/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracRadar

/-!
# The segment Hamiltonian of the parity-even sector

**Category:** 7-SigmaLayer (the record layer). BACKLOG #275 (residue of ~~#270~~).

~~#270~~ reflected a Dirac messenger by the method of images: parity (`x ↦ −x` with `σ_z`) commutes
with the lattice Dirac Hamiltonian, so its even sector evolves on its own, and that sector "is" the
chain on the segment from `A` (site `0`) to the antipode `B` (site `M` of a ring of `2M` sites),
with reflecting ends. Here that sentence is written out: an **isometry from the even sector onto
the segment** `{0, …, M} × Fin 2` (lower component zero at both ends), an **explicit segment
Hamiltonian** it intertwines with `H`, the **segment propagator** it intertwines with `e^{−itH}`,
and the records of `dirac_return` read on the segment.

## The even sum

* `sum_zmod_eq_sum_range`, ★★ `sum_zmod_even` — **a parity-even sum over `ZMod (2M)` is the two ends
  plus twice the interior of `{0, …, M}`**.

## The segment

* `segSite`, `segSite_val`, `IsSegEnd`, `segWt` (`1` at the ends, `√2` inside), `segWt_ne_zero`,
  `star_segWt_mul_segWt`, `segOf` (the map), `segOfₗ`, `segOfₗ_apply`, `segInner`, `segSiteWeight`,
  `segSiteWeight_segOf`, `segRegionWeight`; `IsEvenState`, `IsEvenState.neg_zero`,
  `IsEvenState.neg_one`, `neg_segSite_end`, `IsEvenState.end_one` (**the lower component vanishes
  at both ends**), `IsEvenState.diracHam_mulVec` (**`H` keeps the sector**), `IsEvenState.add`,
  `IsEvenState.smul`, `IsEvenState.pow_mulVec`;
* ★★ `chainInner_eq_segInner` — **the map is an isometry on the even sector**;
  ★★ `regionWeight_eq_segRegionWeight` — **a symmetric region's weight is the weight of its trace on
  the segment**; `chordArc_neg_mem` (the arcs about `±1` are symmetric);
* `segRead`, `segUnfold`, `isEvenState_segUnfold`, ★★ `segOf_segUnfold` — **onto the segment
  states whose lower component vanishes at both ends**.

## The segment Hamiltonian

* `segMask`, `segHop` (`√2` on an edge at an end, `1` inside), ★★ `segHam` — **the hop
  `−iJκ(|j⟩⟨j+1| − |j+1⟩⟨j|) ⊗ σ_x` and the rest energy `μ σ_z` on `{0, …, M}`, the lower component
  removed at both ends**; `sum_fin_ite_val_eq`, `sum_fin_ite_succ_val_eq`, `segHam_mulVec_apply`
  (its three reads); `segSite_succ`, `segSite_pred`, `segSite_zero_sub_one`, `segSite_top_add_one`
  (the neighbours on the ring, `M + 1 = −(M − 1)`), `segMask_of_not_end`, `segWt_mul_eq_nb` (an interior site reads a neighbour as `H_seg` does);
* ★★★ `segOf_diracHam_mulVec` — **`S H φ = H_seg S φ` on the even sector**;
  `segOf_pow_mulVec`, `segProp` (`e^{−itH_seg}`), ★★★ `segOf_chainProp_mulVec` — **`S e^{−itH} φ =
  e^{−itH_seg} S φ`**.

## The records on the segment

* `segTrace`; ★★★ `dirac_segment_return` — `dirac_return`'s records, with the wall state's image on
  the segment moved by `e^{−itH_seg}`, and the registers' weights at `A` and at `B` the weights of
  the segment's two end intervals.

## The finding

**The reflecting ends are explicit**: the segment Hamiltonian is the chain's, except that the lower
spinor component is absent at both ends and the two end edges carry `√2`. Nothing else changes — the
even sector is the open chain with that boundary condition, not an approximation of it.

## Honest scope

⚠️ **`M ≥ 2`**: the ends' neighbours are interior sites (at `M = 1` the end edge would carry `2`).

⚠️ **The records are not re-derived**: the ring's records of `dirac_return` are restated as
functions of the segment state; a detector law stated on the segment from scratch is not given.

References: `specs/BACKLOG.md` #275, #270, #256, #274, #39; `RecordLayer/DiracReturn.lean`
(`chainParity`, `diracHam_mulVec_chainParity`, `wallState`, `chainParity_wallState`,
`chainProp_wallState`, `dirac_return`); `RecordLayer/DiracTiming.lean` (`diracHam_mulVec_apply`);
`RecordLayer/DiracArrival.lean` (`chainProp`, `regionWeight`); `RecordLayer/DiracObservers.lean`
(`chordArc`); `CV/DiracClockChain.lean` (`diracHam`, `diracSx`, `diracSz`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

variable {M : ℕ} [NeZero M]

/-! ### The even sum -/

/-- A sum over `ZMod n` is a sum over `range n`. -/
theorem sum_zmod_eq_sum_range {n : ℕ} [NeZero n] {β : Type*} [AddCommMonoid β] (g : ZMod n → β) :
    ∑ k, g k = ∑ i ∈ Finset.range n, g (i : ZMod n) := by
  symm
  refine Finset.sum_bij (fun i _ => (i : ZMod n)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj h
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj'] at this
  · intro k _
    exact ⟨k.val, Finset.mem_range.2 (ZMod.val_lt k), ZMod.natCast_zmod_val k⟩
  · intro _ _
    rfl

/-- The site `j` of the segment, on the ring of `2M` sites. -/
def segSite (j : Fin (M + 1)) : ZMod (2 * M) := (j.val : ZMod (2 * M))

/-- The ends of the segment: `0` (`A`) and `M` (the antipode `B`). -/
def IsSegEnd (j : Fin (M + 1)) : Prop := j.val = 0 ∨ j.val = M

instance (j : Fin (M + 1)) : Decidable (IsSegEnd j) := by
  unfold IsSegEnd
  infer_instance

/-- ★★ **A parity-even sum over `ZMod (2M)`** is the two ends plus twice the interior of the segment
`{0, …, M}`. -/
theorem sum_zmod_even {β : Type*} [AddCommMonoid β] (g : ZMod (2 * M) → β)
    (hg : ∀ k, g (-k) = g k) :
    ∑ k, g k = ∑ j : Fin (M + 1), (if IsSegEnd j then 1 else 2) • g (segSite j) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  rw [sum_zmod_eq_sum_range, ← Finset.sum_range_add_sum_Ico _ (by omega : M + 1 ≤ 2 * M)]
  -- the upper half is the reflection of the interior
  have hup : ∑ i ∈ Finset.Ico (M + 1) (2 * M), g (i : ZMod (2 * M))
      = ∑ i ∈ Finset.Ico 1 M, g (i : ZMod (2 * M)) := by
    refine Finset.sum_bij' (fun i _ => 2 * M - i) (fun i _ => 2 * M - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, ← hg]
      congr 1
      rw [show ((2 : ZMod (2 * M)) * (M : ZMod (2 * M))) = ((2 * M : ℕ) : ZMod (2 * M)) by
        push_cast; ring, ZMod.natCast_self]
      ring
  have hR : (∑ j : Fin (M + 1), (if IsSegEnd j then 1 else 2) • g (segSite j))
      = ∑ i ∈ Finset.range (M + 1), (if i = 0 ∨ i = M then 1 else 2) • g (i : ZMod (2 * M)) :=
    Fin.sum_univ_eq_sum_range (fun i => (if i = 0 ∨ i = M then 1 else 2) • g (i : ZMod (2 * M)))
      (M + 1)
  rw [hup, hR]
  have hsplit : ∀ i ∈ Finset.range (M + 1),
      (if i = 0 ∨ i = M then 1 else 2) • g (i : ZMod (2 * M))
        = g (i : ZMod (2 * M)) + (if 1 ≤ i ∧ i < M then g (i : ZMod (2 * M)) else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases h : i = 0 ∨ i = M
    · rw [ite_eq_left h, ite_eq_right (by omega), one_smul, add_zero]
    · rw [ite_eq_right h, ite_eq_left (by omega), two_smul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_filter]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-! ### The segment -/

/-- **The weight of a segment site**: `1` at the ends, `√2` inside (an interior site stands for the
pair `±j` of the ring). -/
noncomputable def segWt (j : Fin (M + 1)) : ℂ := if IsSegEnd j then 1 else (Real.sqrt 2 : ℂ)

omit [NeZero M] in
theorem segWt_ne_zero (j : Fin (M + 1)) : segWt j ≠ 0 := by
  unfold segWt
  split_ifs
  · exact one_ne_zero
  · exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'

omit [NeZero M] in
theorem star_segWt_mul_segWt (j : Fin (M + 1)) :
    star (segWt j) * segWt j = ((if IsSegEnd j then 1 else 2 : ℕ) : ℂ) := by
  unfold segWt
  split_ifs
  · simp
  · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt zero_le_two]
    push_cast
    rfl

/-- **The map onto the segment**: `(Sφ)(j, a) = w_j φ(j, a)`. -/
noncomputable def segOf (φ : ZMod (2 * M) × Fin 2 → ℂ) : Fin (M + 1) × Fin 2 → ℂ :=
  fun p => segWt p.1 * φ (segSite p.1, p.2)

/-- The map onto the segment, as a linear map. -/
noncomputable def segOfₗ : (ZMod (2 * M) × Fin 2 → ℂ) →ₗ[ℂ] (Fin (M + 1) × Fin 2 → ℂ) where
  toFun := segOf
  map_add' φ ψ := by
    funext p
    simp only [segOf, Pi.add_apply]
    ring
  map_smul' c φ := by
    funext p
    simp only [segOf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [NeZero M] in
theorem segOfₗ_apply (φ : ZMod (2 * M) × Fin 2 → ℂ) : segOfₗ φ = segOf φ := rfl

/-- The inner product on the segment. -/
noncomputable def segInner (χ ξ : Fin (M + 1) × Fin 2 → ℂ) : ℂ := ∑ p, star (χ p) * ξ p

/-- The weight of a segment site. -/
noncomputable def segSiteWeight (χ : Fin (M + 1) × Fin 2 → ℂ) (j : Fin (M + 1)) : ℝ :=
  ∑ c : Fin 2, ‖χ (j, c)‖ ^ 2

/-- The weight of a set of segment sites. -/
noncomputable def segRegionWeight (χ : Fin (M + 1) × Fin 2 → ℂ) (B : Finset (Fin (M + 1))) : ℝ :=
  ∑ j ∈ B, segSiteWeight χ j

/-- **The even sector**: the states parity keeps. -/
def IsEvenState (φ : ZMod (2 * M) × Fin 2 → ℂ) : Prop := chainParity φ = φ

omit [NeZero M] in
theorem IsEvenState.neg_zero {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (k : ZMod (2 * M)) : φ (-k, 0) = φ (k, 0) := by
  have := congrFun hφ (k, 0)
  simpa [chainParity] using this

omit [NeZero M] in
theorem IsEvenState.neg_one {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (k : ZMod (2 * M)) : φ (-k, 1) = -φ (k, 1) := by
  have := congrFun hφ (k, 1)
  simp only [chainParity, Fin.isValue, one_ne_zero, ↓reduceIte, neg_mul, one_mul] at this
  rw [← this, neg_neg]

omit [NeZero M] in
theorem neg_segSite_end {j : Fin (M + 1)} (hj : IsSegEnd j) : -segSite j = segSite j := by
  rcases hj with h | h
  · simp [segSite, h]
  · rw [segSite, h, neg_eq_iff_add_eq_zero, ← two_mul]
    exact_mod_cast ZMod.natCast_self (2 * M)

omit [NeZero M] in
/-- **The lower component of an even state vanishes at both ends.** -/
theorem IsEvenState.end_one {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ) {j : Fin (M + 1)}
    (hj : IsSegEnd j) : φ (segSite j, 1) = 0 := by
  have h := hφ.neg_one (segSite j)
  rw [neg_segSite_end hj] at h
  linear_combination h / 2

/-- **`H` keeps the even sector.** -/
theorem IsEvenState.diracHam_mulVec {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ) (J μ : ℝ) :
    IsEvenState (diracHam J μ *ᵥ φ) := by
  unfold IsEvenState at hφ ⊢
  rw [← diracHam_mulVec_chainParity, hφ]

omit [NeZero M] in
theorem IsEvenState.add {φ ψ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (hψ : IsEvenState ψ) : IsEvenState (φ + ψ) := by
  unfold IsEvenState at *
  rw [chainParity_add, hφ, hψ]

omit [NeZero M] in
theorem IsEvenState.smul {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ) (c : ℂ) :
    IsEvenState (c • φ) := by
  unfold IsEvenState at *
  rw [chainParity_smul, hφ]

/-- ★★ **The map is an isometry on the even sector.** -/
theorem chainInner_eq_segInner {φ ψ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (hψ : IsEvenState ψ) : chainInner φ ψ = segInner (segOf φ) (segOf ψ) := by
  set g : ZMod (2 * M) → ℂ := fun k => ∑ a : Fin 2, star (φ (k, a)) * ψ (k, a) with hgdef
  have hg : ∀ k, g (-k) = g k := by
    intro k
    simp only [hgdef, Fin.sum_univ_two, hφ.neg_zero, hψ.neg_zero, hφ.neg_one, hψ.neg_one,
      star_neg, neg_mul_neg]
  have h1 : chainInner φ ψ = ∑ k, g k := by
    rw [chainInner, Fintype.sum_prod_type]
  rw [h1, sum_zmod_even g hg, segInner, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hgdef, segOf, star_mul', Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show star (segWt j) * star (φ (segSite j, a)) * (segWt j * ψ (segSite j, a))
      = (star (segWt j) * segWt j) * (star (φ (segSite j, a)) * ψ (segSite j, a)) by ring,
    star_segWt_mul_segWt, nsmul_eq_mul]

omit [NeZero M] in
theorem segSiteWeight_segOf (φ : ZMod (2 * M) × Fin 2 → ℂ) (j : Fin (M + 1)) :
    segSiteWeight (segOf φ) j = (if IsSegEnd j then 1 else 2) * siteWeight φ (segSite j) := by
  have hw : ‖segWt j‖ ^ 2 = if IsSegEnd j then 1 else 2 := by
    unfold segWt
    split_ifs
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt zero_le_two]
  simp only [segSiteWeight, siteWeight, segOf, norm_mul, mul_pow, ← Finset.mul_sum, hw]

/-- ★★ **A symmetric region's weight is the weight of its trace on the segment.** -/
theorem regionWeight_eq_segRegionWeight {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    {A : Finset (ZMod (2 * M))} (hA : ∀ k, -k ∈ A ↔ k ∈ A) :
    regionWeight φ A
      = segRegionWeight (segOf φ) (Finset.univ.filter fun j => segSite j ∈ A) := by
  set g : ZMod (2 * M) → ℝ := fun k => if k ∈ A then siteWeight φ k else 0 with hgdef
  have hsw : ∀ k, siteWeight φ (-k) = siteWeight φ k := by
    intro k
    simp only [siteWeight, Fin.sum_univ_two, hφ.neg_zero, hφ.neg_one, norm_neg]
  have hg : ∀ k, g (-k) = g k := by
    intro k
    simp only [hgdef, hA, hsw]
  have h1 : regionWeight φ A = ∑ k, g k := by
    rw [regionWeight]
    simp only [hgdef, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [h1, sum_zmod_even g hg, segRegionWeight, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hgdef, segSiteWeight_segOf, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- The arcs about `±1` are symmetric. -/
theorem chordArc_neg_mem {z : ℝ} {ρ : ℝ} (k : ZMod (2 * M)) :
    -k ∈ chordArc (L := 2 * M) (z : ℂ) ρ ↔ k ∈ chordArc (L := 2 * M) (z : ℂ) ρ := by
  rw [mem_chordArc, mem_chordArc, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
    show (starRingEnd ℂ) (ZMod.toCircle k : ℂ) - (z : ℂ)
      = (starRingEnd ℂ) ((ZMod.toCircle k : ℂ) - (z : ℂ)) by rw [map_sub, Complex.conj_ofReal],
    Complex.norm_conj]

/-! ### Onto -/

/-- The segment state at a natural-number site, divided by its weight; `0` beyond the end. -/
noncomputable def segRead (χ : Fin (M + 1) × Fin 2 → ℂ) (n : ℕ) (a : Fin 2) : ℂ :=
  if h : n < M + 1 then χ (⟨n, h⟩, a) / segWt (⟨n, h⟩ : Fin (M + 1)) else 0

/-- **The even state of a segment state**: site `k` of the ring reads the segment at `k` or at
`2M − k`, the lower component with the parity sign. -/
noncomputable def segUnfold (χ : Fin (M + 1) × Fin 2 → ℂ) : ZMod (2 * M) × Fin 2 → ℂ := fun p =>
  if p.1.val ≤ M then segRead χ p.1.val p.2
  else (if p.2 = 0 then 1 else -1) * segRead χ (2 * M - p.1.val) p.2

theorem segSite_val (j : Fin (M + 1)) : (segSite j).val = j.val := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  exact ZMod.val_cast_of_lt (by omega)

/-- ★★ **Onto**: every segment state is the image of its unfolding (which is even when the lower
component vanishes at both ends, `isEvenState_segUnfold`). -/
theorem segOf_segUnfold (χ : Fin (M + 1) × Fin 2 → ℂ) : segOf (segUnfold χ) = χ := by
  funext ⟨j, a⟩
  have hj : j.val ≤ M := by omega
  simp only [segOf, segUnfold, segSite_val, segRead]
  rw [ite_eq_left hj]
  simp only [j.isLt, ↓reduceDIte]
  rw [mul_div_cancel₀ _ (segWt_ne_zero j)]

theorem isEvenState_segUnfold {χ : Fin (M + 1) × Fin 2 → ℂ}
    (hχ : ∀ j, IsSegEnd j → χ (j, 1) = 0) : IsEvenState (segUnfold χ) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hEnd : ∀ n (h : n < M + 1), (n = 0 ∨ n = M) → segRead χ n 1 = 0 := by
    intro n h hn
    simp only [segRead, h, dite_true, hχ ⟨n, h⟩ hn, zero_div]
  funext ⟨k, a⟩
  simp only [chainParity, segUnfold]
  have hk := ZMod.val_lt k
  by_cases hk0 : k = 0
  · subst hk0
    simp only [neg_zero, ZMod.val_zero, zero_le, ite_true]
    fin_cases a
    · simp
    · simp [hEnd 0 (by omega) (Or.inl rfl)]
  have hneg : (-k).val = 2 * M - k.val := by
    rw [ZMod.neg_val, ite_eq_right hk0]
  rw [hneg]
  by_cases hkM : k.val = M
  · have e1 : 2 * M - k.val = M := by omega
    rw [e1, hkM]
    fin_cases a
    · simp
    · simp [hEnd M (by omega) (Or.inr rfl)]
  by_cases hkle : k.val ≤ M
  · have h1 : ¬ 2 * M - k.val ≤ M := by omega
    have e2 : 2 * M - (2 * M - k.val) = k.val := by omega
    rw [ite_eq_right h1, ite_eq_left hkle, e2]
    fin_cases a
    · simp
    · simp
  · have h1 : 2 * M - k.val ≤ M := by omega
    rw [ite_eq_left h1, ite_eq_right hkle]

/-! ### The segment Hamiltonian -/

/-- The lower component is absent at both ends. -/
noncomputable def segMask (p : Fin (M + 1) × Fin 2) : ℂ :=
  if IsSegEnd p.1 ∧ p.2 = 1 then 0 else 1

/-- The hop weight: `√2` on an edge at an end, `1` inside. -/
noncomputable def segHop (j j' : Fin (M + 1)) : ℂ :=
  if IsSegEnd j ∨ IsSegEnd j' then (Real.sqrt 2 : ℂ) else 1

/-- ★★ **The segment Hamiltonian**: on `{0, …, M}`, the hop `−iJκ(|j⟩⟨j+1| − |j+1⟩⟨j|) ⊗ σ_x` with
`κ = √2` on the two end edges, the rest energy `μ σ_z`, and the lower component removed at both ends
(the reflecting boundary). -/
noncomputable def segHam (J μ : ℝ) : Matrix (Fin (M + 1) × Fin 2) (Fin (M + 1) × Fin 2) ℂ :=
  Matrix.of fun p q => segMask p * segMask q *
    ((J : ℂ) * (-I) * ((if q.1.val = p.1.val + 1 then 1 else 0)
        - (if q.1.val + 1 = p.1.val then 1 else 0)) * segHop p.1 q.1 * diracSx p.2 q.2
      + (μ : ℂ) * (if q.1 = p.1 then 1 else 0) * diracSz p.2 q.2)


omit [NeZero M] in
theorem sum_fin_ite_val_eq (n : ℕ) (f : Fin (M + 1) → ℂ) :
    ∑ q : Fin (M + 1), (if (q : ℕ) = n then f q else 0)
      = if h : n < M + 1 then f ⟨n, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      exact ite_eq_right (fun hbn => hb (Fin.ext hbn))
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun q _ => ite_eq_right fun hq => ?_
    have := q.isLt
    omega

omit [NeZero M] in
theorem sum_fin_ite_succ_val_eq (n : ℕ) (f : Fin (M + 1) → ℂ) :
    ∑ q : Fin (M + 1), (if (q : ℕ) + 1 = n then f q else 0)
      = if h : 0 < n ∧ n - 1 < M + 1 then f ⟨n - 1, h.2⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n - 1, h.2⟩]
    · simp only [ite_eq_left_iff]
      intro h'
      exact absurd (by omega) h'
    · intro b _ hb
      refine ite_eq_right (fun hbn => hb (Fin.ext ?_))
      simp only
      omega
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun q _ => ite_eq_right fun hq => ?_
    have := q.isLt
    omega

omit [NeZero M] in
theorem segSite_succ (j : Fin (M + 1)) (h : j.val + 1 < M + 1) :
    segSite j + 1 = segSite ⟨j.val + 1, h⟩ := by
  simp [segSite]

omit [NeZero M] in
theorem segSite_pred (j : Fin (M + 1)) (h : 0 < j.val) :
    segSite j - 1 = segSite ⟨j.val - 1, by omega⟩ := by
  simp only [segSite]
  rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
  simp

omit [NeZero M] in
/-- An interior site reads a neighbour as the segment Hamiltonian does. -/
theorem segWt_mul_eq_nb {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ) {j : Fin (M + 1)}
    (hj : ¬ IsSegEnd j) (q : Fin (M + 1)) (b : Fin 2) :
    segWt j * φ (segSite q, b) = segMask (q, b) * segHop j q * (segWt q * φ (segSite q, b)) := by
  by_cases hq : IsSegEnd q
  · fin_cases b
    · simp [segWt, segMask, segHop, hj, hq]
    · simp [hφ.end_one hq]
  · simp [segWt, segMask, segHop, hj, hq]

omit [NeZero M] in
theorem segSite_zero_sub_one (hM : 1 ≤ M) {j : Fin (M + 1)} (hj : j.val = 0) :
    segSite j - 1 = -segSite ⟨1, by omega⟩ := by
  simp [segSite, hj]

omit [NeZero M] in
theorem segSite_top_add_one (hM : 1 ≤ M) {j : Fin (M + 1)} (hj : j.val = M) :
    segSite j + 1 = -segSite ⟨M - 1, by omega⟩ := by
  simp only [segSite, hj]
  rw [eq_neg_iff_add_eq_zero, Nat.cast_sub hM, Nat.cast_one,
    show (M : ZMod (2 * M)) + 1 + ((M : ZMod (2 * M)) - 1) = ((2 * M : ℕ) : ZMod (2 * M)) by
      push_cast; ring,
    ZMod.natCast_self]

omit [NeZero M] in
/-- The segment Hamiltonian on a segment state, in its three reads. -/
theorem segHam_mulVec_apply (J μ : ℝ) (χ : Fin (M + 1) × Fin 2 → ℂ) (j : Fin (M + 1)) (a : Fin 2) :
    (segHam J μ *ᵥ χ) (j, a)
      = segMask (j, a) * segMask (j, a) * μ * (if a = 0 then 1 else -1) * χ (j, a)
        + ((if h : j.val + 1 < M + 1 then segMask (j, a) * segMask (⟨j.val + 1, h⟩, 1 - a)
              * (J * -I * segHop j ⟨j.val + 1, h⟩) * χ (⟨j.val + 1, h⟩, 1 - a) else 0)
          - (if h : 0 < j.val ∧ j.val - 1 < M + 1 then segMask (j, a)
              * segMask (⟨j.val - 1, h.2⟩, 1 - a) * (J * -I * segHop j ⟨j.val - 1, h.2⟩)
              * χ (⟨j.val - 1, h.2⟩, 1 - a) else 0)) := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  all_goals
    simp only [Matrix.mulVec, dotProduct, segHam, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, diracSx, diracSz]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_zero, mul_one, add_zero, zero_add]
    simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ite_mul, mul_ite, zero_mul, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', sum_fin_ite_val_eq, sum_fin_ite_succ_val_eq]
    simp only [Finset.mem_univ, ite_true]
  all_goals simp only [show (1 : Fin 2) - 0 = 1 from rfl, show (1 : Fin 2) - 1 = 0 from rfl,
    one_ne_zero, ↓reduceIte]
  all_goals ring

omit [NeZero M] in
theorem segMask_of_not_end {j : Fin (M + 1)} (hj : ¬ IsSegEnd j) (a : Fin 2) :
    segMask (j, a) = 1 := by
  simp [segMask, hj]

/-- ★★★ **The segment Hamiltonian is the Dirac Hamiltonian on the even sector**:
`S H φ = H_seg S φ`. -/
theorem segOf_diracHam_mulVec (hM : 2 ≤ M) {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (J μ : ℝ) : segOf (diracHam J μ *ᵥ φ) = segHam J μ *ᵥ segOf φ := by
  funext ⟨j, a⟩
  rw [segHam_mulVec_apply]
  simp only [segOf]
  rw [diracHam_mulVec_apply]
  have hs := sqrt2_mul_sqrt2
  by_cases hj0 : j.val = 0
  · have hE : IsSegEnd j := Or.inl hj0
    have h1 : j.val + 1 < M + 1 := by omega
    have hn : ¬ (0 < j.val ∧ j.val - 1 < M + 1) := by omega
    have q1 : (⟨j.val + 1, h1⟩ : Fin (M + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp [hj0])
    have h1E : ¬ IsSegEnd (⟨1, by omega⟩ : Fin (M + 1)) := by unfold IsSegEnd; simp; omega
    rw [dite_eq_left h1, dite_eq_right hn, q1, segSite_succ j h1, q1,
      segSite_zero_sub_one (by omega) hj0]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · simp only [show (1 : Fin 2) - 0 = 1 from rfl, hφ.neg_one, segMask, segHop, segWt, hE, h1E,
        Fin.isValue, zero_ne_one, and_false, ↓reduceIte, and_true, or_false]
      linear_combination (J * I * φ (segSite ⟨1, by omega⟩, 1)) * hs
    · have hz := hφ.end_one hE
      simp only [show (1 : Fin 2) - 1 = 0 from rfl, hφ.neg_zero, segMask, hE, true_and,
        ↓reduceIte, hz]
      ring
  by_cases hjM : j.val = M
  · have hE : IsSegEnd j := Or.inr hjM
    have h1 : ¬ j.val + 1 < M + 1 := by omega
    have hn : 0 < j.val ∧ j.val - 1 < M + 1 := by omega
    have q1 : (⟨j.val - 1, hn.2⟩ : Fin (M + 1)) = ⟨M - 1, by omega⟩ := Fin.ext (by simp [hjM])
    have h1E : ¬ IsSegEnd (⟨M - 1, by omega⟩ : Fin (M + 1)) := by unfold IsSegEnd; simp; omega
    rw [dite_eq_right h1, dite_eq_left hn, q1, segSite_top_add_one (by omega) hjM,
      segSite_pred j hn.1]
    have q2 : (⟨j.val - 1, by omega⟩ : Fin (M + 1)) = ⟨M - 1, by omega⟩ := Fin.ext (by simp [hjM])
    rw [q2]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · simp only [show (1 : Fin 2) - 0 = 1 from rfl, hφ.neg_one, segMask, segHop, segWt, hE, h1E,
        Fin.isValue, zero_ne_one, and_false, ↓reduceIte, and_true, or_false]
      linear_combination (-(J * I * φ (segSite ⟨M - 1, by omega⟩, 1))) * hs
    · have hz := hφ.end_one hE
      simp only [show (1 : Fin 2) - 1 = 0 from rfl, hφ.neg_zero, segMask, hE, true_and,
        ↓reduceIte, hz]
      ring
  · have hI : ¬ IsSegEnd j := by unfold IsSegEnd; omega
    have h1 : j.val + 1 < M + 1 := by omega
    have hn : 0 < j.val ∧ j.val - 1 < M + 1 := by omega
    rw [dite_eq_left h1, dite_eq_left hn, segSite_succ j h1, segSite_pred j hn.1,
      segMask_of_not_end hI]
    have e1 := segWt_mul_eq_nb hφ hI ⟨j.val + 1, h1⟩ (1 - a)
    have e2 := segWt_mul_eq_nb hφ hI ⟨j.val - 1, hn.2⟩ (1 - a)
    linear_combination (J * -I) * e1 - (J * -I) * e2

theorem IsEvenState.pow_mulVec {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ) (J μ : ℝ)
    (n : ℕ) : IsEvenState (diracHam J μ ^ n *ᵥ φ) := by
  induction n with
  | zero => simpa using hφ
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact ih.diracHam_mulVec J μ

theorem segOf_pow_mulVec (hM : 2 ≤ M) {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (J μ : ℝ) (n : ℕ) : segOf (diracHam J μ ^ n *ᵥ φ) = segHam J μ ^ n *ᵥ segOf φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, segOf_diracHam_mulVec hM (hφ.pow_mulVec J μ n), ih,
      pow_succ', Matrix.mulVec_mulVec]

/-- **The segment propagator** `e^{−itH_seg}`. -/
noncomputable def segProp (J μ t : ℝ) : Matrix (Fin (M + 1) × Fin 2) (Fin (M + 1) × Fin 2) ℂ :=
  NormedSpace.exp ((-(I * t)) • segHam J μ)

open scoped Matrix.Norms.L2Operator in
/-- ★★★ **The segment propagator is the chain's on the even sector**:
`S e^{−itH} φ = e^{−itH_seg} S φ`. -/
theorem segOf_chainProp_mulVec (hM : 2 ≤ M) {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsEvenState φ)
    (J μ t : ℝ) : segOf (chainProp (L := 2 * M) J μ t *ᵥ φ) = segProp J μ t *ᵥ segOf φ := by
  set c : ℂ := -(I * t)
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • diracHam (L := 2 * M) J μ)
  have hB := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • segHam (M := M) J μ)
  let LA : Matrix (ZMod (2 * M) × Fin 2) (ZMod (2 * M) × Fin 2) ℂ →ₗ[ℂ]
      (Fin (M + 1) × Fin 2 → ℂ) :=
    { toFun := fun A => segOf (A *ᵥ φ)
      map_add' := fun A B => by rw [Matrix.add_mulVec, ← segOfₗ_apply, map_add]; rfl
      map_smul' := fun a A => by
        rw [Matrix.smul_mulVec, ← segOfₗ_apply, map_smul]; rfl }
  let LB : Matrix (Fin (M + 1) × Fin 2) (Fin (M + 1) × Fin 2) ℂ →ₗ[ℂ]
      (Fin (M + 1) × Fin 2 → ℂ) :=
    { toFun := fun A => A *ᵥ segOf φ
      map_add' := fun A B => Matrix.add_mulVec A B _
      map_smul' := fun a A => Matrix.smul_mulVec a A _ }
  have h1 := hA.mapL (LinearMap.toContinuousLinearMap LA)
  have h2 := hB.mapL (LinearMap.toContinuousLinearMap LB)
  have heq : (fun n => LinearMap.toContinuousLinearMap LA
        (((n.factorial : ℂ)⁻¹) • (c • diracHam (L := 2 * M) J μ) ^ n))
      = fun n => LinearMap.toContinuousLinearMap LB
        (((n.factorial : ℂ)⁻¹) • (c • segHam (M := M) J μ) ^ n) := by
    funext n
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, LA, LB,
      smul_pow, Matrix.smul_mulVec]
    rw [← segOfₗ_apply, map_smul, map_smul, segOfₗ_apply, segOf_pow_mulVec hM hφ]
  rw [heq] at h1
  exact h1.unique h2


/-! ### The records on the segment -/

/-- The trace of a ring region on the segment. -/
def segTrace (A : Finset (ZMod (2 * M))) : Finset (Fin (M + 1)) :=
  Finset.univ.filter fun j => segSite j ∈ A

/-- ★★★ **The return leg on the segment (#275).** On a ring of `2M ≥ 10¹⁹` sites, the wall state of
`dirac_return` is parity-even at every time; its image on the segment `{0, …, M}` is moved by the
segment propagator `e^{−itH_seg}`, has norm `1`, and the weights the detectors at `A` (the arc about
`1`) and at `B` (the arc about `−1`) read are the weights of the segment's traces of those arcs.
The records of `dirac_return` — emission at `A`, reception at `B`, return at `A`, one evolution,
ordered, the round trip within `0.3·1.25·10¹³` below `2ℓ_AB/v` — are thereby records of the
segment's evolution. -/
theorem dirac_segment_return (hL : 10 ^ 19 ≤ 2 * M) {w : ℝ} (hw : 0 ≤ w) :
    let em := wallEmission (L := 2 * M) hL hw
    let rcv := wallReception (L := 2 * M) hL hw
    let ret := wallReturn (L := 2 * M) hL hw
    let J := scaledHop 1 (2 * Real.pi * 10 ^ 13 / (2 * M : ℕ))
    (∀ t, (em.evolve 0 t em.prep).1 = wallState t ∧ IsEvenState (wallState (L := 2 * M) t))
    ∧ (∀ t, segOf (wallState (L := 2 * M) t) = segProp J 3 t *ᵥ segOf (wallState (L := 2 * M) 0))
    ∧ (∀ t, segInner (segOf (wallState (L := 2 * M) t)) (segOf (wallState (L := 2 * M) t)) = 1)
    ∧ (∀ t, regionWeight (wallState (L := 2 * M) t) (chordArc 1 (1 / 5))
        = segRegionWeight (segOf (wallState (L := 2 * M) t)) (segTrace (chordArc 1 (1 / 5))))
    ∧ (∀ t, regionWeight (wallState (L := 2 * M) t) (chordArc (-1) (1 / 5))
        = segRegionWeight (segOf (wallState (L := 2 * M) t)) (segTrace (chordArc (-1) (1 / 5))))
    ∧ em.writeEnd < rcv.writeStart ∧ rcv.writeEnd < ret.writeStart
    ∧ 2 * (Real.pi * 10 ^ 13) / (4 / 5) - 3 / 10 * (125 * 10 ^ 11) ≤ ret.writeStart - em.writeEnd
    ∧ ret.writeEnd - em.writeStart ≤ 2 * (Real.pi * 10 ^ 13) / (4 / 5) := by
  intro em rcv ret J
  have hM : 2 ≤ M := by
    by_contra h
    have : 2 * M ≤ 2 := by omega
    have h19 : (2 : ℕ) < 10 ^ 19 := by norm_num
    omega
  obtain ⟨-, -, hev, -, h1, h2, h3, h4⟩ := dirac_return (L := 2 * M) hL hw
  have hE : ∀ t, IsEvenState (wallState (L := 2 * M) t) := fun t => (hev t).2.1
  have hA : ∀ k : ZMod (2 * M), -k ∈ chordArc (L := 2 * M) ((1 : ℝ) : ℂ) (1 / 5)
      ↔ k ∈ chordArc (L := 2 * M) ((1 : ℝ) : ℂ) (1 / 5) := chordArc_neg_mem
  have hB : ∀ k : ZMod (2 * M), -k ∈ chordArc (L := 2 * M) ((-1 : ℝ) : ℂ) (1 / 5)
      ↔ k ∈ chordArc (L := 2 * M) ((-1 : ℝ) : ℂ) (1 / 5) := chordArc_neg_mem
  push_cast at hA hB
  refine ⟨fun t => ⟨(hev t).1, hE t⟩, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    h1, h2, h3, h4⟩
  · rw [← segOf_chainProp_mulVec hM (hE 0), chainProp_wallState]
  · rw [← chainInner_eq_segInner (hE t) (hE t), wallState_norm hL]
  · exact regionWeight_eq_segRegionWeight (hE t) hA
  · exact regionWeight_eq_segRegionWeight (hE t) hB

end CSD.RecordLayer

end
