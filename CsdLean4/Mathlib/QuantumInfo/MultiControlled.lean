/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Matrix.TwoLevel

/-!
# A two-level unitary on qubits is a Gray-code sandwich of multiply-controlled gates

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #71, part (d) of `R-005`
(`specs/magic-plan.md`, "The split").

On the computational basis `Fin m → Fin 2` of `m` qubits, a **multiply-controlled gate**
`ctrlGate j pat a b c d` acts by the `2 × 2` block `!![a, b; c, d]` on qubit `j` of those basis
labels that agree with `pat` away from `j`, and as the identity on every other label. The bridge to
the two-level matrices of `TwoLevel.lean` is exact: ★ `ctrlGate_eq_twoLevelMat` identifies it with
the two-level matrix on the adjacent pair `pat[j ↦ 0]`, `pat[j ↦ 1]`. So a multiply-controlled `X`
(`ctrlGate j pat 0 1 1 0`) is the transposition of two labels differing in one bit.

Nielsen–Chuang §4.5.2: a two-level unitary on labels `u ≠ v` becomes a multiply-controlled gate
once `u` is walked to a neighbour of `v` along a Gray code, each step being a multiply-controlled
`X`. Here the Gray code is the recursion itself: flip one differing bit, conjugate, and the
differing set shrinks by one.

* `swapMat u v` — the transposition of two labels; `swapMat_apply` (its entries are the
  permutation's), `swapMat_mul_self`, `swapMat_mem_unitaryGroup`;
* ★ `swapMat_conj_apply` — **conjugating by a transposition relabels**:
  `(S V S) k l = V (swap u v k) (swap u v l)`, hence ★ `idOutside_swapMat_conj`;
* `Adjacent u v`, `diffSet`, `adjacent_iff_diffSet_card_eq_one`;
* `ctrlGate`, ★ `ctrlGate_eq_twoLevelMat`, `ctrlGate_mem_unitaryGroup`,
  ★ `exists_ctrlGate_of_adjacent` — **a two-level matrix on an adjacent pair is a
  multiply-controlled gate**;
* `IsMultiCtrlX`, `IsMultiCtrlGate`;
* ★★ `exists_multiCtrl_sandwich` — **every two-level unitary on qubits is
  `L · W · L⁻¹`** with `L` a list of multiply-controlled `X`s and `W` a single multiply-controlled
  gate; ★ `exists_multiCtrl_list` — the same as one flat product, the form #72 consumes.

## Honest scope

⚠️ Existence and structure, no gate counts: the Gray walk here flips the differing bits in the
order the recursion picks them, and `L.length` is the Hamming distance minus one, but no optimality
or circuit-size claim is made (the counting row is #82 for #70; efficiency overall is #74, kept not
claimed). Decomposing a multiply-controlled gate into `CNOT`s and single-qubit gates is #72.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.5.2;
`specs/magic-plan.md`; `specs/BACKLOG.md` #71; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace MultiControlled

open TwoLevel

variable {m : ℕ}

/-! ### Transpositions of basis labels -/

/-- The transposition of two basis labels, as a matrix. -/
noncomputable def swapMat (u v : Fin m → Fin 2) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  twoLevelMat u v 0 1 1 0

theorem swapMat_mem_unitaryGroup {u v : Fin m → Fin 2} (huv : u ≠ v) :
    swapMat u v ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ :=
  twoLevelMat_mem_unitaryGroup huv (by simp) (by simp) (by simp) (by simp)

theorem isTwoLevel_swapMat {u v : Fin m → Fin 2} (huv : u ≠ v) : IsTwoLevel (swapMat u v) :=
  isTwoLevel_twoLevelMat huv

theorem swapMat_mul_self {u v : Fin m → Fin 2} (huv : u ≠ v) :
    swapMat u v * swapMat u v = 1 := by
  rw [swapMat, twoLevelMat_mul huv, show (0:ℂ) * 0 + 1 * 1 = 1 by norm_num,
    show (0:ℂ) * 1 + 1 * 0 = 0 by norm_num, show (1:ℂ) * 0 + 0 * 1 = 0 by norm_num,
    show (1:ℂ) * 1 + 0 * 0 = 1 by norm_num, twoLevelMat_one huv]

/-- The entries of the transposition matrix are those of the permutation. -/
theorem swapMat_apply {u v : Fin m → Fin 2} (huv : u ≠ v) (k l : Fin m → Fin 2) :
    swapMat u v k l = if k = Equiv.swap u v l then 1 else 0 := by
  rw [swapMat]
  by_cases hl : l = u
  · rw [hl, Equiv.swap_apply_left]
    by_cases hk : k = u
    · rw [hk, twoLevelMat_apply_fst_fst, if_neg huv]
    · by_cases hk' : k = v
      · rw [hk', twoLevelMat_apply_snd_fst huv, if_pos rfl]
      · rw [twoLevelMat_apply_of_row_ne hk hk', if_neg hk, if_neg hk']
  · by_cases hl' : l = v
    · rw [hl', Equiv.swap_apply_right]
      by_cases hk : k = u
      · rw [hk, twoLevelMat_apply_fst_snd huv, if_pos rfl]
      · by_cases hk' : k = v
        · rw [hk', twoLevelMat_apply_snd_snd huv, if_neg (Ne.symm huv)]
        · rw [twoLevelMat_apply_of_row_ne hk hk', if_neg hk', if_neg hk]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hl', twoLevelMat_apply_of_col_ne hl hl']

/-- ★ **Conjugating by a transposition relabels the matrix.** -/
theorem swapMat_conj_apply {u v : Fin m → Fin 2} (huv : u ≠ v)
    (V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) (k l : Fin m → Fin 2) :
    (swapMat u v * V * swapMat u v) k l = V (Equiv.swap u v k) (Equiv.swap u v l) := by
  have hinner : ∀ p : Fin m → Fin 2, (swapMat u v * V) k p = V (Equiv.swap u v k) p := by
    intro p
    rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap u v k)]
    · rw [swapMat_apply huv, Equiv.swap_apply_self, if_pos rfl, one_mul]
    · intro q _ hq
      rw [swapMat_apply huv, if_neg ?_, zero_mul]
      intro hkq
      exact hq (by rw [hkq, Equiv.swap_apply_self])
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap u v l)]
  · rw [hinner, swapMat_apply huv, if_pos rfl, mul_one]
  · intro q _ hq
    rw [swapMat_apply huv, if_neg hq, mul_zero]
  · intro hq
    exact absurd (Finset.mem_univ _) hq

/-- ★ Conjugating a two-level matrix by a transposition moves its block to the swapped pair. -/
theorem idOutside_swapMat_conj {u u' v : Fin m → Fin 2} (huu' : u ≠ u')
    (hvu' : v ≠ u') {V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hid : IdOutside {u, v} V) :
    IdOutside {u', v} (swapMat u u' * V * swapMat u u') := by
  intro k l hkl
  rw [swapMat_conj_apply huu']
  have hmap : ∀ x : Fin m → Fin 2, x ∉ ({u', v} : Finset (Fin m → Fin 2)) →
      Equiv.swap u u' x ∉ ({u, v} : Finset (Fin m → Fin 2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx ⊢
    obtain ⟨hxu', hxv⟩ := hx
    by_cases hxu : x = u
    · rw [hxu, Equiv.swap_apply_left]
      exact ⟨Ne.symm huu', Ne.symm hvu'⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxu']
      exact ⟨hxu, hxv⟩
  have hswap : Equiv.swap u u' k = Equiv.swap u u' l ↔ k = l := by
    constructor
    · intro h
      exact (Equiv.swap u u').injective h
    · intro h
      rw [h]
  rcases hkl with hk | hl
  · rw [hid _ _ (Or.inl (hmap k hk))]
    by_cases h : k = l
    · rw [h, if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hc => h (hswap.mp hc))]
  · rw [hid _ _ (Or.inr (hmap l hl))]
    by_cases h : k = l
    · rw [h, if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hc => h (hswap.mp hc))]

/-! ### Adjacent labels -/

/-- The set of qubits where two labels differ. -/
def diffSet (u v : Fin m → Fin 2) : Finset (Fin m) := Finset.univ.filter fun i => u i ≠ v i

theorem mem_diffSet {u v : Fin m → Fin 2} {i : Fin m} : i ∈ diffSet u v ↔ u i ≠ v i := by
  simp [diffSet]

theorem diffSet_eq_empty_iff {u v : Fin m → Fin 2} : diffSet u v = ∅ ↔ u = v := by
  constructor
  · intro h
    funext i
    by_contra hi
    exact absurd (mem_diffSet.mpr hi) (by rw [h]; simp)
  · intro h
    ext i
    simp [diffSet, h]

/-- Two labels are **adjacent** when they differ in exactly one qubit. -/
def Adjacent (u v : Fin m → Fin 2) : Prop :=
  ∃ j, u j ≠ v j ∧ ∀ i, i ≠ j → u i = v i

theorem adjacent_of_diffSet_card_eq_one {u v : Fin m → Fin 2} (h : (diffSet u v).card = 1) :
    Adjacent u v := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  refine ⟨j, mem_diffSet.mp (by rw [hj]; simp), fun i hi => ?_⟩
  by_contra hne
  have : i ∈ diffSet u v := mem_diffSet.mpr hne
  rw [hj, Finset.mem_singleton] at this
  exact hi this

/-! ### Multiply-controlled gates -/

/-- The `2 × 2` block entry selected by a pair of bits. -/
def blockEntry (x y : Fin 2) (a b c d : ℂ) : ℂ :=
  if x = 0 then (if y = 0 then a else b) else (if y = 0 then c else d)

/-- The **multiply-controlled gate**: the `2 × 2` block `!![a, b; c, d]` applied to qubit `j` of
the basis labels agreeing with `pat` away from `j`, the identity on all other labels. -/
def ctrlGate (j : Fin m) (pat : Fin m → Fin 2) (a b c d : ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := fun k l =>
  if (∀ i, i ≠ j → k i = pat i) ∧ (∀ i, i ≠ j → l i = pat i) then
    blockEntry (k j) (l j) a b c d
  else if k = l then 1 else 0

theorem eq_update_iff {k pat : Fin m → Fin 2} {j : Fin m} {x : Fin 2} :
    k = Function.update pat j x ↔ (∀ i, i ≠ j → k i = pat i) ∧ k j = x := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [h, Function.update_of_ne hi]
    · rw [h, Function.update_self]
  · intro ⟨h1, h2⟩
    funext i
    by_cases hi : i = j
    · rw [hi, h2, Function.update_self]
    · rw [Function.update_of_ne hi, h1 i hi]

theorem update_ne_update {pat : Fin m → Fin 2} {j : Fin m} :
    Function.update pat j 0 ≠ Function.update pat j 1 := by
  intro h
  have := congrFun h j
  rw [Function.update_self, Function.update_self] at this
  exact absurd this (by decide)

/-- ★ **A multiply-controlled gate is the two-level matrix on the adjacent pair it acts on.** -/
theorem ctrlGate_eq_twoLevelMat (j : Fin m) (pat : Fin m → Fin 2) (a b c d : ℂ) :
    ctrlGate j pat a b c d
      = twoLevelMat (Function.update pat j 0) (Function.update pat j 1) a b c d := by
  ext k l
  by_cases hk : ∀ i, i ≠ j → k i = pat i
  · by_cases hl : ∀ i, i ≠ j → l i = pat i
    · rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k j) with hkj | hkj <;>
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l j) with hlj | hlj <;>
        rw [ctrlGate, if_pos ⟨hk, hl⟩, blockEntry] <;>
        rw [show k = Function.update pat j (k j) from eq_update_iff.mpr ⟨hk, rfl⟩,
          show l = Function.update pat j (l j) from eq_update_iff.mpr ⟨hl, rfl⟩] <;>
        rw [hkj, hlj] <;>
        simp [twoLevelMat_apply_fst_snd update_ne_update, twoLevelMat_apply_snd_fst update_ne_update,
          twoLevelMat_apply_snd_snd update_ne_update]
    · have hl0 : l ≠ Function.update pat j 0 := fun h => hl (eq_update_iff.mp h).1
      have hl1 : l ≠ Function.update pat j 1 := fun h => hl (eq_update_iff.mp h).1
      rw [ctrlGate, if_neg (by tauto), twoLevelMat_apply_of_col_ne hl0 hl1]
  · have hk0 : k ≠ Function.update pat j 0 := fun h => hk (eq_update_iff.mp h).1
    have hk1 : k ≠ Function.update pat j 1 := fun h => hk (eq_update_iff.mp h).1
    rw [ctrlGate, if_neg (by tauto), twoLevelMat_apply_of_row_ne hk0 hk1]

theorem ctrlGate_mem_unitaryGroup (j : Fin m) (pat : Fin m → Fin 2) {a b c d : ℂ}
    (h1 : starRingEnd ℂ a * a + starRingEnd ℂ c * c = 1)
    (h2 : starRingEnd ℂ b * b + starRingEnd ℂ d * d = 1)
    (h3 : starRingEnd ℂ a * b + starRingEnd ℂ c * d = 0)
    (h4 : starRingEnd ℂ b * a + starRingEnd ℂ d * c = 0) :
    ctrlGate j pat a b c d ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  rw [ctrlGate_eq_twoLevelMat]
  exact twoLevelMat_mem_unitaryGroup update_ne_update h1 h2 h3 h4

/-- A multiply-controlled `X`: the transposition of two labels differing in one qubit. -/
def IsMultiCtrlX (X : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) : Prop :=
  ∃ (j : Fin m) (pat : Fin m → Fin 2), X = ctrlGate j pat 0 1 1 0

/-- A multiply-controlled single-qubit gate. -/
def IsMultiCtrlGate (W : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) : Prop :=
  ∃ (j : Fin m) (pat : Fin m → Fin 2) (a b c d : ℂ), W = ctrlGate j pat a b c d

theorem twoLevelMat_swap_block {u v : Fin m → Fin 2} (huv : u ≠ v) (a b c d : ℂ) :
    twoLevelMat u v a b c d = twoLevelMat v u d c b a := by
  ext k l
  by_cases hk : k = u <;> by_cases hk' : k = v <;> by_cases hl : l = u <;> by_cases hl' : l = v <;>
    simp_all [twoLevelMat, eq_comm]

theorem Adjacent.ne {u v : Fin m → Fin 2} (h : Adjacent u v) : u ≠ v := by
  obtain ⟨j, hj, _⟩ := h
  intro heq
  exact hj (by rw [heq])

/-- For adjacent labels the pair is the multiply-controlled gate's pair, in one of two orders. -/
theorem adjacent_eq_update {u v : Fin m → Fin 2} (hadj : Adjacent u v) :
    ∃ j : Fin m, (u = Function.update u j 0 ∧ v = Function.update u j 1) ∨
      (v = Function.update u j 0 ∧ u = Function.update u j 1) := by
  obtain ⟨j, hj, hoff⟩ := hadj
  refine ⟨j, ?_⟩
  rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (u j) with huj | huj
  · have hvj : v j = 1 := by
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (v j) with h | h
      · exact absurd (huj.trans h.symm) hj
      · exact h
    exact Or.inl ⟨eq_update_iff.mpr ⟨fun i _ => rfl, huj⟩,
      eq_update_iff.mpr ⟨fun i hi => (hoff i hi).symm, hvj⟩⟩
  · have hvj : v j = 0 := by
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (v j) with h | h
      · exact h
      · exact absurd (huj.trans h.symm) hj
    exact Or.inr ⟨eq_update_iff.mpr ⟨fun i hi => (hoff i hi).symm, hvj⟩,
      eq_update_iff.mpr ⟨fun i _ => rfl, huj⟩⟩

/-- ★ **A two-level matrix on an adjacent pair is a multiply-controlled gate.** -/
theorem exists_ctrlGate_of_adjacent {u v : Fin m → Fin 2} (hadj : Adjacent u v) (a b c d : ℂ) :
    IsMultiCtrlGate (twoLevelMat u v a b c d) := by
  obtain ⟨j, hcase⟩ := adjacent_eq_update hadj
  rcases hcase with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · refine ⟨j, u, a, b, c, d, ?_⟩
    rw [ctrlGate_eq_twoLevelMat, ← hu, ← hv]
  · refine ⟨j, u, d, c, b, a, ?_⟩
    rw [ctrlGate_eq_twoLevelMat, ← hu, ← hv, twoLevelMat_swap_block hadj.ne]

/-- ★ The transposition of two adjacent labels is a multiply-controlled `X`. -/
theorem isMultiCtrlX_swapMat {u v : Fin m → Fin 2} (hadj : Adjacent u v) :
    IsMultiCtrlX (swapMat u v) := by
  obtain ⟨j, hcase⟩ := adjacent_eq_update hadj
  refine ⟨j, u, ?_⟩
  rcases hcase with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · rw [swapMat, ctrlGate_eq_twoLevelMat, ← hu, ← hv]
  · rw [swapMat, ctrlGate_eq_twoLevelMat, ← hu, ← hv, twoLevelMat_swap_block hadj.ne]

theorem isMultiCtrlX_mem_unitaryGroup {X : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ}
    (hX : IsMultiCtrlX X) : X ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ := by
  obtain ⟨j, pat, rfl⟩ := hX
  exact ctrlGate_mem_unitaryGroup j pat (by simp) (by simp) (by simp) (by simp)

/-! ### The Gray-code decomposition -/

theorem reverse_prod_mul_prod_of_self_inverse (L : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ))
    (h : ∀ X ∈ L, X * X = 1) : L.reverse.prod * L.prod = 1 := by
  induction L with
  | nil => simp
  | cons X L ih =>
    rw [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc, ← mul_assoc X X L.prod, h X (List.mem_cons_self ..), one_mul]
    exact ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)

/-- The recursion: walking one differing qubit at a time. -/
theorem exists_multiCtrl_sandwich_aux (N : ℕ) : ∀ (u v : Fin m → Fin 2)
    (V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ), (diffSet u v).card ≤ N → u ≠ v →
    IdOutside {u, v} V →
    ∃ (L : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ))
      (W : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ),
      (∀ X ∈ L, IsMultiCtrlX X ∧ X * X = 1) ∧ IsMultiCtrlGate W ∧
        V = L.prod * W * L.reverse.prod := by
  induction N with
  | zero =>
    intro u v V hcard huv _
    exfalso
    rw [Nat.le_zero, Finset.card_eq_zero, diffSet_eq_empty_iff] at hcard
    exact huv hcard
  | succ N ih =>
    intro u v V hcard huv hid
    by_cases hone : (diffSet u v).card = 1
    · -- already adjacent: `V` is itself a multiply-controlled gate
      refine ⟨[], V, by simp, ?_, by simp⟩
      have hVeq : V = twoLevelMat u v (V u u) (V u v) (V v u) (V v v) := by
        ext k l
        by_cases hk : k = u
        · by_cases hl : l = u
          · rw [hk, hl, twoLevelMat_apply_fst_fst]
          · by_cases hl' : l = v
            · rw [hk, hl', twoLevelMat_apply_fst_snd huv]
            · rw [twoLevelMat_apply_of_col_ne hl hl', hid k l (Or.inr (by simp [hl, hl']))]
        · by_cases hk' : k = v
          · by_cases hl : l = u
            · rw [hk', hl, twoLevelMat_apply_snd_fst huv]
            · by_cases hl' : l = v
              · rw [hk', hl', twoLevelMat_apply_snd_snd huv]
              · rw [twoLevelMat_apply_of_col_ne hl hl', hid k l (Or.inr (by simp [hl, hl']))]
          · rw [twoLevelMat_apply_of_row_ne hk hk', hid k l (Or.inl (by simp [hk, hk']))]
      rw [hVeq]
      exact exists_ctrlGate_of_adjacent (adjacent_of_diffSet_card_eq_one hone) _ _ _ _
    · -- otherwise flip one differing qubit and recurse
      have hne : (diffSet u v).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact huv (diffSet_eq_empty_iff.mp h)
      obtain ⟨j, hj⟩ := hne
      have hju : u j ≠ v j := mem_diffSet.mp hj
      set u' := Function.update u j (v j) with hu'
      have hadj : Adjacent u u' := by
        refine ⟨j, ?_, fun i hi => ?_⟩
        · rw [hu', Function.update_self]
          exact hju
        · rw [hu', Function.update_of_ne hi]
      have huu' : u ≠ u' := by
        intro h
        have hc := congrFun h j
        rw [hu', Function.update_self] at hc
        exact hju hc
      have hdiff' : diffSet u' v = (diffSet u v).erase j := by
        ext i
        rw [Finset.mem_erase, mem_diffSet]
        by_cases hi : i = j
        · rw [hi, hu', Function.update_self]
          simp
        · rw [hu', Function.update_of_ne hi, mem_diffSet]
          simp [hi]
      have hcard1 : 1 ≤ (diffSet u v).card := Finset.card_pos.mpr ⟨j, hj⟩
      have hcard' : (diffSet u' v).card ≤ N := by
        rw [hdiff', Finset.card_erase_of_mem hj]
        omega
      have hu'v : u' ≠ v := by
        intro h
        have hc : ((diffSet u v).erase j).card = 0 := by
          rw [← hdiff', diffSet_eq_empty_iff.mpr h, Finset.card_empty]
        rw [Finset.card_erase_of_mem hj] at hc
        omega
      have hidc : IdOutside {u', v} (swapMat u u' * V * swapMat u u') :=
        idOutside_swapMat_conj huu' (Ne.symm hu'v) hid
      obtain ⟨L, W, hL, hW, hVc⟩ := ih u' v _ hcard' hu'v hidc
      refine ⟨swapMat u u' :: L, W, ?_, hW, ?_⟩
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact ⟨isMultiCtrlX_swapMat hadj, swapMat_mul_self huu'⟩
        · exact hL X hX'
      · have hswap : swapMat u u' * (swapMat u u' * V * swapMat u u') * swapMat u u' = V := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, swapMat_mul_self huu', Matrix.one_mul,
            Matrix.mul_assoc, swapMat_mul_self huu', Matrix.mul_one]
        rw [← hswap, hVc, List.prod_cons, List.reverse_cons, List.prod_append, List.prod_cons,
          List.prod_nil, mul_one]
        noncomm_ring

/-- ★★ **Every two-level matrix on qubits is a Gray-code sandwich**: a list of
multiply-controlled `X`s, one multiply-controlled single-qubit gate, and the list again (each
factor being its own inverse). If the matrix is unitary so is the gate. -/
theorem exists_multiCtrl_sandwich {u v : Fin m → Fin 2} (huv : u ≠ v)
    {V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ} (hid : IdOutside {u, v} V) :
    ∃ (L : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ))
      (W : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ),
      (∀ X ∈ L, IsMultiCtrlX X ∧ X * X = 1) ∧ IsMultiCtrlGate W ∧
        V = L.prod * W * L.reverse.prod ∧
        (V ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ →
          W ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ) := by
  obtain ⟨L, W, hL, hW, hV⟩ :=
    exists_multiCtrl_sandwich_aux (diffSet u v).card u v V le_rfl huv hid
  refine ⟨L, W, hL, hW, hV, fun hVu => ?_⟩
  have hinv : L.reverse.prod * L.prod = 1 :=
    reverse_prod_mul_prod_of_self_inverse L fun X hX => (hL X hX).2
  have hLu : L.prod ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ :=
    unitaryGroup_list_prod_mem fun X hX => isMultiCtrlX_mem_unitaryGroup (hL X hX).1
  have hLru : L.reverse.prod ∈ Matrix.unitaryGroup (Fin m → Fin 2) ℂ :=
    unitaryGroup_list_prod_mem fun X hX =>
      isMultiCtrlX_mem_unitaryGroup (hL X (List.mem_reverse.mp hX)).1
  have hWeq : W = L.reverse.prod * V * L.prod := by
    rw [hV]
    calc W = L.reverse.prod * L.prod * W * (L.reverse.prod * L.prod) := by
          rw [hinv, Matrix.one_mul, Matrix.mul_one]
      _ = L.reverse.prod * (L.prod * W * L.reverse.prod) * L.prod := by noncomm_ring
  rw [hWeq]
  exact mul_mem (mul_mem hLru hVu) hLu

/-- ★ The flat form: a two-level matrix on qubits is a product of multiply-controlled gates —
the shape BACKLOG #72 consumes. -/
theorem exists_multiCtrl_list {u v : Fin m → Fin 2} (huv : u ≠ v)
    {V : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ} (hid : IdOutside {u, v} V) :
    ∃ L : List (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ),
      (∀ X ∈ L, IsMultiCtrlX X ∨ IsMultiCtrlGate X) ∧ L.prod = V := by
  obtain ⟨L, W, hL, hW, hV, _⟩ := exists_multiCtrl_sandwich huv hid
  refine ⟨L ++ (W :: L.reverse), ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact Or.inl (hL X h).1
    · rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr hW
      · exact Or.inl (hL X (List.mem_reverse.mp h')).1
  · rw [List.prod_append, List.prod_cons, hV, mul_assoc]

end MultiControlled

end QuantumInfo

end
