/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators

/-!
# Every unitary matrix is a product of two-level unitaries

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #70 and #82, part (c) of `R-005`
(`specs/magic-plan.md`, "The split").

**Glossary:** https://glossary.constraintsurfacedynamics.com/two-level-unitary/
Plain-language, CSD-role and formal statements of two-level unitaries, with this module as
the Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

A matrix is **two-level** when it agrees with the identity outside a `{i, j} × {i, j}` block
(`IsTwoLevel`, through the predicate `IdOutside s` for a general index set). Nielsen–Chuang §4.5.1:
every unitary is a product of two-level unitaries, and at most `d(d − 1)/2` of them suffice. The
proof here is Givens elimination, organised as an induction on the support:

* `IdOutside`, ★ `IdOutside.mul`, `IdOutside.mono`, `IdOutside.eq_one`, `IsTwoLevel`;
* `twoLevelMat i j a b c d` — the identity with the `2 × 2` block `!![a, b; c, d]` at `(i, j)`;
  ★ `twoLevelMat_mul` (composition **is** `2 × 2` matrix multiplication), `twoLevelMat_conjTranspose`,
  `twoLevelMat_one`, ★ `twoLevelMat_mem_unitaryGroup` (unitary exactly when the block is), and the
  action on a vector (`twoLevelMat_mulVec_apply_*`);
* `givensMat i j v` — the Givens rotation in the `(i, j)` plane that kills the `j`-component of `v`
  (★ `givensMat_mulVec_apply_snd`, and `givensMat_mulVec_apply_fst` for the value it accumulates);
* ★★ `exists_clear_column` — **a product of two-level unitaries kills any prescribed set of
  components of a vector**, leaving the rest untouched, one factor per component cleared, and with
  the pivot accumulating the *norm* of the cleared block;
* ★★ `exists_twoLevel_prod` — **every unitary is a product of two-level unitaries** (for an index
  type with at least two elements), via `exists_twoLevel_prod_of_idOutside` by induction on the
  support;
* ★★★ `exists_twoLevel_prod_length` — **Nielsen–Chuang's count: at most `d(d − 1)/2` factors**
  (BACKLOG #82). Not one factor is spent on a phase: the pivot of an elimination round holds the
  norm of the column it has just cleared, a nonnegative real, which for a unitary is exactly `1`, so
  the row and column come out of the round already in the form the induction needs. The bookkeeping
  is Pascal's rule, `(m − 1) + Nat.choose (m − 1) 2 = Nat.choose m 2`, with
  `isTwoLevel_of_idOutside_card_le_two`
  as the base case: on a block of at most two indices the matrix *is* two-level.

## Honest scope

⚠️ The count is an upper bound — which is all Nielsen–Chuang §4.5.1 asserts. No matching lower
bound is proved: nothing here says that `d(d − 1)/2` factors are *necessary*. And it counts
two-level factors, not elementary gates: the CNOT-and-single-qubit-gate count of a unitary is the
efficiency row BACKLOG #74, kept not claimed. `exists_twoLevel_prod` is retained alongside the
counted version because its consumers (the Clifford+T density of #71–#73) need no count.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.5.1;
G. H. Golub, C. F. Van Loan, *Matrix Computations* §5.1 (Givens rotations); `specs/magic-plan.md`;
`specs/BACKLOG.md` #70, #82; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace TwoLevel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Agreeing with the identity outside a block -/

/-- `U` agrees with the identity outside the block `s × s`. -/
def IdOutside (s : Finset n) (U : Matrix n n ℂ) : Prop :=
  ∀ k l, k ∉ s ∨ l ∉ s → U k l = if k = l then 1 else 0

omit [Fintype n] in
theorem IdOutside.one (s : Finset n) : IdOutside s (1 : Matrix n n ℂ) := by
  intro k l _
  rw [Matrix.one_apply]

omit [Fintype n] in
theorem IdOutside.mono {s t : Finset n} {U : Matrix n n ℂ} (hst : s ⊆ t) (h : IdOutside s U) :
    IdOutside t U := by
  intro k l hkl
  refine h k l ?_
  rcases hkl with hk | hl
  · exact Or.inl fun hks => hk (hst hks)
  · exact Or.inr fun hls => hl (hst hls)

/-- Outside its block a matrix has a single nonzero entry in each row and column, so the sum
defining a product collapses. -/
theorem IdOutside.mul {s : Finset n} {U V : Matrix n n ℂ} (hU : IdOutside s U)
    (hV : IdOutside s V) : IdOutside s (U * V) := by
  intro k l hkl
  rcases hkl with hk | hl
  · rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [hU k k (Or.inl hk), if_pos rfl, one_mul]
      exact hV k l (Or.inl hk)
    · intro m _ hmk
      rw [hU k m (Or.inl hk), if_neg (Ne.symm hmk), zero_mul]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · rw [hV l l (Or.inr hl), if_pos rfl, mul_one]
      exact hU k l (Or.inr hl)
    · intro m _ hml
      rw [hV m l (Or.inr hl), if_neg hml, mul_zero]
    · intro hl'
      exact absurd (Finset.mem_univ l) hl'

omit [Fintype n] in
theorem IdOutside.eq_one {U : Matrix n n ℂ} (h : IdOutside (∅ : Finset n) U) : U = 1 := by
  ext k l
  rw [h k l (Or.inl (by simp : k ∉ (∅ : Finset n))), Matrix.one_apply]

theorem IdOutside.list_prod {s : Finset n} {L : List (Matrix n n ℂ)}
    (h : ∀ V ∈ L, IdOutside s V) : IdOutside s L.prod := by
  induction L with
  | nil => simpa using IdOutside.one s
  | cons V L ih =>
    rw [List.prod_cons]
    exact (h V (List.mem_cons_self ..)).mul (ih fun W hW => h W (List.mem_cons_of_mem _ hW))

/-- A **two-level** matrix agrees with the identity outside a `{i, j} × {i, j}` block. -/
def IsTwoLevel (U : Matrix n n ℂ) : Prop :=
  ∃ i j : n, i ≠ j ∧ IdOutside {i, j} U

/-! ### The two-level matrices -/

/-- The identity with the `2 × 2` block `!![a, b; c, d]` inserted in the rows and columns `i`
and `j`. -/
def twoLevelMat (i j : n) (a b c d : ℂ) : Matrix n n ℂ := fun k l =>
  if k = i then (if l = i then a else if l = j then b else 0)
  else if k = j then (if l = i then c else if l = j then d else 0)
  else if k = l then 1 else 0

variable {i j : n} {a b c d : ℂ}

omit [Fintype n] in
@[simp] theorem twoLevelMat_apply_fst_fst : twoLevelMat i j a b c d i i = a := by
  simp [twoLevelMat]

omit [Fintype n] in
@[simp] theorem twoLevelMat_apply_fst_snd (hij : i ≠ j) :
    twoLevelMat i j a b c d i j = b := by
  simp [twoLevelMat, hij.symm]

omit [Fintype n] in
@[simp] theorem twoLevelMat_apply_snd_fst (hij : i ≠ j) :
    twoLevelMat i j a b c d j i = c := by
  simp [twoLevelMat, hij.symm]

omit [Fintype n] in
@[simp] theorem twoLevelMat_apply_snd_snd (hij : i ≠ j) :
    twoLevelMat i j a b c d j j = d := by
  simp [twoLevelMat, hij.symm]

omit [Fintype n] in
theorem twoLevelMat_apply_of_row_ne {k : n} (hki : k ≠ i) (hkj : k ≠ j) (l : n) :
    twoLevelMat i j a b c d k l = if k = l then 1 else 0 := by
  simp [twoLevelMat, hki, hkj]

omit [Fintype n] in
theorem twoLevelMat_apply_of_col_ne {k l : n} (hli : l ≠ i) (hlj : l ≠ j) :
    twoLevelMat i j a b c d k l = if k = l then 1 else 0 := by
  have hil : i ≠ l := Ne.symm hli
  have hjl : j ≠ l := Ne.symm hlj
  by_cases hk : k = i <;> by_cases hkj : k = j <;> simp_all [twoLevelMat, eq_comm]

omit [Fintype n] in
theorem idOutside_twoLevelMat : IdOutside {i, j} (twoLevelMat i j a b c d) := by
  intro k l hkl
  rcases hkl with hk | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact twoLevelMat_apply_of_row_ne hk.1 hk.2 l
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact twoLevelMat_apply_of_col_ne hl.1 hl.2

omit [Fintype n] in
theorem isTwoLevel_twoLevelMat (hij : i ≠ j) : IsTwoLevel (twoLevelMat i j a b c d) :=
  ⟨i, j, hij, idOutside_twoLevelMat⟩

omit [Fintype n] in
theorem twoLevelMat_one (hij : i ≠ j) : twoLevelMat i j 1 0 0 1 = (1 : Matrix n n ℂ) := by
  ext k l
  simp only [Matrix.one_apply]
  by_cases hk : k = i <;> by_cases hkj : k = j <;> by_cases hl : l = i <;> by_cases hl' : l = j <;>
    simp_all [twoLevelMat, eq_comm]

/-- A sum over the index type whose summand vanishes off `{i, j}`. -/
theorem sum_eq_pair (hij : i ≠ j) (f : n → ℂ) (h : ∀ m, m ≠ i → m ≠ j → f m = 0) :
    ∑ m, f m = f i + f j := by
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset n)), Finset.sum_pair hij]
  intro m _ hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact h m hm.1 hm.2

/-- Multiplying by a matrix supported in the `{i, j}` block collapses the sum: rows outside the
block are copied, rows inside it combine only the `i`-th and `j`-th rows of the other factor. -/
theorem mul_apply_of_idOutside_pair (hij : i ≠ j) (U V : Matrix n n ℂ)
    (hU : IdOutside ({i, j} : Finset n) U) (k l : n) :
    (U * V) k l = if k = i ∨ k = j then U k i * V i l + U k j * V j l else V k l := by
  by_cases hk : k = i ∨ k = j
  · rw [if_pos hk, Matrix.mul_apply, sum_eq_pair hij]
    intro m hmi hmj
    rw [hU k m (Or.inr (by simp [hmi, hmj])), if_neg ?_, zero_mul]
    rcases hk with rfl | rfl
    · exact fun h => hmi h.symm
    · exact fun h => hmj h.symm
  · rw [if_neg hk, Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [hU k k (Or.inl (by simp [not_or.mp hk])), if_pos rfl, one_mul]
    · intro m _ hmk
      rw [hU k m (Or.inl (by simp [not_or.mp hk])), if_neg (Ne.symm hmk), zero_mul]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'

/-- ★ **Composition of two-level matrices in the same block is `2 × 2` matrix multiplication.** -/
theorem twoLevelMat_mul (hij : i ≠ j) (a b c d a' b' c' d' : ℂ) :
    twoLevelMat i j a b c d * twoLevelMat i j a' b' c' d'
      = twoLevelMat i j (a * a' + b * c') (a * b' + b * d') (c * a' + d * c')
          (c * b' + d * d') := by
  ext k l
  rw [mul_apply_of_idOutside_pair hij _ _ idOutside_twoLevelMat k l]
  by_cases hk : k = i <;> by_cases hkj : k = j <;> by_cases hl : l = i <;> by_cases hl' : l = j <;>
    simp_all [twoLevelMat, eq_comm]

omit [Fintype n] in
theorem twoLevelMat_conjTranspose (hij : i ≠ j) (a b c d : ℂ) :
    (twoLevelMat i j a b c d)ᴴ
      = twoLevelMat i j (starRingEnd ℂ a) (starRingEnd ℂ c) (starRingEnd ℂ b)
          (starRingEnd ℂ d) := by
  ext k l
  rw [Matrix.conjTranspose_apply]
  by_cases hk : k = i <;> by_cases hkj : k = j <;> by_cases hl : l = i <;> by_cases hl' : l = j <;>
    simp_all [twoLevelMat, eq_comm]

/-- ★ A two-level matrix is unitary exactly when its `2 × 2` block is: the columns must be
orthonormal. -/
theorem twoLevelMat_mem_unitaryGroup (hij : i ≠ j) {a b c d : ℂ}
    (h1 : starRingEnd ℂ a * a + starRingEnd ℂ c * c = 1)
    (h2 : starRingEnd ℂ b * b + starRingEnd ℂ d * d = 1)
    (h3 : starRingEnd ℂ a * b + starRingEnd ℂ c * d = 0)
    (h4 : starRingEnd ℂ b * a + starRingEnd ℂ d * c = 0) :
    twoLevelMat i j a b c d ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show (twoLevelMat i j a b c d)ᴴ * twoLevelMat i j a b c d = 1
  rw [twoLevelMat_conjTranspose hij, twoLevelMat_mul hij, h1, h4, h3, h2, twoLevelMat_one hij]

/-! ### The action on a vector -/

theorem twoLevelMat_mulVec_apply_fst (hij : i ≠ j) (v : n → ℂ) :
    (twoLevelMat i j a b c d *ᵥ v) i = a * v i + b * v j := by
  rw [Matrix.mulVec, dotProduct, sum_eq_pair hij]
  · rw [twoLevelMat_apply_fst_fst, twoLevelMat_apply_fst_snd hij]
  · intro m hmi hmj
    rw [twoLevelMat_apply_of_col_ne hmi hmj, if_neg (Ne.symm hmi), zero_mul]

theorem twoLevelMat_mulVec_apply_snd (hij : i ≠ j) (v : n → ℂ) :
    (twoLevelMat i j a b c d *ᵥ v) j = c * v i + d * v j := by
  rw [Matrix.mulVec, dotProduct, sum_eq_pair hij]
  · rw [twoLevelMat_apply_snd_fst hij, twoLevelMat_apply_snd_snd hij]
  · intro m hmi hmj
    rw [twoLevelMat_apply_of_col_ne hmi hmj, if_neg (Ne.symm hmj), zero_mul]

theorem twoLevelMat_mulVec_apply_of_ne {k : n} (hki : k ≠ i) (hkj : k ≠ j) (v : n → ℂ) :
    (twoLevelMat i j a b c d *ᵥ v) k = v k := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
  · rw [twoLevelMat_apply_of_row_ne hki hkj, if_pos rfl, one_mul]
  · intro m _ hmk
    rw [twoLevelMat_apply_of_row_ne hki hkj, if_neg (Ne.symm hmk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ### The Givens rotation -/

/-- The Givens rotation in the `(i, j)` plane that kills the `j`-component of `v`. -/
noncomputable def givensMat (i j : n) (v : n → ℂ) : Matrix n n ℂ :=
  if Complex.normSq (v i) + Complex.normSq (v j) = 0 then twoLevelMat i j 1 0 0 1
  else
    twoLevelMat i j (starRingEnd ℂ (v i) / (Real.sqrt (Complex.normSq (v i) +
        Complex.normSq (v j)) : ℂ))
      (starRingEnd ℂ (v j) / (Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℂ))
      (-(v j) / (Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℂ))
      ((v i) / (Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℂ))

omit [Fintype n] in
theorem isTwoLevel_givensMat (hij : i ≠ j) (v : n → ℂ) : IsTwoLevel (givensMat i j v) := by
  rw [givensMat]
  split
  · exact isTwoLevel_twoLevelMat hij
  · exact isTwoLevel_twoLevelMat hij

omit [Fintype n] in
theorem idOutside_givensMat (v : n → ℂ) : IdOutside {i, j} (givensMat i j v) := by
  rw [givensMat]
  split
  · exact idOutside_twoLevelMat
  · exact idOutside_twoLevelMat

section Givens

variable (v : n → ℂ)

omit [Fintype n] [DecidableEq n] in
theorem normSq_add_nonneg :
    (0 : ℝ) ≤ Complex.normSq (v i) + Complex.normSq (v j) :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- In the nonzero case the radius is a nonzero complex number. -/
theorem sqrt_normSq_ne_zero (h : Complex.normSq (v i) + Complex.normSq (v j) ≠ 0) :
    ((Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < Complex.normSq (v i) + Complex.normSq (v j) :=
    lt_of_le_of_ne (normSq_add_nonneg (i := i) (j := j) v) (Ne.symm h)
  simpa using Real.sqrt_ne_zero'.mpr hpos

omit [Fintype n] [DecidableEq n] in
/-- The radius squares to the sum of the two squared moduli. -/
theorem sq_sqrt_normSq :
    (((Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℝ) : ℂ)) ^ 2
      = ((Complex.normSq (v i) : ℂ) + (Complex.normSq (v j) : ℂ)) := by
  have hs : Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j))
      * Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j))
      = Complex.normSq (v i) + Complex.normSq (v j) :=
    Real.mul_self_sqrt (normSq_add_nonneg (i := i) (j := j) v)
  rw [sq, ← Complex.ofReal_mul, hs]
  push_cast
  ring

omit [Fintype n] [DecidableEq n] in
theorem conj_sqrt_normSq :
    starRingEnd ℂ ((Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℝ) : ℂ)
      = ((Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℝ) : ℂ) :=
  Complex.conj_ofReal _

theorem givensMat_mem_unitaryGroup (hij : i ≠ j) :
    givensMat i j v ∈ Matrix.unitaryGroup n ℂ := by
  rw [givensMat]
  split
  · rw [twoLevelMat_one hij]
    exact Submonoid.one_mem _
  · rename_i h
    have hr := sqrt_normSq_ne_zero (i := i) (j := j) v h
    have hsq := sq_sqrt_normSq (i := i) (j := j) v
    refine twoLevelMat_mem_unitaryGroup hij ?_ ?_ ?_ ?_ <;>
      simp only [map_div₀, map_neg, Complex.conj_conj, conj_sqrt_normSq (i := i) (j := j) v] <;>
      field_simp
    · rw [hsq]
      simp only [mul_comm (starRingEnd ℂ (v j)) (v j), Complex.mul_conj]
    · rw [hsq]
      simp only [mul_comm (starRingEnd ℂ (v i)) (v i), Complex.mul_conj]
      ring
    · ring
    · ring

/-- ★ **The Givens rotation kills the `j`-component.** -/
theorem givensMat_mulVec_apply_snd (hij : i ≠ j) : (givensMat i j v *ᵥ v) j = 0 := by
  rw [givensMat]
  split
  · rename_i h
    have hj : Complex.normSq (v j) = 0 := by
      have h1 : (0:ℝ) ≤ Complex.normSq (v i) := Complex.normSq_nonneg _
      have h2 : (0:ℝ) ≤ Complex.normSq (v j) := Complex.normSq_nonneg _
      linarith
    rw [twoLevelMat_one hij, Matrix.one_mulVec]
    exact Complex.normSq_eq_zero.mp hj
  · rename_i h
    have hr := sqrt_normSq_ne_zero (i := i) (j := j) v h
    rw [twoLevelMat_mulVec_apply_snd hij]
    field_simp
    ring

/-- The `i`-component accumulates the radius. -/
theorem givensMat_mulVec_apply_fst (hij : i ≠ j) :
    (givensMat i j v *ᵥ v) i
      = ((Real.sqrt (Complex.normSq (v i) + Complex.normSq (v j)) : ℝ) : ℂ) := by
  rw [givensMat]
  split
  · rename_i h
    have hi : Complex.normSq (v i) = 0 := by
      have h1 : (0:ℝ) ≤ Complex.normSq (v i) := Complex.normSq_nonneg _
      have h2 : (0:ℝ) ≤ Complex.normSq (v j) := Complex.normSq_nonneg _
      linarith
    rw [twoLevelMat_one hij, Matrix.one_mulVec, h, Real.sqrt_zero]
    simpa using Complex.normSq_eq_zero.mp hi
  · rename_i h
    have hr := sqrt_normSq_ne_zero (i := i) (j := j) v h
    have hsq := sq_sqrt_normSq (i := i) (j := j) v
    rw [twoLevelMat_mulVec_apply_fst hij]
    field_simp
    rw [hsq]
    simp only [mul_comm (starRingEnd ℂ (v i)) (v i), mul_comm (starRingEnd ℂ (v j)) (v j),
      Complex.mul_conj]

theorem givensMat_mulVec_apply_of_ne {k : n} (hki : k ≠ i) (hkj : k ≠ j) :
    (givensMat i j v *ᵥ v) k = v k := by
  rw [givensMat]
  split
  · exact twoLevelMat_mulVec_apply_of_ne hki hkj v
  · exact twoLevelMat_mulVec_apply_of_ne hki hkj v

end Givens

/-! ### Clearing the components of a vector -/

/-- ★★ **A product of two-level unitaries kills any prescribed set of components of a vector**,
leaving every other component except the `i`-th untouched — one factor per component cleared, and
with the `i`-th component accumulating the *norm* of the block. That the accumulated value is a
nonnegative real is what makes the Nielsen–Chuang count tight: the pivot needs no separate
phase-fixing factor. -/
theorem exists_clear_column (i : n) (s : Finset n) (his : i ∉ s) (v : n → ℂ) :
    ∃ L : List (Matrix n n ℂ),
      (∀ V ∈ L, IsTwoLevel V ∧ V ∈ Matrix.unitaryGroup n ℂ ∧ IdOutside (insert i s) V) ∧
      L.length = s.card ∧
      (∀ k ∈ s, (L.prod *ᵥ v) k = 0) ∧ (∀ k, k ≠ i → k ∉ s → (L.prod *ᵥ v) k = v k) ∧
      Complex.normSq ((L.prod *ᵥ v) i) = ∑ k ∈ insert i s, Complex.normSq (v k) ∧
      (s.Nonempty → (L.prod *ᵥ v) i
        = ((Real.sqrt (∑ k ∈ insert i s, Complex.normSq (v k)) : ℝ) : ℂ)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, by simp, by simp, ?_, ?_, ?_⟩
    · intro k _ _
      rw [List.prod_nil, Matrix.one_mulVec]
    · rw [List.prod_nil, Matrix.one_mulVec, Finset.sum_insert (by simp), Finset.sum_empty,
        add_zero]
    · intro hne
      exact absurd hne (by simp)
  | insert j s hjs ih =>
    have hij : i ≠ j := fun h => his (by rw [h]; exact Finset.mem_insert_self j s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨L, hL, hlen, hzero, hfix, hsq, -⟩ := ih his'
    set w := L.prod *ᵥ v with hw
    have hA : (0 : ℝ) ≤ ∑ k ∈ insert i s, Complex.normSq (v k) :=
      Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
    have hsum : ∑ k ∈ insert i (insert j s), Complex.normSq (v k)
        = (∑ k ∈ insert i s, Complex.normSq (v k)) + Complex.normSq (v j) := by
      rw [show insert i (insert j s) = insert j (insert i s) by rw [Finset.insert_comm],
        Finset.sum_insert (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hij, hjs⟩)]
      ring
    have hnew : ((givensMat i j w :: L).prod *ᵥ v) i
        = ((Real.sqrt (∑ k ∈ insert i (insert j s), Complex.normSq (v k)) : ℝ) : ℂ) := by
      have hwj : w j = v j := hfix j (Ne.symm hij) hjs
      rw [List.prod_cons, ← Matrix.mulVec_mulVec, ← hw, givensMat_mulVec_apply_fst w hij, hsq,
        hwj, hsum]
    refine ⟨givensMat i j w :: L, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro V hV
      rcases List.mem_cons.mp hV with rfl | hV'
      · exact ⟨isTwoLevel_givensMat hij w, givensMat_mem_unitaryGroup w hij,
          (idOutside_givensMat w).mono (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
      · obtain ⟨h1, h2, h3⟩ := hL V hV'
        exact ⟨h1, h2, h3.mono (by
          intro x hx
          simp only [Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx'
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hx'))⟩
    · rw [List.length_cons, hlen, Finset.card_insert_of_notMem hjs]
    · intro k hk
      rw [List.prod_cons, ← Matrix.mulVec_mulVec, ← hw]
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact givensMat_mulVec_apply_snd w hij
      · have hki : k ≠ i := fun h => his' (h ▸ hk')
        have hkj : k ≠ j := fun h => hjs (h ▸ hk')
        rw [givensMat_mulVec_apply_of_ne w hki hkj]
        exact hzero k hk'
    · intro k hki hk
      have hkj : k ≠ j := fun h => hk (by rw [h]; exact Finset.mem_insert_self j s)
      have hks : k ∉ s := fun h => hk (Finset.mem_insert_of_mem h)
      rw [List.prod_cons, ← Matrix.mulVec_mulVec, ← hw,
        givensMat_mulVec_apply_of_ne w hki hkj]
      exact hfix k hki hks
    · rw [hnew, Complex.normSq_ofReal, Real.mul_self_sqrt (by
        exact Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)]
    · intro _
      exact hnew

/-! ### The decomposition -/

theorem unitaryGroup_list_prod_mem {L : List (Matrix n n ℂ)}
    (h : ∀ V ∈ L, V ∈ Matrix.unitaryGroup n ℂ) : L.prod ∈ Matrix.unitaryGroup n ℂ := by
  induction L with
  | nil => simp
  | cons V L ih =>
    rw [List.prod_cons]
    exact mul_mem (h V (List.mem_cons_self ..))
      (ih fun W hW => h W (List.mem_cons_of_mem _ hW))

omit [Fintype n] in
/-- The conjugate transpose of a two-level matrix is two-level in the same block. -/
theorem IsTwoLevel.conjTranspose {U : Matrix n n ℂ} (h : IsTwoLevel U) : IsTwoLevel Uᴴ := by
  obtain ⟨p, q, hpq, hid⟩ := h
  refine ⟨p, q, hpq, fun k l hkl => ?_⟩
  rw [Matrix.conjTranspose_apply, hid l k (Or.symm hkl)]
  by_cases hlk : l = k
  · subst hlk
    simp
  · rw [if_neg hlk, if_neg (Ne.symm hlk)]
    simp

/-- The reversed list of adjoints inverts the product of a list of unitaries. -/
theorem reverse_map_conjTranspose_prod_mul (L : List (Matrix n n ℂ))
    (h : ∀ V ∈ L, V ∈ Matrix.unitaryGroup n ℂ) :
    (L.map fun V => Vᴴ).reverse.prod * L.prod = 1 := by
  induction L with
  | nil => simp
  | cons W L ih =>
    have hWW : Wᴴ * W = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp (h W (List.mem_cons_self ..))
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      List.prod_cons, mul_assoc, ← mul_assoc Wᴴ W L.prod, hWW, one_mul]
    exact ih fun V hV => h V (List.mem_cons_of_mem _ hV)

/-- The column of a unitary matrix that has been cleared to a multiple of a basis vector has
that multiple of modulus one, and the corresponding row is cleared too. -/
theorem row_eq_of_col_eq {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (i : n)
    (hcol : ∀ k, k ≠ i → U k i = 0) :
    starRingEnd ℂ (U i i) * U i i = 1 ∧ ∀ l, l ≠ i → U i l = 0 := by
  have h : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hentry : ∀ l, starRingEnd ℂ (U i i) * U i l = if i = l then 1 else 0 := by
    intro l
    have h1 : (Uᴴ * U) i l = if i = l then 1 else 0 := by rw [h, Matrix.one_apply]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rw [Matrix.conjTranspose_apply, ← starRingEnd_apply] at h1
      exact h1
    · intro m _ hmi
      rw [Matrix.conjTranspose_apply, hcol m hmi, star_zero, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hii := hentry i
  rw [if_pos rfl] at hii
  refine ⟨hii, fun l hl => ?_⟩
  have hl' := hentry l
  rw [if_neg (Ne.symm hl)] at hl'
  have hne : starRingEnd ℂ (U i i) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hii
    exact absurd hii.symm one_ne_zero
  exact (mul_eq_zero.mp hl').resolve_left hne

/-- The squared modulus of the `i`-th column of a unitary is `1`. -/
theorem sum_normSq_col {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ k, Complex.normSq (U k i) = 1 := by
  have h1 : (Uᴴ * U) i i = 1 := by
    rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have h2 : ∀ k, Uᴴ i k * U k i = ((Complex.normSq (U k i) : ℝ) : ℂ) := by
    intro k
    rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, mul_comm, Complex.mul_conj]
  rw [Finset.sum_congr rfl fun k _ => h2 k, ← Complex.ofReal_sum] at h1
  exact_mod_cast h1

/-- A unitary that is the identity outside a block of at most two indices **is** two-level. -/
theorem isTwoLevel_of_idOutside_card_le_two (hcard : 1 < Fintype.card n) {s : Finset n}
    (hs : s.card ≤ 2) (hne : s.Nonempty) {U : Matrix n n ℂ} (hid : IdOutside s U) :
    IsTwoLevel U := by
  have hpos : 0 < s.card := Finset.card_pos.mpr hne
  rcases Nat.lt_or_ge s.card 2 with h1 | h2
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    exact ⟨i, j, Ne.symm hj, hid.mono (by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      simp [hx])⟩
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
    exact ⟨i, j, hij, hid⟩

/-- **The Nielsen–Chuang count.** The decomposition, by induction on the support: a unitary that is
the identity outside a block of `m` indices is a product of at most `(max m 2).choose 2` two-level
unitaries — `m(m − 1)/2` once `m ≥ 2`, the `max` covering only the degenerate one-index case, where
the matrix is a bare phase and costs one factor. -/
theorem exists_twoLevel_prod_of_idOutside (hcard : 1 < Fintype.card n) (s : Finset n) :
    ∀ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ → IdOutside s U →
      ∃ L : List (Matrix n n ℂ),
        (∀ V ∈ L, IsTwoLevel V ∧ V ∈ Matrix.unitaryGroup n ℂ) ∧ L.prod = U ∧
          L.length ≤ Nat.choose (max s.card 2) 2 := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro U hU hid
    rcases Nat.lt_or_ge s.card 3 with hsmall | hbig
    · -- at most two indices: `U` is itself two-level, or the identity
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨[], by simp, by rw [List.prod_nil, hid.eq_one], by simp⟩
      · refine ⟨[U], ?_, by rw [List.prod_singleton], ?_⟩
        · intro V hV
          rw [List.mem_singleton] at hV
          subst hV
          exact ⟨isTwoLevel_of_idOutside_card_le_two hcard (by omega) hne hid, hU⟩
        · rw [List.length_singleton]
          have h2 : 2 ≤ max s.card 2 := le_max_right _ _
          calc 1 = Nat.choose 2 2 := by norm_num
            _ ≤ Nat.choose (max s.card 2) 2 := Nat.choose_le_choose 2 h2
    · -- at least three: clear a column, then induct on the smaller support
      obtain ⟨i, hi⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
      have hcards : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
      obtain ⟨L₁, hL₁, hlen₁, hzero, hfix, -, hslot⟩ :=
        exists_clear_column i (s.erase i) (by simp) (fun k => U k i)
      have hins : insert i (s.erase i) = s := Finset.insert_erase hi
      set G := L₁.prod with hG
      have hGu : G ∈ Matrix.unitaryGroup n ℂ :=
        unitaryGroup_list_prod_mem fun V hV => (hL₁ V hV).2.1
      have hGid : IdOutside s G := by
        rw [← hins]
        exact IdOutside.list_prod fun V hV => (hL₁ V hV).2.2
      have hGU : G * U ∈ Matrix.unitaryGroup n ℂ := mul_mem hGu hU
      have hcolmul : ∀ k, (G * U) k i = (G *ᵥ fun m => U m i) k := by
        intro k
        rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have hcol : ∀ k, k ≠ i → (G * U) k i = 0 := by
        intro k hk
        rw [hcolmul]
        by_cases hks : k ∈ s.erase i
        · exact hzero k hks
        · have hkns : k ∉ s := fun h => hks (Finset.mem_erase.mpr ⟨hk, h⟩)
          rw [hfix k hk hks, hid k i (Or.inl hkns), if_neg hk]
      obtain ⟨-, hrow⟩ := row_eq_of_col_eq hGU i hcol
      -- the pivot is the norm of the column, which is `1`
      have hsumcol : ∑ k ∈ insert i (s.erase i), Complex.normSq (U k i) = 1 := by
        rw [hins, ← sum_normSq_col hU i]
        refine Finset.sum_subset (Finset.subset_univ s) ?_
        intro k _ hks
        have hki : k ≠ i := fun h => hks (h ▸ hi)
        rw [hid k i (Or.inl hks), if_neg hki, Complex.normSq_zero]
      have hdiag : (G * U) i i = 1 := by
        rw [hcolmul, hslot (Finset.card_pos.mp (by omega)), hsumcol, Real.sqrt_one,
          Complex.ofReal_one]
      have hid' : IdOutside (s.erase i) (G * U) := by
        intro k l hkl
        by_cases hk : k = i
        · subst hk
          by_cases hl : l = k
          · rw [hl, hdiag, if_pos rfl]
          · rw [hrow l hl, if_neg (fun h => hl h.symm)]
        · by_cases hl : l = i
          · subst hl
            rw [hcol k hk, if_neg hk]
          · refine (hGid.mul hid) k l ?_
            rcases hkl with hk' | hl'
            · exact Or.inl fun hks => hk' (Finset.mem_erase.mpr ⟨hk, hks⟩)
            · exact Or.inr fun hls => hl' (Finset.mem_erase.mpr ⟨hl, hls⟩)
      obtain ⟨L₂, hL₂, hprod, hlen₂⟩ := ih (s.erase i) (Finset.erase_ssubset hi) (G * U) hGU hid'
      refine ⟨(L₁.map fun V => Vᴴ).reverse ++ L₂, ?_, ?_, ?_⟩
      · intro V hV
        rcases List.mem_append.mp hV with hV' | hV'
        · rw [List.mem_reverse, List.mem_map] at hV'
          obtain ⟨W, hW, rfl⟩ := hV'
          obtain ⟨h1, h2, -⟩ := hL₁ W hW
          refine ⟨h1.conjTranspose, ?_⟩
          rw [← Matrix.star_eq_conjTranspose]
          exact Unitary.star_mem h2
        · exact hL₂ V hV'
      · rw [List.prod_append, hprod, ← mul_assoc, hG,
          reverse_map_conjTranspose_prod_mul L₁ (fun V hV => (hL₁ V hV).2.1), one_mul]
      · -- `(m − 1) + (m − 1)(m − 2)/2 = m(m − 1)/2`, as binomial coefficients
        have hlen : ((L₁.map fun V => Vᴴ).reverse ++ L₂).length = (s.card - 1) + L₂.length := by
          rw [List.length_append, List.length_reverse, List.length_map, hlen₁, hcards]
        have hmax₂ : max (s.erase i).card 2 = (s.card - 1) := by
          rw [hcards]
          exact max_eq_left (by omega)
        have hmax : max s.card 2 = s.card := max_eq_left (by omega)
        have hchoose : Nat.choose s.card 2 = (s.card - 1) + Nat.choose (s.card - 1) 2 := by
          obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
          rw [hk, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel]
        rw [hlen, hmax, hchoose]
        exact Nat.add_le_add_left (by rw [← hmax₂]; exact hlen₂) _

/-- ★★ **Every unitary matrix is a product of two-level unitaries** (Nielsen–Chuang §4.5.1), for
an index type with at least two elements. -/
theorem exists_twoLevel_prod (hcard : 1 < Fintype.card n) (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ∃ L : List (Matrix n n ℂ),
      (∀ V ∈ L, IsTwoLevel V ∧ V ∈ Matrix.unitaryGroup n ℂ) ∧ L.prod = U := by
  obtain ⟨L, hL, hprod, -⟩ := exists_twoLevel_prod_of_idOutside hcard Finset.univ U hU
    fun k l h => by rcases h with h | h <;> exact absurd (Finset.mem_univ _) h
  exact ⟨L, hL, hprod⟩

/-- ★★★ **The Nielsen–Chuang bound: `d(d − 1)/2` two-level factors suffice.** Every `d × d` unitary
(`d ≥ 2`) is a product of at most `d(d − 1)/2` two-level unitaries — the count of §4.5.1, tight for
`d = 2`. The construction is Givens elimination, and the reason no factor is wasted on phases is
`exists_clear_column`: the pivot accumulates the *norm* of the column, which for a unitary is
exactly `1`. -/
theorem exists_twoLevel_prod_length (hcard : 1 < Fintype.card n) (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ∃ L : List (Matrix n n ℂ),
      (∀ V ∈ L, IsTwoLevel V ∧ V ∈ Matrix.unitaryGroup n ℂ) ∧ L.prod = U ∧
        L.length ≤ Fintype.card n * (Fintype.card n - 1) / 2 := by
  obtain ⟨L, hL, hprod, hlen⟩ := exists_twoLevel_prod_of_idOutside hcard Finset.univ U hU
    fun k l h => by rcases h with h | h <;> exact absurd (Finset.mem_univ _) h
  refine ⟨L, hL, hprod, ?_⟩
  rw [Finset.card_univ] at hlen
  rwa [max_eq_left (by omega : 2 ≤ Fintype.card n), Nat.choose_two_right] at hlen

end TwoLevel

end QuantumInfo

end
