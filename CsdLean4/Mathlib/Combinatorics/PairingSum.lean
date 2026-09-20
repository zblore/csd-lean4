/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The pairing sum over perfect matchings of `Fin m`

**Category:** 1-Mathlib (CSD-free; staged for upstream).

A **perfect matching** of `Fin m` is a fixed-point-free involution `σ : Fin m → Fin m`; its pairs
are `{i, σ i}`. The **pairing sum** of a weight `c : Fin m → Fin m → R` is the sum over perfect
matchings of the product over pairs, each pair `{i, σ i}` with `i < σ i` weighted `c i (σ i)` —
the combinatorial skeleton of Wick's theorem (the hafnian when `c` is symmetric).

* `IsPerfectMatching σ` — `∀ i, σ (σ i) = i ∧ σ i ≠ i`; `pairingSum c` — the sum over
  `{σ // IsPerfectMatching σ}` of `∏ i, if i < σ i then c i (σ i) else 1`;
* `pairingSum_zero` (`m = 0`: the empty matching, value `1`), `pairingSum_one` (`m = 1`: no
  matching, value `0`);
* ★ `pairingSum_succ_succ` — **the first-contraction recursion**: for `m = n + 2`,
  `pairingSum c = ∑ j : Fin (n + 1), c 0 j.succ · pairingSum (c ∘ emb j)`, where
  `emb j : Fin n ↪ Fin (n + 2)` is the order embedding onto the complement of `{0, j.succ}`
  (`emb j a = (j.succAbove a).succ`). A matching of `Fin (n + 2)` is the pair `{0, j.succ}`
  together with a matching of the rest, and the weights multiply (`glue`, the bijection
  `glue_bijective`);
* `pairingSum_cast` — transport along `m = m'`;
* ★ `card_isPerfectMatching_even` / `card_isPerfectMatching_odd` — the number of perfect matchings
  of `Fin (2n)` is `(2n − 1)‼`, of `Fin (2n + 1)` zero: the pairing sum of the constant weight `1`.

References: G. C. Wick, *The evaluation of the collision matrix*, Phys. Rev. 80, 268 (1950)
(the pairing sum); `CV/WickTime.lean` (`wickSum`, the same recursion on words of the lattice
field, and `wickSum_eq_pairingSum`); `specs/BACKLOG.md` #36(b)(iv′); `specs/future-work.md`.
-/

@[expose] public section

open Finset
open scoped Nat

namespace Fin

variable {m : ℕ}

/-! ### Perfect matchings -/

/-- A **perfect matching** of `Fin m`: a fixed-point-free involution. -/
def IsPerfectMatching (σ : Fin m → Fin m) : Prop := ∀ i, σ (σ i) = i ∧ σ i ≠ i

instance : DecidablePred (IsPerfectMatching (m := m)) := fun σ =>
  inferInstanceAs (Decidable (∀ i, σ (σ i) = i ∧ σ i ≠ i))

/-- **The pairing sum** of a weight `c`: over perfect matchings `σ`, the product over the pairs
`{i, σ i}`, `i < σ i`, of `c i (σ i)`. -/
def pairingSum {R : Type*} [CommSemiring R] (c : Fin m → Fin m → R) : R :=
  ∑ σ : {σ : Fin m → Fin m // IsPerfectMatching σ}, ∏ i, if i < σ.1 i then c i (σ.1 i) else 1

section Small

variable {R : Type*} [CommSemiring R]

instance instUniqueSubtypeIsPerfectMatchingZero :
    Unique {σ : Fin 0 → Fin 0 // IsPerfectMatching σ} where
  default := ⟨fun i => i.elim0, fun i => i.elim0⟩
  uniq _ := Subtype.ext (funext fun i => i.elim0)

instance instIsEmptySubtypeIsPerfectMatchingOne :
    IsEmpty {σ : Fin 1 → Fin 1 // IsPerfectMatching σ} :=
  ⟨fun ⟨_, h⟩ => (h 0).2 (Subsingleton.elim _ _)⟩

/-- `Fin 0` has one perfect matching, the empty one: the pairing sum is `1`. -/
theorem pairingSum_zero (c : Fin 0 → Fin 0 → R) : pairingSum c = 1 := by
  rw [pairingSum, Fintype.sum_unique]
  exact Finset.prod_of_isEmpty _

/-- `Fin 1` has no perfect matching: the pairing sum is `0`. -/
theorem pairingSum_one (c : Fin 1 → Fin 1 → R) : pairingSum c = 0 := by
  rw [pairingSum]
  exact Fintype.sum_empty _

end Small

/-! ### The first-contraction recursion -/

section Recursion

variable {n : ℕ}

/-- The order embedding of `Fin n` onto the complement of `{0, j.succ}` in `Fin (n + 2)`. -/
def emb (j : Fin (n + 1)) (a : Fin n) : Fin (n + 2) := (j.succAbove a).succ

theorem emb_ne_zero (j : Fin (n + 1)) (a : Fin n) : emb j a ≠ 0 := Fin.succ_ne_zero _

theorem emb_ne_succ (j : Fin (n + 1)) (a : Fin n) : emb j a ≠ j.succ :=
  fun h => Fin.succAbove_ne j a (Fin.succ_injective _ h)

theorem emb_injective (j : Fin (n + 1)) : Function.Injective (emb j) :=
  fun _ _ h => Fin.succAbove_right_injective (Fin.succ_injective _ h)

theorem emb_lt_emb_iff (j : Fin (n + 1)) {a b : Fin n} : emb j a < emb j b ↔ a < b := by
  rw [emb, emb, Fin.succ_lt_succ_iff, Fin.succAbove_lt_succAbove_iff]

/-- Every element of `Fin (n + 2)` other than `0` and `j.succ` is `emb j a` for a unique `a`. -/
theorem exists_emb_eq (j : Fin (n + 1)) {i : Fin (n + 2)} (h0 : i ≠ 0) (hj : i ≠ j.succ) :
    ∃ a, emb j a = i := by
  obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero h0
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (fun h : i' = j => hj (by rw [h]))
  exact ⟨a, by rw [emb, ha]⟩

/-- **Gluing** the pair `{0, j.succ}` onto a matching `τ` of the rest. -/
def glue (j : Fin (n + 1)) (τ : Fin n → Fin n) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons j.succ (Fin.insertNth j 0 fun a => emb j (τ a))

@[simp] theorem glue_zero (j : Fin (n + 1)) (τ : Fin n → Fin n) : glue j τ 0 = j.succ :=
  Fin.cons_zero _ _

@[simp] theorem glue_succ_self (j : Fin (n + 1)) (τ : Fin n → Fin n) : glue j τ j.succ = 0 := by
  rw [glue, Fin.cons_succ, Fin.insertNth_apply_same]

@[simp] theorem glue_emb (j : Fin (n + 1)) (τ : Fin n → Fin n) (a : Fin n) :
    glue j τ (emb j a) = emb j (τ a) := by
  rw [glue, emb, Fin.cons_succ, Fin.insertNth_apply_succAbove]

/-- Case analysis on `Fin (n + 2)`: `0`, `j.succ`, or `emb j a`. -/
theorem cases_emb (j : Fin (n + 1)) {p : Fin (n + 2) → Prop} (h0 : p 0) (hj : p j.succ)
    (he : ∀ a, p (emb j a)) : ∀ i, p i := by
  intro i
  by_cases hi0 : i = 0
  · rw [hi0]; exact h0
  · by_cases hij : i = j.succ
    · rw [hij]; exact hj
    · obtain ⟨a, rfl⟩ := exists_emb_eq j hi0 hij
      exact he a

theorem glue_isPerfectMatching (j : Fin (n + 1)) {τ : Fin n → Fin n}
    (hτ : IsPerfectMatching τ) : IsPerfectMatching (glue j τ) := by
  refine cases_emb j ?_ ?_ ?_
  · exact ⟨by rw [glue_zero, glue_succ_self], by rw [glue_zero]; exact Fin.succ_ne_zero _⟩
  · exact ⟨by rw [glue_succ_self, glue_zero], by rw [glue_succ_self]; exact (Fin.succ_ne_zero _).symm⟩
  · intro a
    refine ⟨by rw [glue_emb, glue_emb, (hτ a).1], ?_⟩
    rw [glue_emb]
    exact fun h => (hτ a).2 (emb_injective j h)

/-- The gluing map from pairs (partner of `0`, matching of the rest) to matchings. -/
def glueMap (j : Fin (n + 1)) : {τ : Fin n → Fin n // IsPerfectMatching τ} →
    {σ : Fin (n + 2) → Fin (n + 2) // IsPerfectMatching σ} :=
  fun τ => ⟨glue j τ.1, glue_isPerfectMatching j τ.2⟩

/-- The gluing map on the sigma type. -/
def glueSigma : (Σ _j : Fin (n + 1), {τ : Fin n → Fin n // IsPerfectMatching τ}) →
    {σ : Fin (n + 2) → Fin (n + 2) // IsPerfectMatching σ} :=
  fun p => glueMap p.1 p.2

theorem glueSigma_injective : Function.Injective (glueSigma (n := n)) := by
  rintro ⟨j, τ, hτ⟩ ⟨j', τ', hτ'⟩ h
  have h' : glue j τ = glue j' τ' := congrArg Subtype.val h
  have hj : j = j' := by
    have := congrFun h' 0
    rw [glue_zero, glue_zero] at this
    exact Fin.succ_injective _ this
  subst hj
  have hτ : τ = τ' := funext fun a => by
    have := congrFun h' (emb j a)
    rw [glue_emb, glue_emb] at this
    exact emb_injective j this
  subst hτ
  rfl

theorem glueSigma_surjective : Function.Surjective (glueSigma (n := n)) := by
  rintro ⟨σ, hσ⟩
  have h0 : σ 0 ≠ 0 := (hσ 0).2
  obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero h0
  -- the image of `emb j` is stable under `σ`
  have hne0 : ∀ a, σ (emb j a) ≠ 0 := fun a h => by
    have := (hσ (emb j a)).1
    rw [h, hj] at this
    exact emb_ne_succ j a this.symm
  have hnej : ∀ a, σ (emb j a) ≠ j.succ := fun a h => by
    have := (hσ (emb j a)).1
    rw [h, ← hj, (hσ 0).1] at this
    exact emb_ne_zero j a this.symm
  choose τ hτ using fun a => exists_emb_eq j (hne0 a) (hnej a)
  have hτm : IsPerfectMatching τ := fun a => by
    refine ⟨emb_injective j ?_, fun h => (hσ (emb j a)).2 ?_⟩
    · rw [hτ, hτ, (hσ _).1]
    · rw [← hτ, h]
  refine ⟨⟨j, ⟨τ, hτm⟩⟩, Subtype.ext (funext (cases_emb j ?_ ?_ ?_))⟩
  · show glue j τ 0 = σ 0
    rw [glue_zero, hj]
  · show glue j τ j.succ = σ j.succ
    rw [glue_succ_self, ← hj, (hσ 0).1]
  · intro a
    show glue j τ (emb j a) = σ (emb j a)
    rw [glue_emb, hτ]

theorem glueSigma_bijective : Function.Bijective (glueSigma (n := n)) :=
  ⟨glueSigma_injective, glueSigma_surjective⟩

variable {R : Type*} [CommSemiring R]

/-- The weight of a glued matching: the pair `{0, j.succ}` times the weight of the rest. -/
theorem prod_glue (c : Fin (n + 2) → Fin (n + 2) → R) (j : Fin (n + 1)) (τ : Fin n → Fin n) :
    (∏ i, if i < glue j τ i then c i (glue j τ i) else 1)
      = c 0 j.succ * ∏ a, if a < τ a then c (emb j a) (emb j (τ a)) else 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succAbove _ j, glue_zero, if_pos (Fin.succ_pos j),
    glue_succ_self, if_neg (Fin.not_lt_zero _), one_mul]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show (j.succAbove a).succ = emb j a from rfl, glue_emb]
  simp only [emb_lt_emb_iff]

/-- ★ **The first-contraction recursion.** A perfect matching of `Fin (n + 2)` is the pair
`{0, j.succ}` together with a perfect matching of the complement, and the weights multiply. -/
theorem pairingSum_succ_succ (c : Fin (n + 2) → Fin (n + 2) → R) :
    pairingSum c = ∑ j : Fin (n + 1), c 0 j.succ * pairingSum fun a b => c (emb j a) (emb j b) := by
  rw [pairingSum, ← Fintype.sum_equiv (Equiv.ofBijective _ glueSigma_bijective) _ _ fun _ => rfl,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairingSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact prod_glue c j τ.1

end Recursion

/-! ### Transport and counting -/

/-- Transport of the pairing sum along `m = m'`. -/
theorem pairingSum_cast {R : Type*} [CommSemiring R] {m m' : ℕ} (h : m = m')
    (c : Fin m' → Fin m' → R) :
    pairingSum (fun a b : Fin m => c (Fin.cast h a) (Fin.cast h b)) = pairingSum c := by
  subst h
  rfl

/-- The pairing sum of the constant weight `1` counts the perfect matchings. -/
theorem pairingSum_one_eq_card (m : ℕ) :
    pairingSum (fun _ _ : Fin m => (1 : ℕ))
      = Fintype.card {σ : Fin m → Fin m // IsPerfectMatching σ} := by
  rw [pairingSum, Fintype.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun _ _ => by simp

/-- ★ **`Fin (2n)` has `(2n − 1)‼` perfect matchings.** -/
theorem card_isPerfectMatching_even (n : ℕ) :
    Fintype.card {σ : Fin (2 * n) → Fin (2 * n) // IsPerfectMatching σ} = (2 * n - 1)‼ := by
  induction n with
  | zero =>
    rw [← pairingSum_one_eq_card]
    exact pairingSum_zero _
  | succ n ih =>
    rw [← pairingSum_one_eq_card, show 2 * (n + 1) = 2 * n + 2 from by ring,
      pairingSum_succ_succ]
    simp only [one_mul, pairingSum_one_eq_card, ih, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    rw [show 2 * n + 2 - 1 = 2 * n + 1 from by omega, Nat.doubleFactorial_add_one]

/-- **`Fin (2n + 1)` has no perfect matching.** -/
theorem card_isPerfectMatching_odd (n : ℕ) :
    Fintype.card {σ : Fin (2 * n + 1) → Fin (2 * n + 1) // IsPerfectMatching σ} = 0 := by
  induction n with
  | zero =>
    show Fintype.card {σ : Fin 1 → Fin 1 // IsPerfectMatching σ} = 0
    exact Fintype.card_eq_zero
  | succ n ih =>
    rw [← pairingSum_one_eq_card, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring,
      pairingSum_succ_succ]
    simp only [one_mul, pairingSum_one_eq_card, ih, Finset.sum_const_zero]

end Fin
