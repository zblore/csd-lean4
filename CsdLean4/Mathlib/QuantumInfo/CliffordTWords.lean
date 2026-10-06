/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.CliffordTNet

/-!
# Clifford+T as words: a length function, and the `5^n` half of Solovay–Kitaev

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #117, out of #115's split.

#115 proved the Solovay–Kitaev *error* bookkeeping and found that the *length* half needs something
the corpus did not have: `cliffordT` is `Submonoid.closure {H, T}`, a set of **matrices**, with no
notion of how many gates an element costs, and #113's net is a `Finset` of matrices rather than of
words. This file supplies the missing cost structure.

## The cost model, stated rather than inherited

The letters are `H`, `T` and `T⁻¹` — three, not two. #115's finding was that the exponent quoted for
Solovay–Kitaev is a **choice of cost model**: the recursion inverts its two factors, and over the
letters `{H, T}` alone a shortest word for `T⁻¹` is `T⁷`, so a level costs `1+1+7+7+1 = 17` rather
than `5` and the exponent becomes `log 17 / log(3/2) ≈ 6.99`. Counting `T⁻¹` as a letter gives `5` and
the literature's `≈ 3.97`, and ★★ `mem_cliffordT_iff_exists_word` shows the price is **nothing**: the
three letters generate exactly the submonoid the two do, because `T⁻¹ = T⁷` was already there. So the
inverse-closed model is free, and it is the one used here.

## What is proved

* `ctGen`, `ctEval` — the three generators and the evaluation of a word `List (Fin 3)` as a product
  of gates, with ★ `ctEval_mem_cliffordT`: every word lands in `cliffordT`;
* ★★ `mem_cliffordT_iff_exists_word` — **the words are a faithful cost model**: the values of words
  are exactly `cliffordT`, so no element is unreachable and none is cheaper than its words;
* `ctInvWord` with ★★ `length_ctInvWord` and ★★ `ctEval_ctInvWord` — **inverses are free**: reversing
  a word and flipping each letter gives the inverse at *the same length*. This is the fact the `5` in
  `5^n` rests on, and the reason the cost model matters;
* ★★★ `exists_word_net` — **#113's net as words**: for every `ε > 0` a `Finset` of words, all of
  length at most some `ℓ₀`, whose values come within `ε` of every determinant-one unitary;
* `skWords` with ★★★ `length_le_of_mem_skWords` — **the length recursion**: the level-`n` words of
  the Solovay–Kitaev shape have length at most `5^n · ℓ₀`, by induction. With #115's
  `C²ε_n ≤ (C²ε₀)^{(3/2)^n}` this is the pair #116 needs.

## Honest scope

⚠️ **`skWords` is the *shape* of the recursion, not the algorithm.** It is the set of words of the
form `v w v⁻¹ w⁻¹ a` with all five parts at the previous level — which is what the recursion
produces — and the theorem bounds their length. It does **not** say which element of `skWords n`
approximates a given `U`; that pairing is #115's error estimate applied to #114's decomposition, and
joining the two quantitatively is #116.

⚠️ **The length bound is an inequality, not a count.** `5^n · ℓ₀` bounds the words this shape
produces; nothing here claims it is attained, or that these are the shortest words for their values.

⚠️ **Nothing about `ε₀`'s size.** `exists_word_net` inherits #113's existence-only net: `ℓ₀` is
whatever the compactness argument produced, with no bound in terms of `ε₀`.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
§5 (the gate count); `CliffordTNet.lean` (#113), `SolovayKitaevStep.lean` (#115),
`CliffordTDensity.lean` (`cliffordT`, `tGateM_pow_eight`, `hGateM_mul_self`);
`specs/BACKLOG.md` #117, #115, #113, #116, #74.
-/

@[expose] public section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace QuantumInfo.SU2

open CliffordT

/-! ### The three letters -/

/-- The generating letters: `H`, `T` and `T⁻¹ = T⁷`. Three rather than two, which is #115's cost
model made explicit. -/
noncomputable def ctGen : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![hGateM, tGateM, tGateM ^ 7]

/-- The letter-level inverse: `H` is its own, and `T` and `T⁻¹` swap. -/
def ctInvLetter : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Evaluation of a word as a product of gates. -/
noncomputable def ctEval (w : List (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ := (w.map ctGen).prod

@[simp] theorem ctEval_nil : ctEval [] = 1 := rfl

theorem ctEval_cons (x : Fin 3) (w : List (Fin 3)) :
    ctEval (x :: w) = ctGen x * ctEval w := by
  simp [ctEval]

theorem ctEval_append (v w : List (Fin 3)) : ctEval (v ++ w) = ctEval v * ctEval w := by
  simp [ctEval, List.prod_append]

theorem ctGen_mem_cliffordT (i : Fin 3) : ctGen i ∈ cliffordT := by
  fin_cases i
  · simpa [ctGen] using hGateM_mem
  · simpa [ctGen] using tGateM_mem
  · simpa [ctGen] using pow_mem tGateM_mem 7

/-- ★ **Every word lands in `cliffordT`.** -/
theorem ctEval_mem_cliffordT (w : List (Fin 3)) : ctEval w ∈ cliffordT := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      rw [ctEval_cons]
      exact mul_mem (ctGen_mem_cliffordT x) ih

/-- The submonoid of word values. -/
noncomputable def ctValues : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {A | ∃ w, ctEval w = A}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro A B ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v ++ w, by rw [ctEval_append, hv, hw]⟩

/-- ★★ **The words are a faithful cost model**: their values are exactly `cliffordT`. Adding `T⁻¹` as
a letter costs no generality, because `T⁻¹ = T⁷` was already in the submonoid generated by `H` and
`T` — so the inverse-closed cost model is free. -/
theorem mem_cliffordT_iff_exists_word {A : Matrix (Fin 2) (Fin 2) ℂ} :
    A ∈ cliffordT ↔ ∃ w, ctEval w = A := by
  constructor
  · intro hA
    have hle : cliffordT ≤ ctValues := by
      rw [cliffordT, Submonoid.closure_le]
      intro B hB
      rcases hB with h | h
      · exact ⟨[0], by rw [ctEval_cons, ctEval_nil, mul_one]; simpa [ctGen] using h.symm⟩
      · refine ⟨[1], ?_⟩
        simp only [Set.mem_singleton_iff] at h
        rw [ctEval_cons, ctEval_nil, mul_one, h]
        simp [ctGen]
    exact hle hA
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact ctEval_mem_cliffordT w

/-! ### Inverses are free -/

/-- The inverse of a word: reverse it and flip each letter. -/
def ctInvWord (w : List (Fin 3)) : List (Fin 3) := (w.map ctInvLetter).reverse

/-- ★★ **Inverting a word does not lengthen it.** This is what the `5` in `5^n` rests on: the
recursion uses two factors and their two inverses, and in this alphabet an inverse is the same
length. -/
@[simp] theorem length_ctInvWord (w : List (Fin 3)) : (ctInvWord w).length = w.length := by
  simp [ctInvWord]

theorem ctGen_invLetter_mul (i : Fin 3) : ctGen (ctInvLetter i) * ctGen i = 1 := by
  fin_cases i
  · simpa [ctGen, ctInvLetter] using hGateM_mul_self
  · have h : tGateM ^ 7 * tGateM = tGateM ^ 8 := by rw [← pow_succ]
    simpa [ctGen, ctInvLetter] using h.trans tGateM_pow_eight
  · have h : tGateM * tGateM ^ 7 = tGateM ^ 8 := by rw [← pow_succ']
    simpa [ctGen, ctInvLetter] using h.trans tGateM_pow_eight

theorem ctInvWord_cons (x : Fin 3) (w : List (Fin 3)) :
    ctInvWord (x :: w) = ctInvWord w ++ [ctInvLetter x] := by
  simp [ctInvWord]

/-- ★★ **The inverse word evaluates to the inverse gate.** -/
theorem ctEval_ctInvWord (w : List (Fin 3)) : ctEval (ctInvWord w) * ctEval w = 1 := by
  induction w with
  | nil => simp [ctInvWord]
  | cons x xs ih =>
      rw [ctInvWord_cons, ctEval_append, ctEval_cons, ctEval_cons, ctEval_nil, mul_one]
      calc ctEval (ctInvWord xs) * ctGen (ctInvLetter x) * (ctGen x * ctEval xs)
          = ctEval (ctInvWord xs) * (ctGen (ctInvLetter x) * ctGen x) * ctEval xs := by
            noncomm_ring
        _ = 1 := by rw [ctGen_invLetter_mul, mul_one, ih]

/-! ### The net as words -/

open Classical in
/-- A word for a given matrix, when it has one. -/
noncomputable def wordOf (A : Matrix (Fin 2) (Fin 2) ℂ) : List (Fin 3) :=
  if h : ∃ w, ctEval w = A then h.choose else []

theorem ctEval_wordOf {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ cliffordT) :
    ctEval (wordOf A) = A := by
  have hex : ∃ w, ctEval w = A := mem_cliffordT_iff_exists_word.1 hA
  rw [wordOf, dif_pos hex]
  exact hex.choose_spec

/-- ★★★ **#113's net, as words with a length bound.** For every `ε > 0` there are finitely many
Clifford+T **words**, none longer than some `ℓ₀`, whose values come within `ε` of every
determinant-one unitary. This is the `ℓ₀` the recursion starts from. -/
theorem exists_word_net {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset (List (Fin 3))) (ℓ₀ : ℕ),
      (∀ w ∈ F, w.length ≤ ℓ₀) ∧
      ∀ U ∈ su2Set, ∃ w ∈ F, dist U (ctEval w) < ε := by
  classical
  obtain ⟨F₀, hF₀mem, hF₀net⟩ := exists_finite_cliffordT_net hε
  refine ⟨F₀.image wordOf, (F₀.image wordOf).sup List.length, ?_, ?_⟩
  · intro w hw
    exact Finset.le_sup hw
  · intro U hU
    obtain ⟨A, hA, hdist⟩ := hF₀net U hU
    refine ⟨wordOf A, Finset.mem_image_of_mem _ hA, ?_⟩
    rwa [ctEval_wordOf (hF₀mem A hA)]

/-! ### The length recursion -/

/-- The words the Solovay–Kitaev recursion produces: at each level, a group commutator of two
previous-level words followed by a previous-level word. -/
def skWords (F : Finset (List (Fin 3))) : ℕ → Set (List (Fin 3))
  | 0 => ↑F
  | n + 1 => {u | ∃ v ∈ skWords F n, ∃ w ∈ skWords F n, ∃ a ∈ skWords F n,
      u = v ++ w ++ ctInvWord v ++ ctInvWord w ++ a}

/-- ★★★ **The length recursion**: a level-`n` word is at most `5^n · ℓ₀` letters long. Five parts per
level, and inverting costs nothing (`length_ctInvWord`), so the factor is exactly `5`.

With #115's `C²·ε_n ≤ (C²·ε_0)^{(3/2)^n}` this is the pair #116 turns into `O(log^c(1/ε))`. -/
theorem length_le_of_mem_skWords {F : Finset (List (Fin 3))} {ℓ₀ : ℕ}
    (hF : ∀ w ∈ F, w.length ≤ ℓ₀) (n : ℕ) :
    ∀ u ∈ skWords F n, u.length ≤ 5 ^ n * ℓ₀ := by
  induction n with
  | zero =>
      intro u hu
      simpa using hF u hu
  | succ n ih =>
      rintro u ⟨v, hv, w, hw, a, ha, rfl⟩
      have hv' := ih v hv
      have hw' := ih w hw
      have ha' := ih a ha
      have hlen : (v ++ w ++ ctInvWord v ++ ctInvWord w ++ a).length
          = v.length + w.length + v.length + w.length + a.length := by
        simp [length_ctInvWord]
        ring
      rw [hlen]
      calc v.length + w.length + v.length + w.length + a.length
          ≤ 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hv' hw') hv') hw') ha'
        _ = 5 ^ (n + 1) * ℓ₀ := by ring

/-- ★ **And every level-`n` word still evaluates into `cliffordT`.** -/
theorem ctEval_mem_cliffordT_of_mem_skWords {F : Finset (List (Fin 3))} (n : ℕ) :
    ∀ u ∈ skWords F n, ctEval u ∈ cliffordT := fun u _ => ctEval_mem_cliffordT u

end QuantumInfo.SU2

end
