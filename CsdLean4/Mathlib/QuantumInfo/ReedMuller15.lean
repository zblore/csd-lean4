/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset

/-!
# The combinatorics of the `[[15, 1, 3]]` quantum Reed–Muller code

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #75, part (a) of `R-004`
(`specs/magic-plan.md`, "The split").

The `X`-stabilisers of the `[[15, 1, 3]]` code are the four rows of the `4 × 15` matrix `H` whose
columns are the nonzero vectors of `𝔽₂⁴` (`col j` = the binary digits of `j + 1`): the punctured
simplex code `[15, 4]`. A `Z`-error pattern `e ∈ 𝔽₂¹⁵` is **undetected** by the `X`-checks iff
`H e = 0`, i.e. `e` lies in the dual, the `[15, 11]` Hamming code.

* `col`, `col_ne_zero`, `col_injective` — the columns are nonzero and distinct;
* `syndrome e = H e`, `weight e`, `support e`, `ind S` (the indicator of a set of qubits);
* `syndrome_ne_zero_of_weight_one`, `syndrome_ne_zero_of_weight_two` — **no undetected pattern
  of weight `1` or `2`** (columns nonzero and distinct);
* ★ `card_undetected_weight_three` — **exactly `35` undetected patterns of weight `3`**
  (the triples `{a, b, a + b}` of nonzero vectors: the lines of `PG(3, 2)`), through the bijection
  with 3-subsets and a finite check (`card_undetectedTriples`, `decide`);
* ★ `dotp_add_one` — **an undetected pattern of odd weight acts as the logical `Z̄`**: on the
  coset `x + 𝟙` of a codeword `x` the pairing `e · (x + 𝟙)` is `e · x + |e|`, so a `Z`-pattern with
  `e · x = 0` on the `X`-stabiliser code picks up the sign `(−1)^{|e|}` on the logical `1̄`;
* ★ `card_undetected` — **the Hamming code has `2¹¹` words**: `syndrome` is surjective
  (`syndrome_preimage`), so its kernel has dimension `11`.

## Honest scope

⚠️ Classical combinatorics only: the quantum statements (transversal `T` on the code, the projection
of fifteen magic states, the `35 p³` bound) are BACKLOG #76–#78 and consume these facts.

References: S. Bravyi, A. Kitaev, PRA 71 (2005) 022316 §IV; E. Knill, R. Laflamme, W. Zurek,
quant-ph/9610011 (the `[[15, 1, 3]]` code); F. J. MacWilliams, N. J. A. Sloane, *The Theory of
Error-Correcting Codes*, Ch. 1 §9 (the Hamming code) and Ch. 13 (Reed–Muller codes);
`specs/magic-plan.md`; `specs/BACKLOG.md` #75; `specs/future-work.md`.
-/

@[expose] public section

open Finset

namespace ReedMuller15

instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ### The parity-check matrix -/

/-- Column `j` of the parity-check matrix: the binary digits of `j + 1`, the `j`-th nonzero vector
of `𝔽₂⁴`. -/
def col (j : Fin 15) : Fin 4 → ZMod 2 := fun i => if Nat.testBit (j.val + 1) i.val then 1 else 0

theorem col_ne_zero (j : Fin 15) : col j ≠ 0 := by
  revert j
  decide

theorem col_injective : Function.Injective col := by
  intro j k
  revert j k
  decide

/-- The syndrome `H e` of a pattern `e`. -/
def syndrome (e : Fin 15 → ZMod 2) : Fin 4 → ZMod 2 := fun i => ∑ j, e j * col j i

/-- The support of a pattern. -/
def support (e : Fin 15 → ZMod 2) : Finset (Fin 15) := univ.filter fun j => e j ≠ 0

/-- The weight of a pattern. -/
def weight (e : Fin 15 → ZMod 2) : ℕ := (support e).card

/-- The indicator pattern of a set of qubits. -/
def ind (S : Finset (Fin 15)) : Fin 15 → ZMod 2 := fun j => if j ∈ S then 1 else 0

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

theorem ind_support (e : Fin 15 → ZMod 2) : ind (support e) = e := by
  funext j
  simp only [ind, support, mem_filter, mem_univ, true_and]
  rcases zmod_two_eq_zero_or_one (e j) with h | h <;> simp [h]

theorem support_ind (S : Finset (Fin 15)) : support (ind S) = S := by
  ext j
  simp [support, ind]

theorem weight_ind (S : Finset (Fin 15)) : weight (ind S) = S.card := by
  rw [weight, support_ind]

theorem syndrome_add (e f : Fin 15 → ZMod 2) : syndrome (e + f) = syndrome e + syndrome f := by
  funext i
  simp only [syndrome, Pi.add_apply, add_mul, sum_add_distrib]

theorem syndrome_ind (S : Finset (Fin 15)) : syndrome (ind S) = ∑ j ∈ S, col j := by
  funext i
  rw [syndrome, sum_apply]
  simp only [ind, ite_mul, one_mul, zero_mul]
  rw [sum_ite_mem, univ_inter]

/-! ### Weights one and two are detected -/

/-- **No undetected pattern of weight one**: the columns are nonzero. -/
theorem syndrome_ne_zero_of_weight_one (e : Fin 15 → ZMod 2) (h : weight e = 1) :
    syndrome e ≠ 0 := by
  obtain ⟨j, hj⟩ := card_eq_one.mp h
  rw [← ind_support e, hj, syndrome_ind, sum_singleton]
  exact col_ne_zero j

/-- **No undetected pattern of weight two**: the columns are distinct. -/
theorem syndrome_ne_zero_of_weight_two (e : Fin 15 → ZMod 2) (h : weight e = 2) :
    syndrome e ≠ 0 := by
  obtain ⟨j, k, hjk, hS⟩ := card_eq_two.mp h
  rw [← ind_support e, hS, syndrome_ind, sum_pair hjk]
  intro h0
  apply hjk
  apply col_injective
  funext i
  exact zmod_two_eq_of_add_eq_zero (congrFun h0 i)

/-! ### Exactly `35` undetected patterns of weight three -/

/-- The 3-subsets of qubits whose columns sum to zero: the lines of `PG(3, 2)`. -/
def undetectedTriples : Finset (Finset (Fin 15)) :=
  (univ.powersetCard 3).filter fun S => ∑ j ∈ S, col j = 0

set_option maxRecDepth 4000 in
theorem card_undetectedTriples : undetectedTriples.card = 35 := by
  decide

/-- ★ **Exactly `35` undetected patterns of weight `3`.** -/
theorem card_undetected_weight_three :
    (univ.filter fun e : Fin 15 → ZMod 2 => syndrome e = 0 ∧ weight e = 3).card = 35 := by
  rw [← card_undetectedTriples]
  refine card_bij (fun e _ => support e) ?_ ?_ ?_
  · intro e he
    rw [mem_filter] at he
    rw [undetectedTriples, mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, he.2.2⟩, ?_⟩
    rw [← syndrome_ind, ind_support]
    exact he.2.1
  · intro e _ e' _ h
    rw [← ind_support e, ← ind_support e', h]
  · intro S hS
    rw [undetectedTriples, mem_filter, mem_powersetCard] at hS
    refine ⟨ind S, ?_, support_ind S⟩
    rw [mem_filter, syndrome_ind, weight_ind]
    exact ⟨mem_univ _, hS.2, hS.1.2⟩

/-! ### Odd weight is the logical `Z̄` -/

/-- The pairing `e · x = ∑ eⱼ xⱼ` in `𝔽₂`. -/
def dotp (e x : Fin 15 → ZMod 2) : ZMod 2 := ∑ j, e j * x j

theorem syndrome_apply_eq_dotp (e : Fin 15 → ZMod 2) (i : Fin 4) :
    syndrome e i = dotp e fun j => col j i :=
  rfl

theorem weight_cast (e : Fin 15 → ZMod 2) : (weight e : ZMod 2) = ∑ j, e j := by
  rw [weight, support, ← sum_boole]
  refine sum_congr rfl fun j _ => ?_
  rcases zmod_two_eq_zero_or_one (e j) with h | h <;> simp [h]

/-- ★ **The parity rule**: `e · (x + 𝟙) = e · x + |e|`. An undetected `Z`-pattern (`e · x = 0` on
the `X`-stabiliser code) acts on the logical `1̄ = 0̄ + 𝟙` with the sign `(−1)^{|e|}`: it is the
logical `Z̄` exactly when its weight is odd. -/
theorem dotp_add_one (e x : Fin 15 → ZMod 2) :
    dotp e (x + 1) = dotp e x + (weight e : ZMod 2) := by
  rw [weight_cast, dotp, dotp, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp [mul_add]

/-! ### The Hamming code has `2¹¹` words -/

/-- The parity-check matrix `H`, columns `col j`. -/
def Hmat : Matrix (Fin 4) (Fin 15) (ZMod 2) := fun i j => col j i

theorem mulVec_eq_syndrome (e : Fin 15 → ZMod 2) : Hmat.mulVec e = syndrome e := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Hmat, syndrome, mul_comm]

/-- A preimage of a syndrome: the unit columns sit at `j = 0, 1, 3, 7`. -/
def preimage (s : Fin 4 → ZMod 2) : Fin 15 → ZMod 2 := fun j =>
  if j.val = 0 then s 0 else if j.val = 1 then s 1 else if j.val = 3 then s 2
    else if j.val = 7 then s 3 else 0

theorem syndrome_preimage (s : Fin 4 → ZMod 2) : syndrome (preimage s) = s := by
  revert s
  decide

theorem syndrome_surjective : Function.Surjective syndrome :=
  fun s => ⟨preimage s, syndrome_preimage s⟩

/-- The syndrome as a linear map. -/
def syndromeₗ : (Fin 15 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) := Hmat.mulVecLin

theorem syndromeₗ_apply (e : Fin 15 → ZMod 2) : syndromeₗ e = syndrome e := by
  rw [syndromeₗ, Matrix.mulVecLin_apply, mulVec_eq_syndrome]

theorem finrank_ker_syndromeₗ : Module.finrank (ZMod 2) (LinearMap.ker syndromeₗ) = 11 := by
  have h := LinearMap.finrank_range_add_finrank_ker syndromeₗ
  have hr : LinearMap.range syndromeₗ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro s
    exact ⟨preimage s, by rw [syndromeₗ_apply, syndrome_preimage]⟩
  rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

/-- ★ **The Hamming code has `2¹¹` words**: the undetected patterns number `2048`. -/
theorem card_undetected :
    (univ.filter fun e : Fin 15 → ZMod 2 => syndrome e = 0).card = 2 ^ 11 := by
  have hker : ∀ e, e ∈ LinearMap.ker syndromeₗ ↔ syndrome e = 0 := fun e => by
    rw [LinearMap.mem_ker, syndromeₗ_apply]
  have h1 : Nat.card (LinearMap.ker syndromeₗ)
      = (univ.filter fun e : Fin 15 → ZMod 2 => syndrome e = 0).card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hker), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have h2 : Nat.card (LinearMap.ker syndromeₗ) = 2 ^ 11 := by
    rw [Nat.card_congr (Module.finBasis (ZMod 2) (LinearMap.ker syndromeₗ)).equivFun.toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card,
      Fintype.card_fin, finrank_ker_syndromeₗ]
  rw [← h1, h2]

end ReedMuller15

end
