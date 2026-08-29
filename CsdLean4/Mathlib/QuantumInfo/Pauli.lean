/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Register
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Pauli operators and their `𝔽₂`-symplectic algebra (GK-1)

**Category:** 1-Mathlib (CSD-free).

The `n`-qubit Pauli operators `X^a Z^b` (`a b : Fin n → Fin 2`) as concrete coordinate
operators on the register, with the algebra that makes the stabiliser formalism tick
(plan `specs/gottesman-knill-plan.md`, brick GK-1):

* ★ **The group law** (`pauliOp_mul`): `X^a Z^b · X^{a'} Z^{b'} = (−1)^{b·a'} X^{a+a'}
  Z^{b+b'}` — the Pauli family is closed under composition, with the phase governed by the
  `𝔽₂` pairing.
* ★ **Commutation is the symplectic form** (`pauliOp_comm`/`pauliOp_comm_of_symp`): the
  composition mismatch is exactly `χ(a·b' + b·a')`, so two Paulis commute iff the symplectic
  form of their labels vanishes in `𝔽₂`.
* **Character orthogonality** (`sum_pauliSign`): `∑_z (−1)^{b·z} = 2ⁿ·[b = 0]`, hence
  ★ **every non-identity Pauli is traceless** (`pauliOp_trace`) — the seed of the
  stabiliser-state uniqueness argument (`tr(2⁻ⁿ ∑_{s∈S} s) = 1`, GK-3, not attempted here).
* **Unitarity in the coordinate sense** (`inner_pauliOp`): Paulis preserve the inner product.

Design note: every sign is `signChar` of an `𝔽₂`-valued form (`bdot`), never an `ℕ` parity —
so sign bookkeeping reduces to `Fin 2` identities in finitely many generalized atoms, closed
by `decide`. `Fin 2` carries the `ZMod 2` ring structure (`Fin.instCommRing`), so `ring` is
available for the form algebra; the one genuinely characteristic-2 fact, `v + v = 0`, is
`fin2_add_self`.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {n : ℕ}

/-! ## The sign character and the `𝔽₂` pairing -/

/-- The sign character on `𝔽₂`: `χ(0) = 1`, `χ(1) = −1`. -/
def signChar (v : Fin 2) : ℂ := if v = 0 then 1 else -1

@[simp] lemma signChar_zero : signChar 0 = 1 := rfl

lemma signChar_add (u v : Fin 2) : signChar (u + v) = signChar u * signChar v := by
  fin_cases u <;> fin_cases v <;>
    norm_num [signChar, show (1 + 1 : Fin 2) = 0 from rfl]

lemma signChar_mul_self (u : Fin 2) : signChar u * signChar u = 1 := by
  fin_cases u <;> norm_num [signChar]

lemma conj_signChar (u : Fin 2) : conj (signChar u) = signChar u := by
  fin_cases u <;> simp [signChar]

/-- `χ` turns `𝔽₂` sums into products. -/
lemma signChar_sum {κ : Type*} (s : Finset κ) (f : κ → Fin 2) :
    signChar (∑ i ∈ s, f i) = ∏ i ∈ s, signChar (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signChar_add, ih]

/-- The characteristic-2 fact: every bit is its own inverse. -/
lemma fin2_add_self (v : Fin 2) : v + v = 0 := by fin_cases v <;> rfl

/-- The `𝔽₂` pairing `b·z = ∑ᵢ bᵢzᵢ` (valued in `Fin 2`). -/
def bdot (b z : Fin n → Fin 2) : Fin 2 := ∑ i, b i * z i

lemma bdot_add_right (b z w : Fin n → Fin 2) : bdot b (z + w) = bdot b z + bdot b w := by
  rw [bdot, bdot, bdot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, mul_add]

lemma bdot_add_left (b b' z : Fin n → Fin 2) : bdot (b + b') z = bdot b z + bdot b' z := by
  rw [bdot, bdot, bdot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

@[simp] lemma bdot_zero_right (b : Fin n → Fin 2) : bdot b 0 = 0 := by
  simp [bdot]

@[simp] lemma bdot_zero_left (z : Fin n → Fin 2) : bdot 0 z = 0 := by
  simp [bdot]

lemma bdot_comm (b z : Fin n → Fin 2) : bdot b z = bdot z b :=
  Finset.sum_congr rfl fun i _ => (by decide : ∀ x y : Fin 2, x * y = y * x) (b i) (z i)

/-- The pairing against a point update: `b·(z[k := v]) = b·z + bₖ(zₖ + v)`. -/
lemma bdot_update (b z : Fin n → Fin 2) (k : Fin n) (v : Fin 2) :
    bdot b (Function.update z k v) = bdot b z + b k * (z k + v) := by
  have hsum : bdot b (Function.update z k v) + bdot b z = b k * (z k + v) := by
    rw [bdot, bdot, ← Finset.sum_add_distrib,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [Function.update_of_ne hik, fin2_add_self])
        (fun hk => absurd (Finset.mem_univ k) hk),
      Function.update_self]
    generalize b k = x
    generalize z k = y
    revert x y v
    decide
  calc bdot b (Function.update z k v)
      = bdot b (Function.update z k v) + (bdot b z + bdot b z) := by
        rw [fin2_add_self, add_zero]
    _ = bdot b (Function.update z k v) + bdot b z + bdot b z := by abel
    _ = b k * (z k + v) + bdot b z := by rw [hsum]
    _ = bdot b z + b k * (z k + v) := by abel

/-- The pairing against a point update in the first slot. -/
lemma bdot_update_left (b z : Fin n → Fin 2) (k : Fin n) (v : Fin 2) :
    bdot (Function.update b k v) z = bdot b z + z k * (b k + v) := by
  rw [bdot_comm, bdot_update, bdot_comm z b]

/-- The Pauli sign `(−1)^{b·z}` as `χ(b·z)`. -/
def pauliSign (b z : Fin n → Fin 2) : ℂ := signChar (bdot b z)

lemma pauliSign_add_right (b z w : Fin n → Fin 2) :
    pauliSign b (z + w) = pauliSign b z * pauliSign b w := by
  rw [pauliSign, pauliSign, pauliSign, bdot_add_right, signChar_add]

lemma pauliSign_add_left (b b' z : Fin n → Fin 2) :
    pauliSign (b + b') z = pauliSign b z * pauliSign b' z := by
  rw [pauliSign, pauliSign, pauliSign, bdot_add_left, signChar_add]

lemma pauliSign_mul_self (b z : Fin n → Fin 2) : pauliSign b z * pauliSign b z = 1 :=
  signChar_mul_self _

@[simp] lemma pauliSign_zero_left (z : Fin n → Fin 2) : pauliSign 0 z = 1 := by
  rw [pauliSign, bdot_zero_left, signChar_zero]

lemma conj_pauliSign (b z : Fin n → Fin 2) : conj (pauliSign b z) = pauliSign b z :=
  conj_signChar _

/-! ## The Pauli operators -/

/-- The **Pauli operator** `X^a Z^b` on the register: coordinate
`(X^a Z^b ψ)(z) = (−1)^{b·(z+a)} ψ(z+a)` — bit-flip by `a`, phase by `b`. -/
noncomputable def pauliOp (a b : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => pauliSign b (z + a) * ψ (z + a))

@[simp] lemma pauliOp_apply (a b : Fin n → Fin 2) (ψ : QReg n) (z : Fin n → Fin 2) :
    pauliOp a b ψ z = pauliSign b (z + a) * ψ (z + a) := rfl

/-- The identity-label Pauli is the identity. -/
@[simp] lemma pauliOp_zero (ψ : QReg n) : pauliOp 0 0 ψ = ψ := by
  ext z
  rw [pauliOp_apply, pauliSign_zero_left, one_mul, add_zero]

/-- ★ **The Pauli group law:** `X^a Z^b · X^{a'} Z^{b'} = (−1)^{b·a'} · X^{a+a'} Z^{b+b'}`.
The family is closed under composition; the phase is the `𝔽₂` pairing `b·a'`. -/
theorem pauliOp_mul (a b a' b' : Fin n → Fin 2) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ)
      = pauliSign b a' • pauliOp (a + a') (b + b') ψ := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, pauliOp_apply, pauliOp_apply,
    pauliOp_apply, show z + a + a' = z + (a + a') from by rw [add_assoc], ← mul_assoc,
    ← mul_assoc]
  congr 1
  rw [pauliSign, pauliSign, pauliSign, pauliSign, ← signChar_add, ← signChar_add]
  congr 1
  rw [bdot_add_left, show z + (a + a') = z + a + a' from by rw [add_assoc],
    bdot_add_right b (z + a) a']
  generalize bdot b (z + a) = p
  generalize bdot b a' = q
  generalize bdot b' (z + a + a') = r
  revert p q r
  decide

/-- ★ **Commutation is the symplectic form:** the composition mismatch between
`X^a Z^b · X^{a'} Z^{b'}` and its reverse is exactly `χ(a·b' + b·a')` — the two Paulis
commute iff the `𝔽₂` symplectic form of their labels vanishes. -/
theorem pauliOp_comm (a b a' b' : Fin n → Fin 2) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ)
      = signChar (bdot a b' + bdot b a') • pauliOp a' b' (pauliOp a b ψ) := by
  rw [pauliOp_mul, pauliOp_mul, smul_smul, show a' + a = a + a' from add_comm a' a,
    show b' + b = b + b' from add_comm b' b]
  congr 1
  rw [pauliSign, pauliSign, ← signChar_add, bdot_comm b' a]
  congr 1
  generalize bdot a b' = p
  generalize bdot b a' = q
  revert p q
  decide

/-- Two Paulis with vanishing symplectic form commute. -/
theorem pauliOp_comm_of_symp (a b a' b' : Fin n → Fin 2)
    (h : bdot a b' + bdot b a' = 0) (ψ : QReg n) :
    pauliOp a b (pauliOp a' b' ψ) = pauliOp a' b' (pauliOp a b ψ) := by
  rw [pauliOp_comm, h, signChar_zero, one_smul]

/-! ## Character orthogonality and tracelessness -/

/-- One-bit character orthogonality: `∑_v χ(u·v) = 2·[u = 0]`. -/
lemma sum_signChar_mul (u : Fin 2) :
    (∑ v : Fin 2, signChar (u * v)) = if u = 0 then 2 else 0 := by
  fin_cases u <;> simp [Fin.sum_univ_two, signChar]

/-- **Character orthogonality:** `∑_z (−1)^{b·z} = 2ⁿ·[b = 0]`. -/
theorem sum_pauliSign (b : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, pauliSign b z = if b = 0 then ((2 : ℂ) ^ n) else 0 := by
  have hfac : ∀ z : Fin n → Fin 2, pauliSign b z = ∏ i, signChar (b i * z i) := by
    intro z
    rw [pauliSign, bdot, signChar_sum]
  have hswap : (∏ i : Fin n, ∑ v : Fin 2, signChar (b i * v))
      = ∑ z ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin 2))),
          ∏ i, signChar (b i * z i) := Finset.prod_univ_sum _ _
  rw [Finset.sum_congr rfl fun z _ => hfac z, ← Fintype.piFinset_univ, ← hswap]
  rw [Finset.prod_congr rfl fun i _ => sum_signChar_mul (b i)]
  by_cases hb : b = 0
  · subst hb
    simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hb]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
    have hi' : b i ≠ 0 := by simpa using hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi'])

/-- ★ **Non-identity Paulis are traceless:** the diagonal sum of `X^a Z^b` over the
computational basis is `2ⁿ` at the identity label and `0` otherwise. This is the seed of the
stabiliser-projector trace argument (GK-3 in the plan). -/
theorem pauliOp_trace (a b : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, pauliOp a b (basisState z) z
      = if a = 0 ∧ b = 0 then ((2 : ℂ) ^ n) else 0 := by
  have hterm : ∀ z : Fin n → Fin 2,
      pauliOp a b (basisState z) z
        = (if a = 0 then 1 else 0) * pauliSign b (z + a) := by
    intro z
    rw [pauliOp_apply, basisState_apply]
    by_cases ha : a = 0
    · subst ha
      rw [add_zero, if_pos rfl, if_pos rfl, one_mul, mul_one]
    · rw [if_neg ha, if_neg (fun h : z + a = z => ha (by
        have h' : z + a = z + 0 := by rw [add_zero]; exact h
        exact add_left_cancel h')), mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z]
  by_cases ha : a = 0
  · subst ha
    have h1 : ∀ z : Fin n → Fin 2,
        ((if (0 : Fin n → Fin 2) = 0 then (1 : ℂ) else 0) * pauliSign b (z + 0))
          = pauliSign b z := by
      intro z
      rw [if_pos rfl, one_mul, add_zero]
    rw [Finset.sum_congr rfl fun z _ => h1 z, sum_pauliSign]
    by_cases hb : b = 0
    · rw [if_pos hb, if_pos ⟨rfl, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
  · rw [if_neg (fun h => ha h.1)]
    simp [if_neg ha]

/-! ## Unitarity in the coordinate sense -/

/-- **Paulis preserve the inner product:** the reindexing `z ↦ z + a` is a bijection and the
sign is real of modulus one. -/
theorem inner_pauliOp (a b : Fin n → Fin 2) (ψ φ : QReg n) :
    inner ℂ (pauliOp a b ψ) (pauliOp a b φ) = inner ℂ ψ φ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun z => ?_
  simp only [RCLike.inner_apply', pauliOp_apply, Equiv.coe_addRight, map_mul, conj_pauliSign]
  linear_combination (conj (ψ (z + a)) * φ (z + a)) * pauliSign_mul_self b (z + a)

end QuantumInfo
