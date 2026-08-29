/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Pauli

/-!
# Clifford generators conjugate Paulis to Paulis (GK-2: the Gottesman–Knill mechanism)

**Category:** 1-Mathlib (CSD-free).

The three Clifford generator families as concrete coordinate operators — `cnotGate j k`
(controlled-NOT), `sGate j` (the phase gate), `hGate j` (the single-qubit Hadamard) — and the
theorem family that IS the Gottesman–Knill mechanism: **conjugation by each generator maps
every Pauli operator to a phase times a Pauli operator, with the label map explicit and
`𝔽₂`-linear** (plan `specs/gottesman-knill-plan.md`, brick GK-2):

* ★ `cnotGate_conj_pauliOp` — `CNOT_{jk} · X^a Z^b · CNOT_{jk} = X^{σa} Z^{σᵀb}` with
  `σ = cnotFlip j k` (add bit `j` into bit `k`), `σᵀ = cnotFlip k j`; **no phase**.
* ★ `sGate_conj_pauliOp` — `S_j · X^a Z^b · S_j† = i^{a_j} · X^a Z^{b + a_j e_j}`.
* ★ `hGate_conj_pauliOp` — `H_j · X^a Z^b · H_j = (−1)^{a_j b_j} · X^{a[j↦b_j]} Z^{b[j↦a_j]}`
  (swap `a_j ↔ b_j`).

**Why this is Gottesman–Knill.** In the Heisenberg picture a Pauli is `2n` bits and a phase,
and each generator updates the bits by the explicit `𝔽₂`-linear maps above — so a stabiliser
description of a state (n commuting Paulis) is carried through any circuit of these gates by
linear algebra over `𝔽₂`. That closure is proved here in full. **Honest scope:** the
"classically simulable in polynomial time" reading is a complexity claim about that update
rule; the corpus has no computation model and does not state it — no circuit datatype, no
gate count, no measurement-update rule (the stabiliser-measurement layer is GK-3 in the plan,
gated). `hGate j` is the single-qubit sibling of `Hadamard.lean`'s all-qubits `H^⊗n`, not a
replacement for it.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {n : ℕ}

/-! ## Update helpers on the bitstring group -/

/-- `σ_{jk}`: add bit `j` into bit `k`. Self-inverse for `j ≠ k`; the label map of CNOT. -/
def cnotFlip (j k : Fin n) (z : Fin n → Fin 2) : Fin n → Fin 2 :=
  Function.update z k (z k + z j)

lemma cnotFlip_apply_ne (j k : Fin n) (z : Fin n → Fin 2) {i : Fin n} (hik : i ≠ k) :
    cnotFlip j k z i = z i :=
  Function.update_of_ne hik _ _

lemma cnotFlip_apply_k (j k : Fin n) (z : Fin n → Fin 2) :
    cnotFlip j k z k = z k + z j :=
  Function.update_self _ _ _

/-- The flip is additive. -/
lemma cnotFlip_add (j k : Fin n) (z w : Fin n → Fin 2) :
    cnotFlip j k (z + w) = cnotFlip j k z + cnotFlip j k w := by
  funext i
  by_cases hik : i = k
  · subst hik
    rw [Pi.add_apply, cnotFlip_apply_k, cnotFlip_apply_k, cnotFlip_apply_k, Pi.add_apply,
      Pi.add_apply]
    abel
  · rw [cnotFlip_apply_ne j k _ hik, Pi.add_apply, Pi.add_apply,
      cnotFlip_apply_ne j k z hik, cnotFlip_apply_ne j k w hik]

/-- The flip is an involution (`j ≠ k`). -/
lemma cnotFlip_invol (j k : Fin n) (hjk : j ≠ k) (z : Fin n → Fin 2) :
    cnotFlip j k (cnotFlip j k z) = z := by
  funext i
  by_cases hik : i = k
  · subst hik
    rw [cnotFlip_apply_k, cnotFlip_apply_k, cnotFlip_apply_ne j i z hjk, add_assoc,
      fin2_add_self, add_zero]
  · rw [cnotFlip_apply_ne j k _ hik, cnotFlip_apply_ne j k z hik]

/-- Updating then translating is translating then updating (with the shifted value). -/
lemma update_add_right (z a : Fin n → Fin 2) (j : Fin n) (v : Fin 2) :
    Function.update z j v + a = Function.update (z + a) j (v + a j) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Pi.add_apply, Function.update_self, Function.update_self]
  · rw [Pi.add_apply, Function.update_of_ne hij, Function.update_of_ne hij, Pi.add_apply]

/-- Translating by an update. -/
lemma add_update_right (z a : Fin n → Fin 2) (j : Fin n) (v : Fin 2) :
    z + Function.update a j v = Function.update (z + a) j (z j + v) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Pi.add_apply, Function.update_self, Function.update_self]
  · rw [Pi.add_apply, Function.update_of_ne hij, Function.update_of_ne hij, Pi.add_apply]

/-! ## The CNOT gate -/

/-- The **controlled-NOT** `CNOT_{jk}` (control `j`, target `k`): the permutation operator of
`cnotFlip j k`. -/
noncomputable def cnotGate (j k : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm (fun z => ψ (cnotFlip j k z))

@[simp] lemma cnotGate_apply (j k : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    cnotGate j k ψ z = ψ (cnotFlip j k z) := rfl

/-- CNOT is self-inverse (`j ≠ k`). -/
lemma cnotGate_cnotGate (j k : Fin n) (hjk : j ≠ k) (ψ : QReg n) :
    cnotGate j k (cnotGate j k ψ) = ψ := by
  ext z
  rw [cnotGate_apply, cnotGate_apply, cnotFlip_invol j k hjk]

/-- ★ **CNOT conjugation:** `CNOT_{jk} · X^a Z^b · CNOT_{jk} = X^{σa} Z^{σᵀb}` — the `X`
label gains `a_j` at bit `k`, the `Z` label gains `b_k` at bit `j`, and there is **no
phase**. -/
theorem cnotGate_conj_pauliOp (j k : Fin n) (hjk : j ≠ k) (a b : Fin n → Fin 2)
    (ψ : QReg n) :
    cnotGate j k (pauliOp a b (cnotGate j k ψ))
      = pauliOp (cnotFlip j k a) (cnotFlip k j b) ψ := by
  ext z
  rw [cnotGate_apply, pauliOp_apply, cnotGate_apply, pauliOp_apply,
    show cnotFlip j k (cnotFlip j k z + a) = z + cnotFlip j k a from by
      rw [cnotFlip_add, cnotFlip_invol j k hjk]]
  congr 1
  rw [pauliSign, pauliSign]
  congr 1
  rw [bdot_add_right, bdot_add_right, cnotFlip, cnotFlip, cnotFlip,
    bdot_update b z k (z k + z j),
    bdot_update_left b z j (b j + b k),
    bdot_update_left b (Function.update a k (a k + a j)) j (b j + b k),
    bdot_update b a k (a k + a j),
    Function.update_of_ne hjk (a k + a j) a]
  generalize bdot b z = p
  generalize bdot b a = q
  generalize z k = x1
  generalize z j = x2
  generalize b j = y1
  generalize b k = y2
  generalize a k = w1
  generalize a j = w2
  revert p q x1 x2 y1 y2 w1 w2
  decide

/-! ## The phase gate -/

/-- The **phase gate** `S_j`: phase `i` on the `z_j = 1` branch. -/
noncomputable def sGate (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => Complex.I ^ ((z j : Fin 2) : ℕ) * ψ z)

/-- The inverse phase gate `S_j†`. -/
noncomputable def sGateInv (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => (-Complex.I) ^ ((z j : Fin 2) : ℕ) * ψ z)

@[simp] lemma sGate_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    sGate j ψ z = Complex.I ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

@[simp] lemma sGateInv_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    sGateInv j ψ z = (-Complex.I) ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

lemma sGate_sGateInv (j : Fin n) (ψ : QReg n) : sGate j (sGateInv j ψ) = ψ := by
  ext z
  rw [sGate_apply, sGateInv_apply, ← mul_assoc, ← mul_pow,
    show Complex.I * -Complex.I = 1 from by rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_pow, one_mul]

lemma sGateInv_sGate (j : Fin n) (ψ : QReg n) : sGateInv j (sGate j ψ) = ψ := by
  ext z
  rw [sGateInv_apply, sGate_apply, ← mul_assoc, ← mul_pow,
    show -Complex.I * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg],
    one_pow, one_mul]

/-- ★ **Phase-gate conjugation:** `S_j · X^a Z^b · S_j† = i^{a_j} · X^a Z^{b[j ↦ b_j+a_j]}` —
the `Z` label gains `a_j` at bit `j`, with phase `i^{a_j}` (this is `S X S† = Y`). -/
theorem sGate_conj_pauliOp (j : Fin n) (a b : Fin n → Fin 2) (ψ : QReg n) :
    sGate j (pauliOp a b (sGateInv j ψ))
      = Complex.I ^ ((a j : Fin 2) : ℕ)
          • pauliOp a (Function.update b j (b j + a j)) ψ := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sGate_apply, pauliOp_apply,
    sGateInv_apply, pauliOp_apply, pauliSign, pauliSign,
    bdot_update_left b (z + a) j (b j + a j), signChar_add, Pi.add_apply z a j]
  generalize hB : bdot b (z + a) = B
  generalize hu : z j = u
  generalize hw : a j = w
  generalize hy : b j = y
  fin_cases u <;> fin_cases w <;> fin_cases y <;> fin_cases B <;>
    simp +decide [signChar, mul_neg, neg_neg] <;>
    first
      | ring1
      | linear_combination (-(ψ (z + a))) * Complex.I_sq
      | linear_combination (ψ (z + a)) * Complex.I_sq

/-! ## The Hadamard gate (single qubit) -/

/-- The **single-qubit Hadamard** `H_j`:
`(H_j ψ)(z) = (1/√2) ∑_v (−1)^{z_j·v} ψ(z[j ↦ v])`. -/
noncomputable def hGate (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => (Real.sqrt 2 : ℂ)⁻¹
      * ∑ v : Fin 2, signChar (z j * v) * ψ (Function.update z j v))

@[simp] lemma hGate_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    hGate j ψ z
      = (Real.sqrt 2 : ℂ)⁻¹
          * ∑ v : Fin 2, signChar (z j * v) * ψ (Function.update z j v) := rfl

/-- The normalisation constant: `(1/√2)·(1/√2)·2 = 1`. -/
lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `H_j` is self-inverse. -/
theorem hGate_hGate (j : Fin n) (ψ : QReg n) : hGate j (hGate j ψ) = ψ := by
  ext z
  rw [hGate_apply]
  have hin : ∀ v : Fin 2,
      signChar (z j * v) * hGate j ψ (Function.update z j v)
        = (Real.sqrt 2 : ℂ)⁻¹
            * ∑ w : Fin 2, signChar (v * (z j + w)) * ψ (Function.update z j w) := by
    intro v
    rw [hGate_apply, ← mul_assoc, mul_comm (signChar (z j * v)), mul_assoc,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Function.update_self, Function.update_idem, ← mul_assoc, ← signChar_add,
      show z j * v + v * w = v * (z j + w) from by
        generalize z j = p
        revert p v w
        decide]
  rw [Finset.sum_congr rfl fun v _ => hin v, ← Finset.mul_sum, Finset.sum_comm]
  have hcol : ∀ w : Fin 2,
      (∑ v : Fin 2, signChar (v * (z j + w)) * ψ (Function.update z j w))
        = (if z j + w = 0 then (2 : ℂ) else 0) * ψ (Function.update z j w) := by
    intro w
    rw [← Finset.sum_mul,
      Finset.sum_congr rfl fun v _ => by rw [mul_comm v (z j + w)],
      sum_signChar_mul]
  rw [Finset.sum_congr rfl fun w _ => hcol w,
    Finset.sum_eq_single (z j)
      (fun w _ hw => by
        rw [if_neg fun h => hw ((by decide : ∀ p q : Fin 2, p + q = 0 → q = p) _ _ h),
          zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    if_pos (fin2_add_self (z j)), Function.update_eq_self,
    show (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ * (2 * ψ z))
        = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2) * ψ z from by ring,
    sqrt_two_inv_sq, one_mul]

/-- ★ **Hadamard conjugation:** `H_j · X^a Z^b · H_j = (−1)^{a_j b_j} · X^{a[j↦b_j]}
Z^{b[j↦a_j]}` — the `X` and `Z` labels swap at bit `j`, with sign `(−1)^{a_j b_j}` (this is
`HXH = Z`, `HZH = X`, `HYH = −Y`). -/
theorem hGate_conj_pauliOp (j : Fin n) (a b : Fin n → Fin 2) (ψ : QReg n) :
    hGate j (pauliOp a b (hGate j ψ))
      = signChar (a j * b j)
          • pauliOp (Function.update a j (b j)) (Function.update b j (a j)) ψ := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hGate_apply, pauliOp_apply,
    add_update_right z a j (b j)]
  have hstep : ∀ v : Fin 2,
      signChar (z j * v) * pauliOp a b (hGate j ψ) (Function.update z j v)
        = (Real.sqrt 2 : ℂ)⁻¹ * ∑ w : Fin 2,
            signChar (v * (z j + b j + w)
                + (bdot b (z + a) + b j * z j + a j * w))
              * ψ (Function.update (z + a) j w) := by
    intro v
    rw [pauliOp_apply, update_add_right z a j v, hGate_apply, Function.update_self,
      pauliSign, bdot_update b (z + a) j (v + a j), Pi.add_apply z a j, ← mul_assoc,
      ← signChar_add, ← mul_assoc, mul_comm _ ((Real.sqrt 2 : ℂ)⁻¹), mul_assoc,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Function.update_idem, ← mul_assoc, ← signChar_add]
    congr 2
    generalize bdot b (z + a) = B
    generalize z j = p
    generalize a j = q
    generalize b j = r
    revert B p q r v w
    decide
  rw [Finset.sum_congr rfl fun v _ => hstep v, ← Finset.mul_sum, Finset.sum_comm]
  have hcol : ∀ w : Fin 2,
      (∑ v : Fin 2, signChar (v * (z j + b j + w)
          + (bdot b (z + a) + b j * z j + a j * w))
        * ψ (Function.update (z + a) j w))
        = ((if z j + b j + w = 0 then (2 : ℂ) else 0)
            * signChar (bdot b (z + a) + b j * z j + a j * w))
          * ψ (Function.update (z + a) j w) := by
    intro w
    rw [← Finset.sum_mul,
      Finset.sum_congr rfl fun v _ => by
        rw [signChar_add, show v * (z j + b j + w) = (z j + b j + w) * v from
          mul_comm _ _],
      ← Finset.sum_mul, sum_signChar_mul]
  rw [Finset.sum_congr rfl fun w _ => hcol w,
    Finset.sum_eq_single (z j + b j)
      (fun w _ hw => by
        rw [if_neg fun h => hw ((by decide : ∀ p q : Fin 2, p + q = 0 → q = p) _ _ h),
          zero_mul, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    if_pos (fin2_add_self (z j + b j)),
    pauliSign, bdot_update_left b (Function.update (z + a) j (z j + b j)) j (a j),
    Function.update_self, bdot_update b (z + a) j (z j + b j), Pi.add_apply z a j]
  have hχ : signChar (bdot b (z + a) + b j * z j + a j * (z j + b j))
      = signChar (a j * b j)
        * signChar (bdot b (z + a) + b j * (z j + a j + (z j + b j))
            + (z j + b j) * (b j + a j)) := by
    rw [← signChar_add]
    congr 1
    generalize bdot b (z + a) = B
    generalize z j = p
    generalize a j = q
    generalize b j = r
    revert B p q r
    decide
  rw [show (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹
        * (2 * signChar (bdot b (z + a) + b j * z j + a j * (z j + b j))
            * ψ (Function.update (z + a) j (z j + b j))))
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2)
          * (signChar (bdot b (z + a) + b j * z j + a j * (z j + b j))
            * ψ (Function.update (z + a) j (z j + b j))) from by ring,
    sqrt_two_inv_sq, one_mul, hχ, mul_assoc]

end QuantumInfo
