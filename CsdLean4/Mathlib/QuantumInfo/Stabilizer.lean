/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Clifford

/-!
# Stabiliser families, the group projector, and the stabilised state (GK-3)

**Category:** 1-Mathlib (CSD-free).

The stabiliser layer over the Pauli algebra (plan `specs/gottesman-knill-plan.md`, GK-3),
in the corpus's hypothesis-driven concrete style: a **stabiliser family** is indexed by
`𝔽₂^m` directly — `𝔽₂`-linear label maps `A B : 𝔽₂^m → 𝔽₂ⁿ` and a sign function
`σ : 𝔽₂^m → 𝔽₂` subject to the one **coherence law**

  `σ(x+y) = σ(x) + σ(y) + B(x)·A(y)`,

which is exactly the condition that the signed Paulis `χ(σx)·X^{Ax}Z^{Bx}` form a genuine
group (the `𝔽₂` pairing on the right is the phase of `pauliOp_mul`) — the "`−I ∉ S`"
condition of the stabiliser formalism. Commutativity of the family is *implied*: coherence
at `(x,y)` and at `(y,x)` forces the symplectic form of any two members to vanish
(`stab_symp_zero`).

* ★ **Absorption** (`stabProjector_absorb`): every signed element of the family fixes the
  group average `P = 2^{−m} ∑_x χ(σx)·X^{Ax}Z^{Bx}` — one reindex `y ↦ x + y`.
* ★ **Idempotence** (`stabProjector_idem`): `P² = P`, three lines from absorption.
* ★ **The trace** (`stabProjector_trace`): with independent labels,
  `tr P = 2ⁿ/2^m` — the dimension count of the code space; `1` for a full stabiliser
  (`m = n`).
* ★★ **The stabilised state exists** (`stabState_exists`): a nonzero `ψ` with `Pψ = ψ` and
  `χ(σx)·X^{Ax}Z^{Bx} ψ = ψ` for **every** group element — the defining property of a
  stabiliser state, extracted from `tr P ≠ 0` plus idempotence, no spectral machinery.

**Honest scope.** Two named residues: (i) *uniqueness/dimension* — that the fixed space has
dimension exactly `2^{n−m}` needs rank-equals-trace for self-adjoint idempotents, spectral
machinery not built here; the trace statement is the dimension count in the form this file
can honestly state. (ii) The *measurement-update rule* (outcome probabilities and the
post-measurement stabiliser) is not attempted. Both are recorded in the plan.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {n m : ℕ}

/-- The **stabiliser-group average**
`P = 2^{−m} ∑_{x ∈ 𝔽₂^m} χ(σx) · X^{Ax} Z^{Bx}`, applied to a state. -/
noncomputable def stabProjector (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) (ψ : QReg n) : QReg n :=
  ((2 : ℂ) ^ m)⁻¹ • ∑ x : Fin m → Fin 2, signChar (σ x) • pauliOp (A x) (B x) ψ

section Coherent

variable {A B : (Fin m → Fin 2) → (Fin n → Fin 2)} {σ : (Fin m → Fin 2) → Fin 2}

/-- Linearity forces the zero label at `0`. -/
lemma stab_label_zero (hA : ∀ x y, A (x + y) = A x + A y) : A 0 = 0 := by
  have h := hA 0 0
  rw [add_zero] at h
  have h2 : A 0 + A 0 = 0 := by
    funext i
    rw [Pi.add_apply, Pi.zero_apply]
    exact fin2_add_self _
  exact h.trans h2

/-- Coherence forces the trivial sign at `0` — the group contains `+I`, not `−I`. -/
lemma stab_sigma_zero (hB : ∀ x y, B (x + y) = B x + B y)
    (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y)) : σ 0 = 0 := by
  have h := hσ 0 0
  rw [add_zero, stab_label_zero hB, bdot_zero_left, add_zero] at h
  exact h.trans (fin2_add_self _)

/-- Coherence at `(x,y)` and `(y,x)` forces the symplectic form of any two members to
vanish: the family is automatically abelian. -/
lemma stab_symp_zero (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))
    (x y : Fin m → Fin 2) : bdot (A x) (B y) + bdot (B x) (A y) = 0 := by
  have h1 := hσ x y
  have h2 := hσ y x
  rw [add_comm y x] at h2
  have h3 : σ x + σ y + bdot (B x) (A y) = σ y + σ x + bdot (B y) (A x) :=
    h1.symm.trans h2
  have h4 : bdot (B x) (A y) = bdot (B y) (A x) := by
    have := h3
    generalize σ x = p at this
    generalize σ y = q at this
    generalize bdot (B x) (A y) = r at this
    generalize bdot (B y) (A x) = s at this
    revert this
    revert p q r s
    decide
  rw [bdot_comm (A x) (B y), ← h4]
  exact fin2_add_self _

variable (hA : ∀ x y, A (x + y) = A x + A y) (hB : ∀ x y, B (x + y) = B x + B y)
variable (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))

include hA hB hσ in
/-- ★ **Absorption:** every signed element of the family fixes the group average. -/
theorem stabProjector_absorb (x : Fin m → Fin 2) (ψ : QReg n) :
    signChar (σ x) • pauliOp (A x) (B x) (stabProjector A B σ ψ)
      = stabProjector A B σ ψ := by
  rw [stabProjector, pauliOp_smul, pauliOp_sum,
    Finset.sum_congr rfl fun y _ => by rw [pauliOp_smul, pauliOp_mul],
    smul_comm (signChar (σ x)) (((2 : ℂ) ^ m)⁻¹), Finset.smul_sum,
    Finset.sum_congr rfl fun y _ => by
      rw [smul_smul, smul_smul, pauliSign, ← signChar_add, ← signChar_add, ← hσ x y,
        ← hA x y, ← hB x y]]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => rfl

include hA hB hσ in
/-- ★ **Idempotence**, three lines from absorption. -/
theorem stabProjector_idem (ψ : QReg n) :
    stabProjector A B σ (stabProjector A B σ ψ) = stabProjector A B σ ψ := by
  conv_lhs => rw [stabProjector]
  rw [Finset.sum_congr rfl fun x _ => stabProjector_absorb hA hB hσ x ψ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

include hA hB hσ in
/-- ★ **The trace of the group average is the code-space dimension count** `2ⁿ/2^m`
(`= 1` for a full stabiliser, `m = n`): only the identity label survives the Pauli trace,
and independence pins it to `x = 0`, where coherence forces the `+` sign. -/
theorem stabProjector_trace (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) :
    ∑ z : Fin n → Fin 2, stabProjector A B σ (basisState z) z
      = (2 : ℂ) ^ n / (2 : ℂ) ^ m := by
  have hterm : ∀ z : Fin n → Fin 2,
      stabProjector A B σ (basisState z) z
        = ((2 : ℂ) ^ m)⁻¹ * ∑ x : Fin m → Fin 2,
            signChar (σ x) * pauliOp (A x) (B x) (basisState z) z := by
    intro z
    rw [stabProjector, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
    congr 1
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum, pauliOp_trace],
    Finset.sum_eq_single 0
      (fun x _ hx => by rw [if_neg fun h => hx (hinj x h.1 h.2), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    if_pos ⟨stab_label_zero hA, stab_label_zero hB⟩, stab_sigma_zero hB hσ,
    signChar_zero, one_mul, mul_comm, ← div_eq_mul_inv]

include hA hB hσ in
/-- ★★ **The stabilised state exists:** a nonzero `ψ` fixed by the group average and by
**every** signed element of the family — the defining property of a stabiliser state.
Extracted from `tr P ≠ 0` and idempotence; no spectral machinery. (That the fixed space has
dimension exactly `2^{n−m}` is the named uniqueness residue in the plan.) -/
theorem stabState_exists (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) :
    ∃ ψ : QReg n, ψ ≠ 0 ∧ stabProjector A B σ ψ = ψ
      ∧ ∀ x, signChar (σ x) • pauliOp (A x) (B x) ψ = ψ := by
  have hne : ∃ φ : QReg n, stabProjector A B σ φ ≠ 0 := by
    by_contra hall
    rw [not_exists] at hall
    have h0 : ∀ φ : QReg n, stabProjector A B σ φ = 0 :=
      fun φ => not_not.mp (hall φ)
    have htr := stabProjector_trace hA hB hσ hinj
    rw [Finset.sum_congr rfl fun z _ => by rw [h0 (basisState z)]] at htr
    simp only [WithLp.ofLp_zero, Pi.zero_apply, Finset.sum_const_zero] at htr
    exact (div_ne_zero (pow_ne_zero n (two_ne_zero))
      (pow_ne_zero m (two_ne_zero))) htr.symm
  obtain ⟨φ, hφ⟩ := hne
  exact ⟨stabProjector A B σ φ, hφ, stabProjector_idem hA hB hσ φ,
    fun x => stabProjector_absorb hA hB hσ x φ⟩

end Coherent

end QuantumInfo
