/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# n-qubit register (R1 foundation)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The foundation for the quantum-algorithm branch (`specs/nqubit-register-plan.md`). An
**n-qubit register state** is a vector in the `2ⁿ`-dimensional Hilbert space indexed by
**bitstrings** `Fin n → Fin 2` (the computational basis):

  `QReg n := EuclideanSpace ℂ (Fin n → Fin 2)`.

The bitstring index makes the per-qubit / tensor structure first-class (single-qubit gates,
the Hadamard product, the dot product `x · y`), which the algorithms need; inner product,
norm and Born probability come for free from `EuclideanSpace`.

This file provides the computational basis `basisState`, the Born probability `prob`, and the
core API: Born as a squared inner product (`prob_eq_inner_sq`), normalisation of a unit state
(`sum_prob_eq_one`), and that a basis state is measured with certainty (`prob_basisState`).
Later phases add the Hadamard transform, oracles, and the algorithms.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

/-- An **n-qubit register state**: a vector in the `2ⁿ`-dimensional Hilbert space indexed by
bitstrings `Fin n → Fin 2`. -/
abbrev QReg (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

variable {n : ℕ}

/-- The **computational basis state** `|x⟩` for a bitstring `x`. -/
noncomputable def basisState (x : Fin n → Fin 2) : QReg n := EuclideanSpace.single x 1

@[simp] lemma basisState_apply (x y : Fin n → Fin 2) :
    basisState x y = if y = x then 1 else 0 := by
  rw [basisState, PiLp.single_apply]

/-- The **Born probability** of measuring computational-basis outcome `z` in state `ψ`:
`‖ψ z‖² = ‖⟨z|ψ⟩‖²`. -/
noncomputable def prob (ψ : QReg n) (z : Fin n → Fin 2) : ℝ := ‖ψ z‖ ^ 2

lemma prob_nonneg (ψ : QReg n) (z : Fin n → Fin 2) : 0 ≤ prob ψ z := sq_nonneg _

/-- **Born rule, inner-product form:** the probability is the squared modulus of the
amplitude `⟨z|ψ⟩`. -/
lemma prob_eq_inner_sq (ψ : QReg n) (z : Fin n → Fin 2) :
    prob ψ z = ‖inner ℂ (basisState z) ψ‖ ^ 2 := by
  simp only [prob, basisState, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- `‖v‖² = ∑ z, ‖v z‖²` on the register (Parseval in coordinate form). -/
lemma normSq_eq_sum_prob (ψ : QReg n) : ‖ψ‖ ^ 2 = ∑ z, prob ψ z := by
  rw [EuclideanSpace.norm_eq]
  simp only [prob]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **Normalisation:** the Born probabilities of a unit register state sum to one. -/
lemma sum_prob_eq_one {ψ : QReg n} (hψ : ‖ψ‖ = 1) : ∑ z, prob ψ z = 1 := by
  rw [← normSq_eq_sum_prob, hψ, one_pow]

@[simp] lemma basisState_norm (x : Fin n → Fin 2) : ‖basisState x‖ = 1 := by
  rw [basisState, PiLp.norm_single, norm_one]

/-- **A computational basis state is measured with certainty:** `prob |x⟩ z = [z = x]`. -/
@[simp] lemma prob_basisState (x z : Fin n → Fin 2) :
    prob (basisState x) z = if z = x then 1 else 0 := by
  rw [prob, basisState_apply]
  split <;> simp

end QuantumInfo
