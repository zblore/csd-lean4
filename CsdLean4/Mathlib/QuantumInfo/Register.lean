/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Computational-basis register (R1 foundation)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The foundation for the quantum-algorithm branch (`specs/nqubit-register-plan.md`). A **register
state** over a finite computational basis `ι` is a vector in `EuclideanSpace ℂ ι`; the
**n-qubit register** is the instance where the basis is the bitstrings:

  `QReg n := EuclideanSpace ℂ (Fin n → Fin 2)`.

This file provides the computational basis `basisState`, the Born probability `prob`, the
coordinate-of-a-sum bridge `sum_coord`, and the core API: Born as a squared inner product
(`prob_eq_inner_sq`), normalisation of a unit state (`sum_prob_eq_one`), and that a basis state
is measured with certainty (`prob_basisState`). Downstream files add the Hadamard transform, the
QFT (`Fourier.lean`), phase estimation (`PhaseEstimation.lean`), oracles, and the algorithms.

*Generalised 2026-08-29 (a strict widening, at the second consumer per `CONVENTIONS.md` §9):
the primitives were stated for bitstrings only, and `Empirical/QM/Algorithms/ShorCore.lean`
carried a verbatim second copy over a general finite index for its `ZMod N` and `Fin T`
registers. The general form subsumes both; the bitstring statements are the `ι = Fin n → Fin 2`
instances and every consumer elaborates as before.*
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

/-- An **n-qubit register state**: a vector in the `2ⁿ`-dimensional Hilbert space indexed by
bitstrings `Fin n → Fin 2`. The bitstring instance of the general finite-basis register below. -/
abbrev QReg (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

variable {ι : Type*} [DecidableEq ι]

/-- The **computational basis state** `|x⟩` indexed by an arbitrary finite type. -/
noncomputable def basisState (x : ι) : EuclideanSpace ℂ ι := EuclideanSpace.single x 1

@[simp] lemma basisState_apply (x y : ι) :
    basisState x y = if y = x then 1 else 0 := by
  rw [basisState, PiLp.single_apply]

omit [DecidableEq ι] in
/-- The **Born probability** of measuring computational-basis outcome `z` in state `ψ`:
`‖ψ z‖² = ‖⟨z|ψ⟩‖²`. -/
noncomputable def prob (ψ : EuclideanSpace ℂ ι) (z : ι) : ℝ := ‖ψ z‖ ^ 2

omit [DecidableEq ι] in
lemma prob_nonneg (ψ : EuclideanSpace ℂ ι) (z : ι) : 0 ≤ prob ψ z := sq_nonneg _

/-- **Born rule, inner-product form:** the probability is the squared modulus of the
amplitude `⟨z|ψ⟩`. -/
lemma prob_eq_inner_sq [Fintype ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    prob ψ z = ‖inner ℂ (basisState z) ψ‖ ^ 2 := by
  simp only [prob, basisState, EuclideanSpace.inner_single_left, map_one, one_mul]

omit [DecidableEq ι] in
/-- `‖v‖² = ∑ z, ‖v z‖²` on the register (Parseval in coordinate form). -/
lemma normSq_eq_sum_prob [Fintype ι] (ψ : EuclideanSpace ℂ ι) : ‖ψ‖ ^ 2 = ∑ z, prob ψ z := by
  rw [EuclideanSpace.norm_eq]
  simp only [prob]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in
/-- **Normalisation:** the Born probabilities of a unit register state sum to one. -/
lemma sum_prob_eq_one [Fintype ι] {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    ∑ z, prob ψ z = 1 := by
  rw [← normSq_eq_sum_prob, hψ, one_pow]

@[simp] lemma basisState_norm [Fintype ι] (x : ι) : ‖basisState x‖ = 1 := by
  rw [basisState, PiLp.norm_single, norm_one]

/-- **A computational basis state is measured with certainty:** `prob |x⟩ z = [z = x]`. -/
@[simp] lemma prob_basisState (x z : ι) :
    prob (basisState x) z = if z = x then 1 else 0 := by
  rw [prob, basisState_apply]
  split <;> simp

omit [DecidableEq ι] in
/-- Coordinatewise: a finite sum of register states evaluates as the sum of coordinates. -/
lemma sum_coord {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ ι) (y : ι) :
    (∑ k ∈ s, f k) y = ∑ k ∈ s, (f k) y := by
  have h : (∑ k ∈ s, f k).ofLp = ∑ k ∈ s, (f k).ofLp :=
    map_sum (WithLp.addEquiv 2 (ι → ℂ)) f s
  calc (∑ k ∈ s, f k) y = (∑ k ∈ s, f k).ofLp y := rfl
    _ = (∑ k ∈ s, (f k).ofLp) y := by rw [h]
    _ = ∑ k ∈ s, (f k) y := by rw [Finset.sum_apply]

end QuantumInfo
