/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.ControlledDilation
public import CsdLean4.Empirical.QM.QEC.SyndromeRecovery

/-!
# Empirical/QM: independent bit-flip noise on the three-qubit code, and its residual failure

**Category:** 3-Local. QM-validity layer (matrix algebra over the K2 `Channel` layer; no CSD
content). BACKLOG #52, the QM half.

`SyndromeRecovery.lean` corrects the *single-error* mixture `∑ₖ qₖ Eₖ ρ Eₖ` exactly. The physical
noise is different: **each of the three qubits flips independently with probability `p`**, so all
eight flip patterns occur, the two- and three-flip patterns with total weight `3p² − 2p³`, and
those the code mis-corrects into the logical flip `X̄ = X ⊗ X ⊗ X`. This file states the channel
and the exact outcome of syndrome recovery on it:

* `flipOp x = X^{x₁} ⊗ X^{x₂} ⊗ X^{x₃}` for a pattern `x : Fin 2 × Fin 2 × Fin 2`, with weight
  `indepWeight p x = ∏ᵢ (p if xᵢ = 1 else 1 − p)` (`sum_indepWeight`: they sum to `1`);
* `indepFlipChannel p` — the mixed-unitary channel of that family
  (`Channel.mixedUnitaryChannel`), so `ControlledDilation.lean` gives it as the Stinespring channel
  of one joint unitary on register ⊗ `ℂ⁸`;
* `flipOp_eq` — every pattern is a single error times `1` (weight `≤ 1`) or times `X̄`
  (weight `≥ 2`), the syndrome reading of the pattern; `recoveryChannel_apply_flipOp` — recovery
  returns `ρ` on the first and `X̄ ρ X̄` on the second;
* ★★ `recoveryChannel_apply_indepFlipChannel_apply` — **on the code,
  `R (N_p ρ) = (1 − p_fail) ρ + p_fail X̄ ρ X̄` with `p_fail = 3p² − 2p³`**: the recovered state is
  the input with probability `1 − 3p² + 2p³` and the logically flipped input otherwise
  (`failProb_lt_of_lt_half`: `p_fail < p` for `0 < p < 1/2`, the code helps exactly below
  `p = 1/2`).

`Empirical/CSD/QEC/IndependentNoiseFlow.lean` reads the joint unitary as a `Σ`-flow.

## Source

Nielsen–Chuang §10.1.1 (the three-qubit bit-flip code, the `3p² − 2p³` failure probability).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### Flip patterns, their operators and their weights -/

/-- A flip pattern: which of the three qubits flip (`1`) or not (`0`). -/
abbrev FlipPattern := Fin 2 × Fin 2 × Fin 2

/-- `flipMat 0 = 1`, `flipMat 1 = X`. -/
noncomputable def flipMat : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pX]

@[simp] lemma flipMat_zero : flipMat 0 = 1 := rfl
@[simp] lemma flipMat_one : flipMat 1 = pX := rfl

lemma flipMat_mul_self (x : Fin 2) : flipMat x * flipMat x = 1 := by
  fin_cases x <;> simp

lemma flipMat_conjTranspose (x : Fin 2) : (flipMat x)ᴴ = flipMat x := by
  fin_cases x <;> simp

/-- The pattern error `X^{x₁} ⊗ X^{x₂} ⊗ X^{x₃}`. -/
noncomputable def flipOp (x : FlipPattern) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  kron3 (flipMat x.1) (flipMat x.2.1) (flipMat x.2.2)

lemma kron3_one : kron3 1 1 1 = 1 := by
  simp only [kron3, Matrix.one_kronecker_one]

lemma flipOp_mul_self (x : FlipPattern) : flipOp x * flipOp x = 1 := by
  rw [flipOp, kron3_mul, flipMat_mul_self, flipMat_mul_self, flipMat_mul_self, kron3_one]

lemma flipOp_conjTranspose (x : FlipPattern) : (flipOp x)ᴴ = flipOp x := by
  rw [flipOp, kron3_conjTranspose, flipMat_conjTranspose, flipMat_conjTranspose,
    flipMat_conjTranspose]

lemma flipOp_conjTranspose_mul_self (x : FlipPattern) : (flipOp x)ᴴ * flipOp x = 1 := by
  rw [flipOp_conjTranspose, flipOp_mul_self]

/-- The weight of one qubit's outcome: `1 − p` for no flip, `p` for a flip. -/
noncomputable def bitWeight (p : ℝ) : Fin 2 → ℝ := ![1 - p, p]

@[simp] lemma bitWeight_zero (p : ℝ) : bitWeight p 0 = 1 - p := rfl
@[simp] lemma bitWeight_one (p : ℝ) : bitWeight p 1 = p := rfl

/-- The weight of a pattern under independent flips: the product over the three qubits. -/
noncomputable def indepWeight (p : ℝ) (x : FlipPattern) : ℝ :=
  bitWeight p x.1 * bitWeight p x.2.1 * bitWeight p x.2.2

lemma bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin 2) : 0 ≤ bitWeight p x := by
  fin_cases x
  · simpa using hp1
  · simpa using hp0

lemma indepWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : FlipPattern) :
    0 ≤ indepWeight p x :=
  mul_nonneg (mul_nonneg (bitWeight_nonneg hp0 hp1 _) (bitWeight_nonneg hp0 hp1 _))
    (bitWeight_nonneg hp0 hp1 _)

/-- The pattern weights sum to `1`: `((1 − p) + p)³ = 1`. -/
lemma sum_indepWeight (p : ℝ) : ∑ x : FlipPattern, indepWeight p x = 1 := by
  simp only [indepWeight, Fintype.sum_prod_type, Fin.sum_univ_two, bitWeight_zero, bitWeight_one]
  ring

/-! ### The independent bit-flip channel -/

/-- **The independent bit-flip channel** on the register: each qubit flips independently with
probability `p`; `ρ ↦ ∑ₓ w_p(x) Xˣ ρ Xˣ`. -/
noncomputable def indepFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) FlipPattern :=
  Channel.mixedUnitaryChannel flipOp flipOp_conjTranspose_mul_self (indepWeight p)
    (indepWeight_nonneg hp0 hp1) (sum_indepWeight p)

lemma indepFlipChannel_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    (indepFlipChannel p hp0 hp1).apply ρ
      = ∑ x, ((indepWeight p x : ℝ) : ℂ) • (flipOp x * ρ * flipOp x) := by
  rw [indepFlipChannel, Channel.mixedUnitaryChannel_apply]
  simp only [flipOp_conjTranspose]

/-! ### The logical flip, and how each pattern reads to the syndrome -/

/-- The logical bit-flip `X̄ = X ⊗ X ⊗ X`, which swaps `|000⟩` and `|111⟩`. -/
noncomputable def logicalX : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  kron3 pX pX pX

lemma logicalX_mul_self : logicalX * logicalX = 1 := by
  rw [logicalX, kron3_mul, pX_mul_pX, kron3_one]

lemma logicalX_conjTranspose : logicalXᴴ = logicalX := by
  rw [logicalX, kron3_conjTranspose, pX_conjTranspose]

lemma pX_mul_q0 : pX * q0 = q1 * pX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pX, q0, q1, Matrix.mul_apply, Fin.sum_univ_two]

lemma pX_mul_q1 : pX * q1 = q0 * pX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pX, q0, q1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The logical flip preserves the code space: `X̄ P₀ = P₀ X̄`. -/
lemma logicalX_mul_codeProj : logicalX * codeProj = codeProj * logicalX := by
  rw [codeProj, logicalX, Matrix.mul_add, Matrix.add_mul, kron3_mul, kron3_mul, kron3_mul,
    kron3_mul, pX_mul_q0, pX_mul_q1, add_comm]

lemma codeProj_mul_logicalX : codeProj * logicalX = logicalX * codeProj :=
  logicalX_mul_codeProj.symm

/-- `X̄ ρ X̄` is code-supported when `ρ` is. -/
lemma codeProj_conj_logicalX (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    codeProj * (logicalX * ρ * logicalX) * codeProj = logicalX * ρ * logicalX := by
  calc codeProj * (logicalX * ρ * logicalX) * codeProj
      = (codeProj * logicalX) * ρ * (logicalX * codeProj) := by simp only [Matrix.mul_assoc]
    _ = (logicalX * codeProj) * ρ * (codeProj * logicalX) := by
        rw [codeProj_mul_logicalX, logicalX_mul_codeProj]
    _ = logicalX * (codeProj * ρ * codeProj) * logicalX := by simp only [Matrix.mul_assoc]
    _ = logicalX * ρ * logicalX := by rw [hρ]

/-- Every single error commutes with the logical flip. -/
lemma errorOp_mul_logicalX (k : Fin 4) : errorOp k * logicalX = logicalX * errorOp k := by
  fin_cases k <;> simp [errorOp, X1, X2, X3, logicalX, kron3_mul]

/-- The number of flipped qubits in a pattern. -/
def flipCount (x : FlipPattern) : ℕ := x.1.val + x.2.1.val + x.2.2.val

/-- The single-error label the syndrome assigns to a pattern: the flipped qubit for weight one,
the *unflipped* qubit for weight two (the code mis-corrects it), `0` for weights zero and three. -/
def singleIdx (x : FlipPattern) : Fin 4 :=
  ![![![0, 3], ![2, 1]], ![![1, 2], ![3, 0]]] x.1 x.2.1 x.2.2

/-- **How the syndrome reads a pattern**: `Xˣ = E_{k(x)}` for weight `≤ 1` and
`Xˣ = E_{k(x)} X̄` for weight `≥ 2`. -/
lemma flipOp_eq (x : FlipPattern) :
    flipOp x = errorOp (singleIdx x) * (if flipCount x ≤ 1 then 1 else logicalX) := by
  obtain ⟨a, b, c⟩ := x
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [flipOp, singleIdx, flipCount, errorOp, X1, X2, X3, logicalX, kron3_mul, kron3_one]

/-! ### Recovery, pattern by pattern -/

/-- Recovery undoes any single error on a code-supported operator. -/
lemma recoveryChannel_apply_errorOp (k : Fin 4)
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    recoveryChannel.apply (errorOp k * ρ * errorOp k) = ρ := by
  conv_lhs => rw [← hρ]
  rw [Channel.apply_def]
  simp only [recoveryChannel_kraus, Matrix.conjTranspose_mul, syndromeProj_conjTranspose,
    errorOp_conjTranspose, recovery_term, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact hρ

/-- **Recovery on one pattern**: the input for weight `≤ 1`, the logically flipped input for
weight `≥ 2`. -/
theorem recoveryChannel_apply_flipOp (x : FlipPattern)
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    recoveryChannel.apply (flipOp x * ρ * flipOp x)
      = if flipCount x ≤ 1 then ρ else logicalX * ρ * logicalX := by
  rw [flipOp_eq]
  split_ifs with h
  · rw [Matrix.mul_one]
    exact recoveryChannel_apply_errorOp _ ρ hρ
  · have hc : errorOp (singleIdx x) * logicalX * ρ * (errorOp (singleIdx x) * logicalX)
        = errorOp (singleIdx x) * (logicalX * ρ * logicalX) * errorOp (singleIdx x) := by
      calc errorOp (singleIdx x) * logicalX * ρ * (errorOp (singleIdx x) * logicalX)
          = errorOp (singleIdx x) * logicalX * ρ * (logicalX * errorOp (singleIdx x)) := by
            rw [errorOp_mul_logicalX]
        _ = errorOp (singleIdx x) * (logicalX * ρ * logicalX) * errorOp (singleIdx x) := by
            simp only [Matrix.mul_assoc]
    rw [hc]
    exact recoveryChannel_apply_errorOp _ _ (codeProj_conj_logicalX ρ hρ)

/-! ### The failure probability -/

/-- The logical failure probability of the three-qubit code under independent flips:
`3p² − 2p³`, the weight of the patterns with at least two flips. -/
noncomputable def failProb (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

/-- The code helps exactly below `p = 1/2`: `p_fail < p` for `0 < p < 1/2`. -/
lemma failProb_lt_of_lt_half {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) : failProb p < p := by
  rw [failProb]
  nlinarith [mul_pos hp0 hp0, mul_pos (mul_pos hp0 hp0) (sub_pos.2 hp)]

/-- ★★ **Syndrome recovery on independent bit-flip noise, on the code**: for every
code-supported `ρ` (`P₀ ρ P₀ = ρ`), `R (N_p ρ) = (1 − p_fail) ρ + p_fail X̄ ρ X̄` with
`p_fail = 3p² − 2p³` — the recovered state is the input with probability `1 − 3p² + 2p³` and the
logically flipped input otherwise. -/
theorem recoveryChannel_apply_indepFlipChannel_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    recoveryChannel.apply ((indepFlipChannel p hp0 hp1).apply ρ)
      = ((1 - failProb p : ℝ) : ℂ) • ρ + ((failProb p : ℝ) : ℂ) • (logicalX * ρ * logicalX) := by
  rw [indepFlipChannel_apply, Channel.apply_def]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_comm]
  have h : ∀ x : FlipPattern, ∑ j, ((indepWeight p x : ℝ) : ℂ)
      • (recoveryChannel.kraus j * (flipOp x * ρ * flipOp x) * (recoveryChannel.kraus j)ᴴ)
      = ((indepWeight p x : ℝ) : ℂ) • (if flipCount x ≤ 1 then ρ else logicalX * ρ * logicalX) := by
    intro x
    rw [← Finset.smul_sum, ← Channel.apply_def, recoveryChannel_apply_flipOp x ρ hρ]
  simp only [h]
  simp only [indepWeight, Fintype.sum_prod_type, Fin.sum_univ_two, bitWeight_zero,
    bitWeight_one, flipCount, Fin.val_zero, Fin.val_one, failProb]
  norm_num
  match_scalars <;> ring

end QEC
end QM
end Empirical
end CSD

end
