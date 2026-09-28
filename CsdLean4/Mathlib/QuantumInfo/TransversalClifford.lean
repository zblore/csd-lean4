/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.StabilizerRecovery
public import CsdLean4.Mathlib.QuantumInfo.BlockKron
public import CsdLean4.Mathlib.QuantumInfo.CliffordTDensity

/-!
# Transversal Cliffords: a Pauli string factorises, and the transversal Hadamard swaps `X` and `Z`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #62 (b), the general half.

A Pauli string is a **tensor product over the qubits** — which is obvious on paper and needs saying
once in Lean, because `pauliMat a b` is defined by its entries and `blockKron` by a product over the
blocks. Once said, the conjugation rule of a **transversal** gate is the single-qubit rule raised to
the tensor power, and that is the whole mechanism of transversality.

* `onePauli u v` — the single-qubit Pauli `X^u Z^v`, and ★★ `pauliMat_eq_blockKron`:
  `pauliMat a b = ⨂ᵢ onePauli (aᵢ) (bᵢ)`;
* `hGateM_mul_onePauli` and ★ `hGateM_conj_onePauli` — `H X^u Z^v H = (−1)^{uv} X^v Z^u`, the
  four cases of `H X H = Z`, `H Z H = X`;
* `hadTransversal n` — the Hadamard on every qubit, with `hadTransversal_mul_self` and
  `hadTransversal_conjTranspose` (it is its own inverse and Hermitian);
* ★★ `hadTransversal_conj_pauliMat` — **the transversal Hadamard exchanges the `X`- and `Z`-labels
  of every Pauli string**: `H^{⊗n} X^a Z^b H^{⊗n} = (−1)^{a·b} X^b Z^a`. For a CSS code, where
  `a · b = 0` on the stabiliser labels, the sign is `1` and the group is preserved — which is what
  the consumer (`Empirical/QM/QEC/SteaneFaultyGate.lean`) spends it on.

## Honest scope

⚠️ Nothing here is about a *code*: these are identities in the Pauli group and its normaliser. That
a particular transversal gate preserves a particular code space is the code's business, and needs
the code's labels (for the Steane code, the CSS condition `bdot_rowComb_rowComb`).

⚠️ The Schrödinger-picture action of a transversal gate on encoded *states* is not here. What the
conjugation rule gives is the Heisenberg picture: where the logical Paulis go.

References: M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information* §10.4.2
(transversal gates), §10.5.8; A. Steane, PRL 77 (1996); `specs/BACKLOG.md` #62;
`specs/steane-plan.md`; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

open CliffordT SU2

variable {n : ℕ}

/-! ### A Pauli string is a tensor product over the qubits -/

/-- The single-qubit Pauli `X^u Z^v`: it moves `|w⟩` to `|w + u⟩` and signs it by `(−1)^{v w}`. -/
def onePauli (u v : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun z w => if w = z + u then signChar (v * w) else 0

theorem onePauli_apply (u v z w : Fin 2) :
    onePauli u v z w = if w = z + u then signChar (v * w) else 0 := rfl

/-- ★★ **A Pauli string is the tensor product of its single-qubit Paulis.** -/
theorem pauliMat_eq_blockKron (a b : Fin n → Fin 2) :
    pauliMat a b = blockKron fun i => onePauli (a i) (b i) := by
  ext z w
  rw [blockKron_apply, pauliMat]
  by_cases h : w = z + a
  · rw [if_pos h, Finset.prod_congr rfl fun i _ =>
      (by rw [onePauli_apply, if_pos (show w i = z i + a i by rw [h]; rfl)] :
        onePauli (a i) (b i) (z i) (w i) = signChar (b i * w i)), ← signChar_sum]
    rfl
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ z i + a i := by
      by_contra hc
      have hall : ∀ i, w i = z i + a i := fun i => by
        by_contra hci
        exact hc ⟨i, hci⟩
      exact h (funext fun i => by rw [hall i]; rfl)
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [onePauli_apply, if_neg hi]

/-! ### The single-qubit Hadamard on a Pauli -/

/-- `H X^u Z^v = (−1)^{uv} X^v Z^u H`: the Hadamard moved across a Pauli, with one factor of `H` on
each side, so the `√2` never has to be squared. -/
theorem hGateM_mul_onePauli (u v : Fin 2) :
    hGateM * onePauli u v = (signChar (u * v) • onePauli v u) * hGateM := by
  fin_cases u <;> fin_cases v <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hGateM, onePauli, signChar, Matrix.mul_apply, Fin.sum_univ_two]

/-- ★ **`H X^u Z^v H = (−1)^{uv} X^v Z^u`** — the four cases `H I H = I`, `H X H = Z`,
`H Z H = X`, `H (XZ) H = −XZ`. -/
theorem hGateM_conj_onePauli (u v : Fin 2) :
    hGateM * onePauli u v * hGateM = signChar (u * v) • onePauli v u := by
  rw [hGateM_mul_onePauli, mul_assoc, hGateM_mul_self, mul_one]

/-! ### The transversal Hadamard -/

/-- The **transversal Hadamard**: the Hadamard on every one of the `n` qubits. -/
noncomputable def hadTransversal (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  blockKron fun _ : Fin n => hGateM

theorem hadTransversal_mul_self : hadTransversal n * hadTransversal n = 1 := by
  rw [hadTransversal, blockKron_mul,
    show (fun _ : Fin n => hGateM * hGateM) = fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ) from
      funext fun _ => hGateM_mul_self,
    blockKron_one]

theorem hGateM_conjTranspose : hGateMᴴ = hGateM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hGateM, Matrix.conjTranspose_apply, Complex.conj_ofReal]

theorem hadTransversal_conjTranspose : (hadTransversal n)ᴴ = hadTransversal n := by
  rw [hadTransversal, blockKron_conjTranspose,
    show (fun _ : Fin n => hGateMᴴ) = fun _ : Fin n => hGateM from
      funext fun _ => hGateM_conjTranspose]

/-- ★★ **The transversal Hadamard exchanges the `X`- and `Z`-labels of a Pauli string**, with the
sign `(−1)^{a·b}`: the single-qubit rule raised to the tensor power. On a CSS code's stabiliser
labels `a · b = 0`, so the group is preserved elementwise. -/
theorem hadTransversal_conj_pauliMat (a b : Fin n → Fin 2) :
    hadTransversal n * pauliMat a b * hadTransversal n = signChar (bdot a b) • pauliMat b a := by
  rw [pauliMat_eq_blockKron, hadTransversal, blockKron_mul, blockKron_mul,
    show (fun i => hGateM * onePauli (a i) (b i) * hGateM)
        = fun i => signChar (a i * b i) • onePauli (b i) (a i) from
      funext fun i => hGateM_conj_onePauli (a i) (b i),
    blockKron_smul, ← signChar_sum, pauliMat_eq_blockKron]
  rfl

end QuantumInfo

end
