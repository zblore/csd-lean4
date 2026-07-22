/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Algorithms.DeutschJozsa
public import CsdLean4.Empirical.QM.Algorithms.Simon

/-!
# Bernstein–Vazirani

**Category:** 3-Local (QM-validity).

The Bernstein–Vazirani algorithm: given a phase oracle for the hidden **linear** function
`f_a(x) = a·x = ⟨a,x⟩ (mod 2)` with secret string `a ∈ {0,1}ⁿ`, recover `a` in a **single**
query. The circuit is the full Hadamard sandwich `H^⊗n ∘ U_f ∘ H^⊗n` on `|0ⁿ⟩`, with `U_f`
the phase oracle `|x⟩ ↦ (-1)^{⟨a,x⟩} |x⟩` (`bvOracle` / `applyBvUf`).

The output amplitude at outcome `y` is `(1/2ⁿ) ∑ₓ (-1)^{⟨y⊕a, x⟩}` (`bv_amplitude`), and the
character sum `∑ₓ (-1)^{⟨z,x⟩}` is `2ⁿ` if `z = 0` and `0` otherwise (`bitInner_char_sum`).
Hence the amplitude is the Kronecker delta `δ_{y,a}`:

* `bv_certain`: the outcome `y = a` is obtained with probability `1`;
* `bv_zero`: every other outcome has probability `0`.

One query recovers the hidden string `a` deterministically.

**Honest scope.** Unlike the single-register *reduced* Simon analysis, this **is** the full
phase-oracle circuit `H^⊗n ∘ U_f ∘ H^⊗n` (no second register, no measurement reduction, no
classical post-processing): `bv_amplitude` is the exact output amplitude vector. The only
modelling choice is the standard phase-oracle encoding of the linear `f_a` as a diagonal sign
matrix. The load-bearing new content is the `𝔽₂` character sum `bitInner_char_sum`, proved by
the per-qubit factorisation `(-1)^{∑ᵢ zᵢxᵢ} = ∏ᵢ (-1)^{zᵢxᵢ}` and the `∑∏ → ∏∑` swap
(`Finset.prod_univ_sum`), each factor collapsing to `2` (if `zᵢ = 0`) or `0` (if `zᵢ = 1`).

Reuses Simon's `bitInner` / `bxor` / `Hn_apply_inner` / `neg_one_bitInner_bxor` and
Deutsch–Jozsa's `inv_sqrt2_pow_mul`.
-/

@[expose] public section

open scoped ComplexConjugate
open QuantumInfo
open CSD.Empirical.QM.Simon
open CSD.Empirical.QM.DeutschJozsa

namespace CSD
namespace Empirical
namespace QM
namespace BernsteinVazirani

variable {n : ℕ}

/-- The **Bernstein–Vazirani phase oracle** `U_f : |x⟩ ↦ (-1)^{⟨a,x⟩} |x⟩` for the hidden
linear function `f_a(x) = a·x = bitInner a x (mod 2)`. -/
noncomputable def bvOracle (a : Fin n → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal (fun x => (-1) ^ (bitInner a x))

/-- The phase oracle's action on a register state. -/
noncomputable def applyBvUf (a : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  Matrix.toEuclideanLin (bvOracle a) ψ

lemma applyBvUf_apply (a : Fin n → Fin 2) (ψ : QReg n) (y : Fin n → Fin 2) :
    applyBvUf a ψ y = (-1) ^ (bitInner a y) * ψ y := by
  rw [applyBvUf, Matrix.toLpLin_apply]
  simp [bvOracle, Matrix.mulVec_diagonal]

/-- **The `𝔽₂` character sum** `∑ₓ (-1)^{⟨z,x⟩}` is `2ⁿ` if `z = 0` and `0` otherwise.
This is the load-bearing fact behind Bernstein–Vazirani: the per-qubit factorisation
`(-1)^{∑ᵢ zᵢxᵢ} = ∏ᵢ (-1)^{zᵢxᵢ}` plus the `∑∏ → ∏∑` swap gives `∏ᵢ (1 + (-1)^{zᵢ})`, with
each factor `2` (if `zᵢ = 0`) or `0` (if `zᵢ = 1`). -/
lemma bitInner_char_sum (z : Fin n → Fin 2) :
    (∑ x : Fin n → Fin 2, (-1 : ℂ) ^ (bitInner z x)) = if z = 0 then (2 : ℂ) ^ n else 0 := by
  have hpow : ∀ x : Fin n → Fin 2,
      (-1 : ℂ) ^ (bitInner z x) = ∏ i, ((-1 : ℂ)) ^ ((z i).val * (x i).val) := by
    intro x
    simp only [bitInner]
    rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [hpow]
  have hfac : (∑ x : Fin n → Fin 2, ∏ i, ((-1 : ℂ)) ^ ((z i).val * (x i).val))
      = ∏ i, ∑ b : Fin 2, ((-1 : ℂ)) ^ ((z i).val * b.val) := by
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
        (fun i b => ((-1 : ℂ)) ^ ((z i).val * b.val)), Fintype.piFinset_univ]
  rw [hfac]
  have hfacf : ∀ i, (∑ b : Fin 2, ((-1 : ℂ)) ^ ((z i).val * b.val))
      = if z i = 0 then (2 : ℂ) else 0 := by
    intro i
    rw [Fin.sum_univ_two, Fin.val_zero, mul_zero, pow_zero, Fin.val_one, mul_one]
    rcases (by decide : ∀ w : Fin 2, w = 0 ∨ w = 1) (z i) with h | h <;> rw [h] <;>
      norm_num [Fin.val_zero, Fin.val_one]
  simp_rw [hfacf]
  by_cases hz : z = 0
  · subst hz
    simp only [Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_neg (by simpa using hi)]

/-- `bxor y a = 0` over `𝔽₂` exactly when `y = a` (bitwise: `yᵢ + aᵢ = 0 ↔ yᵢ = aᵢ`). -/
lemma bxor_eq_zero_iff (y a : Fin n → Fin 2) : bxor y a = 0 ↔ y = a := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [bxor, Pi.zero_apply] at hi
    exact (by decide : ∀ b c : Fin 2, b + c = 0 → b = c) (y i) (a i) hi
  · intro h
    funext i
    simp only [bxor, Pi.zero_apply, h]
    exact (by decide : ∀ b : Fin 2, b + b = 0) (a i)

/-- The **Bernstein–Vazirani circuit** `H^⊗n ∘ U_f ∘ H^⊗n`. -/
noncomputable def bvCircuit (a : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  applyHn (applyBvUf a (applyHn ψ))

/-- **The output amplitude is the Kronecker delta `δ_{y,a}`.** Running the full circuit on
`|0ⁿ⟩` yields amplitude `1` at the hidden string `y = a` and `0` everywhere else. -/
theorem bv_amplitude (a y : Fin n → Fin 2) :
    bvCircuit a (basisState 0) y = if y = a then 1 else 0 := by
  rw [bvCircuit, applyHn_apply]
  have hterm : ∀ x : Fin n → Fin 2,
      Hn y x * applyBvUf a (applyHn (basisState 0)) x
        = ((2 : ℂ) ^ n)⁻¹ * (-1) ^ (bitInner (bxor y a) x) := by
    intro x
    rw [applyBvUf_apply, Hn_apply_zero, Hn_apply_inner, neg_one_bitInner_bxor y a x,
        div_eq_mul_inv, ← inv_pow]
    rw [show ((-1 : ℂ) ^ (bitInner y x) * ((Real.sqrt 2 : ℂ)⁻¹) ^ n)
          * ((-1) ^ (bitInner a x) * ((Real.sqrt 2 : ℂ)⁻¹) ^ n)
          = (((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n)
              * ((-1) ^ (bitInner y x) * (-1) ^ (bitInner a x)) from by ring]
    rw [inv_sqrt2_pow_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, bitInner_char_sum (bxor y a)]
  simp only [bxor_eq_zero_iff]
  by_cases h : y = a
  · rw [if_pos h, if_pos h, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Bernstein–Vazirani:** the hidden linear string `a` is measured with **certainty** after
one query. -/
theorem bv_certain (a : Fin n → Fin 2) : prob (bvCircuit a (basisState 0)) a = 1 := by
  rw [prob, bv_amplitude, if_pos rfl, norm_one, one_pow]

/-- **Bernstein–Vazirani:** every outcome other than the hidden string `a` has probability
`0`. -/
theorem bv_zero (a y : Fin n → Fin 2) (h : y ≠ a) :
    prob (bvCircuit a (basisState 0)) y = 0 := by
  rw [prob, bv_amplitude, if_neg h, norm_zero]
  norm_num

end BernsteinVazirani
end QM
end Empirical
end CSD
