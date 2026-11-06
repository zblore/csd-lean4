/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneTransversalCNOT

/-!
# The logical phase gate `S̄` on the Steane code

**Category:** 3-Local (Empirical, QM twin). BACKLOG #230, first brick (the logical `S̄` the row
was stuck on).

The transversal phase gate `S^{⊗7}`, `S = diag(1, i)`, multiplies a basis label `z` by `i^{|z|}`.
The logical `|0̄⟩` is the uniform superposition over the row space of the Hamming code, whose words
have weight `0` or `4`; the logical `|1̄⟩` is the same over the coset of the all-ones word, weights
`3` or `7`. So the phase is `1` on `|0̄⟩` and `i³ = −i` on `|1̄⟩`: **the transversal `S` is the
logical `S†`**, exactly, with no global phase, and the transversal `S†` is the logical `S`.

* `sGateM`, `sDagM` — `diag(1, i)` and `diag(1, −i)`; `sTransversal` — `S^{⊗7}`;
* `hamWt`, `hamWt_coset_mod_four` — **the weights of the code's words, mod `4`**: `0` on the row
  space, `3` on its all-ones coset (by `decide`, over the sixteen words);
* `sTransversal_apply` — `S^{⊗7}` is diagonal with entries `i^{|z|}`;
* ★★ `sTransversal_mul_steaneEnc` — **`S^{⊗7} E = E S†`**, the Schrödinger-picture statement;
  ★★ `sTransversal_conjTranspose_mul_steaneEnc` — **`(S^{⊗7})† E = E S`**: the transversal `S†` is
  the logical `S`;
* `sTransversal_mul_steaneProj` / `sTransversal_conjTranspose_mul_steaneProj` — **both keep the
  code** — are in `SteaneMachineConcat.lean`, next to `steaneProj_eq`, which this module now
  precedes (#303).

## Honest scope

⚠️ Level one. At the concatenated level the transversal gate alternates between `S` and `S†` from
one level to the next; `SteaneMachineConcat.lean` handles that with its `ConcatGadget.logical` map
and puts both in the level-`k` machine (#303). `S̄` is not in the one-block level-one `Gadget` type;
it is in the two-block gadget set of `SteanePairMachine.lean`.

References: D. Gottesman, PhD thesis (Caltech 1997) §5; M. Nielsen, I. Chuang, *Quantum Computation
and Quantum Information* §10.6.2; `specs/BACKLOG.md` #230, #303;
`Empirical/QM/QEC/SteaneMachineConcat.lean`, `Empirical/QM/QEC/SteaneTransversalCNOT.lean`
(`steaneEnc_eq_cosetAmp`);
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-- The phase gate `S = diag(1, i)`. -/
def sGateM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

/-- Its inverse `S† = diag(1, −i)`. -/
def sDagM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -Complex.I]

theorem sGateM_conjTranspose : sGateMᴴ = sDagM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sGateM, sDagM]

theorem sDagM_mul_conjTranspose : sDagM * sDagMᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sDagM, Matrix.mul_apply, Fin.sum_univ_two]

theorem sGateM_conjTranspose_mul : sGateMᴴ * sGateM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sGateM, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transversal phase gate `S^{⊗7}` on a Steane block. -/
def sTransversal : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ := blockKron fun _ : Fin 7 => sGateM

theorem sTransversal_conjTranspose_mul : sTransversalᴴ * sTransversal = 1 := by
  rw [sTransversal, blockKron_conjTranspose, blockKron_mul]
  simp only [sGateM_conjTranspose_mul]
  exact blockKron_one

/-! ### The weights of the code's words -/

/-- The Hamming weight of a label. -/
def hamWt (z : Fin 7 → Fin 2) : ℕ := (Finset.univ.filter fun q => z q = 1).card

/-- **The weights mod `4`**: the row space has weights `0` and `4`, its all-ones coset `3` and
`7`. -/
theorem hamWt_coset_mod_four :
    ∀ (c : Fin 3 → Fin 2) (y : Fin 2),
      hamWt (rowComb c + constVec y) % 4 = if y = 0 then 0 else 3 := by
  decide

theorem I_pow_eq_pow_mod_four (n : ℕ) : Complex.I ^ n = Complex.I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-! ### The transversal `S` on the encoder -/

theorem sGateM_apply_self (a : Fin 2) : sGateM a a = if a = 1 then Complex.I else 1 := by
  fin_cases a <;> simp [sGateM]

/-- `S^{⊗7}` is diagonal, with entry `i^{|z|}` at `z`. -/
theorem sTransversal_apply (z w : Fin 7 → Fin 2) :
    sTransversal z w = if z = w then Complex.I ^ hamWt z else 0 := by
  rw [sTransversal, blockKron_apply]
  by_cases h : z = w
  · subst h
    rw [ite_eq_left rfl]
    simp only [sGateM_apply_self]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hamWt]
  · rw [ite_eq_right h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    have hoff : ∀ a b : Fin 2, a ≠ b → sGateM a b = 0 := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [sGateM]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (hoff _ _ hq)

/-- The phase `i^{|z|}` on the support of the encoder's column `y` is `S†`'s entry. -/
theorem I_pow_hamWt_mul_steaneEnc (z : Fin 7 → Fin 2) (y : Fin 2) :
    Complex.I ^ hamWt z * steaneEnc z y = steaneEnc z y * sDagM y y := by
  by_cases h : cosetAmp y z = 0
  · rw [steaneEnc_eq_cosetAmp z y, h]
    ring
  · obtain ⟨c, hc⟩ : ∃ c : Fin 3 → Fin 2, z = rowComb c + constVec y := by
      by_contra hcon
      refine h ?_
      rw [cosetAmp]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [ite_eq_right fun hcc => hcon ⟨c, hcc⟩]
    rw [I_pow_eq_pow_mod_four, hc, hamWt_coset_mod_four c y, mul_comm]
    fin_cases y
    · simp [sDagM]
    · simp [sDagM, pow_succ, Complex.I_mul_I]

/-- ★★ **`S^{⊗7} E = E S†`**: the transversal phase gate is the logical `S†`, exactly. -/
theorem sTransversal_mul_steaneEnc : sTransversal * steaneEnc = steaneEnc * sDagM := by
  ext z y
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [sTransversal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [I_pow_hamWt_mul_steaneEnc]
  fin_cases y <;> simp [sDagM]

/-- ★★ **`(S^{⊗7})† E = E S`**: the transversal `S†` is the logical `S`. -/
theorem sTransversal_conjTranspose_mul_steaneEnc :
    sTransversalᴴ * steaneEnc = steaneEnc * sGateM := by
  calc sTransversalᴴ * steaneEnc = sTransversalᴴ * steaneEnc * (sDagM * sDagMᴴ) := by
        rw [sDagM_mul_conjTranspose, Matrix.mul_one]
    _ = sTransversalᴴ * (steaneEnc * sDagM) * sDagMᴴ := by simp only [Matrix.mul_assoc]
    _ = sTransversalᴴ * (sTransversal * steaneEnc) * sDagMᴴ := by rw [sTransversal_mul_steaneEnc]
    _ = steaneEnc * sDagMᴴ := by
        rw [← Matrix.mul_assoc, sTransversal_conjTranspose_mul, Matrix.one_mul]
    _ = steaneEnc * sGateM := by
        rw [← sGateM_conjTranspose, conjTranspose_conjTranspose]

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
