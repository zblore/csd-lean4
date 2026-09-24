/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ReedMuller15Code
public import CsdLean4.Mathlib.QuantumInfo.Stabilizer

/-!
# `Z`-error patterns on the encoded magic state: detection and the logical `Z̄`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #77, part (c) of `R-004`
(`specs/magic-plan.md`, "The split").

The 15-to-1 protocol injects `T` (BACKLOG #66–#67) into each qubit of the encoded `|+̄⟩`; a noisy
resource leaves a `Z`-error pattern `e ∈ 𝔽₂¹⁵` on the encoded magic state
`|Ā'⟩ = T^{⊗15}|+̄⟩ = |0̄⟩ + e^{−iπ/4}|1̄⟩` (`tTrans_logicalPlus`), i.e. the state `Z_e |Ā'⟩`. The
`X`-checks `X^{row i}` are then measured:

* `Z_e` commutes with `X^{row i}` up to the sign `(−1)^{(syndrome e)ᵢ}` (`pauliOp_z_comm_row`), so
  on any state fixed by the checks the measurement of check `i` is **deterministic with outcome
  `(syndrome e)ᵢ`** (★ `measProj_row_z`): a pattern with nonzero syndrome is rejected with certainty
  (`exists_reject_of_syndrome_ne_zero`), a pattern with zero syndrome passes every check;
* an undetected pattern acts on the code space as the logical `Z̄` to the power of its parity:
  `Z_e|0̄⟩ = |0̄⟩` and `Z_e|1̄⟩ = (−1)^{|e|}|1̄⟩` (`pauliOp_z_logical0/1`, from `bdot_codeword` — a
  pattern orthogonal to the rows is orthogonal to the code — and `bdot e 𝟙 = |e| mod 2`,
  `parity_val`, `parity_eq_one_iff_odd`); ★★ `pauliOp_z_encodedMagic`: **the accepted state is
  `|0̄⟩ + (−1)^{|e|} e^{−iπ/4}|1̄⟩`**, the encoded `T†|+⟩` for even `|e|` and its logical `Z̄`-flip for
  odd `|e|`;
* reading the logical coefficients as a qubit (`outQubit e`), the output is `√2 · T†|+⟩` for even
  `|e|` and `√2 · Z T†|+⟩` for odd `|e|` (`outQubit_eq`, `magicConj`), and `S T†|+⟩ = |A⟩`
  (`sGate_magicConj`): the protocol distils the magic state up to the Clifford `S`.

`syndromeF` (on `Fin 2` labels) agrees with `ReedMuller15.syndrome` (`syndromeF_eq`), so the
counts of `ReedMuller15.lean` apply: no undetected pattern of weight `1` or `2`, exactly `35` of
weight `3`, `2¹¹` in all.

## Honest scope

⚠️ The output is read off the logical coefficients; the explicit Clifford decoding circuit is
BACKLOG #79. The probabilities over the pattern under independent noise, and the `35 p³` bound, are
BACKLOG #78.

References: S. Bravyi, A. Kitaev, PRA 71 (2005) 022316 §IV; `specs/magic-plan.md`;
`specs/BACKLOG.md` #77; `specs/future-work.md`.
-/

@[expose] public section

open Finset
open scoped ComplexConjugate

namespace QuantumInfo

namespace ReedMuller15

/-! ### The syndrome on `Fin 2` labels -/

/-- The `X`-check syndrome of a `Z`-pattern: `(syndrome e)ᵢ = e · row i`. -/
def syndromeF (e : Fin 15 → Fin 2) : Fin 4 → Fin 2 := fun i => bdot e (row i)

/-- The parity `e · 𝟙 = |e| mod 2` of a pattern. -/
def parity (e : Fin 15 → Fin 2) : Fin 2 := bdot e 1

/-- The rows are the columns of `ReedMuller15.lean` (`ZMod 2` is `Fin 2`). -/
theorem col_eq_row (j : Fin 15) (i : Fin 4) : _root_.ReedMuller15.col j i = (row i j : ZMod 2) :=
  rfl

/-- The `Fin 2` syndrome is the `ZMod 2` syndrome of `ReedMuller15.lean`, definitionally. -/
theorem syndromeF_eq (e : Fin 15 → Fin 2) : syndromeF e = _root_.ReedMuller15.syndrome e :=
  rfl

theorem parity_cast (e : Fin 15 → Fin 2) : (parity e : ZMod 2) = ((wt e : ℕ) : ZMod 2) := by
  rw [parity, wt_eq_sum, Nat.cast_sum, bdot]
  refine sum_congr rfl fun j _ => ?_
  rw [Pi.one_apply, mul_one]
  exact (ZMod.natCast_zmod_val (n := 2) (e j)).symm

/-- `e · 𝟙` is the weight mod `2`. -/
theorem parity_val (e : Fin 15 → Fin 2) : (parity e).val = wt e % 2 := by
  have h := congrArg (ZMod.val (n := 2)) (parity_cast e)
  rw [ZMod.val_natCast] at h
  exact h

/-- The parity is `1` exactly for odd weight. -/
theorem parity_eq_one_iff_odd (e : Fin 15 → Fin 2) : parity e = 1 ↔ Odd (wt e) := by
  rw [Fin.ext_iff, parity_val, Nat.odd_iff]
  rfl

/-! ### `Z_e` against the `X`-checks -/

/-- `Z_e |x⟩ = (−1)^{e · x} |x⟩`. -/
theorem pauliOp_basisState_z (e x : Fin 15 → Fin 2) :
    pauliOp 0 e (basisState x) = pauliSign e x • basisState x := by
  ext z
  rw [pauliOp_apply, add_zero, PiLp.smul_apply, smul_eq_mul, basisState_apply]
  by_cases h : z = x
  · rw [h]
  · rw [if_neg h, mul_zero, mul_zero]

/-- `Z_e X^{row i} = (−1)^{(syndrome e)ᵢ} X^{row i} Z_e`. -/
theorem pauliOp_z_comm_row (e : Fin 15 → Fin 2) (i : Fin 4) (ψ : QReg 15) :
    pauliOp (row i) 0 (pauliOp 0 e ψ)
      = signChar (syndromeF e i) • pauliOp 0 e (pauliOp (row i) 0 ψ) := by
  rw [pauliOp_comm, bdot_zero_right, add_zero, syndromeF, bdot_comm]

/-- ★ **The `X`-check `i` on `Z_e ψ̄` is deterministic with outcome `(syndrome e)ᵢ`**, for any `ψ̄`
fixed by `X^{row i}`. -/
theorem measProj_row_z (e : Fin 15 → Fin 2) (i : Fin 4) {ψ : QReg 15}
    (hfix : pauliOp (row i) 0 ψ = ψ) :
    measProj (row i) 0 (syndromeF e i) (pauliOp 0 e ψ) = pauliOp 0 e ψ
      ∧ measProj (row i) 0 (syndromeF e i + 1) (pauliOp 0 e ψ) = 0 := by
  apply meas_deterministic
  rw [pauliOp_z_comm_row, hfix, smul_smul, signChar_mul_self, one_smul]

theorem fin2_add_one_eq_zero_of_ne_zero {v : Fin 2} (h : v ≠ 0) : v + 1 = 0 := by
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) v with h0 | h0
  · exact absurd h0 h
  · rw [h0]
    rfl

/-- **A detected pattern is rejected with certainty**: some `X`-check has zero amplitude for the
`+1` outcome. -/
theorem exists_reject_of_syndrome_ne_zero {e : Fin 15 → Fin 2} (he : syndromeF e ≠ 0)
    {ψ : QReg 15} (hfix : ∀ i, pauliOp (row i) 0 ψ = ψ) :
    ∃ i, measProj (row i) 0 0 (pauliOp 0 e ψ) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, syndromeF e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  refine ⟨i, ?_⟩
  have h := (measProj_row_z e i (hfix i)).2
  rwa [fin2_add_one_eq_zero_of_ne_zero hi] at h

/-- **An undetected pattern passes every `X`-check with certainty.** -/
theorem measProj_row_z_zero {e : Fin 15 → Fin 2} (he : syndromeF e = 0) (i : Fin 4)
    {ψ : QReg 15} (hfix : pauliOp (row i) 0 ψ = ψ) :
    measProj (row i) 0 0 (pauliOp 0 e ψ) = pauliOp 0 e ψ := by
  have h := (measProj_row_z e i hfix).1
  rwa [he, Pi.zero_apply] at h

/-! ### Undetected patterns act as the logical `Z̄^{parity}` -/

theorem bdot_codeword (e : Fin 15 → Fin 2) (a : Fin 4 → Fin 2) :
    bdot e (codeword a) = ∑ i, a i * bdot e (row i) := by
  unfold bdot codeword
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_left_comm _ _ _

/-- A pattern orthogonal to the rows is orthogonal to the code. -/
theorem bdot_codeword_eq_zero {e : Fin 15 → Fin 2} (he : syndromeF e = 0) (a : Fin 4 → Fin 2) :
    bdot e (codeword a) = 0 := by
  rw [bdot_codeword]
  refine sum_eq_zero fun i _ => ?_
  rw [show bdot e (row i) = 0 from congrFun he i, mul_zero]

/-- ★ An undetected `Z`-pattern fixes `|0̄⟩`. -/
theorem pauliOp_z_logical0 {e : Fin 15 → Fin 2} (he : syndromeF e = 0) :
    pauliOp 0 e logical0 = logical0 := by
  rw [logical0, pauliOp_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [pauliOp_basisState_z, pauliSign, bdot_codeword_eq_zero he, signChar_zero, one_smul]

/-- ★ An undetected `Z`-pattern multiplies `|1̄⟩` by `(−1)^{|e|}`. -/
theorem pauliOp_z_logical1 {e : Fin 15 → Fin 2} (he : syndromeF e = 0) :
    pauliOp 0 e logical1 = signChar (parity e) • logical1 := by
  rw [logical1, pauliOp_sum, smul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [pauliOp_basisState_z, pauliSign, bdot_add_right, bdot_codeword_eq_zero he, zero_add, parity]

/-- The encoded magic state is fixed by every `X`-check. -/
theorem pauliOp_row_tTrans_logicalPlus (i : Fin 4) :
    pauliOp (row i) 0 (tTrans logicalPlus) = tTrans logicalPlus := by
  rw [tTrans_logicalPlus, pauliOp_add, pauliOp_smul, pauliOp_row_logical0, pauliOp_row_logical1]

/-- ★★ **The accepted state**: an undetected pattern `e` turns the encoded magic state into
`|0̄⟩ + (−1)^{|e|} e^{−iπ/4}|1̄⟩` — the encoded `T†|+⟩` for even `|e|`, its logical `Z̄`-flip for odd. -/
theorem pauliOp_z_encodedMagic {e : Fin 15 → Fin 2} (he : syndromeF e = 0) :
    pauliOp 0 e (tTrans logicalPlus) = logical0 + (signChar (parity e) * tPhaseInv) • logical1 := by
  rw [tTrans_logicalPlus, pauliOp_add, pauliOp_smul, pauliOp_z_logical0 he, pauliOp_z_logical1 he,
    smul_smul, mul_comm]

/-! ### The decoded output -/

/-- The conjugate magic state `T†|+⟩ = T† H |0⟩`. -/
noncomputable def magicConj : QReg 1 := tGateInv 0 (hGate 0 (basisState (fun _ => 0)))

/-- `S T†|+⟩ = |A⟩`: the distilled state is the magic state up to the Clifford `S`. -/
theorem sGate_magicConj : sGate 0 magicConj = magicState := by
  rw [magicConj, magicState, ← tGate_tGate, tGate_tGateInv]

theorem magicConj_apply (z : Fin 1 → Fin 2) :
    magicConj z = (Real.sqrt 2 : ℂ)⁻¹ * tPhaseInv ^ ((z 0 : Fin 2) : ℕ) := by
  rw [magicConj, tGateInv_apply, hGate_apply, Fin.sum_univ_two]
  rw [show (Function.update z 0 0 : Fin 1 → Fin 2) = (fun _ => 0) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    show (Function.update z 0 1 : Fin 1 → Fin 2) = (fun _ => 1) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    basisState_apply, basisState_apply, if_pos rfl,
    if_neg (by intro hc; exact absurd (congrFun hc 0) (by decide))]
  simp only [mul_zero, mul_one, add_zero, signChar_zero]
  ring

/-- The logical coefficients of the accepted state, read as one qubit:
`|0⟩ + (−1)^{|e|} e^{−iπ/4}|1⟩`. -/
noncomputable def outQubit (e : Fin 15 → Fin 2) : QReg 1 :=
  basisState (fun _ => 0) + (signChar (parity e) * tPhaseInv) • basisState (fun _ => 1)

/-- `Z^s` on one qubit. -/
noncomputable def zPow (s : Fin 2) (ψ : QReg 1) : QReg 1 :=
  if s = 0 then ψ else pauliOp 0 (unitV 0) ψ

/-- ★ **The output is `√2 · Z^{|e|} T†|+⟩`**: the conjugate magic state for even `|e|`, its
`Z`-flip for odd `|e|`. -/
theorem outQubit_eq (e : Fin 15 → Fin 2) :
    outQubit e = (Real.sqrt 2 : ℂ) • zPow (parity e) magicConj := by
  ext z
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = 1 := by
    rw [mul_inv_cancel₀]
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [outQubit, zPow, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    basisState_apply, basisState_apply]
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (parity e) with hp | hp <;>
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (z 0) with hz | hz
  · rw [hp, if_pos rfl, magicConj_apply, hz, if_pos (funext fun i => by rw [Subsingleton.elim i 0, hz]),
      if_neg (by intro hc; exact absurd ((congrFun hc 0).symm.trans hz) (by decide))]
    simp only [signChar_zero, one_mul, Fin.isValue, Fin.val_zero, pow_zero, mul_one, mul_zero,
      add_zero]
    exact hsq.symm
  · rw [hp, if_pos rfl, magicConj_apply, hz, if_neg (by intro hc; exact absurd ((congrFun hc 0).symm.trans hz) (by decide)),
      if_pos (funext fun i => by rw [Subsingleton.elim i 0, hz])]
    simp only [signChar_zero, one_mul, Fin.isValue, Fin.val_one, pow_one, mul_one, zero_add]
    rw [← mul_assoc, hsq, one_mul]
  · rw [hp, if_neg (show ¬ ((1 : Fin 2) = 0) by decide), pauliOp_apply, add_zero, pauliSign, bdot_unitV, magicConj_apply, hz,
      if_pos (funext fun i => by rw [Subsingleton.elim i 0, hz]),
      if_neg (by intro hc; exact absurd ((congrFun hc 0).symm.trans hz) (by decide))]
    simp only [signChar_zero, one_mul, Fin.isValue, Fin.val_zero, pow_zero, mul_one, mul_zero,
      add_zero]
    exact hsq.symm
  · rw [hp, if_neg (show ¬ ((1 : Fin 2) = 0) by decide), pauliOp_apply, add_zero, pauliSign, bdot_unitV, magicConj_apply, hz,
      if_neg (by intro hc; exact absurd ((congrFun hc 0).symm.trans hz) (by decide)),
      if_pos (funext fun i => by rw [Subsingleton.elim i 0, hz])]
    simp only [Fin.isValue, Fin.val_one, pow_one, mul_one, zero_add]
    rw [show signChar 1 = -1 from rfl]
    linear_combination tPhaseInv * hsq

end ReedMuller15

end QuantumInfo

end
