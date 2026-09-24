/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ReedMuller15
public import CsdLean4.Mathlib.QuantumInfo.Magic

/-!
# The `[[15, 1, 3]]` code space and its transversal `T`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #76, part (b) of `R-004`
(`specs/magic-plan.md`, "The split").

The logical states of the `[[15, 1, 3]]` quantum Reed–Muller code, in the coordinate-operator model
of `Pauli.lean`/`Magic.lean` on `QReg 15`: `|0̄⟩ = ∑_{x ∈ C} |x⟩` and `|1̄⟩ = ∑_{x ∈ C} |x + 𝟙⟩`, with
`C` the `[15, 4]` simplex code spanned by the four rows of the parity-check matrix
(`ReedMuller15.col`), unnormalised (`‖·‖ = 4`). The `X`-stabilisers `X^{row i}` permute the
codewords and fix both logical states (`pauliOp_row_logical0/1`). Every codeword has weight `0`
or `8` and every word of the coset `C + 𝟙` has weight `7` or `15` (`weight_codeword`,
`weight_codeword_add_one`, finite checks), so the **transversal `T`**, `T^{⊗15}`, whose coordinate
action is `|x⟩ ↦ e^{iπ|x|/4}|x⟩`, fixes `|0̄⟩` and multiplies `|1̄⟩` by `e^{−iπ/4}`: it acts on the
logical qubit as `T†`. Applied to the encoded `|+̄⟩ = |0̄⟩ + |1̄⟩` it produces the encoded
`T†|+⟩`, the magic state up to the Clifford `S` (`S T† = T`).

* `row i`, `codeword a`, `codeword_injective`; `wt` — the weight on `Fin 15 → Fin 2`;
* `weight_codeword`, `weight_codeword_add_one` — **the weights `0/8` and `7/15`** (the
  triorthogonality of the code, in the form the transversal gate needs);
* `logical0`, `logical1`, `logicalPlus`; `pauliOp_basisState_zero`, ★ `pauliOp_row_logical0/1` —
  **the `X`-stabilisers fix the logical states**;
* `tTrans` — the transversal `T` as a coordinate operator, `tTrans_eq_comp` — **it is the
  composite of the fifteen single-qubit `T` gates**; `tTrans_basisState`;
* ★★ `tTrans_logical0`, `tTrans_logical1` — **`T^{⊗15}` is the logical `T†`**;
  ★ `tTrans_logicalPlus` — the encoded magic state `|0̄⟩ + e^{−iπ/4}|1̄⟩`.

## Honest scope

⚠️ The code space is presented by its two logical states, not as the range of the fourteen-generator
stabiliser average of `Stabilizer.lean`; the `Z`-stabilisers and the action of `Z`-error patterns on
the logical states are BACKLOG #77, the distillation bound #78.

References: S. Bravyi, A. Kitaev, PRA 71 (2005) 022316 §IV; E. Knill, R. Laflamme, W. Zurek,
quant-ph/9610011; S. Bravyi, J. Haah, PRA 86 (2012) 052329 (triorthogonal codes);
`specs/magic-plan.md`; `specs/BACKLOG.md` #76; `specs/future-work.md`.
-/

@[expose] public section

open Finset
open scoped ComplexConjugate

namespace QuantumInfo

namespace ReedMuller15

/-! ### The simplex code on `Fin 2` labels -/

/-- Row `i` of the parity-check matrix, as a `Fin 2` label. -/
def row (i : Fin 4) : Fin 15 → Fin 2 := fun j => if Nat.testBit (j.val + 1) i.val then 1 else 0

/-- The codeword `∑ᵢ aᵢ · row i` of the `[15, 4]` simplex code. -/
def codeword (a : Fin 4 → Fin 2) : Fin 15 → Fin 2 := fun j => ∑ i, a i * row i j

/-- The weight of a `Fin 2` label. -/
def wt (x : Fin 15 → Fin 2) : ℕ := (univ.filter fun j => x j = 1).card

theorem codeword_injective : Function.Injective codeword := by
  intro a b
  revert a b
  decide

/-- Every codeword has weight `0` or `8`. -/
theorem weight_codeword (a : Fin 4 → Fin 2) : wt (codeword a) = 0 ∨ wt (codeword a) = 8 := by
  revert a
  decide

/-- Every word of the coset `C + 𝟙` has weight `7` or `15`. -/
theorem weight_codeword_add_one (a : Fin 4 → Fin 2) :
    wt (codeword a + 1) = 7 ∨ wt (codeword a + 1) = 15 := by
  revert a
  decide

/-- `X^{row i}` permutes the codewords: `codeword a + row i = codeword (a + eᵢ)`. -/
theorem codeword_add_row (a : Fin 4 → Fin 2) (i : Fin 4) :
    codeword a + row i = codeword (a + Pi.single i 1) := by
  revert a i
  decide

/-! ### The logical states and the `X`-stabilisers -/

/-- `|0̄⟩ = ∑_{x ∈ C} |x⟩` (unnormalised). -/
noncomputable def logical0 : QReg 15 := ∑ a : Fin 4 → Fin 2, basisState (codeword a)

/-- `|1̄⟩ = ∑_{x ∈ C} |x + 𝟙⟩` (unnormalised). -/
noncomputable def logical1 : QReg 15 := ∑ a : Fin 4 → Fin 2, basisState (codeword a + 1)

/-- The encoded `|+̄⟩`, unnormalised: `|0̄⟩ + |1̄⟩`. -/
noncomputable def logicalPlus : QReg 15 := logical0 + logical1

theorem fin2_add_add_self (x a : Fin 15 → Fin 2) : x + a + a = x := by
  funext j
  simp only [Pi.add_apply]
  generalize x j = u
  generalize a j = v
  revert u v
  decide

/-- `X^a` moves a basis state: `X^a |x⟩ = |x + a⟩`. -/
theorem pauliOp_basisState_zero (a x : Fin 15 → Fin 2) :
    pauliOp a 0 (basisState x) = basisState (x + a) := by
  ext z
  rw [pauliOp_apply, pauliSign_zero_left, one_mul, basisState_apply, basisState_apply]
  by_cases h : z + a = x
  · rw [if_pos h, if_pos (by rw [← h, fin2_add_add_self])]
  · rw [if_neg h, if_neg (by intro hz; exact h (by rw [hz, fin2_add_add_self]))]

/-- ★ The `X`-stabilisers fix `|0̄⟩`. -/
theorem pauliOp_row_logical0 (i : Fin 4) : pauliOp (row i) 0 logical0 = logical0 := by
  rw [logical0, pauliOp_sum, Finset.sum_congr rfl fun a _ => by
    rw [pauliOp_basisState_zero, codeword_add_row]]
  exact Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ fun a => rfl

/-- ★ The `X`-stabilisers fix `|1̄⟩`. -/
theorem pauliOp_row_logical1 (i : Fin 4) : pauliOp (row i) 0 logical1 = logical1 := by
  rw [logical1, pauliOp_sum, Finset.sum_congr rfl fun a _ => by
    rw [pauliOp_basisState_zero, add_right_comm, codeword_add_row]]
  exact Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ fun a => rfl

/-! ### The transversal `T` -/

/-- The transversal `T` gate `T^{⊗15}`: `|x⟩ ↦ e^{iπ|x|/4}|x⟩`. -/
noncomputable def tTrans (ψ : QReg 15) : QReg 15 :=
  (WithLp.equiv 2 ((Fin 15 → Fin 2) → ℂ)).symm (fun z => tPhase ^ wt z * ψ z)

@[simp] lemma tTrans_apply (ψ : QReg 15) (z : Fin 15 → Fin 2) :
    tTrans ψ z = tPhase ^ wt z * ψ z := rfl

theorem fin2_val_eq_ite (v : Fin 2) : (v : ℕ) = if v = 1 then 1 else 0 := by
  revert v
  decide

theorem wt_eq_sum (z : Fin 15 → Fin 2) : wt z = ∑ j, (z j : ℕ) := by
  rw [wt, card_filter]
  exact sum_congr rfl fun j _ => (fin2_val_eq_ite (z j)).symm

theorem finRange_fifteen :
    List.finRange 15 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
  decide

/-- **Transversality**: `tTrans` is the composite of the fifteen single-qubit `T` gates. -/
theorem tTrans_eq_comp (ψ : QReg 15) :
    tTrans ψ = tGate 0 (tGate 1 (tGate 2 (tGate 3 (tGate 4 (tGate 5 (tGate 6 (tGate 7 (tGate 8
      (tGate 9 (tGate 10 (tGate 11 (tGate 12 (tGate 13 (tGate 14 ψ)))))))))))))) := by
  ext z
  simp only [tTrans_apply, tGate_apply, wt_eq_sum, Fin.sum_univ_def, finRange_fifteen,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_add]
  ring

theorem tTrans_sum {κ : Type*} (s : Finset κ) (f : κ → QReg 15) :
    tTrans (∑ k ∈ s, f k) = ∑ k ∈ s, tTrans (f k) := by
  ext z
  rw [tTrans_apply, sum_coord, sum_coord, mul_sum]
  exact sum_congr rfl fun k _ => rfl

theorem tTrans_add (ψ φ : QReg 15) : tTrans (ψ + φ) = tTrans ψ + tTrans φ := by
  ext z
  rw [tTrans_apply, PiLp.add_apply, PiLp.add_apply, tTrans_apply, tTrans_apply, mul_add]

theorem tTrans_smul (c : ℂ) (ψ : QReg 15) : tTrans (c • ψ) = c • tTrans ψ := by
  ext z
  rw [tTrans_apply, PiLp.smul_apply, PiLp.smul_apply, tTrans_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem tTrans_basisState (x : Fin 15 → Fin 2) :
    tTrans (basisState x) = tPhase ^ wt x • basisState x := by
  ext z
  rw [tTrans_apply, PiLp.smul_apply, smul_eq_mul, basisState_apply]
  by_cases h : z = x
  · rw [h]
  · rw [if_neg h, mul_zero, mul_zero]

theorem tPhase_pow_eight : tPhase ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_two, tPhase_sq, show (4 : ℕ) = 2 * 2 from rfl,
    pow_mul, Complex.I_sq]
  norm_num

theorem tPhase_pow_seven : tPhase ^ 7 = tPhaseInv := by
  have h := tPhase_pow_eight
  rw [pow_succ] at h
  calc tPhase ^ 7 = tPhase ^ 7 * (tPhase * tPhaseInv) := by rw [tPhase_mul_inv, mul_one]
    _ = (tPhase ^ 7 * tPhase) * tPhaseInv := by ring
    _ = tPhaseInv := by rw [h, one_mul]

theorem tPhase_pow_fifteen : tPhase ^ 15 = tPhaseInv := by
  rw [show (15 : ℕ) = 7 + 8 from rfl, pow_add, tPhase_pow_eight, mul_one, tPhase_pow_seven]

/-- ★★ **`T^{⊗15}` fixes `|0̄⟩`**: every codeword has weight `0` or `8`. -/
theorem tTrans_logical0 : tTrans logical0 = logical0 := by
  rw [logical0, tTrans_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [tTrans_basisState]
  rcases weight_codeword a with h | h
  · rw [h, pow_zero, one_smul]
  · rw [h, tPhase_pow_eight, one_smul]

/-- ★★ **`T^{⊗15}` multiplies `|1̄⟩` by `e^{−iπ/4}`**: every word of the coset has weight `7` or
`15`. Together with `tTrans_logical0`: the transversal `T` is the logical `T†`. -/
theorem tTrans_logical1 : tTrans logical1 = tPhaseInv • logical1 := by
  rw [logical1, tTrans_sum, smul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [tTrans_basisState]
  rcases weight_codeword_add_one a with h | h
  · rw [h, tPhase_pow_seven]
  · rw [h, tPhase_pow_fifteen]

/-- ★ **The encoded magic state**: `T^{⊗15}|+̄⟩ = |0̄⟩ + e^{−iπ/4}|1̄⟩`, the encoded `T†|+⟩`. -/
theorem tTrans_logicalPlus : tTrans logicalPlus = logical0 + tPhaseInv • logical1 := by
  rw [logicalPlus, tTrans_add, tTrans_logical0, tTrans_logical1]

end ReedMuller15

end QuantumInfo

end
