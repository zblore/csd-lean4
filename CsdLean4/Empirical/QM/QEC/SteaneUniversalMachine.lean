/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneInjection

/-!
# The Steane machine over `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄` and `T̄`, at level one

**Category:** 3-Local (Empirical, QM twin). BACKLOG #305.

`SteanePairMachine.lean`'s `steane_pair_machine` runs circuits of transversal Clifford gadgets on
two Steane blocks, seven fault locations per gadget, with output exactly ideal with probability at
least `1 − 21 N p²`. This module adds the injection gadget of `SteaneInjection.lean` — the logical
`T` on block `0`, block `1` its ancilla — with **the same seven locations**: location `q` of the
injection is the column of qubit `q`, where a fault may hit the magic state's qubit `q` (`V q`), the
`q`-th `CNOT` (`U q 0`, `U q 1`, after the gate, as for the other gadgets) and the read-out of qubit
`q` (`W q`, before it is read), all at once.

* ★ `cnotT_mul_blockKron_gateOf_mul_cnotT` — **`CNOT̄` on a one-qubit fault of the target block**:
  `CNOT̄ (1 ⊗ V_q) CNOT̄ = Σ_x |x⟩⟨x|_q ⊗ (X^x V X^x)_q`, an operator on column `q` alone;
* `colKraus`, ★★ `colKraus_mul_pairEnc` — **a column fault leaves the exact Kraus operator followed
  by the column error `colFaultE`**, ★ `colFaultE_mem_pairSpan` (unitary, and a combination of the
  pair's family); ★★ `deviatesBy_injFaulty` — **a pattern with at most one faulty column keeps the
  injection within the correctable set**;
* `UGadget` — **the gadget set**: the Clifford gadgets of `PairGadget` and the injection `tGate`;
  ★★ `UGadget.deviatesBy_faulty`, ★★★ `steane_universalGadgetSet_corrected` (one recovery for all);
* ★★★ `steane_universal_machine` — **the machine over `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄`, `T̄`**: a
  pattern that makes no gadget bad gives exactly the ideal output, and under independent location
  faults of rate at most `p` the output is exactly ideal with probability at least `1 − 21 N p²`.

## Honest scope

⚠️ Level one, an ideal recovery, unitary faults (a flipped read-out is the unitary `X`; the general
read-out families of `SteaneInjection.lean`'s `injChannelMeas` are not in the count). A location of
the injection is a column — three physical sites; with each site faulty at rate `p`, the column's
rate is at most `3p`. The injection consumes block `1`: `T̄` acts on block `0` only, so the machine
is universal on **one** logical qubit (`H̄`, `S̄`, `T̄` —
`Mathlib/QuantumInfo/CliffordTUniversal.lean`), with block `1` as workspace; universality on two
logical qubits needs a third block (#307).

References: S. Bravyi, A. Kitaev, *Phys. Rev. A* **71**, 022316 (2005); P. Aliferis, D. Gottesman,
J. Preskill, *Quantum Inf. Comput.* **6**, 97 (2006); `specs/BACKLOG.md` #305;
`Empirical/QM/QEC/SteaneInjection.lean`, `Empirical/QM/QEC/SteanePairMachine.lean`
(`steane_pair_machine`); `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped ENNReal

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### `CNOT̄` on a one-qubit fault of the target block -/

theorem pX_mul_mul_pX_apply (V : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    (pX * V * pX) a b = V (1 + a) (1 + b) := by
  fin_cases a <;> fin_cases b <;> simp [pX, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]

theorem projL_apply_self (x s : Fin 2) : projL x s s = if s = x then 1 else 0 := by
  rw [projL, diagonal_apply_eq]

theorem one_mul_gateOf_add_apply (q : Fin 7) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (a b c d : Fin 7 → Fin 2) :
    (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) a c * gateOf q V (a + b) (c + d)
      = gateOf q (projL 0) a c * gateOf q V b d
        + gateOf q (projL 1) a c * gateOf q (pX * V * pX) b d := by
  by_cases hac : a = c
  · subst hac
    have hself : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, gateOf q M a a = M (a q) (a q) :=
      fun M => gateOf_apply_of_agree (fun _ _ => rfl) M
    rw [Matrix.one_apply_eq, one_mul, hself, hself, projL_apply_self, projL_apply_self]
    by_cases hbd : ∀ i, i ≠ q → b i = d i
    · have hab : ∀ i, i ≠ q → (a + b) i = (a + d) i := fun i hi => by
        simp only [Pi.add_apply, hbd i hi]
      rw [gateOf_apply_of_agree hab, gateOf_apply_of_agree hbd, gateOf_apply_of_agree hbd,
        pX_mul_mul_pX_apply]
      simp only [Pi.add_apply]
      generalize a q = s
      fin_cases s <;> simp
    · have hab : ¬∀ i, i ≠ q → (a + b) i = (a + d) i := fun h => hbd fun i hi => by
        simpa using h i hi
      rw [gateOf_apply_of_not_agree hab, gateOf_apply_of_not_agree hbd,
        gateOf_apply_of_not_agree hbd]
      ring
  · rw [Matrix.one_apply_ne hac, zero_mul]
    by_cases hag : ∀ i, i ≠ q → a i = c i
    · have hq : a q ≠ c q := fun h => hac (funext fun i => by
        by_cases hi : i = q
        · subst hi
          exact h
        · exact hag i hi)
      rw [gateOf_apply_of_agree hag, gateOf_apply_of_agree hag]
      simp [projL, diagonal_apply_ne _ hq]
    · rw [gateOf_apply_of_not_agree hag, gateOf_apply_of_not_agree hag]
      ring

/-- ★ **`CNOT̄` on a one-qubit fault of the target block**: it stays on column `q`, as
`Σ_x |x⟩⟨x|_q ⊗ (X^x V X^x)_q` — the `CNOT` on qubit `q`, the others cancelling. -/
theorem cnotT_mul_blockKron_gateOf_mul_cnotT (q : Fin 7) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    cnotT * blockKron ![1, gateOf q V] * cnotT
      = ∑ x : Fin 2,
          blockKron ![gateOf q (projL x), gateOf q (pX ^ (x : ℕ) * V * pX ^ (x : ℕ))] := by
  ext z w
  rw [cnotT, mul_permMat_apply, permMat_mul_apply cnotPerm_involutive, Matrix.sum_apply,
    Fin.sum_univ_two, blockKron_two_apply, blockKron_two_apply, blockKron_two_apply]
  simp only [cnotPerm, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, Matrix.one_mul, Matrix.mul_one]
  exact one_mul_gateOf_add_apply q V (z 0) (z 1) (w 0) (w 1)

/-! ### A fault at one column of the injection -/

/-- **The injection's Kraus operator with every fault at column `q`**: `V` on the magic state's
qubit `q`, `U0 ⊗ U1` after the `q`-th `CNOT`, `W` on qubit `q` of the ancilla before it is read. -/
def colKraus (q : Fin 7) (V U0 U1 W : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 7 → Fin 2) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  readOp m * (blockKron ![1, gateOf q W] * pairFault q U0 U1) * cnotT
    * blockKron ![1, vecMulVec (gateOf q V *ᵥ magicEnc) (Pi.single k 1)]

/-- **The outcome-`m` column error**: an operator on qubit `q` of each block. -/
def colFaultE (q : Fin 7) (V U0 U1 W : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  ∑ x : Fin 2, blockKron ![gateOf q (sDagM ^ (m : ℕ) * (U0 * projL x) * (sDagM ^ (m : ℕ))ᴴ),
    gateOf q (pX ^ (m : ℕ) * (W * U1 * (pX ^ (x : ℕ) * V * pX ^ (x : ℕ))) * pX ^ (m : ℕ))]

/-- ★★ **A column fault leaves the exact Kraus operator followed by the column error**, on the
code. -/
theorem colKraus_mul_pairEnc (q : Fin 7) (V U0 U1 W : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 7 → Fin 2) (m : Fin 2) :
    colKraus q V U0 U1 W k m * pairEnc
      = colFaultE q V U0 U1 W m * (injKraus magicEnc k m * pairEnc) := by
  have hK : colKraus q V U0 U1 W k m = injKrausWith (blockKron ![gateOf q U0, gateOf q (W * U1)]
      * (cnotT * blockKron ![1, gateOf q V] * cnotT)) k m := by
    rw [colKraus, injKrausWith,
      show blockKron ![1, gateOf q W] * pairFault q U0 U1
          = blockKron ![gateOf q U0, gateOf q (W * U1)] by
        rw [pairFault, blockKron_two_mul, Matrix.one_mul, Controlled.gateOf_mul],
      show blockKron ![1, vecMulVec (gateOf q V *ᵥ magicEnc) (Pi.single k 1)]
          = blockKron ![1, gateOf q V] * blockKron ![1, vecMulVec magicEnc (Pi.single k 1)] by
        rw [blockKron_two_mul, Matrix.one_mul, mul_vecMulVec]]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc cnotT cnotT, cnotT_mul_self, Matrix.one_mul]
  rw [hK]
  refine injKrausWith_mul_pairEnc ?_ k
  rw [cnotT_mul_blockKron_gateOf_mul_cnotT, colFaultE]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [blockKron_two_mul, ← Controlled.gateOf_mul, ← Controlled.gateOf_mul,
    readOp_mul_blockKron_gateOf]

theorem blockKron_two_mem_unitaryGroup {A B : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 7 → Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 7 → Fin 2) ℂ) :
    blockKron ![A, B] ∈ Matrix.unitaryGroup PairReg ℂ := by
  refine Matrix.mem_unitaryGroup_iff'.2 ?_
  rw [Matrix.star_eq_conjTranspose, blockKron_two_conjTranspose, blockKron_two_mul,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.1 hA, Matrix.mem_unitaryGroup_iff'.1 hB,
    show ![(1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), 1] = fun _ => 1 from
      funext fun b => by fin_cases b <;> rfl, blockKron_one]

theorem pX_pow_conjTranspose (m : ℕ) : (pX ^ m)ᴴ = pX ^ m := by
  rw [conjTranspose_pow, pX_conjTranspose]

/-- The column error is the column fault conjugated by `S†^m ⊗ X^m` on column `q`. -/
theorem colFaultE_eq_conj (q : Fin 7) (V U0 U1 W : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) :
    colFaultE q V U0 U1 W m
      = blockKron ![gateOf q (sDagM ^ (m : ℕ)), gateOf q (pX ^ (m : ℕ))]
        * (blockKron ![gateOf q U0, gateOf q (W * U1)]
          * (cnotT * blockKron ![1, gateOf q V] * cnotT))
        * (blockKron ![gateOf q (sDagM ^ (m : ℕ)), gateOf q (pX ^ (m : ℕ))])ᴴ := by
  rw [cnotT_mul_blockKron_gateOf_mul_cnotT, colFaultE]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [blockKron_two_conjTranspose, gateOf_conjTranspose, gateOf_conjTranspose,
    pX_pow_conjTranspose, blockKron_two_mul, blockKron_two_mul, blockKron_two_mul,
    ← Controlled.gateOf_mul, ← Controlled.gateOf_mul, ← Controlled.gateOf_mul,
    ← Controlled.gateOf_mul, ← Controlled.gateOf_mul, ← Controlled.gateOf_mul]

set_option maxRecDepth 4000 in
/-- The column error of unitary faults is a correctable pair error: unitary, and a combination of
the pair's family. -/
theorem colFaultE_mem_pairSpan {V U0 U1 W : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hU0 : U0 ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hU1 : U1 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 7) (m : Fin 2) : colFaultE q V U0 U1 W m ∈ pairSpan := by
  have hΓ : blockKron ![gateOf q (sDagM ^ (m : ℕ)), gateOf q (pX ^ (m : ℕ))]
      ∈ Matrix.unitaryGroup PairReg ℂ :=
    blockKron_two_mem_unitaryGroup (gateOf_mem_unitaryGroup q (pow_mem sDagM_mem_unitaryGroup _))
      (gateOf_mem_unitaryGroup q (pow_mem pX_mem_unitaryGroup _))
  have hF : blockKron ![gateOf q U0, gateOf q (W * U1)] ∈ Matrix.unitaryGroup PairReg ℂ :=
    blockKron_two_mem_unitaryGroup (gateOf_mem_unitaryGroup q hU0)
      (gateOf_mem_unitaryGroup q (mul_mem hW hU1))
  have hB : blockKron ![1, gateOf q V] ∈ Matrix.unitaryGroup PairReg ℂ :=
    blockKron_two_mem_unitaryGroup (one_mem _) (gateOf_mem_unitaryGroup q hV)
  have hC : cnotT * blockKron ![1, gateOf q V] * cnotT ∈ Matrix.unitaryGroup PairReg ℂ :=
    mul_mem (mul_mem cnotT_mem_unitaryGroup hB) cnotT_mem_unitaryGroup
  have hE : colFaultE q V U0 U1 W m ∈ Matrix.unitaryGroup PairReg ℂ := by
    rw [colFaultE_eq_conj, ← Matrix.star_eq_conjTranspose]
    exact mul_mem (mul_mem hΓ (mul_mem hF hC)) (Unitary.star_mem hΓ)
  refine ⟨by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hE,
    fun g => ∑ x : Fin 2, ∏ b, singleCoeff ((fun _ => q) b)
      (![sDagM ^ (m : ℕ) * (U0 * projL x) * (sDagM ^ (m : ℕ))ᴴ,
        pX ^ (m : ℕ) * (W * U1 * (pX ^ (x : ℕ) * V * pX ^ (x : ℕ))) * pX ^ (m : ℕ)] b) (g b), ?_⟩
  rw [colFaultE]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (pairFault_eq_blockFault q _ _).trans (blockFault_eq_sum _ _)

/-! ### Fault patterns on the injection -/

/-- The single-block operator of a pattern: `V q` at each faulty location `q`. -/
def colOp (V : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron fun q => if bs q then V q else 1

/-- **The injection's Kraus operator under a fault pattern**: at each faulty location `q`, `V q` on
the magic state's qubit `q`, `U q` after the `q`-th `CNOT`, `W q` before qubit `q` is read. -/
def injFaultyKraus (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) (k : Fin 7 → Fin 2) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  readOp m * (blockKron ![1, colOp W bs] * faultOp U bs) * cnotT
    * blockKron ![1, vecMulVec (colOp V bs *ᵥ magicEnc) (Pi.single k 1)]

/-- **The injection gadget under a fault pattern.** -/
def injFaulty (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (bs : Fin 7 → Bool) (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  ∑ k, ∑ m, injFaultyKraus U V W bs k m * ρ * (injFaultyKraus U V W bs k m)ᴴ

theorem ite_mem_unitaryGroup {b : Bool} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (if b then A else 1) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  split_ifs
  · exact hA
  · exact one_mem _

/-- ★★ **The one-fault bound for the injection**: a pattern with at most one faulty location —
one column, every fault on it unitary — is the ideal injection followed by a correctable mixture. -/
theorem deviatesBy_injFaulty {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    {V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : ∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hW : ∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {bs : Fin 7 → Bool} (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    DeviatesBy pairProj pairMix idealInj (injFaulty U V W bs) := by
  obtain ⟨i, hi⟩ := exists_eq_of_card_le_one h
  set V' := if bs i then V i else 1
  set W' := if bs i then W i else 1
  set U0 := if bs i then U i 0 else 1
  set U1 := if bs i then U i 1 else 1
  have hK : ∀ k m, injFaultyKraus U V W bs k m = colKraus i V' U0 U1 W' k m := by
    intro k m
    have hF : faultOp U bs = pairFault i U0 U1 := by
      rw [faultOp, pairFault]
      congr 1
      funext b
      fin_cases b
      · exact blockKron_ite_eq_gateOf hi fun q => U q 0
      · exact blockKron_ite_eq_gateOf hi fun q => U q 1
    rw [injFaultyKraus, colKraus, hF, colOp, colOp, blockKron_ite_eq_gateOf hi,
      blockKron_ite_eq_gateOf hi]
  intro ρ hρ
  refine ⟨fun σ => ∑ m : Fin 2, ((2⁻¹ : ℝ) : ℂ) • (colFaultE i V' U0 U1 W' m * σ
      * (colFaultE i V' U0 U1 W' m)ᴴ),
    ⟨2, fun _ => 2⁻¹, colFaultE i V' U0 U1 W', fun _ => by norm_num, by norm_num,
      fun m => colFaultE_mem_pairSpan (ite_mem_unitaryGroup (hV i)) (ite_mem_unitaryGroup (hU i 0))
        (ite_mem_unitaryGroup (hU i 1)) (ite_mem_unitaryGroup (hW i)) i m, rfl⟩, ?_⟩
  have h := sum_conj_eq_of_mul_pairEnc (ι := Unit) (fun k m _ => colKraus i V' U0 U1 W' k m)
    (fun m _ => colFaultE i V' U0 U1 W' m)
    (fun k m _ => colKraus_mul_pairEnc i V' U0 U1 W' k m) hρ
  simp only [Fintype.sum_unique] at h
  rw [injFaulty]
  simp only [hK]
  rw [h, show ((2⁻¹ : ℝ) : ℂ) = 2⁻¹ by push_cast; rfl]

/-! ### The universal gadget set -/

/-- **The universal gadget set on two blocks**: the Clifford gadgets of `PairGadget` (`H̄`, `S̄`,
`X̄`, `Z̄` on either block, `CNOT̄`) and the injected `T̄` on block `0`. -/
inductive UGadget
  /-- A Clifford gadget. -/
  | clifford (G : PairGadget)
  /-- The logical `T` on block `0`, by injection with block `1` as the ancilla. -/
  | tGate

namespace UGadget

/-- The ideal gadget. -/
def ideal : UGadget → Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ
  | clifford G => G.ideal
  | tGate => idealInj

/-- The gadget under a fault pattern: `U` at the locations of a Clifford gadget; `U`, `V`, `W` at
the columns of the injection. -/
def faulty (G : UGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) :
    Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ :=
  match G with
  | clifford G => G.faulty U bs
  | tGate => injFaulty U V W bs

/-- The implemented step: the gadget under its fault pattern, then the recovery. -/
def step {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ) (G : UGadget)
    (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (bs : Fin 7 → Bool) (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  R.apply (G.faulty U V W bs ρ)

theorem isCodeState_ideal (G : UGadget) {ρ : Matrix PairReg PairReg ℂ}
    (hρ : IsCodeState pairProj ρ) : IsCodeState pairProj (G.ideal ρ) := by
  cases G with
  | clifford G => exact G.isCodeState_ideal hρ
  | tGate => exact isCodeState_idealInj ρ

/-- ★★ **The one-fault bound for every gadget of the universal set.** -/
theorem deviatesBy_faulty (G : UGadget) {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    {V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : ∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hW : ∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {bs : Fin 7 → Bool} (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    DeviatesBy pairProj pairKrausMix G.ideal (G.faulty U V W bs) := by
  cases G with
  | clifford G =>
    exact (G.deviatesBy_faulty hU h).mono
      (pairWeightOne_subset_pairMix.trans pairMix_subset_pairKrausMix)
  | tGate => exact (deviatesBy_injFaulty hU hV hW h).mono pairMix_subset_pairKrausMix

end UGadget

/-- ★★★ **The universal gadget set is a set of corrected steps.** One recovery channel `R` serves
every Clifford gadget and the injected `T̄`: for unitary faults at the locations and every pattern
that is not bad (at most one faulty location), the faulty gadget followed by `R` is an
`IsCorrectedStep` for the ideal gadget. -/
theorem steane_universalGadgetSet_corrected :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairKrausMix
      ∧ ∀ (G : UGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
        (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) → (∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ω : ConcatPat 7 1, isBad 7 1 ω = false →
          IsCorrectedStep pairProj G.ideal (G.step R U V W (locPat ω)) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_pairKrausMix
  exact ⟨R, hR, fun G U V W hU hV hW ω hω => isCorrectedStep_rect hR
    (G.deviatesBy_faulty hU hV hW (card_le_one_of_isBad_eq_false hω))
    fun _ hρ => G.isCodeState_ideal hρ⟩

/-! ### The machine -/

/-- **The universal machine's circuit**: gadget `j` is `gs j`, with fault data `U j`, `V j`, `W j`
and fault pattern `ω j`; each gadget is run and then recovered. -/
def uMachineCircuit {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ) {N : ℕ}
    (gs : Fin N → UGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 1) : Circuit PairReg :=
  List.ofFn fun j => ((gs j).ideal, (gs j).step R (U j) (V j) (W j) (locPat (ω j)))

/-- The ideal output of the universal machine: the ideal gadgets, in order. -/
def uMachineIdeal {N : ℕ} (gs : Fin N → UGadget) (ρ : Matrix PairReg PairReg ℂ) :
    Matrix PairReg PairReg ℂ :=
  runMaps (List.ofFn fun j => (gs j).ideal) ρ

theorem idealRun_uMachineCircuit {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ)
    {N : ℕ} (gs : Fin N → UGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 1)
    (ρ : Matrix PairReg PairReg ℂ) :
    idealRun (uMachineCircuit R gs U V W ω) ρ = uMachineIdeal gs ρ := by
  rw [idealRun, uMachineCircuit, uMachineIdeal, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine over `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄` and `T̄`, at level one.** One
recovery channel `R` on two blocks such that, for every circuit of `N` gadgets from the universal
set, every assignment of unitary faults to their locations and every encoded input:

* **the deterministic premise holds**: a pattern that makes no gadget bad gives exactly the ideal
  output;
* **the threshold statement follows**: under independent location faults of rate at most `p`, the
  output is exactly the ideal one with probability at least `1 − 21 N p²`.

`steane_pair_machine` is the Clifford special case. -/
theorem steane_universal_machine :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      ∀ (N : ℕ) (gs : Fin N → UGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
        (V W : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j q b, U j q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ j q, V j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ j q, W j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix PairReg PairReg ℂ, IsCodeState pairProj ρ →
          (∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
              correctedRun (uMachineCircuit R gs U V W ω) ρ = uMachineIdeal gs ρ)
          ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
              ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
                ≤ QuantumInfo.circuitMeasure N 7 ν 1
                    {ω | correctedRun (uMachineCircuit R gs U V W ω) ρ = uMachineIdeal gs ρ} := by
  obtain ⟨R, -, hR⟩ := steane_universalGadgetSet_corrected
  refine ⟨R, fun N gs U V W hU hV hW ρ hρ => ?_⟩
  have hgood : ∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
      correctedRun (uMachineCircuit R gs U V W ω) ρ = uMachineIdeal gs ρ := by
    intro ω hω
    rw [← idealRun_uMachineCircuit R gs U V W ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hR (gs j) (U j) (V j) (W j) (hU j) (hV j) (hW j) (ω j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := 1) ν hp hν
    (out := fun ω => correctedRun (uMachineCircuit R gs U V W ω) ρ)
    (ideal := uMachineIdeal gs ρ) hgood
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
