/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteanePairMachine
public import CsdLean4.Empirical.QM.QEC.SteaneLogicalIO
public import CsdLean4.Mathlib.QuantumInfo.Magic

/-!
# The logical `T̄` on the Steane code, by magic-state injection

**Category:** 3-Local (Empirical, QM twin). BACKLOG #230, second brick (the injection; the first
brick was the logical `S̄`, `SteaneLogicalS.lean`).

The two-block register holds the data in block `0` and the ancilla in block `1`. The injection
gadget, written as one channel on the physical register (`injChannel`), is

1. **discard block `1` and prepare the encoded magic state** `|Ā⟩ = E (|0⟩ + e^{iπ/4}|1⟩)/√2` there
   — the Kraus operators `|Ā⟩⟨k|` over all `128` labels `k` of the block;
2. **the transversal `CNOT̄`**, data block controlling;
3. **the transversal `Z` measurement of block `1`, decoded** (`logProj m`, `SteaneLogicalIO.lean`:
   the labels whose syndrome-corrected parity is `m`);
4. **feed-forward on the outcome `m`**: reset the ancilla by the transversal `X̄^m`, and correct the
   data by the logical `S̄^m` (the transversal `S†`, `SteaneLogicalS.lean`).

Every step but the magic state is transversal and Clifford. The theorem is that the whole channel,
on code states, is **the logical `T` on the data with the ancilla left in `|0̄⟩`**, exactly.

* `tGateM` — `T = diag(1, e^{iπ/4})`; `magicL` — the logical magic state `(|0⟩ + e^{iπ/4}|1⟩)/√2`;
  `magicEnc` — its encoding;
* ★★ `injCore` — **the logical heart, outcome by outcome**: after the magic state, `CNOT`, the
  outcome-`m` projector, `X^m` and `S^m`, the data has picked up `T`, with amplitude `magicL m`
  (`|magicL m|² = 1/2`, `magicL_mul_star_sum`) — on outcome `1` the `CNOT` has applied `T†`, and
  `S T† = T`;
* `sum_blockKron_isometry` — discarding a block through the `128` physical labels is, on the code,
  discarding the logical qubit (the encoder is an isometry);
* ★ `injKraus_mul_pairEnc` — **every physical Kraus operator is the logical one**, through the
  encoder intertwinings of `CNOT̄`, `X̄`, `S̄` and the decoded read-out;
* `logicalInj` — the logical channel: `T` on qubit `0`, qubit `1` discarded and reset to `|0⟩`;
  ★ `logicalInj_blockKron` — on a product input it is `tr τ · (T ρ T†) ⊗ |0⟩⟨0|`;
* ★★★ `injChannel_pairEnc` — **the injection gadget is the logical `T`**: on every encoded input,
  `injChannel |Ā⟩ (E σ E†) = E (logicalInj σ) E†`;
* `idealInj`, ★★ `injChannel_eq_idealInj`, `isCodeState_idealInj` — the ideal gadget on the
  physical register, and the gadget equal to it on code states;
* ★★★ `steane_injection_corrected` — **injection is a corrected step**: with any recovery for a
  correctable set `D`, a magic state whose error leaves the gadget within `D` of the ideal (the
  `DeviatesBy` hypothesis) gives #96's `IsCorrectedStep`; ★★ `deviatesBy_injChannel_magicEnc`
  discharges the hypothesis for the exact magic state, and ★★★ `steane_injection` packages it with
  the two-block recovery of `SteanePairMachine.lean`.

## Honest scope

⚠️ Level one, and the magic state's error is a **hypothesis** (`DeviatesBy`), as the row asks: no
theorem here says that a faulty magic-state preparation, or a fault inside the `CNOT̄` or the
read-out, stays within the weight-one set (a single Pauli on the magic state propagates through
`CNOT̄` and the outcome-dependent `X̄^m` into an outcome-dependent pair error). The injection is not
a member of `SteanePairMachine.lean`'s gadget set, so `steane_pair_machine`'s count does not cover
it. Both are rowed.

References: S. Bravyi, A. Kitaev, *Phys. Rev. A* **71**, 022316 (2005); X. Zhou, D. Leung,
I. Chuang, *Phys. Rev. A* **62**, 052316 (2000); M. Nielsen, I. Chuang, *Quantum Computation and
Quantum Information* §10.6.2; `specs/BACKLOG.md` #230; `Empirical/QM/QEC/SteanePairMachine.lean`
(`pairProj_eq`, `exists_isRecovery_pairWeightOne`), `Empirical/QM/QEC/SteaneTransversalCNOT.lean`
(`cnotT_mul_pairEnc`), `Empirical/QM/QEC/SteaneMachineConcat.lean` (`logicalX_mul_steaneEnc`),
`Empirical/QM/QEC/SteaneLogicalIO.lean` (`logProj_mul_steaneEnc`),
`Empirical/QM/QEC/SteaneLogicalS.lean` (`sTransversal_conjTranspose_mul_steaneEnc`),
`Mathlib/QuantumInfo/Magic.lean` (`tPhase`); `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The logical gate, the magic state, the read-out -/

/-- The gate `T = diag(1, e^{iπ/4})`. -/
def tGateM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, tPhase]

/-- `1/√2`. -/
def invSqrtTwo : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- The logical magic state `(|0⟩ + e^{iπ/4}|1⟩)/√2 = T|+⟩`. -/
def magicL : Fin 2 → ℂ := ![invSqrtTwo, invSqrtTwo * tPhase]

/-- The encoded magic state `|Ā⟩ = E |A⟩` on one block. -/
def magicEnc : (Fin 7 → Fin 2) → ℂ := steaneEnc *ᵥ magicL

/-- The logical projector `|m⟩⟨m|` — `logProj m` read through the encoder. -/
def projL (m : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun j => if j = m then 1 else 0

/-- The logical `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]

theorem star_tPhase : star tPhase = tPhaseInv := by
  rw [tPhase_eq, tPhaseInv_eq, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal,
    map_add, map_one, Complex.conj_I, sub_eq_add_neg]

theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  rw [invSqrtTwo, star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 2⁻¹ := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two,
    Complex.ofReal_ofNat]

/-- ★ **The magic state is normalised**: each outcome of its read-out has weight `1/2`. -/
theorem magicL_mul_star_sum : ∑ m, magicL m * star (magicL m) = 1 := by
  rw [Fin.sum_univ_two]
  simp only [magicL, Matrix.cons_val_zero, Matrix.cons_val_one, star_mul', star_invSqrtTwo,
    star_tPhase]
  calc invSqrtTwo * invSqrtTwo + invSqrtTwo * tPhase * (invSqrtTwo * tPhaseInv)
      = invSqrtTwo * invSqrtTwo * (1 + tPhase * tPhaseInv) := by ring
    _ = 1 := by rw [invSqrtTwo_mul_self, tPhase_mul_inv]; norm_num

theorem magicL_star_mul_sum : ∑ m, star (magicL m) * magicL m = 1 := by
  simp_rw [mul_comm (star _)]
  exact magicL_mul_star_sum

/-! ### Two-block tensors -/

theorem blockKron_two_apply {L L' : Type*} (M : Fin 2 → Matrix L L' ℂ) (c : Fin 2 → L)
    (d : Fin 2 → L') : blockKron M c d = M 0 (c 0) (d 0) * M 1 (c 1) (d 1) := by
  rw [blockKron_apply, Fin.prod_univ_two]

theorem blockKron_two_mul {L L' L'' : Type*} [Fintype L'] (A B : Matrix L L' ℂ)
    (A' B' : Matrix L' L'' ℂ) :
    blockKron ![A, B] * blockKron ![A', B'] = blockKron ![A * A', B * B'] := by
  rw [blockKron_mul]
  congr 1
  funext b
  fin_cases b <;> rfl

theorem blockKron_two_conjTranspose {L L' : Type*} (A B : Matrix L L' ℂ) :
    (blockKron ![A, B])ᴴ = blockKron ![Aᴴ, Bᴴ] := by
  rw [blockKron_conjTranspose]
  congr 1
  funext b
  fin_cases b <;> rfl

theorem blockKron_two_smul_right {L L' : Type*} (A B : Matrix L L' ℂ) (c : ℂ) :
    blockKron ![A, c • B] = c • blockKron ![A, B] := by
  ext k l
  simp only [blockKron_two_apply, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem sum_fin_two_arrow (f : (Fin 2 → Fin 2) → ℂ) :
    ∑ e, f e = f ![0, 0] + f ![0, 1] + (f ![1, 0] + f ![1, 1]) := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]
  rfl

theorem fin_two_arrow_eq (c : Fin 2 → Fin 2) : c = ![c 0, c 1] := by
  funext i
  fin_cases i <;> rfl

/-! ### The logical heart -/

/-- ★★ **The logical heart of injection, outcome by outcome.** The ancilla in `|A⟩`, the `CNOT`
from the data, the read-out projector `|m⟩⟨m|` on the ancilla, its reset `X^m` and the correction
`S^m` on the data together apply `T` to the data, with amplitude `magicL m`, and leave the ancilla
in `|0⟩`. On outcome `1` the `CNOT` has applied `e^{iπ/4} T†`, and `S T† = T`. -/
theorem injCore (m : Fin 2) :
    blockKron ![sGateM ^ (m : ℕ), pX ^ (m : ℕ) * projL m] * cnotL
        * blockKron ![1, vecMulVec magicL ket0]
      = magicL m • blockKron ![tGateM, vecMulVec ket0 ket0] := by
  ext c d
  rw [Matrix.mul_assoc, Matrix.mul_apply, sum_fin_two_arrow]
  simp only [cnotL, permMat_mul_apply cnotPermL_involutive, blockKron_two_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [fin_two_arrow_eq c, fin_two_arrow_eq d]
  generalize c 0 = c0, c 1 = c1, d 0 = d0, d 1 = d1
  have ht : tPhase * tPhase = Complex.I := tPhase_sq
  fin_cases m <;> fin_cases c0 <;> fin_cases c1 <;> fin_cases d0 <;> fin_cases d1 <;>
    (simp [cnotPermL, sGateM, pX, projL, tGateM, magicL, ket0, vecMul_diagonal, mul_assoc,
      ← ht, mul_comm _ invSqrtTwo])

/-! ### Discarding a block through an isometry -/

/-- **Discarding a block through any isometry's rows is discarding it through the basis**: two Kraus
representations of the same channel, related by the isometry `V` (`V† V = 1`). With `V` the encoder,
the `128` physical labels of a block act on the code as the two logical ones. -/
theorem sum_blockKron_isometry {κ : Type*} [Fintype κ] (V : Matrix κ (Fin 2) ℂ) (hV : Vᴴ * V = 1)
    (u : Fin 2 → ℂ) (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ k, blockKron ![1, vecMulVec u (V k)] * σ * (blockKron ![1, vecMulVec u (V k)])ᴴ
      = ∑ j, blockKron ![1, vecMulVec u (Pi.single j 1)] * σ
          * (blockKron ![1, vecMulVec u (Pi.single j 1)])ᴴ := by
  set B : Fin 2 → Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
    fun j => blockKron ![1, vecMulVec u (Pi.single j 1)]
  have hB : ∀ k, blockKron ![1, vecMulVec u (V k)] = ∑ j, V k j • B j := by
    intro k
    ext c d
    simp only [B, blockKron_two_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, vecMulVec_apply, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hVV : ∀ j j', ∑ k, V k j * star (V k j') = if j' = j then 1 else 0 := by
    intro j j'
    have h := congrFun (congrFun hV j') j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [conjTranspose_apply, mul_comm]
  calc ∑ k, blockKron ![1, vecMulVec u (V k)] * σ * (blockKron ![1, vecMulVec u (V k)])ᴴ
      = ∑ k, ∑ j, ∑ j', (V k j * star (V k j')) • (B j * σ * (B j')ᴴ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB k, conjTranspose_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [conjTranspose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ j', (∑ k, V k j * star (V k j')) • (B j * σ * (B j')ᴴ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j' _ => (Finset.sum_smul ..).symm
    _ = ∑ j, B j * σ * (B j)ᴴ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hVV, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]

/-! ### The logical channel -/

/-- The logical Kraus operator `T ⊗ |0⟩⟨j|`. -/
def injIdealKraus (j : Fin 2) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  blockKron ![tGateM, vecMulVec ket0 (Pi.single j 1)]

/-- **The logical injection channel**: `T` on qubit `0`; qubit `1` discarded and reset to `|0⟩`. -/
def logicalInj (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  ∑ j, injIdealKraus j * σ * (injIdealKraus j)ᴴ

/-- ★ **The logical channel on a product input**: `ρ ⊗ τ ↦ tr τ · (T ρ T†) ⊗ |0⟩⟨0|`. -/
theorem logicalInj_blockKron (ρ τ : Matrix (Fin 2) (Fin 2) ℂ) :
    logicalInj (blockKron ![ρ, τ])
      = τ.trace • blockKron ![tGateM * ρ * tGateMᴴ, vecMulVec ket0 ket0] := by
  have hj : ∀ j : Fin 2, vecMulVec ket0 (Pi.single j 1) * τ * (vecMulVec ket0 (Pi.single j 1))ᴴ
      = τ j j • vecMulVec ket0 ket0 := by
    intro j
    ext a b
    simp only [Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]
    fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [ket0]
  rw [logicalInj, Matrix.trace, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [injIdealKraus, blockKron_two_conjTranspose, blockKron_two_mul, blockKron_two_mul,
    Matrix.diag_apply, ← blockKron_two_smul_right, hj j]

/-- The outcome-`(k, m)` logical Kraus operator: discard through the encoder's row `k`, prepare
`|A⟩`, `CNOT`, project on `m`, `X^m`, `S^m`. -/
def krausL (k : Fin 7 → Fin 2) (m : Fin 2) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  blockKron ![sGateM ^ (m : ℕ), pX ^ (m : ℕ) * projL m] * cnotL
    * blockKron ![1, vecMulVec magicL (steaneEnc k)]

theorem vecMulVec_mul_ket0 (u r : Fin 2 → ℂ) :
    vecMulVec u ket0 * vecMulVec ket0 r = vecMulVec u r := by
  ext a b
  simp only [Matrix.mul_apply, vecMulVec_apply, Fin.sum_univ_two, ket0, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem krausL_eq (k : Fin 7 → Fin 2) (m : Fin 2) :
    krausL k m = magicL m • (blockKron ![tGateM, vecMulVec ket0 ket0]
      * blockKron ![1, vecMulVec ket0 (steaneEnc k)]) := by
  rw [krausL, show blockKron ![1, vecMulVec magicL (steaneEnc k)]
      = blockKron ![1, vecMulVec magicL ket0] * blockKron ![1, vecMulVec ket0 (steaneEnc k)] by
    rw [blockKron_two_mul, Matrix.one_mul, vecMulVec_mul_ket0], ← Matrix.mul_assoc, injCore,
    smul_mul_assoc]

/-- ★★ **The logical channel of the injection gadget is `logicalInj`.** Summed over the read-out
outcome (weights `1/2`, `1/2`) and over the discarded block, every branch applies `T`. -/
theorem sum_krausL (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ k, ∑ m, krausL k m * σ * (krausL k m)ᴴ = logicalInj σ := by
  set TE := blockKron ![tGateM, vecMulVec ket0 ket0]
  have hm : ∀ k, ∑ m, krausL k m * σ * (krausL k m)ᴴ
      = TE * (blockKron ![1, vecMulVec ket0 (steaneEnc k)] * σ
          * (blockKron ![1, vecMulVec ket0 (steaneEnc k)])ᴴ) * TEᴴ := by
    intro k
    simp only [krausL_eq, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Finset.sum_smul, magicL_star_mul_sum, one_smul, conjTranspose_mul, Matrix.mul_assoc]
    rfl
  simp only [hm]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    sum_blockKron_isometry steaneEnc steaneEnc_conjTranspose_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hTE : TE * blockKron ![1, vecMulVec ket0 (Pi.single j 1)] = injIdealKraus j := by
    rw [blockKron_two_mul, Matrix.mul_one, vecMulVec_mul_ket0]
    rfl
  rw [← hTE, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-! ### The physical gadget -/

/-- **The injection gadget's Kraus operator** for the discarded label `k` and the read-out `m`:
replace block `1` by the state `a`, transversal `CNOT̄`, decoded read-out `m` of block `1`, reset by
`X̄^m`, correct block `0` by `S̄^m` (the transversal `S†`). -/
def injKraus (a : (Fin 7 → Fin 2) → ℂ) (k : Fin 7 → Fin 2) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  blockKron ![sTransversalᴴ ^ (m : ℕ), pauliMat allOnes 0 ^ (m : ℕ) * logProj m] * cnotT
    * blockKron ![1, vecMulVec a (Pi.single k 1)]

/-- **The injection gadget**, with the state `a` prepared in the ancilla block. -/
def injChannel (a : (Fin 7 → Fin 2) → ℂ) (ρ : Matrix PairReg PairReg ℂ) :
    Matrix PairReg PairReg ℂ :=
  ∑ k, ∑ m, injKraus a k m * ρ * (injKraus a k m)ᴴ

theorem pow_mul_of_mul_eq {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : Matrix α α ℂ} {E : Matrix α β ℂ} {B : Matrix β β ℂ} (h : A * E = E * B) (n : ℕ) :
    A ^ n * E = E * B ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc]

/-- Two block operators intertwined with the encoder, one per block, are intertwined with the pair
encoder. -/
theorem blockKron_two_mul_pairEnc {A B : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    {A' B' : Matrix (Fin 2) (Fin 2) ℂ} (hA : A * steaneEnc = steaneEnc * A')
    (hB : B * steaneEnc = steaneEnc * B') :
    blockKron ![A, B] * pairEnc = pairEnc * blockKron ![A', B'] := by
  rw [pairEnc, blockKron_mul, blockKron_mul]
  congr 1
  funext b
  fin_cases b
  · exact hA
  · exact hB

theorem vecMulVec_single_mul_steaneEnc (v : Fin 2 → ℂ) (k : Fin 7 → Fin 2) :
    vecMulVec (steaneEnc *ᵥ v) (Pi.single k 1) * steaneEnc
      = steaneEnc * vecMulVec v (steaneEnc k) := by
  rw [vecMulVec_mul, mul_vecMulVec]
  congr 1
  funext j
  simp [vecMul, dotProduct, Pi.single_apply]

/-- ★ **Every physical Kraus operator of the gadget is the logical one**: through the encoder,
`CNOT̄` is `CNOT`, the decoded read-out is `|m⟩⟨m|`, `X̄` is `X`, the transversal `S†` is `S`, and
the prepared `|Ā⟩` is `|A⟩`. -/
theorem injKraus_mul_pairEnc (k : Fin 7 → Fin 2) (m : Fin 2) :
    injKraus magicEnc k m * pairEnc = pairEnc * krausL k m := by
  have hY : blockKron ![1, vecMulVec magicEnc (Pi.single k 1)] * pairEnc
      = pairEnc * blockKron ![1, vecMulVec magicL (steaneEnc k)] :=
    blockKron_two_mul_pairEnc (by rw [Matrix.one_mul, Matrix.mul_one])
      (vecMulVec_single_mul_steaneEnc magicL k)
  have hX : blockKron ![sTransversalᴴ ^ (m : ℕ), pauliMat allOnes 0 ^ (m : ℕ) * logProj m]
        * pairEnc = pairEnc * blockKron ![sGateM ^ (m : ℕ), pX ^ (m : ℕ) * projL m] := by
    refine blockKron_two_mul_pairEnc
      (pow_mul_of_mul_eq sTransversal_conjTranspose_mul_steaneEnc _) ?_
    rw [Matrix.mul_assoc, logProj_mul_steaneEnc, ← Matrix.mul_assoc,
      pow_mul_of_mul_eq logicalX_mul_steaneEnc, Matrix.mul_assoc]
    rfl
  calc injKraus magicEnc k m * pairEnc
      = blockKron ![sTransversalᴴ ^ (m : ℕ), pauliMat allOnes 0 ^ (m : ℕ) * logProj m]
          * (cnotT * (blockKron ![1, vecMulVec magicEnc (Pi.single k 1)] * pairEnc)) := by
        simp only [injKraus, Matrix.mul_assoc]
    _ = blockKron ![sTransversalᴴ ^ (m : ℕ), pauliMat allOnes 0 ^ (m : ℕ) * logProj m]
          * pairEnc * cnotL * blockKron ![1, vecMulVec magicL (steaneEnc k)] := by
        rw [hY, ← Matrix.mul_assoc cnotT, cnotT_mul_pairEnc]
        simp only [Matrix.mul_assoc]
    _ = pairEnc * krausL k m := by
        rw [hX, krausL]
        simp only [Matrix.mul_assoc]

/-- ★★★ **The injection gadget is the logical `T`.** On every encoded two-qubit input `σ`, the
physical channel — magic state, `CNOT̄`, decoded read-out, `X̄^m`, `S̄^m` — returns the encoding of
`logicalInj σ`: `T` on the data, the ancilla reset to `|0̄⟩`. -/
theorem injChannel_pairEnc (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    injChannel magicEnc (pairEnc * σ * pairEncᴴ) = pairEnc * logicalInj σ * pairEncᴴ := by
  have hterm : ∀ k m, injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ) * (injKraus magicEnc k m)ᴴ
      = pairEnc * (krausL k m * σ * (krausL k m)ᴴ) * pairEncᴴ := by
    intro k m
    have h := injKraus_mul_pairEnc k m
    have h' : pairEncᴴ * (injKraus magicEnc k m)ᴴ = (krausL k m)ᴴ * pairEncᴴ := by
      rw [← conjTranspose_mul, h, conjTranspose_mul]
    calc injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ) * (injKraus magicEnc k m)ᴴ
        = (injKraus magicEnc k m * pairEnc) * σ * (pairEncᴴ * (injKraus magicEnc k m)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h, h']
          simp only [Matrix.mul_assoc]
  rw [injChannel, ← sum_krausL, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun m _ => hterm k m

/-! ### The corrected step -/

/-- A code state of the pair is the encoding of its logical state. -/
theorem eq_pairEnc_of_isCodeState {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    ρ = pairEnc * (pairEncᴴ * ρ * pairEnc) * pairEncᴴ := by
  conv_lhs => rw [hρ, pairProj_eq]
  simp only [Matrix.mul_assoc]

/-- **The ideal injection gadget** on the physical register: decode, apply `logicalInj`, encode. -/
def idealInj (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  pairEnc * logicalInj (pairEncᴴ * ρ * pairEnc) * pairEncᴴ

/-- ★★ **On code states the gadget is the ideal one**, exactly. -/
theorem injChannel_eq_idealInj {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    injChannel magicEnc ρ = idealInj ρ := by
  conv_lhs => rw [eq_pairEnc_of_isCodeState hρ]
  exact injChannel_pairEnc _

/-- The ideal gadget keeps every state in the code. -/
theorem isCodeState_idealInj (ρ : Matrix PairReg PairReg ℂ) :
    IsCodeState pairProj (idealInj ρ) := by
  have h1 : pairProj * pairEnc = pairEnc := by
    rw [pairProj_eq, Matrix.mul_assoc, pairEnc_conjTranspose_mul, Matrix.mul_one]
  have h2 : pairEncᴴ * pairProj = pairEncᴴ := by
    rw [pairProj_eq, ← Matrix.mul_assoc, pairEnc_conjTranspose_mul, Matrix.one_mul]
  show idealInj ρ = pairProj * idealInj ρ * pairProj
  calc idealInj ρ = (pairProj * pairEnc) * logicalInj (pairEncᴴ * ρ * pairEnc)
        * (pairEncᴴ * pairProj) := by rw [h1, h2]; rfl
    _ = pairProj * idealInj ρ * pairProj := by simp only [idealInj, Matrix.mul_assoc]

/-- ★★★ **Injection is a corrected step**, given the magic state's error as a hypothesis: if the
gadget with the prepared state `a` deviates from the ideal by a correctable error (`DeviatesBy`),
the gadget followed by a recovery for that set is #96's `IsCorrectedStep` for the logical `T`. -/
theorem steane_injection_corrected {D : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ)}
    {R : Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ} (hR : IsRecovery pairProj R D)
    {a : (Fin 7 → Fin 2) → ℂ} (ha : DeviatesBy pairProj D idealInj (injChannel a)) :
    IsCorrectedStep pairProj idealInj (rect R (injChannel a)) :=
  isCorrectedStep_rect hR ha fun ρ _ => isCodeState_idealInj ρ

theorem id_mem_pairWeightOne : id ∈ pairWeightOne :=
  ⟨0, fun _ => 1, fun _ => one_mem _,
    funext fun ρ => by simp [blockFault, Controlled.gateOf_one, blockKron_one]⟩

/-- ★★ **The exact magic state discharges the hypothesis**: with `|Ā⟩` prepared exactly, the gadget
is the ideal one on code states (the deviation is the identity). -/
theorem deviatesBy_injChannel_magicEnc :
    DeviatesBy pairProj pairWeightOne idealInj (injChannel magicEnc) :=
  fun _ hρ => ⟨id, id_mem_pairWeightOne, injChannel_eq_idealInj hρ⟩

/-- ★★★ **The logical `T̄` on the two-block Steane register.** There is a recovery `R` (the pair
recovery of `SteanePairMachine.lean`) such that the injection gadget with the encoded magic state,
followed by `R`, is a corrected step for the logical `T` on block `0` — and the same holds, with the
same `R`, for any prepared state whose error leaves the gadget within the weight-one set. -/
theorem steane_injection :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsCorrectedStep pairProj idealInj (rect R.apply (injChannel magicEnc))
        ∧ ∀ a : (Fin 7 → Fin 2) → ℂ, DeviatesBy pairProj pairWeightOne idealInj (injChannel a) →
          IsCorrectedStep pairProj idealInj (rect R.apply (injChannel a)) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_pairWeightOne
  exact ⟨R, steane_injection_corrected hR deviatesBy_injChannel_magicEnc,
    fun _ ha => steane_injection_corrected hR ha⟩

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
