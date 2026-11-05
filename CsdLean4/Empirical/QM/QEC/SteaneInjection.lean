/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteanePairMachine
public import CsdLean4.Empirical.QM.QEC.SteaneLogicalIO
public import CsdLean4.Mathlib.QuantumInfo.Magic
public import CsdLean4.Empirical.QM.QEC.BitFlipChannel

/-!
# The logical `T̄` on the Steane code, by magic-state injection

**Category:** 3-Local (Empirical, QM twin). BACKLOG #230, second brick (the injection; the first
brick was the logical `S̄`, `SteaneLogicalS.lean`), #304 (a faulty magic state) and #306 (a
faulty `CNOT̄` location or read-out).

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
  discharges the hypothesis for the exact magic state.

**A faulty magic state (#304).** A fault `A` on qubit `q` of `|Ā⟩` is carried by `CNOT̄` to a
*pair* error — its `Z` part is copied to the data block — and the reset `X̄^m` signs its `Y`, `Z`
parts by the outcome, so the gadget is not one conjugation but an even mixture of two.

* `pairSpan` — unitary combinations of the pair's Pauli family, **non-product pair errors
  included**; `pairMix` — **mixtures of conjugations by them**; ★★ `exists_isRecovery_pairMix` —
  **the pair recovery undoes every such mixture** (Knill–Laflamme gives a scalar, unitarity makes it
  `1`, linearity handles the mixture); `pairWeightOne_subset_pairMix`;
* ★ `cnotT_mul_blockKron_pauliMat_mul_cnotT` — `CNOT̄ (1 ⊗ X^a Z^b) CNOT̄ = Z^b ⊗ X^a Z^b`;
  ★ `logProj_mul_pauliMat_mul_steaneEnc` — the decoded read-out does not see a single-qubit Pauli on
  the code; `xBar_pow_mul_pauliMat` — the reset's sign;
* ★ `readOp_mul_cnotConj_gateOf` — the fault passes the read-out and the feed-forward on the code,
  for an arbitrary operator by linearity from the Paulis; `faultE q A m` — the outcome-`m` pair
  error, ★ `faultE_mem_pairSpan` (unitary, and a combination of the family);
* ★★ `injKraus_fault_mul_pairEnc` — **each faulty Kraus operator is the exact one followed by
  `faultE q A m`**; ★★★ `injChannel_fault_eq` — **the faulty gadget is the ideal one followed by
  the even mixture `faultMix q A` of the two pair errors**; ★★ `deviatesBy_injChannel_fault`;

**Faults inside the gadget (#306).** A fault after one of the seven transversal `CNOT`s is a product
fault on the two blocks; it passes the feed-forward conjugated by `S†^m` on the data (exactly) and
by `X^m` on the ancilla (on the code, through the decoded read-out). A faulty read-out of one qubit
is a Kraus family on that qubit before it is read (`SteaneLogicalIO.lean`'s `measChannel` at one
faulty readout), so its errors need not be unitary.

* `pairKrausMix` — **the correctable channels of the pair**: Kraus operators in the span of the
  family, trace preserving on the code (the two-block `cssMix`); `pairMix_subset_pairKrausMix`;
  ★★ `exists_isRecovery_pairKrausMix` — **the pair recovery undoes every one** (the
  Knill–Laflamme scalars sum to `1` by trace preservation);
* `sTransversal_pow_mul_gateOf`, ★ `xBar_logProj_mul_gateOf_mul_steaneEnc`, ★
  `readOp_mul_blockKron_gateOf` — a product fault passes the read-out and the feed-forward;
  `injKrausWith`, `injKrausWith_mul_pairEnc`, ★★ `sum_conj_eq_of_mul_pairEnc` — **a gadget whose
  Kraus operators are the exact ones followed by errors is the ideal gadget followed by them**;
* `injChannelCnot`, ★★★ `injChannelCnot_eq`, ★★ `deviatesBy_injChannelCnot` — **a faulty `CNOT̄`
  location** (arbitrary unitaries on its two qubits) is the ideal gadget followed by an even mixture
  of two weight-one pair errors;
* `injChannelMeas`, ★★★ `injChannelMeas_eq`, `measMix_mem_pairKrausMix`, ★★
  `deviatesBy_injChannelMeas` — **a faulty read-out of one qubit** (any trace-preserving family) is
  the ideal gadget followed by a correctable channel;
* ★★★ `steane_injection` — **one recovery, and the corrected step for the exact magic state, for
  one arbitrary fault on the magic state, at a `CNOT̄` location, or at the read-out of one qubit,
  and for any gadget whose deviation is a correctable channel**.

## Honest scope

⚠️ Level one, one fault per gadget, an ideal recovery. The read-out fault model is a Kraus family on
the read qubit before the decoded read-out (`logProj`, a projector on the logical class, not the
full collapse of the seven qubits). The injection is not a member of `SteanePairMachine.lean`'s
gadget set, so `steane_pair_machine`'s count does not cover it (#305).

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
open QuantumInfo.Controlled

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

/-- Each outcome of the magic state's read-out has weight `1/2`. -/
theorem magicL_mul_star (m : Fin 2) : magicL m * star (magicL m) = 2⁻¹ := by
  fin_cases m
  · show invSqrtTwo * star invSqrtTwo = 2⁻¹
    rw [star_invSqrtTwo, invSqrtTwo_mul_self]
  · show invSqrtTwo * tPhase * star (invSqrtTwo * tPhase) = 2⁻¹
    rw [star_mul', star_invSqrtTwo, star_tPhase]
    calc invSqrtTwo * tPhase * (invSqrtTwo * tPhaseInv)
        = invSqrtTwo * invSqrtTwo * (tPhase * tPhaseInv) := by ring
      _ = 2⁻¹ := by rw [invSqrtTwo_mul_self, tPhase_mul_inv, mul_one]

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

/-- ★★ **One read-out outcome of the logical gadget is half the logical channel**: summed over the
discarded block, outcome `m` applies `T` with weight `|magicL m|² = 1/2`. -/
theorem sum_krausL_branch (m : Fin 2) (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ k, krausL k m * σ * (krausL k m)ᴴ = (2⁻¹ : ℂ) • logicalInj σ := by
  set TE := blockKron ![tGateM, vecMulVec ket0 ket0]
  have hk : ∀ k, krausL k m * σ * (krausL k m)ᴴ
      = (2⁻¹ : ℂ) • (TE * (blockKron ![1, vecMulVec ket0 (steaneEnc k)] * σ
          * (blockKron ![1, vecMulVec ket0 (steaneEnc k)])ᴴ) * TEᴴ) := by
    intro k
    rw [krausL_eq, conjTranspose_smul, conjTranspose_mul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
    rw [mul_comm (star (magicL m)), magicL_mul_star]
  simp only [hk, ← Finset.smul_sum]
  congr 1
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    sum_blockKron_isometry steaneEnc steaneEnc_conjTranspose_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hTE : TE * blockKron ![1, vecMulVec ket0 (Pi.single j 1)] = injIdealKraus j := by
    rw [blockKron_two_mul, Matrix.mul_one, vecMulVec_mul_ket0]
    rfl
  rw [← hTE, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- ★★ **The logical channel of the injection gadget is `logicalInj`.** Summed over the read-out
outcome (weights `1/2`, `1/2`) and over the discarded block, every branch applies `T`. -/
theorem sum_krausL (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ k, ∑ m, krausL k m * σ * (krausL k m)ᴴ = logicalInj σ := by
  rw [Finset.sum_comm, Fin.sum_univ_two, sum_krausL_branch, sum_krausL_branch, ← add_smul]
  norm_num

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

/-- The prepared encoded magic state, through the pair encoder. -/
theorem blockKron_magicEnc_mul_pairEnc (k : Fin 7 → Fin 2) :
    blockKron ![1, vecMulVec magicEnc (Pi.single k 1)] * pairEnc
      = pairEnc * blockKron ![1, vecMulVec magicL (steaneEnc k)] :=
  blockKron_two_mul_pairEnc (by rw [Matrix.one_mul, Matrix.mul_one])
    (vecMulVec_single_mul_steaneEnc magicL k)

/-- ★ **Every physical Kraus operator of the gadget is the logical one**: through the encoder,
`CNOT̄` is `CNOT`, the decoded read-out is `|m⟩⟨m|`, `X̄` is `X`, the transversal `S†` is `S`, and
the prepared `|Ā⟩` is `|A⟩`. -/
theorem injKraus_mul_pairEnc (k : Fin 7 → Fin 2) (m : Fin 2) :
    injKraus magicEnc k m * pairEnc = pairEnc * krausL k m := by
  have hY := blockKron_magicEnc_mul_pairEnc k
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

theorem injKraus_conj_pairEnc (k : Fin 7 → Fin 2) (m : Fin 2)
    (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ) * (injKraus magicEnc k m)ᴴ
      = pairEnc * (krausL k m * σ * (krausL k m)ᴴ) * pairEncᴴ := by
  have h := injKraus_mul_pairEnc k m
  have h' : pairEncᴴ * (injKraus magicEnc k m)ᴴ = (krausL k m)ᴴ * pairEncᴴ := by
    rw [← conjTranspose_mul, h, conjTranspose_mul]
  calc injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ) * (injKraus magicEnc k m)ᴴ
      = (injKraus magicEnc k m * pairEnc) * σ * (pairEncᴴ * (injKraus magicEnc k m)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h, h']
        simp only [Matrix.mul_assoc]

/-- ★★ **One read-out outcome of the physical gadget is half the logical `T`**, on every encoded
input. -/
theorem sum_injKraus_branch (m : Fin 2) (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ k, injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ) * (injKraus magicEnc k m)ᴴ
      = (2⁻¹ : ℂ) • (pairEnc * logicalInj σ * pairEncᴴ) := by
  simp only [injKraus_conj_pairEnc]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_krausL_branch, Matrix.mul_smul, Matrix.smul_mul]

/-- ★★★ **The injection gadget is the logical `T`.** On every encoded two-qubit input `σ`, the
physical channel — magic state, `CNOT̄`, decoded read-out, `X̄^m`, `S̄^m` — returns the encoding of
`logicalInj σ`: `T` on the data, the ancilla reset to `|0̄⟩`. -/
theorem injChannel_pairEnc (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    injChannel magicEnc (pairEnc * σ * pairEncᴴ) = pairEnc * logicalInj σ * pairEncᴴ := by
  rw [injChannel, Finset.sum_comm, Fin.sum_univ_two, sum_injKraus_branch, sum_injKraus_branch,
    ← add_smul]
  norm_num

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

/-! ### A faulty magic state: the correctable set of pair errors and their mixtures -/

/-- **The span set**: unitary combinations of the pair's error family (one single-qubit Pauli in
each block) — non-product pair errors included. -/
def pairSpan : Set (Matrix PairReg PairReg ℂ) :=
  {E | Eᴴ * E = 1 ∧ ∃ a : (Fin 2 → SingleErr) → ℂ, E = ∑ g, a g • pairFam g}

/-- **The correctable set of the injection**: mixtures (convex combinations) of conjugations by
members of `pairSpan`. -/
def pairMix : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ) :=
  {f | ∃ (r : ℕ) (w : Fin r → ℝ) (E : Fin r → Matrix PairReg PairReg ℂ),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, E i ∈ pairSpan)
      ∧ f = fun ρ => ∑ i, (w i : ℂ) • (E i * ρ * (E i)ᴴ)}

theorem blockFault_mem_pairSpan {q : Fin 2 → Fin 7} {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ) : blockFault q A ∈ pairSpan :=
  ⟨blockFault_conjTranspose_mul hA, _, blockFault_eq_sum q A⟩

/-- The weight-one set is inside the mixtures: a single conjugation is a mixture of one. -/
theorem pairWeightOne_subset_pairMix : pairWeightOne ⊆ pairMix := by
  rintro _ ⟨q, A, hA, rfl⟩
  refine ⟨1, fun _ => 1, fun _ => blockFault q A, fun _ => zero_le_one, by simp,
    fun _ => blockFault_mem_pairSpan hA, ?_⟩
  funext ρ
  simp

/-- ★★ **One recovery for every mixture of correctable pair errors.** The pair recovery returns a
scalar multiple of the code state for every combination of the family (Knill–Laflamme), the scalar
is `1` for a unitary combination, and a recovery is linear, so it undoes a mixture of such
errors. -/
theorem exists_isRecovery_pairMix :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairMix := by
  obtain ⟨c, R, hR⟩ := exists_pair_recovery
  have hspan : ∀ E ∈ pairSpan, ∀ ρ, IsCodeState pairProj ρ → R.apply (E * ρ * Eᴴ) = ρ := by
    rintro E ⟨hE, a, rfl⟩ ρ hρ
    have hs : ∀ σ, IsCodeState pairProj σ →
        R.apply ((∑ g, a g • pairFam g) * σ * (∑ g, a g • pairFam g)ᴴ)
          = (∑ g, ∑ h, star (a g) * a h * c g h) • σ := fun σ hσ =>
      recovery_apply_lin_comb (P := pairEnc * pairEncᴴ) hR a (by rw [← pairProj_eq]; exact hσ)
    rw [hs ρ hρ, smul_eq_one_of_unitary R hE (hs pairProj isCodeState_pairProj)
      trace_pairProj_ne_zero, one_smul]
  refine ⟨R, ?_⟩
  rintro _ ⟨r, w, E, -, hw, hE, rfl⟩ ρ hρ
  simp only [Channel.apply_sum, Channel.apply_smul, hspan _ (hE _) ρ hρ, ← Finset.sum_smul]
  rw [show (∑ i, (w i : ℂ)) = 1 by exact_mod_cast hw, one_smul]

/-! ### A faulty magic state: propagation through the gadget -/

/-- ★ **`CNOT̄` carries a Pauli on the target block to a pair Pauli**: its `Z` part is copied to the
control block, its `X` part stays. -/
theorem cnotT_mul_blockKron_pauliMat_mul_cnotT (a b : Fin 7 → Fin 2) :
    cnotT * blockKron ![1, pauliMat a b] * cnotT = blockKron ![pauliMat 0 b, pauliMat a b] := by
  ext z w
  rw [cnotT, mul_permMat_apply, permMat_mul_apply cnotPerm_involutive, blockKron_two_apply,
    blockKron_two_apply]
  simp only [cnotPerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply, pauliMat,
    add_zero]
  by_cases h : z 0 = w 0
  · simp only [h, ite_true, one_mul, pauliSign_add_right, add_assoc, add_right_inj]
    split_ifs <;> simp
  · simp [h, Ne.symm h]

/-- `X̄` squares to the identity. -/
theorem xBar_mul_self : pauliMat allOnes 0 * pauliMat allOnes 0 = 1 := by
  rw [pauliMat_mul, show allOnes + allOnes = 0 from funext fun _ => fin2_add_self _, add_zero,
    pauliMat_zero]
  simp [pauliSign, bdot, signChar]

theorem xBar_pow_mul_self (m : Fin 2) :
    pauliMat allOnes 0 ^ (m : ℕ) * pauliMat allOnes 0 ^ (m : ℕ) = 1 := by
  fin_cases m
  · simp
  · simpa using xBar_mul_self

/-- **`X̄` signs a Pauli by its `Z` part's parity**. -/
theorem xBar_pow_mul_pauliMat (m : Fin 2) (a b : Fin 7 → Fin 2) :
    pauliMat allOnes 0 ^ (m : ℕ) * pauliMat a b
      = signChar (bdot allOnes b) ^ (m : ℕ) • (pauliMat a b * pauliMat allOnes 0 ^ (m : ℕ)) := by
  fin_cases m
  · simp
  · simp only [pow_one]
    rw [pauliMat_comm, show bdot 0 a = 0 by simp [bdot], add_zero]

theorem xBar_pow_conj_pauliMat (m : Fin 2) (a b : Fin 7 → Fin 2) :
    pauliMat allOnes 0 ^ (m : ℕ) * pauliMat a b * pauliMat allOnes 0 ^ (m : ℕ)
      = signChar (bdot allOnes b) ^ (m : ℕ) • pauliMat a b := by
  rw [xBar_pow_mul_pauliMat, smul_mul_assoc, Matrix.mul_assoc, xBar_pow_mul_self, Matrix.mul_one]

theorem pauliMat_zero_left_eq_diagonal (b : Fin 7 → Fin 2) :
    pauliMat 0 b = diagonal (pauliSign b) := by
  ext z w
  by_cases h : z = w
  · subst h
    simp [pauliMat]
  · simp [pauliMat, diagonal_apply_ne _ h, Ne.symm h]

theorem sTransversal_eq_diagonal : sTransversal = diagonal fun z => Complex.I ^ hamWt z := by
  ext z w
  rw [sTransversal_apply, diagonal_apply]

/-- The transversal `S†` commutes with a `Z`-type Pauli (both are diagonal). -/
theorem commute_sTransversal_conjTranspose_pauliMat (b : Fin 7 → Fin 2) :
    Commute sTransversalᴴ (pauliMat 0 b) := by
  rw [sTransversal_eq_diagonal, pauliMat_zero_left_eq_diagonal, diagonal_conjTranspose]
  show _ * _ = _ * _
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext z
  ring

/-- The CSS label of a single-qubit Pauli. -/
def errCss : SingleErr → CssErr
  | none => (none, none)
  | some (j, t) => (if t = 1 then none else some j, if t = 0 then none else some j)

theorem cssPauli_errCss (i : SingleErr) : cssPauli (errCss i) = pauliMat (errA i) (errB i) := by
  rcases i with _ | ⟨j, t⟩
  · rfl
  · simp only [errCss, cssPauli, errA, errB]
    congr 1 <;> split_ifs <;> rfl

/-- **The decoded read-out commutes with a single-qubit Pauli on the code.** -/
theorem logProj_mul_pauliMat_mul_steaneEnc (v : Fin 2) (i : SingleErr) :
    logProj v * pauliMat (errA i) (errB i) * steaneEnc
      = pauliMat (errA i) (errB i) * logProj v * steaneEnc := by
  have h := congrArg (· * steaneEnc) (logProj_cssPauli_mul_steaneProj v (errCss i))
  simp only [Matrix.mul_assoc, steaneProj_mul_steaneEnc, cssPauli_errCss] at h
  simpa only [Matrix.mul_assoc] using h

theorem pairEnc_eq_two : pairEnc = blockKron ![steaneEnc, steaneEnc] := by
  rw [pairEnc]
  congr 1
  funext b
  fin_cases b <;> rfl

/-- The feed-forward and read-out operator of outcome `m`. -/
def readOp (m : Fin 2) : Matrix PairReg PairReg ℂ :=
  blockKron ![sTransversalᴴ ^ (m : ℕ), pauliMat allOnes 0 ^ (m : ℕ) * logProj m]

/-- ★ **A Pauli fault on the ancilla passes the read-out and the feed-forward, on the code**: after
`CNOT̄` it is a pair Pauli, the decoded read-out does not see it, the reset `X̄^m` signs it. -/
theorem readOp_mul_cnotConj_pauliMat (m : Fin 2) (i : SingleErr) :
    readOp m * (cnotT * blockKron ![1, pauliMat (errA i) (errB i)] * cnotT) * pairEnc
      = (cnotT * blockKron ![1, pauliMat allOnes 0 ^ (m : ℕ) * pauliMat (errA i) (errB i)
          * pauliMat allOnes 0 ^ (m : ℕ)] * cnotT) * readOp m * pairEnc := by
  rw [xBar_pow_conj_pauliMat, blockKron_two_smul_right, Matrix.mul_smul, Matrix.smul_mul,
    cnotT_mul_blockKron_pauliMat_mul_cnotT, Matrix.smul_mul, Matrix.smul_mul, readOp,
    pairEnc_eq_two, blockKron_two_mul, blockKron_two_mul, blockKron_two_mul, blockKron_two_mul,
    ← blockKron_two_smul_right]
  have h0 : sTransversalᴴ ^ (m : ℕ) * pauliMat 0 (errB i) * steaneEnc
      = pauliMat 0 (errB i) * sTransversalᴴ ^ (m : ℕ) * steaneEnc := by
    rw [((commute_sTransversal_conjTranspose_pauliMat (errB i)).pow_left (m : ℕ)).eq]
  have h1 : pauliMat allOnes 0 ^ (m : ℕ) * logProj m * pauliMat (errA i) (errB i) * steaneEnc
      = signChar (bdot allOnes (errB i)) ^ (m : ℕ)
        • (pauliMat (errA i) (errB i) * (pauliMat allOnes 0 ^ (m : ℕ) * logProj m)
          * steaneEnc) := by
    rw [Matrix.mul_assoc _ (logProj m), Matrix.mul_assoc, logProj_mul_pauliMat_mul_steaneEnc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, xBar_pow_mul_pauliMat, smul_mul_assoc,
      Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  rw [h0, h1]

theorem blockKron_two_sum_right {ι L L' : Type*} [Fintype ι] (A : Matrix L L' ℂ) (c : ι → ℂ)
    (B : ι → Matrix L L' ℂ) :
    blockKron ![A, ∑ i, c i • B i] = ∑ i, c i • blockKron ![A, B i] := by
  ext k l
  simp only [blockKron_two_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The pair error of a fault `A` on qubit `q` of the magic state, on read-out outcome `m`**: the
fault carried through `CNOT̄` and signed by the reset `X̄^m`. -/
def faultE (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) : Matrix PairReg PairReg ℂ :=
  cnotT * blockKron ![1, pauliMat allOnes 0 ^ (m : ℕ) * gateOf q A * pauliMat allOnes 0 ^ (m : ℕ)]
    * cnotT

/-- ★ **An arbitrary single-qubit fault on the ancilla passes the read-out and the feed-forward,
on the code**, by linearity from the Paulis. -/
theorem readOp_mul_cnotConj_gateOf (m : Fin 2) (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    readOp m * (cnotT * blockKron ![1, gateOf q A] * cnotT) * pairEnc
      = faultE q A m * readOp m * pairEnc := by
  rw [faultE, gateOf_eq_sum_pauliMat]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    blockKron_two_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [readOp_mul_cnotConj_pauliMat]

/-- ★★ **A faulty magic state's Kraus operator is the exact one followed by the pair error**, on the
code: `K_{k,m}(A|Ā⟩) E = faultE q A m · K_{k,m}(|Ā⟩) E`. -/
theorem injKraus_fault_mul_pairEnc (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 7 → Fin 2) (m : Fin 2) :
    injKraus (gateOf q A *ᵥ magicEnc) k m * pairEnc
      = faultE q A m * (injKraus magicEnc k m * pairEnc) := by
  have hG : blockKron ![1, vecMulVec (gateOf q A *ᵥ magicEnc) (Pi.single k 1)]
      = blockKron ![1, gateOf q A] * blockKron ![1, vecMulVec magicEnc (Pi.single k 1)] := by
    rw [blockKron_two_mul, Matrix.one_mul, mul_vecMulVec]
  have hY := blockKron_magicEnc_mul_pairEnc k
  calc injKraus (gateOf q A *ᵥ magicEnc) k m * pairEnc
      = readOp m * (cnotT * blockKron ![1, gateOf q A] * cnotT) * pairEnc
          * (cnotL * blockKron ![1, vecMulVec magicL (steaneEnc k)]) := by
        rw [injKraus, hG, ← readOp]
        simp only [Matrix.mul_assoc]
        rw [hY, ← Matrix.mul_assoc cnotT pairEnc, cnotT_mul_pairEnc, Matrix.mul_assoc pairEnc cnotL,
          ← Matrix.mul_assoc cnotL cnotL, cnotL_mul_self, Matrix.one_mul]
    _ = faultE q A m * (injKraus magicEnc k m * pairEnc) := by
        rw [readOp_mul_cnotConj_gateOf, injKraus, ← readOp]
        simp only [Matrix.mul_assoc]
        rw [hY, ← Matrix.mul_assoc cnotT pairEnc, cnotT_mul_pairEnc]
        simp only [Matrix.mul_assoc]

theorem xBar_pow_mem_unitaryGroup (m : Fin 2) :
    pauliMat allOnes 0 ^ (m : ℕ) ∈ Matrix.unitaryGroup (Fin 7 → Fin 2) ℂ :=
  pow_mem (Matrix.mem_unitaryGroup_iff'.2 (by
    rw [Matrix.star_eq_conjTranspose]; exact pauliMat_conjTranspose_mul_self _ _)) _

/-- The pair error is unitary. -/
theorem faultE_conjTranspose_mul {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : Fin 7) (m : Fin 2) :
    (faultE q A m)ᴴ * faultE q A m = 1 := by
  set U := pauliMat allOnes 0 ^ (m : ℕ) * gateOf q A * pauliMat allOnes 0 ^ (m : ℕ)
  have hU : Uᴴ * U = 1 := by
    have hmem : U ∈ Matrix.unitaryGroup (Fin 7 → Fin 2) ℂ :=
      mul_mem (mul_mem (xBar_pow_mem_unitaryGroup m) (gateOf_mem_unitaryGroup q hA))
        (xBar_pow_mem_unitaryGroup m)
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hmem
  have hB : (blockKron ![1, U])ᴴ * blockKron ![1, U] = 1 := by
    rw [blockKron_two_conjTranspose, blockKron_two_mul, conjTranspose_one, Matrix.one_mul, hU,
      show ![(1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), 1] = fun _ => 1 from
        funext fun b => by fin_cases b <;> rfl, blockKron_one]
  rw [faultE, conjTranspose_mul, conjTranspose_mul, cnotT_conjTranspose]
  calc cnotT * ((blockKron ![1, U])ᴴ * cnotT) * (cnotT * blockKron ![1, U] * cnotT)
      = cnotT * ((blockKron ![1, U])ᴴ * (cnotT * cnotT) * blockKron ![1, U]) * cnotT := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cnotT_mul_self, Matrix.mul_one, hB, Matrix.mul_one, cnotT_mul_self]

/-- The `Z` part of a single-qubit Pauli: what `CNOT̄` copies to the control block. -/
def zPart : SingleErr → SingleErr
  | none => none
  | some (j, t) => if t = 0 then none else some (j, 1)

theorem pairFam_zPart (i : SingleErr) :
    pairFam ![zPart i, i] = blockKron ![pauliMat 0 (errB i), pauliMat (errA i) (errB i)] := by
  rw [pairFam]
  congr 1
  funext b
  fin_cases b
  · rcases i with _ | ⟨j, t⟩
    · rfl
    · show pauliMat (errA (zPart (some (j, t)))) (errB (zPart (some (j, t))))
        = pauliMat 0 (errB (some (j, t)))
      by_cases ht : t = 0
      · simp [zPart, errA, errB, ht]
      · simp [zPart, errA, errB, ht]
  · rfl

/-- **The pair error is a combination of the pair's error family** — not a product in general. -/
theorem faultE_mem_pairSpan {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : Fin 7) (m : Fin 2) :
    faultE q A m ∈ pairSpan := by
  refine ⟨faultE_conjTranspose_mul hA q m,
    fun g => ∑ i, if ![zPart i, i] = g then
      singleCoeff q A i * signChar (bdot allOnes (errB i)) ^ (m : ℕ) else 0, ?_⟩
  have hsum : faultE q A m = ∑ i, (singleCoeff q A i * signChar (bdot allOnes (errB i)) ^ (m : ℕ))
      • pairFam ![zPart i, i] := by
    rw [faultE, gateOf_eq_sum_pauliMat]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      xBar_pow_conj_pauliMat, smul_smul, blockKron_two_sum_right,
      cnotT_mul_blockKron_pauliMat_mul_cnotT, pairFam_zPart]
  rw [hsum]
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp

/-- **The faulty gadget's deviation**: the even mixture, over the read-out outcome, of the two pair
errors. -/
def faultMix (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ :=
  fun ρ => ∑ m : Fin 2, ((2⁻¹ : ℝ) : ℂ) • (faultE q A m * ρ * (faultE q A m)ᴴ)

theorem faultMix_mem_pairMix {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : Fin 7) : faultMix q A ∈ pairMix :=
  ⟨2, fun _ => 2⁻¹, faultE q A, fun _ => by norm_num, by norm_num,
    fun m => faultE_mem_pairSpan hA q m, rfl⟩

/-- ★★★ **A faulty magic state is the ideal gadget followed by a mixture of correctable pair
errors.** With an arbitrary operator `A` on any one qubit `q` of the prepared `|Ā⟩`, the gadget on a
code state is the ideal output, conjugated by the outcome-`m` pair error with weight `1/2` each. -/
theorem injChannel_fault_eq (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ)
    {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    injChannel (gateOf q A *ᵥ magicEnc) ρ = faultMix q A (idealInj ρ) := by
  have hterm : ∀ (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) k m,
      injKraus (gateOf q A *ᵥ magicEnc) k m * (pairEnc * σ * pairEncᴴ)
          * (injKraus (gateOf q A *ᵥ magicEnc) k m)ᴴ
        = faultE q A m * (injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ)
          * (injKraus magicEnc k m)ᴴ) * (faultE q A m)ᴴ := by
    intro σ k m
    have h := injKraus_fault_mul_pairEnc q A k m
    have h' : pairEncᴴ * (injKraus (gateOf q A *ᵥ magicEnc) k m)ᴴ
        = (injKraus magicEnc k m * pairEnc)ᴴ * (faultE q A m)ᴴ := by
      rw [← conjTranspose_mul, h, conjTranspose_mul]
    calc injKraus (gateOf q A *ᵥ magicEnc) k m * (pairEnc * σ * pairEncᴴ)
          * (injKraus (gateOf q A *ᵥ magicEnc) k m)ᴴ
        = (injKraus (gateOf q A *ᵥ magicEnc) k m * pairEnc) * σ
          * (pairEncᴴ * (injKraus (gateOf q A *ᵥ magicEnc) k m)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h, h', conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  conv_lhs => rw [eq_pairEnc_of_isCodeState hρ]
  rw [injChannel, Finset.sum_comm]
  simp only [hterm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_injKraus_branch, Matrix.mul_smul, Matrix.smul_mul,
    show ((2⁻¹ : ℝ) : ℂ) = 2⁻¹ by push_cast; rfl]
  rfl

/-- ★★ **A single fault on the magic state stays within the correctable set**: #96's `DeviatesBy`
for the mixtures of pair errors, for an arbitrary unitary fault on any one qubit. -/
theorem deviatesBy_injChannel_fault {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : Fin 7) :
    DeviatesBy pairProj pairMix idealInj (injChannel (gateOf q A *ᵥ magicEnc)) :=
  fun _ hρ => ⟨faultMix q A, faultMix_mem_pairMix hA q, injChannel_fault_eq q A hρ⟩

/-! ### Faults inside the gadget: the correctable channels -/

/-- **The correctable channels of the pair**: channels whose Kraus operators are combinations of the
pair's error family and which are trace preserving on the code — the two-block `cssMix`. -/
def pairKrausMix : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ) :=
  {f | ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix PairReg PairReg ℂ),
    (∀ i, ∃ a : (Fin 2 → SingleErr) → ℂ, K i = ∑ g, a g • pairFam g)
      ∧ pairProj * (∑ i, (K i)ᴴ * K i) * pairProj = pairProj
      ∧ f = fun ρ => ∑ i, K i * ρ * (K i)ᴴ}

/-- The mixtures of unitary pair errors are correctable channels: `√w • E` are their Kraus
operators. -/
theorem pairMix_subset_pairKrausMix : pairMix ⊆ pairKrausMix := by
  rintro _ ⟨r, w, E, hw0, hw, hE, rfl⟩
  have hsq : ∀ i, star ((Real.sqrt (w i) : ℝ) : ℂ) * ((Real.sqrt (w i) : ℝ) : ℂ) = (w i : ℂ) := by
    intro i
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw0 i)]
  have hsq' : ∀ i, ((Real.sqrt (w i) : ℝ) : ℂ) * star ((Real.sqrt (w i) : ℝ) : ℂ) = (w i : ℂ) :=
    fun i => by rw [mul_comm, hsq]
  refine ⟨Fin r, inferInstance, fun i => ((Real.sqrt (w i) : ℝ) : ℂ) • E i, fun i => ?_, ?_, ?_⟩
  · obtain ⟨-, a, ha⟩ := hE i
    refine ⟨fun g => ((Real.sqrt (w i) : ℝ) : ℂ) * a g, ?_⟩
    show _ • E i = _
    rw [ha, Finset.smul_sum]
    simp only [smul_smul]
  · have h1 : ∑ i, (((Real.sqrt (w i) : ℝ) : ℂ) • E i)ᴴ * (((Real.sqrt (w i) : ℝ) : ℂ) • E i)
        = 1 := by
      simp only [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsq',
        (hE _).1]
      rw [← Finset.sum_smul, show (∑ i, (w i : ℂ)) = 1 by exact_mod_cast hw, one_smul]
    rw [h1, Matrix.mul_one, pairProj_mul_self]
  · funext ρ
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsq]

/-- ★★ **One recovery for every correctable channel of the pair.** Each Kraus operator returns a
scalar multiple of the code state (Knill–Laflamme); the scalars sum to `1`, because the recovery and
the channel both preserve the trace of the code projector. -/
theorem exists_isRecovery_pairKrausMix :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairKrausMix := by
  obtain ⟨c, R, hR⟩ := exists_pair_recovery
  refine ⟨R, ?_⟩
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩ ρ hρ
  choose a ha using hK
  set s : ι → ℂ := fun i => ∑ g, ∑ h, star (a i g) * a i h * c g h
  have hs : ∀ σ, IsCodeState pairProj σ →
      R.apply (∑ i, K i * σ * (K i)ᴴ) = (∑ i, s i) • σ := by
    intro σ hσ
    rw [Channel.apply_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i]
    exact recovery_apply_lin_comb (P := pairEnc * pairEncᴴ) hR (a i)
      (by rw [← pairProj_eq]; exact hσ)
  have hone : ∑ i, s i = 1 := by
    have h := congrArg Matrix.trace (hs pairProj isCodeState_pairProj)
    rw [R.apply_trace, Matrix.trace_smul, smul_eq_mul, Matrix.trace_sum] at h
    have htr : ∑ i, (K i * pairProj * (K i)ᴴ).trace = pairProj.trace := by
      calc ∑ i, (K i * pairProj * (K i)ᴴ).trace
          = (pairProj * (∑ i, (K i)ᴴ * K i) * pairProj).trace := by
            rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have e1 : (K i * pairProj * (K i)ᴴ).trace = ((K i)ᴴ * K i * pairProj).trace := by
              rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
            have e2 : (pairProj * ((K i)ᴴ * K i) * pairProj).trace
                = ((K i)ᴴ * K i * pairProj).trace := by
              rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, pairProj_mul_self,
                Matrix.trace_mul_comm]
            rw [e1, e2]
        _ = pairProj.trace := by rw [htp]
    rw [htr] at h
    exact mul_right_cancel₀ trace_pairProj_ne_zero (by rw [one_mul]; exact h.symm)
  rw [hs ρ hρ, hone, one_smul]

/-! ### Faults inside the gadget: propagation -/

theorem sDagM_conjTranspose_mul_self : sDagMᴴ * sDagM = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp sDagM_mem_unitaryGroup

theorem pX_mem_unitaryGroup : pX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_unitaryGroup_iff'.2 ?_
  rw [Matrix.star_eq_conjTranspose, pX_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transversal `S†` carries a one-qubit fault through itself, conjugated by `S†`. -/
theorem sTransversal_pow_mul_gateOf (m : Fin 2) (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    sTransversalᴴ ^ (m : ℕ) * gateOf q A
      = gateOf q (sDagM ^ (m : ℕ) * A * (sDagM ^ (m : ℕ))ᴴ) * sTransversalᴴ ^ (m : ℕ) := by
  fin_cases m
  · simp
  · simp only [pow_one]
    rw [← blockKron_sDagM_eq]
    exact PairGadget.blockKron_mul_gateOf_of_unitary sDagM_conjTranspose_mul_self q A

/-- `X̄` conjugates a one-qubit fault by `X`. -/
theorem xBar_pow_mul_gateOf_mul_xBar_pow (m : Fin 2) (q : Fin 7) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliMat allOnes 0 ^ (m : ℕ) * gateOf q B * pauliMat allOnes 0 ^ (m : ℕ)
      = gateOf q (pX ^ (m : ℕ) * B * pX ^ (m : ℕ)) := by
  fin_cases m
  · simp
  · have hX : pXᴴ * pX = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp pX_mem_unitaryGroup
    simp only [pow_one]
    rw [← blockKron_pX_eq_pauliMat, PairGadget.blockKron_mul_gateOf_of_unitary hX, Matrix.mul_assoc,
      blockKron_pX_eq_pauliMat, xBar_mul_self, Matrix.mul_one, pX_conjTranspose]

theorem xBar_logProj_mul_pauliMat_mul_steaneEnc (m : Fin 2) (i : SingleErr) :
    pauliMat allOnes 0 ^ (m : ℕ) * logProj m * pauliMat (errA i) (errB i) * steaneEnc
      = signChar (bdot allOnes (errB i)) ^ (m : ℕ)
        • (pauliMat (errA i) (errB i) * (pauliMat allOnes 0 ^ (m : ℕ) * logProj m)
          * steaneEnc) := by
  rw [Matrix.mul_assoc _ (logProj m), Matrix.mul_assoc, logProj_mul_pauliMat_mul_steaneEnc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, xBar_pow_mul_pauliMat, smul_mul_assoc,
    Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

/-- **A one-qubit fault on the measured block passes the decoded read-out and the reset, on the
code**, conjugated by `X^m` — by linearity from the Paulis. -/
theorem xBar_logProj_mul_gateOf_mul_steaneEnc (m : Fin 2) (q : Fin 7)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliMat allOnes 0 ^ (m : ℕ) * logProj m * gateOf q B * steaneEnc
      = gateOf q (pX ^ (m : ℕ) * B * pX ^ (m : ℕ))
        * (pauliMat allOnes 0 ^ (m : ℕ) * logProj m) * steaneEnc := by
  rw [← xBar_pow_mul_gateOf_mul_xBar_pow, gateOf_eq_sum_pauliMat]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xBar_logProj_mul_pauliMat_mul_steaneEnc, xBar_pow_conj_pauliMat, smul_mul_assoc,
    Matrix.smul_mul]

/-- ★ **A product fault on the two blocks passes the read-out and the feed-forward, on the code**:
on the data block it is conjugated by `S†^m` exactly, on the measured block by `X^m` on the code. -/
theorem readOp_mul_blockKron_gateOf (m : Fin 2) (q q' : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    readOp m * blockKron ![gateOf q A, gateOf q' B] * pairEnc
      = blockKron ![gateOf q (sDagM ^ (m : ℕ) * A * (sDagM ^ (m : ℕ))ᴴ),
          gateOf q' (pX ^ (m : ℕ) * B * pX ^ (m : ℕ))] * readOp m * pairEnc := by
  rw [readOp, pairEnc_eq_two, blockKron_two_mul, blockKron_two_mul, blockKron_two_mul,
    blockKron_two_mul, sTransversal_pow_mul_gateOf, xBar_logProj_mul_gateOf_mul_steaneEnc]

/-- The gadget's Kraus operator with an operator `F` acting between the `CNOT̄` and the read-out. -/
def injKrausWith (F : Matrix PairReg PairReg ℂ) (k : Fin 7 → Fin 2) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  readOp m * F * cnotT * blockKron ![1, vecMulVec magicEnc (Pi.single k 1)]

/-- An operator that passes the read-out on the code, as `F'`, leaves the exact Kraus operator
followed by `F'`. -/
theorem injKrausWith_mul_pairEnc {F F' : Matrix PairReg PairReg ℂ} {m : Fin 2}
    (h : readOp m * F * pairEnc = F' * readOp m * pairEnc) (k : Fin 7 → Fin 2) :
    injKrausWith F k m * pairEnc = F' * (injKraus magicEnc k m * pairEnc) := by
  have hY := blockKron_magicEnc_mul_pairEnc k
  calc injKrausWith F k m * pairEnc
      = readOp m * F * pairEnc * (cnotL * blockKron ![1, vecMulVec magicL (steaneEnc k)]) := by
        rw [injKrausWith]
        simp only [Matrix.mul_assoc]
        rw [hY, ← Matrix.mul_assoc cnotT pairEnc, cnotT_mul_pairEnc]
        simp only [Matrix.mul_assoc]
    _ = F' * (injKraus magicEnc k m * pairEnc) := by
        rw [h, injKraus, ← readOp]
        simp only [Matrix.mul_assoc]
        rw [hY, ← Matrix.mul_assoc cnotT pairEnc, cnotT_mul_pairEnc]
        simp only [Matrix.mul_assoc]

/-- ★★ **A gadget whose Kraus operators are the exact ones followed by errors is the ideal gadget
followed by those errors, each outcome with weight `1/2`**, on code states. -/
theorem sum_conj_eq_of_mul_pairEnc {ι : Type} [Fintype ι]
    (K : (Fin 7 → Fin 2) → Fin 2 → ι → Matrix PairReg PairReg ℂ)
    (E : Fin 2 → ι → Matrix PairReg PairReg ℂ)
    (hK : ∀ k m i, K k m i * pairEnc = E m i * (injKraus magicEnc k m * pairEnc))
    {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    ∑ k, ∑ m, ∑ i, K k m i * ρ * (K k m i)ᴴ
      = ∑ m, ∑ i, (2⁻¹ : ℂ) • (E m i * idealInj ρ * (E m i)ᴴ) := by
  have hterm : ∀ (σ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) k m i,
      K k m i * (pairEnc * σ * pairEncᴴ) * (K k m i)ᴴ
        = E m i * (injKraus magicEnc k m * (pairEnc * σ * pairEncᴴ)
          * (injKraus magicEnc k m)ᴴ) * (E m i)ᴴ := by
    intro σ k m i
    have h := hK k m i
    have h' : pairEncᴴ * (K k m i)ᴴ = (injKraus magicEnc k m * pairEnc)ᴴ * (E m i)ᴴ := by
      rw [← conjTranspose_mul, h, conjTranspose_mul]
    calc K k m i * (pairEnc * σ * pairEncᴴ) * (K k m i)ᴴ
        = (K k m i * pairEnc) * σ * (pairEncᴴ * (K k m i)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h, h', conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  conv_lhs => rw [eq_pairEnc_of_isCodeState hρ]
  simp only [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_injKraus_branch, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-! ### A faulty `CNOT̄` location -/

/-- **The injection with a faulty `CNOT̄` location**: the `q`-th `CNOT` followed by the product
fault `A ⊗ B` on its two qubits (`SteaneTransversalCNOT.lean`'s `pairFault`). -/
def injChannelCnot (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix PairReg PairReg ℂ) :
    Matrix PairReg PairReg ℂ :=
  ∑ k, ∑ m, injKrausWith (pairFault q A B) k m * ρ * (injKrausWith (pairFault q A B) k m)ᴴ

/-- The outcome-`m` error of a faulty `CNOT̄` location: the fault conjugated by `S†^m` on the data
and by `X^m` on the ancilla. -/
def cnotFaultE (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) :
    Matrix PairReg PairReg ℂ :=
  pairFault q (sDagM ^ (m : ℕ) * A * (sDagM ^ (m : ℕ))ᴴ) (pX ^ (m : ℕ) * B * pX ^ (m : ℕ))

theorem pairFault_eq_blockFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pairFault q A B = blockFault (fun _ => q) ![A, B] := by
  rw [pairFault, blockFault]
  congr 1
  funext b
  fin_cases b <;> rfl

theorem cnotFaultE_mem_pairSpan {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 7) (m : Fin 2) : cnotFaultE q A B m ∈ pairSpan := by
  rw [cnotFaultE, pairFault_eq_blockFault]
  refine blockFault_mem_pairSpan fun b => ?_
  have hS : sDagM ^ (m : ℕ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := pow_mem sDagM_mem_unitaryGroup _
  have hX : pX ^ (m : ℕ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := pow_mem pX_mem_unitaryGroup _
  fin_cases b
  · refine mul_mem (mul_mem hS hA) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hS
  · exact mul_mem (mul_mem hX hB) hX

/-- The faulty `CNOT̄` gadget's deviation: the even mixture of its two outcome errors. -/
def cnotMix (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ :=
  fun ρ => ∑ m : Fin 2, ((2⁻¹ : ℝ) : ℂ) • (cnotFaultE q A B m * ρ * (cnotFaultE q A B m)ᴴ)

/-- ★★★ **A faulty `CNOT̄` location is the ideal gadget followed by a correctable mixture.** -/
theorem injChannelCnot_eq (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    injChannelCnot q A B ρ = cnotMix q A B (idealInj ρ) := by
  have h := sum_conj_eq_of_mul_pairEnc (ι := Unit)
    (fun k m _ => injKrausWith (pairFault q A B) k m) (fun m _ => cnotFaultE q A B m)
    (fun k m _ => injKrausWith_mul_pairEnc (readOp_mul_blockKron_gateOf m q q A B) k) hρ
  simp only [Fintype.sum_unique] at h
  rw [injChannelCnot, h, cnotMix, show ((2⁻¹ : ℝ) : ℂ) = 2⁻¹ by push_cast; rfl]

/-- ★★ **One faulty `CNOT̄` location stays within the correctable set**, for arbitrary unitary
faults on its two qubits. -/
theorem deviatesBy_injChannelCnot {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : Fin 7) :
    DeviatesBy pairProj pairMix idealInj (injChannelCnot q A B) :=
  fun _ hρ => ⟨cnotMix q A B, ⟨2, fun _ => 2⁻¹, cnotFaultE q A B, fun _ => by norm_num,
    by norm_num, fun m => cnotFaultE_mem_pairSpan hA hB q m, rfl⟩, injChannelCnot_eq q A B hρ⟩

/-! ### A faulty read-out -/

/-- **The injection with a faulty read-out of qubit `j`**: the Kraus family `N` on qubit `j` of the
measured block before it is read — `SteaneLogicalIO.lean`'s `measChannel` at one faulty readout (a
flipped outcome is the family `{X}`). -/
def injChannelMeas {κ : Type} [Fintype κ] (j : Fin 7) (N : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  ∑ k, ∑ m, ∑ i, injKrausWith (blockKron ![1, gateOf j (N i)]) k m * ρ
    * (injKrausWith (blockKron ![1, gateOf j (N i)]) k m)ᴴ

/-- The outcome-`m` error of the read-out fault's branch `i`. -/
def measFaultE {κ : Type} (j : Fin 7) (N : κ → Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 2) (i : κ) :
    Matrix PairReg PairReg ℂ :=
  blockKron ![1, gateOf j (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))]

theorem readOp_mul_blockKron_one_gateOf (m : Fin 2) (j : Fin 7) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    readOp m * blockKron ![1, gateOf j B] * pairEnc
      = blockKron ![1, gateOf j (pX ^ (m : ℕ) * B * pX ^ (m : ℕ))] * readOp m * pairEnc := by
  rw [readOp, pairEnc_eq_two, blockKron_two_mul, blockKron_two_mul, blockKron_two_mul,
    blockKron_two_mul, Matrix.mul_one, Matrix.one_mul, xBar_logProj_mul_gateOf_mul_steaneEnc]

/-- The faulty read-out's deviation: the even mixture, over the outcome, of its branches. -/
def measMix {κ : Type} [Fintype κ] (j : Fin 7) (N : κ → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ :=
  fun ρ => ∑ m : Fin 2, ∑ i, (2⁻¹ : ℂ) • (measFaultE j N m i * ρ * (measFaultE j N m i)ᴴ)

/-- ★★★ **A faulty read-out is the ideal gadget followed by a correctable channel.** -/
theorem injChannelMeas_eq {κ : Type} [Fintype κ] (j : Fin 7) (N : κ → Matrix (Fin 2) (Fin 2) ℂ)
    {ρ : Matrix PairReg PairReg ℂ} (hρ : IsCodeState pairProj ρ) :
    injChannelMeas j N ρ = measMix j N (idealInj ρ) :=
  sum_conj_eq_of_mul_pairEnc (fun k m i => injKrausWith (blockKron ![1, gateOf j (N i)]) k m)
    (measFaultE j N)
    (fun k m i => injKrausWith_mul_pairEnc (readOp_mul_blockKron_one_gateOf m j (N i)) k) hρ

theorem measMix_mem_pairKrausMix {κ : Type} [Fintype κ] (j : Fin 7)
    {N : κ → Matrix (Fin 2) (Fin 2) ℂ} (hN : ∑ i, (N i)ᴴ * N i = 1) :
    measMix j N ∈ pairKrausMix := by
  have hN' : ∀ m : Fin 2, ∑ i, (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))ᴴ
      * (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ)) = 1 := by
    intro m
    have hX : (pX ^ (m : ℕ))ᴴ * pX ^ (m : ℕ) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp (pow_mem pX_mem_unitaryGroup _)
    have hi : ∀ i, (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))ᴴ * (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))
        = (pX ^ (m : ℕ))ᴴ * ((N i)ᴴ * N i) * pX ^ (m : ℕ) := by
      intro i
      rw [conjTranspose_mul, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((pX ^ (m : ℕ))ᴴ) (pX ^ (m : ℕ)), hX, Matrix.one_mul]
    rw [Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_mul, ← Finset.mul_sum, hN,
      Matrix.mul_one, hX]
  refine ⟨Fin 2 × κ, inferInstance, fun p => invSqrtTwo • measFaultE j N p.1 p.2, fun p => ?_, ?_,
    ?_⟩
  · refine ⟨fun g => invSqrtTwo
      * ∏ b, singleCoeff (![j, j] b) (![1, pX ^ (p.1 : ℕ) * N p.2 * pX ^ (p.1 : ℕ)] b) (g b), ?_⟩
    show invSqrtTwo • measFaultE j N p.1 p.2 = _
    have hE : measFaultE j N p.1 p.2
        = blockFault ![j, j] ![1, pX ^ (p.1 : ℕ) * N p.2 * pX ^ (p.1 : ℕ)] := by
      rw [measFaultE, blockFault]
      congr 1
      funext b
      fin_cases b
      · exact (Controlled.gateOf_one j).symm
      · rfl
    rw [hE, blockFault_eq_sum, Finset.smul_sum]
    simp only [smul_smul]
  · have h1 : ∑ p : Fin 2 × κ, (invSqrtTwo • measFaultE j N p.1 p.2)ᴴ
        * (invSqrtTwo • measFaultE j N p.1 p.2) = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, star_invSqrtTwo,
        invSqrtTwo_mul_self, measFaultE, blockKron_two_conjTranspose, blockKron_two_mul,
        conjTranspose_one, Matrix.one_mul, gateOf_conjTranspose, ← Controlled.gateOf_mul]
      have hsum : ∀ m : Fin 2, ∑ i, (2⁻¹ : ℂ) • blockKron ![(1 : Matrix (Fin 7 → Fin 2)
          (Fin 7 → Fin 2) ℂ), gateOf j ((pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))ᴴ
            * (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ)))] = (2⁻¹ : ℂ) • 1 := by
        intro m
        rw [← Finset.smul_sum]
        congr 1
        have h := blockKron_two_sum_right (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
          (fun _ : κ => (1 : ℂ))
          (fun i => gateOf j ((pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))ᴴ
            * (pX ^ (m : ℕ) * N i * pX ^ (m : ℕ))))
        simp only [one_smul] at h
        rw [← h, ← gateOf_sum, hN' m, Controlled.gateOf_one,
          show ![(1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), 1] = fun _ => 1 from
            funext fun b => by fin_cases b <;> rfl, blockKron_one]
      simp only [hsum]
      rw [Fin.sum_univ_two, ← add_smul]
      norm_num
    rw [h1, Matrix.mul_one, pairProj_mul_self]
  · funext ρ
    rw [measMix, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_smul, smul_mul_assoc, Matrix.smul_mul, mul_smul_comm, smul_smul,
      star_invSqrtTwo, invSqrtTwo_mul_self]

/-- ★★ **One faulty read-out stays within the correctable set**, for any trace-preserving family on
the read qubit. -/
theorem deviatesBy_injChannelMeas {κ : Type} [Fintype κ] (j : Fin 7)
    {N : κ → Matrix (Fin 2) (Fin 2) ℂ} (hN : ∑ i, (N i)ᴴ * N i = 1) :
    DeviatesBy pairProj pairKrausMix idealInj (injChannelMeas j N) :=
  fun _ hρ => ⟨measMix j N, measMix_mem_pairKrausMix j hN, injChannelMeas_eq j N hρ⟩

/-- `DeviatesBy` is monotone in the correctable set. -/
theorem DeviatesBy.mono {D D' : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ)}
    {ideal G : Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ}
    (h : DeviatesBy pairProj D ideal G) (hD : D ⊆ D') : DeviatesBy pairProj D' ideal G :=
  fun ρ hρ => (h ρ hρ).imp fun _ hE => ⟨hD hE.1, hE.2⟩

/-- ★★★ **The logical `T̄` on the two-block Steane register, with one fault anywhere in the
gadget.** There is one recovery `R` (the pair recovery) for the correctable channels of the pair
such that the injection gadget followed by `R` is a corrected step for the logical `T` on block
`0`: with the exact encoded magic state; with an arbitrary unitary fault on any one qubit of the
magic state; with a faulty `CNOT̄` location (arbitrary unitaries on its two qubits); with a faulty
read-out of any one qubit (any trace-preserving family before it is read); and, generally, with
any gadget whose deviation is a correctable channel. -/
theorem steane_injection :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairKrausMix
        ∧ IsCorrectedStep pairProj idealInj (rect R.apply (injChannel magicEnc))
        ∧ (∀ (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ), A ∈ Matrix.unitaryGroup (Fin 2) ℂ →
          IsCorrectedStep pairProj idealInj (rect R.apply (injChannel (gateOf q A *ᵥ magicEnc))))
        ∧ (∀ (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ), A ∈ Matrix.unitaryGroup (Fin 2) ℂ →
          B ∈ Matrix.unitaryGroup (Fin 2) ℂ →
          IsCorrectedStep pairProj idealInj (rect R.apply (injChannelCnot q A B)))
        ∧ (∀ (κ : Type) [Fintype κ] (j : Fin 7) (N : κ → Matrix (Fin 2) (Fin 2) ℂ),
          ∑ i, (N i)ᴴ * N i = 1 →
          IsCorrectedStep pairProj idealInj (rect R.apply (injChannelMeas j N)))
        ∧ ∀ G : Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ,
          DeviatesBy pairProj pairKrausMix idealInj G →
          IsCorrectedStep pairProj idealInj (rect R.apply G) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_pairKrausMix
  have hstep : ∀ G, DeviatesBy pairProj pairKrausMix idealInj G →
      IsCorrectedStep pairProj idealInj (rect R.apply G) :=
    fun _ hG => isCorrectedStep_rect hR hG fun ρ _ => isCodeState_idealInj ρ
  have hsub : pairWeightOne ⊆ pairKrausMix :=
    pairWeightOne_subset_pairMix.trans pairMix_subset_pairKrausMix
  exact ⟨R, hR, hstep _ (deviatesBy_injChannel_magicEnc.mono hsub),
    fun q A hA => hstep _ ((deviatesBy_injChannel_fault hA q).mono pairMix_subset_pairKrausMix),
    fun q A B hA hB => hstep _ ((deviatesBy_injChannelCnot hA hB q).mono
      pairMix_subset_pairKrausMix),
    fun _ _ j _ hN => hstep _ (deviatesBy_injChannelMeas j hN), hstep⟩

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
