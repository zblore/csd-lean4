/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneMachineConcat
public import CsdLean4.Empirical.QM.QEC.SteaneTransversalCNOT
public import CsdLean4.Empirical.QM.QEC.SteaneLogicalS

/-!
# The two-block Steane machine: `CNOT̄` in the gadget set

**Category:** 3-Local (Empirical, QM twin). BACKLOG #226 (QC chain, link 12).

`SteaneMachine.lean` (#207) discharged the gadget-set premise for `H̄`, `X̄`, `Z̄` on one block.
The remaining Clifford generator, the transversal `CNOT̄`, acts on two blocks
(`SteaneTransversalCNOT.lean`), so it could not sit in that machine. This module moves the machine
to the two-block register `Fin 2 → Fin 7 → Fin 2` and puts all four gates — with the logical `S̄`
(`SteaneLogicalS.lean`), five — in one gadget set.

* `isCodeState_conj_of_commute` — conjugation by a matrix commuting with a Hermitian projector keeps
  code states in the code;
* `pairProj`, `pairProj_eq` (`= pairEnc pairEncᴴ`), `isCodeState_pairProj`,
  `trace_pairProj_ne_zero` — **the two-block code projector**;
* `blockFault`, `blockFault_eq_sum`, `blockFault_conjTranspose_mul` — a fault on one qubit of each
  block; ★★ `exists_pairRecovery` — **one channel undoes every unitary fault of weight at most one
  per block** (the scalar of Knill–Laflamme is fixed to `1` on the projector itself, a code state of
  nonzero trace); `pairWeightOne`, ★ `exists_isRecovery_pairWeightOne` — the second correctable set
  and the pair recovery as #96's `IsRecovery`;
* `PairGadget` — **the gadget set**: `H̄`, `X̄`, `Z̄` (`single`) and `S̄` (`phase`) on either
  block, and `CNOT̄`
  (`cnot`); `PairGadget.op_mul_pairProj`, ★★ `PairGadget.isCodeState_ideal` — every gadget keeps the
  code (for `CNOT̄` from `cnotT_mul_pairEnc`);
* `faultOp`, `PairGadget.faulty`, `PairGadget.step` — a fault pattern over the seven locations;
  `exists_eq_of_card_le_one`, `exists_faultOp_eq_blockFault` — a good pattern is one location's
  fault; ★★ `PairGadget.deviatesBy_faulty` — **the one-fault bound for every gadget**;
* `PairGadget.onBlock_mul_blockFault`, `PairGadget.propagatesD_onBlock`,
  ★★ `PairGadget.propagatesD_single`, ★★ `PairGadget.propagatesD_phase` — **transversality** for
  the single-block gadgets on the two-block register;
* ★★★ `steane_pairGadgetSet_corrected` — **every good step of the gadget set is an
  `IsCorrectedStep`**, one recovery for all; ★★★ `steane_pair_machine` — **the Steane machine over
  `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄`**, generators of the two-qubit Clifford group: a pattern with no
  bad gadget gives exactly the ideal output, and under independent location faults of rate at
  most `p` the output is ideal with probability at least `1 − 21 N p²`.

## Honest scope

⚠️ **The fault model at a location.** Location `q` of every gadget is the pair of qubits `q` of the
two blocks, and a fault there is an arbitrary unitary on each of those qubits, in product form
(`faultOp`). For `CNOT̄` that is the gate's own pair; for a single-block gadget it is the gate's
qubit together with the idle qubit `q` of the other block, so a fault on the gate alone is the
case where the second factor is `1`. Non-product faults on a `CNOT` location are not stated (as in
`SteaneTransversalCNOT.lean`). The count of locations per gadget stays `7`, so the threshold bound
is #207's `21 N p²` unchanged.

⚠️ **`PropagatesD` for `CNOT̄` is not stated.** The correctable set allows weight one in *each*
block. A transversal `CNOT` copies an `X` error on the control block's qubit `q₀` onto the target
block's qubit `q₀`, so with a target-block error already on `q₁ ≠ q₀` the one-set
`PropagatesD pairProj pairWeightOne` is expected to fail. The extended rectangle for `CNOT̄`
(#96's `isCorrectedStep_exRec_leading`) needs a two-set form: input errors in at most one block,
output weight one per block. The machine does not use it: `steane_pair_machine` runs on
`isCorrectedStep_rect` with an ideal recovery, as #207 does. Residue rowed.

⚠️ **As in #207:** level one, an ideal recovery (faulty recoveries are `SteaneFaultyRecovery` and
`SteaneOverlapMachine`, on one block), independent unitary faults, ideal gadgets as maps and the
recovery as a `Channel`. The recovery is the Knill–Laflamme channel of the two-block code, not two
per-block recoveries. A fault-tolerant `T̄` is not in the set (#230); `S̄` joined it with
#230's first brick (`SteaneLogicalS.lean`).

References: D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008) 1207; P. Aliferis, D. Gottesman,
J. Preskill, Quantum Inf. Comput. 6 (2006) 97; M. Nielsen, I. Chuang, *Quantum Computation and
Quantum Information* §10.6; `specs/BACKLOG.md` #226, #207, #96, #62 (f);
`Empirical/QM/QEC/SteaneMachine.lean` (`steane_machine`),
`Empirical/QM/QEC/SteaneTransversalCNOT.lean` (`cnotT_mul_pairEnc`, `exists_pair_recovery`),
`Mathlib/QuantumInfo/ExtendedRectangle.lean`, `Mathlib/QuantumInfo/LevelReduction.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
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

/-- The two-block register: qubit `q` of block `b` is `z b q`. -/
abbrev PairReg : Type := Fin 2 → Fin 7 → Fin 2

/-! ### Code preservation from commutation -/

/-- **Conjugation by a matrix commuting with a Hermitian projector keeps code states in the
code.** -/
theorem isCodeState_conj_of_commute {n : Type*} [Fintype n] {P Q ρ : Matrix n n ℂ}
    (hP : Pᴴ = P) (hQ : Q * P = P * Q) (hρ : IsCodeState P ρ) : IsCodeState P (Q * ρ * Qᴴ) := by
  have hQ' : Qᴴ * P = P * Qᴴ := by
    have h := congrArg conjTranspose hQ
    rw [conjTranspose_mul, conjTranspose_mul, hP] at h
    exact h.symm
  unfold IsCodeState at hρ ⊢
  calc Q * ρ * Qᴴ = Q * (P * ρ * P) * Qᴴ := congrArg (fun σ => Q * σ * Qᴴ) hρ
    _ = (Q * P) * ρ * (P * Qᴴ) := by simp only [Matrix.mul_assoc]
    _ = (P * Q) * ρ * (Qᴴ * P) := by rw [hQ, hQ']
    _ = P * (Q * ρ * Qᴴ) * P := by simp only [Matrix.mul_assoc]

/-! ### The two-block code projector -/

/-- **The two-block code projector**: the Steane projector on each block. -/
def pairProj : Matrix PairReg PairReg ℂ := blockKron fun _ : Fin 2 => steaneProj

theorem pairProj_eq : pairProj = pairEnc * pairEncᴴ := by
  rw [pairProj, pairEnc, blockKron_conjTranspose, blockKron_mul]
  exact congrArg blockKron (funext fun _ => steaneProj_eq)

theorem pairProj_conjTranspose : pairProjᴴ = pairProj := by
  rw [pairProj_eq, conjTranspose_mul, conjTranspose_conjTranspose]

theorem pairProj_mul_self : pairProj * pairProj = pairProj := by
  rw [pairProj_eq,
    show pairEnc * pairEncᴴ * (pairEnc * pairEncᴴ) = pairEnc * (pairEncᴴ * pairEnc) * pairEncᴴ by
      simp only [Matrix.mul_assoc],
    pairEnc_conjTranspose_mul, Matrix.mul_one]

/-- The projector is itself a code state. -/
theorem isCodeState_pairProj : IsCodeState pairProj pairProj := by
  show pairProj = pairProj * pairProj * pairProj
  rw [pairProj_mul_self, pairProj_mul_self]

/-- The projector has nonzero trace (it is `4`, the dimension of the two encoded qubits). -/
theorem trace_pairProj_ne_zero : pairProj.trace ≠ 0 := by
  rw [pairProj_eq, Matrix.trace_mul_comm, pairEnc_conjTranspose_mul, Matrix.trace_one]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-! ### The pair recovery: weight one in each block -/

/-- **A fault on one qubit of each block**: `A b` on qubit `q b` of block `b`. -/
def blockFault (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix PairReg PairReg ℂ :=
  blockKron fun b => gateOf (q b) (A b)

/-- The fault is a combination of the pair's error family, one Pauli per block. -/
theorem blockFault_eq_sum (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    blockFault q A
      = ∑ g : Fin 2 → SingleErr, (∏ b, singleCoeff (q b) (A b) (g b)) • pairFam g := by
  rw [blockFault,
    show (fun b => gateOf (q b) (A b))
        = fun b => ∑ i : SingleErr, singleCoeff (q b) (A b) i • pauliMat (errA i) (errB i) from
      funext fun b => gateOf_eq_sum_pauliMat (q b) (A b),
    blockKron_sum_smul]
  rfl

theorem blockFault_conjTranspose_mul {q : Fin 2 → Fin 7} {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ) : (blockFault q A)ᴴ * blockFault q A = 1 := by
  rw [blockFault, blockKron_conjTranspose, blockKron_mul,
    show (fun b => (gateOf (q b) (A b))ᴴ * gateOf (q b) (A b))
        = fun _ : Fin 2 => (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) from
      funext fun b => by
        rw [← Matrix.star_eq_conjTranspose]
        exact Matrix.mem_unitaryGroup_iff'.mp (gateOf_mem_unitaryGroup (q b) (hA b)),
    blockKron_one]

/-- ★★ **One channel undoes every unitary fault of weight at most one per block.** The pair
recovery of `SteaneTransversalCNOT.lean` returns a scalar multiple of the code state for every
combination of the family; the scalar depends only on the fault, and on the projector — a code state
of nonzero trace — a unitary fault forces it to be `1`. -/
theorem exists_pairRecovery :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      ∀ ρ, IsCodeState pairProj ρ → ∀ (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        R.apply (blockFault q A * ρ * (blockFault q A)ᴴ) = ρ := by
  obtain ⟨c, R, hR⟩ := exists_pair_recovery
  refine ⟨R, fun ρ hρ q A hA => ?_⟩
  have hs : ∀ σ, IsCodeState pairProj σ →
      R.apply (blockFault q A * σ * (blockFault q A)ᴴ)
        = (∑ g, ∑ h, star (∏ b, singleCoeff (q b) (A b) (g b))
            * (∏ b, singleCoeff (q b) (A b) (h b)) * c g h) • σ := by
    intro σ hσ
    rw [blockFault_eq_sum]
    exact recovery_apply_lin_comb (P := pairEnc * pairEncᴴ) hR
      (fun g => ∏ b, singleCoeff (q b) (A b) (g b)) (by rw [← pairProj_eq]; exact hσ)
  rw [hs ρ hρ, smul_eq_one_of_unitary R (blockFault_conjTranspose_mul hA)
    (hs pairProj isCodeState_pairProj) trace_pairProj_ne_zero, one_smul]

/-- **The two-block correctable set**: a unitary fault on at most one qubit of each block. -/
def pairWeightOne : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ) :=
  {f | ∃ (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
      ∧ f = fun ρ => blockFault q A * ρ * (blockFault q A)ᴴ}

/-- ★ **The pair recovery is a recovery for the two-block correctable set**, in #96's sense. -/
theorem exists_isRecovery_pairWeightOne :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairWeightOne := by
  obtain ⟨R, hR⟩ := exists_pairRecovery
  refine ⟨R, ?_⟩
  rintro _ ⟨q, A, hA, rfl⟩ ρ hρ
  exact hR ρ hρ q A hA

/-! ### The gadget set -/

/-- The transversal operator of a single-block gadget: its gate on each of the seven qubits. -/
def Gadget.transversal (G : Gadget) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron fun _ : Fin 7 => G.gate

/-- Each single-block gadget commutes with the Steane code projector. -/
theorem Gadget.transversal_mul_steaneProj (G : Gadget) :
    G.transversal * steaneProj = steaneProj * G.transversal := by
  cases G with
  | had => exact steaneProj_mul_hadTransversal.symm
  | x =>
    show blockKron (fun _ : Fin 7 => pX) * steaneProj = steaneProj * blockKron (fun _ : Fin 7 => pX)
    rw [blockKron_pX_eq_pauliMat]
    exact logicalX_mul_steaneProj
  | z =>
    show blockKron (fun _ : Fin 7 => pZ) * steaneProj = steaneProj * blockKron (fun _ : Fin 7 => pZ)
    rw [blockKron_pZ_eq_pauliMat]
    exact logicalZ_mul_steaneProj

/-- The transversal `S†` on a block is `blockKron` of `S†`: the logical `S`. -/
theorem blockKron_sDagM_eq : blockKron (fun _ : Fin 7 => sDagM) = sTransversalᴴ := by
  rw [sTransversal, blockKron_conjTranspose, sGateM_conjTranspose]

theorem sDagM_mem_unitaryGroup : sDagM ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff.2 (by
    rw [Matrix.star_eq_conjTranspose]; exact sDagM_mul_conjTranspose)

/-- An operator `T` on block `b`, the identity on the other block. -/
def onBlock (b : Fin 2) (T : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix PairReg PairReg ℂ :=
  blockKron fun b' => if b' = b then T else 1

/-- A block operator commuting with the Steane projector commutes with the two-block projector. -/
theorem onBlock_mul_pairProj (b : Fin 2) {T : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hT : T * steaneProj = steaneProj * T) : onBlock b T * pairProj = pairProj * onBlock b T := by
  rw [onBlock, pairProj, blockKron_mul, blockKron_mul]
  refine congrArg blockKron (funext fun b' => ?_)
  by_cases h : b' = b
  · simp only [ite_eq_left h]
    exact hT
  · simp only [ite_eq_right h, Matrix.one_mul, Matrix.mul_one]

/-- **The two-block gadget set**: a single-block gadget (`H̄`, `X̄`, `Z̄`) on block `b`, the logical
phase gate `S̄` on block `b`, or the transversal `CNOT̄` from block `0` to block `1` — the Clifford
group's generators on two encoded qubits. -/
inductive PairGadget
  /-- The single-block gadget `G` on block `b`, the identity on the other block. -/
  | single (b : Fin 2) (G : Gadget)
  /-- The logical `S̄` on block `b`: the transversal `S†`
  (`sTransversal_conjTranspose_mul_steaneEnc`). -/
  | phase (b : Fin 2)
  /-- The transversal `CNOT̄`, control block `0`, target block `1`. -/
  | cnot

namespace PairGadget

/-- The ideal gadget's operator on the two-block register. -/
def op : PairGadget → Matrix PairReg PairReg ℂ
  | single b G => onBlock b G.transversal
  | phase b => onBlock b (blockKron fun _ : Fin 7 => sDagM)
  | cnot => cnotT

/-- The ideal gadget, as a map on density operators. -/
def ideal (G : PairGadget) (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  G.op * ρ * G.opᴴ

/-- Every gadget of the set commutes with the two-block code projector. -/
theorem op_mul_pairProj (G : PairGadget) : G.op * pairProj = pairProj * G.op := by
  cases G with
  | single b G => exact onBlock_mul_pairProj b G.transversal_mul_steaneProj
  | phase b =>
    show onBlock b (blockKron fun _ : Fin 7 => sDagM) * pairProj
      = pairProj * onBlock b (blockKron fun _ : Fin 7 => sDagM)
    rw [blockKron_sDagM_eq]
    exact onBlock_mul_pairProj b sTransversal_conjTranspose_mul_steaneProj
  | cnot =>
    show cnotT * pairProj = pairProj * cnotT
    have h1 : pairEncᴴ * cnotT = cnotL * pairEncᴴ := by
      have h := congrArg conjTranspose cnotT_mul_pairEnc
      rwa [conjTranspose_mul, conjTranspose_mul, cnotT_conjTranspose, cnotL_conjTranspose] at h
    rw [pairProj_eq]
    calc cnotT * (pairEnc * pairEncᴴ) = cnotT * pairEnc * pairEncᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = pairEnc * cnotL * pairEncᴴ := by rw [cnotT_mul_pairEnc]
      _ = pairEnc * (pairEncᴴ * cnotT) := by rw [h1, Matrix.mul_assoc]
      _ = pairEnc * pairEncᴴ * cnotT := (Matrix.mul_assoc _ _ _).symm

/-- ★★ **Every gadget of the set keeps code states in the code.** -/
theorem isCodeState_ideal (G : PairGadget) {ρ : Matrix PairReg PairReg ℂ}
    (hρ : IsCodeState pairProj ρ) : IsCodeState pairProj (G.ideal ρ) :=
  isCodeState_conj_of_commute pairProj_conjTranspose G.op_mul_pairProj hρ

end PairGadget

/-! ### Faults at the gadget's locations -/

/-- **The fault operator of a pattern**: if location `q` is faulty (`bs q`), the unitary `U q b`
acts on qubit `q` of block `b`, for both blocks. -/
def faultOp (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) :
    Matrix PairReg PairReg ℂ :=
  blockKron fun b => blockKron fun q => if bs q then U q b else 1

namespace PairGadget

/-- **The gadget under a fault pattern**: the ideal gadget, then the faults at its faulty
locations. -/
def faulty (G : PairGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool)
    (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  (faultOp U bs * G.op) * ρ * (faultOp U bs * G.op)ᴴ

/-- **The implemented step**: the gadget under its fault pattern, then the recovery channel. -/
def step {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ) (G : PairGadget)
    (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool)
    (ρ : Matrix PairReg PairReg ℂ) : Matrix PairReg PairReg ℂ :=
  R.apply (G.faulty U bs ρ)

end PairGadget

/-- A pattern with at most one faulty location has all its faults at one location `i`. -/
theorem exists_eq_of_card_le_one {bs : Fin 7 → Bool}
    (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    ∃ i, ∀ q, bs q = true → q = i := by
  by_cases hex : ∃ i, bs i = true
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun q hq => ?_⟩
    by_contra hne
    have hsub : ({i, q} : Finset (Fin 7)) ⊆ Finset.univ.filter fun q : Fin 7 => bs q = true := by
      intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · simpa using hi
      · rw [Finset.mem_singleton] at hr
        subst hr
        simpa using hq
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hne)] at h2
    omega
  · push Not at hex
    exact ⟨0, fun q hq => absurd hq (hex q)⟩

/-- With all faults at location `i`, the per-block fault operator is one single-qubit gate. -/
theorem blockKron_ite_eq_gateOf {bs : Fin 7 → Bool} {i : Fin 7} (hi : ∀ q, bs q = true → q = i)
    (V : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron (fun q => if bs q then V q else 1) = gateOf i (if bs i then V i else 1) := by
  rw [← blockKron_single_eq_gateOf]
  refine congrArg blockKron (funext fun q => ?_)
  by_cases hq : q = i
  · subst hq
    simp
  · have hb : bs q = false := by
      cases h : bs q
      · rfl
      · exact absurd (hi q h) hq
    simp [hb, hq]

/-- **A good pattern is one location's fault**: a weight-one-per-block fault. -/
theorem exists_faultOp_eq_blockFault {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) {bs : Fin 7 → Bool}
    (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    ∃ (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ faultOp U bs = blockFault q A := by
  obtain ⟨i, hi⟩ := exists_eq_of_card_le_one h
  refine ⟨fun _ => i, fun b => if bs i then U i b else 1, fun b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hU i b
    · exact one_mem _
  · rw [faultOp, blockFault]
    exact congrArg blockKron (funext fun b => blockKron_ite_eq_gateOf hi fun q => U q b)

namespace PairGadget

/-- ★★ **The one-fault bound for every gadget**: a gadget whose pattern has at most one faulty
location, each fault unitary, is the ideal gadget followed by a fault of weight at most one per
block — #96's `DeviatesBy` on the two-block register. -/
theorem deviatesBy_faulty (G : PairGadget) {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) {bs : Fin 7 → Bool}
    (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    DeviatesBy pairProj pairWeightOne G.ideal (G.faulty U bs) := by
  intro ρ _
  obtain ⟨q, A, hA, hF⟩ := exists_faultOp_eq_blockFault hU h
  refine ⟨fun σ => blockFault q A * σ * (blockFault q A)ᴴ, ⟨q, A, hA, rfl⟩, ?_⟩
  show (faultOp U bs * G.op) * ρ * (faultOp U bs * G.op)ᴴ
    = blockFault q A * (G.op * ρ * G.opᴴ) * (blockFault q A)ᴴ
  rw [hF, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A transversal single-qubit unitary carries a single-qubit gate through itself, conjugated:
`g^{⊗7} M_q = (g M g†)_q g^{⊗7}`. -/
theorem blockKron_mul_gateOf_of_unitary {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1)
    (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron (fun _ : Fin 7 => g) * gateOf q M
      = gateOf q (g * M * gᴴ) * blockKron (fun _ : Fin 7 => g) := by
  rw [← blockKron_single_eq_gateOf, blockKron_mul,
    ← blockKron_replace_eq_gateOf_mul (fun _ : Fin 7 => g) q (g * M * gᴴ)]
  congr 1
  funext b
  by_cases h : b = q
  · rw [ite_eq_left h, ite_eq_left h, mul_assoc (g * M), hg, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_one]

/-- A transversal gate on one block carries a fault on that block through itself, conjugated by its
gate, and leaves the other block's fault alone. -/
theorem onBlock_mul_blockFault (b : Fin 2) {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1)
    (q : Fin 2 → Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    onBlock b (blockKron fun _ : Fin 7 => g) * blockFault q A
      = blockFault q (fun b' => if b' = b then g * A b' * gᴴ else A b')
        * onBlock b (blockKron fun _ : Fin 7 => g) := by
  rw [onBlock, blockFault, blockFault, blockKron_mul, blockKron_mul]
  refine congrArg blockKron (funext fun b' => ?_)
  by_cases h : b' = b
  · simp only [ite_eq_left h]
    exact blockKron_mul_gateOf_of_unitary hg (q b') (A b')
  · simp only [ite_eq_right h, Matrix.one_mul, Matrix.mul_one]

/-- **Transversality for a transversal gate on one block**: #96's `PropagatesD` for the correctable
set of weight one per block. -/
theorem propagatesD_onBlock (b : Fin 2) {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    PropagatesD pairProj pairWeightOne fun ρ => onBlock b (blockKron fun _ : Fin 7 => g) * ρ
      * (onBlock b (blockKron fun _ : Fin 7 => g))ᴴ := by
  have hgg : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hg
  rintro _ ⟨q, A, hA, rfl⟩ ρ _
  set O := onBlock b (blockKron fun _ : Fin 7 => g)
  set A' : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun b' => if b' = b then g * A b' * gᴴ else A b'
  have hA' : ∀ b', A' b' ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro b'
    simp only [A']
    split_ifs
    · refine mul_mem (mul_mem hg (hA b')) ?_
      rw [← Matrix.star_eq_conjTranspose]
      exact Unitary.star_mem hg
    · exact hA b'
  refine ⟨fun σ => blockFault q A' * σ * (blockFault q A')ᴴ, ⟨q, A', hA', rfl⟩, ?_⟩
  show O * (blockFault q A * ρ * (blockFault q A)ᴴ) * Oᴴ
    = blockFault q A' * (O * ρ * Oᴴ) * (blockFault q A')ᴴ
  calc O * (blockFault q A * ρ * (blockFault q A)ᴴ) * Oᴴ
      = (O * blockFault q A) * ρ * (O * blockFault q A)ᴴ := by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (blockFault q A' * O) * ρ * (blockFault q A' * O)ᴴ := by
        rw [onBlock_mul_blockFault b hgg]
    _ = _ := by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/-- A single-block gadget carries a fault on its block through itself, conjugated by its gate, and
leaves the other block's fault alone. -/
theorem single_mul_blockFault (b : Fin 2) (G : Gadget) (q : Fin 2 → Fin 7)
    (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (single b G).op * blockFault q A
      = blockFault q (fun b' => if b' = b then G.gate * A b' * G.gateᴴ else A b')
        * (single b G).op :=
  onBlock_mul_blockFault b G.gate_conjTranspose_mul q A

/-- ★★ **Transversality for the single-block gadgets** on the two-block register: #96's
`PropagatesD` for the correctable set of weight one per block. -/
theorem propagatesD_single (b : Fin 2) (G : Gadget) :
    PropagatesD pairProj pairWeightOne (single b G).ideal :=
  propagatesD_onBlock b G.gate_mem_unitaryGroup

/-- ★★ **Transversality for the logical `S̄`** on the two-block register. -/
theorem propagatesD_phase (b : Fin 2) : PropagatesD pairProj pairWeightOne (phase b).ideal :=
  propagatesD_onBlock b sDagM_mem_unitaryGroup

end PairGadget

/-! ### The gadget set discharges the premise -/

/-- ★★★ **The two-block gadget set is a set of corrected steps.** One recovery channel `R` on the
two-block register serves `H̄`, `X̄`, `Z̄`, `S̄` on either block and `CNOT̄`: for every assignment
of unitary faults to the seven locations and every pattern that is **not bad** (`isBad 7 1`, at most
one faulty location), the faulty gadget followed by `R` is an `IsCorrectedStep` for the ideal gadget
— #96's `isCorrectedStep_rect` with `exists_isRecovery_pairWeightOne`,
`PairGadget.deviatesBy_faulty` and `PairGadget.isCodeState_ideal`. -/
theorem steane_pairGadgetSet_corrected :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairWeightOne
      ∧ ∀ (G : PairGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ω : ConcatPat 7 1, isBad 7 1 ω = false →
          IsCorrectedStep pairProj G.ideal (G.step R U (locPat ω)) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_pairWeightOne
  exact ⟨R, hR, fun G U hU ω hω => isCorrectedStep_rect hR
    (G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hω)) fun _ hρ => G.isCodeState_ideal hρ⟩

/-! ### The machine -/

/-- **The two-block machine's circuit**: gadget `j` is `gs j`, its fault unitaries are `U j`, and
its fault pattern is `ω j`; each gadget is run and then recovered. -/
def pairMachineCircuit {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ) {N : ℕ}
    (gs : Fin N → PairGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : CircuitPat N 7 1) : Circuit PairReg :=
  List.ofFn fun j => ((gs j).ideal, (gs j).step R (U j) (locPat (ω j)))

/-- The ideal output of the two-block machine: the ideal gadgets, in order. -/
def pairMachineIdeal {N : ℕ} (gs : Fin N → PairGadget) (ρ : Matrix PairReg PairReg ℂ) :
    Matrix PairReg PairReg ℂ :=
  runMaps (List.ofFn fun j => (gs j).ideal) ρ

theorem idealRun_pairMachineCircuit {κ : Type*} [Fintype κ] (R : Channel PairReg PairReg κ)
    {N : ℕ} (gs : Fin N → PairGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : CircuitPat N 7 1) (ρ : Matrix PairReg PairReg ℂ) :
    idealRun (pairMachineCircuit R gs U ω) ρ = pairMachineIdeal gs ρ := by
  rw [idealRun, pairMachineCircuit, pairMachineIdeal, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine over `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄`, at level one.** One recovery
channel `R` on two blocks such that, for every circuit of `N` gadgets from the set, every
assignment of unitary faults to their locations and every encoded input:

* **the deterministic premise holds**: a pattern that makes no gadget bad gives exactly the ideal
  output (`correctedRun_eq_idealRun_of_level` at level `0`);
* **the threshold statement follows**: under independent location faults of rate at most `p`, the
  output is exactly the ideal one with probability at least `1 − 21 N p²`. -/
theorem steane_pair_machine :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      ∀ (N : ℕ) (gs : Fin N → PairGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j q b, U j q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix PairReg PairReg ℂ, IsCodeState pairProj ρ →
          (∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
              correctedRun (pairMachineCircuit R gs U ω) ρ = pairMachineIdeal gs ρ)
          ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
              ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
                ≤ QuantumInfo.circuitMeasure N 7 ν 1
                    {ω | correctedRun (pairMachineCircuit R gs U ω) ρ = pairMachineIdeal gs ρ} := by
  obtain ⟨R, -, hR⟩ := steane_pairGadgetSet_corrected
  refine ⟨R, fun N gs U hU ρ hρ => ?_⟩
  have hgood : ∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
      correctedRun (pairMachineCircuit R gs U ω) ρ = pairMachineIdeal gs ρ := by
    intro ω hω
    rw [← idealRun_pairMachineCircuit R gs U ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hR (gs j) (U j) (hU j) (ω j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := 1) ν hp hν
    (out := fun ω => correctedRun (pairMachineCircuit R gs U ω) ρ)
    (ideal := pairMachineIdeal gs ρ) hgood
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
