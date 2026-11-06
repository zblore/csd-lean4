/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneTripleMachine
public import CsdLean4.Mathlib.QuantumInfo.CliffordTCount

/-!
# The three-block Steane machine is universal on its two logical qubits

**Category:** 3-Local (Empirical, QM twin). BACKLOG #308; the gate count #309.

`SteaneTripleMachine.lean`'s gadget set holds Clifford+T on two logical qubits, and
`Mathlib/QuantumInfo/CliffordTUniversal.lean` proves Clifford+T circuits dense in `U(2ᵐ)` modulo
phase. This module composes the two: the machine's logical gates are matched to the corpus's
Clifford+T vocabulary (`cliffordTGates`: `gateOf j hGateM`, `gateOf j tGateM`, `cnotGate' a b`), so
every Clifford+T circuit on two qubits is a circuit of the machine, exactly, and every two-qubit
unitary is a limit of them up to a phase.

* `dataEmb`, `dataEnc` — **data states**: a state of the two data qubits with the ancilla qubit in
  `|0⟩`, and its encoding on the three blocks; `lift3_conj_dataEmb`;
* ★ `TGadget.ideal_clifford_tripleEnc` — a lifted Clifford gadget is the lifted logical gate on
  encoded inputs (with `TGadget.ideal_tGate_tripleEnc` for the injection);
* `cnotL_eq_cnotGate'`, `cnotL_submatrix_swapQ`, `lift3_swap01` — `CNOT̄` in either direction is
  `cnotGate'`; ★ `exists_had_mul_steaneEnc` — **the transversal Hadamard's scalar has modulus one**,
  so `H̄` is `hGateM` exactly as a conjugation;
* `realised` — **the logical gates the machine realises exactly**: the two-qubit unitaries `W` for
  which some list of three-block gadgets, run ideally on every encoded data state, applies `W` to
  the data and leaves the ancilla in `|0⟩` — a submonoid, since circuits compose;
* ★ `exists_gadget_hGateM`, ★ `exists_gadget_cnotGate'`, ★ `exists_gadget_tGateM` — each
  Clifford+T gate is **one gadget** (the injection through ancilla block `2`, on either data
  block); `gateOf_hGateM_mem_realised`, `cnotGate'_mem_realised`, `gateOf_tGateM_mem_realised`;
  ★★ `cliffordTm_le_realised` —
  **every Clifford+T circuit on two qubits is realised by the machine, exactly**;
* ★★★ `steane_triple_machine_universal` — **every two-qubit unitary is, up to a global phase, a
  limit of logical gates the machine realises**; `tMachineIdeal_get` — a realising list is a
  circuit of `steane_triple_machine`, whose fault-tolerance theorem covers it;
* `exists_gadget_of_mem_cliffordTGates`, ★ `exists_gadgets_of_cliffordT` (**a Clifford+T circuit
  of `N` gates is `N` gadgets**), `isCodeState_dataEnc`; ★★★ `steane_triple_machine_count` — **the
  gate count**: for every two-qubit unitary and every `ε ≤ e`, at most `K · log(1/ε)^c` gadgets
  realise exactly a logical gate within `ε` of it up to a phase, and run as a circuit of the
  machine they give that gate's output with probability at least `1 − 21 N p²`
  (`CliffordTCount.lean`'s `exists_cliffordT_circuit_polylog`, #309).

## Honest scope

⚠️ The realisation is of the **ideal** runs on encoded data states; the faulty runs are covered by
`steane_triple_machine` (level one, an ideal recovery, unitary faults, `1 − 21 N p²` per circuit of
`N` gadgets). `steane_triple_machine_universal` is topological; the rate is
`steane_triple_machine_count`'s, whose `K` and `e` are existential (inherited from #116's net and
an uncomputed lift constant) and whose `c = skExponent` is #116's three-letter exponent. Its two
errors are kept apart: the logical gate `W` is within `ε` of the target in the operator norm, and
the run gives `W`'s output exactly with probability at least `1 − 21 N p²`; no state-level bound
combining them is stated.

References: A. Kitaev, *Russ. Math. Surv.* **52**, 1191 (1997); M. Nielsen, I. Chuang, *Quantum
Computation and Quantum Information* §4.5 and §10.6; `specs/BACKLOG.md` #308, #309;
`Empirical/QM/QEC/SteaneTripleMachine.lean`, `Mathlib/QuantumInfo/CliffordTUniversal.lean`
(`exists_phase_mem_cliffordTmLim`); `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open Controlled QuantumInfo.Controlled
open scoped ENNReal Kronecker

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### Data states: two logical data qubits, the ancilla in `|0⟩` -/

/-- **A data state on three logical qubits**: `X` on the data qubits `0`, `1`, the ancilla qubit `2`
in `|0⟩`. -/
def dataEmb (X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  lift3 1 X (vecMulVec ket0 ket0)

/-- Its encoding on the three Steane blocks. -/
def dataEnc (X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) : Matrix TripleReg TripleReg ℂ :=
  tripleEnc * dataEmb X * tripleEncᴴ

theorem lift3_conj_dataEmb (W X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    lift3 1 W 1 * dataEmb X * (lift3 1 W 1)ᴴ = dataEmb (W * X * Wᴴ) := by
  rw [dataEmb, dataEmb, lift3_conjTranspose, lift3_mul, lift3_mul, conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

theorem lift3_zero_right {α β : Type*} (σ : Equiv.Perm (Fin 3))
    (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) : lift3 σ M (0 : Matrix α β ℂ) = 0 := by
  ext z w
  simp [lift3]

theorem lift3_zero_left {α β : Type*} (σ : Equiv.Perm (Fin 3)) (N : Matrix α β ℂ) :
    lift3 σ (0 : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) N = 0 := by
  ext z w
  simp [lift3]

/-! ### The logical action of a lifted Clifford gadget -/

/-- ★ **A lifted Clifford gadget is the lifted logical gate, on encoded inputs.** -/
theorem TGadget.ideal_clifford_tripleEnc (σ : Equiv.Perm (Fin 3)) {G : PairGadget}
    {Gl : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ} (hG : G.op * pairEnc = pairEnc * Gl)
    (Y : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :
    (TGadget.mk σ (UGadget.clifford G)).ideal (tripleEnc * Y * tripleEncᴴ)
      = tripleEnc * (lift3 σ Gl 1 * Y * (lift3 σ Gl 1)ᴴ) * tripleEncᴴ := by
  have hK : lift3 σ G.op 1 * tripleEnc = tripleEnc * lift3 σ Gl 1 := by
    rw [tripleEnc_eq_lift3 σ, lift3_mul, lift3_mul, hG, Matrix.one_mul, Matrix.mul_one]
  have hK' : tripleEncᴴ * (lift3 σ G.op 1)ᴴ = (lift3 σ Gl 1)ᴴ * tripleEncᴴ := by
    rw [← conjTranspose_mul, hK, conjTranspose_mul]
  rw [TGadget.ideal, Fin.sum_univ_two]
  show lift3 σ G.op 1 * (tripleEnc * Y * tripleEncᴴ) * (lift3 σ G.op 1)ᴴ
      + lift3 σ 0 1 * (tripleEnc * Y * tripleEncᴴ) * (lift3 σ 0 1)ᴴ = _
  rw [lift3_zero_left, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  calc lift3 σ G.op 1 * (tripleEnc * Y * tripleEncᴴ) * (lift3 σ G.op 1)ᴴ
      = (lift3 σ G.op 1 * tripleEnc) * Y * (tripleEncᴴ * (lift3 σ G.op 1)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hK, hK']
        simp only [Matrix.mul_assoc]

/-! ### The gate vocabulary of `CliffordTUniversal.lean` -/

/-- The logical `CNOT` is the corpus's `cnotGate' 0 1`. -/
theorem cnotL_eq_cnotGate' : cnotL = cnotGate' (0 : Fin 2) 1 := by
  ext z w
  rw [fin_two_arrow_eq z, fin_two_arrow_eq w]
  generalize z 0 = a, z 1 = b, w 0 = c, w 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cnotL, permMat_apply, cnotPermL, cnotGate', ctrlSet, MultiControlled.blockEntry,
      Fin.forall_fin_two,
      funext_iff]

/-- The coordinate swap of the two data qubits. -/
def swapQ (c : Fin 2 → Fin 2) : Fin 2 → Fin 2 := ![c 1, c 0]

/-- The logical `CNOT` with control and target exchanged is `cnotGate' 1 0`. -/
theorem cnotL_submatrix_swapQ : cnotL.submatrix swapQ swapQ = cnotGate' (1 : Fin 2) 0 := by
  ext z w
  rw [fin_two_arrow_eq z, fin_two_arrow_eq w]
  generalize z 0 = a, z 1 = b, w 0 = c, w 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cnotL, permMat_apply, cnotPermL, cnotGate', ctrlSet, MultiControlled.blockEntry,
      Fin.forall_fin_two,
      funext_iff, swapQ]

/-- Exchanging blocks `0`, `1` (block `2` idle) is reindexing the pair by the swap. -/
theorem lift3_swap01 {α β : Type*} (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) (N : Matrix α β ℂ) :
    lift3 (Equiv.swap 0 1) M N
      = lift3 1 (M.submatrix (fun c : Fin 2 → α => ![c 1, c 0])
          (fun c : Fin 2 → β => ![c 1, c 0])) N := by
  ext z w
  simp only [lift3, submatrix_apply, kronecker_apply, split3, Equiv.coe_fn_mk]
  congr 2
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl

theorem blockKron_two_eq_gateOf_zero (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron ![M, 1] = gateOf (0 : Fin 2) M := by
  rw [← blockKron_single_eq_gateOf]
  congr 1
  funext b
  fin_cases b <;> rfl

theorem blockKron_two_eq_gateOf_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron ![1, M] = gateOf (1 : Fin 2) M := by
  rw [← blockKron_single_eq_gateOf]
  congr 1
  funext b
  fin_cases b <;> rfl

/-! ### The machine's realised logical gates -/

/-- **The logical gates the machine realises exactly**: the two-qubit unitaries `W` for which some
circuit of three-block gadgets, run ideally on every encoded data state, applies `W` to the data
and leaves the ancilla in `|0⟩`. A monoid: circuits compose. -/
def realised : Submonoid (Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) where
  carrier := {W | ∃ l : List TGadget, ∀ X,
    runMaps (l.map TGadget.ideal) (dataEnc X) = dataEnc (W * X * Wᴴ)}
  one_mem' := ⟨[], fun X => by
    show dataEnc X = dataEnc (1 * X * 1ᴴ)
    rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro W₁ W₂ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
    refine ⟨l₂ ++ l₁, fun X => ?_⟩
    rw [List.map_append, runMaps, List.foldl_append, ← runMaps, ← runMaps, h₂, h₁,
      conjTranspose_mul]
    simp only [Matrix.mul_assoc]

theorem mem_realised_of_gadget {W : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ} (T : TGadget)
    (hT : ∀ X, T.ideal (dataEnc X) = dataEnc (W * X * Wᴴ)) : W ∈ realised :=
  ⟨[T], fun X => by simpa [runMaps] using hT X⟩

/-- A scalar of modulus one does not change a conjugation. -/
theorem smul_conj_eq {n : Type*} [Fintype n] {c : ℂ} (hc : c * star c = 1)
    (M X : Matrix n n ℂ) : (c • M) * X * (c • M)ᴴ = M * X * Mᴴ := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc,
    one_smul]

/-- **The transversal Hadamard's scalar has modulus one.** -/
theorem exists_had_mul_steaneEnc :
    ∃ c : ℂ, c * star c = 1 ∧
      blockKron (fun _ : Fin 7 => Gadget.had.gate) * steaneEnc
        = steaneEnc * (c • Gadget.had.gate) := by
  obtain ⟨c, hc⟩ := Gadget.had.exists_blockKron_mul_steaneEnc
  refine ⟨c, ?_, hc⟩
  have hT : (blockKron fun _ : Fin 7 => Gadget.had.gate)ᴴ
      * blockKron (fun _ : Fin 7 => Gadget.had.gate) = 1 := by
    rw [blockKron_conjTranspose, blockKron_mul,
      show (fun _ : Fin 7 => (Gadget.had.gate)ᴴ * Gadget.had.gate) = fun _ => 1 from
        funext fun _ => Gadget.had.gate_conjTranspose_mul, blockKron_one]
  set T := blockKron fun _ : Fin 7 => Gadget.had.gate
  have h : (c • Gadget.had.gate)ᴴ * (c • Gadget.had.gate) = 1 :=
    calc (c • Gadget.had.gate)ᴴ * (c • Gadget.had.gate)
        = (c • Gadget.had.gate)ᴴ * (steaneEncᴴ * steaneEnc) * (c • Gadget.had.gate) := by
          rw [steaneEnc_conjTranspose_mul, Matrix.mul_one]
      _ = (steaneEnc * (c • Gadget.had.gate))ᴴ * (steaneEnc * (c • Gadget.had.gate)) := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (T * steaneEnc)ᴴ * (T * steaneEnc) := by rw [hc]
      _ = steaneEncᴴ * (Tᴴ * T) * steaneEnc := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, Matrix.mul_one, steaneEnc_conjTranspose_mul]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Gadget.had.gate_conjTranspose_mul] at h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h00
  rw [mul_comm]
  exact h00

/-- ★ **`H̄` on either data qubit is realised, by one gadget.** -/
theorem exists_gadget_hGateM (b : Fin 2) :
    ∃ T : TGadget, ∀ X, T.ideal (dataEnc X)
      = dataEnc (gateOf b CliffordT.hGateM * X * (gateOf b CliffordT.hGateM)ᴴ) := by
  obtain ⟨c, hc, hH⟩ := exists_had_mul_steaneEnc
  set Gl : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
    blockKron fun b' => if b' = b then c • Gadget.had.gate else 1
  have hG : (PairGadget.single b Gadget.had).op * pairEnc = pairEnc * Gl := by
    show onBlock b Gadget.had.transversal * pairEnc = pairEnc * Gl
    rw [onBlock, pairEnc, blockKron_mul, blockKron_mul]
    refine congrArg blockKron (funext fun b' => ?_)
    by_cases h : b' = b
    · simp only [ite_eq_left h]
      exact hH
    · simp only [ite_eq_right h, Matrix.one_mul, Matrix.mul_one]
  have hGl : Gl = c • gateOf b CliffordT.hGateM := by
    rw [← blockKron_single_eq_gateOf]
    ext z w
    simp only [Gl, blockKron_apply, Fin.prod_univ_two, Matrix.smul_apply, smul_eq_mul]
    fin_cases b <;> simp [Gadget.gate] <;> ring
  refine ⟨TGadget.mk 1 (UGadget.clifford (PairGadget.single b Gadget.had)), fun X => ?_⟩
  rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc 1 hG, lift3_conj_dataEmb, hGl,
    smul_conj_eq hc]

theorem gateOf_hGateM_mem_realised (b : Fin 2) : gateOf b CliffordT.hGateM ∈ realised :=
  (exists_gadget_hGateM b).elim fun T hT => mem_realised_of_gadget T hT

/-- ★ **`CNOT̄` in both directions between the data qubits is realised, by one gadget.** -/
theorem exists_gadget_cnotGate' {a b : Fin 2} (hab : a ≠ b) :
    ∃ T : TGadget, ∀ X, T.ideal (dataEnc X) = dataEnc (cnotGate' a b * X * (cnotGate' a b)ᴴ) := by
  have hG : PairGadget.cnot.op * pairEnc = pairEnc * cnotL := cnotT_mul_pairEnc
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · refine ⟨TGadget.mk 1 (UGadget.clifford PairGadget.cnot), fun X => ?_⟩
    rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc 1 hG, lift3_conj_dataEmb,
      cnotL_eq_cnotGate']
    rfl
  · refine ⟨TGadget.mk (Equiv.swap 0 1) (UGadget.clifford PairGadget.cnot), fun X => ?_⟩
    rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc _ hG, lift3_swap01,
      show cnotL.submatrix (fun c : Fin 2 → Fin 2 => ![c 1, c 0]) (fun c => ![c 1, c 0])
        = cnotGate' (1 : Fin 2) 0 from cnotL_submatrix_swapQ, lift3_conj_dataEmb]
    rfl
  · exact absurd rfl hab

theorem cnotGate'_mem_realised {a b : Fin 2} (hab : a ≠ b) : cnotGate' a b ∈ realised :=
  (exists_gadget_cnotGate' hab).elim fun T hT => mem_realised_of_gadget T hT

theorem ket0_conj_ket0 (j : Fin 2) :
    vecMulVec ket0 (Pi.single j 1) * vecMulVec ket0 ket0 * (vecMulVec ket0 (Pi.single j 1))ᴴ
      = if j = 0 then vecMulVec ket0 ket0 else 0 := by
  ext a b
  simp only [Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, Fin.sum_univ_two]
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [ket0]

/-- The injected `T` on data qubit `d`, ancilla block `2`, read on data states. -/
theorem sum_lift3_injIdealKraus_dataEmb {σ : Equiv.Perm (Fin 3)}
    {B : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ}
    (hσ : ∀ j : Fin 2, lift3 σ (injIdealKraus j) 1 = lift3 1 B (vecMulVec ket0 (Pi.single j 1)))
    (X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    ∑ j, lift3 σ (injIdealKraus j) 1 * dataEmb X * (lift3 σ (injIdealKraus j) 1)ᴴ
      = dataEmb (B * X * Bᴴ) := by
  simp only [hσ, dataEmb, lift3_conjTranspose, lift3_mul, ket0_conj_ket0]
  rw [Fin.sum_univ_two]
  simp only [ite_true, one_ne_zero, ite_false, lift3_zero_right, add_zero]

/-- ★ **`T̄` on either data qubit is realised**, by one injection through the ancilla block `2`. -/
theorem exists_gadget_tGateM (d : Fin 2) :
    ∃ T : TGadget, ∀ X, T.ideal (dataEnc X)
      = dataEnc (gateOf d CliffordT.tGateM * X * (gateOf d CliffordT.tGateM)ᴴ) := by
  have hT : CliffordT.tGateM = Steane.tGateM := rfl
  fin_cases d
  · -- data block 0 with ancilla block 2: `σ = (1 2)`
    refine ⟨TGadget.mk (Equiv.swap 1 2) UGadget.tGate, fun X => ?_⟩
    have hσ : ∀ j : Fin 2, lift3 (Equiv.swap 1 2) (injIdealKraus j) 1
        = lift3 1 (blockKron ![Steane.tGateM, 1]) (vecMulVec ket0 (Pi.single j 1)) := by
      intro j
      rw [injIdealKraus, lift3_blockKron, lift3_blockKron]
      congr 1
      funext b
      fin_cases b <;> rfl
    rw [dataEnc, dataEnc, dataEmb, ← dataEmb, TGadget.ideal_tGate_tripleEnc,
      sum_lift3_injIdealKraus_dataEmb hσ, blockKron_two_eq_gateOf_zero, hT]
    rfl
  · -- data block 1 with ancilla block 2: `σ = (0 1)(1 2)`
    refine ⟨TGadget.mk (Equiv.swap 0 1 * Equiv.swap 1 2) UGadget.tGate, fun X => ?_⟩
    have hσ : ∀ j : Fin 2, lift3 (Equiv.swap 0 1 * Equiv.swap 1 2) (injIdealKraus j) 1
        = lift3 1 (blockKron ![1, Steane.tGateM]) (vecMulVec ket0 (Pi.single j 1)) := by
      intro j
      rw [injIdealKraus, lift3_blockKron, lift3_blockKron]
      congr 1
      funext b
      fin_cases b <;> rfl
    rw [dataEnc, dataEnc, dataEmb, ← dataEmb, TGadget.ideal_tGate_tripleEnc,
      sum_lift3_injIdealKraus_dataEmb hσ, blockKron_two_eq_gateOf_one, hT]
    rfl

theorem gateOf_tGateM_mem_realised (d : Fin 2) : gateOf d CliffordT.tGateM ∈ realised :=
  (exists_gadget_tGateM d).elim fun T hT => mem_realised_of_gadget T hT

/-- ★★ **Every Clifford+T circuit on two qubits is realised by the machine, exactly.** -/
theorem cliffordTm_le_realised : cliffordTm 2 ≤ realised := by
  rw [cliffordTm, Submonoid.closure_le]
  rintro g (⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨a, b, hab, rfl⟩)
  · exact gateOf_hGateM_mem_realised j
  · exact gateOf_tGateM_mem_realised j
  · exact cnotGate'_mem_realised hab

/-- ★★★ **The three-block Steane machine is universal on its two logical qubits.** Every unitary
`V` on two qubits is, after a global phase, a limit of logical gates that circuits of the machine's
gadget set realise exactly on every encoded data state — `exists_phase_mem_cliffordTmLim`, carried
through `cliffordTm_le_realised`. -/
theorem steane_triple_machine_universal {V : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ) :
    ∃ φ : ℝ, Euler.expI φ • V ∈ realised.topologicalClosure := by
  obtain ⟨φ, hφ⟩ := exists_phase_mem_cliffordTmLim (m := 2) (by norm_num) hV
  exact ⟨φ, Submonoid.topologicalClosure_mono cliffordTm_le_realised hφ⟩

/-- The realised gates are the machine's: a list of gadgets is a circuit of `steane_triple_machine`,
whose ideal output is the list's ideal run. -/
theorem tMachineIdeal_get (l : List TGadget) (X : Matrix TripleReg TripleReg ℂ) :
    tMachineIdeal (fun j : Fin l.length => l.get j) X = runMaps (l.map TGadget.ideal) X := by
  rw [tMachineIdeal,
    show (fun j : Fin l.length => (l.get j).ideal) = TGadget.ideal ∘ l.get from rfl,
    ← List.map_ofFn, List.ofFn_get]

/-! ### The machine's gate count -/

/-- **Every Clifford+T gate is one gadget.** -/
theorem exists_gadget_of_mem_cliffordTGates {g : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ}
    (hg : g ∈ cliffordTGates 2) :
    ∃ T : TGadget, ∀ X, T.ideal (dataEnc X) = dataEnc (g * X * gᴴ) := by
  rcases hg with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact exists_gadget_hGateM j
  · exact exists_gadget_tGateM j
  · exact exists_gadget_cnotGate' hab

/-- ★ **A Clifford+T circuit of `N` gates is a list of `N` gadgets**, realising it exactly on every
encoded data state. -/
theorem exists_gadgets_of_cliffordT (l : List (Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ))
    (hl : ∀ g ∈ l, g ∈ cliffordTGates 2) :
    ∃ gs : List TGadget, gs.length = l.length ∧
      ∀ X, runMaps (gs.map TGadget.ideal) (dataEnc X) = dataEnc (l.prod * X * (l.prod)ᴴ) := by
  induction l with
  | nil => exact ⟨[], rfl, fun X => by simp [runMaps]⟩
  | cons g l ih =>
    obtain ⟨T, hT⟩ := exists_gadget_of_mem_cliffordTGates (hl g (List.mem_cons_self ..))
    obtain ⟨gs, hlen, hgs⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    refine ⟨gs ++ [T], by simp [hlen], fun X => ?_⟩
    have h1 : ∀ Y, runMaps ([T].map TGadget.ideal) Y = T.ideal Y := fun Y => rfl
    rw [List.map_append, runMaps, List.foldl_append, ← runMaps, ← runMaps, hgs, h1, hT,
      List.prod_cons, conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- An encoded data state is a code state. -/
theorem isCodeState_dataEnc (X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    IsCodeState tripleProj (dataEnc X) := by
  show dataEnc X = tripleProj * dataEnc X * tripleProj
  rw [tripleProj_eq, dataEnc]
  symm
  calc tripleEnc * tripleEncᴴ * (tripleEnc * dataEmb X * tripleEncᴴ) * (tripleEnc * tripleEncᴴ)
      = tripleEnc * (tripleEncᴴ * tripleEnc) * dataEmb X * (tripleEncᴴ * tripleEnc)
          * tripleEncᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [tripleEnc_conjTranspose_mul, Matrix.mul_one, Matrix.mul_one]

open scoped Matrix.Norms.L2Operator in
/-- ★★★ **The machine's gate count.** There are a recovery `R` and constants `K`, `e` such that for
every two-qubit unitary `V` and every accuracy `ε ≤ e` some list of at most `K · log(1/ε)^c` gadgets
(`c = skExponent ∈ (3, 4)`) realises, exactly on every encoded data state, a logical gate `W` within
`ε` of `V` up to a global phase (operator norm); and that list, run as a circuit of
`steane_triple_machine` with any unitary faults, gives exactly `W`'s output whenever no gadget is
bad, so with probability at least `1 − 21 N p²`, `N ≤ K · log(1/ε)^c`. -/
theorem steane_triple_machine_count :
    ∃ R : Channel TripleReg TripleReg (Option (Fin 3 → SingleErr)), ∃ K e : ℝ, 0 < K ∧ 0 < e ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ e → ∀ V ∈ Matrix.unitaryGroup (Fin 2 → Fin 2) ℂ,
        ∃ (φ : ℝ) (gs : List TGadget) (W : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ),
          ‖Euler.expI φ • V - W‖ ≤ ε ∧
          (gs.length : ℝ) ≤ K * (Real.log ε⁻¹) ^ SU2.skExponent ∧
          ∀ (Uf : Fin gs.length → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
            (Vf Wf Yf : Fin gs.length → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
            (∀ j q b, Uf j q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
            (∀ j q, Vf j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
            (∀ j q, Wf j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
            (∀ j q, Yf j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
            ∀ X : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ,
              (∀ ω : CircuitPat gs.length 7 1, (∀ j, isBad 7 1 (ω j) = false) →
                  correctedRun (tMachineCircuit R (fun j => gs.get j) Uf Vf Wf Yf ω) (dataEnc X)
                    = dataEnc (W * X * Wᴴ))
              ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
                  ν {c | c = true} ≤ ENNReal.ofReal p →
                  1 - (gs.length : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
                    ≤ QuantumInfo.circuitMeasure gs.length 7 ν 1
                        {ω | correctedRun (tMachineCircuit R (fun j => gs.get j) Uf Vf Wf Yf ω)
                          (dataEnc X) = dataEnc (W * X * Wᴴ)} := by
  obtain ⟨R, hR⟩ := steane_triple_machine
  obtain ⟨K, e, hK, he, hcount⟩ := exists_cliffordT_circuit_polylog (m := 2) (by norm_num)
  refine ⟨R, K, e, hK, he, fun ε hε hεe V hV => ?_⟩
  obtain ⟨φ, l, hl, hlen, hnorm⟩ := hcount ε hε hεe V hV
  obtain ⟨gs, hgs_len, hgs⟩ := exists_gadgets_of_cliffordT l hl
  refine ⟨φ, gs, l.prod, hnorm, by rw [hgs_len]; exact hlen,
    fun Uf Vf Wf Yf hU hV' hW hY X => ?_⟩
  have hideal : tMachineIdeal (fun j : Fin gs.length => gs.get j) (dataEnc X)
      = dataEnc (l.prod * X * (l.prod)ᴴ) := by
    rw [tMachineIdeal_get, hgs X]
  rw [← hideal]
  exact hR gs.length (fun j => gs.get j) Uf Vf Wf Yf hU hV' hW hY (dataEnc X)
    (isCodeState_dataEnc X)

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
