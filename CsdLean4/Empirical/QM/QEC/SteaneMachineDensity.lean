/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneTripleMachine

/-!
# The three-block Steane machine is universal on its two logical qubits

**Category:** 3-Local (Empirical, QM twin). BACKLOG #308.

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
* ★ `gateOf_hGateM_mem_realised`, ★ `cnotGate'_mem_realised`, ★ `gateOf_tGateM_mem_realised` (the
  injection through ancilla block `2`, on either data block); ★★ `cliffordTm_le_realised` —
  **every Clifford+T circuit on two qubits is realised by the machine, exactly**;
* ★★★ `steane_triple_machine_universal` — **every two-qubit unitary is, up to a global phase, a
  limit of logical gates the machine realises**; `tMachineIdeal_get` — a realising list is a
  circuit of `steane_triple_machine`, whose fault-tolerance theorem covers it.

## Honest scope

⚠️ The realisation is of the **ideal** runs on encoded data states; the faulty runs are covered by
`steane_triple_machine` (level one, an ideal recovery, unitary faults, `1 − 21 N p²` per circuit of
`N` gadgets). The density is topological (a closure in the matrix topology) with no rate: the
Solovay–Kitaev counts of `SolovayKitaevCount.lean` are not composed here, so no bound on `N` for a
given accuracy is stated.

References: A. Kitaev, *Russ. Math. Surv.* **52**, 1191 (1997); M. Nielsen, I. Chuang, *Quantum
Computation and Quantum Information* §4.5 and §10.6; `specs/BACKLOG.md` #308;
`Empirical/QM/QEC/SteaneTripleMachine.lean`, `Mathlib/QuantumInfo/CliffordTUniversal.lean`
(`exists_phase_mem_cliffordTmLim`); `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open Controlled QuantumInfo.Controlled
open scoped Kronecker

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

/-- ★ **`H̄` on either data qubit is realised.** -/
theorem gateOf_hGateM_mem_realised (b : Fin 2) :
    gateOf b CliffordT.hGateM ∈ realised := by
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
  refine mem_realised_of_gadget (TGadget.mk 1 (UGadget.clifford (PairGadget.single b Gadget.had)))
    fun X => ?_
  rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc 1 hG, lift3_conj_dataEmb, hGl,
    smul_conj_eq hc]

/-- ★ **`CNOT̄` in both directions between the data qubits is realised.** -/
theorem cnotGate'_mem_realised {a b : Fin 2} (hab : a ≠ b) : cnotGate' a b ∈ realised := by
  have hG : PairGadget.cnot.op * pairEnc = pairEnc * cnotL := cnotT_mul_pairEnc
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · refine mem_realised_of_gadget (TGadget.mk 1 (UGadget.clifford PairGadget.cnot)) fun X => ?_
    rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc 1 hG, lift3_conj_dataEmb,
      cnotL_eq_cnotGate']
    rfl
  · refine mem_realised_of_gadget (TGadget.mk (Equiv.swap 0 1) (UGadget.clifford PairGadget.cnot))
      fun X => ?_
    rw [dataEnc, dataEnc, TGadget.ideal_clifford_tripleEnc _ hG, lift3_swap01,
      show cnotL.submatrix (fun c : Fin 2 → Fin 2 => ![c 1, c 0]) (fun c => ![c 1, c 0])
        = cnotGate' (1 : Fin 2) 0 from cnotL_submatrix_swapQ, lift3_conj_dataEmb]
    rfl
  · exact absurd rfl hab

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

/-- ★ **`T̄` on either data qubit is realised**, by injection through the ancilla block `2`. -/
theorem gateOf_tGateM_mem_realised (d : Fin 2) :
    gateOf d CliffordT.tGateM ∈ realised := by
  have hT : CliffordT.tGateM = Steane.tGateM := rfl
  fin_cases d
  · -- data block 0 with ancilla block 2: `σ = (1 2)`
    refine mem_realised_of_gadget (TGadget.mk (Equiv.swap 1 2) UGadget.tGate) fun X => ?_
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
    refine mem_realised_of_gadget (TGadget.mk (Equiv.swap 0 1 * Equiv.swap 1 2) UGadget.tGate)
      fun X => ?_
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

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
