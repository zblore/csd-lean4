/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneUniversalMachine

/-!
# The Steane machine on three blocks: universal on two logical qubits

**Category:** 3-Local (Empirical, QM twin). BACKLOG #307.

`SteaneUniversalMachine.lean`'s machine is universal on one logical qubit: the injection of `T̄`
consumes block `1`. With a third block as the injection's ancilla, two logical qubits get the whole
of Clifford+T. Instead of re-proving the two-block development over three blocks, every two-block
gadget is **lifted**: placed on an ordered pair of blocks `σ 0`, `σ 1` by a permutation `σ`, with an
operator on the idle block `σ 2`, and the two-block theorems are carried over by the lift.

* `split3`, `lift3` — three blocks as an ordered pair and an idle block, and the tensor of a pair
  operator with an idle-block operator; `lift3_mul`, `lift3_conjTranspose`, `lift3_one`,
  `lift3_sum_left`, `lift3_sum_right`, ★ `lift3_blockKron`;
* ★★ `sum_kronecker_one_conj_eq`, `sum_kronecker_conj_eq`, ★★ `sum_lift3_conj_eq` — **two Kraus
  families with the same channel on the pair give the same channel on three blocks**, read slice by
  slice;
* `tripleEnc`, `tripleProj`, ★ `tripleEnc_eq_lift3` (the three-block encoder is the pair encoder on
  any ordered pair, tensored with the block encoder); `tripleFam`, `encoderKL_tripleFam`,
  `tripleKrausMix`, ★★ `exists_isRecovery_tripleKrausMix` — **one recovery for every correctable
  channel of three blocks**;
* `UGadget.idealK`, `UGadget.faultyK`, `UGadget.ideal_eq_sum`, `UGadget.faulty_eq_sum` — the pair
  gadgets as Kraus families; ★★ `UGadget.exists_uniform_deviation` — **the pair's one-fault bound
  with one deviation channel for every code state**;
* `TGadget` — **a pair gadget on an ordered pair of blocks**; `TGadget.isCodeState_ideal`,
  `lift3_mem_tripleSpan`, ★★ `TGadget.deviatesBy_faulty` (**the one-fault bound on three blocks**,
  with a unitary fault on the idle block at the faulty location too); ★★
  `TGadget.ideal_tGate_tripleEnc` (**the lifted injection is `T` on logical qubit `σ 0`, logical
  qubit `σ 1` reset, logical qubit `σ 2` untouched**);
* ★★★ `steane_tripleGadgetSet_corrected`, ★★★ `steane_triple_machine` — **the machine on three
  blocks**: a pattern that makes no gadget bad gives exactly the ideal output, and the output is
  exactly ideal with probability at least `1 − 21 N p²`. With blocks `0`, `1` as data and block `2`
  as the ancilla, the set holds `H̄`, `S̄`, `T̄` on each data qubit and `CNOT̄` between them —
  Clifford+T on two logical qubits, dense in `U(4)` modulo phase
  (`Mathlib/QuantumInfo/CliffordTUniversal.lean`'s `exists_phase_mem_cliffordTmLim`).

## Honest scope

⚠️ Level one, an ideal recovery, unitary faults, the injection's locations its seven columns (as in
`SteaneUniversalMachine.lean`); the idle block takes a unitary fault at the gadget's faulty location
and is otherwise noiseless. The density statement is cited, not composed with the machine: no
theorem here says that a given two-qubit unitary is approximated by a circuit of the gadget set.

References: S. Bravyi, A. Kitaev, *Phys. Rev. A* **71**, 022316 (2005); P. Aliferis, D. Gottesman,
J. Preskill, *Quantum Inf. Comput.* **6**, 97 (2006); `specs/BACKLOG.md` #307;
`Empirical/QM/QEC/SteaneUniversalMachine.lean` (`steane_universal_machine`),
`Empirical/QM/QEC/SteaneInjection.lean`, `Mathlib/QuantumInfo/CliffordTUniversal.lean`;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped ENNReal Kronecker

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### Three blocks as an ordered pair and an idle block -/

/-- **The split of three blocks by a permutation `σ`**: blocks `σ 0`, `σ 1` as an ordered pair,
block `σ 2` idle. -/
def split3 {α : Type*} (σ : Equiv.Perm (Fin 3)) : (Fin 3 → α) ≃ (Fin 2 → α) × α where
  toFun z := (fun t => z (σ t.castSucc), z (σ (Fin.last 2)))
  invFun p b := Fin.lastCases (motive := fun _ => α) p.2 p.1 (σ.symm b)
  left_inv z := by
    funext b
    obtain ⟨c, rfl⟩ := σ.surjective b
    simp only [Equiv.symm_apply_apply]
    induction c using Fin.lastCases with
    | last => exact Fin.lastCases_last
    | cast i => exact Fin.lastCases_castSucc i
  right_inv p := by
    ext t
    · show Fin.lastCases (motive := fun _ => α) p.2 p.1 (σ.symm (σ t.castSucc)) = p.1 t
      rw [Equiv.symm_apply_apply, Fin.lastCases_castSucc]
    · show Fin.lastCases (motive := fun _ => α) p.2 p.1 (σ.symm (σ (Fin.last 2))) = p.2
      rw [Equiv.symm_apply_apply, Fin.lastCases_last]

/-- **A two-block operator `M` on the pair `σ 0`, `σ 1`, tensored with `N` on the idle block
`σ 2`.** -/
def lift3 {α β : Type*} (σ : Equiv.Perm (Fin 3)) (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ)
    (N : Matrix α β ℂ) : Matrix (Fin 3 → α) (Fin 3 → β) ℂ :=
  (M ⊗ₖ N).submatrix (split3 σ) (split3 σ)

section Lift

variable {α β γ : Type*} [Fintype β] [DecidableEq β] (σ : Equiv.Perm (Fin 3))

omit [DecidableEq β] in
theorem lift3_mul (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) (M' : Matrix (Fin 2 → β) (Fin 2 → γ) ℂ)
    (N : Matrix α β ℂ) (N' : Matrix β γ ℂ) :
    lift3 σ M N * lift3 σ M' N' = lift3 σ (M * M') (N * N') := by
  rw [lift3, lift3, lift3, submatrix_mul_equiv, mul_kronecker_mul]

omit [Fintype β] [DecidableEq β] in
theorem lift3_conjTranspose (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) (N : Matrix α β ℂ) :
    (lift3 σ M N)ᴴ = lift3 σ Mᴴ Nᴴ := by
  rw [lift3, lift3, conjTranspose_submatrix, conjTranspose_kronecker]

omit [Fintype β] in
theorem lift3_one : lift3 σ (1 : Matrix (Fin 2 → β) (Fin 2 → β) ℂ) (1 : Matrix β β ℂ) = 1 := by
  rw [lift3, one_kronecker_one, submatrix_one_equiv]

omit [Fintype β] [DecidableEq β] in
theorem lift3_sum_left {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (M : ι → Matrix (Fin 2 → α) (Fin 2 → β) ℂ)
    (N : Matrix α β ℂ) : lift3 σ (∑ i, c i • M i) N = ∑ i, c i • lift3 σ (M i) N := by
  have h : (∑ i, c i • M i) ⊗ₖ N = ∑ i, c i • (M i ⊗ₖ N) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [kronecker_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
      mul_assoc]
  ext z w
  rw [lift3, h]
  simp only [submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, lift3]

omit [Fintype β] [DecidableEq β] in
theorem lift3_sum_right {ι : Type*} [Fintype ι] (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ)
    (c : ι → ℂ) (N : ι → Matrix α β ℂ) :
    lift3 σ M (∑ i, c i • N i) = ∑ i, c i • lift3 σ M (N i) := by
  have h : M ⊗ₖ (∑ i, c i • N i) = ∑ i, c i • (M ⊗ₖ N i) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [kronecker_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  ext z w
  rw [lift3, h]
  simp only [submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, lift3]

omit [Fintype β] [DecidableEq β] in
theorem lift3_smul_left (c : ℂ) (M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ) (N : Matrix α β ℂ) :
    lift3 σ (c • M) N = c • lift3 σ M N := by
  rw [lift3, lift3, smul_kronecker]
  rfl

omit [Fintype β] [DecidableEq β] in
/-- **The lift of a tensor over the two blocks is the tensor over the three**, the idle factor on
block `σ 2`. -/
theorem lift3_blockKron (M : Fin 2 → Matrix α β ℂ) (N : Matrix α β ℂ) :
    lift3 σ (blockKron M) N
      = blockKron fun b => Fin.lastCases (motive := fun _ => Matrix α β ℂ) N M (σ.symm b) := by
  ext z w
  rw [lift3, submatrix_apply, kronecker_apply, blockKron_apply, blockKron_apply,
    ← Equiv.prod_comp σ, Fin.prod_univ_three, Fin.prod_univ_two]
  simp only [Equiv.symm_apply_apply]
  rfl

end Lift

/-! ### Channels tensored with the idle block -/

theorem kronecker_one_conj_apply {A B C : Type*} [Fintype B] [Fintype C] [DecidableEq C]
    (K : Matrix A B ℂ) (Y : Matrix (B × C) (B × C) ℂ) (a a' : A) (c c' : C) :
    ((K ⊗ₖ (1 : Matrix C C ℂ)) * Y * (K ⊗ₖ (1 : Matrix C C ℂ))ᴴ) (a, c) (a', c')
      = (K * Matrix.of (fun b b' => Y (b, c) (b', c')) * Kᴴ) a a' := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  simp only [Matrix.mul_apply, kronecker_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- ★★ **Equal channels stay equal when tensored with the identity**: two Kraus families with the
same channel on `B` give the same channel on `B × C` with `1` on `C`, read slice by slice. -/
theorem sum_kronecker_one_conj_eq {ι κ A B C : Type*} [Fintype ι] [Fintype κ] [Fintype B]
    [Fintype C] [DecidableEq C] {K : ι → Matrix A B ℂ} {J : κ → Matrix A B ℂ}
    (h : ∀ σ : Matrix B B ℂ, ∑ i, K i * σ * (K i)ᴴ = ∑ j, J j * σ * (J j)ᴴ)
    (Y : Matrix (B × C) (B × C) ℂ) :
    ∑ i, (K i ⊗ₖ (1 : Matrix C C ℂ)) * Y * (K i ⊗ₖ (1 : Matrix C C ℂ))ᴴ
      = ∑ j, (J j ⊗ₖ (1 : Matrix C C ℂ)) * Y * (J j ⊗ₖ (1 : Matrix C C ℂ))ᴴ := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [Matrix.sum_apply, kronecker_one_conj_apply]
  rw [← Matrix.sum_apply, ← Matrix.sum_apply, h]

/-- The same with any operator `N` on the idle factor. -/
theorem sum_kronecker_conj_eq {ι κ A B C D : Type*} [Fintype ι] [Fintype κ] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] {K : ι → Matrix A B ℂ}
    {J : κ → Matrix A B ℂ}
    (h : ∀ σ : Matrix B B ℂ, ∑ i, K i * σ * (K i)ᴴ = ∑ j, J j * σ * (J j)ᴴ)
    (N : Matrix C D ℂ) (Y : Matrix (B × D) (B × D) ℂ) :
    ∑ i, (K i ⊗ₖ N) * Y * (K i ⊗ₖ N)ᴴ = ∑ j, (J j ⊗ₖ N) * Y * (J j ⊗ₖ N)ᴴ := by
  have hsplit : ∀ M : Matrix A B ℂ,
      M ⊗ₖ N = (M ⊗ₖ (1 : Matrix C C ℂ)) * ((1 : Matrix B B ℂ) ⊗ₖ N) := by
    intro M
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hY : ∀ M : Matrix A B ℂ, (M ⊗ₖ N) * Y * (M ⊗ₖ N)ᴴ
      = (M ⊗ₖ (1 : Matrix C C ℂ)) * (((1 : Matrix B B ℂ) ⊗ₖ N) * Y * ((1 : Matrix B B ℂ) ⊗ₖ N)ᴴ)
        * (M ⊗ₖ (1 : Matrix C C ℂ))ᴴ := by
    intro M
    rw [hsplit, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [hY]
  exact sum_kronecker_one_conj_eq h _

/-- ★★ **Equal channels on the pair stay equal on three blocks**, with any operator on the idle
block. -/
theorem sum_lift3_conj_eq {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (σ : Equiv.Perm (Fin 3))
    {K : ι → Matrix (Fin 2 → α) (Fin 2 → β) ℂ} {J : κ → Matrix (Fin 2 → α) (Fin 2 → β) ℂ}
    (h : ∀ τ : Matrix (Fin 2 → β) (Fin 2 → β) ℂ,
      ∑ i, K i * τ * (K i)ᴴ = ∑ j, J j * τ * (J j)ᴴ)
    (N : Matrix α β ℂ) (Y : Matrix (Fin 3 → β) (Fin 3 → β) ℂ) :
    ∑ i, lift3 σ (K i) N * Y * (lift3 σ (K i) N)ᴴ
      = ∑ j, lift3 σ (J j) N * Y * (lift3 σ (J j) N)ᴴ := by
  have hY : ∀ M : Matrix (Fin 2 → α) (Fin 2 → β) ℂ, lift3 σ M N * Y * (lift3 σ M N)ᴴ
      = ((M ⊗ₖ N) * Y.submatrix (split3 σ).symm (split3 σ).symm * (M ⊗ₖ N)ᴴ).submatrix
          (split3 σ) (split3 σ) := by
    intro M
    rw [lift3, conjTranspose_submatrix,
      show Y = (Y.submatrix (split3 σ).symm (split3 σ).symm).submatrix (split3 σ) (split3 σ) by
        simp,
      submatrix_mul_equiv, submatrix_mul_equiv]
    simp
  simp only [hY]
  ext z w
  simp only [Matrix.sum_apply, submatrix_apply]
  rw [← Matrix.sum_apply, ← Matrix.sum_apply, sum_kronecker_conj_eq h]

/-! ### The three-block code -/

/-- The three-block register: qubit `q` of block `b` is `z b q`. -/
abbrev TripleReg : Type := Fin 3 → Fin 7 → Fin 2

/-- The encoder of three Steane blocks. -/
def tripleEnc : Matrix TripleReg (Fin 3 → Fin 2) ℂ := blockKron fun _ : Fin 3 => steaneEnc

/-- The three-block code projector. -/
def tripleProj : Matrix TripleReg TripleReg ℂ := blockKron fun _ : Fin 3 => steaneProj

theorem lastCases_const {γ : Type*} (x : γ) (b : Fin 3) :
    Fin.lastCases (motive := fun _ => γ) x (fun _ : Fin 2 => x) b = x := by
  induction b using Fin.lastCases with
  | last => exact Fin.lastCases_last
  | cast i => exact Fin.lastCases_castSucc i

/-- The three-block encoder is the pair encoder on any ordered pair, tensored with the encoder of
the idle block. -/
theorem tripleEnc_eq_lift3 (σ : Equiv.Perm (Fin 3)) : tripleEnc = lift3 σ pairEnc steaneEnc := by
  rw [pairEnc, lift3_blockKron, tripleEnc]
  exact congrArg blockKron (funext fun b => (lastCases_const steaneEnc (σ.symm b)).symm)

theorem tripleProj_eq_lift3 (σ : Equiv.Perm (Fin 3)) :
    tripleProj = lift3 σ pairProj steaneProj := by
  rw [pairProj, lift3_blockKron, tripleProj]
  exact congrArg blockKron (funext fun b => (lastCases_const steaneProj (σ.symm b)).symm)

theorem tripleEnc_conjTranspose_mul : tripleEncᴴ * tripleEnc = 1 := by
  rw [tripleEnc, blockKron_conjTranspose, blockKron_mul,
    show (fun _ : Fin 3 => steaneEncᴴ * steaneEnc)
        = fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) ℂ) from
      funext fun _ => steaneEnc_conjTranspose_mul,
    blockKron_one]

theorem tripleProj_eq : tripleProj = tripleEnc * tripleEncᴴ := by
  rw [tripleProj, tripleEnc, blockKron_conjTranspose, blockKron_mul]
  exact congrArg blockKron (funext fun _ => steaneProj_eq)

theorem tripleProj_conjTranspose : tripleProjᴴ = tripleProj := by
  rw [tripleProj_eq, conjTranspose_mul, conjTranspose_conjTranspose]

theorem tripleProj_mul_self : tripleProj * tripleProj = tripleProj := by
  rw [tripleProj_eq,
    show tripleEnc * tripleEncᴴ * (tripleEnc * tripleEncᴴ)
        = tripleEnc * (tripleEncᴴ * tripleEnc) * tripleEncᴴ by simp only [Matrix.mul_assoc],
    tripleEnc_conjTranspose_mul, Matrix.mul_one]

theorem isCodeState_tripleProj : IsCodeState tripleProj tripleProj := by
  show tripleProj = tripleProj * tripleProj * tripleProj
  rw [tripleProj_mul_self, tripleProj_mul_self]

theorem trace_tripleProj_ne_zero : tripleProj.trace ≠ 0 := by
  rw [tripleProj_eq, Matrix.trace_mul_comm, tripleEnc_conjTranspose_mul, Matrix.trace_one]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-- A code state of three blocks is the encoding of its logical state. -/
theorem eq_tripleEnc_of_isCodeState {X : Matrix TripleReg TripleReg ℂ}
    (hX : IsCodeState tripleProj X) :
    X = tripleEnc * (tripleEncᴴ * X * tripleEnc) * tripleEncᴴ := by
  conv_lhs => rw [hX, tripleProj_eq]
  simp only [Matrix.mul_assoc]

/-! ### The three-block recovery -/

/-- The error family of three blocks: one single-qubit Pauli in each. -/
def tripleFam (g : Fin 3 → SingleErr) : Matrix TripleReg TripleReg ℂ :=
  blockKron fun b => pauliMat (errA (g b)) (errB (g b))

/-- Knill–Laflamme in encoder form for three blocks: it composes over the blocks. -/
theorem encoderKL_tripleFam : EncoderKL tripleEnc tripleFam := by
  intro g h
  refine ⟨∏ b, (1 : Matrix SingleErr SingleErr ℂ) (g b) (h b), ?_⟩
  rw [tripleFam, tripleFam, tripleEnc, blockKron_conjTranspose, blockKron_conjTranspose,
    blockKron_mul, blockKron_mul, blockKron_mul,
    show (fun b : Fin 3 => steaneEncᴴ * (pauliMat (errA (g b)) (errB (g b)))ᴴ
        * pauliMat (errA (h b)) (errB (h b)) * steaneEnc)
        = fun b : Fin 3 => (1 : Matrix SingleErr SingleErr ℂ) (g b) (h b) • 1 from
      funext fun b => steaneEnc_pauli_pair (g b) (h b),
    blockKron_smul, blockKron_one]

/-- **The correctable channels of three blocks**: Kraus operators in the span of the family, trace
preserving on the code. -/
def tripleKrausMix : Set (Matrix TripleReg TripleReg ℂ → Matrix TripleReg TripleReg ℂ) :=
  {f | ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix TripleReg TripleReg ℂ),
    (∀ i, ∃ a : (Fin 3 → SingleErr) → ℂ, K i = ∑ g, a g • tripleFam g)
      ∧ tripleProj * (∑ i, (K i)ᴴ * K i) * tripleProj = tripleProj
      ∧ f = fun ρ => ∑ i, K i * ρ * (K i)ᴴ}

/-- ★★ **One recovery for every correctable channel of three blocks.** -/
theorem exists_isRecovery_tripleKrausMix :
    ∃ R : Channel TripleReg TripleReg (Option (Fin 3 → SingleErr)),
      IsRecovery tripleProj R.apply tripleKrausMix := by
  obtain ⟨c, R, hR⟩ := exists_recovery_of_encoderKL tripleEnc_conjTranspose_mul encoderKL_tripleFam
  refine ⟨R, ?_⟩
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩ ρ hρ
  choose a ha using hK
  set s : ι → ℂ := fun i => ∑ g, ∑ h, star (a i g) * a i h * c g h
  have hs : ∀ σ, IsCodeState tripleProj σ →
      R.apply (∑ i, K i * σ * (K i)ᴴ) = (∑ i, s i) • σ := by
    intro σ hσ
    rw [Channel.apply_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i]
    exact recovery_apply_lin_comb (P := tripleEnc * tripleEncᴴ) hR (a i)
      (by rw [← tripleProj_eq]; exact hσ)
  have hone : ∑ i, s i = 1 := by
    have h := congrArg Matrix.trace (hs tripleProj isCodeState_tripleProj)
    rw [R.apply_trace, Matrix.trace_smul, smul_eq_mul, Matrix.trace_sum] at h
    have htr : ∑ i, (K i * tripleProj * (K i)ᴴ).trace = tripleProj.trace := by
      calc ∑ i, (K i * tripleProj * (K i)ᴴ).trace
          = (tripleProj * (∑ i, (K i)ᴴ * K i) * tripleProj).trace := by
            rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have e1 : (K i * tripleProj * (K i)ᴴ).trace = ((K i)ᴴ * K i * tripleProj).trace := by
              rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
            have e2 : (tripleProj * ((K i)ᴴ * K i) * tripleProj).trace
                = ((K i)ᴴ * K i * tripleProj).trace := by
              rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, tripleProj_mul_self,
                Matrix.trace_mul_comm]
            rw [e1, e2]
        _ = tripleProj.trace := by rw [htp]
    rw [htr] at h
    exact mul_right_cancel₀ trace_tripleProj_ne_zero (by rw [one_mul]; exact h.symm)
  rw [hs ρ hρ, hone, one_smul]

/-! ### The gadgets of the pair as Kraus families -/

namespace UGadget

/-- The ideal gadget's Kraus operators (the second Clifford one is `0`). -/
def idealK : UGadget → Fin 2 → Matrix PairReg PairReg ℂ
  | clifford G => ![G.op, 0]
  | tGate => fun j => pairEnc * injIdealKraus j * pairEncᴴ

/-- The faulty gadget's Kraus operators. -/
def faultyK (G : UGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) :
    (Fin 7 → Fin 2) × Fin 2 → Matrix PairReg PairReg ℂ :=
  match G with
  | clifford G => fun p => if p = (0, 0) then faultOp U bs * G.op else 0
  | tGate => fun p => injFaultyKraus U V W bs p.1 p.2

theorem ideal_eq_sum (G : UGadget) (ρ : Matrix PairReg PairReg ℂ) :
    G.ideal ρ = ∑ j, G.idealK j * ρ * (G.idealK j)ᴴ := by
  cases G with
  | clifford G =>
    simp [ideal, idealK, PairGadget.ideal, Fin.sum_univ_two]
  | tGate =>
    simp only [ideal, idealK, idealInj, logicalInj, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]

theorem faulty_eq_sum (G : UGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool) (ρ : Matrix PairReg PairReg ℂ) :
    G.faulty U V W bs ρ = ∑ p, G.faultyK U V W bs p * ρ * (G.faultyK U V W bs p)ᴴ := by
  cases G with
  | clifford G =>
    simp only [faulty, faultyK, PairGadget.faulty]
    rw [Finset.sum_eq_single (0, 0)]
    · simp
    · intro p _ hp
      simp [hp]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | tGate =>
    simp only [faulty, faultyK, injFaulty]
    rw [Fintype.sum_prod_type]

/-- The ideal Kraus operators map the code into the code. -/
theorem pairProj_mul_idealK_mul_pairProj (G : UGadget) (j : Fin 2) :
    pairProj * G.idealK j * pairProj = G.idealK j * pairProj := by
  cases G with
  | clifford G =>
    fin_cases j
    · show pairProj * G.op * pairProj = G.op * pairProj
      rw [← G.op_mul_pairProj, Matrix.mul_assoc, pairProj_mul_self]
    · show pairProj * 0 * pairProj = 0 * pairProj
      simp
  | tGate =>
    show pairProj * (pairEnc * injIdealKraus j * pairEncᴴ) * pairProj
      = pairEnc * injIdealKraus j * pairEncᴴ * pairProj
    have h1 : pairProj * pairEnc = pairEnc := by
      rw [pairProj_eq, Matrix.mul_assoc, pairEnc_conjTranspose_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]

/-- ★★ **The one-fault bound for the pair gadgets, uniformly**: a pattern with at most one faulty
location gives the ideal gadget followed by one channel — two Kraus operators, each a combination
of the pair's family, trace preserving — the same for every code state. -/
theorem exists_uniform_deviation (G : UGadget) {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    {V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : ∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hW : ∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {bs : Fin 7 → Bool} (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    ∃ L : Fin 2 → Matrix PairReg PairReg ℂ,
      (∀ l, ∃ a : (Fin 2 → SingleErr) → ℂ, L l = ∑ g, a g • pairFam g)
        ∧ ∑ l, (L l)ᴴ * L l = 1
        ∧ ∀ ρ, IsCodeState pairProj ρ →
          G.faulty U V W bs ρ = ∑ l, L l * G.ideal ρ * (L l)ᴴ := by
  cases G with
  | clifford G =>
    obtain ⟨q, A, hA, hF⟩ := exists_faultOp_eq_blockFault hU h
    refine ⟨![blockFault q A, 0], fun l => ?_, ?_, fun ρ _ => ?_⟩
    · fin_cases l
      · exact ⟨_, blockFault_eq_sum q A⟩
      · exact ⟨0, by simp⟩
    · rw [Fin.sum_univ_two]
      simp [blockFault_conjTranspose_mul hA]
    · show (faultOp U bs * G.op) * ρ * (faultOp U bs * G.op)ᴴ = _
      rw [Fin.sum_univ_two, hF]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, conjTranspose_zero, Matrix.zero_mul,
        Matrix.mul_zero, add_zero, ideal, PairGadget.ideal, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
  | tGate =>
    obtain ⟨i, hi⟩ := exists_eq_of_card_le_one h
    set V' := if bs i then V i else 1
    set W' := if bs i then W i else 1
    set U0 := if bs i then U i 0 else 1
    set U1 := if bs i then U i 1 else 1
    have hmem : ∀ m, colFaultE i V' U0 U1 W' m ∈ pairSpan := fun m =>
      colFaultE_mem_pairSpan (ite_mem_unitaryGroup (hV i)) (ite_mem_unitaryGroup (hU i 0))
        (ite_mem_unitaryGroup (hU i 1)) (ite_mem_unitaryGroup (hW i)) i m
    refine ⟨fun m => invSqrtTwo • colFaultE i V' U0 U1 W' m, fun m => ?_, ?_, fun ρ hρ => ?_⟩
    · obtain ⟨-, a, ha⟩ := hmem m
      refine ⟨fun g => invSqrtTwo * a g, ?_⟩
      show invSqrtTwo • colFaultE i V' U0 U1 W' m = _
      rw [ha, Finset.smul_sum]
      simp only [smul_smul]
    · simp only [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, star_invSqrtTwo,
        invSqrtTwo_mul_self, fun m => (hmem m).1]
      rw [Fin.sum_univ_two, ← add_smul]
      norm_num
    · have hK : ∀ k m, injFaultyKraus U V W bs k m = colKraus i V' U0 U1 W' k m := by
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
      have hsum := sum_conj_eq_of_mul_pairEnc (ι := Unit) (fun k m _ => colKraus i V' U0 U1 W' k m)
        (fun m _ => colFaultE i V' U0 U1 W' m)
        (fun k m _ => colKraus_mul_pairEnc i V' U0 U1 W' k m) hρ
      simp only [Fintype.sum_unique] at hsum
      show injFaulty U V W bs ρ = _
      rw [injFaulty]
      simp only [hK]
      rw [hsum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [conjTranspose_smul, smul_mul_assoc, Matrix.smul_mul, mul_smul_comm, smul_smul,
        star_invSqrtTwo, invSqrtTwo_mul_self]
      rfl

end UGadget

/-! ### The gadgets on three blocks -/

/-- **A gadget on three blocks**: a gadget of the pair's universal set on the ordered pair of blocks
`σ 0`, `σ 1`, block `σ 2` idle. -/
structure TGadget where
  /-- The blocks: `σ 0` and `σ 1` the pair, `σ 2` idle. -/
  σ : Equiv.Perm (Fin 3)
  /-- The gadget on the pair. -/
  G : UGadget

namespace TGadget

/-- The ideal gadget on three blocks: the pair's ideal Kraus operators, the identity on the idle
block. -/
def ideal (T : TGadget) (X : Matrix TripleReg TripleReg ℂ) : Matrix TripleReg TripleReg ℂ :=
  ∑ j, lift3 T.σ (T.G.idealK j) 1 * X * (lift3 T.σ (T.G.idealK j) 1)ᴴ

/-- The gadget under a fault pattern: the pair's faulty Kraus operators on the pair, and `Y q` on
qubit `q` of the idle block at each faulty location `q`. -/
def faulty (T : TGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W Y : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (bs : Fin 7 → Bool)
    (X : Matrix TripleReg TripleReg ℂ) : Matrix TripleReg TripleReg ℂ :=
  ∑ p, lift3 T.σ (T.G.faultyK U V W bs p) (colOp Y bs) * X
    * (lift3 T.σ (T.G.faultyK U V W bs p) (colOp Y bs))ᴴ

/-- The implemented step: the gadget under its fault pattern, then the recovery. -/
def step {κ : Type*} [Fintype κ] (R : Channel TripleReg TripleReg κ) (T : TGadget)
    (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (V W Y : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (bs : Fin 7 → Bool) (X : Matrix TripleReg TripleReg ℂ) : Matrix TripleReg TripleReg ℂ :=
  R.apply (T.faulty U V W Y bs X)

theorem tripleProj_mul_lift3_mul_tripleProj (T : TGadget) (j : Fin 2) :
    tripleProj * lift3 T.σ (T.G.idealK j) 1 * tripleProj
      = lift3 T.σ (T.G.idealK j) 1 * tripleProj := by
  rw [tripleProj_eq_lift3 T.σ, lift3_mul, lift3_mul, lift3_mul,
    T.G.pairProj_mul_idealK_mul_pairProj, Matrix.mul_one, Matrix.one_mul,
    isCodeProjector_steaneProj.mul_self]

/-- The ideal gadget keeps code states in the code. -/
theorem isCodeState_ideal (T : TGadget) {X : Matrix TripleReg TripleReg ℂ}
    (hX : IsCodeState tripleProj X) : IsCodeState tripleProj (T.ideal X) := by
  have hL : ∀ j, lift3 T.σ (T.G.idealK j) 1 * tripleProj
      = tripleProj * lift3 T.σ (T.G.idealK j) 1 * tripleProj :=
    fun j => (T.tripleProj_mul_lift3_mul_tripleProj j).symm
  have hL' : ∀ j, tripleProj * (lift3 T.σ (T.G.idealK j) 1)ᴴ
      = tripleProj * (lift3 T.σ (T.G.idealK j) 1)ᴴ * tripleProj := by
    intro j
    have h := congrArg conjTranspose (hL j)
    simp only [conjTranspose_mul, tripleProj_conjTranspose] at h
    rw [h]
    simp only [Matrix.mul_assoc, tripleProj_mul_self]
  unfold IsCodeState at hX ⊢
  rw [ideal, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [hX]
  calc lift3 T.σ (T.G.idealK j) 1 * (tripleProj * X * tripleProj) * (lift3 T.σ (T.G.idealK j) 1)ᴴ
      = (lift3 T.σ (T.G.idealK j) 1 * tripleProj) * X
          * (tripleProj * (lift3 T.σ (T.G.idealK j) 1)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = (tripleProj * lift3 T.σ (T.G.idealK j) 1 * tripleProj) * X
          * (tripleProj * (lift3 T.σ (T.G.idealK j) 1)ᴴ * tripleProj) := by rw [← hL j, ← hL' j]
    _ = tripleProj * (lift3 T.σ (T.G.idealK j) 1 * (tripleProj * X * tripleProj)
          * (lift3 T.σ (T.G.idealK j) 1)ᴴ) * tripleProj := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hX]

theorem colOp_mem_unitaryGroup {Y : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ}
    (hY : ∀ q, Y q ∈ Matrix.unitaryGroup (Fin 2) ℂ) {bs : Fin 7 → Bool} {i : Fin 7}
    (hi : ∀ q, bs q = true → q = i) : colOp Y bs ∈ Matrix.unitaryGroup (Fin 7 → Fin 2) ℂ := by
  rw [colOp, blockKron_ite_eq_gateOf hi]
  exact gateOf_mem_unitaryGroup i (ite_mem_unitaryGroup (hY i))

/-- The lift of a pair Pauli and a block Pauli is a three-block Pauli. -/
theorem lift3_pairFam_pauliMat (σ : Equiv.Perm (Fin 3)) (g : Fin 2 → SingleErr) (s : SingleErr) :
    lift3 σ (pairFam g) (pauliMat (errA s) (errB s))
      = tripleFam fun b => Fin.lastCases (motive := fun _ => SingleErr) s g (σ.symm b) := by
  rw [pairFam, lift3_blockKron, tripleFam]
  refine congrArg blockKron (funext fun b => ?_)
  induction σ.symm b using Fin.lastCases with
  | last => simp only [Fin.lastCases_last]
  | cast i => simp only [Fin.lastCases_castSucc]

/-- **Lifted pair errors with a one-qubit fault on the idle block are three-block errors.** -/
theorem lift3_mem_tripleSpan (σ : Equiv.Perm (Fin 3)) {L : Matrix PairReg PairReg ℂ}
    (hL : ∃ a : (Fin 2 → SingleErr) → ℂ, L = ∑ g, a g • pairFam g) (i : Fin 7)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ a : (Fin 3 → SingleErr) → ℂ, lift3 σ L (gateOf i M) = ∑ h, a h • tripleFam h := by
  obtain ⟨a, rfl⟩ := hL
  set merge : (Fin 2 → SingleErr) × SingleErr → Fin 3 → SingleErr :=
    fun p b => Fin.lastCases (motive := fun _ => SingleErr) p.2 p.1 (σ.symm b)
  refine ⟨fun h => ∑ p : (Fin 2 → SingleErr) × SingleErr,
    if merge p = h then a p.1 * singleCoeff i M p.2 else 0, ?_⟩
  rw [lift3_sum_left, gateOf_eq_sum_pauliMat]
  simp only [lift3_sum_right, Finset.smul_sum, smul_smul, lift3_pairFam_pauliMat]
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  symm
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

set_option maxRecDepth 4000 in
/-- ★★ **The one-fault bound on three blocks**: a pattern with at most one faulty location — on the
pair as for `UGadget`, a unitary on the idle block — is the ideal gadget followed by a correctable
channel of three blocks. -/
theorem deviatesBy_faulty (T : TGadget) {U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ}
    {V W Y : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : ∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hW : ∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hY : ∀ q, Y q ∈ Matrix.unitaryGroup (Fin 2) ℂ) {bs : Fin 7 → Bool}
    (h : (Finset.univ.filter fun q : Fin 7 => bs q = true).card ≤ 1) :
    DeviatesBy tripleProj tripleKrausMix T.ideal (T.faulty U V W Y bs) := by
  obtain ⟨L, hspan, htp, hdev⟩ := T.G.exists_uniform_deviation hU hV hW h
  obtain ⟨i, hi⟩ := exists_eq_of_card_le_one h
  set C := colOp Y bs
  have hC : Cᴴ * C = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 (colOp_mem_unitaryGroup hY hi)
  have hCi : C = gateOf i (if bs i then Y i else 1) := blockKron_ite_eq_gateOf hi Y
  -- the pair identity, for every logical input
  have hpair : ∀ τ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ,
      ∑ p, (T.G.faultyK U V W bs p * pairEnc) * τ * (T.G.faultyK U V W bs p * pairEnc)ᴴ
        = ∑ q : Fin 2 × Fin 2, (L q.1 * T.G.idealK q.2 * pairEnc) * τ
          * (L q.1 * T.G.idealK q.2 * pairEnc)ᴴ := by
    intro τ
    have hcode : IsCodeState pairProj (pairEnc * τ * pairEncᴴ) := by
      show _ = _
      rw [pairProj_eq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc pairEncᴴ pairEnc, pairEnc_conjTranspose_mul, Matrix.one_mul,
        ← Matrix.mul_assoc pairEncᴴ pairEnc, pairEnc_conjTranspose_mul, Matrix.one_mul]
    have h1 := hdev _ hcode
    rw [UGadget.faulty_eq_sum, UGadget.ideal_eq_sum] at h1
    calc ∑ p, (T.G.faultyK U V W bs p * pairEnc) * τ * (T.G.faultyK U V W bs p * pairEnc)ᴴ
        = ∑ p, T.G.faultyK U V W bs p * (pairEnc * τ * pairEncᴴ)
            * (T.G.faultyK U V W bs p)ᴴ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h1, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Matrix.mul_sum, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [conjTranspose_mul, Matrix.mul_assoc]
  intro X hX
  refine ⟨fun Z => ∑ l, lift3 T.σ (L l) C * Z * (lift3 T.σ (L l) C)ᴴ,
    ⟨Fin 2, inferInstance, fun l => lift3 T.σ (L l) C, fun l => ?_, ?_, rfl⟩, ?_⟩
  · rw [hCi]
    exact lift3_mem_tripleSpan T.σ (hspan l) i _
  · have h1 : ∑ l, (lift3 T.σ (L l) C)ᴴ * lift3 T.σ (L l) C = 1 := by
      simp only [lift3_conjTranspose, lift3_mul, hC]
      rw [show (∑ l, lift3 T.σ ((L l)ᴴ * L l) (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ))
          = lift3 T.σ (∑ l, (1 : ℂ) • ((L l)ᴴ * L l)) 1 by
        rw [lift3_sum_left]
        simp only [one_smul]]
      simp only [one_smul, htp, lift3_one]
    rw [h1, Matrix.mul_one, tripleProj_mul_self]
  · -- the lift
    have hlift := sum_lift3_conj_eq T.σ hpair (C * steaneEnc) (tripleEncᴴ * X * tripleEnc)
    have hE : ∀ M : Matrix PairReg PairReg ℂ, ∀ N : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ,
        lift3 T.σ (M * pairEnc) (N * steaneEnc) = lift3 T.σ M N * tripleEnc := by
      intro M N
      rw [tripleEnc_eq_lift3 T.σ, lift3_mul]
    simp only [hE] at hlift
    show ∑ p, lift3 T.σ (T.G.faultyK U V W bs p) C * X * (lift3 T.σ (T.G.faultyK U V W bs p) C)ᴴ
      = ∑ l, lift3 T.σ (L l) C * T.ideal X * (lift3 T.σ (L l) C)ᴴ
    have hX' := eq_tripleEnc_of_isCodeState hX
    have hconj : ∀ K : Matrix TripleReg TripleReg ℂ, K * X * Kᴴ
        = (K * tripleEnc) * (tripleEncᴴ * X * tripleEnc) * (K * tripleEnc)ᴴ := by
      intro K
      conv_lhs => rw [hX']
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    calc ∑ p, lift3 T.σ (T.G.faultyK U V W bs p) C * X * (lift3 T.σ (T.G.faultyK U V W bs p) C)ᴴ
        = ∑ p, (lift3 T.σ (T.G.faultyK U V W bs p) C * tripleEnc) * (tripleEncᴴ * X * tripleEnc)
            * (lift3 T.σ (T.G.faultyK U V W bs p) C * tripleEnc)ᴴ :=
          Finset.sum_congr rfl fun p _ => hconj _
      _ = ∑ q : Fin 2 × Fin 2, (lift3 T.σ (L q.1 * T.G.idealK q.2) C * tripleEnc)
            * (tripleEncᴴ * X * tripleEnc) * (lift3 T.σ (L q.1 * T.G.idealK q.2) C * tripleEnc)ᴴ :=
          hlift
      _ = _ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [ideal, Matrix.mul_sum, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hLI : lift3 T.σ (L l * T.G.idealK j) C
              = lift3 T.σ (L l) C * lift3 T.σ (T.G.idealK j) 1 := by
            rw [lift3_mul, Matrix.mul_one]
          rw [hLI]
          conv_rhs => rw [hX']
          simp only [conjTranspose_mul, Matrix.mul_assoc]

end TGadget

/-! ### The logical action of the lifted gadgets -/

/-- ★★ **A lifted gadget is the lifted logical gadget, on encoded inputs**: on three encoded
qubits, the ideal gadget acts by the pair's logical Kraus operators on the logical qubits `σ 0`,
`σ 1` and by the identity on `σ 2` — for `tGate`, `T` on logical qubit `σ 0` and logical qubit
`σ 1` reset to `|0⟩`. -/
theorem TGadget.ideal_tGate_tripleEnc (σ : Equiv.Perm (Fin 3))
    (τ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :
    (TGadget.mk σ UGadget.tGate).ideal (tripleEnc * τ * tripleEncᴴ)
      = tripleEnc * (∑ j, lift3 σ (injIdealKraus j) 1 * τ * (lift3 σ (injIdealKraus j) 1)ᴴ)
        * tripleEncᴴ := by
  have hK : ∀ j, lift3 σ (UGadget.tGate.idealK j) 1 * tripleEnc
      = tripleEnc * lift3 σ (injIdealKraus j) 1 := by
    intro j
    show lift3 σ (pairEnc * injIdealKraus j * pairEncᴴ) 1 * tripleEnc = _
    rw [tripleEnc_eq_lift3 σ, lift3_mul, lift3_mul, Matrix.mul_assoc, pairEnc_conjTranspose_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  rw [TGadget.ideal, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hK' : tripleEncᴴ * (lift3 σ (UGadget.tGate.idealK j) 1)ᴴ
      = (lift3 σ (injIdealKraus j) 1)ᴴ * tripleEncᴴ := by
    rw [← conjTranspose_mul, hK, conjTranspose_mul]
  calc lift3 σ (UGadget.tGate.idealK j) 1 * (tripleEnc * τ * tripleEncᴴ)
        * (lift3 σ (UGadget.tGate.idealK j) 1)ᴴ
      = (lift3 σ (UGadget.tGate.idealK j) 1 * tripleEnc) * τ
          * (tripleEncᴴ * (lift3 σ (UGadget.tGate.idealK j) 1)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hK, hK']
        simp only [Matrix.mul_assoc]

/-! ### The machine on three blocks -/

/-- ★★★ **The three-block gadget set is a set of corrected steps.** One recovery channel `R` serves
every gadget of the pair's universal set on every ordered pair of blocks. -/
theorem steane_tripleGadgetSet_corrected :
    ∃ R : Channel TripleReg TripleReg (Option (Fin 3 → SingleErr)),
      IsRecovery tripleProj R.apply tripleKrausMix
      ∧ ∀ (T : TGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
        (V W Y : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ q, V q ∈ Matrix.unitaryGroup (Fin 2) ℂ) → (∀ q, W q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ q, Y q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ω : ConcatPat 7 1, isBad 7 1 ω = false →
          IsCorrectedStep tripleProj T.ideal (T.step R U V W Y (locPat ω)) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_tripleKrausMix
  exact ⟨R, hR, fun T U V W Y hU hV hW hY ω hω => isCorrectedStep_rect hR
    (T.deviatesBy_faulty hU hV hW hY (card_le_one_of_isBad_eq_false hω))
    fun _ hX => T.isCodeState_ideal hX⟩

/-- **The three-block machine's circuit.** -/
def tMachineCircuit {κ : Type*} [Fintype κ] (R : Channel TripleReg TripleReg κ) {N : ℕ}
    (gs : Fin N → TGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W Y : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 1) :
    Circuit TripleReg :=
  List.ofFn fun j => ((gs j).ideal, (gs j).step R (U j) (V j) (W j) (Y j) (locPat (ω j)))

/-- The ideal output of the three-block machine. -/
def tMachineIdeal {N : ℕ} (gs : Fin N → TGadget) (X : Matrix TripleReg TripleReg ℂ) :
    Matrix TripleReg TripleReg ℂ :=
  runMaps (List.ofFn fun j => (gs j).ideal) X

theorem idealRun_tMachineCircuit {κ : Type*} [Fintype κ] (R : Channel TripleReg TripleReg κ)
    {N : ℕ} (gs : Fin N → TGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (V W Y : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 1)
    (X : Matrix TripleReg TripleReg ℂ) :
    idealRun (tMachineCircuit R gs U V W Y ω) X = tMachineIdeal gs X := by
  rw [idealRun, tMachineCircuit, tMachineIdeal, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine on three blocks, at level one.** One recovery channel `R` on three
blocks such that, for every circuit of `N` gadgets — `H̄`, `S̄`, `X̄`, `Z̄`, `CNOT̄` and the
injected `T̄` on any ordered pair of blocks — every assignment of unitary faults to their locations
and every encoded input:

* **the deterministic premise holds**: a pattern that makes no gadget bad gives exactly the ideal
  output;
* **the threshold statement follows**: under independent location faults of rate at most `p`, the
  output is exactly the ideal one with probability at least `1 − 21 N p²`.

With blocks `0`, `1` as data and block `2` as the injection's ancilla, the gadget set holds `H̄`,
`S̄`, `T̄` on each data qubit and `CNOT̄` between them: Clifford+T on two logical qubits, which
`exists_phase_mem_cliffordTmLim` shows dense in `U(4)` modulo phase. -/
theorem steane_triple_machine :
    ∃ R : Channel TripleReg TripleReg (Option (Fin 3 → SingleErr)),
      ∀ (N : ℕ) (gs : Fin N → TGadget) (U : Fin N → Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
        (V W Y : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j q b, U j q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ j q, V j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ j q, W j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        (∀ j q, Y j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ X : Matrix TripleReg TripleReg ℂ, IsCodeState tripleProj X →
          (∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
              correctedRun (tMachineCircuit R gs U V W Y ω) X = tMachineIdeal gs X)
          ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
              ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
                ≤ QuantumInfo.circuitMeasure N 7 ν 1
                    {ω | correctedRun (tMachineCircuit R gs U V W Y ω) X = tMachineIdeal gs X} := by
  obtain ⟨R, -, hR⟩ := steane_tripleGadgetSet_corrected
  refine ⟨R, fun N gs U V W Y hU hV hW hY X hX => ?_⟩
  have hgood : ∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
      correctedRun (tMachineCircuit R gs U V W Y ω) X = tMachineIdeal gs X := by
    intro ω hω
    rw [← idealRun_tMachineCircuit R gs U V W Y ω X]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hX
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hR (gs j) (U j) (V j) (W j) (Y j) (hU j) (hV j) (hW j) (hY j) (ω j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := 1) ν hp hν
    (out := fun ω => correctedRun (tMachineCircuit R gs U V W Y ω) X)
    (ideal := tMachineIdeal gs X) hgood
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
