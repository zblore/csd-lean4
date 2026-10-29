/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneMachine
public import CsdLean4.Empirical.QM.QEC.SteaneConcat

/-!
# The Steane machine at every level, and its threshold

**Category:** 3-Local (Empirical, QM twin). BACKLOG #227 (QC chain, link 12), residue of #207.

`SteaneMachine.lean` (#207) discharged the threshold theorem's gadget-set premise at level one. Here
the gadgets act on the **concatenated** code `cProj k` of `SteaneConcat.lean` (#86), `7^k` physical
qubits, with faults at every leaf, and the machine's guarantee tends to certainty as the level grows.

## The logical gates, in the Schrödinger picture

`cProj k` is built from an encoder, not as a stabiliser projector, so code preservation goes through
the encoder: a gate `T` with `T E_k = E_k W` keeps level-`k` code states in the code
(`isCodeState_cProj_conj`). The level-one input is new:

* `trace_steaneProj`, ★★ `steaneProj_eq` — **the Steane projector is `E Eᴴ`**: `P − E Eᴴ` is a
  Hermitian idempotent of trace `2 − 2`; `cProj_one` — the level-one concatenated code is the Steane
  code; `mul_steaneEnc_of_comm` — a matrix commuting with `P` acts on the encoder as `Eᴴ T E`;
* ★ `logicalX_mul_steaneEnc`, ★ `logicalZ_mul_steaneEnc` — `X̄ E = E X`, `Z̄ E = E Z`;
* ★★ `exists_hadTransversal_mul_steaneEnc` — **the transversal Hadamard is a logical Hadamard in the
  Schrödinger picture, up to a scalar**: it commutes with `P`, so it acts as a `2 × 2` matrix `V`, and
  exchanging `X̄` with `Z̄` forces `V X = Z V`, `V Z = X V`, whose solutions are the multiples of `H`.
  No coset sum is computed — `SteaneFaultyGate.lean` had this as open;
* `Gadget.exists_blockKron_mul_steaneEnc`, `cTrans` (the gate on all `7^k` qubits), ★★★
  `Gadget.exists_cTrans_mul_cEnc` — **every gadget of the set is a logical gate at every level**, by
  induction one Steane layer at a time.

## Faults at the leaves, and the recovery

* `patBit`, `cFaulty`, `cFaultErr`, ★★ `cFaulty_eq` — **a faulty level-`k` transversal gadget is the
  ideal one followed by the pattern's error**; `patErr_cFaultErr` — that error is an error of the
  pattern (`PatErr`); `cFaultErr_unitary`;
* ★★ `exists_concat_recovery_exact` — #86's level-`k` recovery restores **every** code state exactly
  from every good pattern of unitary errors (the scalar is state-independent, pinned once on `cProj k`).

## The machine

* `Gadget.idealK`, `Gadget.stepK`, `Gadget.isCodeState_idealK`; ★★★
  `steane_gadgetSet_corrected_level` — **at every level, every good step of the gadget set is an
  `IsCorrectedStep` for the level-`k` code**, one recovery for all gadgets;
* `machineCircuitK`, `machineIdealK`, `idealRun_machineCircuitK`; ★★★ `steane_machine_level` — **the
  premise discharged at level `k`, and the bound** `1 − N (21p)^{2^k}/21`;
* ★★★ `steane_machine_threshold` — **below `p < 1/21` that bound tends to `1` as `k → ∞`**, for every
  circuit length `N`: the threshold theorem for the Steane machine.

## Honest scope

⚠️ **One recovery per gadget, applied at level `k`, and ideal.** Each level-`k` gadget is the
transversal gate on `7^k` qubits followed by #86's level-`k` recovery. It is **not** built as the
recursive simulation — a level-`(k−1)` circuit of gadgets with interleaved level-`(k−1)` recoveries —
so recovery faults at any level are not modelled; the noise sits on the gates. Those are their own
BACKLOG rows.

⚠️ **One block, three gates** (`H̄`, `X̄`, `Z̄`), as in #207: not universal.

⚠️ **Independent unitary faults** at the leaves, after the ideal gate, as in #207 and #97.

⚠️ **The scalars are existential.** The logical Hadamard is `c H` for some `c` (a unit-modulus
phase, not computed); the code-preservation and correction statements do not need its value.

References: E. Knill, R. Laflamme, W. Zurek, *Science* 279 (1998) 342; D. Aharonov, M. Ben-Or,
SIAM J. Comput. 38 (2008) 1207; `specs/BACKLOG.md` #227, #207, #97, #86, #62;
`Empirical/QM/QEC/SteaneMachine.lean`, `Empirical/QM/QEC/SteaneConcat.lean`,
`Empirical/QM/QEC/SteaneEncoder.lean`, `Mathlib/QuantumInfo/LevelReduction.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped ENNReal ComplexOrder

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The Steane projector is the encoder's range projector -/

/-- **The Steane code projector has trace two** — `steane_code_dimension` in matrix form. -/
theorem trace_steaneProj : steaneProj.trace = 2 := by
  rw [← steane_code_dimension]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h := congrFun (stabMat_mulVec steaneA steaneB (fun _ => 0) (Pi.single z 1)) z
  rw [mulVec_single_one] at h
  exact h

/-- ★★ **The Steane projector is `E Eᴴ`** for the encoder `E`: `P − E Eᴴ` is a Hermitian idempotent
of trace `2 − 2 = 0`, hence zero. -/
theorem steaneProj_eq : steaneProj = steaneEnc * steaneEncᴴ := by
  have hP := isCodeProjector_steaneProj
  have hPE : steaneProj * steaneEnc = steaneEnc := steaneProj_mul_steaneEnc
  have hEP : steaneEncᴴ * steaneProj = steaneEncᴴ := by
    have h := congrArg conjTranspose hPE
    rwa [conjTranspose_mul, hP.conjTranspose_eq] at h
  have hEE : steaneEncᴴ * steaneEnc = 1 := steaneEnc_conjTranspose_mul
  set Q := steaneProj - steaneEnc * steaneEncᴴ with hQ
  have hQh : Qᴴ = Q := by
    rw [hQ, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hP.conjTranspose_eq]
  have hQQ : Q * Q = Q := by
    rw [hQ, sub_mul, mul_sub, mul_sub, hP.mul_self, ← Matrix.mul_assoc, hPE,
      Matrix.mul_assoc steaneEnc, hEP, Matrix.mul_assoc steaneEnc, ← Matrix.mul_assoc steaneEncᴴ,
      hEE, Matrix.one_mul]
    abel
  have htr : Q.trace = 0 := by
    rw [hQ, trace_sub, trace_steaneProj, trace_mul_comm, hEE, trace_one]
    simp
  have hQQ' : Qᴴ * Q = Q := by rw [hQh, hQQ]
  have h0 : Q = 0 := trace_conjTranspose_mul_self_eq_zero_iff.1 (by rw [hQQ']; exact htr)
  exact sub_eq_zero.1 h0

/-- **A matrix commuting with the Steane projector acts on the encoder as a `2 × 2` matrix**:
`T E = E (Eᴴ T E)`. -/
theorem mul_steaneEnc_of_comm {T : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hT : T * steaneProj = steaneProj * T) :
    T * steaneEnc = steaneEnc * (steaneEncᴴ * T * steaneEnc) := by
  calc T * steaneEnc = T * (steaneProj * steaneEnc) := by rw [steaneProj_mul_steaneEnc]
    _ = steaneProj * T * steaneEnc := by rw [← Matrix.mul_assoc, hT]
    _ = steaneEnc * (steaneEncᴴ * T * steaneEnc) := by
        rw [steaneProj_eq]; simp only [Matrix.mul_assoc]

/-! ### The logical actions at level one, in the Schrödinger picture -/

theorem mul_steaneEnc_apply (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (z : Fin 7 → Fin 2)
    (a : Fin 2) : (M * steaneEnc) z a = (M *ᵥ fun w => steaneEnc w a) z := rfl

/-- ★ **`X̄ E = E X`**: the transversal `X` flips the encoded qubit. -/
theorem logicalX_mul_steaneEnc : pauliMat allOnes 0 * steaneEnc = steaneEnc * pX := by
  ext z a
  rw [mul_steaneEnc_apply, pauliMat_mulVec]
  fin_cases a
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, steaneEnc_col_zero, WithLp.toLp_ofLp,
      logicalX_steaneZero, Matrix.mul_apply, Fin.sum_univ_two]
    simp [pX, ← steaneEnc_col_one]
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, steaneEnc_col_one, WithLp.toLp_ofLp,
      logicalX_steaneOne, Matrix.mul_apply, Fin.sum_univ_two]
    simp [pX, ← steaneEnc_col_zero]

/-- ★ **`Z̄ E = E Z`**: the transversal `Z` signs the encoded qubit. -/
theorem logicalZ_mul_steaneEnc : pauliMat 0 allOnes * steaneEnc = steaneEnc * pZ := by
  ext z a
  rw [mul_steaneEnc_apply, pauliMat_mulVec]
  fin_cases a
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, steaneEnc_col_zero, WithLp.toLp_ofLp,
      logicalZ_steaneZero, Matrix.mul_apply, Fin.sum_univ_two]
    simp [pZ, ← steaneEnc_col_zero]
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, steaneEnc_col_one, WithLp.toLp_ofLp,
      logicalZ_steaneOne, Matrix.mul_apply, Fin.sum_univ_two]
    simp [pZ, ← steaneEnc_col_one]

/-- ★★ **The transversal Hadamard is a logical Hadamard in the Schrödinger picture**, up to a
scalar: `H^{⊗7} E = E (c H)`. It commutes with the code projector, so it acts on the encoder as a
`2 × 2` matrix `V`; exchanging `X̄` and `Z̄` (`hadTransversal_conj_logicalX`/`_logicalZ`) forces
`V X = Z V` and `V Z = X V`, whose solutions are the multiples of `H`. No coset sum is computed. -/
theorem exists_hadTransversal_mul_steaneEnc :
    ∃ c : ℂ, hadTransversal 7 * steaneEnc = steaneEnc * (c • hGateM) := by
  have hTE := mul_steaneEnc_of_comm steaneProj_mul_hadTransversal.symm
  set V := steaneEncᴴ * hadTransversal 7 * steaneEnc with hV
  have hTT : hadTransversal 7 * hadTransversal 7 = 1 := hadTransversal_mul_self
  have hEE : steaneEncᴴ * steaneEnc = 1 := steaneEnc_conjTranspose_mul
  have hXZ : hadTransversal 7 * pauliMat allOnes 0 = pauliMat 0 allOnes * hadTransversal 7 := by
    calc hadTransversal 7 * pauliMat allOnes 0
        = hadTransversal 7 * pauliMat allOnes 0 * (hadTransversal 7 * hadTransversal 7) := by
          rw [hTT, Matrix.mul_one]
      _ = (hadTransversal 7 * pauliMat allOnes 0 * hadTransversal 7) * hadTransversal 7 := by
          simp only [Matrix.mul_assoc]
      _ = pauliMat 0 allOnes * hadTransversal 7 := by rw [hadTransversal_conj_logicalX]
  have hZX : hadTransversal 7 * pauliMat 0 allOnes = pauliMat allOnes 0 * hadTransversal 7 := by
    calc hadTransversal 7 * pauliMat 0 allOnes
        = hadTransversal 7 * pauliMat 0 allOnes * (hadTransversal 7 * hadTransversal 7) := by
          rw [hTT, Matrix.mul_one]
      _ = (hadTransversal 7 * pauliMat 0 allOnes * hadTransversal 7) * hadTransversal 7 := by
          simp only [Matrix.mul_assoc]
      _ = pauliMat allOnes 0 * hadTransversal 7 := by rw [hadTransversal_conj_logicalZ]
  have cancel : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, steaneEnc * A = steaneEnc * B → A = B := by
    intro A B h
    calc A = steaneEncᴴ * steaneEnc * A := by rw [hEE, Matrix.one_mul]
      _ = steaneEncᴴ * (steaneEnc * A) := Matrix.mul_assoc _ _ _
      _ = steaneEncᴴ * (steaneEnc * B) := by rw [h]
      _ = B := by rw [← Matrix.mul_assoc, hEE, Matrix.one_mul]
  have hVX : V * pX = pZ * V := cancel _ _ (by
    calc steaneEnc * (V * pX) = hadTransversal 7 * steaneEnc * pX := by
          rw [hTE, Matrix.mul_assoc steaneEnc V pX]
      _ = hadTransversal 7 * (pauliMat allOnes 0 * steaneEnc) := by
          rw [logicalX_mul_steaneEnc, Matrix.mul_assoc]
      _ = pauliMat 0 allOnes * (hadTransversal 7 * steaneEnc) := by
          rw [← Matrix.mul_assoc, hXZ, Matrix.mul_assoc]
      _ = steaneEnc * (pZ * V) := by
          rw [hTE, ← Matrix.mul_assoc, logicalZ_mul_steaneEnc, Matrix.mul_assoc])
  have hVZ : V * pZ = pX * V := cancel _ _ (by
    calc steaneEnc * (V * pZ) = hadTransversal 7 * steaneEnc * pZ := by
          rw [hTE, Matrix.mul_assoc steaneEnc V pZ]
      _ = hadTransversal 7 * (pauliMat 0 allOnes * steaneEnc) := by
          rw [logicalZ_mul_steaneEnc, Matrix.mul_assoc]
      _ = pauliMat allOnes 0 * (hadTransversal 7 * steaneEnc) := by
          rw [← Matrix.mul_assoc, hZX, Matrix.mul_assoc]
      _ = steaneEnc * (pX * V) := by
          rw [hTE, ← Matrix.mul_assoc, logicalX_mul_steaneEnc, Matrix.mul_assoc])
  have e00 := congrFun (congrFun hVX 0) 0
  have e10 := congrFun (congrFun hVX 1) 0
  have f00 := congrFun (congrFun hVZ 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, pX, pZ] at e00 e10 f00
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  refine ⟨V 0 0 * Real.sqrt 2, ?_⟩
  rw [hTE]
  congr 1
  have hc : (V 0 0 * (Real.sqrt 2 : ℂ)) • hGateM = V 0 0 • !![1, 1; 1, -1] := by
    rw [hGateM, smul_smul, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact e00
  · exact f00.symm
  · rw [e10, ← f00]

/-- ★★ **Every gadget of the set is a logical gate at level one, in the Schrödinger picture**, up to
a scalar: `g^{⊗7} E = E (c g)`. -/
theorem Gadget.exists_blockKron_mul_steaneEnc (G : Gadget) :
    ∃ c : ℂ, blockKron (fun _ : Fin 7 => G.gate) * steaneEnc = steaneEnc * (c • G.gate) := by
  cases G with
  | had => exact exists_hadTransversal_mul_steaneEnc
  | x =>
    refine ⟨1, ?_⟩
    rw [one_smul]
    show blockKron (fun _ : Fin 7 => pX) * steaneEnc = steaneEnc * pX
    rw [blockKron_pX_eq_pauliMat]
    exact logicalX_mul_steaneEnc
  | z =>
    refine ⟨1, ?_⟩
    rw [one_smul]
    show blockKron (fun _ : Fin 7 => pZ) * steaneEnc = steaneEnc * pZ
    rw [blockKron_pZ_eq_pauliMat]
    exact logicalZ_mul_steaneEnc

/-- ★ **`cProj 1` is the Steane projector**: the level-one concatenated code is the Steane code. -/
theorem cProj_one : cProj 1 = steaneProj := by
  rw [steaneProj_eq]
  show blockKron (fun _ : Fin 7 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) * steaneEnc
      * (blockKron (fun _ : Fin 7 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) * steaneEnc)ᴴ = _
  rw [blockKron_one, Matrix.one_mul]

/-! ### The transversal gate at level `k` -/

/-- **The transversal gate at level `k`**: the single-qubit gate `g` on every one of the `7^k`
physical qubits. -/
def cTrans (g : Matrix (Fin 2) (Fin 2) ℂ) : ∀ k, Matrix (cLabel k) (cLabel k) ℂ
  | 0 => g
  | k + 1 => blockKron fun _ : Fin 7 => cTrans g k

/-- ★★★ **Every gadget is a logical gate at every level**: `g^{⊗7^k} E_k = E_k (μ g)` for the
level-`k` encoder, by induction — one Steane layer at a time, the scalar raised to the seventh power
and multiplied by the level-one scalar. -/
theorem Gadget.exists_cTrans_mul_cEnc (G : Gadget) :
    ∀ k, ∃ μ : ℂ, cTrans G.gate k * cEnc k = cEnc k * (μ • G.gate)
  | 0 => ⟨1, by
      show G.gate * (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : ℂ) • G.gate)
      rw [Matrix.mul_one, Matrix.one_mul, one_smul]⟩
  | k + 1 => by
      obtain ⟨μ, hμ⟩ := G.exists_cTrans_mul_cEnc k
      obtain ⟨c, hc⟩ := G.exists_blockKron_mul_steaneEnc
      refine ⟨μ ^ 7 * c, ?_⟩
      have hs : blockKron (fun _ : Fin 7 => μ • G.gate) = μ ^ 7 • blockKron (fun _ : Fin 7 => G.gate) := by
        rw [blockKron_smul (fun _ : Fin 7 => μ) (fun _ : Fin 7 => G.gate)]
        simp
      show blockKron (fun _ : Fin 7 => cTrans G.gate k)
          * (blockKron (fun _ : Fin 7 => cEnc k) * steaneEnc)
        = blockKron (fun _ : Fin 7 => cEnc k) * steaneEnc * ((μ ^ 7 * c) • G.gate)
      rw [← Matrix.mul_assoc, blockKron_mul,
        show (fun _ : Fin 7 => cTrans G.gate k * cEnc k) = fun _ => cEnc k * (μ • G.gate) from
          funext fun _ => hμ,
        ← blockKron_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hc]
      simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]

/-- **A level-`k` gate that acts on the encoder keeps level-`k` code states in the code.** -/
theorem isCodeState_cProj_conj {k : ℕ} {T : Matrix (cLabel k) (cLabel k) ℂ}
    {W : Matrix (Fin 2) (Fin 2) ℂ} (h : T * cEnc k = cEnc k * W)
    {ρ : Matrix (cLabel k) (cLabel k) ℂ} (hρ : IsCodeState (cProj k) ρ) :
    IsCodeState (cProj k) (T * ρ * Tᴴ) := by
  have hE := cEnc_conjTranspose_mul k
  have hT' : (cEnc k)ᴴ * Tᴴ = Wᴴ * (cEnc k)ᴴ := by
    have h' := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_mul] at h'
  unfold IsCodeState cProj at hρ ⊢
  set E := cEnc k
  set X := W * (Eᴴ * ρ * E) * Wᴴ
  have hform : T * ρ * Tᴴ = E * X * Eᴴ := by
    calc T * ρ * Tᴴ = T * (E * Eᴴ * ρ * (E * Eᴴ)) * Tᴴ := congrArg (fun σ => T * σ * Tᴴ) hρ
      _ = (T * E) * (Eᴴ * ρ * E) * (Eᴴ * Tᴴ) := by simp only [Matrix.mul_assoc]
      _ = E * X * Eᴴ := by rw [h, hT']; simp only [X, Matrix.mul_assoc]
  rw [hform]
  calc E * X * Eᴴ = E * (Eᴴ * E) * X * (Eᴴ * E) * Eᴴ := by rw [hE, Matrix.mul_one, Matrix.mul_one]
    _ = E * Eᴴ * (E * X * Eᴴ) * (E * Eᴴ) := by simp only [Matrix.mul_assoc]

/-! ### Faults at the leaves -/

/-- A level-`0` pattern read as a bit. -/
def patBit (x : ConcatPat 7 0) : Bool := x

/-- **The level-`k` transversal gadget under a fault pattern**: at a hit leaf the fault `U a` acts
after the gate, `a` the leaf's address. -/
def cFaulty (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ k, ConcatPat 7 k → ((Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) → Matrix (cLabel k) (cLabel k) ℂ
  | 0, x, U => if patBit x then U Fin.elim0 * g else g
  | k + 1, x, U => blockKron fun b : Fin 7 => cFaulty g k (x b) fun a => U (Fin.cons b a)

/-- **The pattern's error**: the faults alone, the identity at every unhit leaf. -/
def cFaultErr :
    ∀ k, ConcatPat 7 k → ((Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) → Matrix (cLabel k) (cLabel k) ℂ
  | 0, x, U => if patBit x then U Fin.elim0 else 1
  | k + 1, x, U => blockKron fun b : Fin 7 => cFaultErr k (x b) fun a => U (Fin.cons b a)

/-- ★★ **Error propagation at every level**: the faulty transversal gadget is the ideal one followed by
the pattern's error. -/
theorem cFaulty_eq (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ k (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
      cFaulty g k x U = cFaultErr k x U * cTrans g k
  | 0, x, U => by
      show (if patBit x then U Fin.elim0 * g else g) = (if patBit x then U Fin.elim0 else 1) * g
      by_cases hx : patBit x = true
      · rw [ite_eq_left hx, ite_eq_left hx]
      · rw [ite_eq_right hx, ite_eq_right hx, Matrix.one_mul]
  | k + 1, x, U => by
      show blockKron (fun b : Fin 7 => cFaulty g k (x b) fun a => U (Fin.cons b a))
        = blockKron (fun b : Fin 7 => cFaultErr k (x b) fun a => U (Fin.cons b a))
          * blockKron (fun _ : Fin 7 => cTrans g k)
      rw [blockKron_mul]
      congr 1
      funext b
      exact cFaulty_eq g k (x b) _

/-- **The pattern's error is an error of the pattern** in the sense of `PatErr`. -/
theorem patErr_cFaultErr :
    ∀ k (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
      PatErr k x (cFaultErr k x U)
  | 0, x, U => by
      rw [patErr_zero]
      intro hx
      show (if patBit x then U Fin.elim0 else 1) = 1
      rw [ite_eq_right (by simp [patBit, hx])]
  | k + 1, x, U => patErr_succ.2 ⟨_, rfl, fun b => patErr_cFaultErr k (x b) _⟩

/-- **The pattern's error is unitary** when the faults are. -/
theorem cFaultErr_unitary {U' : Matrix (Fin 2) (Fin 2) ℂ → Prop}
    (hU' : ∀ M, U' M → Mᴴ * M = 1) :
    ∀ k (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ a, U' (U a)) → (cFaultErr k x U)ᴴ * cFaultErr k x U = 1
  | 0, x, U, hU => by
      show (if patBit x then U Fin.elim0 else 1)ᴴ * (if patBit x then U Fin.elim0 else 1) = 1
      by_cases hx : patBit x = true
      · rw [ite_eq_left hx]; exact hU' _ (hU _)
      · rw [ite_eq_right hx, conjTranspose_one, Matrix.one_mul]
  | k + 1, x, U, hU => by
      show (blockKron fun b : Fin 7 => cFaultErr k (x b) fun a => U (Fin.cons b a))ᴴ
          * blockKron (fun b : Fin 7 => cFaultErr k (x b) fun a => U (Fin.cons b a)) = 1
      rw [blockKron_conjTranspose, blockKron_mul,
        show (fun b : Fin 7 => (cFaultErr k (x b) fun a => U (Fin.cons b a))ᴴ
            * cFaultErr k (x b) fun a => U (Fin.cons b a)) = fun _ => 1 from
          funext fun b => cFaultErr_unitary hU' k (x b) _ fun a => hU _,
        blockKron_one]

/-! ### The recovery at level `k`, exactly, on every code state -/

/-- ★★ **The level-`k` recovery restores every code state exactly** from every good pattern of
unitary errors — `exists_concat_recovery_unitary` without its trace hypothesis: the scalar does not
depend on the state, so it is pinned to `1` once, on the code projector itself (trace `2`). -/
theorem exists_concat_recovery_exact (k : ℕ) :
    ∃ R : Channel (cLabel k) (cLabel k) (Option (cFam k)),
      ∀ x : ConcatPat 7 k, isBad 7 k x = false →
        ∀ E : Matrix (cLabel k) (cLabel k) ℂ, PatErr k x E → Eᴴ * E = 1 →
          ∀ ρ, IsCodeState (cProj k) ρ → R.apply (E * ρ * Eᴴ) = ρ := by
  obtain ⟨R, hR⟩ := exists_concat_recovery k
  refine ⟨R, fun x hx E hE hU ρ hρ => ?_⟩
  obtain ⟨γ, hγ⟩ := hR x hx E hE
  have hP : cProj k = cProj k * cProj k * cProj k := by
    rw [(isCodeProjector_cProj k).mul_self, (isCodeProjector_cProj k).mul_self]
  have htr : (cProj k).trace ≠ 0 := by
    rw [cProj, trace_mul_comm, cEnc_conjTranspose_mul, trace_one]
    simp
  have h1 := smul_eq_one_of_unitary R hU (hγ _ hP) htr
  rw [hγ ρ hρ, h1, one_smul]

/-! ### The level-`k` gadget set -/

namespace Gadget

/-- The ideal level-`k` gadget. -/
def idealK (G : Gadget) (k : ℕ) (ρ : Matrix (cLabel k) (cLabel k) ℂ) :
    Matrix (cLabel k) (cLabel k) ℂ :=
  cTrans G.gate k * ρ * (cTrans G.gate k)ᴴ

/-- The implemented level-`k` step: the gadget under its fault pattern, then the recovery. -/
def stepK (G : Gadget) (k : ℕ) (R : Channel (cLabel k) (cLabel k) (Option (cFam k)))
    (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (cLabel k) (cLabel k) ℂ) : Matrix (cLabel k) (cLabel k) ℂ :=
  R.apply (cFaulty G.gate k x U * ρ * (cFaulty G.gate k x U)ᴴ)

theorem isCodeState_idealK (G : Gadget) (k : ℕ) {ρ : Matrix (cLabel k) (cLabel k) ℂ}
    (hρ : IsCodeState (cProj k) ρ) : IsCodeState (cProj k) (G.idealK k ρ) := by
  obtain ⟨μ, hμ⟩ := G.exists_cTrans_mul_cEnc k
  exact isCodeState_cProj_conj hμ hρ

end Gadget

/-- ★★★ **The gadget set is a set of corrected steps at every level.** For each `k` one recovery
channel serves every gadget: for each of `H̄`, `X̄`, `Z̄` on the level-`k` code, every unitary fault
at every one of its `7^k` leaves, and every pattern that is **not bad at level `k`** (at most one bad
sub-block at every level of the tree), the faulty transversal gadget followed by the recovery is an
`IsCorrectedStep` for the level-`k` code. -/
theorem steane_gadgetSet_corrected_level (k : ℕ) :
    ∃ R : Channel (cLabel k) (cLabel k) (Option (cFam k)),
      ∀ (G : Gadget) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ a, U a ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ x : ConcatPat 7 k, isBad 7 k x = false →
          IsCorrectedStep (cProj k) (G.idealK k) (G.stepK k R x U) := by
  obtain ⟨R, hR⟩ := exists_concat_recovery_exact k
  refine ⟨R, fun G U hU x hx => ⟨fun ρ hρ => ?_, fun ρ hρ => G.isCodeState_idealK k hρ⟩⟩
  have hunit := cFaultErr_unitary (U' := fun M => M ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (fun M hM => by
      have := Matrix.mem_unitaryGroup_iff'.1 hM
      rwa [Matrix.star_eq_conjTranspose] at this) k x U hU
  have hrw : G.stepK k R x U ρ
      = R.apply (cFaultErr k x U * G.idealK k ρ * (cFaultErr k x U)ᴴ) := by
    show R.apply (cFaulty G.gate k x U * ρ * (cFaulty G.gate k x U)ᴴ) = _
    rw [cFaulty_eq, Gadget.idealK, conjTranspose_mul]
    congr 1
    noncomm_ring
  rw [hrw]
  exact hR x hx _ (patErr_cFaultErr k x U) hunit _ (G.isCodeState_idealK k hρ)

/-! ### The level-`k` machine -/

/-- The machine's circuit at level `k`. -/
def machineCircuitK (k : ℕ) (R : Channel (cLabel k) (cLabel k) (Option (cFam k))) {N : ℕ}
    (gs : Fin N → Gadget) (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : CircuitPat N 7 k) : Circuit (cLabel k) :=
  List.ofFn fun j => ((gs j).idealK k, (gs j).stepK k R (ω j) (U j))

/-- The ideal output of the level-`k` machine. -/
def machineIdealK (k : ℕ) {N : ℕ} (gs : Fin N → Gadget) (ρ : Matrix (cLabel k) (cLabel k) ℂ) :
    Matrix (cLabel k) (cLabel k) ℂ :=
  runMaps (List.ofFn fun j => (gs j).idealK k) ρ

theorem idealRun_machineCircuitK (k : ℕ) (R : Channel (cLabel k) (cLabel k) (Option (cFam k)))
    {N : ℕ} (gs : Fin N → Gadget) (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : CircuitPat N 7 k) (ρ : Matrix (cLabel k) (cLabel k) ℂ) :
    idealRun (machineCircuitK k R gs U ω) ρ = machineIdealK k gs ρ := by
  rw [idealRun, machineCircuitK, machineIdealK, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine at level `k`.** For each level one recovery channel such that, for every
circuit of `N` gadgets on the level-`k` code, every assignment of unitary faults to their `7^k`
leaves and every encoded input, a pattern that makes no gadget bad gives exactly the ideal output
(the level reduction's `correctedRun_eq_idealRun_of_level`, fed the level-`k` corrected steps), and
under independent leaf faults of rate at most `p` the output is ideal with probability at least
`1 − N · codeCapacityBound 21 p k = 1 − N (21 p)^{2^k} / 21`. -/
theorem steane_machine_level (k : ℕ) :
    ∃ R : Channel (cLabel k) (cLabel k) (Option (cFam k)),
      ∀ (N : ℕ) (gs : Fin N → Gadget) (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j a, U j a ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix (cLabel k) (cLabel k) ℂ, IsCodeState (cProj k) ρ →
          (∀ ω : CircuitPat N 7 k, (∀ j, isBad 7 k (ω j) = false) →
              correctedRun (machineCircuitK k R gs U ω) ρ = machineIdealK k gs ρ)
          ∧ ∀ (ν : MeasureTheory.Measure Bool) [MeasureTheory.IsProbabilityMeasure ν] {p : ℝ},
              0 ≤ p → ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p k)
                ≤ QuantumInfo.circuitMeasure N 7 ν k
                    {ω | correctedRun (machineCircuitK k R gs U ω) ρ = machineIdealK k gs ρ} := by
  obtain ⟨R, hR⟩ := steane_gadgetSet_corrected_level k
  refine ⟨R, fun N gs U hU ρ hρ => ?_⟩
  have hgood : ∀ ω : CircuitPat N 7 k, (∀ j, isBad 7 k (ω j) = false) →
      correctedRun (machineCircuitK k R gs U ω) ρ = machineIdealK k gs ρ := by
    intro ω hω
    rw [← idealRun_machineCircuitK k R gs U ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hR (gs j) (U j) (hU j) (ω j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := k) ν hp hν
    (out := fun ω => correctedRun (machineCircuitK k R gs U ω) ρ) (ideal := machineIdealK k gs ρ)
    hgood
  rwa [h21] at h

/-- ★★★ **The threshold theorem for the Steane machine.** Below `p < 1/21` the guaranteed success
probability `1 − N (21 p)^{2^k}/21` of the level-`k` machine tends to `1` as the level grows: every
accuracy is reached by concatenating far enough, for every circuit length `N`. -/
theorem steane_machine_threshold {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (hthr : p < 1 / 21) :
    Filter.Tendsto (fun k : ℕ => 1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p k))
      Filter.atTop (nhds 1) := by
  have h := tendsto_one_sub_codeCapacityBound (n := 7) (N := N) (p := p) (by norm_num [Nat.choose])
    hp (by norm_num [Nat.choose]; linarith)
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
