/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneRectangle
public import CsdLean4.Mathlib.QuantumInfo.ChannelComp

/-!
# The recovery is decode-then-encode, and a rectangle after it is a decoded channel

**Category:** 3-Local (Empirical, QM twin). BACKLOG #313 (split from #231), part (A).

`SteaneRectangle.lean` (#312) proved a good rectangle correct under the ideal decoder `D` on the
inputs the leading recovery accepts. The level reduction needs the decoder on **every** input. This
file proves the structural fact behind it: **the ideal recovery is "decode, then re-encode" on every
input**, `R(ρ) = E · D(ρ) · Eᴴ`. Everything else follows from that identity.

## Every branch of the recovery lands in the code

* `bdot_rowComb` — a stabiliser row combination read against a word is the combination read
  against the word's syndrome; `syndrome_decode` — the decoder is a right inverse of the syndrome
  (the Hamming code is perfect);
* `pauliMat_zero_mul_bitProj`, `bitProj_mul_pauliMat_rowComb`, `pauliMat_zero_mul_phaseProj`,
  `pauliMat_mul_phaseProj` — a `Z`-stabiliser acts on a bit-syndrome space by the sign
  `(−1)^{c·s}` and commutes with the phase-syndrome projectors; an `X`-stabiliser the same with the
  roles exchanged (through the transversal Hadamard);
* ★★ `pauliMat_steane_mul_recKraus` — **every stabiliser fixes every branch of the recovery**: the
  sign it picks up on the syndrome spaces is the sign it picks up commuting past the correction,
  because the correction has exactly the syndrome read;
* ★★ `steaneProj_mul_recKraus` — **`P K = K` for every branch**: the recovery's output is in the
  code on every input.

## Decode-then-encode

* ★★ `isCodeState_methodRecovery` — Steane's method outputs a code state **on every input**;
* `methodRecovery_idem` (`R ∘ R = R`), `steaneDecode_apply` (`D(σ) = Eᴴ R(σ) E` on every input);
* ★★★ `methodRecovery_apply_eq_encode` — **`R(σ) = E D(σ) Eᴴ` on every input**;
* ★★ `steaneDecode_methodRecovery` — **`D ∘ R = D` on every input**: the decoder absorbs a
  fault-free recovery;
* `steaneEncode`, `steaneEncode_apply`, ★ `steaneDecode_encode` (`D ∘ Enc = id`).

## Rectangles after a fault-free recovery

* `decodedChannel` — `D ∘ Rect ∘ Enc`, a channel on the decoded qubit;
* ★★★ `steaneDecode_apply_after_recovery` — **any channel `Rect` run after a fault-free recovery
  satisfies `D ∘ Rect ∘ R = (D ∘ Rect ∘ Enc) ∘ D` on every input**;
* `ConcatGadget.faultyChannel`, `rectChannel` — the gadget and the trailing recovery, under any
  pattern, as one channel;
* ★★★ `steane_badRect` — **a rectangle whose leading recovery is fault-free, with any number of
  faults in its gadget and trailing recovery, is a channel on the decoded qubit**:
  `D(exRec σ) = Φ(D σ)` for every input `σ`, with `Φ = D ∘ Rect ∘ Enc`;
* ★★★ `steane_rect_correct_clean` — **#312 on every input**: with the leading recovery fault-free
  and at most one fault in the rectangle, `D(exRec σ) = L D(σ) L†` for every `σ`.

## Honest scope

⚠️ **The leading recovery is fault-free here.** With faults in it, a rectangle can read the
incoming syndrome and act on it, so `D ∘ exRec = Φ ∘ D` with `Φ` on the decoded qubit alone is
**false** in general: two inputs with one decoded state can give different outputs.
Aliferis–Gottesman–Preskill's form keeps the syndrome — a unitary decoder `D̃` to the logical qubit
and six syndrome bits, every rectangle `D̃⁻¹ Φ̃ D̃` with `Φ̃` acting on the qubit and the syndrome
as its environment — and is part (B) of #313, its Remainder.

⚠️ **One block**, as in #312.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97;
`specs/BACKLOG.md` #313, #312, #314, #315, #231; `Empirical/QM/QEC/SteaneRectangle.lean`,
`Empirical/QM/QEC/SteaneCircuitRecovery.lean`, `Empirical/QM/QEC/SteaneMethod.lean`,
`Mathlib/QuantumInfo/ChannelComp.lean`, `Mathlib/QuantumInfo/StabilizerRecovery.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### Every branch of the recovery lands in the code -/

/-- A row combination read against a word is the combination read against the word's syndrome. -/
theorem bdot_rowComb (c : Fin 3 → Fin 2) (z : Fin 7 → Fin 2) :
    bdot (rowComb c) z = bdot c (syndrome z) := by
  simp only [bdot, rowComb, syndrome, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

/-- **The decoder is a right inverse of the syndrome**: every syndrome is the syndrome of its own
correction — the Hamming code is perfect. -/
theorem syndrome_decode (s : Fin 3 → Fin 2) : syndrome (decode s) = s := by
  revert s
  decide

/-- A `Z`-stabiliser acts on the bit-syndrome space `s` by the sign `(−1)^{c·s}`. -/
theorem pauliMat_zero_mul_bitProj (c s : Fin 3 → Fin 2) :
    pauliMat 0 (rowComb c) * bitProj s = signChar (bdot c s) • bitProj s := by
  ext z w
  simp only [bitProj, synProj, Matrix.mul_diagonal, pauliMat, add_zero, Matrix.smul_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : w = z
  · subst h
    by_cases hs : syndrome w = s
    · simp [hs, pauliSign, bdot_rowComb]
    · simp [hs]
  · simp [h, Ne.symm h]

/-- An `X`-stabiliser commutes with the bit-syndrome projectors: it has syndrome zero. -/
theorem bitProj_mul_pauliMat_rowComb (s c : Fin 3 → Fin 2) :
    bitProj s * pauliMat (rowComb c) 0 = pauliMat (rowComb c) 0 * bitProj s := by
  rw [bitProj_mul_pauliMat, syndrome_rowComb, add_zero]

/-- The transversal Hadamard carries `X^a` to `Z^a`. -/
theorem hadTransversal_conj_pauliMat_x (a : Fin 7 → Fin 2) :
    hadTransversal 7 * pauliMat a 0 * hadTransversal 7 = pauliMat 0 a := by
  rw [hadTransversal_conj_pauliMat, bdot_zero_right, signChar_zero, one_smul]

/-- The transversal Hadamard carries `Z^b` to `X^b`. -/
theorem hadTransversal_conj_pauliMat_z (b : Fin 7 → Fin 2) :
    hadTransversal 7 * pauliMat 0 b * hadTransversal 7 = pauliMat b 0 := by
  rw [hadTransversal_conj_pauliMat, bdot_zero_left, signChar_zero, one_smul]

/-- A `Z`-stabiliser commutes with the phase-syndrome projectors. -/
theorem pauliMat_zero_mul_phaseProj (c t : Fin 3 → Fin 2) :
    pauliMat 0 (rowComb c) * phaseProj t = phaseProj t * pauliMat 0 (rowComb c) := by
  set T := hadTransversal 7
  have hTT : T * T = 1 := hadTransversal_mul_self
  have hXZ : T * pauliMat 0 (rowComb c) * T = pauliMat (rowComb c) 0 :=
    hadTransversal_conj_pauliMat_z _
  have hZ : pauliMat 0 (rowComb c) = T * pauliMat (rowComb c) 0 * T := by
    calc pauliMat 0 (rowComb c) = (T * T) * pauliMat 0 (rowComb c) * (T * T) := by
          rw [hTT, Matrix.one_mul, Matrix.mul_one]
      _ = T * (T * pauliMat 0 (rowComb c) * T) * T := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hXZ]
  rw [hZ, phaseProj]
  calc T * pauliMat (rowComb c) 0 * T * (T * bitProj t * T)
      = T * pauliMat (rowComb c) 0 * (T * T) * bitProj t * T := by simp only [Matrix.mul_assoc]
    _ = T * (pauliMat (rowComb c) 0 * bitProj t) * T := by
        rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = T * (bitProj t * pauliMat (rowComb c) 0) * T := by rw [bitProj_mul_pauliMat_rowComb]
    _ = T * bitProj t * (T * T) * pauliMat (rowComb c) 0 * T := by
        rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = T * bitProj t * T * (T * pauliMat (rowComb c) 0 * T) := by simp only [Matrix.mul_assoc]

/-- An `X`-stabiliser acts on the phase-syndrome space `t` by the sign `(−1)^{c·t}`. -/
theorem pauliMat_mul_phaseProj (c t : Fin 3 → Fin 2) :
    pauliMat (rowComb c) 0 * phaseProj t = signChar (bdot c t) • phaseProj t := by
  set T := hadTransversal 7
  have hTT : T * T = 1 := hadTransversal_mul_self
  have hZX : T * pauliMat (rowComb c) 0 * T = pauliMat 0 (rowComb c) :=
    hadTransversal_conj_pauliMat_x _
  have hX : pauliMat (rowComb c) 0 = T * pauliMat 0 (rowComb c) * T := by
    calc pauliMat (rowComb c) 0 = (T * T) * pauliMat (rowComb c) 0 * (T * T) := by
          rw [hTT, Matrix.one_mul, Matrix.mul_one]
      _ = T * (T * pauliMat (rowComb c) 0 * T) * T := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hZX]
  rw [hX, phaseProj]
  calc T * pauliMat 0 (rowComb c) * T * (T * bitProj t * T)
      = T * pauliMat 0 (rowComb c) * (T * T) * bitProj t * T := by simp only [Matrix.mul_assoc]
    _ = T * (pauliMat 0 (rowComb c) * bitProj t) * T := by
        rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = signChar (bdot c t) • (T * bitProj t * T) := by
        rw [pauliMat_zero_mul_bitProj, Matrix.mul_smul, Matrix.smul_mul]

/-- ★★ **Every stabiliser fixes every branch of the recovery.** The sign a stabiliser picks up on
the branch's syndrome spaces is the sign it picks up commuting past the branch's correction, since
the correction has exactly the syndrome that was read. -/
theorem pauliMat_steane_mul_recKraus (x : Fin 6 → Fin 2) (st : SynPair) :
    pauliMat (steaneA x) (steaneB x) * recKraus st = recKraus st := by
  obtain ⟨s, t⟩ := st
  set c₁ : Fin 3 → Fin 2 := fun i => x (Fin.castAdd 3 i)
  set c₂ : Fin 3 → Fin 2 := fun i => x (Fin.natAdd 3 i)
  have hA : steaneA x = rowComb c₁ := rfl
  have hB : steaneB x = rowComb c₂ := rfl
  have hS : pauliMat (steaneA x) (steaneB x)
      = pauliMat (rowComb c₁) 0 * pauliMat 0 (rowComb c₂) := by
    rw [pauliMat_mul, hA, hB, add_zero, zero_add, pauliSign, bdot_zero_left, signChar_zero,
      one_smul]
  have hSP : pauliMat (steaneA x) (steaneB x) * phaseProj t * bitProj s
      = (signChar (bdot c₁ t) * signChar (bdot c₂ s)) • (phaseProj t * bitProj s) := by
    rw [hS]
    calc pauliMat (rowComb c₁) 0 * pauliMat 0 (rowComb c₂) * phaseProj t * bitProj s
        = pauliMat (rowComb c₁) 0 * (pauliMat 0 (rowComb c₂) * phaseProj t) * bitProj s := by
          simp only [Matrix.mul_assoc]
      _ = pauliMat (rowComb c₁) 0 * (phaseProj t * pauliMat 0 (rowComb c₂)) * bitProj s := by
          rw [pauliMat_zero_mul_phaseProj]
      _ = (pauliMat (rowComb c₁) 0 * phaseProj t) * (pauliMat 0 (rowComb c₂) * bitProj s) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [pauliMat_mul_phaseProj, pauliMat_zero_mul_bitProj, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul]
  have hsign : signChar (bdot (steaneA x) (decode t) + bdot (steaneB x) (decode s))
      * (signChar (bdot c₁ t) * signChar (bdot c₂ s)) = 1 := by
    rw [hA, hB, bdot_rowComb, bdot_rowComb, syndrome_decode, syndrome_decode, signChar_add]
    calc signChar (bdot c₁ t) * signChar (bdot c₂ s) * (signChar (bdot c₁ t) * signChar (bdot c₂ s))
        = (signChar (bdot c₁ t) * signChar (bdot c₁ t))
          * (signChar (bdot c₂ s) * signChar (bdot c₂ s)) := by ring
      _ = 1 := by rw [signChar_mul_self, signChar_mul_self, one_mul]
  rw [recKraus_eq]
  calc pauliMat (steaneA x) (steaneB x)
        * (pauliMat (decode (s, t).1) (decode (s, t).2) * phaseProj (s, t).2 * bitProj (s, t).1)
      = (pauliMat (steaneA x) (steaneB x) * pauliMat (decode s) (decode t))
        * (phaseProj t * bitProj s) := by simp only [Matrix.mul_assoc]
    _ = (signChar (bdot (steaneA x) (decode t) + bdot (steaneB x) (decode s))
          • (pauliMat (decode s) (decode t) * pauliMat (steaneA x) (steaneB x)))
        * (phaseProj t * bitProj s) := by rw [pauliMat_comm]
    _ = signChar (bdot (steaneA x) (decode t) + bdot (steaneB x) (decode s))
          • (pauliMat (decode s) (decode t)
            * (pauliMat (steaneA x) (steaneB x) * phaseProj t * bitProj s)) := by
        rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]
    _ = pauliMat (decode s) (decode t) * phaseProj t * bitProj s := by
        rw [hSP, Matrix.mul_smul, smul_smul, hsign, one_smul]
        simp only [Matrix.mul_assoc]

/-- ★★ **Every branch of the recovery lands in the code**: `P K = K`. -/
theorem steaneProj_mul_recKraus (st : SynPair) : steaneProj * recKraus st = recKraus st := by
  rw [steaneProj, stabMat, Matrix.smul_mul, Finset.sum_mul]
  simp only [genMat, signChar_zero, one_smul, pauliMat_steane_mul_recKraus]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-! ### Decode-then-encode -/

/-- ★★ **Steane's method outputs a code state on every input.** -/
theorem isCodeState_methodRecovery (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    IsCodeState steaneProj (methodRecovery.apply ρ) := by
  have hP := isCodeProjector_steaneProj
  rw [methodRecovery_apply]
  show _ = steaneProj * _ * steaneProj
  rw [Channel.apply_def, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun st _ => ?_
  change recKraus st * ρ * (recKraus st)ᴴ = steaneProj * (recKraus st * ρ * (recKraus st)ᴴ)
    * steaneProj
  have h1 := steaneProj_mul_recKraus st
  have h2 : (recKraus st)ᴴ * steaneProj = (recKraus st)ᴴ := by
    have h := congrArg conjTranspose h1
    rwa [conjTranspose_mul, hP.conjTranspose_eq] at h
  calc recKraus st * ρ * (recKraus st)ᴴ
      = (steaneProj * recKraus st) * ρ * ((recKraus st)ᴴ * steaneProj) := by rw [h1, h2]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **`R ∘ R = R`**: the fault-free recovery is idempotent on every input. -/
theorem methodRecovery_idem (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    methodRecovery.apply (methodRecovery.apply ρ) = methodRecovery.apply ρ :=
  isRecovery_methodRecovery_cssMix.apply_of_isCodeState id_mem_cssMix
    (isCodeState_methodRecovery ρ)

/-- **The decoder on every input**: `D(σ) = Eᴴ R(σ) E`. -/
theorem steaneDecode_apply (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply σ = steaneEncᴴ * methodRecovery.apply σ * steaneEnc :=
  steaneDecode_apply_of_isCodeState (isCodeState_methodRecovery σ)

/-- ★★★ **The fault-free recovery is decode-then-encode, on every input**:
`R(σ) = E D(σ) Eᴴ`. -/
theorem methodRecovery_apply_eq_encode (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    methodRecovery.apply σ = steaneEnc * steaneDecode.apply σ * steaneEncᴴ := by
  rw [steaneDecode_apply]
  have h : methodRecovery.apply σ = steaneProj * methodRecovery.apply σ * steaneProj :=
    isCodeState_methodRecovery σ
  conv_lhs => rw [h, steaneProj_eq]
  simp only [Matrix.mul_assoc]

/-- ★★ **The decoder absorbs a fault-free recovery**: `D ∘ R = D` on every input. -/
theorem steaneDecode_methodRecovery (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (methodRecovery.apply σ) = steaneDecode.apply σ := by
  rw [steaneDecode_apply, steaneDecode_apply, methodRecovery_idem]

/-- **The encoder** as a channel from one qubit to seven. -/
def steaneEncode : Channel (Fin 2) (Fin 7 → Fin 2) Unit where
  kraus _ := steaneEnc
  tp := by simp [steaneEnc_conjTranspose_mul]

theorem steaneEncode_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    steaneEncode.apply X = steaneEnc * X * steaneEncᴴ := by
  simp [Channel.apply_def, steaneEncode]

/-- ★ **`D ∘ Enc = id`.** -/
theorem steaneDecode_encode (X : Matrix (Fin 2) (Fin 2) ℂ) :
    steaneDecode.apply (steaneEncode.apply X) = X := by
  have hP := isCodeProjector_steaneProj
  have hEP : steaneEncᴴ * steaneProj = steaneEncᴴ := by
    have h := congrArg conjTranspose steaneProj_mul_steaneEnc
    rwa [conjTranspose_mul, hP.conjTranspose_eq] at h
  have hcode : IsCodeState steaneProj (steaneEnc * X * steaneEncᴴ) := by
    show _ = steaneProj * (steaneEnc * X * steaneEncᴴ) * steaneProj
    calc steaneEnc * X * steaneEncᴴ
        = (steaneProj * steaneEnc) * X * (steaneEncᴴ * steaneProj) := by
          rw [steaneProj_mul_steaneEnc, hEP]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [steaneEncode_apply, steaneDecode_apply_code hcode]
  calc steaneEncᴴ * (steaneEnc * X * steaneEncᴴ) * steaneEnc
      = (steaneEncᴴ * steaneEnc) * X * (steaneEncᴴ * steaneEnc) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [steaneEnc_conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]

/-! ### Rectangles after a fault-free recovery -/

/-- **A seven-qubit channel read on the decoded qubit**: encode, run it, decode. -/
def decodedChannel {ι : Type} [Fintype ι] (Rect : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι) :
    Channel (Fin 2) (Fin 2) ((OutPair × Option (Fin 7 → Fin 2)) × (ι × Unit)) :=
  steaneDecode.comp (Rect.comp steaneEncode)

/-- ★★★ **Any channel run after a fault-free recovery is a channel on the decoded qubit**:
`D(Rect(R σ)) = (D ∘ Rect ∘ Enc)(D σ)` for every input `σ`. -/
theorem steaneDecode_apply_after_recovery {ι : Type} [Fintype ι]
    (Rect : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι)
    (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (Rect.apply (methodRecovery.apply σ))
      = (decodedChannel Rect).apply (steaneDecode.apply σ) := by
  rw [decodedChannel, Channel.comp_apply, Channel.comp_apply, steaneEncode_apply,
    ← methodRecovery_apply_eq_encode]

namespace ConcatGadget

/-- **The faulty gadget as a channel**: trace preserving whenever every location's family is. -/
def faultyChannel {γ : Type} [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (b : Fin 7 → Bool) : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Fin 7 → Option γ) where
  kraus s := roundKraus (fun q k => gateOf q (U q k)) b s * blockKron (fun _ : Fin 7 => G.gate)
  tp := by
    have h := roundKraus_tp (fun q => gateOf_family_tp q (hU q)) b
    simp only [conjTranspose_mul]
    calc ∑ s, (blockKron fun _ : Fin 7 => G.gate)ᴴ * (roundKraus (fun q k => gateOf q (U q k)) b s)ᴴ
          * (roundKraus (fun q k => gateOf q (U q k)) b s * blockKron fun _ : Fin 7 => G.gate)
        = (blockKron fun _ : Fin 7 => G.gate)ᴴ
          * (∑ s, (roundKraus (fun q k => gateOf q (U q k)) b s)ᴴ
          * roundKraus (fun q k => gateOf q (U q k)) b s) * blockKron fun _ : Fin 7 => G.gate := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          noncomm_ring
      _ = 1 := by rw [h, Matrix.mul_one, G.conjTranspose_blockKron_mul]

theorem faultyChannel_apply {γ : Type} [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (b : Fin 7 → Bool) : (G.faultyChannel U hU b).apply = G.faultyMap U b := rfl

end ConcatGadget

/-- **The rectangle after its leading recovery**: the gadget, then the trailing recovery, each under
its pattern, as one channel. -/
def rectChannel {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N : RecNoise κ) (ω : RectLoc → Bool) :
    Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ((RoundIdx κ × RoundIdx κ) × (Fin 7 → Option γ)) :=
  (recUnder N.F N.Φ N.hF N.hΦ (trailPat ω)).comp (G.faultyChannel U hU (gadPat ω))

/-- With a fault-free leading recovery, the rectangle is `rectChannel` after `R`. -/
theorem rectRun_eq_rectChannel {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hL : leadPat ω = fun _ => false)
    (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    rectRun G U N₁ N₂ ω σ = (rectChannel G U hU N₂ ω).apply (methodRecovery.apply σ) := by
  rw [rectRun, hL, N₁.run_none, rectChannel, Channel.comp_apply, ConcatGadget.faultyChannel_apply]
  rfl

/-- ★★★ **A rectangle after a fault-free recovery, with any faults in its gadget and trailing
recovery, is a channel on the decoded qubit**: `D(exRec σ) = Φ(D σ)` for every input `σ`, with
`Φ = D ∘ Rect ∘ Enc` (`decodedChannel`). -/
theorem steane_badRect {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hL : leadPat ω = fun _ => false)
    (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (rectRun G U N₁ N₂ ω σ)
      = (decodedChannel (rectChannel G U hU N₂ ω)).apply (steaneDecode.apply σ) := by
  rw [rectRun_eq_rectChannel G hU N₁ N₂ hL, steaneDecode_apply_after_recovery]

/-- ★★★ **One correct rectangle on every input**: with the leading recovery fault-free and at most
one fault among the rectangle's `403` locations, `D(exRec σ) = L D(σ) L†` for every `σ` — #312's
`steane_rect_correct` without its restriction on the input. -/
theorem steane_rect_correct_clean {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hω : RectGood ω)
    (hL : leadPat ω = fun _ => false) (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (rectRun G U N₁ N₂ ω σ)
      = G.logical.gate * steaneDecode.apply σ * G.logical.gateᴴ := by
  have hψ := isCodeState_methodRecovery σ
  have hrun : rectRun G U N₁ N₂ ω σ = rectRun G U N₁ N₂ ω (methodRecovery.apply σ) := by
    simp only [rectRun, hL, N₁.run_none, methodRecovery_idem]
  rw [hrun, ← steaneDecode_methodRecovery σ]
  generalize methodRecovery.apply σ = ψ at hψ ⊢
  exact steane_rect_correct G hU N₁ N₂ hω hψ ⟨id, id_mem_cssMix, rfl⟩
    (fun ⟨l, hl⟩ => by simp [hL] at hl)

end Steane
end QEC
end QM
end Empirical
end CSD

end
