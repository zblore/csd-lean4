/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneOverlapMachine
public import CsdLean4.Empirical.QM.QEC.SteaneRecursiveSim
public import CsdLean4.Empirical.QM.QEC.SteanePairMachine

/-!
# The ideal decoder and one correct rectangle

**Category:** 3-Local (Empirical, QM twin). BACKLOG #312 (split from #231).

`SteaneOverlapMachine.lean` (~~#233~~) proves the level-one machine correct for whole circuits on an
encoded input, with a final ideal decoding. The level reduction (#313, #314) needs the statement
**per rectangle**, with an ideal decoder in place of the code-state input: a good extended rectangle
followed by the decoder is the decoder followed by the logical gate. This file proves it for the
five single-block gates `H̄`, `X̄`, `Z̄`, `S`, `S†` (`ConcatGadget`, where the transversal `S` is
the logical `S†` and the transversal `S†` the logical `S`), with every location of both recoveries
counted.

## The decoder

* `decodeRow`, `sum_decodeRow` — the rows of the seven-qubit register, moved to the first row of the
  logical qubit;
* ★★ `steaneDecode` — **the ideal Steane decoder as a channel from seven qubits to one**: Steane's
  method (`methodRecovery`), then `Eᴴ` on the code, the complement of the code sent to `|0⟩` so that
  the map is trace preserving on every input;
* `steaneDecode_apply_of_isCodeState` — when the recovery's output is a code state the decoder is
  `Eᴴ R(σ) E`; ★★ `steaneDecode_apply_cssMix` — **a CSS deviation of a code state `ψ` decodes to
  `Eᴴ ψ E`**.

## The gates on the decoded qubit

* `encConj_conj` — a gate intertwining the encoder, `g E = E L`, acts on decoded code states as `L`;
* `ConcatGadget.ideal`, `ConcatGadget.blockKron_mul_steaneProj`, `ConcatGadget.isCodeState_ideal`;
* ★★ `ConcatGadget.steaneDecode_ideal` — **the decoder carries each transversal gate to its logical
  gate**: `D(g ψ g†) = L D(ψ) L†` for every code state `ψ`, the scalar of
  `exists_blockKron_mul_steaneEnc` cancelling.

## A class the transversal `S` carries

The transversal `S` does **not** carry `cssMix`: an `X` on qubit `a` and a `Z` on qubit `b`, a
member, go to `X_a Z_a Z_b`, which is not. Every single fault here acts on one qubit, so the class
is cut down:

* ★ `qubitMix` — **mixtures whose every Kraus operator acts on one qubit** (which qubit may
  depend on the branch); `qubitMix_subset_cssMix`, `id_mem_qubitMix`,
  `isRecovery_methodRecovery_qubitMix`;
* ★★ `deviatesBy_qubitMix_of_exists_atQubit` — `deviatesBy_cssMix_of_exists_atQubit` into the
  smaller class; ★★ `deviatesBy_recUnder_single_qubitMix` — **one fault anywhere in Steane's method
  with its factories is a `qubitMix` deviation of the identity**;
* `propagatesD_qubitMix_of_unitary`, ★★ `ConcatGadget.propagatesD_qubitMix` — **every transversal
  gate of the set, `S` included, carries `qubitMix`**;
* `ConcatGadget.faultyMap`, `ConcatGadget.faultyMap_eq`, `ConcatGadget.faultyMap_none`,
  ★★ `ConcatGadget.deviatesBy_faultyMap` — **a gadget with at most one faulty location, any
  trace-preserving family there, is the ideal gadget followed by a `qubitMix` deviation**.

## The rectangle

* `RecNoise` — the faults a recovery can carry (#235's pair channels, #238's factory faults);
  `RecNoise.run`;
* `RectLoc` (★ `card_rectLoc`: **`403` locations**, the leading recovery's `198`, the gadget's `7`,
  the trailing recovery's `198`), `leadPat`, `gadPat`, `trailPat`, `RectGood`, `rectRun`;
* ★★★ `rectRun_eq` — **a good rectangle hands on a CSS deviation of the ideal gate's output**, on
  every input the leading recovery accepts: a CSS deviation of a code state, the code state itself
  if the leading recovery is the faulty piece;
* ★★★ `steane_rect_correct` — **`D ∘ exRec = 𝒰_L ∘ D`**: on those inputs, a rectangle with at most
  one fault among its `403` locations, followed by the ideal decoder, equals the decoder followed by
  the logical gate.

## Honest scope

⚠️ **The inputs are the ones the leading recovery accepts**: a CSS deviation of a code state when
the leading recovery is fault-free, a code state when it is the faulty piece.
Aliferis–Gottesman–Preskill state correctness on **every** input; that needs the decoder on
arbitrary inputs (#313).

⚠️ **The decoder's classical decoding and its Steane's method are ideal**, as a decoder is by
definition; nothing else in the rectangle is.

⚠️ **One block.** The `CNOT̄` rectangle with the decoder on two blocks is not here; ~~#302~~'s
`steane_pair_exRec` is the exRec statement without the decoder.

⚠️ **No probability here.** The count of malignant pairs per rectangle and the recursion are #314,
#315.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97;
`specs/BACKLOG.md` #312, #313, #314, #315, #231, ~~#233~~, ~~#302~~, ~~#96~~;
`Empirical/QM/QEC/SteaneOverlapMachine.lean`, `Empirical/QM/QEC/SteaneMachineConcat.lean`,
`Empirical/QM/QEC/SteaneFaultyRecovery.lean`, `Mathlib/QuantumInfo/ExtendedRectangle.lean`;
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

/-! ### The decoder -/

/-- Row `z` of the register, moved to the first row of the logical qubit. -/
def decodeRow (z : Fin 7 → Fin 2) : Matrix (Fin 2) (Fin 7 → Fin 2) ℂ :=
  Matrix.of fun i w => if i = 0 ∧ w = z then 1 else 0

/-- The moved rows add up to the identity: `∑_z rowᴴ row = 1`. -/
theorem sum_decodeRow : ∑ z, (decodeRow z)ᴴ * decodeRow z = 1 := by
  ext w w'
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, decodeRow, Matrix.of_apply,
    Fin.sum_univ_two, Matrix.one_apply]
  by_cases h : w = w'
  · subst h
    simp
  · simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, false_and, ↓reduceIte, mul_zero, add_zero,
      h]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : w = z
    · subst hz
      have : ¬ w' = w := fun h' => h h'.symm
      simp [this]
    · simp [hz]

/-- The Kraus operators of the decoder: `Eᴴ` after a branch of Steane's method, or, on the
complement of the code, a row of the register sent to `|0⟩`. -/
def decodeKraus : OutPair × Option (Fin 7 → Fin 2) → Matrix (Fin 2) (Fin 7 → Fin 2) ℂ
  | (m, none) => steaneEncᴴ * methodRecovery.kraus m
  | (m, some z) => decodeRow z * (1 - steaneProj) * methodRecovery.kraus m

theorem decodeKraus_tp : ∑ i, (decodeKraus i)ᴴ * decodeKraus i = 1 := by
  have hP := isCodeProjector_steaneProj
  have hQ : (1 - steaneProj)ᴴ * (1 - steaneProj) = 1 - steaneProj := by
    rw [conjTranspose_sub, conjTranspose_one, hP.conjTranspose_eq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP.mul_self, sub_self,
      sub_zero]
  have hm : ∀ m, ∑ o : Option (Fin 7 → Fin 2), (decodeKraus (m, o))ᴴ * decodeKraus (m, o)
      = (methodRecovery.kraus m)ᴴ * methodRecovery.kraus m := by
    intro m
    rw [Fintype.sum_option]
    simp only [decodeKraus, conjTranspose_mul, conjTranspose_conjTranspose]
    have hsome : ∑ z, (methodRecovery.kraus m)ᴴ * ((1 - steaneProj)ᴴ * (decodeRow z)ᴴ)
          * (decodeRow z * (1 - steaneProj) * methodRecovery.kraus m)
        = (methodRecovery.kraus m)ᴴ * (1 - steaneProj) * methodRecovery.kraus m := by
      calc _ = (methodRecovery.kraus m)ᴴ * ((1 - steaneProj)ᴴ
              * (∑ z, (decodeRow z)ᴴ * decodeRow z) * (1 - steaneProj))
            * methodRecovery.kraus m := by
            rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
            refine Finset.sum_congr rfl fun z _ => ?_
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [sum_decodeRow, Matrix.mul_one, hQ]
    have hfst : (methodRecovery.kraus m)ᴴ * steaneEnc * (steaneEncᴴ * methodRecovery.kraus m)
        = (methodRecovery.kraus m)ᴴ * steaneProj * methodRecovery.kraus m := by
      rw [steaneProj_eq]
      simp only [Matrix.mul_assoc]
    rw [hsome, hfst]
    calc (methodRecovery.kraus m)ᴴ * steaneProj * methodRecovery.kraus m
          + (methodRecovery.kraus m)ᴴ * (1 - steaneProj) * methodRecovery.kraus m
        = (methodRecovery.kraus m)ᴴ * (steaneProj + (1 - steaneProj)) * methodRecovery.kraus m := by
          rw [Matrix.mul_add, Matrix.add_mul]
      _ = _ := by rw [add_sub_cancel, Matrix.mul_one]
  rw [Fintype.sum_prod_type]
  simp only [hm]
  exact methodRecovery.tp

/-- ★★ **The ideal Steane decoder**: a channel from the seven qubits to one — Steane's method, then
`Eᴴ` on the code; the complement of the code, which Steane's method never outputs on the inputs used
here, is sent to `|0⟩` so that the map is trace preserving on every input. -/
def steaneDecode : Channel (Fin 7 → Fin 2) (Fin 2) (OutPair × Option (Fin 7 → Fin 2)) where
  kraus := decodeKraus
  tp := decodeKraus_tp

/-- **When the recovery's output is a code state, the decoder is `Eᴴ R(σ) E`.** -/
theorem steaneDecode_apply_of_isCodeState {σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (h : IsCodeState steaneProj (methodRecovery.apply σ)) :
    steaneDecode.apply σ = steaneEncᴴ * methodRecovery.apply σ * steaneEnc := by
  have hP := isCodeProjector_steaneProj
  have hzero : (1 - steaneProj) * methodRecovery.apply σ = 0 := by
    have h' : methodRecovery.apply σ = steaneProj * methodRecovery.apply σ * steaneProj := h
    rw [Matrix.sub_mul, Matrix.one_mul]
    conv_lhs => rw [h']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self, ← h', sub_self]
  rw [Channel.apply_def, Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_option]
  simp only [steaneDecode, decodeKraus]
  have hnone : ∑ m, steaneEncᴴ * methodRecovery.kraus m * σ
        * (steaneEncᴴ * methodRecovery.kraus m)ᴴ
      = steaneEncᴴ * methodRecovery.apply σ * steaneEnc := by
    rw [Channel.apply_def, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hsome : ∀ z, ∑ m, decodeRow z * (1 - steaneProj) * methodRecovery.kraus m * σ
        * (decodeRow z * (1 - steaneProj) * methodRecovery.kraus m)ᴴ = 0 := by
    intro z
    calc _ = decodeRow z * ((1 - steaneProj) * methodRecovery.apply σ)
            * ((1 - steaneProj)ᴴ * (decodeRow z)ᴴ) := by
          rw [Channel.apply_def, Matrix.mul_sum, Matrix.mul_sum, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [conjTranspose_mul, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.mul_zero, Matrix.zero_mul]
  rw [hnone, Finset.sum_eq_zero fun z _ => hsome z, add_zero]

/-- ★★ **A CSS deviation of a code state decodes to the code state**: `D(F ψ) = Eᴴ ψ E`. -/
theorem steaneDecode_apply_cssMix {F : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
      → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hF : F ∈ cssMix)
    {ψ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hψ : IsCodeState steaneProj ψ) :
    steaneDecode.apply (F ψ) = steaneEncᴴ * ψ * steaneEnc := by
  have hR : methodRecovery.apply (F ψ) = ψ := isRecovery_methodRecovery_cssMix F hF ψ hψ
  rw [steaneDecode_apply_of_isCodeState (by rw [hR]; exact hψ), hR]

/-- A code state decodes to `Eᴴ ψ E`. -/
theorem steaneDecode_apply_code {ψ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hψ : IsCodeState steaneProj ψ) : steaneDecode.apply ψ = steaneEncᴴ * ψ * steaneEnc :=
  steaneDecode_apply_cssMix (F := id) id_mem_cssMix hψ

/-! ### The gates on the decoded qubit -/

/-- **A gate intertwining the encoder acts on decoded code states as its logical gate**: if
`g E = E L`, then `Eᴴ (g ψ g†) E = L (Eᴴ ψ E) L†` for every code state `ψ`. -/
theorem encConj_conj {g : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} {L : Matrix (Fin 2) (Fin 2) ℂ}
    (hL : g * steaneEnc = steaneEnc * L) {ψ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hψ : IsCodeState steaneProj ψ) :
    steaneEncᴴ * (g * ψ * gᴴ) * steaneEnc = L * (steaneEncᴴ * ψ * steaneEnc) * Lᴴ := by
  have hψ' : ψ = steaneEnc * (steaneEncᴴ * ψ * steaneEnc) * steaneEncᴴ := by
    conv_lhs => rw [show ψ = steaneProj * ψ * steaneProj from hψ, steaneProj_eq]
    simp only [Matrix.mul_assoc]
  have hL' : steaneEncᴴ * gᴴ = Lᴴ * steaneEncᴴ := by
    have h := congrArg conjTranspose hL
    rwa [conjTranspose_mul, conjTranspose_mul] at h
  set X := steaneEncᴴ * ψ * steaneEnc
  rw [hψ']
  calc steaneEncᴴ * (g * (steaneEnc * X * steaneEncᴴ) * gᴴ) * steaneEnc
      = steaneEncᴴ * (g * steaneEnc) * X * (steaneEncᴴ * gᴴ) * steaneEnc := by
        simp only [Matrix.mul_assoc]
    _ = (steaneEncᴴ * steaneEnc) * L * X * Lᴴ * (steaneEncᴴ * steaneEnc) := by
        rw [hL, hL']; simp only [Matrix.mul_assoc]
    _ = L * X * Lᴴ := by rw [steaneEnc_conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]

namespace ConcatGadget

/-- The ideal single-block gadget: the transversal gate. -/
def ideal (G : ConcatGadget) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron (fun _ : Fin 7 => G.gate) * ρ * (blockKron (fun _ : Fin 7 => G.gate))ᴴ

/-- On the three gadgets of the level-one set it is their ideal gadget. -/
theorem ideal_of (G : Gadget) : (of G).ideal = G.ideal := rfl

/-- Every transversal gate of the set commutes with the code projector. -/
theorem blockKron_mul_steaneProj (G : ConcatGadget) :
    blockKron (fun _ : Fin 7 => G.gate) * steaneProj
      = steaneProj * blockKron (fun _ : Fin 7 => G.gate) := by
  cases G with
  | of G => exact G.blockKron_mul_steaneProj
  | s => exact sTransversal_mul_steaneProj
  | sDag =>
    have h : blockKron (fun _ : Fin 7 => sDagM) = sTransversalᴴ := by
      rw [sTransversal, blockKron_conjTranspose, sGateM_conjTranspose]
    show blockKron (fun _ : Fin 7 => sDagM) * steaneProj
      = steaneProj * blockKron (fun _ : Fin 7 => sDagM)
    rw [h]
    exact sTransversal_conjTranspose_mul_steaneProj

/-- The transversal gate is unitary. -/
theorem conjTranspose_blockKron_mul (G : ConcatGadget) :
    (blockKron fun _ : Fin 7 => G.gate)ᴴ * blockKron (fun _ : Fin 7 => G.gate) = 1 := by
  rw [blockKron_conjTranspose, blockKron_mul]
  simp only [G.gate_conjTranspose_mul]
  exact blockKron_one

/-- Every gadget of the set keeps code states in the code. -/
theorem isCodeState_ideal (G : ConcatGadget) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : IsCodeState steaneProj ρ) : IsCodeState steaneProj (G.ideal ρ) :=
  isCodeState_conj_of_mul_steaneProj G.blockKron_mul_steaneProj hρ

/-- ★★ **The decoder carries each transversal gate to its logical gate**: `D(g ψ g†) = L D(ψ) L†`
for every code state `ψ`, with `L` the logical gate (`S̄†` for the transversal `S`). -/
theorem steaneDecode_ideal (G : ConcatGadget) {ψ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hψ : IsCodeState steaneProj ψ) :
    steaneDecode.apply (G.ideal ψ)
      = G.logical.gate * steaneDecode.apply ψ * G.logical.gateᴴ := by
  obtain ⟨c, hc⟩ := G.exists_blockKron_mul_steaneEnc
  rw [steaneDecode_apply_code (G.isCodeState_ideal hψ), steaneDecode_apply_code hψ, ideal,
    encConj_conj hc hψ]
  -- the scalar has modulus one: `(c L)ᴴ (c L) = Eᴴ g† g E = 1`
  have e1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, (steaneEnc * X)ᴴ * (steaneEnc * X) = Xᴴ * X := by
    intro X
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc steaneEncᴴ,
      steaneEnc_conjTranspose_mul, Matrix.one_mul]
  have e2 : (blockKron (fun _ : Fin 7 => G.gate) * steaneEnc)ᴴ
      * (blockKron (fun _ : Fin 7 => G.gate) * steaneEnc) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockKron _)ᴴ,
      G.conjTranspose_blockKron_mul, Matrix.one_mul, steaneEnc_conjTranspose_mul]
  have hunit : (c • G.logical.gate)ᴴ * (c • G.logical.gate) = 1 := by
    rw [← e1, ← hc, e2]
  have hL : G.logical.gateᴴ * G.logical.gate = 1 := G.logical.gate_conjTranspose_mul
  have hcc : star c * c = 1 := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hL] at hunit
    exact eq_one_of_smul_one_eq_one hunit
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc, one_smul]

end ConcatGadget

/-! ### A class the transversal `S` carries -/

/-- ★ **Mixtures whose every Kraus operator acts on one qubit** — which qubit may depend on the
branch — trace preserving on the code. -/
def qubitMix : Set (Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
    → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :=
  {E | ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
    (∀ b, ∃ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ), K b = gateOf q M)
      ∧ steaneProj * (∑ b, (K b)ᴴ * K b) * steaneProj = steaneProj
      ∧ E = fun ρ => ∑ b, K b * ρ * (K b)ᴴ}

/-- The class lies inside the CSS class. -/
theorem qubitMix_subset_cssMix : qubitMix ⊆ cssMix := by
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩
  refine ⟨ι, inferInstance, K, fun b => ?_, htp, rfl⟩
  obtain ⟨q, M, h⟩ := hK b
  rw [h]
  exact gateOf_mem_cssSpan q M

/-- "No error" is in the class. -/
theorem id_mem_qubitMix : id ∈ qubitMix := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => ⟨0, 1, (gateOf_one 0).symm⟩, ?_, ?_⟩
  · simp [isCodeProjector_steaneProj.mul_self]
  · funext ρ
    simp

/-- A fault-free Steane's method corrects the class. -/
theorem isRecovery_methodRecovery_qubitMix : IsRecovery steaneProj methodRecovery.apply qubitMix :=
  isRecovery_methodRecovery_cssMix.mono qubitMix_subset_cssMix

/-- ★★ **A channel each of whose branches acts on the code on one qubit is a `qubitMix` deviation of
the identity.** -/
theorem deviatesBy_qubitMix_of_exists_atQubit {ι : Type} [Fintype ι]
    (Φ : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι) (h : ∀ b, ∃ q, AtQubit q (Φ.kraus b)) :
    DeviatesBy steaneProj qubitMix id Φ.apply := by
  have hP := isCodeProjector_steaneProj
  choose q M hM using h
  have hM' : ∀ b, steaneProj * (Φ.kraus b)ᴴ = steaneProj * (gateOf (q b) (M b))ᴴ := by
    intro b
    have h2 := congrArg conjTranspose (hM b)
    rwa [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq] at h2
  intro ρ hρ
  refine ⟨fun σ => ∑ b, gateOf (q b) (M b) * σ * (gateOf (q b) (M b))ᴴ,
    ⟨ι, inferInstance, fun b => gateOf (q b) (M b), fun b => ⟨q b, M b, rfl⟩, ?_, rfl⟩, ?_⟩
  · have hterm : ∀ b, steaneProj * ((gateOf (q b) (M b))ᴴ * gateOf (q b) (M b)) * steaneProj
        = steaneProj * ((Φ.kraus b)ᴴ * Φ.kraus b) * steaneProj := by
      intro b
      calc steaneProj * ((gateOf (q b) (M b))ᴴ * gateOf (q b) (M b)) * steaneProj
          = (steaneProj * (gateOf (q b) (M b))ᴴ) * (gateOf (q b) (M b) * steaneProj) := by
            simp only [Matrix.mul_assoc]
        _ = (steaneProj * (Φ.kraus b)ᴴ) * (Φ.kraus b * steaneProj) := by rw [hM b, hM' b]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_congr rfl fun b _ => hterm b, ← Matrix.sum_mul,
      ← Matrix.mul_sum, Φ.tp, Matrix.mul_one, hP.mul_self]
  · show Φ.apply ρ = ∑ b, gateOf (q b) (M b) * ρ * (gateOf (q b) (M b))ᴴ
    rw [Channel.apply_def]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hρ' : ρ = steaneProj * ρ * steaneProj := hρ
    calc Φ.kraus b * ρ * (Φ.kraus b)ᴴ
        = (Φ.kraus b * steaneProj) * ρ * (steaneProj * (Φ.kraus b)ᴴ) := by
          conv_lhs => rw [hρ']
          simp only [Matrix.mul_assoc]
      _ = (gateOf (q b) (M b) * steaneProj) * ρ * (steaneProj * (gateOf (q b) (M b))ᴴ) := by
          rw [hM b, hM' b]
      _ = gateOf (q b) (M b) * ρ * (gateOf (q b) (M b))ᴴ := by
          conv_rhs => rw [hρ']
          simp only [Matrix.mul_assoc]

/-- ★★ **One fault anywhere in Steane's method with its factories is a `qubitMix` deviation of the
identity** — `deviatesBy_recUnder_single` into the smaller class. -/
theorem deviatesBy_recUnder_single_qubitMix {κ : Type} [Fintype κ]
    {F : MethodRound → Fin 7 → κ → PairOp} {Φ : MethodRound → RetryFaults κ}
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (hOn : ∀ r q k, OnPair q (F r q k))
    (hΦ : ∀ r, (Φ r).Valid) (l : RecLoc) :
    DeviatesBy steaneProj qubitMix id (recUnder F Φ hF hΦ fun l' => decide (l' = l)).apply :=
  deviatesBy_qubitMix_of_exists_atQubit _ (exists_atQubit_recKraus'_single hOn hΦ l)

/-- **A transversal unitary commuting with the code projector carries `qubitMix`**: it conjugates an
operator on qubit `q` to an operator on qubit `q`. -/
theorem propagatesD_qubitMix_of_unitary {u : Matrix (Fin 2) (Fin 2) ℂ} (hu : uᴴ * u = 1)
    (hgP : blockKron (fun _ : Fin 7 => u) * steaneProj
      = steaneProj * blockKron (fun _ : Fin 7 => u)) :
    PropagatesD steaneProj qubitMix
      (fun ρ => blockKron (fun _ : Fin 7 => u) * ρ * (blockKron (fun _ : Fin 7 => u))ᴴ) := by
  set g := blockKron (fun _ : Fin 7 => u) with hg
  have hP := isCodeProjector_steaneProj
  have hgg : gᴴ * g = 1 := by
    rw [hg, blockKron_conjTranspose, blockKron_mul]
    simp only [hu]
    exact blockKron_one
  have hgg' : g * gᴴ = 1 := mul_eq_one_comm.1 hgg
  have hgP' : gᴴ * steaneProj = steaneProj * gᴴ := by
    have h := congrArg conjTranspose hgP
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq] at h
    exact h.symm
  have hmem : ∀ (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ),
      g * gateOf q M * gᴴ = gateOf q (u * M * uᴴ) := by
    intro q M
    rw [hg, PairGadget.blockKron_mul_gateOf_of_unitary hu q M, Matrix.mul_assoc, ← hg, hgg',
      Matrix.mul_one]
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩ ρ _
  have hterm : ∀ b, (g * K b * gᴴ)ᴴ * (g * K b * gᴴ) = g * ((K b)ᴴ * K b) * gᴴ := by
    intro b
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc g * ((K b)ᴴ * gᴴ) * (g * K b * gᴴ) = g * (K b)ᴴ * (gᴴ * g) * K b * gᴴ := by
          simp only [Matrix.mul_assoc]
      _ = g * ((K b)ᴴ * K b) * gᴴ := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨fun σ => ∑ b, (g * K b * gᴴ) * σ * (g * K b * gᴴ)ᴴ,
    ⟨ι, inferInstance, fun b => g * K b * gᴴ, fun b => ?_, ?_, rfl⟩, ?_⟩
  · obtain ⟨q, M, h⟩ := hK b
    exact ⟨q, u * M * uᴴ, by show g * K b * gᴴ = _; rw [h, hmem]⟩
  · rw [Finset.sum_congr rfl fun b _ => hterm b, ← Matrix.sum_mul, ← Matrix.mul_sum]
    calc steaneProj * (g * (∑ b, (K b)ᴴ * K b) * gᴴ) * steaneProj
        = (steaneProj * g) * (∑ b, (K b)ᴴ * K b) * (gᴴ * steaneProj) := by
          simp only [Matrix.mul_assoc]
      _ = g * (steaneProj * (∑ b, (K b)ᴴ * K b) * steaneProj) * gᴴ := by
          rw [← hgP, hgP']; simp only [Matrix.mul_assoc]
      _ = steaneProj := by
          rw [htp, hgP, Matrix.mul_assoc, hgg', Matrix.mul_one]
  · show g * (∑ b, K b * ρ * (K b)ᴴ) * gᴴ
      = ∑ b, (g * K b * gᴴ) * (g * ρ * gᴴ) * (g * K b * gᴴ)ᴴ
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc g * (K b * ρ * (K b)ᴴ) * gᴴ
        = g * K b * (gᴴ * g) * ρ * (gᴴ * g) * (K b)ᴴ * gᴴ := by
          rw [hgg, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

namespace ConcatGadget

/-- ★★ **Every transversal gate of the set, `S` and `S†` included, carries `qubitMix`.** -/
theorem propagatesD_qubitMix (G : ConcatGadget) : PropagatesD steaneProj qubitMix G.ideal :=
  propagatesD_qubitMix_of_unitary G.gate_conjTranspose_mul G.blockKron_mul_steaneProj

/-- **The gadget with a channel at each faulty location**, as `Gadget.faultyMap`, for the five gates
of the set. -/
def faultyMap {γ : Type} [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 7 → Bool)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  ∑ s : Fin 7 → Option γ,
    (roundKraus (fun q k => gateOf q (U q k)) b s * blockKron (fun _ : Fin 7 => G.gate)) * ρ
      * (roundKraus (fun q k => gateOf q (U q k)) b s * blockKron (fun _ : Fin 7 => G.gate))ᴴ

/-- On the three gadgets of the level-one set it is their faulty gadget. -/
theorem faultyMap_of {γ : Type} [Fintype γ] (G : Gadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 7 → Bool) :
    (of G).faultyMap U b = G.faultyMap U b := rfl

/-- The faulty gadget is the ideal one followed by the locations' faults. -/
theorem faultyMap_eq {γ : Type} [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 7 → Bool)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    G.faultyMap U b ρ = ∑ s : Fin 7 → Option γ, roundKraus (fun q k => gateOf q (U q k)) b s
      * G.ideal ρ * (roundKraus (fun q k => gateOf q (U q k)) b s)ᴴ := by
  unfold faultyMap ideal
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [conjTranspose_mul]
  noncomm_ring

/-- A gadget with no faulty location is the ideal gadget. -/
theorem faultyMap_none {γ : Type} [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) : G.faultyMap U (fun _ => false) = G.ideal := by
  funext ρ
  rw [faultyMap_eq, Finset.sum_eq_single (fun _ => none)]
  · rw [roundKraus_none, Matrix.one_mul, conjTranspose_one, Matrix.mul_one]
  · intro s _ hs
    rw [roundKraus_none_of_ne _ hs, Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- ★★ **A gadget with at most one faulty location** — any trace-preserving family on its qubit
there — **is the ideal gadget followed by a `qubitMix` deviation.** -/
theorem deviatesBy_faultyMap {γ : Type} [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    {b : Fin 7 → Bool} (hb : (Finset.univ.filter fun q : Fin 7 => b q = true).card ≤ 1) :
    DeviatesBy steaneProj qubitMix G.ideal (G.faultyMap U b) := by
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, ∀ q, q ≠ q₀ → b q = false := by
    by_cases h : ∃ q, b q = true
    · obtain ⟨q₁, h₁⟩ := h
      refine ⟨q₁, fun q hq => ?_⟩
      by_contra hbq
      rw [Bool.not_eq_false] at hbq
      exact hq (Finset.card_le_one.1 hb q (by simp [hbq]) q₁ (by simp [h₁]))
    · exact ⟨0, fun q _ => by simpa using not_exists.1 h q⟩
  intro ρ _
  refine ⟨fun σ => ∑ s : Fin 7 → Option γ, roundKraus (fun q k => gateOf q (U q k)) b s * σ
      * (roundKraus (fun q k => gateOf q (U q k)) b s)ᴴ,
    ⟨Fin 7 → Option γ, inferInstance, roundKraus (fun q k => gateOf q (U q k)) b,
      fun s => ⟨q₀, _, roundKraus_gateOf U q₀ hq₀ s⟩, ?_, rfl⟩, G.faultyMap_eq U b ρ⟩
  rw [roundKraus_tp (fun q => gateOf_family_tp q (hU q)) b, Matrix.mul_one,
    isCodeProjector_steaneProj.mul_self]

end ConcatGadget

/-! ### The rectangle -/

/-- **The faults a recovery can carry**: a channel on the pair at each extraction location
(~~#235~~) and faults in each round's ancilla factory with its retry (~~#238~~). -/
structure RecNoise (κ : Type) [Fintype κ] where
  /-- The channel at each extraction location, on the data–ancilla pair. -/
  F : MethodRound → Fin 7 → κ → PairOp
  /-- The faults of each round's factory. -/
  Φ : MethodRound → RetryFaults κ
  /-- Each extraction family is trace preserving. -/
  hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1
  /-- Each extraction family acts on its pair. -/
  hOn : ∀ r q k, OnPair q (F r q k)
  /-- The factory faults are valid. -/
  hΦ : ∀ r, (Φ r).Valid

/-- Steane's method with its factories, under the noise and a pattern of faulty locations. -/
def RecNoise.run {κ : Type} [Fintype κ] (N : RecNoise κ) (b : RecLoc → Bool) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (recUnder N.F N.Φ N.hF N.hΦ b).apply

/-- **The locations of one extended rectangle**: the leading recovery's, the gadget's, the trailing
recovery's. -/
abbrev RectLoc : Type := RecLoc ⊕ (Fin 7 ⊕ RecLoc)

/-- ★ **A rectangle has `403` locations**: `198 + 7 + 198`. -/
theorem card_rectLoc : Fintype.card RectLoc = 403 := by
  simp [Fintype.card_sum, Fintype.card_prod, card_methodRound]

/-- The pattern read on the leading recovery. -/
def leadPat (ω : RectLoc → Bool) : RecLoc → Bool := fun l => ω (.inl l)

/-- The pattern read on the gadget. -/
def gadPat (ω : RectLoc → Bool) : Fin 7 → Bool := fun q => ω (.inr (.inl q))

/-- The pattern read on the trailing recovery. -/
def trailPat (ω : RectLoc → Bool) : RecLoc → Bool := fun l => ω (.inr (.inr l))

/-- **A good rectangle**: at most one of its `403` locations is faulty. -/
def RectGood (ω : RectLoc → Bool) : Prop :=
  (Finset.univ.filter fun x => ω x = true).card ≤ 1

/-- **The extended rectangle under a pattern**: the leading recovery, the gadget, the trailing
recovery, each with the pattern's faults. -/
def rectRun {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    (U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ) (N₁ N₂ : RecNoise κ) (ω : RectLoc → Bool)
    (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  N₂.run (trailPat ω) (G.faultyMap U (gadPat ω) (N₁.run (leadPat ω) σ))

theorem RectGood.eq {ω : RectLoc → Bool} (hω : RectGood ω) {x y : RectLoc} (hx : ω x = true)
    (hy : ω y = true) : x = y :=
  Finset.card_le_one.1 hω x (by simp [hx]) y (by simp [hy])

/-- A pattern on a piece with at most one fault: none, or exactly one. -/
theorem pat_cases {α : Type} [DecidableEq α] {f : α → Bool}
    (h : ∀ x y, f x = true → f y = true → x = y) :
    (f = fun _ => false) ∨ ∃ a, f = fun a' => decide (a' = a) := by
  by_cases hex : ∃ a, f a = true
  · obtain ⟨a, ha⟩ := hex
    refine Or.inr ⟨a, funext fun a' => ?_⟩
    by_cases h' : a' = a
    · subst h'
      simpa using ha
    · have : f a' ≠ true := fun h'' => h' (h a' a h'' ha)
      simpa [h'] using this
  · exact Or.inl (funext fun a => by simpa using fun h' => hex ⟨a, h'⟩)

/-- A fault-free recovery is `methodRecovery`. -/
theorem RecNoise.run_none {κ : Type} [Fintype κ] (N : RecNoise κ) :
    N.run (fun _ => false) = methodRecovery.apply :=
  recUnder_none N.hF N.hΦ

/-- ★★★ **A good rectangle hands on a CSS deviation of the ideal gate's output**, on every input the
leading recovery accepts: a CSS deviation `σ = E ψ` of a code state `ψ`, equal to `ψ` if the leading
recovery holds the fault. -/
theorem rectRun_eq {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hω : RectGood ω)
    {ψ σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hψ : IsCodeState steaneProj ψ)
    (hσ : ∃ E ∈ cssMix, σ = E ψ) (hlead : (∃ l, leadPat ω l = true) → σ = ψ) :
    ∃ F ∈ cssMix, rectRun G U N₁ N₂ ω σ = F (G.ideal ψ) := by
  have hgψ := G.isCodeState_ideal hψ
  -- the gadget: at most one faulty location
  have hgad : (Finset.univ.filter fun q : Fin 7 => gadPat ω q = true).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb => by
      have := hω.eq (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
      simpa using this
  -- the pieces' patterns: none, or one location
  have hL := pat_cases (f := leadPat ω) fun x y hx hy => by simpa using hω.eq hx hy
  have hT := pat_cases (f := trailPat ω) fun x y hx hy => by simpa using hω.eq hx hy
  -- at most one faulty piece
  have hLG : ∀ l q, leadPat ω l = true → gadPat ω q = true → False := fun l q hl hq => by
    have := hω.eq hl hq; simp at this
  have hLT : ∀ l l', leadPat ω l = true → trailPat ω l' = true → False := fun l l' hl hl' => by
    have := hω.eq hl hl'; simp at this
  have hGT : ∀ q l', gadPat ω q = true → trailPat ω l' = true → False := fun q l' hq hl' => by
    have := hω.eq hq hl'; simp at this
  simp only [rectRun]
  rcases hL with hL0 | ⟨l, hL1⟩
  · -- the leading recovery is fault-free: it removes the incoming deviation
    obtain ⟨E, hE, rfl⟩ := hσ
    rw [hL0, N₁.run_none, isRecovery_methodRecovery_cssMix E hE ψ hψ]
    rcases hT with hT0 | ⟨l', hT1⟩
    · -- the trailing recovery is fault-free: it removes the gadget's deviation
      obtain ⟨F, hF, hFeq⟩ := G.deviatesBy_faultyMap hU hgad ψ hψ
      refine ⟨id, id_mem_cssMix, ?_⟩
      rw [hT0, N₂.run_none, hFeq, isRecovery_methodRecovery_qubitMix F hF _ hgψ]
      rfl
    · -- the trailing recovery holds the fault: the gadget is ideal, the deviation is handed on
      have hG0 : gadPat ω = fun _ => false := funext fun q => by
        by_contra h
        exact hGT q l' (by simpa using h) (by rw [hT1]; simp)
      rw [hG0, G.faultyMap_none, hT1]
      obtain ⟨F, hF, hFeq⟩ := deviatesBy_recUnder_single_qubitMix N₂.hF N₂.hOn N₂.hΦ l' _ hgψ
      exact ⟨F, qubitMix_subset_cssMix hF, hFeq⟩
  · -- the leading recovery holds the fault: the input is the code state, the gadget carries the
    -- deviation, the trailing recovery removes it
    have hl : leadPat ω l = true := by rw [hL1]; simp
    have hσψ := hlead ⟨l, hl⟩
    have hG0 : gadPat ω = fun _ => false := funext fun q => by
      by_contra h
      exact hLG l q hl (by simpa using h)
    have hT0 : trailPat ω = fun _ => false := funext fun l' => by
      by_contra h
      exact hLT l l' hl (by simpa using h)
    rw [hσψ, hG0, G.faultyMap_none, hT0, N₂.run_none, hL1]
    obtain ⟨E, hE, hEeq⟩ := deviatesBy_recUnder_single_qubitMix N₁.hF N₁.hOn N₁.hΦ l ψ hψ
    obtain ⟨E', hE', hE'eq⟩ := G.propagatesD_qubitMix E hE ψ hψ
    refine ⟨id, id_mem_cssMix, ?_⟩
    rw [show N₁.run (fun a' => decide (a' = l)) ψ = E ψ from hEeq, hE'eq,
      isRecovery_methodRecovery_qubitMix E' hE' _ hgψ]
    rfl

/-- ★★★ **One correct rectangle: `D ∘ exRec = 𝒰_L ∘ D`.** For each of `H̄`, `X̄`, `Z̄`, `S`, `S†`,
any trace-preserving fault family at each gadget location, any noise in either recovery (pair
channels at the extraction locations, faults in the factories), and any pattern with at most one
fault among the rectangle's `403` locations: on every input the leading recovery accepts — a CSS
deviation of a code state, the code state itself if the leading recovery holds the fault — the
rectangle followed by the ideal decoder equals the ideal decoder followed by the logical gate. -/
theorem steane_rect_correct {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hω : RectGood ω)
    {ψ σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hψ : IsCodeState steaneProj ψ)
    (hσ : ∃ E ∈ cssMix, σ = E ψ) (hlead : (∃ l, leadPat ω l = true) → σ = ψ) :
    steaneDecode.apply (rectRun G U N₁ N₂ ω σ)
      = G.logical.gate * steaneDecode.apply σ * G.logical.gateᴴ := by
  obtain ⟨F, hF, hFeq⟩ := rectRun_eq G hU N₁ N₂ hω hψ hσ hlead
  obtain ⟨E, hE, rfl⟩ := hσ
  rw [hFeq, steaneDecode_apply_cssMix hF (G.isCodeState_ideal hψ), steaneDecode_apply_cssMix hE hψ,
    ← steaneDecode_apply_code (G.isCodeState_ideal hψ), G.steaneDecode_ideal hψ,
    steaneDecode_apply_code hψ]

end Steane
end QEC
end QM
end Empirical
end CSD

end
