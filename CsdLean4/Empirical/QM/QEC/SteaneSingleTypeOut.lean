/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneSingleType

/-!
# Steane's method with one fault has single-type branches

**Category:** 3-Local (Empirical, QM twin). BACKLOG #321 (split from #320).

~~#320~~'s `steane_rect_isGoodAfter_of_singleTypeOut` assumes that Steane's method, with its
factories and one fault anywhere, has branches whose outputs lie in the single-type syndrome spaces
(`RecNoise.SingleTypeOut`). This file proves it, on **every** input, and so removes the hypothesis.

## The syndrome projectors

* `phaseProj_mul_pauliMat_zero`, `bitProj_mul_pauliMat_zero` — a `Z`-type Pauli shifts the phase
  syndrome by its own and fixes the bit syndrome;
* ★ `bitProj_mul_of_commute` — **an operator commuting with every `Z`-stabiliser commutes with every
  bit-syndrome projector**; so the two kinds of syndrome projector commute
  (`bitProj_mul_phaseProj`);
* `gateOf_mul_bitProj`, `gateOf_mul_phaseProj` — an operator on qubit `q` moves either syndrome by
  `0` or by the syndrome `h_q` of qubit `q`;
* `synCorr_mul_steaneEnc_conjTranspose_mul_bitProj` (and `_phaseProj`) — the rows of ~~#317~~'s
  decoder see one syndrome pair each.

## Single-type outputs

* `qubitSynProj q` — the projector onto the four syndrome spaces of the errors on qubit `q`: no
  error, `X_q`, `Z_q`, `Y_q`; ★ `isSingleTypeOp_of_qubitSynProj_mul` — **an operator landing
  there is single-type**, as is one landing on bit syndrome `0` or on phase syndrome `0`;
* ★★ `qubitSynProj_mul_phaseFaultOp_mul_bitProj_zero` — **the phase round with an operator on the
  pair `q`, fed bit syndrome `0`, lands in the syndrome spaces of qubit `q`**: the residual phase
  syndrome is the data's `Z` error on `q` plus the readout's error on `q`, the bit syndrome the
  data's `X` error on `q`;
* ★★ `bitProj_zero_mul_ancPhaseOp_mul_bitProj_zero` — **the phase round with a periodic ancilla
  keeps bit syndrome `0`**: its readout commutes with every `X`-stabiliser.

## Steane's method

* ★★★ `isSingleTypeOp_recKraus'_single` — **every branch of Steane's method with its factories and
  one fault anywhere is single-type, on every input.** A fault in the bit round leaves the
  fault-free phase round to land the output on phase syndrome `0`; a fault in the phase round meets
  a fault-free bit round's bit syndrome `0`, and is a pair operator (an extraction location), a
  periodic ancilla or a one-qubit ancilla error (a factory location, through ~~#239~~'s
  `goodAnc_retryOut_single`);
* ★★★ `RecNoise.singleTypeOut` — #320's hypothesis, for every noise model;
* ★★★ `steane_rect_isGoodAfter` — **for each of `H̄`, `X̄`, `Z̄`, `S`, `S†`, every rectangle with
  at most one fault among its `403` locations is good after its leading recovery** (#316's
  `IsGoodAfter`, `D = steaneDecode`), on every input, with no hypothesis on the noise beyond the
  fault model's.

## Honest scope

⚠️ **One block, one rectangle.** Joining the rectangles of #233's machine into
`one_sub_le_measure_decode_recRun` is #319.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, § 4;
`specs/BACKLOG.md` #321, #320, #319, #315, #239;
`Empirical/QM/QEC/SteaneSingleType.lean`, `Empirical/QM/QEC/SteaneOverlapMachine.lean`,
`Empirical/QM/QEC/SteaneVerifiedAncilla.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md`
link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The syndrome projectors -/

/-- Conjugation by the transversal Hadamard is multiplicative. -/
theorem hadTransversal_conj_mul (A B : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    hadTransversal 7 * A * hadTransversal 7 * (hadTransversal 7 * B * hadTransversal 7)
      = hadTransversal 7 * (A * B) * hadTransversal 7 := by
  calc _ = hadTransversal 7 * A * (hadTransversal 7 * hadTransversal 7) * B * hadTransversal 7 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hadTransversal_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- A `Z`-type Pauli fixes every bit-syndrome projector. -/
theorem bitProj_mul_pauliMat_zero (s : Fin 3 → Fin 2) (b : Fin 7 → Fin 2) :
    bitProj s * pauliMat 0 b = pauliMat 0 b * bitProj s := by
  rw [bitProj_mul_pauliMat, syndrome_zero, add_zero]

/-- **A `Z`-type Pauli shifts the phase syndrome by its own**: `Π'_t Z^b = Z^b Π'_{t + syn b}`. -/
theorem phaseProj_mul_pauliMat_zero (t : Fin 3 → Fin 2) (b : Fin 7 → Fin 2) :
    phaseProj t * pauliMat 0 b = pauliMat 0 b * phaseProj (t + syndrome b) := by
  rw [← hadTransversal_conj_pauliMat_x b, phaseProj, phaseProj, hadTransversal_conj_mul,
    hadTransversal_conj_mul, bitProj_mul_pauliMat]

/-- Two different syndromes are told apart by some `Z`-stabiliser. -/
theorem exists_bdot_ne {s u : Fin 3 → Fin 2} (h : s ≠ u) : ∃ c, bdot c s ≠ bdot c u := by
  revert s u
  decide

theorem signChar_ne {x y : Fin 2} (h : x ≠ y) : signChar x ≠ signChar y := by
  revert h
  fin_cases x <;> fin_cases y <;> norm_num [signChar]

/-- ★ **An operator commuting with every `Z`-stabiliser commutes with every bit-syndrome
projector**: between two different bit syndromes some `Z`-stabiliser has two different signs. -/
theorem bitProj_mul_of_commute {M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hM : ∀ c, pauliMat 0 (rowComb c) * M = M * pauliMat 0 (rowComb c)) (s : Fin 3 → Fin 2) :
    bitProj s * M = M * bitProj s := by
  have hoff : ∀ u v, u ≠ v → bitProj u * M * bitProj v = 0 := by
    intro u v huv
    obtain ⟨c, hc⟩ := exists_bdot_ne huv
    have h1 : bitProj u * (pauliMat 0 (rowComb c) * M) * bitProj v
        = signChar (bdot c u) • (bitProj u * M * bitProj v) := by
      rw [← Matrix.mul_assoc, bitProj_mul_pauliMat_zero, pauliMat_zero_mul_bitProj, Matrix.smul_mul,
        Matrix.smul_mul]
    have h2 : bitProj u * (M * pauliMat 0 (rowComb c)) * bitProj v
        = signChar (bdot c v) • (bitProj u * M * bitProj v) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, pauliMat_zero_mul_bitProj, Matrix.mul_smul,
        Matrix.mul_smul, ← Matrix.mul_assoc]
    rw [hM c, h2] at h1
    have h3 : (signChar (bdot c v) - signChar (bdot c u)) • (bitProj u * M * bitProj v) = 0 := by
      rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (signChar_ne (Ne.symm hc)))
  calc bitProj s * M = bitProj s * M * ∑ v, bitProj v := by rw [sum_bitProj, Matrix.mul_one]
    _ = bitProj s * M * bitProj s := by
        rw [Matrix.mul_sum, Finset.sum_eq_single s (fun v _ hv => hoff s v (Ne.symm hv)) (by simp)]
    _ = (∑ u, bitProj u) * M * bitProj s := by
        rw [Matrix.sum_mul, Matrix.sum_mul,
          Finset.sum_eq_single s (fun u _ hu => hoff u s hu) (by simp)]
    _ = M * bitProj s := by rw [sum_bitProj, Matrix.one_mul]

/-- **The bit and phase syndrome projectors commute.** -/
theorem bitProj_mul_phaseProj (s t : Fin 3 → Fin 2) :
    bitProj s * phaseProj t = phaseProj t * bitProj s :=
  bitProj_mul_of_commute (fun c => pauliMat_zero_mul_phaseProj c t) s

theorem syndrome_unitErr_ne_zero (q : Fin 7) : syndrome (unitErr q) ≠ 0 := by
  revert q
  decide

theorem ne_add_syndrome_unitErr (s : Fin 3 → Fin 2) (q : Fin 7) :
    s ≠ s + syndrome (unitErr q) := fun h =>
  syndrome_unitErr_ne_zero q (add_left_cancel (h.symm.trans (add_zero s).symm))

/-- An operator on qubit `q` moves the bit syndrome by `0` or by `h_q`, and nowhere else. -/
theorem bitProj_mul_gateOf_mul_bitProj_eq_zero {q : Fin 7} (M : Matrix (Fin 2) (Fin 2) ℂ)
    {s u : Fin 3 → Fin 2} (h₁ : u ≠ s) (h₂ : u ≠ s + syndrome (unitErr q)) :
    bitProj u * gateOf q M * bitProj s = 0 := by
  ext z w
  simp only [bitProj, synProj, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hag : ∀ i, i ≠ q → z i = w i
  · by_cases hw : syndrome w = s
    · have hz : syndrome z ≠ u := by
        rcases eq_or_eq_add_unitErr_of_agree (fun i hi => (hag i hi).symm) with h | h
        · rw [h, hw]; exact Ne.symm h₁
        · rw [h, syndrome_add, hw]; exact Ne.symm h₂
      simp [hz]
    · simp [hw]
  · simp [gateOf_apply_of_not_agree hag]

/-- ★ **An operator on qubit `q` moves the bit syndrome by `0` or by `h_q`.** -/
theorem gateOf_mul_bitProj (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 3 → Fin 2) :
    gateOf q M * bitProj s
      = (bitProj s + bitProj (s + syndrome (unitErr q))) * (gateOf q M * bitProj s) := by
  calc gateOf q M * bitProj s = (∑ u, bitProj u) * gateOf q M * bitProj s := by
        rw [sum_bitProj, Matrix.one_mul]
    _ = _ := by
        rw [Matrix.sum_mul, Matrix.sum_mul, Fintype.sum_eq_add s (s + syndrome (unitErr q))
          (ne_add_syndrome_unitErr s q)
          (fun u hu => bitProj_mul_gateOf_mul_bitProj_eq_zero M hu.1 hu.2), Matrix.add_mul]
        simp only [Matrix.mul_assoc]

/-- ★ **And the phase syndrome**: the bit statement in the Hadamard basis. -/
theorem gateOf_mul_phaseProj (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) (t : Fin 3 → Fin 2) :
    gateOf q M * phaseProj t
      = (phaseProj t + phaseProj (t + syndrome (unitErr q))) * (gateOf q M * phaseProj t) := by
  have hG : gateOf q M = hadTransversal 7 * gateOf q (hGateM * M * hGateM) * hadTransversal 7 := by
    rw [hadTransversal_conj_gateOf]
    simp only [← Matrix.mul_assoc, SU2.hGateM_mul_self, Matrix.one_mul]
    simp only [Matrix.mul_assoc, SU2.hGateM_mul_self, Matrix.mul_one]
  have hb := gateOf_mul_bitProj q (hGateM * M * hGateM) t
  calc gateOf q M * phaseProj t
      = hadTransversal 7 * (gateOf q (hGateM * M * hGateM) * bitProj t) * hadTransversal 7 := by
        rw [hG, phaseProj, hadTransversal_conj_mul]
    _ = hadTransversal 7 * ((bitProj t + bitProj (t + syndrome (unitErr q)))
          * (gateOf q (hGateM * M * hGateM) * bitProj t)) * hadTransversal 7 := by rw [← hb]
    _ = _ := by
        rw [← hadTransversal_conj_mul, ← hadTransversal_conj_mul, ← hG]
        simp only [phaseProj, Matrix.mul_add, Matrix.add_mul]

theorem synCorr_mul_steaneEnc_eq (st : SynPair) :
    synCorr st * steaneEnc = pauliMat (decode st.1) (decode st.2) * steaneProj * steaneEnc := by
  rw [Matrix.mul_assoc, steaneProj_mul_steaneEnc, synCorr]

theorem bitProj_mul_synCorr_mul_steaneEnc (u : Fin 3 → Fin 2) (st : SynPair) :
    bitProj u * (synCorr st * steaneEnc) = if u = st.1 then synCorr st * steaneEnc else 0 := by
  rw [synCorr_mul_steaneEnc_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    bitProj_mul_pauliMat_mul_steaneProj, syndrome_decode]
  split_ifs <;> simp

theorem phaseProj_mul_synCorr_mul_steaneEnc (u : Fin 3 → Fin 2) (st : SynPair) :
    phaseProj u * (synCorr st * steaneEnc) = if u = st.2 then synCorr st * steaneEnc else 0 := by
  rw [synCorr_mul_steaneEnc_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    phaseProj_mul_pauliMat_mul_steaneProj, syndrome_decode]
  split_ifs <;> simp

/-- **A row of the decoder sees one bit syndrome.** -/
theorem synCorr_mul_steaneEnc_conjTranspose_mul_bitProj (st : SynPair) (u : Fin 3 → Fin 2) :
    (synCorr st * steaneEnc)ᴴ * bitProj u = if u = st.1 then (synCorr st * steaneEnc)ᴴ else 0 := by
  have h := congrArg conjTranspose (bitProj_mul_synCorr_mul_steaneEnc u st)
  rw [conjTranspose_mul, bitProj_conjTranspose] at h
  rw [h]
  split_ifs <;> simp

/-- **And one phase syndrome.** -/
theorem synCorr_mul_steaneEnc_conjTranspose_mul_phaseProj (st : SynPair) (u : Fin 3 → Fin 2) :
    (synCorr st * steaneEnc)ᴴ * phaseProj u
      = if u = st.2 then (synCorr st * steaneEnc)ᴴ else 0 := by
  have h := congrArg conjTranspose (phaseProj_mul_synCorr_mul_steaneEnc u st)
  rw [conjTranspose_mul, phaseProj_conjTranspose] at h
  rw [h]
  split_ifs <;> simp

/-! ### Single-type outputs -/

/-- **The syndrome spaces of the errors on qubit `q`**: no error, `X_q`, `Z_q`, `Y_q`. -/
def qubitSynProj (q : Fin 7) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (bitProj 0 + bitProj (syndrome (unitErr q))) * (phaseProj 0 + phaseProj (syndrome (unitErr q)))

theorem isSingleTypeOp_zero : IsSingleTypeOp 0 := fun _ _ => Matrix.mul_zero _

theorem IsSingleTypeOp.mul_right {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : IsSingleTypeOp K) (L : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    IsSingleTypeOp (K * L) := by
  intro st hst
  rw [← Matrix.mul_assoc, hK st hst, Matrix.zero_mul]

theorem IsSingleTypeOp.smul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : IsSingleTypeOp K) (c : ℂ) : IsSingleTypeOp (c • K) := by
  intro st hst
  rw [Matrix.mul_smul, hK st hst, smul_zero]

/-- An operator landing on bit syndrome `0` is single-type. -/
theorem isSingleTypeOp_of_bitProj_zero_mul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (h : bitProj 0 * K = K) : IsSingleTypeOp K := by
  intro st hst
  have h1 : ¬ (0 : Fin 3 → Fin 2) = st.1 := fun h => hst (Or.inl h.symm)
  rw [← h, ← Matrix.mul_assoc, synCorr_mul_steaneEnc_conjTranspose_mul_bitProj, ite_eq_right h1,
    Matrix.zero_mul]

/-- An operator landing on phase syndrome `0` is single-type. -/
theorem isSingleTypeOp_of_phaseProj_zero_mul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (h : phaseProj 0 * K = K) : IsSingleTypeOp K := by
  intro st hst
  have h2 : ¬ (0 : Fin 3 → Fin 2) = st.2 := fun h => hst (Or.inr (Or.inl h.symm))
  rw [← h, ← Matrix.mul_assoc, synCorr_mul_steaneEnc_conjTranspose_mul_phaseProj, ite_eq_right h2,
    Matrix.zero_mul]

/-- ★ **An operator landing in the syndrome spaces of one qubit is single-type.** -/
theorem isSingleTypeOp_of_qubitSynProj_mul {q : Fin 7}
    {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (h : qubitSynProj q * K = K) :
    IsSingleTypeOp K := by
  intro st hst
  have h1 : ¬ (0 : Fin 3 → Fin 2) = st.1 := fun h => hst (Or.inl h.symm)
  have h2 : ¬ (0 : Fin 3 → Fin 2) = st.2 := fun h => hst (Or.inr (Or.inl h.symm))
  have hB : (synCorr st * steaneEnc)ᴴ * (bitProj 0 + bitProj (syndrome (unitErr q)))
      = if syndrome (unitErr q) = st.1 then (synCorr st * steaneEnc)ᴴ else 0 := by
    rw [Matrix.mul_add, synCorr_mul_steaneEnc_conjTranspose_mul_bitProj,
      synCorr_mul_steaneEnc_conjTranspose_mul_bitProj, ite_eq_right h1, zero_add]
  have hP : (synCorr st * steaneEnc)ᴴ * (phaseProj 0 + phaseProj (syndrome (unitErr q)))
      = if syndrome (unitErr q) = st.2 then (synCorr st * steaneEnc)ᴴ else 0 := by
    rw [Matrix.mul_add, synCorr_mul_steaneEnc_conjTranspose_mul_phaseProj,
      synCorr_mul_steaneEnc_conjTranspose_mul_phaseProj, ite_eq_right h2, zero_add]
  rw [← h, qubitSynProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB]
  by_cases h3 : syndrome (unitErr q) = st.1
  · have h4 : ¬ syndrome (unitErr q) = st.2 := fun h4 => hst (Or.inr (Or.inr (h3.symm.trans h4)))
    rw [ite_eq_left h3, hP, ite_eq_right h4, Matrix.zero_mul]
  · rw [ite_eq_right h3, Matrix.zero_mul, Matrix.zero_mul]

/-- **One term of the faulty phase round lands in the syndrome spaces of qubit `q`**: the
correction for `v`, an operator on qubit `q`, and a readout of phase syndrome `v` or `v + h_q`, fed
bit syndrome `0`. -/
theorem qubitSynProj_mul_term (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) {v u : Fin 3 → Fin 2}
    (hu : u = v ∨ u = v + syndrome (unitErr q)) :
    qubitSynProj q * (pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0)
      = pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0 := by
  have hPv : phaseProj v + phaseProj (v + syndrome (unitErr q))
      = phaseProj u + phaseProj (u + syndrome (unitErr q)) := by
    rcases hu with rfl | rfl
    · rfl
    · rw [add_add_self, add_comm]
  have hP : (phaseProj 0 + phaseProj (syndrome (unitErr q))) * pauliMat 0 (decode v)
      = pauliMat 0 (decode v) * (phaseProj v + phaseProj (v + syndrome (unitErr q))) := by
    rw [Matrix.add_mul, phaseProj_mul_pauliMat_zero, phaseProj_mul_pauliMat_zero, syndrome_decode,
      zero_add, add_comm (syndrome (unitErr q)) v, Matrix.mul_add]
  have hB : (bitProj 0 + bitProj (syndrome (unitErr q))) * (gateOf q M * bitProj 0)
      = gateOf q M * bitProj 0 := by
    have h := gateOf_mul_bitProj q M 0
    rw [zero_add] at h
    exact h.symm
  have hBZ : (bitProj 0 + bitProj (syndrome (unitErr q))) * pauliMat 0 (decode v)
      = pauliMat 0 (decode v) * (bitProj 0 + bitProj (syndrome (unitErr q))) := by
    rw [Matrix.add_mul, bitProj_mul_pauliMat_zero, bitProj_mul_pauliMat_zero, Matrix.mul_add]
  have hPX : (phaseProj 0 + phaseProj (syndrome (unitErr q)))
      * (pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0)
      = pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0 := by
    rw [← Matrix.mul_assoc (phaseProj 0 + phaseProj (syndrome (unitErr q))),
      ← Matrix.mul_assoc (phaseProj 0 + phaseProj (syndrome (unitErr q))), hP,
      Matrix.mul_assoc (pauliMat 0 (decode v)), hPv, ← gateOf_mul_phaseProj]
  have hX : pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0
      = pauliMat 0 (decode v) * (gateOf q M * bitProj 0 * phaseProj u) := by
    rw [Matrix.mul_assoc (pauliMat 0 (decode v)), Matrix.mul_assoc (gateOf q M),
      ← bitProj_mul_phaseProj, ← Matrix.mul_assoc (gateOf q M)]
  have hBX : (bitProj 0 + bitProj (syndrome (unitErr q)))
      * (pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0)
      = pauliMat 0 (decode v) * (gateOf q M * phaseProj u) * bitProj 0 := by
    rw [hX, ← Matrix.mul_assoc (bitProj 0 + bitProj (syndrome (unitErr q))), hBZ,
      Matrix.mul_assoc (pauliMat 0 (decode v)),
      ← Matrix.mul_assoc (bitProj 0 + bitProj (syndrome (unitErr q))) (gateOf q M * bitProj 0), hB]
  rw [qubitSynProj, Matrix.mul_assoc (bitProj 0 + bitProj (syndrome (unitErr q))), hPX, hBX]

/-- Reading the ancilla after a product operator on data and ancilla. -/
theorem faultReadOp_kronecker (A B : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    faultReadOp (A ⊗ₖ B) m = ∑ m', B m m' • (A * steaneRead m') := by
  rw [faultReadOp, ancRead_mul_kronecker, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc A, Matrix.mul_assoc A]

theorem hadTransversal_conj_gateOf_mul_steaneRead (q : Fin 7) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (m : Fin 7 → Fin 2) :
    hadTransversal 7 * (gateOf q A * steaneRead m) * hadTransversal 7
      = (1 / 4 : ℂ) • (gateOf q (hGateM * A * hGateM) * phaseProj (syndrome m)) := by
  rw [steaneRead_eq, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, ← hadTransversal_conj_mul,
    hadTransversal_conj_gateOf, phaseProj]

/-- ★★ **The phase round with an operator on the pair `q`, fed bit syndrome `0`, lands in the
syndrome spaces of qubit `q`.** The readout is moved by the ancilla's error on `q`, the data by its
own error on `q`; after the correction both syndromes are `0` or `h_q`. -/
theorem qubitSynProj_mul_phaseFaultOp_mul_bitProj_zero {q : Fin 7} {G : PairOp} (hG : OnPair q G)
    (m : Fin 7 → Fin 2) :
    qubitSynProj q * (phaseFaultOp G m * bitProj 0) = phaseFaultOp G m * bitProj 0 := by
  obtain ⟨r, A, B, rfl⟩ := hG
  simp only [phaseFaultOp, faultReadOp_sum, faultReadOp_kronecker, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m' _ => ?_
  by_cases hag : ∀ i, i ≠ q → m i = m' i
  · congr 1
    have hu : syndrome m' = syndrome m ∨ syndrome m' = syndrome m + syndrome (unitErr q) := by
      rcases eq_or_eq_add_unitErr_of_agree hag with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h, syndrome_add])
    rw [hadTransversal_conj_gateOf_mul_steaneRead, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, qubitSynProj_mul_term q _ hu]
  · rw [gateOf_apply_of_not_agree hag, zero_smul, zero_smul]

/-- `X^a` commutes with a diagonal operator whose entries are invariant under the shift by `a`. -/
theorem pauliMat_mul_diagonal_comm {g : (Fin 7 → Fin 2) → ℂ} {a : Fin 7 → Fin 2}
    (hg : ∀ z, g (z + a) = g z) :
    pauliMat a 0 * Matrix.diagonal g = Matrix.diagonal g * pauliMat a 0 := by
  ext z w
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [pauliMat]
  by_cases h : w = z + a
  · subst h
    simp [hg, mul_comm]
  · simp [h]

/-- ★★ **The phase round with a periodic ancilla keeps bit syndrome `0`**: its readout is diagonal
with entries invariant under the Hamming code, so it commutes with every `X`-stabiliser, and in the
Hadamard basis with every `Z`-stabiliser. -/
theorem bitProj_zero_mul_ancPhaseOp_mul_bitProj_zero {f : (Fin 7 → Fin 2) → ℂ} (hf : IsPeriodic f)
    (m : Fin 7 → Fin 2) :
    bitProj 0 * (ancPhaseOp f m * bitProj 0) = ancPhaseOp f m * bitProj 0 := by
  have hd : ancReadOp f m = Matrix.diagonal fun z => f (m + z) := by
    rw [ancReadOp, ancRead_mul_extractMat_mul_ancPrep id_add_self]
    rfl
  have hX : ∀ c,
      pauliMat (rowComb c) 0 * ancReadOp f m = ancReadOp f m * pauliMat (rowComb c) 0 := by
    intro c
    rw [hd]
    refine pauliMat_mul_diagonal_comm fun z => ?_
    show f (m + (z + rowComb c)) = f (m + z)
    rw [← add_assoc, hf (m + z) _ (syndrome_rowComb c)]
  have hZ : ∀ c, pauliMat 0 (rowComb c) * (hadTransversal 7 * ancReadOp f m * hadTransversal 7)
      = hadTransversal 7 * ancReadOp f m * hadTransversal 7 * pauliMat 0 (rowComb c) := by
    intro c
    rw [← hadTransversal_conj_pauliMat_x (rowComb c), hadTransversal_conj_mul,
      hadTransversal_conj_mul, hX]
  have hc := bitProj_mul_of_commute hZ 0
  rw [ancPhaseOp, ← Matrix.mul_assoc (bitProj 0), ← Matrix.mul_assoc (bitProj 0),
    bitProj_mul_pauliMat_zero, Matrix.mul_assoc (pauliMat 0 _) (bitProj 0), hc]
  simp only [Matrix.mul_assoc, bitProj_mul_self]

theorem phaseProj_zero_mul_phaseRound (m : Fin 7 → Fin 2) :
    phaseProj 0 * phaseRound m = phaseRound m := by
  rw [phaseRound_eq, Matrix.mul_smul, ← Matrix.mul_assoc, phaseProj_mul_pauliMat_zero, zero_add,
    syndrome_decode, Matrix.mul_assoc, phaseProj_mul_self]

theorem bitProj_zero_mul_bitRound (m : Fin 7 → Fin 2) : bitProj 0 * bitRound m = bitRound m := by
  rw [bitRound_eq, Matrix.mul_smul, ← Matrix.mul_assoc, bitProj_mul_pauliMat, zero_add,
    syndrome_decode, Matrix.mul_assoc, bitProj_mul_self]

/-! ### Steane's method -/

variable {κ : Type}

/-- ★★★ **Every branch of Steane's method with its factories and one fault anywhere is
single-type, on every input.** A fault in the bit round: the fault-free phase round lands the
output on phase syndrome `0`. A fault in the phase round: the fault-free bit round hands it bit
syndrome `0`, and the fault is an operator on one pair (an extraction location), or leaves a good
ancilla (a factory location) — periodic, keeping bit syndrome `0`, or with an error on one qubit,
a pair operator before the `CNOT`. -/
theorem isSingleTypeOp_recKraus'_single {F : MethodRound → Fin 7 → κ → PairOp}
    {Φ : MethodRound → RetryFaults κ} [Fintype κ] (hOn : ∀ r q k, OnPair q (F r q k))
    (hΦ : ∀ r, (Φ r).Valid) (l : RecLoc) (i : RoundIdx κ × RoundIdx κ) :
    IsSingleTypeOp (recKraus' F Φ (fun l' => decide (l' = l)) i) := by
  obtain ⟨⟨⟨s₁, p₁⟩, m₁⟩, ⟨⟨s₂, p₂⟩, m₂⟩⟩ := i
  obtain ⟨r, x⟩ := l
  cases r with
  | bit =>
    obtain ⟨c, hc⟩ := roundOp_none (F := F .phase) (Φ .phase) (s₂, p₂)
    simp only [recKraus', Prod.mk.injEq, reduceCtorEq, false_and, decide_false]
    refine IsSingleTypeOp.mul_right (isSingleTypeOp_of_phaseProj_zero_mul ?_) _
    simp only [hc, Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (c • ·) (phaseProj_zero_mul_phaseRound m₂)
  | phase =>
    obtain ⟨c, hc⟩ := roundOp_none (F := F .bit) (Φ .bit) (s₁, p₁)
    simp only [recKraus', Prod.mk.injEq, reduceCtorEq, false_and, decide_false, true_and, hc]
    have hKb : pauliMat (decode (syndrome m₁)) 0 * (c • steaneRead m₁)
        = bitProj 0 * (pauliMat (decode (syndrome m₁)) 0 * (c • steaneRead m₁)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul]
      exact congrArg (c • ·) (bitProj_zero_mul_bitRound m₁).symm
    rw [hKb, ← Matrix.mul_assoc]
    refine IsSingleTypeOp.mul_right ?_ _
    rcases x with q | ℓ
    · simp only [roundOp, Sum.inl.injEq, reduceCtorEq, decide_false]
      obtain ⟨c₂, hc₂⟩ := retryOut_none (Φ .phase) p₂
      rw [hc₂, extractOp_smul, extractOp_plusAnc]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      exact (isSingleTypeOp_of_qubitSynProj_mul (qubitSynProj_mul_phaseFaultOp_mul_bitProj_zero
        (onPair_roundKraus_single (hOn .phase q) s₂) m₂)).smul c₂
    · simp only [roundOp, Sum.inr.injEq, reduceCtorEq, decide_false]
      have hg := goodAnc_retryOut_single (hΦ .phase) ℓ p₂
      rcases roundKraus_false_cases (F .phase) s₂ with h | h
      · rw [h, extractOp_one]
        rcases hg with hf | ⟨j, N, hf⟩
        · exact isSingleTypeOp_of_bitProj_zero_mul
            (bitProj_zero_mul_ancPhaseOp_mul_bitProj_zero hf m₂)
        · rw [hf, ancReadOp_gateOf]
          exact isSingleTypeOp_of_qubitSynProj_mul (qubitSynProj_mul_phaseFaultOp_mul_bitProj_zero
            ((onPair_one j).mul (onPair_one_kron_gateOf j N).conj_tCNOT) m₂)
      · rw [h, extractOp_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]
        exact isSingleTypeOp_zero

/-- ★★★ **#320's hypothesis holds for every noise model**: Steane's method with its factories and
one fault anywhere has single-type branches. -/
theorem RecNoise.singleTypeOut [Fintype κ] (N : RecNoise κ) : N.SingleTypeOut :=
  fun l i => isSingleTypeOp_recKraus'_single N.hOn N.hΦ l i

/-- ★★★ **Every rectangle with at most one fault is good after its leading recovery.** For each of
`H̄`, `X̄`, `Z̄`, `S`, `S†`, any trace-preserving fault family at the gadget locations, any noise in
either recovery, and any pattern with at most one fault among the `403` locations: on **every**
input, `D(T'(G'(T ρ))) = L D(T ρ) L†` (#316's `IsGoodAfter` with `D = steaneDecode`). -/
theorem steane_rect_isGoodAfter {γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) {ω : RectLoc → Bool} (hω : RectGood ω) :
    IsGoodAfter steaneDecode.apply G.logical.gate (N₁.run (leadPat ω))
      (G.faultyMap U (gadPat ω)) (N₂.run (trailPat ω)) :=
  steane_rect_isGoodAfter_of_singleTypeOut G hU N₁ N₂ N₁.singleTypeOut hω

end Steane
end QEC
end QM
end Empirical
end CSD

end
