/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneBadRectangle
public import CsdLean4.Mathlib.QuantumInfo.SyndromeDecoder

/-!
# Steane's decoder that keeps the syndrome

**Category:** 3-Local (Empirical, QM twin). BACKLOG #317 (split from #314; narrowed 2026-11-07).

`SyndromeDecoder.lean` (#316) inserts a decoder that keeps the syndrome between rectangles. This
file builds it at the Steane code and checks it against the decoder used so far.

## The decoder

* `synCorr st` — the correction `X^{decode s} Z^{decode t}` for the syndrome pair `st`;
* `steaneW` — **the unitary from seven qubits to the logical qubit and the six syndrome bits**: row
  `(a, st)` is the state `synCorr st · E |a⟩`, the logical state `a` with the error the syndrome
  `st` names;
* `phaseProj_zero_mul_steaneEnc`, `steaneEnc_conjTranspose_mul_pauliMat_mul_steaneEnc` — a Pauli
  with a nonzero syndrome has no matrix element between logical states;
* ★★ `synCorr_steaneEnc_orthonormal` — **the `128` states `synCorr st · E |a⟩` are orthonormal**;
* ★★ `steaneW_mul_conjTranspose`, ★★ `steaneW_conjTranspose_mul` — `steaneW` is unitary (the second
  from the first, `128 = 2 · 64`);
* `synDecode_steaneW` — `Tr_syn(W ρ W†) = ∑_st (synCorr st E)† ρ (synCorr st E)`;
* `recKraus_conjTranspose_mul_steaneEnc` — a branch of the recovery, read back on the code, is `±`
  the correction of its syndrome;
* ★★★ `steaneDecode_eq_synDecode` — **the decoder of #312 is `Tr_syn ∘ W` on every input**: the
  ideal decoder that discards the syndrome is the one that keeps it, traced.

## Transversal `S` and the decoder (the finding behind the narrowing)

* `sTransversal_conj_pauliMat` (`S X^a Z^b S† = i^{|a|} X^a Z^{b+a}`),
  `sTransversal_conj_pauliMat_unitErr` — `S` turns an `X` on qubit `q` into `i · X_q Z_q`;
* `steaneDecode_pauliMat_conj` — a Pauli-conjugated code operator decodes to the code operator
  conjugated by `E† C† P E`, `C` the correction of the Pauli's syndrome;
* ★★★ `exists_steaneDecode_sTransversal_ne` — **the transversal `S` does not commute with the ideal
  decoder on arbitrary inputs**: on `X₀ Z₁` applied to a code operator, `S` makes the error
  `X₀ Z₀ Z₁`, whose phase syndrome names qubit `2`, and the residual `Z₀ Z₁ Z₂` is a logical `Z̄`.
  So `D ∘ 𝒮 = 𝒮̄ ∘ D` holds on the inputs a recovery outputs (#312, #313) and **not** on every
  input; the level reduction uses the relative form `IsGoodAfter` (#316's amendment), and the
  analysis of a faulty recovery's output on arbitrary inputs is #320.

## Honest scope

⚠️ **The decoder only.** That a good rectangle is good after its leading recovery when that
recovery is faulty is #320.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, § 4;
`specs/BACKLOG.md` #317, #320, #316, #313, #312, #315; `Mathlib/QuantumInfo/SyndromeDecoder.lean`,
`Empirical/QM/QEC/SteaneBadRectangle.lean`, `Empirical/QM/QEC/SteaneCircuitRecovery.lean`,
`Empirical/QM/QEC/SteaneLogicalS.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
`specs/future-work.md`.
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

/-- The correction `X^{decode s} Z^{decode t}` the syndrome pair `st` calls for. -/
def synCorr (st : SynPair) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode st.1) (decode st.2)

/-- **The decoder that keeps the syndrome**: row `(a, st)` is the state `synCorr st · E |a⟩`. -/
def steaneW : Matrix (Fin 2 × SynPair) (Fin 7 → Fin 2) ℂ :=
  Matrix.of fun p z => star ((synCorr p.2 * steaneEnc) z p.1)

theorem steaneW_conjTranspose : steaneWᴴ = Matrix.of fun z (p : Fin 2 × SynPair) =>
    (synCorr p.2 * steaneEnc) z p.1 := by
  ext z p
  simp [steaneW, conjTranspose_apply]

/-- The phase projector of the zero syndrome fixes the logical states. -/
theorem phaseProj_zero_mul_steaneEnc : phaseProj 0 * steaneEnc = steaneEnc := by
  have h := phaseProj_mul_pauliMat_mul_steaneProj 0 0 0
  rw [pauliMat_zero, Matrix.mul_one, Matrix.one_mul, syndrome_zero, ite_eq_left rfl] at h
  rw [← steaneProj_mul_steaneEnc, ← Matrix.mul_assoc, h]

theorem steaneEnc_conjTranspose_mul_bitProj_zero : steaneEncᴴ * bitProj 0 = steaneEncᴴ := by
  have h := congrArg conjTranspose bitProj_zero_mul_steaneEnc
  rwa [conjTranspose_mul, bitProj_conjTranspose] at h

theorem steaneEnc_conjTranspose_mul_phaseProj_zero : steaneEncᴴ * phaseProj 0 = steaneEncᴴ := by
  have h := congrArg conjTranspose phaseProj_zero_mul_steaneEnc
  rwa [conjTranspose_mul, phaseProj_conjTranspose] at h

/-- **A Pauli with a nonzero syndrome has no matrix element between logical states.** -/
theorem steaneEnc_conjTranspose_mul_pauliMat_mul_steaneEnc {a b : Fin 7 → Fin 2}
    (h : syndrome a ≠ 0 ∨ syndrome b ≠ 0) : steaneEncᴴ * pauliMat a b * steaneEnc = 0 := by
  rcases h with h | h
  · calc steaneEncᴴ * pauliMat a b * steaneEnc
        = (steaneEncᴴ * bitProj 0) * pauliMat a b * (steaneProj * steaneEnc) := by
          rw [steaneEnc_conjTranspose_mul_bitProj_zero, steaneProj_mul_steaneEnc]
      _ = steaneEncᴴ * (bitProj 0 * pauliMat a b * steaneProj) * steaneEnc := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [bitProj_mul_pauliMat_mul_steaneProj, ite_eq_right (Ne.symm h), Matrix.mul_zero,
            Matrix.zero_mul]
  · calc steaneEncᴴ * pauliMat a b * steaneEnc
        = (steaneEncᴴ * phaseProj 0) * pauliMat a b * (steaneProj * steaneEnc) := by
          rw [steaneEnc_conjTranspose_mul_phaseProj_zero, steaneProj_mul_steaneEnc]
      _ = steaneEncᴴ * (phaseProj 0 * pauliMat a b * steaneProj) * steaneEnc := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [phaseProj_mul_pauliMat_mul_steaneProj, ite_eq_right (Ne.symm h), Matrix.mul_zero,
            Matrix.zero_mul]

/-- ★★ **The `128` states `synCorr st · E |a⟩` are orthonormal**: `(C E)† (C' E)` is `1` for equal
syndrome pairs and `0` otherwise. -/
theorem synCorr_steaneEnc_orthonormal (st st' : SynPair) :
    (synCorr st * steaneEnc)ᴴ * (synCorr st' * steaneEnc) = if st = st' then 1 else 0 := by
  rw [conjTranspose_mul]
  by_cases h : st = st'
  · subst h
    rw [ite_eq_left rfl]
    calc steaneEncᴴ * (synCorr st)ᴴ * (synCorr st * steaneEnc)
        = steaneEncᴴ * ((synCorr st)ᴴ * synCorr st) * steaneEnc := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [synCorr, pauliMat_conjTranspose_mul_self, Matrix.mul_one, steaneEnc_conjTranspose_mul]
  · rw [ite_eq_right h]
    obtain ⟨s, t⟩ := st
    obtain ⟨s', t'⟩ := st'
    have hne : syndrome (decode s + decode s') ≠ 0 ∨ syndrome (decode t + decode t') ≠ 0 := by
      rw [syndrome_add, syndrome_add, syndrome_decode, syndrome_decode, syndrome_decode,
        syndrome_decode]
      by_contra hc
      push Not at hc
      exact h (Prod.ext (synVec_add_eq_zero_iff.1 hc.1) (synVec_add_eq_zero_iff.1 hc.2))
    calc steaneEncᴴ * (synCorr (s, t))ᴴ * (synCorr (s', t') * steaneEnc)
        = steaneEncᴴ * ((synCorr (s, t))ᴴ * synCorr (s', t')) * steaneEnc := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          simp only [synCorr]
          rw [pauliMat_conjTranspose, Matrix.smul_mul, pauliMat_mul, smul_smul, Matrix.mul_smul,
            Matrix.smul_mul, steaneEnc_conjTranspose_mul_pauliMat_mul_steaneEnc hne, smul_zero]

/-- ★★ **The decoder that keeps the syndrome is unitary**: `W W† = 1`. -/
theorem steaneW_mul_conjTranspose : steaneW * steaneWᴴ = 1 := by
  ext ⟨a, st⟩ ⟨b, st'⟩
  have h := congrFun (congrFun (synCorr_steaneEnc_orthonormal st st') a) b
  rw [Matrix.mul_apply] at h
  rw [Matrix.mul_apply, steaneW_conjTranspose]
  simp only [steaneW, Matrix.of_apply, conjTranspose_apply] at h ⊢
  rw [h, Matrix.one_apply]
  by_cases hst : st = st'
  · subst hst
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  · simp [hst]

/-- ★★ **`W† W = 1`**: the other half, since both registers have `128` states. -/
theorem steaneW_conjTranspose_mul : steaneWᴴ * steaneW = 1 :=
  (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by
    simp [Fintype.card_prod]))).1 steaneW_mul_conjTranspose

/-- The decoder through `W`, as a sum over the syndrome pairs. -/
theorem synDecode_steaneW (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    synDecode steaneW ρ
      = ∑ st : SynPair, (synCorr st * steaneEnc)ᴴ * ρ * (synCorr st * steaneEnc) := by
  ext a b
  simp only [synDecode, partialTraceRight_apply, Matrix.sum_apply, Matrix.mul_apply, steaneW,
    Matrix.of_apply, conjTranspose_apply, star_star]

/-- **A branch of the recovery, read back on the code, is `±` the correction of its syndrome**:
`K_st† E = ± synCorr st · E`. -/
theorem recKraus_conjTranspose_mul_steaneEnc (st : SynPair) :
    (recKraus st)ᴴ * steaneEnc
      = pauliSign (decode st.2) (decode st.1) • (synCorr st * steaneEnc) := by
  obtain ⟨s, t⟩ := st
  have hb : bitProj s * synCorr (s, t) * steaneEnc = synCorr (s, t) * steaneEnc := by
    rw [← steaneProj_mul_steaneEnc]
    calc bitProj s * synCorr (s, t) * (steaneProj * steaneEnc)
        = (bitProj s * synCorr (s, t) * steaneProj) * steaneEnc := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [synCorr, bitProj_mul_pauliMat_mul_steaneProj, syndrome_decode, ite_eq_left rfl,
            Matrix.mul_assoc]
  have hp : phaseProj t * synCorr (s, t) * steaneEnc = synCorr (s, t) * steaneEnc := by
    rw [← steaneProj_mul_steaneEnc]
    calc phaseProj t * synCorr (s, t) * (steaneProj * steaneEnc)
        = (phaseProj t * synCorr (s, t) * steaneProj) * steaneEnc := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [synCorr, phaseProj_mul_pauliMat_mul_steaneProj, syndrome_decode, ite_eq_left rfl,
            Matrix.mul_assoc]
  rw [recKraus_eq, conjTranspose_mul, conjTranspose_mul, bitProj_conjTranspose,
    phaseProj_conjTranspose, pauliMat_conjTranspose]
  change bitProj s * (phaseProj t * (pauliSign (decode t) (decode s) • synCorr (s, t)))
    * steaneEnc = _
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc bitProj s * (phaseProj t * synCorr (s, t)) * steaneEnc
      = bitProj s * (phaseProj t * synCorr (s, t) * steaneEnc) := by simp only [Matrix.mul_assoc]
    _ = synCorr (s, t) * steaneEnc := by rw [hp, ← Matrix.mul_assoc, hb]

/-- ★★★ **The decoder of #312 is `Tr_syn ∘ W` on every input**: discarding the syndrome after the
recovery is keeping it and tracing it out. -/
theorem steaneDecode_eq_synDecode (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply ρ = synDecode steaneW ρ := by
  rw [steaneDecode_apply, synDecode_steaneW, methodRecovery_apply, Channel.apply_def,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun st _ => ?_
  change steaneEncᴴ * (recKraus st * ρ * (recKraus st)ᴴ) * steaneEnc = _
  have h := recKraus_conjTranspose_mul_steaneEnc st
  have h' : steaneEncᴴ * recKraus st
      = star (pauliSign (decode st.2) (decode st.1)) • (synCorr st * steaneEnc)ᴴ := by
    have := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul] at this
  have hσ : star (pauliSign (decode st.2) (decode st.1)) * pauliSign (decode st.2) (decode st.1)
      = 1 := by
    rw [show star (pauliSign (decode st.2) (decode st.1))
        = (starRingEnd ℂ) (pauliSign (decode st.2) (decode st.1)) from rfl, conj_pauliSign,
      pauliSign_mul_self]
  calc steaneEncᴴ * (recKraus st * ρ * (recKraus st)ᴴ) * steaneEnc
      = (steaneEncᴴ * recKraus st) * ρ * ((recKraus st)ᴴ * steaneEnc) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h, h', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσ, one_smul]

/-! ### Transversal `S` and the decoder -/

theorem sGateM_apply_eq_ite (i j : Fin 2) :
    sGateM i j = if i = j then (if i = 1 then Complex.I else 1) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [sGateM]

/-- `S` on one qubit carries `X^u Z^v` to `i^u X^u Z^{v + u}`. -/
theorem sGateM_conj_onePauli (u v : Fin 2) :
    sGateM * onePauli u v * sGateMᴴ = (if u = 1 then Complex.I else 1) • onePauli u (v + u) := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, sGateM_apply_eq_ite, onePauli_apply,
    Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;>
    simp [signChar]

/-- **The transversal `S` on a Pauli string**: `S X^a Z^b S† = i^{|a|} X^a Z^{b + a}`. -/
theorem sTransversal_conj_pauliMat (a b : Fin 7 → Fin 2) :
    sTransversal * pauliMat a b * sTransversalᴴ
      = (∏ i, if a i = 1 then Complex.I else 1) • pauliMat a (b + a) := by
  rw [pauliMat_eq_blockKron, sTransversal, blockKron_conjTranspose, blockKron_mul, blockKron_mul,
    show (fun i => sGateM * onePauli (a i) (b i) * sGateMᴴ)
        = fun i => (if a i = 1 then Complex.I else 1) • onePauli (a i) (b i + a i) from
      funext fun i => sGateM_conj_onePauli (a i) (b i),
    blockKron_smul, pauliMat_eq_blockKron]
  rfl

/-- **`S` turns an `X` on qubit `q` into `i · X_q Z_q`**, the rest of the string unchanged. -/
theorem sTransversal_conj_pauliMat_unitErr (q : Fin 7) (b : Fin 7 → Fin 2) :
    sTransversal * pauliMat (unitErr q) b * sTransversalᴴ
      = Complex.I • pauliMat (unitErr q) (b + unitErr q) := by
  rw [sTransversal_conj_pauliMat, Finset.prod_eq_single q]
  · simp [unitErr]
  · intro i _ hi
    simp [unitErr, hi]
  · simp

/-- **A Pauli-conjugated code operator decodes to the code operator conjugated by
`N = E† C† Q E`**, `C` the correction of the Pauli's syndrome: every other syndrome pair gives
`0`. -/
theorem steaneDecode_pauliMat_conj (a b : Fin 7 → Fin 2) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    steaneDecode.apply (pauliMat a b * (steaneEnc * X * steaneEncᴴ) * (pauliMat a b)ᴴ)
      = (steaneEncᴴ * (synCorr (syndrome a, syndrome b))ᴴ * pauliMat a b * steaneEnc) * X
        * (steaneEncᴴ * (synCorr (syndrome a, syndrome b))ᴴ * pauliMat a b * steaneEnc)ᴴ := by
  have hterm : ∀ st, (synCorr st * steaneEnc)ᴴ
        * (pauliMat a b * (steaneEnc * X * steaneEncᴴ) * (pauliMat a b)ᴴ) * (synCorr st * steaneEnc)
      = (steaneEncᴴ * (synCorr st)ᴴ * pauliMat a b * steaneEnc) * X
        * (steaneEncᴴ * (synCorr st)ᴴ * pauliMat a b * steaneEnc)ᴴ := by
    intro st
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hzero : ∀ st, st ≠ (syndrome a, syndrome b) →
      steaneEncᴴ * (synCorr st)ᴴ * pauliMat a b * steaneEnc = 0 := by
    rintro ⟨s, t⟩ hst
    have hne : syndrome (decode s + a) ≠ 0 ∨ syndrome (decode t + b) ≠ 0 := by
      rw [syndrome_add, syndrome_add, syndrome_decode, syndrome_decode]
      by_contra hc
      push Not at hc
      exact hst (Prod.ext (synVec_add_eq_zero_iff.1 hc.1) (synVec_add_eq_zero_iff.1 hc.2))
    rw [synCorr, pauliMat_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_assoc (steaneEncᴴ) (pauliMat _ _), pauliMat_mul, Matrix.mul_smul,
      Matrix.smul_mul, steaneEnc_conjTranspose_mul_pauliMat_mul_steaneEnc hne, smul_zero,
      smul_zero]
  rw [steaneDecode_eq_synDecode, synDecode_steaneW, Finset.sum_eq_single (syndrome a, syndrome b)]
  · exact hterm _
  · intro st _ hst
    rw [hterm, hzero st hst, Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A `Z`-stabiliser fixes the logical states. -/
theorem pauliMat_zero_rowComb_mul_steaneEnc (c : Fin 3 → Fin 2) :
    pauliMat 0 (rowComb c) * steaneEnc = steaneEnc := by
  rw [← bitProj_zero_mul_steaneEnc, ← Matrix.mul_assoc, pauliMat_zero_mul_bitProj, bdot_zero_right,
    signChar_zero, one_smul]

/-- **A logical `Z̄` times a `Z`-stabiliser reads `Z` on the decoded qubit.** -/
theorem steaneEnc_conjTranspose_mul_logicalZ_stab (c : Fin 3 → Fin 2) :
    steaneEncᴴ * pauliMat 0 (allOnes + rowComb c) * steaneEnc = pZ := by
  have hsplit : pauliMat 0 (allOnes + rowComb c) = pauliMat 0 allOnes * pauliMat 0 (rowComb c) := by
    rw [pauliMat_mul, add_zero, pauliSign, bdot_zero_right, signChar_zero, one_smul]
  rw [hsplit, Matrix.mul_assoc, Matrix.mul_assoc, pauliMat_zero_rowComb_mul_steaneEnc,
    logicalZ_mul_steaneEnc, ← Matrix.mul_assoc, steaneEnc_conjTranspose_mul, Matrix.one_mul]

/-- The density operator of `|+⟩`. -/
def plusDensity : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]]

/-- ★★★ **The transversal `S` does not commute with the ideal decoder on arbitrary inputs.** For
`ρ = X₀ Z₁ (E |+⟩⟨+| E†) Z₁ X₀` — the encoded `|+⟩` with an `X` on qubit `0` and a `Z` on qubit `1`,
a correctable error — `D(ρ) = |+⟩⟨+|`, but `S ρ S†` carries the error `X₀ Z₀ Z₁`, whose phase
syndrome names qubit `2`; the residual `Z₀ Z₁ Z₂` is a logical `Z̄`, so
`D(S ρ S†) = Z S† |+⟩⟨+| S Z`, not `S† |+⟩⟨+| S`. -/
theorem exists_steaneDecode_sTransversal_ne :
    ∃ ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ,
      steaneDecode.apply (sTransversal * ρ * sTransversalᴴ)
        ≠ sDagM * steaneDecode.apply ρ * sDagMᴴ := by
  refine ⟨pauliMat (unitErr 0) (unitErr 1) * (steaneEnc * plusDensity * steaneEncᴴ)
    * (pauliMat (unitErr 0) (unitErr 1))ᴴ, ?_⟩
  -- the decoded input
  have hD : steaneDecode.apply (pauliMat (unitErr 0) (unitErr 1)
      * (steaneEnc * plusDensity * steaneEncᴴ) * (pauliMat (unitErr 0) (unitErr 1))ᴴ)
      = plusDensity := by
    rw [steaneDecode_pauliMat_conj, synCorr, decode_syndrome_unitErr, decode_syndrome_unitErr]
    have h1 : steaneEncᴴ * (pauliMat (unitErr 0) (unitErr 1))ᴴ * pauliMat (unitErr 0) (unitErr 1)
        * steaneEnc = 1 := by
      rw [Matrix.mul_assoc (steaneEncᴴ), pauliMat_conjTranspose_mul_self, Matrix.mul_one,
        steaneEnc_conjTranspose_mul]
    rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  -- the conjugated input: `S Q S† = i Q'` and `S E = E S†`
  set Q' := pauliMat (unitErr 0) (unitErr 1 + unitErr 0) with hQ'def
  have hSQ := sTransversal_conj_pauliMat_unitErr 0 (unitErr 1)
  have hSS : sTransversalᴴ * sTransversal = 1 := sTransversal_conjTranspose_mul
  have hSE : sTransversal * steaneEnc = steaneEnc * sDagM := sTransversal_mul_steaneEnc
  have hSE' : steaneEncᴴ * sTransversalᴴ = sDagMᴴ * steaneEncᴴ := by
    have := congrArg conjTranspose hSE
    rwa [conjTranspose_mul, conjTranspose_mul] at this
  have hQ : sTransversal * pauliMat (unitErr 0) (unitErr 1)
      = (Complex.I • Q') * sTransversal := by
    calc sTransversal * pauliMat (unitErr 0) (unitErr 1)
        = (sTransversal * pauliMat (unitErr 0) (unitErr 1) * sTransversalᴴ) * sTransversal := by
          rw [Matrix.mul_assoc _ sTransversalᴴ, hSS, Matrix.mul_one]
      _ = _ := by rw [hSQ]
  have hQc : (pauliMat (unitErr 0) (unitErr 1))ᴴ * sTransversalᴴ
      = sTransversalᴴ * (Complex.I • Q')ᴴ := by
    have := congrArg conjTranspose hQ
    rwa [conjTranspose_mul, conjTranspose_mul] at this
  have hII : star Complex.I * Complex.I = 1 := by simp
  have hconj : sTransversal * (pauliMat (unitErr 0) (unitErr 1)
      * (steaneEnc * plusDensity * steaneEncᴴ) * (pauliMat (unitErr 0) (unitErr 1))ᴴ)
      * sTransversalᴴ
      = Q' * (steaneEnc * (sDagM * plusDensity * sDagMᴴ) * steaneEncᴴ) * Q'ᴴ := by
    calc sTransversal * (pauliMat (unitErr 0) (unitErr 1)
          * (steaneEnc * plusDensity * steaneEncᴴ) * (pauliMat (unitErr 0) (unitErr 1))ᴴ)
          * sTransversalᴴ
        = (sTransversal * pauliMat (unitErr 0) (unitErr 1)) * steaneEnc * plusDensity
          * steaneEncᴴ * ((pauliMat (unitErr 0) (unitErr 1))ᴴ * sTransversalᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (Complex.I • Q') * (sTransversal * steaneEnc) * plusDensity
          * (steaneEncᴴ * sTransversalᴴ) * (Complex.I • Q')ᴴ := by
          rw [hQ, hQc]; simp only [Matrix.mul_assoc]
      _ = (star Complex.I * Complex.I) • (Q' * (steaneEnc * sDagM) * plusDensity
          * (sDagMᴴ * steaneEncᴴ) * Q'ᴴ) := by
          rw [hSE, hSE', conjTranspose_smul]
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = _ := by rw [hII, one_smul]; simp only [Matrix.mul_assoc]
  -- the decoded output: the correction leaves `Z₀ Z₁ Z₂ = Z̄ · (Z-stabiliser)`
  have hsyn : syndrome (unitErr 1 + unitErr 0) = syndrome (unitErr 2) := by decide
  have hw : unitErr 2 + (unitErr 1 + unitErr 0) = allOnes + rowComb ![0, 0, 1] := by decide
  have h00 : unitErr (0 : Fin 7) + unitErr 0 = 0 := by decide
  have hN : steaneEncᴴ * (synCorr (syndrome (unitErr 0), syndrome (unitErr 1 + unitErr 0)))ᴴ
      * Q' * steaneEnc = pZ := by
    rw [hsyn, synCorr, decode_syndrome_unitErr, decode_syndrome_unitErr, pauliMat_conjTranspose,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc (steaneEncᴴ), hQ'def,
      pauliMat_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h00, hw,
      steaneEnc_conjTranspose_mul_logicalZ_stab]
    have h1 : pauliSign (unitErr 2) (unitErr (0 : Fin 7)) = 1 := by
      rw [pauliSign, show bdot (unitErr 2) (unitErr (0 : Fin 7)) = 0 by decide, signChar_zero]
    rw [h1, one_mul, one_smul]
  have hDS : steaneDecode.apply (sTransversal * (pauliMat (unitErr 0) (unitErr 1)
      * (steaneEnc * plusDensity * steaneEncᴴ) * (pauliMat (unitErr 0) (unitErr 1))ᴴ)
      * sTransversalᴴ) = pZ * (sDagM * plusDensity * sDagMᴴ) * pZᴴ := by
    rw [hconj, hQ'def, steaneDecode_pauliMat_conj, ← hQ'def, hN]
  rw [hDS, hD]
  intro h
  have hs : ∀ i j : Fin 2, sDagM i j = if i = j then (if i = 1 then -Complex.I else 1) else 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [sDagM]
  have hz : ∀ i j : Fin 2, pZ i j = if i = j then (if i = 1 then -1 else 1) else 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [pZ]
  have hp : ∀ i j : Fin 2, plusDensity i j = 1 / 2 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [plusDensity]
  have h01 := congrFun (congrFun h 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, hs, hz, hp] at h01
  norm_num [Complex.ext_iff] at h01

end Steane
end QEC
end QM
end Empirical
end CSD

end
