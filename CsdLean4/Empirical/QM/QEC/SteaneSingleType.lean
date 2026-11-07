/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneSyndromeDecoder

/-!
# The decoder commutes with the gates on single-type syndromes

**Category:** 3-Local (Empirical, QM twin). BACKLOG #320 (split from #317; narrowed 2026-11-07).

#317 found that the transversal `S` does not commute with the ideal decoder on every input: the
input `X₀ Z₁ ψ` has the syndrome pair of an `X` on one qubit and a `Z` on another, and `S` turns the
decoder's correction into a logical error. This file proves the condition under which every gate of
the set does commute with the decoder.

## Single-type syndromes

A syndrome pair `(s, t)` is **single-type** when `s = 0`, `t = 0` or `s = t` — the syndromes of
`X_q`, `Z_q` and `Y_q`. On those the corrections add: `decode s + decode t = decode (s + t)`
(`decode_add_decode_of_singleType`), which is exactly what the transversal `S` needs.

* `SingleType`, `IsSingleTypeOp K` — every row `(C_st E)†` of #317's decoder `W` with `st` not
  single-type annihilates `K`: the output of `K` lies in the single-type syndrome spaces;
* ★ `isSingleTypeOp_of_steaneProj_mul` — **an operator landing in the code is single-type**; with
  ~~#313~~'s `steaneProj_mul_recKraus`, every branch of the fault-free recovery is
  (`isSingleTypeOp_recKraus`);
* `sum_synCorr_steaneEnc_mul_conjTranspose` — `∑_st (C_st E)(C_st E)† = 1`, `W† W = 1` in blocks.

## The gates on the syndromes

* `ConcatGadget.synPerm` — the action on syndrome pairs: `H̄` swaps them, `X̄`, `Z̄` fix them, `S`
  and `S†` send `(s, t)` to `(s, s + t)`; an involution (`synPerm_synPerm`);
* ★★ `ConcatGadget.exists_conj_synCorr` — **on a single-type pair each gate carries the correction
  to the correction of the image pair, up to a phase**: `g C_st g† = ω C_{π st}`;
* `ConcatGadget.exists_unit_blockKron_mul_steaneEnc` — `g E = E (c L)` with `|c| = 1`;
* ★★★ `ConcatGadget.steaneDecode_conj_of_isSingleTypeOp` — **`D(g K ρ K† g†) = L D(K ρ K†) L†` for
  every single-type `K` and every `ρ`**; ★★★ `ConcatGadget.steaneDecode_conj_channel` — the same for
  a channel all of whose branches are single-type.

## The rectangle in the relative form

* `RecNoise.SingleTypeOut` — **the hypothesis**: Steane's method with its factories and one fault
  anywhere has single-type branches (BACKLOG #321);
* ★★★ `steane_rect_isGoodAfter` — **for each of `H̄`, `X̄`, `Z̄`, `S`, `S†`, every rectangle with at
  most one fault among its `403` locations is good after its leading recovery** (#316's
  `IsGoodAfter`, `D = steaneDecode`), on **every** input, given `SingleTypeOut` for the leading
  recovery's noise. A fault-free leading recovery needs nothing (~~#313~~); a faulty one hands on a
  single-type output, which the ideal gadget and trailing recovery carry to its decoded image.

## Honest scope

⚠️ **`SingleTypeOut` is a hypothesis here**, discharged by #321 (the output side of Steane's method
with one fault: pair channels at the extraction locations, both kinds of good ancilla, the retry).

⚠️ **One block, one rectangle.** Joining the rectangles of #233's machine into
`one_sub_le_measure_decode_recRun` is #319.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, § 4;
`specs/BACKLOG.md` #320, #321, #317, #316, #319, #315;
`Empirical/QM/QEC/SteaneSyndromeDecoder.lean`, `Empirical/QM/QEC/SteaneBadRectangle.lean`,
`Empirical/QM/QEC/SteaneRectangle.lean`,
`Mathlib/QuantumInfo/SyndromeDecoder.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
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

/-! ### Single-type syndromes -/

/-- **A single-type syndrome pair**: that of an `X`, a `Z` or a `Y` on one qubit (or none). -/
def SingleType (st : SynPair) : Prop := st.1 = 0 ∨ st.2 = 0 ∨ st.1 = st.2

instance (st : SynPair) : Decidable (SingleType st) := by unfold SingleType; infer_instance

/-- On a single-type pair the corrections add. -/
theorem decode_add_decode_of_singleType {st : SynPair} (h : SingleType st) :
    decode st.2 + decode st.1 = decode (st.1 + st.2) := by
  obtain ⟨s, t⟩ := st
  rcases h with h | h | h
  · simp only at h; subst h; rw [decode_zero, add_zero, zero_add]
  · simp only at h; subst h; rw [decode_zero, zero_add, add_zero]
  · simp only at h; subst h
    rw [show s + s = 0 from synVec_add_eq_zero_iff.2 rfl, decode_zero]
    funext q; exact fin2_add_self _

/-- **A single-type operator**: its output lies in the single-type syndrome spaces. -/
def IsSingleTypeOp (K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Prop :=
  ∀ st, ¬ SingleType st → (synCorr st * steaneEnc)ᴴ * K = 0

/-- ★ **An operator landing in the code is single-type.** -/
theorem isSingleTypeOp_of_steaneProj_mul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (h : steaneProj * K = K) : IsSingleTypeOp K := by
  intro st hst
  have hne : st ≠ ((0 : Fin 3 → Fin 2), (0 : Fin 3 → Fin 2)) := by
    rintro rfl; exact hst (Or.inl rfl)
  have h0 : (synCorr st * steaneEnc)ᴴ * (synCorr (0, 0) * steaneEnc) = 0 := by
    rw [synCorr_steaneEnc_orthonormal, ite_eq_right hne]
  have hC : synCorr ((0 : Fin 3 → Fin 2), (0 : Fin 3 → Fin 2)) = 1 := by
    rw [synCorr, decode_zero, pauliMat_zero]
  rw [hC, Matrix.one_mul] at h0
  rw [← h, steaneProj_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
    Matrix.zero_mul]

/-- Every branch of the fault-free recovery is single-type. -/
theorem isSingleTypeOp_recKraus (st : SynPair) : IsSingleTypeOp (recKraus st) :=
  isSingleTypeOp_of_steaneProj_mul (steaneProj_mul_recKraus st)

/-- `W† W = 1` in blocks: `∑_st (C_st E)(C_st E)† = 1`. -/
theorem sum_synCorr_steaneEnc_mul_conjTranspose :
    ∑ st : SynPair, (synCorr st * steaneEnc) * (synCorr st * steaneEnc)ᴴ = 1 := by
  rw [← steaneW_conjTranspose_mul]
  ext z w
  rw [Matrix.sum_apply]
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext st; rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun st _ => ?_
  simp [steaneW, conjTranspose_apply]

/-- The decoder in blocks, on every input. -/
theorem steaneDecode_apply_eq_sum (Y : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply Y
      = ∑ st : SynPair, (synCorr st * steaneEnc)ᴴ * Y * (synCorr st * steaneEnc) := by
  rw [steaneDecode_eq_synDecode, synDecode_steaneW]

/-! ### The gates on the syndromes -/

namespace ConcatGadget

/-- **The action of a gate on syndrome pairs**: `H̄` swaps the two syndromes, `X̄` and `Z̄` fix
them, `S` and `S†` send `(s, t)` to `(s, s + t)`. -/
def synPerm : ConcatGadget → SynPair → SynPair
  | of .had, st => (st.2, st.1)
  | of .x, st => st
  | of .z, st => st
  | s, st => (st.1, st.1 + st.2)
  | sDag, st => (st.1, st.1 + st.2)

theorem synPerm_synPerm (G : ConcatGadget) (st : SynPair) : G.synPerm (G.synPerm st) = st := by
  obtain ⟨a, b⟩ := st
  cases G with
  | of G => cases G <;> rfl
  | s =>
    show ((a, a + (a + b)) : SynPair) = (a, b)
    rw [← add_assoc, synVec_add_eq_zero_iff.2 rfl, zero_add]
  | sDag =>
    show ((a, a + (a + b)) : SynPair) = (a, b)
    rw [← add_assoc, synVec_add_eq_zero_iff.2 rfl, zero_add]

theorem synPerm_injective (G : ConcatGadget) : Function.Injective G.synPerm := fun a b h => by
  rw [← G.synPerm_synPerm a, ← G.synPerm_synPerm b, h]

/-- A unit-modulus product of phases `i` and `1`. -/
theorem star_mul_self_prod_I (a : Fin 7 → Fin 2) :
    star (∏ i, if a i = 1 then Complex.I else 1) * (∏ i, if a i = 1 then Complex.I else 1) = 1 := by
  rw [show star (∏ i, if a i = 1 then Complex.I else 1)
      = ∏ i, star (if a i = 1 then Complex.I else 1) from map_prod (starRingEnd ℂ) _ _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> simp

theorem star_mul_self_signChar (u : Fin 2) : star (signChar u) * signChar u = 1 := by
  rw [show star (signChar u) = (starRingEnd ℂ) (signChar u) from rfl, conj_signChar,
    signChar_mul_self]

/-- ★★ **On a single-type pair each gate carries the correction to the correction of the image
pair, up to a phase**: `g C_st g† = ω C_{π st}`. For `S` the phase is `i^{|decode s|}` and the
identity is exact because `decode s + decode t = decode (s + t)`. -/
theorem exists_conj_synCorr (G : ConcatGadget) (st : SynPair) :
    ∃ ω : ℂ, star ω * ω = 1 ∧ (SingleType st →
      blockKron (fun _ : Fin 7 => G.gate) * synCorr st * (blockKron fun _ : Fin 7 => G.gate)ᴴ
        = ω • synCorr (G.synPerm st)) := by
  obtain ⟨s, t⟩ := st
  cases G with
  | of G =>
    cases G with
    | had =>
      refine ⟨signChar (bdot (decode s) (decode t)), star_mul_self_signChar _, fun _ => ?_⟩
      show hadTransversal 7 * pauliMat (decode s) (decode t) * (hadTransversal 7)ᴴ = _
      rw [hadTransversal_conjTranspose, hadTransversal_conj_pauliMat]
      rfl
    | x =>
      refine ⟨signChar (bdot allOnes (decode t) + bdot 0 (decode s)),
        star_mul_self_signChar _, fun _ => ?_⟩
      show blockKron (fun _ : Fin 7 => pX) * pauliMat (decode s) (decode t)
        * (blockKron fun _ : Fin 7 => pX)ᴴ = _
      rw [blockKron_pX_eq_pauliMat, pauliMat_conj]
      rfl
    | z =>
      refine ⟨signChar (bdot 0 (decode t) + bdot allOnes (decode s)),
        star_mul_self_signChar _, fun _ => ?_⟩
      show blockKron (fun _ : Fin 7 => pZ) * pauliMat (decode s) (decode t)
        * (blockKron fun _ : Fin 7 => pZ)ᴴ = _
      rw [blockKron_pZ_eq_pauliMat, pauliMat_conj]
      rfl
  | s =>
    refine ⟨∏ i, if decode s i = 1 then Complex.I else 1, star_mul_self_prod_I _, fun h => ?_⟩
    show sTransversal * pauliMat (decode s) (decode t) * sTransversalᴴ = _
    rw [sTransversal_conj_pauliMat, decode_add_decode_of_singleType h]
    rfl
  | sDag =>
    refine ⟨star (∏ i, if decode s i = 1 then Complex.I else 1), ?_, fun h => ?_⟩
    · rw [star_star, mul_comm]; exact star_mul_self_prod_I _
    · have hst' : SingleType (s, s + t) := by
        unfold SingleType at h ⊢
        simp only at h ⊢
        rcases h with h | h | h
        · exact Or.inl h
        · right; right; rw [h, add_zero]
        · right; left; rw [h]; exact synVec_add_eq_zero_iff.2 rfl
      have hS := sTransversal_conj_pauliMat (decode s) (decode (s + t))
      rw [decode_add_decode_of_singleType hst',
        show ((s, s + t) : SynPair).1 + ((s, s + t) : SynPair).2 = t by
          show s + (s + t) = t
          rw [← add_assoc, synVec_add_eq_zero_iff.2 rfl, zero_add]] at hS
      have hg : blockKron (fun _ : Fin 7 => sDagM) = sTransversalᴴ := by
        rw [sTransversal, blockKron_conjTranspose, sGateM_conjTranspose]
      show blockKron (fun _ : Fin 7 => sDagM) * pauliMat (decode s) (decode t)
        * (blockKron fun _ : Fin 7 => sDagM)ᴴ = _
      rw [hg, conjTranspose_conjTranspose]
      set ω := ∏ i, if decode s i = 1 then Complex.I else 1
      have hω : star ω * ω = 1 := star_mul_self_prod_I _
      have hSS : sTransversalᴴ * sTransversal = 1 := sTransversal_conjTranspose_mul
      have hSS' : sTransversal * sTransversalᴴ = 1 := mul_eq_one_comm.1 hSS
      show sTransversalᴴ * pauliMat (decode s) (decode t) * sTransversal
        = star ω • pauliMat (decode s) (decode (s + t))
      calc sTransversalᴴ * pauliMat (decode s) (decode t) * sTransversal
          = sTransversalᴴ * ((star ω * ω) • pauliMat (decode s) (decode t)) * sTransversal := by
            rw [hω, one_smul]
        _ = star ω • (sTransversalᴴ * (ω • pauliMat (decode s) (decode t)) * sTransversal) := by
            rw [← smul_smul, Matrix.mul_smul, Matrix.smul_mul]
        _ = star ω • (sTransversalᴴ * (sTransversal * pauliMat (decode s) (decode (s + t))
              * sTransversalᴴ) * sTransversal) := by rw [← hS]
        _ = star ω • pauliMat (decode s) (decode (s + t)) := by
            congr 1
            calc sTransversalᴴ * (sTransversal * pauliMat (decode s) (decode (s + t))
                  * sTransversalᴴ) * sTransversal
                = (sTransversalᴴ * sTransversal) * pauliMat (decode s) (decode (s + t))
                  * (sTransversalᴴ * sTransversal) := by simp only [Matrix.mul_assoc]
              _ = _ := by rw [hSS, Matrix.one_mul, Matrix.mul_one]

/-- `g E = E (c L)` with `|c| = 1`. -/
theorem exists_unit_blockKron_mul_steaneEnc (G : ConcatGadget) :
    ∃ c : ℂ, star c * c = 1 ∧
      blockKron (fun _ : Fin 7 => G.gate) * steaneEnc = steaneEnc * (c • G.logical.gate) := by
  obtain ⟨c, hc⟩ := G.exists_blockKron_mul_steaneEnc
  refine ⟨c, ?_, hc⟩
  have e1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, (steaneEnc * X)ᴴ * (steaneEnc * X) = Xᴴ * X := by
    intro X
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc steaneEncᴴ,
      steaneEnc_conjTranspose_mul, Matrix.one_mul]
  have e2 : (blockKron (fun _ : Fin 7 => G.gate) * steaneEnc)ᴴ
      * (blockKron (fun _ : Fin 7 => G.gate) * steaneEnc) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockKron _)ᴴ,
      G.conjTranspose_blockKron_mul, Matrix.one_mul, steaneEnc_conjTranspose_mul]
  have hunit : (c • G.logical.gate)ᴴ * (c • G.logical.gate) = 1 := by rw [← e1, ← hc, e2]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    G.logical.gate_conjTranspose_mul] at hunit
  exact eq_one_of_smul_one_eq_one hunit

/-- ★★★ **The decoder commutes with each gate on single-type operators**:
`D(g K ρ K† g†) = L D(K ρ K†) L†` for every single-type `K` and every `ρ`. -/
theorem steaneDecode_conj_of_isSingleTypeOp (G : ConcatGadget)
    {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hK : IsSingleTypeOp K)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (blockKron (fun _ : Fin 7 => G.gate) * (K * ρ * Kᴴ)
        * (blockKron fun _ : Fin 7 => G.gate)ᴴ)
      = G.logical.gate * steaneDecode.apply (K * ρ * Kᴴ) * G.logical.gateᴴ := by
  set g := blockKron (fun _ : Fin 7 => G.gate) with hg
  set L := G.logical.gate
  set B : SynPair → Matrix (Fin 2) (Fin 7 → Fin 2) ℂ := fun st => (synCorr st * steaneEnc)ᴴ * K
  choose ω hω hconj using G.exists_conj_synCorr
  obtain ⟨c, hc, hgE⟩ := G.exists_unit_blockKron_mul_steaneEnc
  have hgg : gᴴ * g = 1 := G.conjTranspose_blockKron_mul
  -- `g K = ∑ g C E B`, and each term moves through the gate
  have hgK : g * K = ∑ st, ω st • (synCorr (G.synPerm st) * steaneEnc * ((c • L) * B st)) := by
    have h1 : K = ∑ st, (synCorr st * steaneEnc) * B st := by
      simp only [B, ← Matrix.mul_assoc, ← Matrix.sum_mul, sum_synCorr_steaneEnc_mul_conjTranspose,
        Matrix.one_mul]
    conv_lhs => rw [h1]
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun st _ => ?_
    by_cases hst : SingleType st
    · calc g * (synCorr st * steaneEnc * B st)
          = (g * synCorr st * gᴴ) * (g * steaneEnc) * B st := by
            rw [show g * synCorr st * gᴴ * (g * steaneEnc) = g * synCorr st * (gᴴ * g) * steaneEnc
              by simp only [Matrix.mul_assoc], hgg, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hconj st hst, hgE, Matrix.smul_mul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc]
            rfl
    · have hB : B st = 0 := hK st hst
      simp [hB]
  -- each row of the decoder picks one term
  have hA : ∀ st, (synCorr (G.synPerm st) * steaneEnc)ᴴ * (g * K) = (ω st * c) • (L * B st) := by
    intro st
    rw [hgK, Matrix.mul_sum, Finset.sum_eq_single st]
    · rw [Matrix.mul_smul, ← Matrix.mul_assoc, synCorr_steaneEnc_orthonormal, ite_eq_left rfl,
        Matrix.one_mul, Matrix.smul_mul, smul_smul]
    · intro st' _ hne
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, synCorr_steaneEnc_orthonormal,
        ite_eq_right fun h => hne (G.synPerm_injective h).symm, Matrix.zero_mul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [steaneDecode_apply_eq_sum, steaneDecode_apply_eq_sum,
    ← (Equiv.ofBijective _ (G.synPerm_injective.bijective_of_finite)).sum_comp,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun st _ => ?_
  simp only [Equiv.ofBijective_apply]
  have hA' := hA st
  have hAc : (g * K)ᴴ * (synCorr (G.synPerm st) * steaneEnc) = (star (ω st * c)) • (L * B st)ᴴ := by
    have := congrArg conjTranspose hA'
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul] at this
  have hωc' : star (ω st * c) * (ω st * c) = 1 := by
    rw [star_mul', mul_mul_mul_comm, hω st, hc, one_mul]
  calc (synCorr (G.synPerm st) * steaneEnc)ᴴ * (g * (K * ρ * Kᴴ) * gᴴ)
        * (synCorr (G.synPerm st) * steaneEnc)
      = ((synCorr (G.synPerm st) * steaneEnc)ᴴ * (g * K)) * ρ
        * ((g * K)ᴴ * (synCorr (G.synPerm st) * steaneEnc)) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = L * ((synCorr st * steaneEnc)ᴴ * (K * ρ * Kᴴ) * (synCorr st * steaneEnc)) * Lᴴ := by
        rw [hA', hAc]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hωc', one_smul]
        simp only [B, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- ★★★ **The same for a channel whose branches are all single-type**: `D(g Φ(ρ) g†) = L D(Φ ρ) L†`
for every `ρ`. -/
theorem steaneDecode_conj_channel (G : ConcatGadget) {ι : Type*} [Fintype ι]
    (Φ : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι) (hΦ : ∀ i, IsSingleTypeOp (Φ.kraus i))
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    steaneDecode.apply (G.ideal (Φ.apply ρ))
      = G.logical.gate * steaneDecode.apply (Φ.apply ρ) * G.logical.gateᴴ := by
  have hsum : ∀ Y : ι → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ,
      steaneDecode.apply (∑ i, Y i) = ∑ i, steaneDecode.apply (Y i) := by
    intro Y
    simp only [steaneDecode_apply_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_comm]
  rw [ideal, Channel.apply_def Φ ρ, Matrix.mul_sum, Matrix.sum_mul, hsum, hsum, Matrix.mul_sum,
    Matrix.sum_mul]
  exact Finset.sum_congr rfl fun i _ => G.steaneDecode_conj_of_isSingleTypeOp (hΦ i) ρ

end ConcatGadget

/-! ### The rectangle in the relative form -/

/-- **The hypothesis (BACKLOG #321)**: Steane's method with its factories and one fault anywhere has
single-type branches. -/
def RecNoise.SingleTypeOut {κ : Type} [Fintype κ] (N : RecNoise κ) : Prop :=
  ∀ (l : RecLoc) i, IsSingleTypeOp ((recUnder N.F N.Φ N.hF N.hΦ fun l' => decide (l' = l)).kraus i)

/-- ★★★ **Every rectangle with at most one fault is good after its leading recovery.** For each of
`H̄`, `X̄`, `Z̄`, `S`, `S†`, any trace-preserving fault family at the gadget locations, any noise in
either recovery, and any pattern with at most one fault among the `403` locations: on **every**
input, `D(T'(G'(T ρ))) = L D(T ρ) L†` (#316's `IsGoodAfter` with `D = steaneDecode`), given that
the leading recovery's noise has single-type branches when faulty. -/
theorem steane_rect_isGoodAfter {κ γ : Type} [Fintype κ] [Fintype γ] (G : ConcatGadget)
    {U : Fin 7 → γ → Matrix (Fin 2) (Fin 2) ℂ} (hU : ∀ q, ∑ k, (U q k)ᴴ * U q k = 1)
    (N₁ N₂ : RecNoise κ) (hN₁ : N₁.SingleTypeOut) {ω : RectLoc → Bool} (hω : RectGood ω) :
    IsGoodAfter steaneDecode.apply G.logical.gate (N₁.run (leadPat ω))
      (G.faultyMap U (gadPat ω)) (N₂.run (trailPat ω)) := by
  intro ρ
  rcases pat_cases (f := leadPat ω) (fun x y hx hy => by simpa using hω.eq hx hy) with hL | ⟨l, hL⟩
  · -- a fault-free leading recovery: #313
    have h := steane_rect_correct_clean G hU N₁ N₂ hω hL ρ
    rw [rectRun] at h
    rw [h, hL, N₁.run_none, steaneDecode_methodRecovery]
  · -- the leading recovery holds the fault: the gadget and the trailing recovery are ideal
    have hl : leadPat ω l = true := by rw [hL]; simp
    have hG0 : gadPat ω = fun _ => false := funext fun q => by
      by_contra h
      have := hω.eq hl (show gadPat ω q = true by simpa using h)
      simp at this
    have hT0 : trailPat ω = fun _ => false := funext fun l' => by
      by_contra h
      have := hω.eq hl (show trailPat ω l' = true by simpa using h)
      simp at this
    rw [hG0, hT0, G.faultyMap_none, N₂.run_none, steaneDecode_methodRecovery, hL, RecNoise.run]
    exact G.steaneDecode_conj_channel _ (hN₁ l) ρ

end Steane
end QEC
end QM
end Empirical
end CSD

end
