/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneOverlapMachine

/-!
# Encoded input and logical read-out for the Steane machine

**Category:** 3-Local (Empirical, QM twin). BACKLOG #236 (residue of ~~#233~~).

`SteaneOverlapMachine.lean` (~~#233~~, ~~#238~~) runs the machine from an exact code state and ends with an
ideal decoding. This module puts the two ends into the fault pattern: the input is prepared by a
verified ancilla factory, and the output is read by a transversal `Z` measurement whose word is
decoded classically. Nothing quantum is ideal.

## The prepared input

* `plusAnc_eq_steaneEnc_mulVec`, ★ `steaneProj_mulVec_plusAnc`, `plusState`, `isCodeState_plusState` —
  `|+̄⟩` is a code state; `mulVec_vecMulVec_star`;
* `steaneProj_mul_pauliMat_mul_steaneProj_of_bit` / `_of_phase`, `syndrome_oneBit_add_ne_zero`,
  ★★ `steaneProj_cssPauli_conj` — **Knill–Laflamme for the sixty-four CSS errors**,
  `P E_eᴴ E_e' P = δ_{ee'} P`; ★★ `exists_steaneProj_conj_eq_smul`, `steaneProj_conj_scalar_eq` — on
  the code, `Kᴴ K` is the scalar `‖K |+̄⟩‖²` for every `K` in the CSS span;
* `pauliMat_decode_mem_cssSpan`, ★ `GoodAnc.exists_mem_cssSpan` — a good ancilla is `M |+̄⟩` with `M`
  in the span; `prepState`, `vecMulVec_smul_star`, ★★ `prepState_none` — **a fault-free factory
  prepares `|+̄⟩⟨+̄|`**; ★★★ `exists_prepState_single` — **one fault anywhere in the factory prepares a
  CSS deviation of it**.

## The logical read-out

* `logicalBit` (**decode the word's syndrome, correct, take the parity**), `logProj`, ★ `logicalProb`
  — the probability that the decoded transversal measurement reads `v`; ★★ `logicalProb_steaneEnc` —
  on `E σ Eᴴ` it is `σ v v`: the read-out measures the logical qubit in the `Z̄` basis;
* `logicalBit_add_oneBit`, `logicalBit_rowComb`, `logicalBit_rowComb_add_allOnes`,
  `steaneProj_apply_eq_zero`, `logProj_cssPauli_mul_steaneProj`, `logProj_mul_steaneEnc`,
  ★ `logProj_mul_steaneProj`, `logProj_mul_mem_cssSpan`; ★★★ `logicalProb_cssMix` — **a CSS
  deviation of a code state never changes the logical read-out**;
* `gateOf_family_tp`, `measChannel` (**a Kraus family on each qubit before it is read** — a flipped
  outcome is the family `{X}`), ★ `measChannel_none`, `exists_gateOf_list_prod`,
  ★★ `measChannel_single_mem` — one faulty readout is a CSS deviation.

## The machine from preparation to read-out

* `IOLoc N` — **`46 + 113 N + 7` locations**: the input's factory, the steps, the readouts;
  `ioRun`; `prepLocs`, `measLocs`, `lastLocs`, `ioWindow` — the first extended rectangle with the
  input's factory, every later one, and a last window, the last recovery with the measurement;
  `card_window_zero_le`, ★ `card_ioWindow_le` (`≤ 219`); `IOWindowsGood`, `IOWindowsGood.eq`,
  `IOWindowsGood.windowsGood`, `pattern_cases`, the `mem_ioWindow_*` lemmas, `prepFlag`, `measFlag`,
  `IOWindowsGood.prep_cases`, `IOWindowsGood.meas_cases`, `IOWindowsGood.good_from`,
  `IOWindowsGood.good_last`;
* ★★★ `logicalProb_ioRun` — **with one fault per window the read-out's distribution is the ideal
  one**, through `IsFaultChain.ovRun_spec_from` (`OverlappingRectangles.lean`: the chain from a
  deviated input);
* ★★★ `steane_machine_io` — **the level-one Steane machine from preparation to read-out**: under
  independent faults of rate at most `p` at every location, the decoded logical read-out has its
  ideal distribution with probability at least `1 − 23871 (N + 1) p²`. Nothing is ideal but the
  classical decoding.

## Honest scope

⚠️ **The input is `|+̄⟩`.** `|0̄⟩` is `H̄ |+̄⟩`, the first gadget of the circuit; an arbitrary logical
input, a magic state in particular, is the logical `T̄`'s row (#230).

⚠️ **A rejected ancilla is replaced fault-free**, here at the input as in every recovery (#240).

⚠️ **Gadget faults are unitary on one qubit** (#207's model, #237); one block, three gates (#226);
level one (#231); the constant is `C(219, 2)` (#239).

⚠️ **The read-out is one basis.** An `X̄` read-out is `H̄` and then this one.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97; A. Steane,
PRL 78 (1997) 2252; E. Knill, R. Laflamme, PRA 55 (1997) 900; `specs/BACKLOG.md` #236, #233, #234,
#238, #239, #240, #237, #230, #231; `Empirical/QM/QEC/SteaneOverlapMachine.lean`,
`Empirical/QM/QEC/SteaneVerifiedAncilla.lean`, `Empirical/QM/QEC/SteaneFaultyRecovery.lean`,
`Mathlib/QuantumInfo/OverlappingRectangles.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md`
link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker ENNReal

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### `|+̄⟩` is a code state -/

theorem plusAnc_eq_steaneEnc_mulVec :
    plusAnc = steaneEnc *ᵥ fun _ => ((Real.sqrt 2 : ℂ)⁻¹) := by
  have hcount : ∀ z : Fin 7 → Fin 2,
      (Finset.univ.filter fun c : Fin 3 → Fin 2 => z = rowComb c).card
        + (Finset.univ.filter fun c : Fin 3 → Fin 2 => z = rowComb c + allOnes).card
        = if syndrome z = 0 then 1 else 0 := by
    decide +kernel
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 8 : ℂ)⁻¹ = 1 / 4 := by
    rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num),
      show (2 : ℝ) * 8 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  funext z
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, steaneEnc, Matrix.of_apply, ite_true,
    one_ne_zero, ite_false, steaneZero, steaneOne, WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, basisState_apply, Finset.sum_boole]
  have h := congrArg (fun n : ℕ => (n : ℂ)) (hcount z)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  rw [plusAnc]
  calc (if syndrome z = 0 then (1 / 4 : ℂ) else 0)
      = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 8 : ℂ)⁻¹ * (if syndrome z = 0 then 1 else 0) := by
        rw [hs]; split_ifs <;> ring
    _ = _ := by rw [← h]; ring

/-- ★ **`|+̄⟩` is in the code.** -/
theorem steaneProj_mulVec_plusAnc : steaneProj *ᵥ plusAnc = plusAnc := by
  rw [plusAnc_eq_steaneEnc_mulVec, steaneProj_eq, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    steaneEnc_conjTranspose_mul, Matrix.mul_one]

/-- **The encoded `|+̄⟩` as a density matrix.** -/
def plusState : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ := vecMulVec plusAnc (star plusAnc)

theorem isCodeState_plusState : IsCodeState steaneProj plusState := by
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have hv : star plusAnc ᵥ* steaneProj = star plusAnc := by
    rw [← hP, ← Matrix.star_mulVec, steaneProj_mulVec_plusAnc]
  show plusState = steaneProj * plusState * steaneProj
  rw [plusState, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, steaneProj_mulVec_plusAnc, hv]

theorem mulVec_vecMulVec_star (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
    (v : (Fin 7 → Fin 2) → ℂ) : vecMulVec (M *ᵥ v) (star (M *ᵥ v)) = M * vecMulVec v (star v) * Mᴴ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-! ### Knill–Laflamme for the sixty-four CSS errors -/

theorem steaneProj_mul_pauliMat_mul_steaneProj_of_bit {a b : Fin 7 → Fin 2} (h : syndrome a ≠ 0) :
    steaneProj * pauliMat a b * steaneProj = 0 := by
  have h1 := bitProj_mul_pauliMat_mul_steaneProj (syndrome a) a b
  rw [ite_eq_left rfl] at h1
  have h2 : steaneProj * bitProj (syndrome a) = 0 := by
    have := congrArg conjTranspose (bitProj_mul_steaneProj (syndrome a))
    rw [conjTranspose_mul, bitProj_conjTranspose, isCodeProjector_steaneProj.conjTranspose_eq,
      ite_eq_right h, conjTranspose_zero] at this
    exact this
  rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.zero_mul,
    Matrix.zero_mul]

theorem steaneProj_mul_pauliMat_mul_steaneProj_of_phase {a b : Fin 7 → Fin 2} (h : syndrome b ≠ 0) :
    steaneProj * pauliMat a b * steaneProj = 0 := by
  have h1 := phaseProj_mul_pauliMat_mul_steaneProj (syndrome b) a b
  rw [ite_eq_left rfl] at h1
  have h0 : phaseProj (syndrome b) * steaneProj = 0 := by
    have := phaseProj_mul_pauliMat_mul_steaneProj (syndrome b) 0 0
    rw [pauliMat_zero, Matrix.mul_one, syndrome_zero, ite_eq_right h] at this
    exact this
  have h2 : steaneProj * phaseProj (syndrome b) = 0 := by
    have := congrArg conjTranspose h0
    rw [conjTranspose_mul, phaseProj_conjTranspose, isCodeProjector_steaneProj.conjTranspose_eq,
      conjTranspose_zero] at this
    exact this
  rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.zero_mul,
    Matrix.zero_mul]

theorem syndrome_oneBit_add_ne_zero : ∀ o o' : Option (Fin 7), o ≠ o' →
    syndrome (oneBit o + oneBit o') ≠ 0 := by
  decide

/-- ★★ **Knill–Laflamme for the sixty-four CSS errors**: `P E_eᴴ E_e' P = δ_{ee'} P`. -/
theorem steaneProj_cssPauli_conj (e e' : CssErr) :
    steaneProj * ((cssPauli e)ᴴ * cssPauli e') * steaneProj
      = if e = e' then steaneProj else 0 := by
  by_cases hee : e = e'
  · subst hee
    rw [ite_eq_left rfl, cssPauli, pauliMat_conjTranspose_mul_self, Matrix.mul_one,
      isCodeProjector_steaneProj.mul_self]
  · rw [ite_eq_right hee, cssPauli, cssPauli, pauliMat_conjTranspose, Matrix.smul_mul, pauliMat_mul,
      smul_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Prod.ext_iff.not, not_and_or] at hee
    rcases hee with h | h
    · rw [steaneProj_mul_pauliMat_mul_steaneProj_of_bit (syndrome_oneBit_add_ne_zero _ _ h),
        smul_zero]
    · rw [steaneProj_mul_pauliMat_mul_steaneProj_of_phase (syndrome_oneBit_add_ne_zero _ _ h),
        smul_zero]

/-- ★★ **On the code, `Kᴴ K` is a scalar for every `K` in the CSS span.** -/
theorem exists_steaneProj_conj_eq_smul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : K ∈ cssSpan) : ∃ c : ℂ, steaneProj * (Kᴴ * K) * steaneProj = c • steaneProj := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hK
  refine ⟨∑ e, a e * star (a e), ?_⟩
  have hKK : (∑ e, a e • cssPauli e)ᴴ * (∑ e, a e • cssPauli e)
      = ∑ x, ∑ y, (a y * star (a x)) • ((cssPauli x)ᴴ * cssPauli y) := by
    rw [conjTranspose_sum, Finset.sum_mul_sum]
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hKK, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    steaneProj_cssPauli_conj]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single e (fun e' _ he' => by rw [ite_eq_right (Ne.symm he'), smul_zero])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- A code vector of norm one reads that scalar. -/
theorem steaneProj_conj_scalar_eq {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} {c : ℂ}
    (hc : steaneProj * (Kᴴ * K) * steaneProj = c • steaneProj) :
    ∑ a, star ((K *ᵥ plusAnc) a) * (K *ᵥ plusAnc) a = c := by
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have hn : star plusAnc ⬝ᵥ plusAnc = 1 := sum_plusAnc_sq
  have hv : star plusAnc ᵥ* steaneProj = star plusAnc := by
    rw [← hP, ← Matrix.star_mulVec, steaneProj_mulVec_plusAnc]
  have h1 : (steaneProj * (Kᴴ * K) * steaneProj) *ᵥ plusAnc
      = steaneProj *ᵥ ((Kᴴ * K) *ᵥ plusAnc) := by
    rw [← Matrix.mulVec_mulVec, steaneProj_mulVec_plusAnc, ← Matrix.mulVec_mulVec]
  calc ∑ a, star ((K *ᵥ plusAnc) a) * (K *ᵥ plusAnc) a
      = star (K *ᵥ plusAnc) ⬝ᵥ (K *ᵥ plusAnc) := rfl
    _ = star plusAnc ⬝ᵥ ((Kᴴ * K) *ᵥ plusAnc) := by
        rw [Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec]
    _ = star plusAnc ⬝ᵥ ((steaneProj * (Kᴴ * K) * steaneProj) *ᵥ plusAnc) := by
        rw [h1, dotProduct_mulVec (star plusAnc) steaneProj ((Kᴴ * K) *ᵥ plusAnc), hv]
    _ = c := by rw [hc, Matrix.smul_mulVec, steaneProj_mulVec_plusAnc, dotProduct_smul, hn,
          smul_eq_mul, mul_one]

/-! ### The prepared input -/

theorem pauliMat_decode_mem_cssSpan (t : Fin 3 → Fin 2) : pauliMat (decode t) 0 ∈ cssSpan := by
  rcases decode_eq_zero_or_unitErr t with h | ⟨q, h⟩
  · have := cssPauli_mem_cssSpan (none, none)
    rw [h]
    simpa [cssPauli, oneBit] using this
  · have := cssPauli_mem_cssSpan (some q, none)
    rw [h]
    simpa [cssPauli, oneBit] using this

/-- **A good ancilla is `M |+̄⟩` with `M` in the CSS span.** -/
theorem GoodAnc.exists_mem_cssSpan {f : (Fin 7 → Fin 2) → ℂ} (hf : GoodAnc f) :
    ∃ M ∈ cssSpan, f = M *ᵥ plusAnc := by
  rcases hf with hf | ⟨j, N, rfl⟩
  · refine ⟨∑ t, (4 * f (decode t)) • pauliMat (decode t) 0,
      Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (pauliMat_decode_mem_cssSpan t), ?_⟩
    conv_lhs => rw [hf.eq_sum]
    rw [Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
  · exact ⟨gateOf j N, gateOf_mem_cssSpan j N, rfl⟩

/-- **The factory's output as the input state**: the mixture of its branches. -/
def prepState {κ : Type} [Fintype κ] (Φ : FacFaults κ) (b : FacLoc → Bool) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  ∑ p, vecMulVec (facOut Φ b p) (star (facOut Φ b p))

theorem vecMulVec_smul_star (c : ℂ) (u : (Fin 7 → Fin 2) → ℂ) :
    vecMulVec (c • u) (star (c • u)) = (c * star c) • vecMulVec u (star u) := by
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', Matrix.smul_apply]
  ring

/-- ★★ **A fault-free factory prepares `|+̄⟩⟨+̄|`.** -/
theorem prepState_none {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) :
    prepState Φ (fun _ => false) = plusState := by
  choose c hc using facOut_none Φ
  have hn := facOut_norm hΦ (fun _ => false)
  simp only [hc, Pi.smul_apply, smul_eq_mul, star_mul'] at hn
  have hcc : ∑ p, c p * star (c p) = 1 := by
    rw [← hn]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc c p * star (c p) = c p * star (c p) * ∑ a, star (plusAnc a) * plusAnc a := by
          rw [sum_plusAnc_sq, mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [prepState]
  simp only [hc, vecMulVec_smul_star]
  rw [← Finset.sum_smul, hcc, one_smul]
  rfl

/-- ★★★ **One fault anywhere in the factory prepares a CSS deviation of `|+̄⟩⟨+̄|`**: every branch is
`M |+̄⟩` with `M` in the CSS span, and the branches' weights make the mixture trace preserving on the
code (`exists_steaneProj_conj_eq_smul`). -/
theorem exists_prepState_single {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid)
    (ℓ : FacLoc) : ∃ E ∈ cssMix, prepState Φ (fun ℓ' => decide (ℓ' = ℓ)) = E plusState := by
  choose M hM hf using fun p => (goodAnc_facOut_single hΦ ℓ p).exists_mem_cssSpan
  choose c hc using fun p => exists_steaneProj_conj_eq_smul (hM p)
  have hsum : ∑ p, c p = 1 := by
    rw [← facOut_norm hΦ (fun ℓ' => decide (ℓ' = ℓ))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hf p]
    exact (steaneProj_conj_scalar_eq (hc p)).symm
  refine ⟨fun σ => ∑ p, M p * σ * (M p)ᴴ, ⟨_, inferInstance, M, hM, ?_, rfl⟩, ?_⟩
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    simp only [hc]
    rw [← Finset.sum_smul, hsum, one_smul]
  · rw [prepState]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hf p, mulVec_vecMulVec_star]
    rfl

/-! ### The logical read-out -/

/-- **The logical bit read from a word**: correct the word by its syndrome's decoding, take the
parity. -/
def logicalBit (z : Fin 7 → Fin 2) : Fin 2 := ∑ i, (z + decode (syndrome z)) i

/-- The words read as logical `v`. -/
def logProj (v : Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  Matrix.diagonal fun z => if logicalBit z = v then 1 else 0

/-- ★ **The probability that the transversal `Z` measurement, decoded, reads logical `v`.** -/
def logicalProb (σ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (v : Fin 2) : ℂ :=
  (logProj v * σ).trace

theorem logicalBit_add_oneBit {c : Fin 7 → Fin 2} (hc : syndrome c = 0) (o : Option (Fin 7)) :
    logicalBit (c + oneBit o) = logicalBit c := by
  have h1 : decode (syndrome (c + oneBit o)) = oneBit o := by
    rw [syndrome_add, hc, zero_add, decode_syndrome_oneBit]
  have h2 : decode (syndrome c) = 0 := by rw [hc, decode_zero]
  simp only [logicalBit, h1, h2, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  rw [add_assoc, fin2_add_self, add_zero]

theorem logicalBit_rowComb (c : Fin 3 → Fin 2) : logicalBit (rowComb c) = 0 := by
  revert c
  decide

theorem logicalBit_rowComb_add_allOnes (c : Fin 3 → Fin 2) :
    logicalBit (rowComb c + allOnes) = 1 := by
  revert c
  decide

theorem steaneProj_apply_eq_zero {u w : Fin 7 → Fin 2} (hu : syndrome u ≠ 0) :
    steaneProj u w = 0 := by
  rw [← bitProj_zero_mul_steaneProj]
  simp only [bitProj, synProj, Matrix.diagonal_mul]
  rw [ite_eq_right hu, zero_mul]

/-- **A CSS error moves the read word only within its logical class**, on the code. -/
theorem logProj_cssPauli_mul_steaneProj (v : Fin 2) (e : CssErr) :
    logProj v * cssPauli e * steaneProj = cssPauli e * logProj v * steaneProj := by
  ext y w
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [logProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : u = y + oneBit e.1
  · by_cases hs : syndrome u = 0
    · have hl : logicalBit y = logicalBit u := by
        have h := logicalBit_add_oneBit hs e.1
        rwa [hu, add_assoc, show oneBit e.1 + oneBit e.1 = 0 from funext fun i => fin2_add_self _,
          add_zero, ← hu] at h
      simp only [hl]
      ring
    · rw [steaneProj_apply_eq_zero hs]
      ring
  · have h0 : cssPauli e y u = 0 := by simp [cssPauli, pauliMat, hu]
    rw [h0]
    ring

theorem logProj_mul_steaneEnc (v : Fin 2) :
    logProj v * steaneEnc = steaneEnc * Matrix.diagonal fun j : Fin 2 => if j = v then (1 : ℂ) else 0 := by
  ext z j
  rw [logProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [steaneEnc, Matrix.of_apply, steaneZero, steaneOne, WithLp.ofLp_smul, WithLp.ofLp_sum,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, basisState_apply]
  fin_cases j
  · simp only [Fin.zero_eta, ite_true]
    by_cases hz : ∃ c, z = rowComb c
    · obtain ⟨c, rfl⟩ := hz
      rw [logicalBit_rowComb]
      ring
    · simp only [not_exists] at hz
      simp [hz]
  · simp only [Fin.mk_one, one_ne_zero, ite_false]
    by_cases hz : ∃ c, z = rowComb c + allOnes
    · obtain ⟨c, rfl⟩ := hz
      rw [logicalBit_rowComb_add_allOnes]
      ring
    · simp only [not_exists] at hz
      simp [hz]

/-- ★ **The read-out's logical classes are a decomposition of the code.** -/
theorem logProj_mul_steaneProj (v : Fin 2) :
    logProj v * steaneProj = steaneProj * logProj v * steaneProj := by
  calc logProj v * steaneProj = logProj v * steaneEnc * steaneEncᴴ := by
        rw [steaneProj_eq, Matrix.mul_assoc]
    _ = steaneEnc * (Matrix.diagonal fun j : Fin 2 => if j = v then (1 : ℂ) else 0) * steaneEncᴴ := by
        rw [logProj_mul_steaneEnc]
    _ = steaneEnc * (steaneEncᴴ * (logProj v * steaneEnc)) * steaneEncᴴ := by
        rw [logProj_mul_steaneEnc, ← Matrix.mul_assoc steaneEncᴴ, steaneEnc_conjTranspose_mul,
          Matrix.one_mul]
    _ = steaneProj * logProj v * steaneProj := by
        rw [steaneProj_eq]
        simp only [Matrix.mul_assoc]

theorem logProj_mul_mem_cssSpan (v : Fin 2) {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : K ∈ cssSpan) : logProj v * K * steaneProj = K * logProj v * steaneProj := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hK
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    logProj_cssPauli_mul_steaneProj]

/-- ★★★ **A CSS deviation of a code state never changes the logical read-out**: the transversal
measurement, decoded, reads each logical value with the same probability. -/
theorem logicalProb_cssMix {E : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ →
      Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hE : E ∈ cssMix)
    {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hρ : IsCodeState steaneProj ρ) (v : Fin 2) :
    logicalProb (E ρ) v = logicalProb ρ v := by
  obtain ⟨ι, _, K, hK, htp, rfl⟩ := hE
  have hρ' : ρ = steaneProj * ρ * steaneProj := hρ
  have hP := isCodeProjector_steaneProj
  have hterm : ∀ b, (logProj v * (K b * ρ * (K b)ᴴ)).trace
      = (steaneProj * ((K b)ᴴ * K b) * steaneProj * (logProj v * steaneProj) * ρ).trace := by
    intro b
    have h1 : steaneProj * (K b)ᴴ * logProj v * K b * steaneProj
        = steaneProj * ((K b)ᴴ * K b) * steaneProj * (logProj v * steaneProj) := by
      calc steaneProj * (K b)ᴴ * logProj v * K b * steaneProj
          = steaneProj * (K b)ᴴ * (logProj v * K b * steaneProj) := by simp only [Matrix.mul_assoc]
        _ = steaneProj * (K b)ᴴ * (K b * (logProj v * steaneProj)) := by
            rw [logProj_mul_mem_cssSpan v (hK b)]; simp only [Matrix.mul_assoc]
        _ = steaneProj * (K b)ᴴ * (K b * (steaneProj * (logProj v * steaneProj))) := by
            rw [logProj_mul_steaneProj, ← Matrix.mul_assoc steaneProj, ← Matrix.mul_assoc steaneProj,
              hP.mul_self]
        _ = _ := by simp only [Matrix.mul_assoc]
    calc (logProj v * (K b * ρ * (K b)ᴴ)).trace
        = (logProj v * (K b * (steaneProj * ρ * steaneProj) * (K b)ᴴ)).trace := by rw [← hρ']
      _ = (steaneProj * (K b)ᴴ * logProj v * K b * steaneProj * ρ).trace := by
          rw [show logProj v * (K b * (steaneProj * ρ * steaneProj) * (K b)ᴴ)
              = (logProj v * K b * steaneProj * ρ) * (steaneProj * (K b)ᴴ) by
                simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  rw [logicalProb, logicalProb, Matrix.mul_sum, Matrix.trace_sum]
  simp only [hterm]
  have hPρ : steaneProj * ρ = ρ := by
    calc steaneProj * ρ = steaneProj * (steaneProj * ρ * steaneProj) := by rw [← hρ']
      _ = steaneProj * ρ * steaneProj := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self]
      _ = ρ := hρ'.symm
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.mul_sum, htp,
    ← Matrix.mul_assoc steaneProj, ← logProj_mul_steaneProj, Matrix.mul_assoc, hPρ]

/-! ### Faults at the transversal measurement -/

theorem gateOf_family_tp {κ : Type*} [Fintype κ] {N : κ → Matrix (Fin 2) (Fin 2) ℂ} (j : Fin 7)
    (hN : ∑ k, (N k)ᴴ * N k = 1) : ∑ k, (gateOf j (N k))ᴴ * gateOf j (N k) = 1 := by
  simp only [gateOf_conjTranspose, ← Controlled.gateOf_mul]
  rw [← gateOf_sum, hN, gateOf_one]

/-- **The measurement's faults under a pattern**: a Kraus family on qubit `j` before it is read, at
each faulty readout — a flipped outcome is the family `{X}`. -/
def measChannel {κ : Type} [Fintype κ] (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1) (b : Fin 7 → Bool) :
    Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Fin 7 → Option κ) where
  kraus s := roundKraus (fun j k => gateOf j (Nm j k)) b s
  tp := roundKraus_tp (fun j => gateOf_family_tp j (hNm j)) b

/-- A fault-free measurement adds nothing. -/
theorem measChannel_none {κ : Type} [Fintype κ] (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1) : (measChannel Nm hNm fun _ => false).apply = id := by
  funext σ
  rw [Channel.apply_def, Finset.sum_eq_single (fun _ => none)]
  · show roundKraus (fun j k => gateOf j (Nm j k)) (fun _ => false) (fun _ => none) * σ
      * (roundKraus (fun j k => gateOf j (Nm j k)) (fun _ => false) (fun _ => none))ᴴ = σ
    rw [roundKraus_none, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro s _ hs
    show roundKraus (fun j k => gateOf j (Nm j k)) (fun _ => false) s * σ
      * (roundKraus (fun j k => gateOf j (Nm j k)) (fun _ => false) s)ᴴ = 0
    rw [roundKraus_none_of_ne _ hs, Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_gateOf_list_prod (j : Fin 7) :
    ∀ l : List (Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ), (∀ K ∈ l, ∃ M, K = gateOf j M) →
      ∃ M, l.prod = gateOf j M
  | [], _ => ⟨1, by rw [List.prod_nil, gateOf_one]⟩
  | K :: l, h => by
    obtain ⟨M, hM⟩ := h K List.mem_cons_self
    obtain ⟨M', hM'⟩ := exists_gateOf_list_prod j l fun K' hK' => h K' (List.mem_cons_of_mem _ hK')
    exact ⟨M * M', by rw [List.prod_cons, hM, hM', Controlled.gateOf_mul]⟩

/-- ★★ **One faulty readout is a CSS deviation**: every branch acts on the read qubit alone. -/
theorem measChannel_single_mem {κ : Type} [Fintype κ] (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1) (j : Fin 7) :
    (measChannel Nm hNm fun j' => decide (j' = j)).apply ∈ cssMix := by
  have hK : ∀ s, ∃ M, (measChannel Nm hNm fun j' => decide (j' = j)).kraus s = gateOf j M := by
    intro s
    refine exists_gateOf_list_prod j _ fun K hK => ?_
    obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hK
    by_cases h : j' = j
    · subst h
      rcases hs : s j' with _ | k
      · exact ⟨0, by simp [locFam, gateOf_zero]⟩
      · exact ⟨Nm j' k, by simp [locFam]⟩
    · rcases hs : s j' with _ | k
      · exact ⟨1, by simp [locFam, h, gateOf_one]⟩
      · exact ⟨0, by simp [locFam, h, gateOf_zero]⟩
  refine ⟨_, inferInstance, (measChannel Nm hNm fun j' => decide (j' = j)).kraus, fun s => ?_, ?_,
    funext fun ρ => Channel.apply_def _ ρ⟩
  · obtain ⟨M, hM⟩ := hK s
    rw [hM]
    exact gateOf_mem_cssSpan j M
  · rw [(measChannel Nm hNm fun j' => decide (j' = j)).tp, Matrix.mul_one,
      isCodeProjector_steaneProj.mul_self]

/-! ### The machine from preparation to read-out -/

/-- **The locations from preparation to read-out**: the input's factory, the `N` steps, the seven
readouts. -/
abbrev IOLoc (N : ℕ) : Type := FacLoc ⊕ OvLoc N ⊕ Fin 7

instance instDecidableEqIOLoc (N : ℕ) : DecidableEq (IOLoc N) :=
  inferInstanceAs (DecidableEq (FacLoc ⊕ OvLoc N ⊕ Fin 7))

instance instFintypeIOLoc (N : ℕ) : Fintype (IOLoc N) :=
  inferInstanceAs (Fintype (FacLoc ⊕ OvLoc N ⊕ Fin 7))

variable {N : ℕ} {κ : Type}

/-- **The machine from preparation to read-out under a pattern**: the input prepared by a factory,
the `N` steps, the measurement with its faults; the state whose transversal read-out is decoded. -/
def ioRun (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp) (Φ : Fin N → MethodRound → FacFaults κ)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1) (hΦ : ∀ j r, (Φ j r).Valid)
    (Φ₀ : FacFaults κ) (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1) (ω : IOLoc N → Bool) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (measChannel Nm hNm fun j => ω (.inr (.inr j))).apply
    (overlapRun gs U F Φ hF hΦ (fun x => ω (.inr (.inl x))) (prepState Φ₀ fun ℓ => ω (.inl ℓ)))

/-- The input's factory locations. -/
def prepLocs : Finset (IOLoc N) := Finset.univ.image Sum.inl

/-- The readouts. -/
def measLocs : Finset (IOLoc N) := Finset.univ.image fun j => Sum.inr (Sum.inr j)

/-- The last recovery's locations, or the input's factory when there is no step. -/
def lastLocs : Finset (IOLoc N) :=
  if h : 0 < N then Finset.univ.image fun l : RecLoc => Sum.inr (Sum.inl ((⟨N - 1, by omega⟩ : Fin N), .inr l))
  else prepLocs

/-- **The windows from preparation to read-out**: the `k`-th extended rectangle — the first one with
the input's factory — and a last window, the last recovery with the measurement. -/
def ioWindow (k : Fin (N + 1)) : Finset (IOLoc N) :=
  if h : (k : ℕ) < N then
    (window ⟨k, h⟩).image (fun x => Sum.inr (Sum.inl x)) ∪ (if (k : ℕ) = 0 then prepLocs else ∅)
  else lastLocs ∪ measLocs

theorem card_window_zero_le (h : 0 < N) : (window (⟨0, h⟩ : Fin N)).card ≤ 113 := by
  have hsub : window (⟨0, h⟩ : Fin N) ⊆ Finset.univ.image fun s : StepLoc => ((⟨0, h⟩ : Fin N), s) := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ?_
    rcases a with s | l
    · exact ⟨s, Finset.mem_univ _, rfl⟩
    · exact ⟨.inr l, Finset.mem_univ _, by simp [winLoc, prevStep]⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, card_methodRound]

/-- ★ **Every window from preparation to read-out has at most `219` locations.** -/
theorem card_ioWindow_le (k : Fin (N + 1)) : (ioWindow k).card ≤ 219 := by
  have hp : (prepLocs : Finset (IOLoc N)).card ≤ 46 := by
    refine Finset.card_image_le.trans ?_
    simp [Finset.card_univ, Fintype.card_sum]
  have hm : (measLocs : Finset (IOLoc N)).card ≤ 7 := Finset.card_image_le.trans (by simp)
  rw [ioWindow]
  split_ifs with h h0
  · have h0' : (⟨(k : ℕ), h⟩ : Fin N) = ⟨0, by omega⟩ := Fin.ext h0
    rw [h0']
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : ((window (⟨0, by omega⟩ : Fin N)).image
        (fun x => (Sum.inr (Sum.inl x) : IOLoc N))).card ≤ 113 :=
      Finset.card_image_le.trans (card_window_zero_le _)
    omega
  · rw [Finset.union_empty]
    exact Finset.card_image_le.trans (card_window_le _)
  · refine (Finset.card_union_le _ _).trans ?_
    have hl : (lastLocs : Finset (IOLoc N)).card ≤ 106 := by
      rw [lastLocs]
      split_ifs
      · refine Finset.card_image_le.trans ?_
        simp [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, card_methodRound]
      · omega
    omega

/-- Every window from preparation to read-out holds at most one fault. -/
def IOWindowsGood (ω : IOLoc N → Bool) : Prop :=
  ∀ k, ((ioWindow k).filter fun x => ω x = true).card ≤ 1

theorem IOWindowsGood.eq {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) (k : Fin (N + 1))
    {x y : IOLoc N} (hx : x ∈ ioWindow k) (hy : y ∈ ioWindow k) (hωx : ω x = true)
    (hωy : ω y = true) : x = y :=
  Finset.card_le_one.1 (hω k) x (Finset.mem_filter.2 ⟨hx, hωx⟩) y (Finset.mem_filter.2 ⟨hy, hωy⟩)

theorem IOWindowsGood.windowsGood {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) :
    WindowsGood fun x => ω (.inr (.inl x)) := by
  intro k
  have hsub : ((window k).filter fun x => ω (.inr (.inl x)) = true).image
      (fun x => (Sum.inr (Sum.inl x) : IOLoc N))
      ⊆ (ioWindow ⟨k, by omega⟩).filter fun x => ω x = true := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hxw, hωx⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨?_, hωx⟩
    simp only [ioWindow, k.isLt, ↓reduceDIte]
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨x, hxw, rfl⟩)
  rw [← Finset.card_image_of_injective _ (f := fun x => (Sum.inr (Sum.inl x) : IOLoc N))
    (fun a b h => by simpa using h)]
  exact (Finset.card_le_card hsub).trans (hω _)

/-- A pattern with at most one fault in a set holding all its locations is fault-free or single. -/
theorem pattern_cases {α : Type*} [DecidableEq α] (b : α → Bool)
    (h : ∀ x y, b x = true → b y = true → x = y) :
    (b = fun _ => false) ∨ ∃ a, b = fun x => decide (x = a) := by
  by_cases hb : ∃ a, b a = true
  · obtain ⟨a, ha⟩ := hb
    refine Or.inr ⟨a, funext fun x => ?_⟩
    by_cases hx : x = a
    · subst hx
      simpa using ha
    · have : b x ≠ true := fun hbx => hx (h x a hbx ha)
      simpa [hx] using this
  · refine Or.inl (funext fun x => ?_)
    simpa using fun h' => hb ⟨x, h'⟩

theorem mem_ioWindow_prep (h : 0 < N) (ℓ : FacLoc) : (Sum.inl ℓ : IOLoc N) ∈ ioWindow 0 := by
  simp [ioWindow, h, prepLocs]

theorem mem_ioWindow_step (h : 0 < N) (s : StepLoc) :
    (Sum.inr (Sum.inl ((⟨0, h⟩ : Fin N), s)) : IOLoc N) ∈ ioWindow 0 := by
  simp only [ioWindow, Fin.val_zero, h, ↓reduceDIte]
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨_, mem_window_step _ s, rfl⟩)

theorem mem_ioWindow_meas (j : Fin 7) : (Sum.inr (Sum.inr j) : IOLoc N) ∈ ioWindow (Fin.last N) := by
  simp [ioWindow, measLocs]

theorem mem_ioWindow_last {k : ℕ} (hk : N = k + 1) (l : RecLoc) :
    (Sum.inr (Sum.inl ((⟨k, by omega⟩ : Fin N), .inr l)) : IOLoc N) ∈ ioWindow (Fin.last N) := by
  have hN : 0 < N := by omega
  simp only [ioWindow, Fin.val_last, lt_irrefl, ↓reduceDIte, lastLocs, hN]
  refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, ?_⟩)
  congr
  omega

theorem mem_ioWindow_last_prep (hN : N = 0) (ℓ : FacLoc) :
    (Sum.inl ℓ : IOLoc N) ∈ ioWindow (Fin.last N) := by
  have hN' : ¬0 < N := by omega
  simp only [ioWindow, Fin.val_last, lt_irrefl, ↓reduceDIte, lastLocs, hN']
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨ℓ, Finset.mem_univ _, rfl⟩)

/-- ★★ **The read-out measures the logical qubit in the `Z̄` basis**: on an encoded state
`E σ Eᴴ` it reads `v` with probability `σ v v`. -/
theorem logicalProb_steaneEnc (σ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2) :
    logicalProb (steaneEnc * σ * steaneEncᴴ) v = σ v v := by
  rw [logicalProb, show logProj v * (steaneEnc * σ * steaneEncᴴ)
      = (logProj v * steaneEnc) * σ * steaneEncᴴ by simp only [Matrix.mul_assoc],
    logProj_mul_steaneEnc, Matrix.trace_mul_comm,
    show steaneEncᴴ * (steaneEnc * (Matrix.diagonal fun j : Fin 2 => if j = v then (1 : ℂ) else 0) * σ)
      = (steaneEncᴴ * steaneEnc) * (Matrix.diagonal fun j : Fin 2 => if j = v then (1 : ℂ) else 0) * σ
      by simp only [Matrix.mul_assoc], steaneEnc_conjTranspose_mul, Matrix.one_mul]
  simp [Matrix.trace, Matrix.diagonal_mul, Finset.sum_ite_eq']

/-- Whether the input's factory holds a fault. -/
def prepFlag (ω : IOLoc N → Bool) : Bool := decide (∃ ℓ, ω (.inl ℓ) = true)

/-- Whether a readout holds a fault. -/
def measFlag (ω : IOLoc N → Bool) : Bool := decide (∃ j, ω (.inr (.inr j)) = true)

theorem IOWindowsGood.prep_cases {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) :
    ((fun ℓ => ω (.inl ℓ)) = fun _ => false) ∨ ∃ ℓ₀, (fun ℓ => ω (.inl ℓ)) = fun ℓ => decide (ℓ = ℓ₀) :=
  pattern_cases _ fun x y hx hy => by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simpa using hω.eq (Fin.last N) (mem_ioWindow_last_prep hN x) (mem_ioWindow_last_prep hN y) hx hy
    · simpa using hω.eq 0 (mem_ioWindow_prep hN x) (mem_ioWindow_prep hN y) hx hy

theorem IOWindowsGood.meas_cases {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) :
    ((fun j => ω (.inr (.inr j))) = fun _ => false)
      ∨ ∃ j₀, (fun j => ω (.inr (.inr j))) = fun j => decide (j = j₀) :=
  pattern_cases _ fun x y hx hy => by
    simpa using hω.eq (Fin.last N) (mem_ioWindow_meas x) (mem_ioWindow_meas y) hx hy

/-- **The first extended rectangle, with the input's factory, holds at most one faulty piece.** -/
theorem IOWindowsGood.good_from {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) :
    ∀ k < N, (lastFaultFrom (prepFlag ω) (recoveryFlag fun x => ω (.inr (.inl x))) k).toNat
      + (gadgetFlag (fun x => ω (.inr (.inl x))) k).toNat
      + (recoveryFlag (fun x => ω (.inr (.inl x))) k).toNat ≤ 1 := by
  intro k hk
  have hg := exRecGood_of_windowsGood hω.windowsGood k hk
  cases k with
  | succ k => exact hg
  | zero =>
    unfold ExRecGood at hg
    simp only [lastFault, Bool.toNat_false, zero_add] at hg
    simp only [lastFaultFrom]
    have hP : prepFlag ω = true → ∃ ℓ, ω (.inl ℓ) = true := fun h => of_decide_eq_true h
    have hG : gadgetFlag (fun x => ω (.inr (.inl x))) 0 = true →
        ∃ q, ω (.inr (.inl ((⟨0, hk⟩ : Fin N), .inl q))) = true := by
      intro h
      simp only [gadgetFlag, hk, ↓reduceDIte] at h
      exact of_decide_eq_true h
    have hR : recoveryFlag (fun x => ω (.inr (.inl x))) 0 = true →
        ∃ l, ω (.inr (.inl ((⟨0, hk⟩ : Fin N), .inr l))) = true := by
      intro h
      simpa [recoveryFlag, hk, recPat, decide_eq_true_eq] using h
    have hPG : prepFlag ω = true → gadgetFlag (fun x => ω (.inr (.inl x))) 0 = true → False := by
      intro h1 h2
      obtain ⟨ℓ, hℓ⟩ := hP h1
      obtain ⟨q, hq⟩ := hG h2
      have := hω.eq 0 (mem_ioWindow_prep hk ℓ) (mem_ioWindow_step hk (.inl q)) hℓ hq
      simp at this
    have hPR : prepFlag ω = true → recoveryFlag (fun x => ω (.inr (.inl x))) 0 = true → False := by
      intro h1 h2
      obtain ⟨ℓ, hℓ⟩ := hP h1
      obtain ⟨l, hl⟩ := hR h2
      have := hω.eq 0 (mem_ioWindow_prep hk ℓ) (mem_ioWindow_step hk (.inr l)) hℓ hl
      simp at this
    cases h0 : prepFlag ω <;> cases h1 : gadgetFlag (fun x => ω (.inr (.inl x))) 0 <;>
      cases h2 : recoveryFlag (fun x => ω (.inr (.inl x))) 0 <;> simp_all

/-- **The last window, the last recovery with the measurement, holds at most one faulty piece.** -/
theorem IOWindowsGood.good_last {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) :
    (lastFaultFrom (prepFlag ω) (recoveryFlag fun x => ω (.inr (.inl x))) N).toNat
      + (measFlag ω).toNat ≤ 1 := by
  have hM : measFlag ω = true → ∃ j, ω (.inr (.inr j)) = true := fun h => of_decide_eq_true h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [lastFaultFrom]
    have hP : prepFlag ω = true → ∃ ℓ, ω (.inl ℓ) = true := fun h => of_decide_eq_true h
    have hPM : prepFlag ω = true → measFlag ω = true → False := by
      intro h1 h2
      obtain ⟨ℓ, hℓ⟩ := hP h1
      obtain ⟨j, hj⟩ := hM h2
      have := hω.eq (Fin.last 0) (mem_ioWindow_last_prep rfl ℓ) (mem_ioWindow_meas j) hℓ hj
      simp at this
    cases h0 : prepFlag ω <;> cases h1 : measFlag ω <;> simp_all
  · obtain ⟨k, hk'⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    have hkN : k < N := by omega
    have key : ∀ (f₀ : Bool) (fR : ℕ → Bool) (n : ℕ), n = k + 1 → lastFaultFrom f₀ fR n = fR k := by
      intro f₀ fR n hn
      subst hn
      rfl
    rw [key _ _ N hk']
    have hR : recoveryFlag (fun x => ω (.inr (.inl x))) k = true →
        ∃ l, ω (.inr (.inl ((⟨k, hkN⟩ : Fin N), .inr l))) = true := by
      intro h
      simpa [recoveryFlag, hkN, recPat, decide_eq_true_eq] using h
    have hRM : recoveryFlag (fun x => ω (.inr (.inl x))) k = true → measFlag ω = true → False := by
      intro h1 h2
      obtain ⟨l, hl⟩ := hR h1
      obtain ⟨j, hj⟩ := hM h2
      have := hω.eq (Fin.last N) (mem_ioWindow_last hk' l) (mem_ioWindow_meas j) hl hj
      simp at this
    cases h0 : recoveryFlag (fun x => ω (.inr (.inl x))) k <;> cases h1 : measFlag ω <;> simp_all

/-- ★★★ **The machine from preparation to read-out, with one fault per window, reads the ideal
logical outcome distribution.** -/
theorem logicalProb_ioRun (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
    (hOn : ∀ j r q k, OnPair q (F j r q k)) (Φ : Fin N → MethodRound → FacFaults κ)
    (hΦ : ∀ j r, (Φ j r).Valid) {Φ₀ : FacFaults κ} (hΦ₀ : Φ₀.Valid)
    (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ) (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1)
    {ω : IOLoc N → Bool} (hω : IOWindowsGood ω) (v : Fin 2) :
    logicalProb (ioRun gs U F Φ hF hΦ Φ₀ Nm hNm ω) v = logicalProb (machineIdeal gs plusState) v := by
  have hc := isFaultChain_overlap gs U hU F hF hOn Φ hΦ hω.windowsGood
  have hprep : (∃ E ∈ cssMix, prepState Φ₀ (fun ℓ => ω (.inl ℓ)) = E plusState)
      ∧ (prepFlag ω = false → prepState Φ₀ (fun ℓ => ω (.inl ℓ)) = plusState) := by
    rcases hω.prep_cases with h | ⟨ℓ₀, h⟩
    · rw [h, prepState_none hΦ₀]
      exact ⟨⟨id, id_mem_cssMix, rfl⟩, fun _ => rfl⟩
    · refine ⟨h ▸ exists_prepState_single hΦ₀ ℓ₀, fun hf => ?_⟩
      have h1 : ω (.inl ℓ₀) = true := by simpa using congrFun h ℓ₀
      have h2 : ω (.inl ℓ₀) ≠ true := by
        simp only [prepFlag, decide_eq_false_iff_not, not_exists] at hf
        exact hf ℓ₀
      exact absurd h1 h2
  obtain ⟨hdev, hex⟩ := hc.ovRun_spec_from hω.good_from isCodeState_plusState hprep.1 hprep.2 N
    le_rfl
  rw [ovIdeal_ovGadget] at hdev hex
  have hideal : IsCodeState steaneProj (machineIdeal gs plusState) := by
    have h := hc.isCodeState_ovIdeal isCodeState_plusState N le_rfl
    rwa [ovIdeal_ovGadget] at h
  have hrun : overlapRun gs U F Φ hF hΦ (fun x => ω (.inr (.inl x)))
      (prepState Φ₀ fun ℓ => ω (.inl ℓ))
      = ovRun (ovRecovery F Φ hF hΦ fun x => ω (.inr (.inl x)))
          (ovFaultyGadget gs U fun x => ω (.inr (.inl x))) N (prepState Φ₀ fun ℓ => ω (.inl ℓ)) :=
    rfl
  rw [ioRun, hrun]
  rcases hω.meas_cases with hm | ⟨j₀, hm⟩
  · rw [hm, measChannel_none]
    obtain ⟨E, hE, hEq⟩ := hdev
    rw [id, hEq, logicalProb_cssMix hE hideal]
  · have hmf : measFlag ω = true := by
      simp only [measFlag, decide_eq_true_eq]
      exact ⟨j₀, by simpa using congrFun hm j₀⟩
    have hfin := hω.good_last
    rw [hmf] at hfin
    have hl : lastFaultFrom (prepFlag ω) (recoveryFlag fun x => ω (.inr (.inl x))) N = false := by
      cases h : lastFaultFrom (prepFlag ω) (recoveryFlag fun x => ω (.inr (.inl x))) N
      · rfl
      · rw [h] at hfin
        simp at hfin
    rw [hm, hex hl, logicalProb_cssMix (measChannel_single_mem Nm hNm j₀) hideal]

/-- ★★★ **The level-one Steane machine from preparation to read-out.** For every circuit of `N`
gadgets, unitary faults at the gadgets, channel faults on the pairs at every extraction location,
faults at every location of every ancilla factory — the input's included — and at every readout of
the final transversal measurement:

* **a pattern with at most one fault in each window** — the first extended rectangle with the input's
  factory, every later one, and the last recovery with the measurement — reads every logical value
  with its ideal probability (`logicalProb_ioRun`);
* **under independent faults of rate at most `p`** at all `46 + 113 N + 7` locations, it does so with
  probability at least `1 − 23871 (N + 1) p²`. Nothing is ideal but the classical decoding. -/
theorem steane_machine_io (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
    (hOn : ∀ j r q k, OnPair q (F j r q k)) (Φ : Fin N → MethodRound → FacFaults κ)
    (hΦ : ∀ j r, (Φ j r).Valid) {Φ₀ : FacFaults κ} (hΦ₀ : Φ₀.Valid)
    (Nm : Fin 7 → κ → Matrix (Fin 2) (Fin 2) ℂ) (hNm : ∀ j, ∑ k, (Nm j k)ᴴ * Nm j k = 1) :
    (∀ ω : IOLoc N → Bool, IOWindowsGood ω →
        logicalProb (ioRun gs U F Φ hF hΦ Φ₀ Nm hNm ω) = logicalProb (machineIdeal gs plusState))
    ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
        ν {c | c = true} ≤ ENNReal.ofReal p →
        1 - ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (23871 * p ^ 2)
          ≤ Measure.pi (fun _ : IOLoc N => ν)
              {ω | logicalProb (ioRun gs U F Φ hF hΦ Φ₀ Nm hNm ω)
                = logicalProb (machineIdeal gs plusState)} := by
  have hdet : ∀ ω : IOLoc N → Bool, IOWindowsGood ω →
      logicalProb (ioRun gs U F Φ hF hΦ Φ₀ Nm hNm ω) = logicalProb (machineIdeal gs plusState) :=
    fun ω hω => funext fun v => logicalProb_ioRun gs U hU F hF hOn Φ hΦ hΦ₀ Nm hNm hω v
  refine ⟨hdet, fun ν _ p hp hν => ?_⟩
  have hch : ((Nat.choose 219 2 : ℕ) : ℝ) = 23871 := by norm_num [Nat.choose_two_right]
  have h := one_sub_le_measure_output_eq_windows ν hp hν (w := 219) ioWindow card_ioWindow_le
    (out := fun ω => logicalProb (ioRun gs U F Φ hF hΦ Φ₀ Nm hNm ω))
    (ideal := logicalProb (machineIdeal gs plusState)) fun ω hω => hdet ω hω
  rwa [hch] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
