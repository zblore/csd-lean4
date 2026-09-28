/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneConcat
public import CsdLean4.Empirical.QM.QEC.SteaneFaultyGate

/-!
# The transversal `CNOT` across two Steane blocks, and a fault at one of its locations

**Category:** 3-Local (Empirical, QM twin). BACKLOG #62 (f), the two-block half of the transversal
gate set.

`SteaneFaultyGate.lean` (#62 (a), (b)) treats gadgets on **one** block: the transversal `X̄`, `Z̄` and
Hadamard. The remaining Clifford generator acts on **two** blocks: `CNOT` on the `q`-th qubit of each,
for all seven `q`. In the computational basis that gadget is a *permutation* of the labels,
`(u, v) ↦ (u, u + v)`, and the whole content of its transversality is that the Steane code is
**linear**: adding a codeword of the coset of `x` to the coset of `y` lands in the coset of `x + y`.

* `pairEnc` — the two-block encoder `steaneEnc ⊗ steaneEnc`, as a `blockKron` over two blocks
  (#86's layer), with `pairEnc_conjTranspose_mul`;
* `cosetAmp`, `steaneEnc_eq_cosetAmp` — the encoder's amplitudes as coset counts, and ★★
  `cosetAmp_shift` / ★★ `steaneEnc_mul_shift`: **the coset shift**, the linearity of the code in the
  form the gadget needs;
* `cnotPerm`, `cnotT` — the transversal `CNOT` as the permutation matrix of `(u, v) ↦ (u, u + v)`,
  with `cnotT_conjTranspose`, `cnotT_mul_self` (it is its own inverse) and
  `cnotT_mem_unitaryGroup`; `cnotL` is the logical `CNOT`, the same permutation on two bits;
* ★★★ `cnotT_mul_pairEnc` — **the transversal `CNOT` IS the logical `CNOT`**:
  `CNOT^{⊗7} · (V ⊗ V) = (V ⊗ V) · CNOT`, in the Schrödinger picture, so ★★
  `cnotT_conj_pairEnc_code` gives the ideal gadget's action on an encoded pair of qubits;
* `pairFam`, ★★ `encoderKL_pairFam`, ★★ `exists_pair_recovery` — one recovery channel for the two
  blocks, from Knill–Laflamme in encoder form (#86): the family is one single-qubit Pauli per block,
  and the condition composes over the blocks because `steaneEnc_pauli_pair` holds in each;
* ★★★ `steane_faultyCNOT_recovery` — **a faulty transversal `CNOT` is corrected**: one bad location
  (an arbitrary unitary on the two qubits of one `CNOT`, in product form) leaves the recovery
  returning the *ideal* output, the logical `CNOT` applied to the encoded pair.

## Honest scope

⚠️ The fault at a location is taken in **product form** `A ⊗ B` (an arbitrary single-qubit operator
on each of the two qubits of that `CNOT`). Products span the operators on two qubits, and
`recovery_apply_lin_comb` is exactly the tool that lifts the statement to sums, but the general
non-product fault is not stated: it would need a pair-register view of the two-block labels, which
this file does not build.

⚠️ The recovery is the Knill–Laflamme channel of the two-block code, not two independent per-block
recoveries; nothing here says the two blocks can be corrected separately (they can, but that needs a
tensor product of channels, which the corpus does not have).

⚠️ Faults in the *recovery* gadget — extended rectangles — are still BACKLOG #62 (c), and the
simulation theorem #62 (d).

References: A. Steane, PRL 77 (1996); M. Nielsen, I. Chuang, *Quantum Computation and Quantum
Information* §10.4.2 (CSS codes and transversal gates); P. Aliferis, D. Gottesman, J. Preskill,
Quantum Inf. Comput. 6 (2006); `Empirical/QM/QEC/SteaneConcat.lean` (#86);
`specs/BACKLOG.md` #62 (f); `specs/steane-plan.md`.
-/

@[expose] public section

open Matrix QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

open Controlled QuantumInfo.Controlled

/-! ### The two-block encoder -/

/-- The encoder of a **pair** of Steane blocks: `steaneEnc` on each, as a tensor over two blocks. -/
noncomputable def pairEnc : Matrix (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  blockKron fun _ : Fin 2 => steaneEnc

theorem pairEnc_conjTranspose_mul : pairEncᴴ * pairEnc = 1 := by
  rw [pairEnc, blockKron_conjTranspose, blockKron_mul,
    show (fun _ : Fin 2 => steaneEncᴴ * steaneEnc)
        = fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ) from
      funext fun _ => steaneEnc_conjTranspose_mul,
    blockKron_one]

theorem pairEnc_apply (z : Fin 2 → Fin 7 → Fin 2) (c : Fin 2 → Fin 2) :
    pairEnc z c = steaneEnc (z 0) (c 0) * steaneEnc (z 1) (c 1) := by
  rw [pairEnc, blockKron_apply, Fin.prod_univ_two]

/-! ### The encoder's amplitudes are coset counts -/

/-- The constant label: `0` for the code itself, the all-ones vector for the other coset. -/
def constVec (y : Fin 2) : Fin 7 → Fin 2 := fun _ => y

theorem constVec_zero : constVec 0 = 0 := rfl

theorem constVec_one : constVec 1 = allOnes := rfl

theorem constVec_add (x y : Fin 2) : constVec (x + y) = constVec x + constVec y := rfl

/-- How many row-space representatives put `z` in the coset labelled `y`. -/
noncomputable def cosetAmp (y : Fin 2) (z : Fin 7 → Fin 2) : ℂ :=
  ∑ c : Fin 3 → Fin 2, if z = rowComb c + constVec y then 1 else 0

/-- The encoder's entries are the coset counts, normalised: the logical states are the uniform
superpositions over the code and its coset. -/
theorem steaneEnc_eq_cosetAmp (z : Fin 7 → Fin 2) (y : Fin 2) :
    steaneEnc z y = (Real.sqrt 8 : ℂ)⁻¹ * cosetAmp y z := by
  rcases (by decide : ∀ t : Fin 2, t = 0 ∨ t = 1) y with rfl | rfl
  · rw [show steaneEnc z 0 = WithLp.ofLp steaneZero z from by rw [← steaneEnc_col_zero],
      steaneZero, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, cosetAmp]
    congr 1
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [basisState_apply, constVec_zero, add_zero]
  · rw [show steaneEnc z 1 = WithLp.ofLp steaneOne z from by rw [← steaneEnc_col_one],
      steaneOne, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, cosetAmp]
    congr 1
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [basisState_apply, constVec_one]

/-- ★★ **The coset shift.** If `u` lies in the coset labelled `x`, adding `u` carries the coset
labelled `y` onto the coset labelled `x + y`: the code is linear, which is the whole reason a
transversal `CNOT` is a logical `CNOT`. -/
theorem cosetAmp_shift {u : Fin 7 → Fin 2} {x : Fin 2} {c₀ : Fin 3 → Fin 2}
    (hu : u = rowComb c₀ + constVec x) (v : Fin 7 → Fin 2) (y : Fin 2) :
    cosetAmp y (u + v) = cosetAmp (x + y) v := by
  have hco : ∀ a b s t w : Fin 2, (w = b + (s + t)) ↔ (a + s + w = b + a + t) := by decide
  rw [cosetAmp, cosetAmp]
  refine (Fintype.sum_equiv (Equiv.addRight c₀) _ _ fun d => ?_).symm
  have hiff : (v = rowComb d + constVec (x + y))
      ↔ (u + v = rowComb (d + c₀) + constVec y) := by
    rw [hu, rowComb_add, constVec_add]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      simp only [Pi.add_apply, constVec] at hi ⊢
      exact (hco (rowComb c₀ i) (rowComb d i) x y (v i)).mp hi
    · intro h
      funext i
      have hi := congrFun h i
      simp only [Pi.add_apply, constVec] at hi ⊢
      exact (hco (rowComb c₀ i) (rowComb d i) x y (v i)).mpr hi
  show (if v = rowComb d + constVec (x + y) then (1 : ℂ) else 0)
    = if u + v = rowComb ((Equiv.addRight c₀) d) + constVec y then (1 : ℂ) else 0
  rw [Equiv.coe_addRight]
  exact if_congr hiff rfl rfl

/-- ★★ **The product form the gadget consumes**: on the support of the coset of `x`, shifting by `u`
relabels `y` as `x + y`. -/
theorem steaneEnc_mul_shift (u v : Fin 7 → Fin 2) (x y : Fin 2) :
    steaneEnc u x * steaneEnc (u + v) y = steaneEnc u x * steaneEnc v (x + y) := by
  by_cases h : cosetAmp x u = 0
  · rw [steaneEnc_eq_cosetAmp u x, h]
    ring
  · obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin 3 → Fin 2, u = rowComb c₀ + constVec x := by
      by_contra hcon
      refine h ?_
      rw [cosetAmp]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg fun hcc => hcon ⟨c, hcc⟩]
    rw [steaneEnc_eq_cosetAmp (u + v) y, steaneEnc_eq_cosetAmp v (x + y), cosetAmp_shift hc₀]

/-! ### The transversal `CNOT` -/

/-- The label permutation of the transversal `CNOT`: the control block is unchanged, the target
block is added the control, qubit by qubit. -/
def cnotPerm (z : Fin 2 → Fin 7 → Fin 2) : Fin 2 → Fin 7 → Fin 2 := ![z 0, z 0 + z 1]

theorem cnotPerm_involutive : Function.Involutive cnotPerm := by
  intro z
  funext b
  have hself : ∀ w : Fin 7 → Fin 2, w + w = 0 := by
    intro w
    funext i
    exact (by decide : ∀ a : Fin 2, a + a = 0) _
  fin_cases b
  · rfl
  · show z 0 + (z 0 + z 1) = z 1
    rw [← add_assoc, hself, zero_add]

/-- The logical `CNOT`, the same permutation on two bits. -/
def cnotPermL (c : Fin 2 → Fin 2) : Fin 2 → Fin 2 := ![c 0, c 0 + c 1]

theorem cnotPermL_involutive : Function.Involutive cnotPermL := by
  intro c
  funext b
  fin_cases b
  · rfl
  · show c 0 + (c 0 + c 1) = c 1
    rw [← add_assoc, (by decide : ∀ a : Fin 2, a + a = 0) (c 0), zero_add]

/-- The **transversal `CNOT`** on two blocks: `CNOT` between the `q`-th qubits, for every `q` — the
permutation matrix of `cnotPerm`. -/
noncomputable def cnotT : Matrix (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 7 → Fin 2) ℂ :=
  permMat cnotPerm

/-- The logical `CNOT` on the two encoded qubits. -/
noncomputable def cnotL : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  permMat cnotPermL

theorem cnotT_conjTranspose : cnotTᴴ = cnotT :=
  permMat_conjTranspose cnotPerm_involutive

theorem cnotT_mul_self : cnotT * cnotT = 1 :=
  permMat_mul_self cnotPerm_involutive

theorem cnotT_mem_unitaryGroup : cnotT ∈ Matrix.unitaryGroup (Fin 2 → Fin 7 → Fin 2) ℂ :=
  permMat_mem_unitaryGroup cnotPerm_involutive

theorem cnotL_conjTranspose : cnotLᴴ = cnotL :=
  permMat_conjTranspose cnotPermL_involutive

theorem cnotL_mul_self : cnotL * cnotL = 1 :=
  permMat_mul_self cnotPermL_involutive

/-- ★★★ **The transversal `CNOT` is the logical `CNOT`.** Conjugating the pair encoder by the
gadget is the logical gate on the two encoded qubits — the Schrödinger-picture statement, with the
coset shift as the only input. -/
theorem cnotT_mul_pairEnc : cnotT * pairEnc = pairEnc * cnotL := by
  ext z c
  rw [cnotT, cnotL, permMat_mul_apply cnotPerm_involutive, mul_permMat_apply, pairEnc_apply,
    pairEnc_apply]
  show steaneEnc (z 0) (c 0) * steaneEnc (z 0 + z 1) (c 1)
    = steaneEnc (z 0) (c 0) * steaneEnc (z 1) (c 0 + c 1)
  exact steaneEnc_mul_shift (z 0) (z 1) (c 0) (c 1)

/-- ★★ The ideal gadget on an encoded pair: the logical `CNOT`, conjugated into the code. -/
theorem cnotT_conj_pairEnc_code (ρ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    cnotT * (pairEnc * ρ * pairEncᴴ) * cnotTᴴ
      = pairEnc * (cnotL * ρ * cnotLᴴ) * pairEncᴴ := by
  rw [cnotT_conjTranspose]
  calc cnotT * (pairEnc * ρ * pairEncᴴ) * cnotT
      = (cnotT * pairEnc) * ρ * (cnotT * pairEnc)ᴴ := by
        rw [Matrix.conjTranspose_mul, cnotT_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = (pairEnc * cnotL) * ρ * (pairEnc * cnotL)ᴴ := by rw [cnotT_mul_pairEnc]
    _ = pairEnc * (cnotL * ρ * cnotLᴴ) * pairEncᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/-! ### The two-block recovery -/

/-- The error family of the pair: one single-qubit Pauli in each block. -/
noncomputable def pairFam (g : Fin 2 → SingleErr) : Matrix (Fin 2 → Fin 7 → Fin 2)
    (Fin 2 → Fin 7 → Fin 2) ℂ :=
  blockKron fun b => pauliMat (errA (g b)) (errB (g b))

/-- ★★ **Knill–Laflamme in encoder form for the pair**: it composes over the blocks, because it
holds in each (`steaneEnc_pauli_pair`). -/
theorem encoderKL_pairFam : EncoderKL pairEnc pairFam := by
  intro g h
  refine ⟨∏ b, (1 : Matrix SingleErr SingleErr ℂ) (g b) (h b), ?_⟩
  rw [pairFam, pairFam, pairEnc, blockKron_conjTranspose, blockKron_conjTranspose,
    blockKron_mul, blockKron_mul, blockKron_mul,
    show (fun b : Fin 2 => steaneEncᴴ * (pauliMat (errA (g b)) (errB (g b)))ᴴ
        * pauliMat (errA (h b)) (errB (h b)) * steaneEnc)
        = fun b : Fin 2 => (1 : Matrix SingleErr SingleErr ℂ) (g b) (h b) • 1 from
      funext fun b => steaneEnc_pauli_pair (g b) (h b),
    blockKron_smul, blockKron_one]

/-- ★★ **One recovery channel for the two blocks.** -/
theorem exists_pair_recovery :
    ∃ (c : Matrix (Fin 2 → SingleErr) (Fin 2 → SingleErr) ℂ)
      (R : Channel (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 7 → Fin 2)
        (Option (Fin 2 → SingleErr))),
      ∀ ρ : Matrix (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 7 → Fin 2) ℂ,
        ρ = pairEnc * pairEncᴴ * ρ * (pairEnc * pairEncᴴ) →
        ∀ g h, R.apply (pairFam g * ρ * (pairFam h)ᴴ) = c h g • ρ :=
  exists_recovery_of_encoderKL pairEnc_conjTranspose_mul encoderKL_pairFam

/-! ### A fault at one location of the gadget -/

/-- A product fault on the two qubits of the `q`-th `CNOT`: an arbitrary single-qubit operator on
each block's `q`-th qubit. -/
noncomputable def pairFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 7 → Fin 2) ℂ :=
  blockKron ![gateOf q A, gateOf q B]

/-- The fault is a combination of the family: the Paulis span the operators of a qubit
(`gateOf_eq_sum_pauliMat`) and the tensor over blocks is multilinear. -/
theorem pairFault_eq_sum (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pairFault q A B
      = ∑ g : Fin 2 → SingleErr,
          (∏ b, (![singleCoeff q A, singleCoeff q B] : Fin 2 → SingleErr → ℂ) b (g b))
            • pairFam g := by
  rw [pairFault,
    show (![gateOf q A, gateOf q B] : Fin 2 → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
        = fun b => ∑ i : SingleErr,
            (![singleCoeff q A, singleCoeff q B] : Fin 2 → SingleErr → ℂ) b i
              • pauliMat (errA i) (errB i) from by
      funext b
      fin_cases b
      · exact gateOf_eq_sum_pauliMat q A
      · exact gateOf_eq_sum_pauliMat q B,
    blockKron_sum_smul]
  rfl

/-! ### A faulty transversal `CNOT` is corrected -/

theorem pairFault_conjTranspose_mul {q : Fin 7} {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (pairFault q A B)ᴴ * pairFault q A B = 1 := by
  have hgate : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      (gateOf q M)ᴴ * gateOf q M = (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) := by
    intro M hM
    rw [← blockKron_single_eq_gateOf, blockKron_conjTranspose, blockKron_mul,
      show (fun b : Fin 7 => (if b = q then M else 1)ᴴ * (if b = q then M else 1))
          = fun _ : Fin 7 => (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
        funext b
        by_cases h : b = q
        · rw [if_pos h, ← Matrix.star_eq_conjTranspose]
          exact Matrix.mem_unitaryGroup_iff'.mp hM
        · rw [if_neg h, Matrix.conjTranspose_one, one_mul],
      blockKron_one]
  rw [pairFault, blockKron_conjTranspose, blockKron_mul,
    show (fun b : Fin 2 => (![gateOf q A, gateOf q B] b)ᴴ * ![gateOf q A, gateOf q B] b)
        = fun _ : Fin 2 => (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) from by
      funext b
      fin_cases b
      · exact hgate A hA
      · exact hgate B hB,
    blockKron_one]

theorem trace_pairEnc_conj (ρ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    (pairEnc * ρ * pairEncᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_cycle, pairEnc_conjTranspose_mul, Matrix.one_mul]

theorem trace_cnotL_conj (ρ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) :
    (cnotL * ρ * cnotLᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_cycle, cnotL_conjTranspose, cnotL_mul_self, Matrix.one_mul]

set_option maxRecDepth 4000 in
/-- ★★★ **A faulty transversal `CNOT` is corrected.** The gadget is `CNOT` between the `q`-th qubits
of the two blocks for every `q` — the logical `CNOT`, by `cnotT_mul_pairEnc` — and one of its seven
locations is faulty, the fault an arbitrary unitary on each of that location's two qubits. One
channel returns the **ideal** output: the logical `CNOT` applied to the encoded pair. -/
theorem steane_faultyCNOT_recovery :
    ∃ R : Channel (Fin 2 → Fin 7 → Fin 2) (Fin 2 → Fin 7 → Fin 2)
        (Option (Fin 2 → SingleErr)),
      ∀ (ρ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) (q : Fin 7)
        (A B : Matrix (Fin 2) (Fin 2) ℂ), A ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        B ∈ Matrix.unitaryGroup (Fin 2) ℂ → ρ.trace ≠ 0 →
        R.apply (pairFault q A B * (cnotT * (pairEnc * ρ * pairEncᴴ) * cnotTᴴ)
              * (pairFault q A B)ᴴ)
          = pairEnc * (cnotL * ρ * cnotLᴴ) * pairEncᴴ := by
  obtain ⟨c, R, hR⟩ := exists_pair_recovery
  refine ⟨R, fun ρ q A B hA hB htr => ?_⟩
  have hcode : ∀ τ : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ,
      pairEnc * τ * pairEncᴴ
        = pairEnc * pairEncᴴ * (pairEnc * τ * pairEncᴴ) * (pairEnc * pairEncᴴ) := by
    intro τ
    calc pairEnc * τ * pairEncᴴ
        = pairEnc * (τ * pairEncᴴ) := by rw [Matrix.mul_assoc]
      _ = pairEnc * ((pairEncᴴ * pairEnc) * τ * ((pairEncᴴ * pairEnc) * pairEncᴴ)) := by
          rw [pairEnc_conjTranspose_mul, Matrix.one_mul, Matrix.one_mul]
      _ = pairEnc * pairEncᴴ * (pairEnc * τ * pairEncᴴ) * (pairEnc * pairEncᴴ) := by
          simp only [Matrix.mul_assoc]
  have htrσ : (pairEnc * (cnotL * ρ * cnotLᴴ) * pairEncᴴ).trace ≠ 0 := by
    rw [trace_pairEnc_conj, trace_cnotL_conj]
    exact htr
  have hsum := recovery_apply_lin_comb (P := pairEnc * pairEncᴴ) hR
    (fun g => ∏ b, (![singleCoeff q A, singleCoeff q B] : Fin 2 → SingleErr → ℂ) b (g b))
    (hcode (cnotL * ρ * cnotLᴴ))
  rw [← pairFault_eq_sum] at hsum
  rw [cnotT_conj_pairEnc_code, hsum,
    smul_eq_one_of_unitary R (pairFault_conjTranspose_mul hA hB) hsum htrσ, one_smul]

end Steane
end QEC
end QM
end Empirical
end CSD

end
