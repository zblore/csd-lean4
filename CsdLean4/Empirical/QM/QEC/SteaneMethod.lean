/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneCircuitRecovery

/-!
# Steane's method, and one fault in it

**Category:** 3-Local (Empirical, QM twin). BACKLOG #229, first brick (split 2026-10-29; the rest is
#232–#234).

The recovery of ~~#228~~ reads each syndrome through one unverified ancilla block per check, which is
not fault-tolerant: a single phase fault on a shared ancilla spreads to every data qubit it touched
(#95). **Steane's method** reads the syndrome through an *encoded* ancilla instead — the logical
`|+̄⟩`, a transversal `CNOT`, the ancilla read in full, and the syndrome computed classically from the
word read. Every gate touches one data qubit, so a fault cannot spread inside the block.

## The method, as gates

* `ancPrep`, ★★ `ancRead_mul_extractMat_mul_ancPrep` — **prepare `ψ`, extract, read `m` is the
  diagonal operator `ψ(m + H z)` on the data** (generic; `ancInit` is the case `ψ = |0⟩`);
  `ancRead_mul_kronecker` — reading after a product operator moves the read word;
* `plusAnc`, `tCNOT`, `steaneRead`, ★★ `steaneRead_eq` — **with `|+̄⟩`, a transversal `CNOT` and the
  ancilla read as `m`, the data is projected onto the syndrome of `m`**, a quarter of `bitProj`: the
  syndrome is learned, the encoded qubit is not;
* `card_syndrome_fiber`, `sum_syndrome`, `sum_outPair` — sixteen read words per syndrome;
* `bitRound`, `phaseRound` (the same in the Hadamard basis), `methodKraus`, ★★ `methodKraus_eq`
  (a branch is `±1/16` of a branch of ~~#228~~'s circuit), `methodKraus_tp`, `methodRecovery`;
  ★★★ `methodRecovery_apply` — **Steane's method and the recovery circuit are the same channel, on
  every input**, so everything ~~#228~~ proved of the circuit holds of the method.

## One fault

A fault at an **extraction location** `q` of a round — the transversal `CNOT` on data qubit `q` and
ancilla qubit `q`, or ancilla qubit `q` before it is read (a measurement fault) — is an arbitrary
operator `A ⊗ B` on those two qubits.

* `AtQubit q K` — `K` acts on the code as an operator on data qubit `q` alone (`K P = M_q P`), closed
  under sums, scalars and operators on `q`;
* `faultRead`, ★★ `faultRead_mul_steaneProj` — on the code a faulty readout is the data fault,
  weighted; ★★ `syndrome_of_faultCoeff_ne_zero` — **the read word moves at most at `q`**, so it reads
  nothing or the flip at `q`;
* ★★ `atQubit_bitFault`, ★★ `atQubit_phaseFault` — one fault in either round leaves an error on qubit
  `q` alone: the correction, if any, is at `q` too;
* ★★ `AtQubit.phaseRound_mul` — a fault-free phase round keeps an error on `q` on `q`;
  `bitRound_mul_steaneProj` — a fault-free bit round passes a code state through;
* ★★★ `steaneMethod_single_fault` — **one fault at any extraction location of Steane's method, the
  rest fault-free: every branch acts on the code as an operator on one data qubit**;
  ★★★ `steaneMethod_single_fault_apply` — on a code state the output is `Σ_b M_b ρ M_bᴴ` with every
  `M_b` on that qubit.

## Honest scope

⚠️ **Ancilla preparation is ideal here.** A fault while preparing `|+̄⟩` can leave the ancilla with a
`Z` error of weight two or more, which the transversal `CNOT` copies onto the data. The verification
that rejects such ancillas, and the prep-fault case of the theorem, are BACKLOG #234.

⚠️ **Extraction locations only.** Faults on the data between rounds or after the correction are
operators on one qubit by definition and are not restated; faults in the classical decoding are not
modelled.

⚠️ **Not yet in the machine.** The single-fault output is a mixture of errors on one qubit; turning it
into #96's `DeviatesBy` for a correctable set that the recovery corrects and the gadgets propagate is
BACKLOG #232, and counting the recovery's locations in the machine — overlapping extended rectangles —
is #233.

⚠️ **One round per basis**, as in ~~#228~~: no repetition of the syndrome measurement.

References: A. Steane, *Active stabilization, quantum computation, and quantum state synthesis*,
PRL 78 (1997) 2252; P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97;
`specs/BACKLOG.md` #229, #232, #233, #234, #228, #95, #96; `Empirical/QM/QEC/SteaneCircuitRecovery.lean`,
`Mathlib/QuantumInfo/SyndromeExtraction.lean`, `Empirical/QM/QEC/SteaneArbitrary.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker

noncomputable section

/-! ### An ancilla block prepared in a given state -/

namespace QuantumInfo

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [AddCommGroup β]

/-- **Preparing the ancilla block in the state `ψ`**: `z ↦ z ⊗ ψ`. -/
def ancPrep (ψ : β → ℂ) : Matrix (α × β) α ℂ := Matrix.of fun p z => if p.1 = z then ψ p.2 else 0

/-- ★★ **Prepare `ψ`, extract, read `m`: a diagonal operator on the data**, with entry `ψ(m + H z)`
at `z`. For `ψ` the all-zero state this is `ancRead_mul_extractMat_mul_ancInit`. -/
theorem ancRead_mul_extractMat_mul_ancPrep {H : α → β} (hH : ∀ z, H z + H z = 0) (m : β)
    (ψ : β → ℂ) :
    ancRead m * extractMat H * (ancPrep ψ : Matrix (α × β) α ℂ)
      = Matrix.diagonal fun z => ψ (m + H z) := by
  ext z w
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (z, m)]
  · rw [extractMat, permMat_mul_apply (extractPerm_involutive hH)]
    simp only [ancRead, ancPrep, Matrix.of_apply, ite_true, one_mul, extractPerm,
      Matrix.diagonal_apply]
  · intro p _ hp
    simp [ancRead, hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [AddCommGroup β] in
/-- **Reading the ancilla after a product operator on data and ancilla**: the ancilla factor moves
the readout, `⟨m| (A ⊗ B) = Σ_{m'} B_{m m'} A ⟨m'|`. -/
theorem ancRead_mul_kronecker (m : β) (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    ancRead m * (A ⊗ₖ B) = ∑ m', B m m' • (A * ancRead m') := by
  ext z ⟨w, b⟩
  have hl : (ancRead m * (A ⊗ₖ B) : Matrix α (α × β) ℂ) z (w, b) = A z w * B m b := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (z, m)]
    · simp [ancRead]
    · intro q _ hq
      simp [ancRead, hq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hr : ∀ m' : β, (A * ancRead m' : Matrix α (α × β) ℂ) z (w, b) = if b = m' then A z w else 0 := by
    intro m'
    rw [Matrix.mul_apply, Finset.sum_eq_single w]
    · by_cases h : b = m' <;> simp [ancRead, h]
    · intro w' _ hw'
      simp [ancRead, Prod.ext_iff, Ne.symm hw']
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hl, Matrix.sum_apply, Finset.sum_eq_single b]
  · rw [Matrix.smul_apply, hr, ite_eq_left rfl, smul_eq_mul, mul_comm]
  · intro m' _ hm'
    rw [Matrix.smul_apply, hr, ite_eq_right (Ne.symm hm'), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### Steane's encoded ancilla and the transversal `CNOT` -/

/-- **Steane's ancilla `|+̄⟩`**: the uniform superposition over the sixteen Hamming codewords. -/
def plusAnc (a : Fin 7 → Fin 2) : ℂ := if syndrome a = 0 then 1 / 4 else 0

/-- The transversal `CNOT` from the data block into the ancilla block: `(z, a) ↦ (z, a + z)`. -/
abbrev tCNOT : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ :=
  extractMat (id : (Fin 7 → Fin 2) → (Fin 7 → Fin 2))

theorem id_add_self (z : Fin 7 → Fin 2) : id z + id z = 0 := by
  funext i
  exact fin2_add_self _

/-- The readout of Steane's extraction, read as `m`. -/
abbrev steaneRead (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  ancRead m * tCNOT * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

/-- ★★ **Steane's extraction is the syndrome measurement**: with the ancilla in `|+̄⟩`, a transversal
`CNOT` and the ancilla read as `m`, the data is projected onto the syndrome of `m` — only the
syndrome is learned, the encoded qubit is not. -/
theorem steaneRead_eq (m : Fin 7 → Fin 2) :
    steaneRead m = (1 / 4 : ℂ) • bitProj (syndrome m) := by
  rw [steaneRead, ancRead_mul_extractMat_mul_ancPrep id_add_self]
  simp only [bitProj, synProj, ← Matrix.diagonal_smul]
  congr 1
  funext z
  simp only [plusAnc, id, Pi.smul_apply, smul_eq_mul, syndrome_add]
  by_cases h : syndrome z = syndrome m
  · rw [ite_eq_left (synVec_add_eq_zero_iff.2 h.symm), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun h' => h (synVec_add_eq_zero_iff.1 h').symm), ite_eq_right h, mul_zero]

/-- **Every syndrome is read by sixteen ancilla outcomes.** -/
theorem card_syndrome_fiber (t : Fin 3 → Fin 2) :
    (Finset.univ.filter fun m : Fin 7 → Fin 2 => syndrome m = t).card = 16 := by
  revert t
  decide

theorem sum_syndrome {M : Type*} [AddCommMonoid M] (f : (Fin 3 → Fin 2) → M) :
    ∑ m : Fin 7 → Fin 2, f (syndrome m) = 16 • ∑ t, f t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := syndrome) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.1 hm).2]), Finset.sum_const,
    card_syndrome_fiber]

/-! ### The two rounds of Steane's method -/

/-- **The bit round**: extract with `|+̄⟩`, read `m`, correct `X^{decode(syn m)}`. -/
def bitRound (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode (syndrome m)) 0 * steaneRead m

/-- **The phase round**: the bit round's extraction in the Hadamard basis, then `Z^{decode(syn m)}`. -/
def phaseRound (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat 0 (decode (syndrome m)) * (hadTransversal 7 * steaneRead m * hadTransversal 7)

theorem bitRound_eq (m : Fin 7 → Fin 2) :
    bitRound m = (1 / 4 : ℂ) • (pauliMat (decode (syndrome m)) 0 * bitProj (syndrome m)) := by
  rw [bitRound, steaneRead_eq, Matrix.mul_smul]

theorem phaseRound_eq (m : Fin 7 → Fin 2) :
    phaseRound m = (1 / 4 : ℂ) • (pauliMat 0 (decode (syndrome m)) * phaseProj (syndrome m)) := by
  rw [phaseRound, steaneRead_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, phaseProj]

/-- An `X`-type Pauli commutes with every phase-syndrome projector. -/
theorem pauliMat_X_mul_phaseProj (a : Fin 7 → Fin 2) (t : Fin 3 → Fin 2) :
    pauliMat a 0 * phaseProj t = phaseProj t * pauliMat a 0 := by
  have hTT : hadTransversal 7 * hadTransversal 7 = 1 := hadTransversal_mul_self
  have hc : hadTransversal 7 * pauliMat a 0 * hadTransversal 7 = pauliMat 0 a := by
    rw [hadTransversal_conj_pauliMat, bdot_zero_right, signChar_zero, one_smul]
  have hX : pauliMat a 0 = hadTransversal 7 * pauliMat 0 a * hadTransversal 7 := by
    rw [← hc]
    calc pauliMat a 0 = (hadTransversal 7 * hadTransversal 7) * pauliMat a 0
          * (hadTransversal 7 * hadTransversal 7) := by rw [hTT, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hZ : bitProj t * pauliMat 0 a = pauliMat 0 a * bitProj t := by
    rw [bitProj_mul_pauliMat, syndrome_zero, add_zero]
  rw [hX, phaseProj]
  calc hadTransversal 7 * pauliMat 0 a * hadTransversal 7
        * (hadTransversal 7 * bitProj t * hadTransversal 7)
      = hadTransversal 7 * (pauliMat 0 a * bitProj t) * hadTransversal 7 := by
        rw [show hadTransversal 7 * pauliMat 0 a * hadTransversal 7
            * (hadTransversal 7 * bitProj t * hadTransversal 7)
            = hadTransversal 7 * pauliMat 0 a * (hadTransversal 7 * hadTransversal 7) * bitProj t
              * hadTransversal 7 by simp only [Matrix.mul_assoc], hTT, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = hadTransversal 7 * (bitProj t * pauliMat 0 a) * hadTransversal 7 := by rw [hZ]
    _ = hadTransversal 7 * bitProj t * hadTransversal 7
          * (hadTransversal 7 * pauliMat 0 a * hadTransversal 7) := by
        rw [show hadTransversal 7 * bitProj t * hadTransversal 7
            * (hadTransversal 7 * pauliMat 0 a * hadTransversal 7)
            = hadTransversal 7 * bitProj t * (hadTransversal 7 * hadTransversal 7) * pauliMat 0 a
              * hadTransversal 7 by simp only [Matrix.mul_assoc], hTT, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

/-- The outcome pair of Steane's method: the bit round's ancilla word, then the phase round's. -/
abbrev OutPair : Type := (Fin 7 → Fin 2) × (Fin 7 → Fin 2)

/-- ★ **One branch of Steane's method, as gates**: the bit round, then the phase round. -/
def methodKraus (mm : OutPair) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  phaseRound mm.2 * bitRound mm.1

/-- ★★ **A branch of Steane's method is a sixteenth of a branch of the recovery circuit**, up to a
sign: the correction `Z^{dec t}` commutes past nothing it does not commute with, and
`Z^{b} X^{a} = ± X^{a} Z^{b}`. -/
theorem methodKraus_eq (mm : OutPair) :
    methodKraus mm = ((1 / 16 : ℂ) * pauliSign (decode (syndrome mm.2)) (decode (syndrome mm.1)))
      • recKraus (syndrome mm.1, syndrome mm.2) := by
  rw [methodKraus, bitRound_eq, phaseRound_eq, recKraus_eq, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have h := pauliMat_X_mul_phaseProj (decode (syndrome mm.1)) (syndrome mm.2)
  have hp := pauliMat_mul (0 : Fin 7 → Fin 2) (decode (syndrome mm.2)) (decode (syndrome mm.1)) 0
  rw [zero_add, add_zero] at hp
  calc ((1 / 4 : ℂ) * (1 / 4)) • (pauliMat 0 (decode (syndrome mm.2)) * phaseProj (syndrome mm.2)
        * (pauliMat (decode (syndrome mm.1)) 0 * bitProj (syndrome mm.1)))
      = ((1 / 4 : ℂ) * (1 / 4)) • (pauliMat 0 (decode (syndrome mm.2))
          * (phaseProj (syndrome mm.2) * pauliMat (decode (syndrome mm.1)) 0)
          * bitProj (syndrome mm.1)) := by simp only [Matrix.mul_assoc]
    _ = ((1 / 4 : ℂ) * (1 / 4)) • ((pauliMat 0 (decode (syndrome mm.2))
          * pauliMat (decode (syndrome mm.1)) 0) * phaseProj (syndrome mm.2)
          * bitProj (syndrome mm.1)) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hp, Matrix.smul_mul, Matrix.smul_mul, smul_smul]
        congr 1
        ring

/-- **Every syndrome pair is read by `256` outcome pairs.** -/
theorem sum_outPair {M : Type*} [AddCommMonoid M] (g : SynPair → M) :
    ∑ mm : OutPair, g (syndrome mm.1, syndrome mm.2) = 256 • ∑ st : SynPair, g st := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc ∑ m, ∑ m', g (syndrome m, syndrome m')
      = ∑ m, 16 • ∑ t, g (syndrome m, t) :=
        Finset.sum_congr rfl fun m _ => sum_syndrome (fun t => g (syndrome m, t))
    _ = 16 • ∑ m, ∑ t, g (syndrome m, t) := by rw [Finset.smul_sum]
    _ = 16 • (16 • ∑ s, ∑ t, g (s, t)) := by rw [sum_syndrome (fun s => ∑ t, g (s, t))]
    _ = 256 • ∑ s, ∑ t, g (s, t) := by rw [smul_smul]; norm_num

/-- The scalar of a branch has modulus `1/16`. -/
theorem methodScalar_mul_star (mm : OutPair) :
    ((1 / 16 : ℂ) * pauliSign (decode (syndrome mm.2)) (decode (syndrome mm.1)))
      * star ((1 / 16 : ℂ) * pauliSign (decode (syndrome mm.2)) (decode (syndrome mm.1)))
      = 1 / 256 := by
  rw [star_mul', Complex.star_def, conj_pauliSign, map_div₀, map_one, map_ofNat]
  have hs := pauliSign_mul_self (decode (syndrome mm.2)) (decode (syndrome mm.1))
  linear_combination (1 / 256 : ℂ) * hs

/-- **The branches of Steane's method form a channel.** -/
theorem methodKraus_tp : ∑ mm : OutPair, (methodKraus mm)ᴴ * methodKraus mm = 1 := by
  have hterm : ∀ mm : OutPair, (methodKraus mm)ᴴ * methodKraus mm
      = (1 / 256 : ℂ) • ((recKraus (syndrome mm.1, syndrome mm.2))ᴴ
          * recKraus (syndrome mm.1, syndrome mm.2)) := by
    intro mm
    rw [methodKraus_eq, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm,
      methodScalar_mul_star]
  rw [Finset.sum_congr rfl fun mm _ => hterm mm, ← Finset.smul_sum,
    show (∑ mm : OutPair, (recKraus (syndrome mm.1, syndrome mm.2))ᴴ
        * recKraus (syndrome mm.1, syndrome mm.2))
      = 256 • ∑ st : SynPair, (recKraus st)ᴴ * recKraus st
      from sum_outPair (fun st => (recKraus st)ᴴ * recKraus st),
    recKraus_tp, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- ★★ **Steane's method as a channel**: the transversal `CNOT` into an encoded ancilla, read, decoded
and corrected, once in each basis. -/
def methodRecovery : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) OutPair where
  kraus := methodKraus
  tp := methodKraus_tp

/-- ★★★ **Steane's method implements the recovery circuit.** As channels, the encoded-ancilla
extraction of Steane's method and the recovery circuit of ~~#228~~ are the same map, on every input:
each syndrome pair is read by `256` outcome pairs, each branch a sixteenth of the circuit's. -/
theorem methodRecovery_apply (X : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    methodRecovery.apply X = circuitRecovery.apply X := by
  have hterm : ∀ mm : OutPair, methodKraus mm * X * (methodKraus mm)ᴴ
      = (1 / 256 : ℂ) • (recKraus (syndrome mm.1, syndrome mm.2) * X
          * (recKraus (syndrome mm.1, syndrome mm.2))ᴴ) := by
    intro mm
    rw [methodKraus_eq, conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, methodScalar_mul_star]
  show ∑ mm : OutPair, methodKraus mm * X * (methodKraus mm)ᴴ
    = ∑ st : SynPair, recKraus st * X * (recKraus st)ᴴ
  rw [Finset.sum_congr rfl fun mm _ => hterm mm, ← Finset.smul_sum,
    show (∑ mm : OutPair, recKraus (syndrome mm.1, syndrome mm.2) * X
        * (recKraus (syndrome mm.1, syndrome mm.2))ᴴ)
      = 256 • ∑ st : SynPair, recKraus st * X * (recKraus st)ᴴ
      from sum_outPair (fun st => recKraus st * X * (recKraus st)ᴴ),
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-! ### Errors on one data qubit -/

theorem gateOf_zero (q : Fin 7) : gateOf q (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  ext z w
  by_cases hag : ∀ i, i ≠ q → z i = w i
  · rw [gateOf_apply_of_agree hag]
    rfl
  · rw [gateOf_apply_of_not_agree hag]
    rfl

/-- **`K` acts on the code as an operator on data qubit `q` alone**: `K P = M_q P`. -/
def AtQubit (q : Fin 7) (K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℂ, K * steaneProj = gateOf q M * steaneProj

namespace AtQubit

variable {q : Fin 7}

theorem zero : AtQubit q 0 := ⟨0, by rw [gateOf_zero]⟩

theorem of_gateOf (M : Matrix (Fin 2) (Fin 2) ℂ) : AtQubit q (gateOf q M) := ⟨M, rfl⟩

theorem add {K L : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hK : AtQubit q K)
    (hL : AtQubit q L) : AtQubit q (K + L) := by
  obtain ⟨M, hM⟩ := hK
  obtain ⟨N, hN⟩ := hL
  exact ⟨M + N, by rw [Matrix.add_mul, hM, hN, gateOf_add, Matrix.add_mul]⟩

theorem smul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hK : AtQubit q K) (c : ℂ) :
    AtQubit q (c • K) := by
  obtain ⟨M, hM⟩ := hK
  exact ⟨c • M, by rw [Matrix.smul_mul, hM, gateOf_smul, Matrix.smul_mul]⟩

theorem sum {ι : Type*} (s : Finset ι) {K : ι → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : ∀ i ∈ s, AtQubit q (K i)) : AtQubit q (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add (hK a (Finset.mem_insert_self a s))
      (ih fun i hi => hK i (Finset.mem_insert_of_mem hi))

theorem gateOf_mul {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hK : AtQubit q K)
    (N : Matrix (Fin 2) (Fin 2) ℂ) : AtQubit q (gateOf q N * K) := by
  obtain ⟨M, hM⟩ := hK
  exact ⟨N * M, by rw [Matrix.mul_assoc, hM, ← Matrix.mul_assoc, ← Controlled.gateOf_mul]⟩

end AtQubit

/-- A word that agrees with `m` off qubit `q` is `m` or `m` with bit `q` flipped. -/
theorem eq_or_eq_add_unitErr_of_agree {m m' : Fin 7 → Fin 2} {q : Fin 7}
    (h : ∀ i, i ≠ q → m i = m' i) : m' = m ∨ m' = m + unitErr q := by
  by_cases hq : m' q = m q
  · left
    funext i
    by_cases hi : i = q
    · rw [hi, hq]
    · exact (h i hi).symm
  · right
    funext i
    rw [Pi.add_apply, unitErr_apply]
    by_cases hi : i = q
    · subst hi
      rw [ite_eq_left rfl]
      revert hq
      generalize m' i = x
      generalize m i = y
      revert x y
      decide
    · rw [ite_eq_right hi, add_zero, h i hi]

/-! ### One fault at an extraction location -/

/-- **Steane's extraction with one fault at location `q`**: an operator `A ⊗ B` on data qubit `q` and
ancilla qubit `q` after the transversal `CNOT` — a fault on the `CNOT` at `q`, or (with `A = 1`) on
the ancilla qubit before it is read, which is a measurement fault. -/
def faultRead (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    * (gateOf q A ⊗ₖ gateOf q B) * tCNOT
    * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

theorem faultRead_eq (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    faultRead q A B m = ∑ m', gateOf q B m m' • (gateOf q A * steaneRead m') := by
  rw [faultRead, ancRead_mul_kronecker, Matrix.sum_mul, Matrix.sum_mul]
  simp only [Matrix.smul_mul, Matrix.mul_assoc]

/-- The weight the fault's readout leaves on the code. -/
def faultCoeff (q : Fin 7) (B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) : ℂ :=
  ∑ m', if syndrome m' = 0 then gateOf q B m m' / 4 else 0

/-- ★★ **On the code, a faulty readout is the data fault, weighted.** -/
theorem faultRead_mul_steaneProj (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    faultRead q A B m * steaneProj = faultCoeff q B m • (gateOf q A * steaneProj) := by
  rw [faultRead_eq, Finset.sum_mul, faultCoeff, Finset.sum_smul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_assoc, steaneRead_eq, Matrix.smul_mul, bitProj_mul_steaneProj]
  by_cases h : syndrome m' = 0
  · rw [ite_eq_left h, ite_eq_left h, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  · rw [ite_eq_right h, ite_eq_right h, smul_zero, Matrix.mul_zero, smul_zero, zero_smul]

/-- ★★ **A faulty readout that leaves anything on the code reads either nothing or the syndrome of a
flip at `q`**: the fault moves the read word at most at `q`. -/
theorem syndrome_of_faultCoeff_ne_zero {q : Fin 7} {B : Matrix (Fin 2) (Fin 2) ℂ}
    {m : Fin 7 → Fin 2} (h : faultCoeff q B m ≠ 0) :
    syndrome m = 0 ∨ syndrome m = syndrome (unitErr q) := by
  obtain ⟨m', _, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hs : syndrome m' = 0
  · rw [ite_eq_left hs] at hm'
    have hag : ∀ i, i ≠ q → m i = m' i := by
      by_contra hag
      apply hm'
      rw [gateOf_apply_of_not_agree hag, zero_div]
    rcases eq_or_eq_add_unitErr_of_agree hag with rfl | rfl
    · exact Or.inl hs
    · right
      rw [syndrome_add] at hs
      exact synVec_add_eq_zero_iff.1 hs
  · rw [ite_eq_right hs] at hm'
    exact absurd rfl hm'

/-- **The bit round with one fault at extraction location `q`.** -/
def bitFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode (syndrome m)) 0 * faultRead q A B m

/-- **The phase round with one fault at extraction location `q`.** -/
def phaseFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat 0 (decode (syndrome m)) * (hadTransversal 7 * faultRead q A B m * hadTransversal 7)

/-- ★★ **One fault in the bit round leaves an error on qubit `q` alone**, whatever is read: either the
read word is clean and no correction is made, or it reads the flip at `q` and the correction is at
`q` too. -/
theorem atQubit_bitFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    AtQubit q (bitFault q A B m) := by
  have hr := faultRead_mul_steaneProj q A B m
  by_cases hc : faultCoeff q B m = 0
  · exact ⟨0, by rw [bitFault, Matrix.mul_assoc, hr, hc, zero_smul, Matrix.mul_zero, gateOf_zero,
      Matrix.zero_mul]⟩
  rcases syndrome_of_faultCoeff_ne_zero hc with h | h
  · exact ⟨faultCoeff q B m • A, by
      rw [bitFault, Matrix.mul_assoc, hr, h, decode_zero, pauliMat_zero, Matrix.one_mul,
        gateOf_smul, Matrix.smul_mul]⟩
  · exact ⟨faultCoeff q B m • (pX * A), by
      rw [bitFault, Matrix.mul_assoc, hr, h, decode_syndrome_unitErr, ← gateOf_pX_eq_pauliMat,
        gateOf_smul, Controlled.gateOf_mul q pX A, Matrix.mul_smul, Matrix.smul_mul]
      simp only [Matrix.mul_assoc]⟩

/-- The transversal Hadamard carries an operator on qubit `q` to one on qubit `q`. -/
theorem hadTransversal_conj_gateOf (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    hadTransversal 7 * gateOf q M * hadTransversal 7 = gateOf q (hGateM * M * hGateM) := by
  have h := Gadget.blockKron_mul_gateOf Gadget.had q M
  change hadTransversal 7 * gateOf q M = gateOf q (hGateM * M * hGateMᴴ) * hadTransversal 7 at h
  rw [h, Matrix.mul_assoc, hadTransversal_mul_self, Matrix.mul_one, hGateM_conjTranspose]

/-- ★★ **One fault in the phase round leaves an error on qubit `q` alone**: the bit statement in the
Hadamard basis. -/
theorem atQubit_phaseFault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    AtQubit q (phaseFault q A B m) := by
  have hTP : hadTransversal 7 * steaneProj = steaneProj * hadTransversal 7 :=
    steaneProj_mul_hadTransversal.symm
  have hr : hadTransversal 7 * faultRead q A B m * hadTransversal 7 * steaneProj
      = faultCoeff q B m • (gateOf q (hGateM * A * hGateM) * steaneProj) := by
    calc hadTransversal 7 * faultRead q A B m * hadTransversal 7 * steaneProj
        = hadTransversal 7 * (faultRead q A B m * steaneProj) * hadTransversal 7 := by
          rw [Matrix.mul_assoc _ (hadTransversal 7), hTP]; simp only [Matrix.mul_assoc]
      _ = faultCoeff q B m • (hadTransversal 7 * gateOf q A * (steaneProj * hadTransversal 7)) := by
          rw [faultRead_mul_steaneProj, Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = faultCoeff q B m • (gateOf q (hGateM * A * hGateM) * steaneProj) := by
          rw [← hTP, ← hadTransversal_conj_gateOf]; simp only [Matrix.mul_assoc]
  by_cases hc : faultCoeff q B m = 0
  · exact ⟨0, by rw [phaseFault, Matrix.mul_assoc, hr, hc, zero_smul, Matrix.mul_zero, gateOf_zero,
      Matrix.zero_mul]⟩
  rcases syndrome_of_faultCoeff_ne_zero hc with h | h
  · exact ⟨faultCoeff q B m • (hGateM * A * hGateM), by
      rw [phaseFault, Matrix.mul_assoc, hr, h, decode_zero, pauliMat_zero, Matrix.one_mul,
        gateOf_smul, Matrix.smul_mul]⟩
  · exact ⟨faultCoeff q B m • (pZ * (hGateM * A * hGateM)), by
      rw [phaseFault, Matrix.mul_assoc, hr, h, decode_syndrome_unitErr, ← gateOf_pZ_eq_pauliMat,
        gateOf_smul, Controlled.gateOf_mul q pZ (hGateM * A * hGateM), Matrix.mul_smul,
        Matrix.smul_mul]
      simp only [Matrix.mul_assoc]⟩

/-! ### The other round, fault-free -/

/-- The single-qubit Paulis at `q` are operators on qubit `q`. -/
theorem exists_pauliMat_eq_gateOf {q : Fin 7} {i : SingleErr}
    (hi : i = none ∨ ∃ t, i = some (q, t)) :
    (∃ N, pauliMat (errA i) (errB i) = gateOf q N) ∧ ∃ N, pauliMat 0 (errB i) = gateOf q N := by
  rcases hi with rfl | ⟨t, rfl⟩
  · exact ⟨⟨1, (gateOf_one_eq_pauliMat q).symm⟩, ⟨1, (gateOf_one_eq_pauliMat q).symm⟩⟩
  · fin_cases t
    · exact ⟨⟨pX, by simp [errA, errB, gateOf_pX_eq_pauliMat]⟩,
        ⟨1, by simp [errB, gateOf_one_eq_pauliMat]⟩⟩
    · exact ⟨⟨pZ, by simp [errA, errB, gateOf_pZ_eq_pauliMat]⟩,
        ⟨pZ, by simp [errB, gateOf_pZ_eq_pauliMat]⟩⟩
    · exact ⟨⟨pXZ, by simp [errA, errB, gateOf_pXZ_eq_pauliMat]⟩,
        ⟨pZ, by simp [errB, gateOf_pZ_eq_pauliMat]⟩⟩

theorem singleCoeff_eq_zero {q : Fin 7} {M : Matrix (Fin 2) (Fin 2) ℂ} {i : SingleErr}
    (hi : ¬(i = none ∨ ∃ t, i = some (q, t))) : singleCoeff q M i = 0 := by
  rcases i with _ | ⟨j, t⟩
  · exact absurd (Or.inl rfl) hi
  · have hj : j ≠ q := fun hj => hi (Or.inr ⟨t, by rw [hj]⟩)
    simp [singleCoeff, hj]

/-- ★★ **A fault-free phase round keeps an error on qubit `q` on qubit `q`**: it measures the error's
`Z` part and, if it reads one, corrects it at `q`. -/
theorem AtQubit.phaseRound_mul {q : Fin 7} {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hK : AtQubit q K) (m : Fin 7 → Fin 2) : AtQubit q (phaseRound m * K) := by
  obtain ⟨M, hM⟩ := hK
  have hexp : phaseRound m * K * steaneProj
      = ∑ i : SingleErr, singleCoeff q M i
          • (phaseRound m * pauliMat (errA i) (errB i) * steaneProj) := by
    rw [Matrix.mul_assoc, hM, gateOf_eq_sum_pauliMat q M, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul]
    simp only [Matrix.mul_assoc]
  suffices h : AtQubit q (∑ i : SingleErr, singleCoeff q M i
      • (phaseRound m * pauliMat (errA i) (errB i))) by
    obtain ⟨N, hN⟩ := h
    refine ⟨N, ?_⟩
    rw [hexp, ← hN, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  refine AtQubit.sum _ fun i _ => ?_
  by_cases hi : i = none ∨ ∃ t, i = some (q, t)
  · refine AtQubit.smul ?_ _
    rw [phaseRound_eq, Matrix.smul_mul]
    refine AtQubit.smul ?_ _
    show ∃ N, pauliMat 0 (decode (syndrome m)) * phaseProj (syndrome m)
        * pauliMat (errA i) (errB i) * steaneProj = gateOf q N * steaneProj
    rw [Matrix.mul_assoc (pauliMat 0 _ * phaseProj _), Matrix.mul_assoc (pauliMat 0 _),
      ← Matrix.mul_assoc (phaseProj _), phaseProj_mul_pauliMat_mul_steaneProj]
    by_cases ht : syndrome m = syndrome (errB i)
    · rw [ite_eq_left ht, ht, decode_syndrome_errB]
      obtain ⟨⟨N₁, h₁⟩, ⟨N₂, h₂⟩⟩ := exists_pauliMat_eq_gateOf hi
      exact ⟨N₂ * N₁, by rw [h₁, h₂, ← Matrix.mul_assoc, ← Controlled.gateOf_mul]⟩
    · exact ⟨0, by rw [ite_eq_right ht, Matrix.mul_zero, gateOf_zero, Matrix.zero_mul]⟩
  · rw [singleCoeff_eq_zero hi, zero_smul]
    exact AtQubit.zero

/-- A fault-free bit round on a code state reads a clean word or nothing. -/
theorem bitRound_mul_steaneProj (m : Fin 7 → Fin 2) :
    bitRound m * steaneProj = if syndrome m = 0 then (1 / 4 : ℂ) • steaneProj else 0 := by
  rw [bitRound_eq, Matrix.smul_mul, Matrix.mul_assoc, bitProj_mul_steaneProj]
  by_cases h : syndrome m = 0
  · rw [ite_eq_left h, ite_eq_left h, h, decode_zero, pauliMat_zero, Matrix.one_mul]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.mul_zero, smul_zero]

/-! ### The theorem -/

/-- ★★★ **One fault in Steane's method leaves a weight-one error.** For a fault `A ⊗ B` at any
extraction location `q` — a `CNOT` of either round, or an ancilla qubit before it is read — with the
rest of the method fault-free, every branch of the method acts on the code as an operator on data
qubit `q` alone. -/
theorem steaneMethod_single_fault (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) (mm : OutPair) :
    AtQubit q (phaseRound mm.2 * bitFault q A B mm.1)
      ∧ AtQubit q (phaseFault q A B mm.2 * bitRound mm.1) := by
  refine ⟨(atQubit_bitFault q A B mm.1).phaseRound_mul mm.2, ?_⟩
  obtain ⟨M, hM⟩ := atQubit_phaseFault q A B mm.2
  by_cases h : syndrome mm.1 = 0
  · refine ⟨(1 / 4 : ℂ) • M, ?_⟩
    rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_left h, Matrix.mul_smul, hM, gateOf_smul,
      Matrix.smul_mul]
  · refine ⟨0, ?_⟩
    rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_right h, Matrix.mul_zero, gateOf_zero,
      Matrix.zero_mul]

/-- ★★★ **On a code state, Steane's method with one extraction fault outputs a mixture of errors on
one qubit**: `Σ_b M_b ρ M_bᴴ` with every `M_b` acting on qubit `q` alone. -/
theorem steaneMethod_single_fault_apply (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (hρ : ρ = steaneProj * ρ * steaneProj) :
    (∃ M : OutPair → Matrix (Fin 2) (Fin 2) ℂ,
        ∑ mm : OutPair, (phaseRound mm.2 * bitFault q A B mm.1) * ρ
            * (phaseRound mm.2 * bitFault q A B mm.1)ᴴ
          = ∑ mm, gateOf q (M mm) * ρ * (gateOf q (M mm))ᴴ)
      ∧ ∃ M : OutPair → Matrix (Fin 2) (Fin 2) ℂ,
        ∑ mm : OutPair, (phaseFault q A B mm.2 * bitRound mm.1) * ρ
            * (phaseFault q A B mm.2 * bitRound mm.1)ᴴ
          = ∑ mm, gateOf q (M mm) * ρ * (gateOf q (M mm))ᴴ := by
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have key : ∀ K : OutPair → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ,
      (∀ mm, AtQubit q (K mm)) →
      ∃ M : OutPair → Matrix (Fin 2) (Fin 2) ℂ,
        ∑ mm, K mm * ρ * (K mm)ᴴ = ∑ mm, gateOf q (M mm) * ρ * (gateOf q (M mm))ᴴ := by
    intro K hK
    choose M hM using hK
    refine ⟨M, Finset.sum_congr rfl fun mm _ => ?_⟩
    have h1 : K mm * ρ * (K mm)ᴴ = (K mm * steaneProj) * ρ * (K mm * steaneProj)ᴴ := by
      rw [conjTranspose_mul, hP]
      conv_lhs => rw [hρ]
      simp only [Matrix.mul_assoc]
    have h2 : gateOf q (M mm) * ρ * (gateOf q (M mm))ᴴ
        = (gateOf q (M mm) * steaneProj) * ρ * (gateOf q (M mm) * steaneProj)ᴴ := by
      rw [conjTranspose_mul, hP]
      conv_lhs => rw [hρ]
      simp only [Matrix.mul_assoc]
    rw [h1, h2, hM mm]
  exact ⟨key _ fun mm => (steaneMethod_single_fault q A B mm).1,
    key _ fun mm => (steaneMethod_single_fault q A B mm).2⟩


end Steane
end QEC
end QM
end Empirical
end CSD

end

end
