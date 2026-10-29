/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneMachineConcat
public import CsdLean4.Empirical.QM.QEC.SteaneSyndromeCircuit

/-!
# The Steane recovery as a circuit

**Category:** 3-Local (Empirical, QM twin). BACKLOG #228 (QC chain, link 12), residue of #207.

The Steane machine (#207, #227) ran on a recovery channel that `exists_recovery_of_knillLaflamme`
produces abstractly. This module builds the recovery from gates — ancilla preparation, the `CNOT`
ladder of #94, ancilla readout, the transversal Hadamard, and a decoded Pauli correction — and proves
it does the same job, so the machine runs on it.

## The readout, and the two syndromes

* `ancRead`, ★★ `ancRead_mul_extractMat_mul_ancInit` — **prepare, extract, read is the syndrome
  projector**: preparing a fresh ancilla, running the ladder and reading the ancilla as `s` is, on the
  data, exactly `synProj H s` (generic in the check map);
* `bitProj`, `phaseProj` — the bit-flip syndrome projector and its conjugate by the transversal
  Hadamard, which reads the **`Z`-checks** (the conjugate basis #94 left open);
* `bitProj_mul_pauliMat` — a Pauli shifts the bit syndrome by its own; `bitProj_zero_mul_steaneEnc`,
  `bitProj_mul_steaneProj` — the code lives on syndrome-zero words; ★
  `bitProj_mul_pauliMat_mul_steaneProj`, ★ `phaseProj_mul_pauliMat_mul_steaneProj` — **on an errored
  code state the bit syndrome is that of the error's `X` part, the phase syndrome that of its `Z`
  part**.

## The decoder and the circuit

* `decode`, ★ `decode_syndrome_unitErr` — **the decoder names the faulty qubit**;
  `decode_syndrome_errA`/`_errB`, ★ `syndromePair_injective` — the syndrome pair determines the
  single-qubit Pauli;
* `recKraus` — **one branch of the recovery circuit as gates** (extract and read the bit syndrome,
  Hadamard, extract and read the phase syndrome, Hadamard, correct), ★★ `recKraus_eq` — it is
  correction ∘ phase projector ∘ bit projector; ★★ `recKraus_tp`; ★★★ `circuitRecovery` — **the
  channel**;
* ★★ `recKraus_mul_pauliMat_mul_steaneProj` — a branch returns `±` the code state on the error's
  syndrome pair and nothing elsewhere; ★★★ `circuitRecovery_cross` — **the Knill–Laflamme correction
  property for every pair of single-qubit Paulis**, with the identity matrix of scalars;
* ★★★ `circuitRecovery_arbitrary`, ★★★ `circuitRecovery_unitary` — **every error on one qubit is
  corrected**, exactly for a unitary one; ★★ `isRecovery_circuitRecovery` — #96's `IsRecovery` for
  the weight-one errors.

## The machine on it

* ★★★ `steane_gadgetSet_corrected_circuit` — the gadget set of #207 is corrected by the circuit;
* ★★★ `steane_machine_circuit` — **#207's machine with `circuitRecovery` after every gadget**: the
  premise and the bound `1 − 21 N p²`, with the recovery now a named circuit rather than an existential
  channel.

## Honest scope

⚠️ **The recovery circuit is fault-free.** Its gates, ancillas and readouts act ideally; faults in
it, and the verified (cat) ancilla that makes them harmless, are BACKLOG #229, which this row
unblocks.

⚠️ **One unverified ancilla block per syndrome, one round.** No repetition of the syndrome
measurement, no ancilla verification. ▸ The same channel built through Steane's encoded ancilla, where
one fault leaves a weight-one error, is `SteaneMethod.lean` (`methodRecovery_apply`,
`steaneMethod_single_fault`, BACKLOG #229).

⚠️ **Measurement and feed-forward are branches.** The readout `ancRead` with its classically
controlled correction is modelled as the Kraus branches of one channel, one per outcome pair: the
standard form of measure-then-correct with the ancilla discarded.

⚠️ **Level one.** The level-`k` machine (#227) still uses #86's Knill–Laflamme channel; the level-`k`
recovery as a circuit is what the recursive simulation of BACKLOG #231 builds.

⚠️ **Weight-one decoding.** The decoder is the syndrome lookup for single-qubit errors, which is
all a distance-3 code corrects.

References: A. Steane, PRL 77 (1996); M. Nielsen, I. Chuang, §10.4–10.5; `specs/BACKLOG.md` #228,
#207, #94, #96, #229, #231; `Mathlib/QuantumInfo/SyndromeExtraction.lean`,
`Empirical/QM/QEC/SteaneSyndromeCircuit.lean`, `Empirical/QM/QEC/SteaneArbitrary.lean`
(`gateOf_eq_sum_pauliMat`, `sum_singleCoeff_sq`), `Empirical/QM/QEC/SteaneMachine.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped ENNReal

noncomputable section

/-! ### Reading the ancilla -/

namespace QuantumInfo

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [AddCommGroup β]

/-- **Reading the ancilla block as `s`** and keeping the data: the map `(z, s) ↦ z`. -/
def ancRead (s : β) : Matrix α (α × β) ℂ := Matrix.of fun z p => if p = (z, s) then 1 else 0

/-- ★★ **Prepare, extract, read: the circuit is the syndrome projector.** Preparing a fresh ancilla,
running the `CNOT` ladder and reading the ancilla as `s` is, as an operator on the data, exactly the
projector onto the syndrome-`s` subspace. -/
theorem ancRead_mul_extractMat_mul_ancInit {H : α → β} (hH : ∀ z, H z + H z = 0) (s : β) :
    ancRead s * extractMat H * (ancInit : Matrix (α × β) α ℂ) = synProj H s := by
  ext z w
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (z, s)]
  · rw [extractMat_mul_ancInit_apply hH, synProj, Matrix.diagonal_apply]
    simp only [ancRead, Matrix.of_apply, ite_true, one_mul]
    by_cases h : z = w
    · subst h
      by_cases hs : H z = s
      · simp [hs]
      · simp [hs, Ne.symm hs]
    · simp [h]
  · intro p _ hp
    simp [ancRead, hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The two syndrome projectors around the code -/

/-- The bit-flip syndrome projector: onto `{z | syndrome z = s}`. -/
abbrev bitProj (s : Fin 3 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ := synProj syndrome s

/-- The phase-flip syndrome projector: the same in the Hadamard basis. -/
def phaseProj (t : Fin 3 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  hadTransversal 7 * bitProj t * hadTransversal 7

theorem synVec_add_eq_zero_iff {s t : Fin 3 → Fin 2} : s + t = 0 ↔ s = t := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    revert hi
    generalize s i = x
    generalize t i = y
    revert x y
    decide
  · rintro rfl
    funext i
    exact (by decide : ∀ x : Fin 2, x + x = 0) (s i)

/-- **A Pauli shifts the bit syndrome by its own**: `Π_s X^a Z^b = X^a Z^b Π_{s + syn a}`. -/
theorem bitProj_mul_pauliMat (s : Fin 3 → Fin 2) (a b : Fin 7 → Fin 2) :
    bitProj s * pauliMat a b = pauliMat a b * bitProj (s + syndrome a) := by
  ext z w
  simp only [bitProj, synProj, Matrix.diagonal_mul, Matrix.mul_diagonal, pauliMat]
  by_cases h : w = z + a
  · subst h
    rw [syndrome_add]
    have : (syndrome z = s) ↔ (syndrome z + syndrome a = s + syndrome a) :=
      ⟨fun h => by rw [h], fun h => add_right_cancel h⟩
    by_cases hs : syndrome z = s
    · simp [hs]
    · simp [hs, mt this.2 hs]
  · simp [h]

theorem bitProj_mul_bitProj (s u : Fin 3 → Fin 2) :
    bitProj s * bitProj u = if s = u then bitProj s else 0 := by
  simp only [bitProj, synProj, Matrix.diagonal_mul_diagonal]
  by_cases h : s = u
  · subst h
    rw [ite_eq_left rfl]
    congr 1
    funext z
    by_cases hz : syndrome z = s <;> simp [hz]
  · rw [ite_eq_right h, ← Matrix.diagonal_zero]
    congr 1
    funext z
    by_cases hz : syndrome z = s
    · simp [hz, h]
    · simp [hz]

theorem syndrome_rowComb (c : Fin 3 → Fin 2) : syndrome (rowComb c) = 0 := by
  revert c
  decide

theorem syndrome_rowComb_add_allOnes (c : Fin 3 → Fin 2) :
    syndrome (rowComb c + allOnes) = 0 := by
  revert c
  decide

/-- **The logical states live on syndrome-zero words**: `Π_0 E = E`. -/
theorem bitProj_zero_mul_steaneEnc : bitProj 0 * steaneEnc = steaneEnc := by
  ext z a
  simp only [bitProj, synProj, Matrix.diagonal_mul]
  by_cases hz : syndrome z = 0
  · rw [ite_eq_left hz, one_mul]
  · rw [ite_eq_right hz, zero_mul]
    symm
    have hne : ∀ c : Fin 3 → Fin 2, z ≠ rowComb c := fun c h => hz (h ▸ syndrome_rowComb c)
    have hne' : ∀ c : Fin 3 → Fin 2, z ≠ rowComb c + allOnes := fun c h =>
      hz (h ▸ syndrome_rowComb_add_allOnes c)
    simp only [steaneEnc, Matrix.of_apply, steaneZero, steaneOne, WithLp.ofLp_smul,
      WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    split_ifs
    · rw [Finset.sum_eq_zero fun c _ => by simp [basisState, hne c], mul_zero]
    · rw [Finset.sum_eq_zero fun c _ => by simp [basisState, hne' c], mul_zero]

theorem bitProj_zero_mul_steaneProj : bitProj 0 * steaneProj = steaneProj := by
  rw [steaneProj_eq, ← Matrix.mul_assoc, bitProj_zero_mul_steaneEnc]

theorem bitProj_mul_steaneProj (u : Fin 3 → Fin 2) :
    bitProj u * steaneProj = if u = 0 then steaneProj else 0 := by
  rw [← bitProj_zero_mul_steaneProj, ← Matrix.mul_assoc, bitProj_mul_bitProj]
  by_cases h : u = 0
  · simp [h, bitProj_zero_mul_steaneProj]
  · simp [h]

/-- ★ **The bit syndrome of a Pauli error on the code is the syndrome of its `X` part.** -/
theorem bitProj_mul_pauliMat_mul_steaneProj (s : Fin 3 → Fin 2) (a b : Fin 7 → Fin 2) :
    bitProj s * pauliMat a b * steaneProj
      = if s = syndrome a then pauliMat a b * steaneProj else 0 := by
  rw [bitProj_mul_pauliMat, Matrix.mul_assoc, bitProj_mul_steaneProj]
  by_cases h : s = syndrome a
  · rw [ite_eq_left (synVec_add_eq_zero_iff.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt synVec_add_eq_zero_iff.1 h), ite_eq_right h, Matrix.mul_zero]

/-- ★ **The phase syndrome of a Pauli error on the code is the syndrome of its `Z` part.** The bit
statement in the Hadamard basis: the transversal Hadamard exchanges the labels and commutes with the
code projector. -/
theorem phaseProj_mul_pauliMat_mul_steaneProj (t : Fin 3 → Fin 2) (a b : Fin 7 → Fin 2) :
    phaseProj t * pauliMat a b * steaneProj
      = if t = syndrome b then pauliMat a b * steaneProj else 0 := by
  set T := hadTransversal 7
  have hTT : T * T = 1 := hadTransversal_mul_self
  have hTP : T * steaneProj = steaneProj * T := steaneProj_mul_hadTransversal.symm
  have hconj := hadTransversal_conj_pauliMat a b
  have hM : T * pauliMat a b = (signChar (bdot a b) • pauliMat b a) * T := by
    rw [← hconj, Matrix.mul_assoc _ T T, hTT, Matrix.mul_one]
  have hback : T * (signChar (bdot a b) • pauliMat b a) * T = pauliMat a b := by
    rw [← hconj]
    calc T * (T * pauliMat a b * T) * T = (T * T) * pauliMat a b * (T * T) := by
          simp only [Matrix.mul_assoc]
      _ = pauliMat a b := by rw [hTT, Matrix.one_mul, Matrix.mul_one]
  have hbit := bitProj_mul_pauliMat_mul_steaneProj t b a
  calc phaseProj t * pauliMat a b * steaneProj
      = T * (bitProj t * (signChar (bdot a b) • pauliMat b a) * steaneProj) * T := by
        rw [phaseProj]
        calc T * bitProj t * T * pauliMat a b * steaneProj
            = T * bitProj t * (T * pauliMat a b) * steaneProj := by simp only [Matrix.mul_assoc]
          _ = T * bitProj t * ((signChar (bdot a b) • pauliMat b a) * T) * steaneProj := by rw [hM]
          _ = T * bitProj t * (signChar (bdot a b) • pauliMat b a) * (T * steaneProj) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hTP]; simp only [Matrix.mul_assoc]
    _ = if t = syndrome b then pauliMat a b * steaneProj else 0 := by
        rw [Matrix.mul_smul, Matrix.smul_mul, hbit]
        by_cases h : t = syndrome b
        · rw [ite_eq_left h, ite_eq_left h]
          calc T * (signChar (bdot a b) • (pauliMat b a * steaneProj)) * T
              = T * (signChar (bdot a b) • pauliMat b a) * (steaneProj * T) := by
                simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
            _ = T * (signChar (bdot a b) • pauliMat b a) * T * steaneProj := by
                rw [← hTP]; simp only [Matrix.mul_assoc]
            _ = pauliMat a b * steaneProj := by rw [hback]
        · rw [ite_eq_right h, ite_eq_right h, smul_zero, Matrix.mul_zero, Matrix.zero_mul]

/-! ### The decoder -/

/-- **The decoder**: the correction a syndrome calls for — the single-bit pattern at the qubit whose
single-bit error has that syndrome, and nothing for a syndrome no single error has (in particular
`0`). -/
def decode (s : Fin 3 → Fin 2) : Fin 7 → Fin 2 :=
  fun q => if syndrome (unitErr q) = s then 1 else 0

theorem syndrome_zero : syndrome 0 = 0 := by
  funext i
  simp [syndrome, bdot]

theorem decode_zero : decode 0 = 0 := by
  funext q
  simp [decode, steane_syndrome_single_ne_zero q]

/-- ★ **The decoder names the faulty qubit.** -/
theorem decode_syndrome_unitErr (j : Fin 7) : decode (syndrome (unitErr j)) = unitErr j := by
  funext q
  simp only [decode, unitErr_apply]
  by_cases h : q = j
  · subst h
    simp
  · rw [ite_eq_right fun h' => h (steane_syndrome_single_injective q j h'), ite_eq_right h]

theorem decode_syndrome_of {e : Fin 7 → Fin 2} (h : e = 0 ∨ ∃ j, e = unitErr j) :
    decode (syndrome e) = e := by
  rcases h with rfl | ⟨j, rfl⟩
  · rw [syndrome_zero, decode_zero]
  · exact decode_syndrome_unitErr j

theorem decode_syndrome_errA (i : SingleErr) : decode (syndrome (errA i)) = errA i := by
  refine decode_syndrome_of ?_
  rcases i with _ | ⟨j, t⟩
  · exact Or.inl rfl
  · by_cases ht : t = 1
    · exact Or.inl (by simp [errA, ht])
    · exact Or.inr ⟨j, by simp [errA, ht]⟩

theorem decode_syndrome_errB (i : SingleErr) : decode (syndrome (errB i)) = errB i := by
  refine decode_syndrome_of ?_
  rcases i with _ | ⟨j, t⟩
  · exact Or.inl rfl
  · by_cases ht : t = 0
    · exact Or.inl (by simp [errB, ht])
    · exact Or.inr ⟨j, by simp [errB, ht]⟩

/-- The single-qubit Paulis have distinct labels. -/
theorem errA_errB_injective : ∀ i j : SingleErr, errA i = errA j → errB i = errB j → i = j := by
  decide

/-- ★ **Distinct single-qubit Paulis have distinct syndrome pairs.** -/
theorem syndromePair_injective {i j : SingleErr}
    (h : (syndrome (errA i), syndrome (errB i)) = (syndrome (errA j), syndrome (errB j))) :
    i = j := by
  obtain ⟨ha, hb⟩ := Prod.mk.inj h
  refine errA_errB_injective i j ?_ ?_
  · rw [← decode_syndrome_errA i, ha, decode_syndrome_errA]
  · rw [← decode_syndrome_errB i, hb, decode_syndrome_errB]

/-! ### The recovery circuit -/

/-- The syndrome pair a recovery round reads: the bit-flip syndrome, then the phase-flip one. -/
abbrev SynPair : Type := (Fin 3 → Fin 2) × (Fin 3 → Fin 2)

/-- ★ **One branch of the recovery circuit, as gates.** Prepare an ancilla, run the `CNOT` ladder,
read the bit syndrome `s`; apply the transversal Hadamard, prepare a second ancilla, run the ladder,
read the phase syndrome `t`, undo the Hadamard; apply the decoded correction
`X^{decode s} Z^{decode t}`. -/
def recKraus (st : SynPair) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode st.1) (decode st.2)
    * (hadTransversal 7 * (ancRead st.2 * steaneExtract
        * (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ))
      * hadTransversal 7)
    * (ancRead st.1 * steaneExtract
        * (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ))

/-- ★★ **The circuit branch is correction ∘ phase projector ∘ bit projector.** -/
theorem recKraus_eq (st : SynPair) :
    recKraus st = pauliMat (decode st.1) (decode st.2) * phaseProj st.2 * bitProj st.1 := by
  rw [recKraus, steaneExtract, ancRead_mul_extractMat_mul_ancInit steane_syndrome_add_self,
    ancRead_mul_extractMat_mul_ancInit steane_syndrome_add_self, phaseProj]

theorem bitProj_mul_self (s : Fin 3 → Fin 2) : bitProj s * bitProj s = bitProj s :=
  synProj_mul_self _ _

theorem sum_bitProj : ∑ s, bitProj s = 1 := sum_synProj _

theorem bitProj_conjTranspose (s : Fin 3 → Fin 2) : (bitProj s)ᴴ = bitProj s :=
  synProj_conjTranspose _ _

theorem phaseProj_conjTranspose (t : Fin 3 → Fin 2) : (phaseProj t)ᴴ = phaseProj t := by
  rw [phaseProj, conjTranspose_mul, conjTranspose_mul, hadTransversal_conjTranspose,
    synProj_conjTranspose, Matrix.mul_assoc]

theorem phaseProj_mul_self (t : Fin 3 → Fin 2) : phaseProj t * phaseProj t = phaseProj t := by
  have hTT : hadTransversal 7 * hadTransversal 7 = 1 := hadTransversal_mul_self
  calc phaseProj t * phaseProj t
      = hadTransversal 7 * bitProj t * (hadTransversal 7 * hadTransversal 7) * bitProj t
          * hadTransversal 7 := by rw [phaseProj]; simp only [Matrix.mul_assoc]
    _ = hadTransversal 7 * (bitProj t * bitProj t) * hadTransversal 7 := by
        rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = phaseProj t := by rw [bitProj_mul_self, phaseProj]

theorem sum_phaseProj : ∑ t, phaseProj t = 1 := by
  simp only [phaseProj, ← Finset.sum_mul, ← Finset.mul_sum, sum_synProj, Matrix.mul_one,
    hadTransversal_mul_self]

/-- ★★ **The recovery circuit is a channel**: its branches satisfy `∑ Kᴴ K = 1`. -/
theorem recKraus_tp : ∑ st : SynPair, (recKraus st)ᴴ * recKraus st = 1 := by
  have hterm : ∀ st : SynPair, (recKraus st)ᴴ * recKraus st
      = bitProj st.1 * phaseProj st.2 * bitProj st.1 := by
    intro st
    rw [recKraus_eq, conjTranspose_mul, conjTranspose_mul, bitProj_conjTranspose,
      phaseProj_conjTranspose]
    have hC := pauliMat_conjTranspose_mul_self (decode st.1) (decode st.2)
    calc _ = bitProj st.1 * (phaseProj st.2
          * ((pauliMat (decode st.1) (decode st.2))ᴴ * pauliMat (decode st.1) (decode st.2))
          * phaseProj st.2) * bitProj st.1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hC, Matrix.mul_one, phaseProj_mul_self]
  rw [Finset.sum_congr rfl fun st _ => hterm st, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_phaseProj, Matrix.mul_one, bitProj_mul_self,
    sum_bitProj]

/-- ★★★ **The Steane recovery as a circuit**: the channel whose branches are the recovery circuit's,
one per syndrome pair. -/
def circuitRecovery : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) SynPair where
  kraus := recKraus
  tp := recKraus_tp

/-! ### What the circuit does to a single-qubit Pauli error on the code -/

/-- ★★ **A branch on an errored code state**: it returns `±` the code state when the syndrome pair
read is the error's, and nothing otherwise. -/
theorem recKraus_mul_pauliMat_mul_steaneProj (st : SynPair) (i : SingleErr) :
    recKraus st * pauliMat (errA i) (errB i) * steaneProj
      = if st = (syndrome (errA i), syndrome (errB i))
        then pauliSign (errB i) (errA i) • steaneProj else 0 := by
  obtain ⟨s, t⟩ := st
  rw [recKraus_eq]
  have hassoc : pauliMat (decode s) (decode t) * phaseProj t * bitProj s
        * pauliMat (errA i) (errB i) * steaneProj
      = pauliMat (decode s) (decode t)
          * (phaseProj t * (bitProj s * pauliMat (errA i) (errB i) * steaneProj)) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, bitProj_mul_pauliMat_mul_steaneProj]
  by_cases hs : s = syndrome (errA i)
  · rw [ite_eq_left hs, ← Matrix.mul_assoc (phaseProj t), phaseProj_mul_pauliMat_mul_steaneProj]
    by_cases ht : t = syndrome (errB i)
    · rw [ite_eq_left ht, ite_eq_left (by rw [hs, ht]), hs, ht, decode_syndrome_errA,
        decode_syndrome_errB, ← Matrix.mul_assoc, pauliMat_mul]
      have ha : errA i + errA i = 0 := by funext q; exact fin2_add_self _
      have hb : errB i + errB i = 0 := by funext q; exact fin2_add_self _
      rw [ha, hb, pauliMat_zero, Matrix.smul_mul, Matrix.one_mul]
    · rw [ite_eq_right ht, ite_eq_right (by intro h; exact ht (Prod.mk.inj h).2), Matrix.mul_zero]
  · rw [ite_eq_right hs, ite_eq_right (by intro h; exact hs (Prod.mk.inj h).1), Matrix.mul_zero,
      Matrix.mul_zero]

/-- ★★★ **The circuit corrects every single-qubit Pauli error, cross terms included**: the
Knill–Laflamme correction property with the identity matrix of scalars. -/
theorem circuitRecovery_cross :
    ∀ ρ, ρ = steaneProj * ρ * steaneProj →
      ∀ i j, circuitRecovery.apply (pauliMat (errA i) (errB i) * ρ * (pauliMat (errA j) (errB j))ᴴ)
        = (1 : Matrix SingleErr SingleErr ℂ) j i • ρ := by
  intro ρ hρ i j
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have hterm : ∀ st : SynPair,
      recKraus st * (pauliMat (errA i) (errB i) * ρ * (pauliMat (errA j) (errB j))ᴴ)
          * (recKraus st)ᴴ
        = (recKraus st * pauliMat (errA i) (errB i) * steaneProj) * ρ
          * (recKraus st * pauliMat (errA j) (errB j) * steaneProj)ᴴ := by
    intro st
    rw [conjTranspose_mul, conjTranspose_mul, hP]
    conv_lhs => rw [hρ]
    simp only [Matrix.mul_assoc]
  show ∑ st : SynPair, recKraus st * _ * (recKraus st)ᴴ = _
  rw [Finset.sum_congr rfl fun st _ => hterm st]
  simp only [recKraus_mul_pauliMat_mul_steaneProj]
  rw [Finset.sum_eq_single (syndrome (errA i), syndrome (errB i))]
  · rw [ite_eq_left rfl]
    by_cases hij : i = j
    · subst hij
      have hl : star (pauliSign (errB i) (errA i)) * pauliSign (errB i) (errA i) = 1 := by
        rw [Complex.star_def, conj_pauliSign, pauliSign_mul_self]
      rw [ite_eq_left rfl, Matrix.one_apply_eq, one_smul, conjTranspose_smul, hP]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hl, one_smul]
      exact hρ.symm
    · rw [ite_eq_right (fun h => hij (syndromePair_injective h)), conjTranspose_zero,
        Matrix.mul_zero, Matrix.one_apply_ne (Ne.symm hij), zero_smul]
  · intro st _ hst
    rw [ite_eq_right hst, Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Every single-qubit error -/

/-- ★★★ **The circuit corrects an arbitrary error on one qubit**, up to the scalar `tr(MᴴM)/2` — the
Paulis span a qubit's operators and the correction property is bilinear. -/
theorem circuitRecovery_arbitrary (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
    (hρ : ρ = steaneProj * ρ * steaneProj) (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    circuitRecovery.apply (gateOf q M * ρ * (gateOf q M)ᴴ)
      = ((star (M 0 0) * M 0 0 + star (M 0 1) * M 0 1 + star (M 1 0) * M 1 0
          + star (M 1 1) * M 1 1) / 2) • ρ := by
  rw [gateOf_eq_sum_pauliMat q M,
    recovery_apply_lin_comb (fun ρ' hρ' i j => circuitRecovery_cross ρ' hρ' i j) (singleCoeff q M) hρ,
    sum_singleCoeff_sq]

/-- ★★★ **A unitary error on one qubit is undone exactly by the circuit.** -/
theorem circuitRecovery_unitary (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
    (hρ : ρ = steaneProj * ρ * steaneProj) (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    circuitRecovery.apply (gateOf q M * ρ * (gateOf q M)ᴴ) = ρ := by
  obtain ⟨h1, h2, -, -⟩ := unitary_entries hM
  rw [circuitRecovery_arbitrary ρ hρ q M]
  rw [show (star (M 0 0) * M 0 0 + star (M 0 1) * M 0 1 + star (M 1 0) * M 1 0
      + star (M 1 1) * M 1 1) / 2 = 1 by
    rw [← starRingEnd_apply, ← starRingEnd_apply, ← starRingEnd_apply, ← starRingEnd_apply]
    rw [show (starRingEnd ℂ) (M 0 0) * M 0 0 + (starRingEnd ℂ) (M 0 1) * M 0 1
        + (starRingEnd ℂ) (M 1 0) * M 1 0 + (starRingEnd ℂ) (M 1 1) * M 1 1
        = ((starRingEnd ℂ) (M 0 0) * M 0 0 + (starRingEnd ℂ) (M 1 0) * M 1 0)
          + ((starRingEnd ℂ) (M 0 1) * M 0 1 + (starRingEnd ℂ) (M 1 1) * M 1 1) by ring, h1, h2]
    norm_num, one_smul]

/-- ★★ **The circuit is a recovery for the weight-one errors**, in #96's sense. -/
theorem isRecovery_circuitRecovery : IsRecovery steaneProj circuitRecovery.apply weightOne :=
  isRecovery_weightOne fun ρ hρ q M hM => circuitRecovery_unitary ρ hρ q M hM

/-! ### The machine on the circuit recovery -/

/-- ★★★ **The gadget set is corrected by the recovery circuit**: #207's theorem with the existential
recovery channel replaced by the gate-built one. -/
theorem steane_gadgetSet_corrected_circuit (G : Gadget) {U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : ∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) {b : ConcatPat 7 1}
    (hb : isBad 7 1 b = false) :
    IsCorrectedStep steaneProj G.ideal (G.step circuitRecovery U (locPat b)) :=
  isCorrectedStep_rect isRecovery_circuitRecovery
    (G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hb)) fun _ hρ => G.isCodeState_ideal hρ

/-- ★★★ **The Steane machine with its recovery built from gates.** For every circuit of `N` gadgets
from the set, unitary faults at their locations and an encoded input, with `circuitRecovery` after
every gadget: a pattern that makes no gadget bad gives exactly the ideal output, and under independent
location faults of rate at most `p` the output is ideal with probability at least `1 − 21 N p²`. -/
theorem steane_machine_circuit (N : ℕ) (gs : Fin N → Gadget)
    (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (hρ : IsCodeState steaneProj ρ) :
    (∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
        correctedRun (machineCircuit circuitRecovery gs U ω) ρ = machineIdeal gs ρ)
    ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
        ν {c | c = true} ≤ ENNReal.ofReal p →
        1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p 1)
          ≤ QuantumInfo.circuitMeasure N 7 ν 1
              {ω | correctedRun (machineCircuit circuitRecovery gs U ω) ρ = machineIdeal gs ρ} := by
  have hgood : ∀ ω : CircuitPat N 7 1, (∀ j, isBad 7 1 (ω j) = false) →
      correctedRun (machineCircuit circuitRecovery gs U ω) ρ = machineIdeal gs ρ := by
    intro ω hω
    rw [← idealRun_machineCircuit circuitRecovery gs U ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact steane_gadgetSet_corrected_circuit (gs j) (hU j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := 1) ν hp hν
    (out := fun ω => correctedRun (machineCircuit circuitRecovery gs U ω) ρ)
    (ideal := machineIdeal gs ρ) hgood
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
