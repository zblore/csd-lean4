/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneFaultModel

/-!
# Verified ancilla preparation for Steane's method

**Category:** 3-Local (Empirical, QM twin). BACKLOG #234 (split from ~~#229~~).

~~#229~~'s Steane's method takes its ancilla `|+̄⟩` as prepared ideally. A fault in the encoding circuit
can leave a `Z` error of weight two or more on it, which the transversal `CNOT` copies onto the data.
This module prepares the ancilla by a circuit, verifies it, and proves that one fault anywhere in the
preparation still leaves Steane's method a correctable deviation.

## The encoder

* `cnotRelabel`, `cnotRelabel_involutive`, `plusGates`, `cnotCircuit`, `plusInit`, `plusEncoder` — **nine
  `CNOT`s** from the information qubits `2, 4, 5, 6` (in `|+⟩`) onto the parity qubits `0, 1, 3` (in
  `|0⟩`); ★★ `plusEncoder_mulVec` — **the encoder prepares `|+̄⟩`** (checked over the 128 labels);
* `cnotCircuit_mulVec_apply`, `cnotCircuit_conjTranspose_mul`; ★★ `cnotCircuit_fault_mulVec` — **one
  fault anywhere in the encoder leaves `M |+̄⟩`** with `M = pre F preᴴ`; `encoderFault`,
  `encoderFault_tp` — as a trace-preserving family.

## The verification

* `pairPlus`, `hadB`, `verifyOut`, `Accepts` — a second `|+̄⟩`, the **checker**, controls a transversal
  `CNOT` onto the ancilla and is read in the `X` basis; it **passes** when its word is orthogonal to
  the Hamming code; `prepAOp`, `prepBOp`, `pairFaultOp` — the verification with a fault in the
  ancilla's preparation, in the checker's, or after the `CNOT`; `verify_fault_before`,
  `readout_fault_eq` — a fault before the `CNOT`, or at the checker's readout, is one after the `CNOT`;
* `IsPeriodic` (**`X` errors only**), ★ `IsPeriodic.eq_sum` — such an ancilla is a combination of
  `X^{decode t} |+̄⟩`, its `Z` error trivial modulo the stabiliser; `GoodAnc` — `X` errors only, or any
  error on one qubit;
* ★★★ `isPeriodic_verifyOut_prepA` — **a passing checker leaves the ancilla with `X` errors only,
  whatever error its preparation made**: the `CNOT` copies the error's `Z` part onto the checker, and a
  word orthogonal to the code passes only what a stabiliser absorbs; ★★ `isPeriodic_verifyOut_prepB`
  — a faulty checker leaves `X` errors only, whatever is read; ★★ `verifyOut_pairFault` — a fault on
  pair `j` leaves an error on qubit `j`;
* `FacIdx`, ★★ `factoryOut` — **the factory**: on a pass the ancilla, on a failure a fresh `|+̄⟩` (the
  one fault spent); ★★ `factoryOut_norm` — its branches carry weight one; `goodAnc_factoryOut`,
  `verifyOut_ideal`, `factoryOut_ideal`.

## Steane's method with the verified ancilla

* `ancReadOp`, `ancBitOp`, `ancPhaseOp`, `ancKraus`, `ancKraus_tp`, ★★ `ancMethod` — **Steane's method
  with one round's ancilla drawn from a family**; ★★ `ancMethod_apply_of_eq_smul` — multiples of
  `|+̄⟩` give `methodRecovery` exactly;
* `ancReadOp_mul_steaneProj_of_periodic`, `ancReadOp_gateOf`, ★★ `exists_atQubit_ancBitOp`,
  ★★ `exists_atQubit_ancPhaseOp` — **a good ancilla leaves an error on one data qubit**: an `X` error
  on the ancilla only mis-reads the syndrome, and the decoder's correction has weight one;
* ★★★ `deviatesBy_cssMix_of_exists_atQubit` — a channel each of whose branches acts on one qubit
  (which one may depend on the branch) is a CSS deviation; ★★★ `deviatesBy_ancMethod`;
* ★★★ `steane_verified_ancilla` — **the encoder prepares `|+̄⟩`; fault-free, the verified method is
  Steane's method; with one fault in the ancilla's preparation, the checker's, or the verification
  `CNOT`, it is a CSS deviation of the identity.**

## The factory under any fault pattern (BACKLOG ~~#238~~)

* `BlockOp`, `EncLoc`, `plusGateMat`, `prod_ofFn_plusGateMat`, `encUnder`, `encUnder_tp`,
  ★ `encUnder_none_mulVec` — **the encoder with a Kraus family after each of its sixteen locations**;
  `sum_plusInit_sq`; `prod_ofFn_mul_eq_zero`, `prod_ofFn_one_mul`, `sum_mul_unitary_conjTranspose_mul`;
* `verUnder`, `verUnder_tp`, `facIn`, `sum_facIn_sq` — **the verification with faults on its seven
  pairs and seven checker readouts**, and the two encoded blocks;
* ★★ `isPeriodic_verifyVec_A`, ★★ `isPeriodic_verifyVec_B`, ★ `readVec_apply` — the verification's
  cases for **any** input on the faulty block; `GoodAnc.smul`, `roundKraus_false_cases`,
  `verUnder_none`, `verUnder_pair`, `verUnder_read`, `facIn_noneA`, `facIn_noneB`, `facIn_none`;
* `FacFaults`, `FacFaults.Valid`, `FacLoc` (**forty-six locations**), `FacBranch`, `facVec`,
  `sum_facVec_sq`, `factoryOutV`, `factoryOutV_norm`, `goodAnc_factoryOutV`, `factoryOutV_eq_smul`;
  ★★ `facOut`, ★★ `facOut_norm`, ★★ `facOut_none`, ★★★ `goodAnc_facOut_single` — **one fault anywhere
  in the factory leaves a good ancilla in every branch; none leaves `|+̄⟩`**.

## Honest scope

⚠️ **One verified ancilla here; the machine is elsewhere.** `steane_verified_ancilla` is about one
run of Steane's method; the factory under any fault pattern (below) is what `SteaneOverlapMachine.lean`
counts in every recovery (BACKLOG ~~#238~~).

⚠️ **Repeat until success, with the one fault spent.** On a rejection the factory prepares a fresh
`|+̄⟩` fault-free: under one fault per extended rectangle, a second attempt is ideal. Rejection with
two faults, and the expected number of attempts, are not treated.

⚠️ **The checker reads one basis.** It catches `Z` errors on the ancilla, the dangerous ones; `X`
errors pass and only mis-read the syndrome. A fault in the encoder is any trace-preserving family on
the seven qubits (`cnotCircuit_fault_mulVec`), not a propagation analysis gate by gate — none is
needed, since the verification catches every `Z` part.

⚠️ **One round per basis**, as in ~~#228~~ and ~~#229~~.

References: A. Steane, PRL 78 (1997) 2252; P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf.
Comput. 6 (2006) 97; D. Gottesman, arXiv:0904.2557 §6; `specs/BACKLOG.md` #234, #229, #232, #235,
#95, #236, #231; `Empirical/QM/QEC/SteaneMethod.lean`, `Empirical/QM/QEC/SteaneFaultyRecovery.lean`,
`Empirical/QM/QEC/SteaneFaultModel.lean`, `Mathlib/QuantumInfo/AncillaLadder.lean`;
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker

noncomputable section

namespace QuantumInfo

section Generic

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A basis permutation acts on a vector by relabelling it. -/
theorem permMat_mulVec_apply {σ : α → α} (hσ : Function.Involutive σ) (v : α → ℂ) (z : α) :
    (permMat σ *ᵥ v) z = v (σ z) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (σ z)]
  · rw [permMat_apply, ite_eq_left (hσ z).symm, one_mul]
  · intro w _ hw
    rw [permMat_apply, ite_eq_right, zero_mul]
    intro hzw
    exact hw (by rw [hzw, hσ w])
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq α] [DecidableEq β] in
/-- A product operator on a product vector. -/
theorem kronecker_mulVec_prod (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (u : α → ℂ) (v : β → ℂ) :
    (X ⊗ₖ Y) *ᵥ (fun p : α × β => u p.1 * v p.2) = fun p => (X *ᵥ u) p.1 * (Y *ᵥ v) p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq α] in
/-- An operator on the first factor only. -/
theorem kronecker_one_mulVec_apply_eq_sum (X : Matrix α α ℂ) (u : α × β → ℂ) (i : α) (j : β) :
    ((X ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ u) (i, j) = ∑ b, X i b * u (b, j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.one_apply]

omit [DecidableEq β] in
/-- **Preparing `M ψ` is preparing `ψ` and applying `M` to the ancilla.** -/
theorem ancPrep_mulVec (M : Matrix β β ℂ) (ψ : β → ℂ) :
    (ancPrep (M *ᵥ ψ) : Matrix (α × β) α ℂ) = ((1 : Matrix α α ℂ) ⊗ₖ M) * ancPrep ψ := by
  ext ⟨z, a⟩ z'
  simp only [ancPrep, Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.mulVec, dotProduct]
  by_cases h : z = z'
  · subst h
    simp
  · simp [h]

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem ancPrep_smul (c : ℂ) (ψ : β → ℂ) :
    (ancPrep (c • ψ) : Matrix (α × β) α ℂ) = c • ancPrep ψ := by
  ext p z
  by_cases h : p.1 = z <;> simp [ancPrep, h]

/-- **A trace-preserving family keeps the squared norm**: `Σ_k ‖G_k v‖² = ‖v‖²`. -/
theorem sum_star_mulVec_mul_mulVec {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    {G : κ → Matrix n n ℂ} (hG : ∑ k, (G k)ᴴ * G k = 1) (v : n → ℂ) :
    ∑ k, ∑ p, star ((G k *ᵥ v) p) * (G k *ᵥ v) p = ∑ p, star (v p) * v p := by
  have h : ∀ k, ∑ p, star ((G k *ᵥ v) p) * (G k *ᵥ v) p = (star v ᵥ* ((G k)ᴴ * G k)) ⬝ᵥ v := by
    intro k
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← star_mulVec]
    rfl
  simp only [h]
  rw [← sum_dotProduct, ← vecMul_sum, hG, vecMul_one]
  rfl

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem sum_one_kronecker {κ : Type*} [Fintype κ] (X : κ → Matrix β β ℂ) :
    ∑ k, ((1 : Matrix α α ℂ) ⊗ₖ X k) = (1 : Matrix α α ℂ) ⊗ₖ ∑ k, X k := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

omit [Fintype α] [DecidableEq α] [Fintype β] in
theorem sum_kronecker_one_eq {κ : Type*} [Fintype κ] (X : κ → Matrix α α ℂ) :
    ∑ k, (X k ⊗ₖ (1 : Matrix β β ℂ)) = (∑ k, X k) ⊗ₖ (1 : Matrix β β ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- A unitary after a trace-preserving family keeps it trace preserving. -/
theorem sum_unitary_mul_conjTranspose_mul {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    {U : Matrix n n ℂ} {K : κ → Matrix n n ℂ} (hU : Uᴴ * U = 1) (hK : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ k, (U * K k)ᴴ * (U * K k) = 1 := by
  have h : ∀ k, (U * K k)ᴴ * (U * K k) = (K k)ᴴ * K k := by
    intro k
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  simp only [h]
  exact hK

/-- **The transversal Hadamard's entries**: `H^{⊗n}_{wb} = 2^{-n/2} (−1)^{w·b}`. -/
theorem hadTransversal_apply (n : ℕ) (w b : Fin n → Fin 2) :
    hadTransversal n w b = ((Real.sqrt 2 : ℂ)⁻¹) ^ n * signChar (bdot w b) := by
  have h : ∀ i j : Fin 2, hGateM i j = (Real.sqrt 2 : ℂ)⁻¹ * signChar (i * j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hGateM, signChar]
  rw [hadTransversal, blockKron_apply, Finset.prod_congr rfl fun i _ => h (w i) (b i),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, bdot,
    signChar_sum]

end Generic

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The encoding circuit of `|+̄⟩` -/

/-- **The `CNOT` from qubit `c` to qubit `t`**, as a relabelling of the register. -/
def cnotRelabel (c t : Fin 7) (a : Fin 7 → Fin 2) : Fin 7 → Fin 2 :=
  Function.update a t (a t + a c)

theorem cnotRelabel_involutive {c t : Fin 7} (h : c ≠ t) : Function.Involutive (cnotRelabel c t) := by
  intro a
  funext i
  by_cases hi : i = t
  · subst hi
    simp only [cnotRelabel, Function.update_self, Function.update_of_ne h]
    rw [add_assoc, fin2_add_self, add_zero]
  · simp [cnotRelabel, Function.update_of_ne hi]

/-- **The encoder's nine `CNOT`s**: each information qubit `2, 4, 5, 6` onto the parity qubits `0, 1,
3` its Hamming column names. -/
def plusGates : List (Fin 7 × Fin 7) :=
  [(2, 0), (2, 1), (4, 0), (4, 3), (5, 1), (5, 3), (6, 0), (6, 1), (6, 3)]

theorem plusGates_ne : ∀ g ∈ plusGates, g.1 ≠ g.2 := by decide

/-- The gate matrix of a list of `CNOT`s, the last in the list acting first. -/
def cnotCircuit (l : List (Fin 7 × Fin 7)) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (l.map fun g => permMat (cnotRelabel g.1 g.2)).prod

/-- **The input of the encoder**: `|+⟩` on the information qubits, `|0⟩` on the parity qubits. -/
def plusInit (a : Fin 7 → Fin 2) : ℂ :=
  if a 0 = 0 ∧ a 1 = 0 ∧ a 3 = 0 then 1 / 4 else 0

/-- **The encoder of `|+̄⟩`.** -/
def plusEncoder : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ := cnotCircuit plusGates

theorem cnotCircuit_mulVec_apply :
    ∀ (l : List (Fin 7 × Fin 7)), (∀ g ∈ l, g.1 ≠ g.2) → ∀ (v : (Fin 7 → Fin 2) → ℂ) z,
      (cnotCircuit l *ᵥ v) z = v (l.foldl (fun z g => cnotRelabel g.1 g.2 z) z)
  | [], _, v, z => by simp [cnotCircuit]
  | g :: l, h, v, z => by
    rw [cnotCircuit, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      permMat_mulVec_apply (cnotRelabel_involutive (h g List.mem_cons_self)), List.foldl_cons]
    exact cnotCircuit_mulVec_apply l (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) v _

theorem cnotCircuit_conjTranspose_mul :
    ∀ (l : List (Fin 7 × Fin 7)), (∀ g ∈ l, g.1 ≠ g.2) → (cnotCircuit l)ᴴ * cnotCircuit l = 1
  | [], _ => by simp [cnotCircuit]
  | g :: l, h => by
    have hg := cnotRelabel_involutive (h g List.mem_cons_self)
    have ih := cnotCircuit_conjTranspose_mul l fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    rw [cnotCircuit, List.map_cons, List.prod_cons, conjTranspose_mul, permMat_conjTranspose hg]
    rw [show (cnotCircuit l)ᴴ = ((l.map fun g => permMat (cnotRelabel g.1 g.2)).prod)ᴴ from rfl] at ih
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMat _), permMat_mul_self hg, Matrix.one_mul]
    exact ih

/-- ★★ **The encoder prepares `|+̄⟩`**: nine `CNOT`s carry `|+⟩^{⊗4} |0⟩^{⊗3}` to the uniform
superposition over the sixteen Hamming codewords. -/
theorem plusEncoder_mulVec : plusEncoder *ᵥ plusInit = plusAnc := by
  funext a
  rw [plusEncoder, cnotCircuit_mulVec_apply _ plusGates_ne]
  have key : ∀ a : Fin 7 → Fin 2,
      ((plusGates.foldl (fun z g => cnotRelabel g.1 g.2 z) a) 0 = 0
        ∧ (plusGates.foldl (fun z g => cnotRelabel g.1 g.2 z) a) 1 = 0
        ∧ (plusGates.foldl (fun z g => cnotRelabel g.1 g.2 z) a) 3 = 0) ↔ syndrome a = 0 := by
    decide +kernel
  exact if_congr (key a) rfl rfl

/-- ★★ **One fault anywhere in the encoder leaves `M |+̄⟩`**: a fault `F` between the gates `post`
(already applied) and `pre` (still to come) is the fault `pre F preᴴ` on the encoded state. -/
theorem cnotCircuit_fault_mulVec {pre post : List (Fin 7 × Fin 7)} (h : pre ++ post = plusGates)
    (F : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    (cnotCircuit pre * F * cnotCircuit post) *ᵥ plusInit
      = (cnotCircuit pre * F * (cnotCircuit pre)ᴴ) *ᵥ plusAnc := by
  have hpre : (cnotCircuit pre)ᴴ * cnotCircuit pre = 1 :=
    cnotCircuit_conjTranspose_mul pre fun g hg => plusGates_ne g (h ▸ List.mem_append_left _ hg)
  have henc : cnotCircuit pre * cnotCircuit post = plusEncoder := by
    rw [plusEncoder, ← h, cnotCircuit, cnotCircuit, cnotCircuit, List.map_append, List.prod_append]
  rw [← plusEncoder_mulVec, ← henc, Matrix.mulVec_mulVec]
  congr 1
  calc cnotCircuit pre * F * cnotCircuit post
      = cnotCircuit pre * F * ((cnotCircuit pre)ᴴ * cnotCircuit pre) * cnotCircuit post := by
        rw [hpre, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-! ### Ancillas that carry `X` errors only -/

theorem vec_add_add_self (x a : Fin 7 → Fin 2) : x + (a + x) = a := by
  funext i
  simp only [Pi.add_apply]
  generalize x i = u
  generalize a i = v
  revert u v
  decide

/-- **A vector invariant under the Hamming code's translations** — an `|+̄⟩` with `X` errors only. -/
def IsPeriodic (f : (Fin 7 → Fin 2) → ℂ) : Prop :=
  ∀ a b, syndrome b = 0 → f (a + b) = f a

theorem plusAnc_add (a b : Fin 7 → Fin 2) (hb : syndrome b = 0) : plusAnc (a + b) = plusAnc a := by
  simp only [plusAnc, syndrome_add, hb, add_zero]

theorem isPeriodic_plusAnc : IsPeriodic plusAnc := plusAnc_add

theorem IsPeriodic.smul {f : (Fin 7 → Fin 2) → ℂ} (hf : IsPeriodic f) (c : ℂ) :
    IsPeriodic (c • f) := fun a b hb => by simp only [Pi.smul_apply, hf a b hb]

theorem isPeriodic_zero : IsPeriodic 0 := fun _ _ _ => rfl

theorem decode_eq_zero_or_unitErr (t : Fin 3 → Fin 2) : decode t = 0 ∨ ∃ q, decode t = unitErr q := by
  revert t
  decide

/-- ★ **A periodic vector is `|+̄⟩` with an `X` error of weight at most one in each branch**: it is a
combination of `X^{decode t} |+̄⟩`. -/
theorem IsPeriodic.eq_sum {f : (Fin 7 → Fin 2) → ℂ} (hf : IsPeriodic f) :
    f = ∑ t, (4 * f (decode t)) • (pauliMat (decode t) 0 *ᵥ plusAnc) := by
  have hsyn : ∀ t, syndrome (decode t) = t := by decide
  funext a
  have hX : ∀ t, (pauliMat (decode t) 0 *ᵥ plusAnc) a = if syndrome a = t then 1 / 4 else 0 := by
    intro t
    simp only [Matrix.mulVec, dotProduct, pauliMat, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, pauliSign, bdot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      signChar_zero, one_mul, plusAnc, syndrome_add, hsyn]
    by_cases h : syndrome a = t
    · rw [ite_eq_left (synVec_add_eq_zero_iff.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (synVec_add_eq_zero_iff.1 h')), ite_eq_right h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hX, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have h := hf (decode (syndrome a)) (a + decode (syndrome a)) (by
    rw [syndrome_add, hsyn]
    exact synVec_add_eq_zero_iff.2 rfl)
  rw [vec_add_add_self] at h
  rw [h]
  ring

/-! ### Steane's method with a prepared ancilla -/

/-- **Steane's extraction with the ancilla prepared in `f`**, read as `m`. -/
def ancReadOp (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * tCNOT
    * (ancPrep f : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

/-- The bit round with the ancilla `f`. -/
def ancBitOp (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode (syndrome m)) 0 * ancReadOp f m

/-- The phase round with the ancilla `f`. -/
def ancPhaseOp (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat 0 (decode (syndrome m)) * (hadTransversal 7 * ancReadOp f m * hadTransversal 7)

/-- **A periodic ancilla reads a multiple of the code projector**: the readout on the code is the
scalar `f m`. -/
theorem ancReadOp_mul_steaneProj_of_periodic {f : (Fin 7 → Fin 2) → ℂ} (hf : IsPeriodic f)
    (m : Fin 7 → Fin 2) : ancReadOp f m * steaneProj = f m • steaneProj := by
  have hd : ancReadOp f m = Matrix.diagonal fun z => f (m + z) := by
    rw [ancReadOp, ancRead_mul_extractMat_mul_ancPrep id_add_self]
    rfl
  have hb : (Matrix.diagonal fun z => f (m + z)) * bitProj 0 = f m • bitProj 0 := by
    simp only [bitProj, synProj]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext z
    by_cases hz : syndrome z = 0
    · simp [hz, hf m z hz]
    · simp [hz]
  rw [hd, ← bitProj_zero_mul_steaneProj, ← Matrix.mul_assoc, hb, Matrix.smul_mul]

theorem onPair_one_kron_gateOf (j : Fin 7) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    OnPair j ((1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) ⊗ₖ gateOf j N) :=
  ⟨1, fun _ => 1, fun _ => N, by simp [gateOf_one]⟩

/-- **An ancilla with an error on qubit `j` is a fault on the pair `j` before the `CNOT`.** -/
theorem ancReadOp_gateOf (j : Fin 7) (N : Matrix (Fin 2) (Fin 2) ℂ) (m : Fin 7 → Fin 2) :
    ancReadOp (gateOf j N *ᵥ plusAnc) m
      = faultReadOp (1 * (tCNOT * ((1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) ⊗ₖ gateOf j N)
          * tCNOT)) m := by
  rw [← readAround_eq, readAround, ancReadOp, ancPrep_mulVec]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- **A good ancilla**: `|+̄⟩` with `X` errors only (`IsPeriodic`), or with any error on one qubit. -/
def GoodAnc (f : (Fin 7 → Fin 2) → ℂ) : Prop :=
  IsPeriodic f ∨ ∃ (j : Fin 7) (N : Matrix (Fin 2) (Fin 2) ℂ), f = gateOf j N *ᵥ plusAnc

/-- ★★ **The bit round with a good ancilla leaves an error on one qubit.** -/
theorem exists_atQubit_ancBitOp {f : (Fin 7 → Fin 2) → ℂ} (hf : GoodAnc f) (m : Fin 7 → Fin 2) :
    ∃ q, AtQubit q (ancBitOp f m) := by
  rcases hf with hf | ⟨j, N, rfl⟩
  · have hr := ancReadOp_mul_steaneProj_of_periodic hf m
    rcases decode_eq_zero_or_unitErr (syndrome m) with h | ⟨q, h⟩
    · exact ⟨0, f m • 1, by
        rw [ancBitOp, Matrix.mul_assoc, hr, h, pauliMat_zero, Matrix.one_mul, gateOf_smul,
          gateOf_one, Matrix.smul_mul, Matrix.one_mul]⟩
    · exact ⟨q, f m • pX, by
        rw [ancBitOp, Matrix.mul_assoc, hr, h, ← gateOf_pX_eq_pauliMat, Matrix.mul_smul, gateOf_smul,
          Matrix.smul_mul]⟩
  · have h := atQubit_bitFaultOp ((onPair_one j).mul (onPair_one_kron_gateOf j N).conj_tCNOT) m
    rw [bitFaultOp] at h
    rw [ancBitOp, ancReadOp_gateOf]
    exact ⟨j, h⟩

/-- ★★ **And the phase round.** -/
theorem exists_atQubit_ancPhaseOp {f : (Fin 7 → Fin 2) → ℂ} (hf : GoodAnc f) (m : Fin 7 → Fin 2) :
    ∃ q, AtQubit q (ancPhaseOp f m) := by
  have hTP : hadTransversal 7 * steaneProj = steaneProj * hadTransversal 7 :=
    steaneProj_mul_hadTransversal.symm
  rcases hf with hf | ⟨j, N, rfl⟩
  · have hr : hadTransversal 7 * ancReadOp f m * hadTransversal 7 * steaneProj
        = f m • steaneProj := by
      calc hadTransversal 7 * ancReadOp f m * hadTransversal 7 * steaneProj
          = hadTransversal 7 * (ancReadOp f m * steaneProj) * hadTransversal 7 := by
            rw [Matrix.mul_assoc _ (hadTransversal 7), hTP]; simp only [Matrix.mul_assoc]
        _ = f m • steaneProj := by
            rw [ancReadOp_mul_steaneProj_of_periodic hf, Matrix.mul_smul, Matrix.smul_mul, hTP,
              Matrix.mul_assoc, hadTransversal_mul_self, Matrix.mul_one]
    rcases decode_eq_zero_or_unitErr (syndrome m) with h | ⟨q, h⟩
    · exact ⟨0, f m • 1, by
        rw [ancPhaseOp, Matrix.mul_assoc, hr, h, pauliMat_zero, Matrix.one_mul, gateOf_smul,
          gateOf_one, Matrix.smul_mul, Matrix.one_mul]⟩
    · exact ⟨q, f m • pZ, by
        rw [ancPhaseOp, Matrix.mul_assoc, hr, h, ← gateOf_pZ_eq_pauliMat, Matrix.mul_smul, gateOf_smul,
          Matrix.smul_mul]⟩
  · have h := atQubit_phaseFaultOp ((onPair_one j).mul (onPair_one_kron_gateOf j N).conj_tCNOT) m
    rw [phaseFaultOp] at h
    rw [ancPhaseOp, ancReadOp_gateOf]
    exact ⟨j, h⟩

/-! ### Steane's method fed by a family of prepared ancillas -/

theorem sum_ancReadOp_conjTranspose_mul_eq (f : (Fin 7 → Fin 2) → ℂ) :
    ∑ m, (ancReadOp f m)ᴴ * ancReadOp f m = (∑ a, star (f a) * f a) • (1 : Matrix _ _ ℂ) := by
  set W : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := tCNOT * ancPrep f
  have hT : tCNOTᴴ * tCNOT = 1 := by
    rw [extractMat_conjTranspose id_add_self, extractMat_mul_self id_add_self]
  have hW : ∀ m, ancReadOp f m
      = (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W := by
    intro m
    simp only [ancReadOp, W, Matrix.mul_assoc]
  have h2 : ∀ m : Fin 7 → Fin 2,
      ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W)ᴴ
        * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W)
      = Wᴴ * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)ᴴ
          * ancRead m) * W := by
    intro m
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [hW]
  rw [Finset.sum_congr rfl fun m _ => h2 m, ← Matrix.sum_mul, ← Matrix.mul_sum,
    sum_ancRead_conjTranspose_mul, Matrix.mul_one, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc tCNOTᴴ, hT, Matrix.one_mul, ancPrep_conjTranspose_mul]

theorem sum_ancReadOp_family {ι : Type*} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) :
    ∑ p : ι × (Fin 7 → Fin 2), (ancReadOp (out p.1) p.2)ᴴ * ancReadOp (out p.1) p.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_ancReadOp_conjTranspose_mul_eq]
  rw [← Finset.sum_smul, hn, one_smul]

theorem ancBitOp_conjTranspose_mul (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    (ancBitOp f m)ᴴ * ancBitOp f m = (ancReadOp f m)ᴴ * ancReadOp f m := by
  rw [ancBitOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
    pauliMat_conjTranspose_mul_self, Matrix.one_mul]

theorem ancPhaseOp_conjTranspose_mul (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    (ancPhaseOp f m)ᴴ * ancPhaseOp f m
      = hadTransversal 7 * ((ancReadOp f m)ᴴ * ancReadOp f m) * hadTransversal 7 := by
  rw [ancPhaseOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
    pauliMat_conjTranspose_mul_self, Matrix.one_mul, conjTranspose_mul, conjTranspose_mul,
    hadTransversal_conjTranspose]
  calc hadTransversal 7 * ((ancReadOp f m)ᴴ * hadTransversal 7)
        * (hadTransversal 7 * ancReadOp f m * hadTransversal 7)
      = hadTransversal 7 * (ancReadOp f m)ᴴ * (hadTransversal 7 * hadTransversal 7)
        * ancReadOp f m * hadTransversal 7 := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hadTransversal_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem sum_ancBitOp_family {ι : Type*} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) :
    ∑ p : ι × (Fin 7 → Fin 2), (ancBitOp (out p.1) p.2)ᴴ * ancBitOp (out p.1) p.2 = 1 := by
  simp only [ancBitOp_conjTranspose_mul]
  exact sum_ancReadOp_family hn

theorem sum_ancPhaseOp_family {ι : Type*} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) :
    ∑ p : ι × (Fin 7 → Fin 2), (ancPhaseOp (out p.1) p.2)ᴴ * ancPhaseOp (out p.1) p.2 = 1 := by
  simp only [ancPhaseOp_conjTranspose_mul]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_ancReadOp_family hn, Matrix.mul_one,
    hadTransversal_mul_self]

/-- A branch of Steane's method whose round `r` takes its ancilla from the family `out`, the other
round's ancilla ideal. -/
def ancKraus {ι : Type*} (out : ι → (Fin 7 → Fin 2) → ℂ) :
    MethodRound → ι × OutPair → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
  | .bit, p => phaseRound p.2.2 * ancBitOp (out p.1) p.2.1
  | .phase, p => ancPhaseOp (out p.1) p.2.2 * bitRound p.2.1

theorem ancKraus_tp {ι : Type*} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) (r : MethodRound) :
    ∑ p, (ancKraus out r p)ᴴ * ancKraus out r p = 1 := by
  have h1 : (1 : PairOp)ᴴ * 1 = 1 := by rw [conjTranspose_one, Matrix.one_mul]
  cases r with
  | bit =>
    have hY := sum_phaseFaultOp_conjTranspose_mul h1
    simp only [phaseFaultOp_one] at hY
    have h := sum_mul_conjTranspose_mul_of_tp (sum_ancBitOp_family hn) hY
    rw [← (Equiv.prodAssoc ι (Fin 7 → Fin 2) (Fin 7 → Fin 2)).sum_comp]
    simp only [Equiv.prodAssoc_apply, ancKraus]
    exact h
  | phase =>
    have hX := sum_bitFaultOp_conjTranspose_mul h1
    simp only [bitFaultOp_one] at hX
    have h := sum_mul_conjTranspose_mul_of_tp hX (sum_ancPhaseOp_family hn)
    let e : (Fin 7 → Fin 2) × (ι × (Fin 7 → Fin 2)) ≃ ι × OutPair :=
      { toFun := fun p => (p.2.1, (p.1, p.2.2)), invFun := fun p => (p.2.1, (p.1, p.2.2)),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [← e.sum_comp]
    simp only [e, Equiv.coe_fn_mk, ancKraus]
    exact h

/-- ★★ **Steane's method with round `r`'s ancilla drawn from the family `out`**: a channel whenever
the family's squared norms sum to one. -/
def ancMethod {ι : Type*} [Fintype ι] (out : ι → (Fin 7 → Fin 2) → ℂ)
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) (r : MethodRound) :
    Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (ι × OutPair) where
  kraus := ancKraus out r
  tp := ancKraus_tp hn r

/-- ★★★ **A channel each of whose branches acts on the code on one qubit — which qubit may depend on
the branch — is a CSS deviation of the identity.** -/
theorem deviatesBy_cssMix_of_exists_atQubit {ι : Type} [Fintype ι]
    (Φ : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι) (h : ∀ b, ∃ q, AtQubit q (Φ.kraus b)) :
    DeviatesBy steaneProj cssMix id Φ.apply := by
  have hP := isCodeProjector_steaneProj
  choose q M hM using h
  have hM' : ∀ b, steaneProj * (Φ.kraus b)ᴴ = steaneProj * (gateOf (q b) (M b))ᴴ := by
    intro b
    have h2 := congrArg conjTranspose (hM b)
    rwa [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq] at h2
  intro ρ hρ
  refine ⟨fun σ => ∑ b, gateOf (q b) (M b) * σ * (gateOf (q b) (M b))ᴴ,
    ⟨ι, inferInstance, fun b => gateOf (q b) (M b), fun b => gateOf_mem_cssSpan (q b) (M b), ?_,
      rfl⟩, ?_⟩
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

theorem exists_atQubit_ancKraus {ι : Type*} {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hgood : ∀ i, GoodAnc (out i)) : ∀ (r : MethodRound) (p : ι × OutPair),
      ∃ q, AtQubit q (ancKraus out r p)
  | .bit, p => by
    obtain ⟨q, h⟩ := exists_atQubit_ancBitOp (hgood p.1) p.2.1
    exact ⟨q, h.phaseRound_mul p.2.2⟩
  | .phase, p => by
    obtain ⟨q, M, hM⟩ := exists_atQubit_ancPhaseOp (hgood p.1) p.2.2
    refine ⟨q, ?_⟩
    show AtQubit q (ancPhaseOp (out p.1) p.2.2 * bitRound p.2.1)
    by_cases h : syndrome p.2.1 = 0
    · refine ⟨(1 / 4 : ℂ) • M, ?_⟩
      rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_left h, Matrix.mul_smul, hM,
        gateOf_smul, Matrix.smul_mul]
    · refine ⟨0, ?_⟩
      rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_right h, Matrix.mul_zero, gateOf_zero,
        Matrix.zero_mul]

/-- ★★★ **Steane's method fed by good ancillas is a CSS deviation of the identity.** -/
theorem deviatesBy_ancMethod {ι : Type} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) (hgood : ∀ i, GoodAnc (out i))
    (r : MethodRound) : DeviatesBy steaneProj cssMix id (ancMethod out hn r).apply :=
  deviatesBy_cssMix_of_exists_atQubit _ (exists_atQubit_ancKraus hgood r)

/-- ★★ **Ancillas that are all multiples of `|+̄⟩` give Steane's method exactly.** -/
theorem ancMethod_apply_of_eq_smul {ι : Type*} [Fintype ι] {out : ι → (Fin 7 → Fin 2) → ℂ}
    (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) {c : ι → ℂ} (hc : ∀ i, out i = c i • plusAnc)
    (r : MethodRound) : (ancMethod out hn r).apply = methodRecovery.apply := by
  have hcc : ∑ i, star (c i) * c i = 1 := by
    rw [← hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc, Pi.smul_apply, smul_eq_mul, star_mul']
    calc star (c i) * c i = star (c i) * c i * ∑ a, star (plusAnc a) * plusAnc a := by
          rw [sum_plusAnc_sq, mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have hread : ∀ i m, ancReadOp (out i) m = c i • steaneRead m := by
    intro i m
    rw [hc, ancReadOp, ancPrep_smul, Matrix.mul_smul]
  have hk : ∀ p : ι × OutPair, ancKraus out r p = c p.1 • methodKraus p.2 := by
    rintro ⟨i, mm⟩
    cases r with
    | bit =>
      show phaseRound mm.2 * (pauliMat (decode (syndrome mm.1)) 0 * ancReadOp (out i) mm.1) = _
      rw [hread, Matrix.mul_smul, Matrix.mul_smul, methodKraus, bitRound]
    | phase =>
      show pauliMat 0 (decode (syndrome mm.2))
          * (hadTransversal 7 * ancReadOp (out i) mm.2 * hadTransversal 7) * bitRound mm.1 = _
      rw [hread, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, methodKraus,
        phaseRound]
  have hcc' : ∑ i, c i * star (c i) = 1 := by simpa only [mul_comm] using hcc
  funext ρ
  rw [Channel.apply_def, Channel.apply_def, Fintype.sum_prod_type]
  have hterm : ∀ i mm, (ancMethod out hn r).kraus (i, mm) * ρ * ((ancMethod out hn r).kraus (i, mm))ᴴ
      = (c i * star (c i)) • (methodKraus mm * ρ * (methodKraus mm)ᴴ) := by
    intro i mm
    show ancKraus out r (i, mm) * ρ * (ancKraus out r (i, mm))ᴴ = _
    rw [hk, conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [hterm, ← Finset.smul_sum]
  rw [← Finset.sum_smul, hcc', one_smul]
  rfl

/-! ### The verification -/

/-- **The checker `|+̄⟩` and the ancilla `|+̄⟩`**, side by side: the checker is the first block (the
control of the verification `CNOT`), the ancilla the second. -/
def pairPlus (p : (Fin 7 → Fin 2) × (Fin 7 → Fin 2)) : ℂ := plusAnc p.1 * plusAnc p.2

/-- The Hadamard on the checker block, so that reading it in the `Z` basis is an `X`-basis readout. -/
abbrev hadB : PairOp := hadTransversal 7 ⊗ₖ (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)

/-- **The ancilla after the checker is read as `w`**, the verification (faults included) being the
operator `G` on the two blocks. -/
def verifyOut (G : PairOp) (w : Fin 7 → Fin 2) : (Fin 7 → Fin 2) → ℂ :=
  fun a => (G *ᵥ pairPlus) (w, a)

/-- **The checker word passes**: it is orthogonal to every Hamming codeword. -/
def Accepts (w : Fin 7 → Fin 2) : Prop :=
  ∀ b, syndrome b = 0 → bdot w b = 0

instance : DecidablePred Accepts := fun w =>
  inferInstanceAs (Decidable (∀ b : Fin 7 → Fin 2, syndrome b = 0 → bdot w b = 0))

/-- **The verification**: the checker controls a transversal `CNOT` onto the ancilla — a `Z` error on
the ancilla is copied back onto the checker — and the checker is read in the `X` basis. -/
def prepAOp {κ : Type*} (M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (k : κ) : PairOp :=
  hadB * tCNOT * ((1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) ⊗ₖ M k)

/-- The verification with the checker's preparation faulty. -/
def prepBOp {κ : Type*} (M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (k : κ) : PairOp :=
  hadB * tCNOT * (M k ⊗ₖ (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ))

/-- The verification with a fault `F` after its `CNOT` — on the pair `j`, a fault on the `CNOT` at
`j` or on the checker qubit `j` before it is read. -/
def pairFaultOp {κ : Type*} (F : κ → PairOp) (k : κ) : PairOp :=
  hadB * F k * tCNOT

/-- **A fault before the verification `CNOT` is the conjugated fault after it.** -/
theorem verify_fault_before (F : PairOp) : hadB * tCNOT * F = hadB * (tCNOT * F * tCNOT) * tCNOT := by
  have hT : tCNOT * tCNOT = 1 := extractMat_mul_self id_add_self
  simp only [Matrix.mul_assoc]
  rw [hT, Matrix.mul_one]

/-- **A fault on checker qubit `j` at its readout is a fault on the pair `j` after the `CNOT`**, the
Hadamard carried through. -/
theorem readout_fault_eq (j : Fin 7) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    (gateOf j N ⊗ₖ (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)) * (hadB * tCNOT)
      = hadB * (gateOf j (hGateM * N * hGateM) ⊗ₖ gateOf j 1) * tCNOT := by
  have hH : gateOf j N * hadTransversal 7 = hadTransversal 7 * gateOf j (hGateM * N * hGateM) := by
    rw [← hadTransversal_conj_gateOf, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hadTransversal_mul_self,
      Matrix.one_mul]
  rw [gateOf_one, ← Matrix.mul_assoc, ← mul_kronecker_mul, hH, mul_kronecker_mul]

theorem tCNOT_mulVec_apply (u : (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ) (b a : Fin 7 → Fin 2) :
    (tCNOT *ᵥ u) (b, a) = u (b, a + b) := by
  rw [show tCNOT = permMat (extractPerm (id : (Fin 7 → Fin 2) → (Fin 7 → Fin 2))) from rfl,
    permMat_mulVec_apply (extractPerm_involutive id_add_self)]
  rfl

theorem tCNOT_mulVec_pairPlus : tCNOT *ᵥ pairPlus = pairPlus := by
  funext ⟨b, a⟩
  rw [tCNOT_mulVec_apply]
  simp only [pairPlus]
  by_cases hb : syndrome b = 0
  · rw [plusAnc_add a b hb]
  · simp [plusAnc, hb]

theorem hadB_mulVec_apply (u : (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ) (w a : Fin 7 → Fin 2) :
    (hadB *ᵥ u) (w, a) = ∑ b, hadTransversal 7 w b * u (b, a) :=
  kronecker_one_mulVec_apply_eq_sum _ _ _ _

theorem hadTransversal_add_of_accepts {w c : Fin 7 → Fin 2} (hw : Accepts w) (hc : syndrome c = 0)
    (b : Fin 7 → Fin 2) : hadTransversal 7 w (b + c) = hadTransversal 7 w b := by
  rw [hadTransversal_apply, hadTransversal_apply, bdot_add_right, hw c hc, add_zero]

theorem pairPlus_eq : pairPlus = fun p => plusAnc p.1 * plusAnc p.2 := rfl

theorem verifyOut_prepA (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (w a : Fin 7 → Fin 2) :
    verifyOut (hadB * tCNOT * ((1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) ⊗ₖ M)) w a
      = ∑ b, hadTransversal 7 w b * (plusAnc b * (M *ᵥ plusAnc) (a + b)) := by
  simp only [verifyOut, ← Matrix.mulVec_mulVec, hadB_mulVec_apply, tCNOT_mulVec_apply]
  rw [pairPlus_eq, kronecker_mulVec_prod, one_mulVec]

theorem verifyOut_prepB (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (w a : Fin 7 → Fin 2) :
    verifyOut (hadB * tCNOT * (M ⊗ₖ (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ))) w a
      = ∑ b, hadTransversal 7 w b * ((M *ᵥ plusAnc) b * plusAnc (a + b)) := by
  simp only [verifyOut, ← Matrix.mulVec_mulVec, hadB_mulVec_apply, tCNOT_mulVec_apply]
  rw [pairPlus_eq, kronecker_mulVec_prod, one_mulVec]

theorem vec_add_add_add (a b c : Fin 7 → Fin 2) : a + c + (b + c) = a + b := by
  funext i
  simp only [Pi.add_apply]
  generalize a i = x
  generalize b i = y
  generalize c i = z
  revert x y z
  decide

/-- ★★★ **A passing checker leaves the ancilla with `X` errors only, whatever error its preparation
made**: an error `M` on the ancilla's `|+̄⟩` is copied by the verification `CNOT` onto the checker as
its `Z` part, and a checker word orthogonal to the code passes only the part a stabiliser absorbs. -/
theorem isPeriodic_verifyOut_prepA (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
    {w : Fin 7 → Fin 2} (hw : Accepts w) :
    IsPeriodic (verifyOut (hadB * tCNOT * ((1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) ⊗ₖ M)) w) := by
  intro a c hc
  rw [verifyOut_prepA, verifyOut_prepA, ← Equiv.sum_comp (Equiv.addRight c)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight]
  rw [plusAnc_add b c hc, vec_add_add_add]
  by_cases hb : syndrome b = 0
  · rw [hadTransversal_add_of_accepts hw hc]
  · simp [plusAnc, hb]

/-- ★★ **A faulty checker leaves the ancilla with `X` errors only, whatever is read**: the checker's
`X` errors are copied onto the ancilla, its `Z` errors stay on it. -/
theorem isPeriodic_verifyOut_prepB (M : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
    (w : Fin 7 → Fin 2) :
    IsPeriodic (verifyOut (hadB * tCNOT * (M ⊗ₖ (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ))) w) := by
  intro a c hc
  rw [verifyOut_prepB, verifyOut_prepB]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [add_right_comm a c b, plusAnc_add _ c hc]

theorem gateOf_sum {ι : Type*} (s : Finset ι) (j : Fin 7) (X : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    gateOf j (∑ k ∈ s, X k) = ∑ k ∈ s, gateOf j (X k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, gateOf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, gateOf_add, ih]

/-- ★★ **A fault on the pair `j` of the verification leaves the ancilla with an error on qubit `j`
alone**, whatever is read. -/
theorem verifyOut_pairFault {j : Fin 7} {F : PairOp} (hF : OnPair j F) (w : Fin 7 → Fin 2) :
    ∃ N, verifyOut (hadB * F * tCNOT) w = gateOf j N *ᵥ plusAnc := by
  obtain ⟨r, A, B, rfl⟩ := hF
  refine ⟨∑ k, (∑ b, hadTransversal 7 w b * (gateOf j (A k) *ᵥ plusAnc) b) • B k, ?_⟩
  funext a
  simp only [verifyOut, ← Matrix.mulVec_mulVec, tCNOT_mulVec_pairPlus]
  simp only [hadB_mulVec_apply, Matrix.sum_mulVec, Finset.sum_apply, pairPlus_eq,
    kronecker_mulVec_prod, gateOf_sum, gateOf_smul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring

/-! ### The verification preserves the squared norm -/

theorem hadB_conjTranspose_mul : hadBᴴ * hadB = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hadTransversal_conjTranspose,
    hadTransversal_mul_self, conjTranspose_one, Matrix.one_mul, one_kronecker_one]

theorem tCNOT_conjTranspose_mul : tCNOTᴴ * tCNOT = 1 := by
  rw [extractMat_conjTranspose id_add_self, extractMat_mul_self id_add_self]

theorem hadB_tCNOT_unitary : (hadB * tCNOT)ᴴ * (hadB * tCNOT) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc hadBᴴ, hadB_conjTranspose_mul,
    Matrix.one_mul, tCNOT_conjTranspose_mul]

theorem prepAOp_tp {κ : Type*} [Fintype κ] {M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hM : ∑ k, (M k)ᴴ * M k = 1) : ∑ k, (prepAOp M k)ᴴ * prepAOp M k = 1 := by
  refine sum_unitary_mul_conjTranspose_mul hadB_tCNOT_unitary ?_
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_one_kronecker, hM, one_kronecker_one]

theorem prepBOp_tp {κ : Type*} [Fintype κ] {M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hM : ∑ k, (M k)ᴴ * M k = 1) : ∑ k, (prepBOp M k)ᴴ * prepBOp M k = 1 := by
  refine sum_unitary_mul_conjTranspose_mul hadB_tCNOT_unitary ?_
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_one_eq, hM, one_kronecker_one]

theorem pairFaultOp_tp {κ : Type*} [Fintype κ] {F : κ → PairOp} (hF : ∑ k, (F k)ᴴ * F k = 1) :
    ∑ k, (pairFaultOp F k)ᴴ * pairFaultOp F k = 1 := by
  have h : ∀ k, (pairFaultOp F k)ᴴ * pairFaultOp F k = tCNOTᴴ * ((F k)ᴴ * F k) * tCNOT := by
    intro k
    rw [pairFaultOp, conjTranspose_mul, conjTranspose_mul]
    calc tCNOTᴴ * ((F k)ᴴ * hadBᴴ) * (hadB * F k * tCNOT)
        = tCNOTᴴ * (F k)ᴴ * (hadBᴴ * hadB) * F k * tCNOT := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hadB_conjTranspose_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hF, Matrix.mul_one, tCNOT_conjTranspose_mul]

/-! ### The verified factory -/

/-- The branches of the factory: the fault's Kraus operator, the checker word, and (on a rejection)
the discarded ancilla's basis label. -/
abbrev FacIdx (κ : Type) : Type := κ × (Fin 7 → Fin 2) × (Fin 7 → Fin 2)

/-- ★★ **The verified factory, branch by branch**: on a passing checker word, the ancilla; on a
failing one, the ancilla is discarded (one Kraus operator per basis label) and a fresh `|+̄⟩` is
prepared — fault-free, the one fault having been spent. -/
def factoryOut {κ : Type} (G : κ → PairOp) (p : FacIdx κ) : (Fin 7 → Fin 2) → ℂ :=
  if Accepts p.2.1 then (if p.2.2 = 0 then verifyOut (G p.1) p.2.1 else 0)
  else verifyOut (G p.1) p.2.1 p.2.2 • plusAnc

theorem sum_pairPlus_sq : ∑ p, star (pairPlus p) * pairPlus p = 1 := by
  simp only [pairPlus, Fintype.sum_prod_type, star_mul']
  calc ∑ x, ∑ y, star (plusAnc x) * star (plusAnc y) * (plusAnc x * plusAnc y)
      = ∑ x, star (plusAnc x) * plusAnc x * ∑ y, star (plusAnc y) * plusAnc y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = 1 := by rw [sum_plusAnc_sq, ← Finset.sum_mul, sum_plusAnc_sq, mul_one]

/-- ★★ **The factory's branches carry total weight one**: the verification is a measurement and the
discard-and-replace step a channel. -/
theorem factoryOut_norm {κ : Type} [Fintype κ] {G : κ → PairOp} (hG : ∑ k, (G k)ᴴ * G k = 1) :
    ∑ p, ∑ a, star (factoryOut G p a) * factoryOut G p a = 1 := by
  have hrow : ∀ k w, ∑ a', ∑ a, star (factoryOut G (k, w, a') a) * factoryOut G (k, w, a') a
      = ∑ a, star (verifyOut (G k) w a) * verifyOut (G k) w a := by
    intro k w
    by_cases hw : Accepts w
    · simp only [factoryOut, hw, ↓reduceIte]
      rw [Finset.sum_eq_single 0 (fun a' _ h => by simp [h])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · simp only [factoryOut, hw, ↓reduceIte, Pi.smul_apply, smul_eq_mul, star_mul']
      calc ∑ a', ∑ a, star (verifyOut (G k) w a') * star (plusAnc a)
            * (verifyOut (G k) w a' * plusAnc a)
          = ∑ a', star (verifyOut (G k) w a') * verifyOut (G k) w a'
              * ∑ a, star (plusAnc a) * plusAnc a := by
            refine Finset.sum_congr rfl fun a' _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
        _ = _ := by rw [sum_plusAnc_sq]; simp
  calc ∑ p : FacIdx κ, ∑ a, star (factoryOut G p a) * factoryOut G p a
      = ∑ k, ∑ w, ∑ a', ∑ a, star (factoryOut G (k, w, a') a) * factoryOut G (k, w, a') a := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ k, ∑ w, ∑ a, star (verifyOut (G k) w a) * verifyOut (G k) w a := by simp only [hrow]
    _ = ∑ k, ∑ q, star ((G k *ᵥ pairPlus) q) * (G k *ᵥ pairPlus) q := by
        simp only [verifyOut, Fintype.sum_prod_type]
    _ = 1 := by rw [sum_star_mulVec_mul_mulVec hG, sum_pairPlus_sq]

/-- Every branch of the factory is good as soon as every passing branch is. -/
theorem goodAnc_factoryOut {κ : Type} {G : κ → PairOp}
    (h : ∀ k w, Accepts w → GoodAnc (verifyOut (G k) w)) (p : FacIdx κ) :
    GoodAnc (factoryOut G p) := by
  obtain ⟨k, w, a'⟩ := p
  by_cases hw : Accepts w
  · by_cases ha : a' = 0
    · simp only [factoryOut, hw, ha, ↓reduceIte]
      exact h k w hw
    · simp only [factoryOut, hw, ha, ↓reduceIte]
      exact Or.inl isPeriodic_zero
  · simp only [factoryOut, hw, ↓reduceIte]
    exact Or.inl (isPeriodic_plusAnc.smul _)

/-- **The fault-free verification passes a multiple of `|+̄⟩`**, whatever the checker reads. -/
theorem verifyOut_ideal (w : Fin 7 → Fin 2) :
    verifyOut (prepAOp (fun _ : Unit => (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)) ()) w
      = (∑ b, hadTransversal 7 w b * plusAnc b) • plusAnc := by
  funext a
  rw [prepAOp, verifyOut_prepA, one_mulVec, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : syndrome b = 0
  · rw [plusAnc_add a b hb, mul_assoc]
  · simp [plusAnc, hb]

theorem factoryOut_ideal (p : FacIdx Unit) :
    ∃ c : ℂ, factoryOut (prepAOp fun _ : Unit => (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)) p
      = c • plusAnc := by
  obtain ⟨k, w, a'⟩ := p
  by_cases hw : Accepts w
  · by_cases ha : a' = 0
    · simp only [factoryOut, hw, ha, ↓reduceIte]
      exact ⟨_, verifyOut_ideal w⟩
    · simp only [factoryOut, hw, ha, ↓reduceIte]
      exact ⟨0, (zero_smul ℂ plusAnc).symm⟩
  · simp only [factoryOut, hw, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- **A fault in the encoder, as a Kraus family on the encoded state** (`cnotCircuit_fault_mulVec`). -/
def encoderFault {κ : Type*} (pre : List (Fin 7 × Fin 7))
    (F : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) (k : κ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  cnotCircuit pre * F k * (cnotCircuit pre)ᴴ

theorem encoderFault_tp {κ : Type*} [Fintype κ] {pre post : List (Fin 7 × Fin 7)}
    (h : pre ++ post = plusGates) {F : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hF : ∑ k, (F k)ᴴ * F k = 1) : ∑ k, (encoderFault pre F k)ᴴ * encoderFault pre F k = 1 := by
  have hpre : (cnotCircuit pre)ᴴ * cnotCircuit pre = 1 :=
    cnotCircuit_conjTranspose_mul pre fun g hg => plusGates_ne g (h ▸ List.mem_append_left _ hg)
  have hpre' : cnotCircuit pre * (cnotCircuit pre)ᴴ = 1 := mul_eq_one_comm.1 hpre
  have hterm : ∀ k, (encoderFault pre F k)ᴴ * encoderFault pre F k
      = cnotCircuit pre * ((F k)ᴴ * F k) * (cnotCircuit pre)ᴴ := by
    intro k
    rw [encoderFault, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc cnotCircuit pre * ((F k)ᴴ * (cnotCircuit pre)ᴴ) * (cnotCircuit pre * F k * (cnotCircuit pre)ᴴ)
        = cnotCircuit pre * (F k)ᴴ * ((cnotCircuit pre)ᴴ * cnotCircuit pre) * F k
            * (cnotCircuit pre)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpre, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hF, Matrix.mul_one, hpre']

/-! ### The theorem -/

/-- ★★★ **Verified ancilla preparation for Steane's method.** The ancilla `|+̄⟩` is prepared by the
nine-`CNOT` encoder, verified against a second `|+̄⟩` (a transversal `CNOT` from the checker onto it,
the checker read in the `X` basis, passed when its word is orthogonal to the Hamming code), and on a
rejection replaced by a fresh one.

* the encoder prepares `|+̄⟩`, and a fault `F` anywhere in it leaves `pre F preᴴ |+̄⟩`;
* fault-free, Steane's method with the verified ancilla in either round is `methodRecovery`;
* with **one fault** — any trace-preserving family on the ancilla's preparation, or on the checker's,
  or on one pair `j` of the verification `CNOT` (the checker's readout included) — Steane's method
  with that round's ancilla from the factory is a CSS deviation of the identity: every branch leaves
  an error on one data qubit. -/
theorem steane_verified_ancilla :
    plusEncoder *ᵥ plusInit = plusAnc
    ∧ (∀ {pre post : List (Fin 7 × Fin 7)}, pre ++ post = plusGates →
        ∀ F : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ,
          (cnotCircuit pre * F * cnotCircuit post) *ᵥ plusInit
            = (cnotCircuit pre * F * (cnotCircuit pre)ᴴ) *ᵥ plusAnc)
    ∧ (∀ r : MethodRound,
        (ancMethod (factoryOut (prepAOp fun _ : Unit => (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)))
          (factoryOut_norm (prepAOp_tp (by simp))) r).apply = methodRecovery.apply)
    ∧ (∀ {κ : Type} [Fintype κ] (M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
        (hM : ∑ k, (M k)ᴴ * M k = 1) (r : MethodRound),
        DeviatesBy steaneProj cssMix id
          (ancMethod (factoryOut (prepAOp M)) (factoryOut_norm (prepAOp_tp hM)) r).apply)
    ∧ (∀ {κ : Type} [Fintype κ] (M : κ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ)
        (hM : ∑ k, (M k)ᴴ * M k = 1) (r : MethodRound),
        DeviatesBy steaneProj cssMix id
          (ancMethod (factoryOut (prepBOp M)) (factoryOut_norm (prepBOp_tp hM)) r).apply)
    ∧ (∀ {κ : Type} [Fintype κ] (j : Fin 7) (F : κ → PairOp) (hF : ∑ k, (F k)ᴴ * F k = 1),
        (∀ k, OnPair j (F k)) → ∀ r : MethodRound,
        DeviatesBy steaneProj cssMix id
          (ancMethod (factoryOut (pairFaultOp F)) (factoryOut_norm (pairFaultOp_tp hF)) r).apply) := by
  refine ⟨plusEncoder_mulVec, fun h F => cnotCircuit_fault_mulVec h F, fun r => ?_,
    fun M hM r => ?_, fun M hM r => ?_, fun j F hF hOn r => ?_⟩
  · choose c hc using factoryOut_ideal
    exact ancMethod_apply_of_eq_smul _ hc r
  · exact deviatesBy_ancMethod _ (goodAnc_factoryOut fun k w hw =>
      Or.inl (isPeriodic_verifyOut_prepA (M k) hw)) r
  · exact deviatesBy_ancMethod _ (goodAnc_factoryOut fun k w _ =>
      Or.inl (isPeriodic_verifyOut_prepB (M k) w)) r
  · exact deviatesBy_ancMethod _ (goodAnc_factoryOut fun k w _ =>
      Or.inr ⟨j, verifyOut_pairFault (hOn k) w⟩) r

/-! ### The factory under a fault pattern -/

/-- Operators on one block of seven qubits. -/
abbrev BlockOp : Type := Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ

/-- **The encoder's locations**: the preparation of each of the seven qubits, then each of the nine
`CNOT`s. -/
abbrev EncLoc : Type := Fin 7 ⊕ Fin 9

/-- The `i`-th `CNOT` of the encoder. -/
def plusGateMat (i : Fin 9) : BlockOp :=
  permMat (cnotRelabel (plusGates[(i : ℕ)]'i.isLt).1 (plusGates[(i : ℕ)]'i.isLt).2)

theorem plusGateMat_conjTranspose_mul (i : Fin 9) : (plusGateMat i)ᴴ * plusGateMat i = 1 := by
  have h := cnotRelabel_involutive (plusGates_ne _ (List.getElem_mem i.isLt))
  rw [plusGateMat, permMat_conjTranspose h, permMat_mul_self h]

theorem prod_ofFn_plusGateMat : (List.ofFn plusGateMat).prod = plusEncoder := by
  rw [plusEncoder, cnotCircuit, ← List.ofFn_getElem_eq_map,
    List.ofFn_congr (rfl : plusGates.length = 9)]
  rfl

/-- An ordered product with a zero factor is zero. -/
theorem prod_ofFn_mul_eq_zero {M : Type*} [MonoidWithZero M] {m : ℕ} (f g : Fin m → M) (i : Fin m)
    (h : f i = 0) : (List.ofFn fun j => f j * g j).prod = 0 :=
  List.prod_eq_zero (List.mem_ofFn.2 ⟨i, by rw [h, zero_mul]⟩)

theorem prod_ofFn_one_mul {M : Type*} [Monoid M] {m : ℕ} (g : Fin m → M) :
    (List.ofFn fun j => (1 : M) * g j).prod = (List.ofFn g).prod := by
  simp only [one_mul]

/-- A trace-preserving family followed... preceded by a unitary stays trace preserving. -/
theorem sum_mul_unitary_conjTranspose_mul {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    {U : Matrix n n ℂ} {K : κ → Matrix n n ℂ} (hU : Uᴴ * U = 1) (hK : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ k, (K k * U)ᴴ * (K k * U) = 1 := by
  have h : ∀ k, (K k * U)ᴴ * (K k * U) = Uᴴ * ((K k)ᴴ * K k) * U := by
    intro k
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hK, Matrix.mul_one, hU]

/-- **The encoder under a pattern**, in branch `s`: the seven preparations, each followed by its
location's Kraus operator, then the nine `CNOT`s, each followed by its location's. -/
def encUnder {κ : Type*} (K : EncLoc → κ → BlockOp) (b : EncLoc → Bool)
    (s : (Fin 7 → Option κ) × (Fin 9 → Option κ)) : BlockOp :=
  (List.ofFn fun i : Fin 9 => locFam (K (.inr i)) (b (.inr i)) (s.2 i) * plusGateMat i).prod
    * roundKraus (fun q => K (.inl q)) (fun q => b (.inl q)) s.1

theorem encUnder_tp {κ : Type*} [Fintype κ] {K : EncLoc → κ → BlockOp}
    (hK : ∀ l, ∑ k, (K l k)ᴴ * K l k = 1) (b : EncLoc → Bool) :
    ∑ s, (encUnder K b s)ᴴ * encUnder K b s = 1 := by
  have hP := roundKraus_tp (fun q => hK (.inl q)) (fun q => b (.inl q))
  have hG := sum_prod_ofFn_conjTranspose_mul
    (fun i o => locFam (K (.inr i)) (b (.inr i)) o * plusGateMat i)
    fun i => sum_mul_unitary_conjTranspose_mul (plusGateMat_conjTranspose_mul i)
      (locFam_tp (hK (.inr i)) _)
  have h := sum_mul_conjTranspose_mul_of_tp hP hG
  simp only [encUnder]
  exact h

/-- **A fault-free encoder prepares `|+̄⟩`** in one branch and nothing in the others. -/
theorem encUnder_none_mulVec {κ : Type*} (K : EncLoc → κ → BlockOp)
    (s : (Fin 7 → Option κ) × (Fin 9 → Option κ)) :
    ∃ c : ℂ, encUnder K (fun _ => false) s *ᵥ plusInit = c • plusAnc := by
  by_cases h1 : s.1 = fun _ => none
  · by_cases h2 : ∃ i, s.2 i ≠ none
    · obtain ⟨i, hi⟩ := h2
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hi
      refine ⟨0, ?_⟩
      have h0 : locFam (K (.inr i)) false (s.2 i) = 0 := by simp [locFam, hk]
      rw [encUnder, prod_ofFn_mul_eq_zero _ _ i h0, Matrix.zero_mul, zero_mulVec, zero_smul]
    · simp only [not_exists, not_not] at h2
      refine ⟨1, ?_⟩
      have hl : ∀ i, locFam (K (.inr i)) false (s.2 i) = 1 := fun i => by simp [locFam, h2 i]
      rw [encUnder, h1, roundKraus_none]
      simp only [hl]
      rw [prod_ofFn_one_mul, prod_ofFn_plusGateMat, Matrix.mul_one, plusEncoder_mulVec, one_smul]
  · refine ⟨0, ?_⟩
    rw [encUnder, roundKraus_none_of_ne _ h1, Matrix.mul_zero, zero_mulVec, zero_smul]

theorem sum_plusInit_sq : ∑ a, star (plusInit a) * plusInit a = 1 := by
  have hc : (Finset.univ.filter fun a : Fin 7 → Fin 2 => a 0 = 0 ∧ a 1 = 0 ∧ a 3 = 0).card = 16 := by
    decide +kernel
  have h : ∀ a, star (plusInit a) * plusInit a
      = if a 0 = 0 ∧ a 1 = 0 ∧ a 3 = 0 then (1 / 16 : ℂ) else 0 := by
    intro a
    by_cases h : a 0 = 0 ∧ a 1 = 0 ∧ a 3 = 0
    · rw [plusInit, ite_eq_left h, ite_eq_left h]; norm_num [Complex.ext_iff]
    · rw [plusInit, ite_eq_right h, ite_eq_right h, star_zero, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, hc]
  norm_num

/-- **The verification under a pattern**, in branch `s = (sP, sR)`: the transversal `CNOT`, the
faults on the pairs, the Hadamard on the checker, the faults at the checker's readout. -/
def verUnder {κ : Type*} (P : Fin 7 → κ → PairOp) (R : Fin 7 → κ → BlockOp) (bP bR : Fin 7 → Bool)
    (s : (Fin 7 → Option κ) × (Fin 7 → Option κ)) : PairOp :=
  (roundKraus R bR s.2 ⊗ₖ (1 : BlockOp)) * (hadB * roundKraus P bP s.1 * tCNOT)

theorem verUnder_tp {κ : Type*} [Fintype κ] {P : Fin 7 → κ → PairOp} {R : Fin 7 → κ → BlockOp}
    (hP : ∀ j, ∑ k, (P j k)ᴴ * P j k = 1) (hR : ∀ j, ∑ k, (R j k)ᴴ * R j k = 1)
    (bP bR : Fin 7 → Bool) : ∑ s, (verUnder P R bP bR s)ᴴ * verUnder P R bP bR s = 1 := by
  have hX := pairFaultOp_tp (roundKraus_tp hP bP)
  have hY : ∑ s, (roundKraus R bR s ⊗ₖ (1 : BlockOp))ᴴ * (roundKraus R bR s ⊗ₖ (1 : BlockOp)) = 1 := by
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_one_eq, roundKraus_tp hR bR, one_kronecker_one]
  have h := sum_mul_conjTranspose_mul_of_tp hX hY
  simp only [verUnder]
  exact h

/-- **The two blocks after their encoders**, in branch `s = (sA, sB)`: the checker first. -/
def facIn {κ : Type*} (EA EB : EncLoc → κ → BlockOp) (bA bB : EncLoc → Bool)
    (s : ((Fin 7 → Option κ) × (Fin 9 → Option κ)) × ((Fin 7 → Option κ) × (Fin 9 → Option κ))) :
    (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ :=
  fun p => (encUnder EB bB s.2 *ᵥ plusInit) p.1 * (encUnder EA bA s.1 *ᵥ plusInit) p.2

theorem sum_facIn_sq {κ : Type*} [Fintype κ] {EA EB : EncLoc → κ → BlockOp}
    (hA : ∀ l, ∑ k, (EA l k)ᴴ * EA l k = 1) (hB : ∀ l, ∑ k, (EB l k)ᴴ * EB l k = 1)
    (bA bB : EncLoc → Bool) : ∑ s, ∑ p, star (facIn EA EB bA bB s p) * facIn EA EB bA bB s p = 1 := by
  have nA := sum_star_mulVec_mul_mulVec (encUnder_tp hA bA) plusInit
  have nB := sum_star_mulVec_mul_mulVec (encUnder_tp hB bB) plusInit
  rw [sum_plusInit_sq] at nA nB
  rw [Fintype.sum_prod_type]
  calc ∑ x, ∑ y, ∑ p, star (facIn EA EB bA bB (x, y) p) * facIn EA EB bA bB (x, y) p
      = ∑ x, ∑ y, (∑ b, star ((encUnder EB bB y *ᵥ plusInit) b) * (encUnder EB bB y *ᵥ plusInit) b)
          * ∑ a, star ((encUnder EA bA x *ᵥ plusInit) a) * (encUnder EA bA x *ᵥ plusInit) a := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [facIn, star_mul']
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    _ = 1 := by
        simp only [← Finset.sum_mul, nB, one_mul]
        exact nA

/-! ### The verification's four fault cases, for any input -/

theorem isPeriodic_verifyVec_A (u : (Fin 7 → Fin 2) → ℂ) {w : Fin 7 → Fin 2} (hw : Accepts w) :
    IsPeriodic fun a => ((hadB * tCNOT) *ᵥ fun p => plusAnc p.1 * u p.2) (w, a) := by
  have happ : ∀ a, ((hadB * tCNOT) *ᵥ fun p => plusAnc p.1 * u p.2) (w, a)
      = ∑ b, hadTransversal 7 w b * (plusAnc b * u (a + b)) := by
    intro a
    simp only [← Matrix.mulVec_mulVec, hadB_mulVec_apply, tCNOT_mulVec_apply]
  intro a c hc
  simp only [happ]
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight]
  rw [plusAnc_add b c hc, vec_add_add_add]
  by_cases hb : syndrome b = 0
  · rw [hadTransversal_add_of_accepts hw hc]
  · simp [plusAnc, hb]

theorem isPeriodic_verifyVec_B (u : (Fin 7 → Fin 2) → ℂ) (w : Fin 7 → Fin 2) :
    IsPeriodic fun a => ((hadB * tCNOT) *ᵥ fun p => u p.1 * plusAnc p.2) (w, a) := by
  have happ : ∀ a, ((hadB * tCNOT) *ᵥ fun p => u p.1 * plusAnc p.2) (w, a)
      = ∑ b, hadTransversal 7 w b * (u b * plusAnc (a + b)) := by
    intro a
    simp only [← Matrix.mulVec_mulVec, hadB_mulVec_apply, tCNOT_mulVec_apply]
  intro a c hc
  simp only [happ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [add_right_comm a c b, plusAnc_add _ c hc]

/-- **A fault on the checker at its readout leaves the ancilla `|+̄⟩`**, up to a scalar. -/
theorem readVec_apply (X : BlockOp) (w a : Fin 7 → Fin 2) :
    (((X ⊗ₖ (1 : BlockOp)) * (hadB * tCNOT)) *ᵥ pairPlus) (w, a)
      = ((X * hadTransversal 7) *ᵥ plusAnc) w * plusAnc a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tCNOT_mulVec_pairPlus,
    show hadB = hadTransversal 7 ⊗ₖ (1 : BlockOp) from rfl, pairPlus_eq, kronecker_mulVec_prod,
    kronecker_mulVec_prod, one_mulVec, one_mulVec, Matrix.mulVec_mulVec]

theorem GoodAnc.smul {f : (Fin 7 → Fin 2) → ℂ} (hf : GoodAnc f) (c : ℂ) : GoodAnc (c • f) := by
  rcases hf with hf | ⟨j, N, rfl⟩
  · exact Or.inl (hf.smul c)
  · exact Or.inr ⟨j, c • N, by rw [gateOf_smul, Matrix.smul_mulVec]⟩

theorem roundKraus_false_cases {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α)
    (s : Fin 7 → Option κ) :
    roundKraus K (fun _ => false) s = 1 ∨ roundKraus K (fun _ => false) s = 0 := by
  by_cases h : s = fun _ => none
  · exact Or.inl (h ▸ roundKraus_none K)
  · exact Or.inr (roundKraus_none_of_ne K h)

/-- A fault-free verification stage is `H ⊗ 1 · CNOT`, up to a scalar. -/
theorem verUnder_none {κ : Type*} (P : Fin 7 → κ → PairOp) (R : Fin 7 → κ → BlockOp)
    (s : (Fin 7 → Option κ) × (Fin 7 → Option κ)) :
    ∃ c : ℂ, verUnder P R (fun _ => false) (fun _ => false) s = c • (hadB * tCNOT) := by
  rcases roundKraus_false_cases P s.1 with hp | hp <;>
    rcases roundKraus_false_cases R s.2 with hr | hr
  · exact ⟨1, by rw [verUnder, hp, hr, one_kronecker_one, Matrix.one_mul, Matrix.mul_one, one_smul]⟩
  · exact ⟨0, by rw [verUnder, hr, zero_kronecker, Matrix.zero_mul, zero_smul]⟩
  · exact ⟨0, by rw [verUnder, hp, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, zero_smul]⟩
  · exact ⟨0, by rw [verUnder, hr, zero_kronecker, Matrix.zero_mul, zero_smul]⟩

theorem verUnder_pair {κ : Type*} (P : Fin 7 → κ → PairOp) (R : Fin 7 → κ → BlockOp)
    (bP : Fin 7 → Bool) (s : (Fin 7 → Option κ) × (Fin 7 → Option κ)) :
    ∃ c : ℂ, verUnder P R bP (fun _ => false) s = c • (hadB * roundKraus P bP s.1 * tCNOT) := by
  rcases roundKraus_false_cases R s.2 with hr | hr
  · exact ⟨1, by rw [verUnder, hr, one_kronecker_one, Matrix.one_mul, one_smul]⟩
  · exact ⟨0, by rw [verUnder, hr, zero_kronecker, Matrix.zero_mul, zero_smul]⟩

theorem verUnder_read {κ : Type*} (P : Fin 7 → κ → PairOp) (R : Fin 7 → κ → BlockOp)
    (bR : Fin 7 → Bool) (s : (Fin 7 → Option κ) × (Fin 7 → Option κ)) :
    ∃ c : ℂ, verUnder P R (fun _ => false) bR s
      = c • ((roundKraus R bR s.2 ⊗ₖ (1 : BlockOp)) * (hadB * tCNOT)) := by
  rcases roundKraus_false_cases P s.1 with hp | hp
  · exact ⟨1, by rw [verUnder, hp, Matrix.mul_one, one_smul]⟩
  · exact ⟨0, by rw [verUnder, hp, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, zero_smul]⟩

theorem facIn_noneB {κ : Type*} (EA EB : EncLoc → κ → BlockOp) (bA : EncLoc → Bool)
    (s : ((Fin 7 → Option κ) × (Fin 9 → Option κ)) × ((Fin 7 → Option κ) × (Fin 9 → Option κ))) :
    ∃ c : ℂ, facIn EA EB bA (fun _ => false) s
      = c • fun p => plusAnc p.1 * (encUnder EA bA s.1 *ᵥ plusInit) p.2 := by
  obtain ⟨c, hc⟩ := encUnder_none_mulVec EB s.2
  refine ⟨c, funext fun p => ?_⟩
  simp only [facIn, hc, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem facIn_noneA {κ : Type*} (EA EB : EncLoc → κ → BlockOp) (bB : EncLoc → Bool)
    (s : ((Fin 7 → Option κ) × (Fin 9 → Option κ)) × ((Fin 7 → Option κ) × (Fin 9 → Option κ))) :
    ∃ c : ℂ, facIn EA EB (fun _ => false) bB s
      = c • fun p => (encUnder EB bB s.2 *ᵥ plusInit) p.1 * plusAnc p.2 := by
  obtain ⟨c, hc⟩ := encUnder_none_mulVec EA s.1
  refine ⟨c, funext fun p => ?_⟩
  simp only [facIn, hc, Pi.smul_apply, smul_eq_mul]
  ring

theorem facIn_none {κ : Type*} (EA EB : EncLoc → κ → BlockOp)
    (s : ((Fin 7 → Option κ) × (Fin 9 → Option κ)) × ((Fin 7 → Option κ) × (Fin 9 → Option κ))) :
    ∃ c : ℂ, facIn EA EB (fun _ => false) (fun _ => false) s = c • pairPlus := by
  obtain ⟨c, hc⟩ := encUnder_none_mulVec EA s.1
  obtain ⟨c', hc'⟩ := encUnder_none_mulVec EB s.2
  refine ⟨c' * c, funext fun p => ?_⟩
  simp only [facIn, hc, hc', pairPlus, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The factory under a pattern -/

/-- **The faults of one factory**: a Kraus family at each location — the ancilla's encoder, the
checker's encoder, the seven verification pairs, the seven checker readouts. -/
structure FacFaults (κ : Type) where
  /-- The ancilla's encoder. -/
  encA : EncLoc → κ → BlockOp
  /-- The checker's encoder. -/
  encB : EncLoc → κ → BlockOp
  /-- The verification pairs, after the `CNOT`. -/
  pair : Fin 7 → κ → PairOp
  /-- The checker's readout. -/
  read : Fin 7 → κ → BlockOp

/-- **The factory's faults are channels, and a pair fault stays on its pair.** -/
structure FacFaults.Valid {κ : Type} [Fintype κ] (Φ : FacFaults κ) : Prop where
  encA_tp : ∀ l, ∑ k, (Φ.encA l k)ᴴ * Φ.encA l k = 1
  encB_tp : ∀ l, ∑ k, (Φ.encB l k)ᴴ * Φ.encB l k = 1
  pair_tp : ∀ j, ∑ k, (Φ.pair j k)ᴴ * Φ.pair j k = 1
  read_tp : ∀ j, ∑ k, (Φ.read j k)ᴴ * Φ.read j k = 1
  pair_on : ∀ j k, OnPair j (Φ.pair j k)

/-- **The factory's locations**: the ancilla's encoder (sixteen), the checker's (sixteen), the
verification pairs (seven), the checker's readouts (seven). -/
abbrev FacLoc : Type := EncLoc ⊕ EncLoc ⊕ Fin 7 ⊕ Fin 7

/-- The factory's fault branches: both encoders', the pairs', the readouts'. -/
abbrev FacBranch (κ : Type) : Type :=
  (((Fin 7 → Option κ) × (Fin 9 → Option κ)) × ((Fin 7 → Option κ) × (Fin 9 → Option κ)))
    × ((Fin 7 → Option κ) × (Fin 7 → Option κ))

/-- **The two blocks before the checker is read**, under the pattern `b`, in branch `s`. -/
def facVec {κ : Type} (Φ : FacFaults κ) (b : FacLoc → Bool) (s : FacBranch κ) :
    (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ :=
  verUnder Φ.pair Φ.read (fun j => b (.inr (.inr (.inl j)))) (fun j => b (.inr (.inr (.inr j)))) s.2
    *ᵥ facIn Φ.encA Φ.encB (fun l => b (.inl l)) (fun l => b (.inr (.inl l))) s.1

theorem sum_facVec_sq {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (b : FacLoc → Bool) :
    ∑ s, ∑ p, star (facVec Φ b s p) * facVec Φ b s p = 1 := by
  rw [Fintype.sum_prod_type]
  calc ∑ x, ∑ y, ∑ p, star (facVec Φ b (x, y) p) * facVec Φ b (x, y) p
      = ∑ x, ∑ p, star (facIn Φ.encA Φ.encB (fun l => b (.inl l)) (fun l => b (.inr (.inl l))) x p)
          * facIn Φ.encA Φ.encB (fun l => b (.inl l)) (fun l => b (.inr (.inl l))) x p := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have h := sum_star_mulVec_mul_mulVec (verUnder_tp hΦ.pair_tp hΦ.read_tp
          (fun j => b (.inr (.inr (.inl j)))) (fun j => b (.inr (.inr (.inr j)))))
          (facIn Φ.encA Φ.encB (fun l => b (.inl l)) (fun l => b (.inr (.inl l))) x)
        simp only [facVec]
        exact h
    _ = 1 := sum_facIn_sq hΦ.encA_tp hΦ.encB_tp _ _

/-- **The factory's output from a family of pre-readout states**: a pass keeps the ancilla, a failure
replaces it by a fresh `|+̄⟩`. -/
def factoryOutV {ι : Type} (V : ι → (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ) (p : FacIdx ι) :
    (Fin 7 → Fin 2) → ℂ :=
  if Accepts p.2.1 then (if p.2.2 = 0 then fun a => V p.1 (p.2.1, a) else 0)
  else V p.1 (p.2.1, p.2.2) • plusAnc

theorem factoryOutV_norm {ι : Type} [Fintype ι] {V : ι → (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ}
    (hV : ∑ i, ∑ q, star (V i q) * V i q = 1) :
    ∑ p, ∑ a, star (factoryOutV V p a) * factoryOutV V p a = 1 := by
  have hrow : ∀ i w, ∑ a', ∑ a, star (factoryOutV V (i, w, a') a) * factoryOutV V (i, w, a') a
      = ∑ a, star (V i (w, a)) * V i (w, a) := by
    intro i w
    by_cases hw : Accepts w
    · simp only [factoryOutV, hw, ↓reduceIte]
      rw [Finset.sum_eq_single 0 (fun a' _ h => by simp [h])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · simp only [factoryOutV, hw, ↓reduceIte, Pi.smul_apply, smul_eq_mul, star_mul']
      calc ∑ a', ∑ a, star (V i (w, a')) * star (plusAnc a) * (V i (w, a') * plusAnc a)
          = ∑ a', star (V i (w, a')) * V i (w, a') * ∑ a, star (plusAnc a) * plusAnc a := by
            refine Finset.sum_congr rfl fun a' _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
        _ = _ := by rw [sum_plusAnc_sq]; simp
  calc ∑ p : FacIdx ι, ∑ a, star (factoryOutV V p a) * factoryOutV V p a
      = ∑ i, ∑ w, ∑ a', ∑ a, star (factoryOutV V (i, w, a') a) * factoryOutV V (i, w, a') a := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ i, ∑ w, ∑ a, star (V i (w, a)) * V i (w, a) := by simp only [hrow]
    _ = 1 := by
        rw [← hV]
        simp only [Fintype.sum_prod_type]

theorem goodAnc_factoryOutV {ι : Type} {V : ι → (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ}
    (h : ∀ i w, Accepts w → GoodAnc fun a => V i (w, a)) (p : FacIdx ι) :
    GoodAnc (factoryOutV V p) := by
  obtain ⟨i, w, a'⟩ := p
  by_cases hw : Accepts w
  · by_cases ha : a' = 0
    · simp only [factoryOutV, hw, ha, ↓reduceIte]
      exact h i w hw
    · simp only [factoryOutV, hw, ha, ↓reduceIte]
      exact Or.inl isPeriodic_zero
  · simp only [factoryOutV, hw, ↓reduceIte]
    exact Or.inl (isPeriodic_plusAnc.smul _)

theorem factoryOutV_eq_smul {ι : Type} {V : ι → (Fin 7 → Fin 2) × (Fin 7 → Fin 2) → ℂ}
    (h : ∀ i w, ∃ c : ℂ, (fun a => V i (w, a)) = c • plusAnc) (p : FacIdx ι) :
    ∃ c : ℂ, factoryOutV V p = c • plusAnc := by
  obtain ⟨i, w, a'⟩ := p
  by_cases hw : Accepts w
  · by_cases ha : a' = 0
    · simp only [factoryOutV, hw, ha, ↓reduceIte]
      exact h i w
    · simp only [factoryOutV, hw, ha, ↓reduceIte]
      exact ⟨0, (zero_smul ℂ plusAnc).symm⟩
  · simp only [factoryOutV, hw, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- ★★ **The factory under a fault pattern**: its output ancillas, branch by branch. -/
def facOut {κ : Type} (Φ : FacFaults κ) (b : FacLoc → Bool) :
    FacIdx (FacBranch κ) → (Fin 7 → Fin 2) → ℂ :=
  factoryOutV (facVec Φ b)

/-- ★★ **The factory's branches carry weight one, under every pattern.** -/
theorem facOut_norm {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (b : FacLoc → Bool) :
    ∑ p, ∑ a, star (facOut Φ b p a) * facOut Φ b p a = 1 :=
  factoryOutV_norm (sum_facVec_sq hΦ b)

/-- ★★ **A fault-free factory prepares `|+̄⟩`**, up to a scalar in each branch. -/
theorem facOut_none {κ : Type} (Φ : FacFaults κ) (p : FacIdx (FacBranch κ)) :
    ∃ c : ℂ, facOut Φ (fun _ => false) p = c • plusAnc := by
  refine factoryOutV_eq_smul (fun s w => ?_) p
  obtain ⟨c, hc⟩ := verUnder_none Φ.pair Φ.read s.2
  obtain ⟨c', hc'⟩ := facIn_none Φ.encA Φ.encB s.1
  refine ⟨c * c' * ((hadTransversal 7 *ᵥ plusAnc) w), funext fun a => ?_⟩
  have h := readVec_apply 1 w a
  rw [one_kronecker_one, Matrix.one_mul, Matrix.one_mul] at h
  simp only [facVec, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h]
  ring

/-- ★★★ **One fault anywhere in the factory leaves a good ancilla in every branch**: a fault in the
ancilla's encoder is caught by the checker up to `X` errors, a fault in the checker's encoder or at
its readout leaves `X` errors only, a fault on a verification pair leaves an error on one qubit. -/
theorem goodAnc_facOut_single {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (ℓ : FacLoc)
    (p : FacIdx (FacBranch κ)) : GoodAnc (facOut Φ (fun ℓ' => decide (ℓ' = ℓ)) p) := by
  refine goodAnc_factoryOutV (fun s w hw => ?_) p
  rcases ℓ with e | e | j | j
  · -- the ancilla's encoder
    have hB : (fun l => decide ((Sum.inr (Sum.inl l) : FacLoc) = Sum.inl e)) = fun _ => false :=
      funext fun _ => by simp
    have hP : (fun j => decide ((Sum.inr (Sum.inr (Sum.inl j)) : FacLoc) = Sum.inl e))
        = fun _ => false := funext fun _ => by simp
    have hR : (fun j => decide ((Sum.inr (Sum.inr (Sum.inr j)) : FacLoc) = Sum.inl e))
        = fun _ => false := funext fun _ => by simp
    obtain ⟨c, hc⟩ := verUnder_none Φ.pair Φ.read s.2
    obtain ⟨c', hc'⟩ := facIn_noneB Φ.encA Φ.encB (fun l => decide ((Sum.inl l : FacLoc) = Sum.inl e)) s.1
    have h := (isPeriodic_verifyVec_A (encUnder Φ.encA
      (fun l => decide ((Sum.inl l : FacLoc) = Sum.inl e)) s.1.1 *ᵥ plusInit) hw).smul (c * c')
    refine Or.inl ?_
    convert h using 1
    funext a
    simp only [facVec, hB, hP, hR, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  · -- the checker's encoder
    have hA : (fun l => decide ((Sum.inl l : FacLoc) = Sum.inr (Sum.inl e))) = fun _ => false :=
      funext fun _ => by simp
    have hP : (fun j => decide ((Sum.inr (Sum.inr (Sum.inl j)) : FacLoc) = Sum.inr (Sum.inl e)))
        = fun _ => false := funext fun _ => by simp
    have hR : (fun j => decide ((Sum.inr (Sum.inr (Sum.inr j)) : FacLoc) = Sum.inr (Sum.inl e)))
        = fun _ => false := funext fun _ => by simp
    obtain ⟨c, hc⟩ := verUnder_none Φ.pair Φ.read s.2
    obtain ⟨c', hc'⟩ := facIn_noneA Φ.encA Φ.encB
      (fun l => decide ((Sum.inr (Sum.inl l) : FacLoc) = Sum.inr (Sum.inl e))) s.1
    have h := (isPeriodic_verifyVec_B (encUnder Φ.encB
      (fun l => decide ((Sum.inr (Sum.inl l) : FacLoc) = Sum.inr (Sum.inl e))) s.1.2 *ᵥ plusInit)
      w).smul (c * c')
    refine Or.inl ?_
    convert h using 1
    funext a
    simp only [facVec, hA, hP, hR, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  · -- a verification pair
    have hA : (fun l => decide ((Sum.inl l : FacLoc) = Sum.inr (Sum.inr (Sum.inl j))))
        = fun _ => false := funext fun _ => by simp
    have hB : (fun l => decide ((Sum.inr (Sum.inl l) : FacLoc) = Sum.inr (Sum.inr (Sum.inl j))))
        = fun _ => false := funext fun _ => by simp
    have hP : (fun j' => decide ((Sum.inr (Sum.inr (Sum.inl j')) : FacLoc)
        = Sum.inr (Sum.inr (Sum.inl j)))) = fun j' => decide (j' = j) := funext fun _ => by simp
    have hR : (fun j' => decide ((Sum.inr (Sum.inr (Sum.inr j')) : FacLoc)
        = Sum.inr (Sum.inr (Sum.inl j)))) = fun _ => false := funext fun _ => by simp
    obtain ⟨c, hc⟩ := verUnder_pair Φ.pair Φ.read (fun j' => decide (j' = j)) s.2
    obtain ⟨c', hc'⟩ := facIn_none Φ.encA Φ.encB s.1
    obtain ⟨N, hN⟩ := verifyOut_pairFault (onPair_roundKraus_single (hΦ.pair_on j) s.2.1) w
    have h : GoodAnc (gateOf j N *ᵥ plusAnc) := Or.inr ⟨j, N, rfl⟩
    convert h.smul (c * c') using 1
    funext a
    have ha := congrFun hN a
    simp only [verifyOut] at ha
    simp only [facVec, hA, hB, hP, hR, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul, ha]
    ring
  · -- a checker readout
    have hA : (fun l => decide ((Sum.inl l : FacLoc) = Sum.inr (Sum.inr (Sum.inr j))))
        = fun _ => false := funext fun _ => by simp
    have hB : (fun l => decide ((Sum.inr (Sum.inl l) : FacLoc) = Sum.inr (Sum.inr (Sum.inr j))))
        = fun _ => false := funext fun _ => by simp
    have hP : (fun j' => decide ((Sum.inr (Sum.inr (Sum.inl j')) : FacLoc)
        = Sum.inr (Sum.inr (Sum.inr j)))) = fun _ => false := funext fun _ => by simp
    obtain ⟨c, hc⟩ := verUnder_read Φ.pair Φ.read
      (fun j' => decide ((Sum.inr (Sum.inr (Sum.inr j')) : FacLoc) = Sum.inr (Sum.inr (Sum.inr j))))
      s.2
    obtain ⟨c', hc'⟩ := facIn_none Φ.encA Φ.encB s.1
    refine Or.inl ?_
    convert isPeriodic_plusAnc.smul (c * c' * (((roundKraus Φ.read
      (fun j' => decide ((Sum.inr (Sum.inr (Sum.inr j')) : FacLoc) = Sum.inr (Sum.inr (Sum.inr j))))
      s.2.2) * hadTransversal 7) *ᵥ plusAnc) w) using 1
    funext a
    simp only [facVec, hA, hB, hP, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul, readVec_apply]
    ring

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
