/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneMethod
public import CsdLean4.Empirical.QM.QEC.SteaneMachineConcat

/-!
# The faulty recovery as a correctable deviation

**Category:** 3-Local (Empirical, QM twin). BACKLOG #232 (split from ~~#229~~).

`ExtendedRectangle.lean` (~~#96~~) lets the leading recovery of an extended rectangle be faulty, as the
hypothesis `DeviatesBy P D id R₁`, and `SteaneMachine.lean` (~~#207~~) instantiated it with `D` the
weight-one unitary errors and left the hypothesis standing. `SteaneMethod.lean` (~~#229~~'s brick)
built the recovery as a circuit — Steane's method — and showed one extraction fault leaves a mixture of
errors on one data qubit. This module closes the gap: it fixes a correctable set that such a mixture
belongs to, proves the recovery corrects it and the gadgets carry it, and so turns the faulty recovery
into a **theorem** about a circuit inside the rectangle.

## The correctable set

The weight-one *unitary* errors are not enough: a fault leaves a *mixture*, and a fault in ancilla
preparation (#234) can leave an `X` and a `Z` on **different** qubits, which a CSS code still corrects.

* `CssErr`, `oneBit`, `cssPauli` — **the sixty-four errors** `X^a Z^b`, `wt a ≤ 1`, `wt b ≤ 1`;
  `cssSyn`, ★ `cssSyn_injective` — the decoder tells them apart;
* ★★★ `circuitRecovery_css_cross` — **the recovery circuit's Knill–Laflamme property for all sixty-four,
  cross terms included**, with the identity matrix of scalars (`recKraus_mul_pauliMat_mul_steaneProj_of_decode`);
* `cssSpan`, ★ `gateOf_mem_cssSpan` — every operator on one qubit is a combination of them;
* ★★ `cssMix` — **the correctable set**: maps `ρ ↦ Σ_b K_b ρ K_bᴴ` with every `K_b` in the span and
  `P (Σ_b K_bᴴ K_b) P = P`; `id_mem_cssMix`, ★ `conj_cssPauli_mem_cssMix` (`X` and `Z` on different
  qubits included), ★★ `weightOne_subset_cssMix` — ~~#207~~'s set sits inside.

## The three properties

* ★★★ `isRecovery_cssMix` — **the recovery circuit is a recovery for the class** (bilinearity,
  `recovery_apply_lin_comb`, and the trace on the code fixes the scalar at `1`);
  ★★ `isRecovery_methodRecovery_cssMix` — so is Steane's method;
* `propagatesD_cssMix_of_unitary`, ★★ `Gadget.propagatesD_cssMix` — **the transversal `H̄`, `X̄`, `Z̄`
  carry the class** (the Hadamard swaps the two labels, `X̄` and `Z̄` keep them);
* `OnPair`, `faultReadOp`, `bitFaultOp`, `phaseFaultOp`, ★★ `atQubit_bitFaultOp` /
  `atQubit_phaseFaultOp` — **a fault is any operator on data qubit `q` and ancilla qubit `q`**, by
  linearity from ~~#229~~'s product faults; `sum_ancRead_conjTranspose_mul`, `ancPrep_conjTranspose_mul`,
  `sum_plusAnc_sq`, `sum_faultReadOp_conjTranspose_mul`, `faultyKraus_tp` — with a **unitary** fault
  the faulty method is a channel, ★★ `faultyMethod`;
* ★★★ `deviatesBy_cssMix_of_atQubit` — a channel whose every branch acts on the code on one qubit is a
  CSS deviation of the identity; ★★★ `deviatesBy_faultyMethod` — **Steane's method with one fault is
  #96's `DeviatesBy`, discharged**; ★★★ `methodRecovery_faultyMethod` — one fault in a recovery is
  removed by the next.

## The rectangle

★★★ `steane_exRec_faultyMethod` — **#96's extended rectangle at the Steane code with every piece a
circuit**: a fault in the leading run of Steane's method, or in the gadget, is corrected; a fault in the
trailing run hands on a CSS deviation that the next recovery corrects.

## Honest scope

⚠️ **Ancilla preparation is ideal.** The faults are at extraction locations: a unitary on data qubit
`q` and ancilla qubit `q` after the transversal `CNOT` of either round, which covers a faulty `CNOT` and
a fault on the ancilla qubit before it is read. A fault before the `CNOT` at `q` is the conjugated fault
after it; that rewriting is not proved here. Faults in preparing `|+̄⟩` are #234. ▸ The rewriting
is `readAround_eq` in `SteaneFaultModel.lean` (BACKLOG ~~#235~~).

⚠️ **One rectangle, not the machine.** The trailing-fault case hands on a deviation; chaining
overlapping rectangles, with the recovery's own locations counted in the fault pattern, is #233.
`steane_machine` and `steane_machine_circuit` still put faults at the gadgets only. ▸ The machine
with every recovery's extraction locations counted is `SteaneOverlapMachine.lean`
(`steane_machine_overlap`, BACKLOG ~~#233~~).

⚠️ **Unitary faults.** `faultyMethod` needs `Fᴴ F = 1`, so the faulty method is a channel; a fault that
is itself a channel (several Kraus operators) is a mixture of such runs and is not restated. ▸ It
is restated in `SteaneFaultModel.lean` (`channelMethod`, `deviatesBy_channelMethod`, BACKLOG ~~#235~~).

⚠️ **One round per basis**, as in ~~#228~~ and ~~#229~~; no repeated syndrome measurement.

References: A. Steane, PRL 78 (1997) 2252; P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf.
Comput. 6 (2006) 97; E. Knill, R. Laflamme, PRA 55 (1997) 900; `specs/BACKLOG.md` #232, #229, #233,
#234, #228, #207, #96; `Mathlib/QuantumInfo/ExtendedRectangle.lean`, `Mathlib/QuantumInfo/KnillLaflamme.lean`,
`Empirical/QM/QEC/SteaneMethod.lean`, `Empirical/QM/QEC/SteaneCircuitRecovery.lean`,
`Empirical/QM/QEC/SteaneMachine.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker

noncomputable section

namespace QuantumInfo

section Generic

variable {n : Type*} [Fintype n]

/-- **More correctable deviations is a weaker hypothesis**: a deviation in `D` is one in any larger
set. -/
theorem DeviatesBy.mono {P : Matrix n n ℂ} {D D' : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {ideal actual : Matrix n n ℂ → Matrix n n ℂ} (h : DeviatesBy P D ideal actual) (hD : D ⊆ D') :
    DeviatesBy P D' ideal actual := fun ρ hρ => by
  obtain ⟨E, hE, h⟩ := h ρ hρ
  exact ⟨E, hD hE, h⟩

/-- **A recovery for a set is a recovery for every subset.** -/
theorem IsRecovery.anti {P : Matrix n n ℂ} {R : Matrix n n ℂ → Matrix n n ℂ}
    {D D' : Set (Matrix n n ℂ → Matrix n n ℂ)} (h : IsRecovery P R D) (hD : D' ⊆ D) :
    IsRecovery P R D' := fun E hE => h E (hD hE)

/-- A Pauli is unitary from either side: `E Eᴴ = 1`. -/
theorem pauliMat_mul_conjTranspose_self {m : ℕ} (a b : Fin m → Fin 2) :
    pauliMat a b * (pauliMat a b)ᴴ = 1 :=
  mul_eq_one_comm.1 (pauliMat_conjTranspose_mul_self a b)

/-- **Conjugating a Pauli by a Pauli gives the same Pauli up to the symplectic sign.** -/
theorem pauliMat_conj {m : ℕ} (c d a b : Fin m → Fin 2) :
    pauliMat c d * pauliMat a b * (pauliMat c d)ᴴ = signChar (bdot c b + bdot d a) • pauliMat a b := by
  rw [pauliMat_comm c d a b, Matrix.smul_mul, Matrix.mul_assoc, pauliMat_mul_conjTranspose_self,
    Matrix.mul_one]

/-- Two channels in sequence: Kraus operators `Y k X i` are trace-preserving when both families are. -/
theorem sum_mul_conjTranspose_mul_of_tp {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq n]
    {X : ι → Matrix n n ℂ} {Y : κ → Matrix n n ℂ} (hX : ∑ i, (X i)ᴴ * X i = 1)
    (hY : ∑ k, (Y k)ᴴ * Y k = 1) : ∑ p : ι × κ, (Y p.2 * X p.1)ᴴ * (Y p.2 * X p.1) = 1 := by
  rw [Fintype.sum_prod_type]
  calc ∑ i, ∑ k, (Y k * X i)ᴴ * (Y k * X i) = ∑ i, (X i)ᴴ * (∑ k, (Y k)ᴴ * Y k) * X i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by simp only [hY, Matrix.mul_one]; exact hX

end Generic

namespace Controlled

/-- The adjoint of an operator on one qubit is the adjoint on that qubit. -/
theorem gateOf_conjTranspose {m : ℕ} (q : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (gateOf q M)ᴴ = gateOf q Mᴴ := by
  rw [← blockKron_single_eq_gateOf, blockKron_conjTranspose, ← blockKron_single_eq_gateOf]
  congr 1
  funext b
  by_cases h : b = q
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, conjTranspose_one]

end Controlled

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Reading the ancilla is a complete measurement**: `Σ_m (read m)ᴴ (read m) = 1`. -/
theorem sum_ancRead_conjTranspose_mul :
    ∑ m : β, (ancRead m : Matrix α (α × β) ℂ)ᴴ * ancRead m = 1 := by
  ext p p'
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, ancRead, Matrix.of_apply,
    Matrix.one_apply]
  have h : ∀ (m : β) (z : α), star (if p = (z, m) then (1 : ℂ) else 0) * (if p' = (z, m) then 1 else 0)
      = if (z, m) = p ∧ p = p' then 1 else 0 := by
    intro m z
    by_cases h1 : p = (z, m) <;> by_cases h2 : p' = (z, m) <;> simp_all [eq_comm]
  simp only [h]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type'
    (f := fun z m => if ((z, m) : α × β) = p ∧ p = p' then (1 : ℂ) else 0)]
  simp only [Prod.mk.eta, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq β] in
/-- **Preparing the ancilla in `ψ` is an isometry when `ψ` is normalised**:
`(prep ψ)ᴴ (prep ψ) = ‖ψ‖² · 1`. -/
theorem ancPrep_conjTranspose_mul (ψ : β → ℂ) :
    (ancPrep ψ : Matrix (α × β) α ℂ)ᴴ * ancPrep ψ = (∑ a, star (ψ a) * ψ a) • (1 : Matrix α α ℂ) := by
  ext z z'
  simp only [Matrix.mul_apply, conjTranspose_apply, ancPrep, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  by_cases h : z = z'
  · subst h
    simp
  · simp [h, Ne.symm h]

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The 64 errors of the CSS code -/

/-- **The errors a CSS reading of the Steane code corrects**: an `X` on at most one qubit and a `Z`
on at most one qubit, independently — sixty-four of them. -/
abbrev CssErr : Type := Option (Fin 7) × Option (Fin 7)

/-- A bit label of weight at most one: nothing, or a flip at one qubit. -/
def oneBit : Option (Fin 7) → Fin 7 → Fin 2
  | none => 0
  | some i => unitErr i

/-- The Pauli of a CSS error: `X^{oneBit e.1} Z^{oneBit e.2}`. -/
def cssPauli (e : CssErr) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (oneBit e.1) (oneBit e.2)

theorem decode_syndrome_oneBit (o : Option (Fin 7)) : decode (syndrome (oneBit o)) = oneBit o :=
  decode_syndrome_of (by cases o with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩)

theorem oneBit_injective : Function.Injective oneBit := by
  intro o o' h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j =>
      have := congrFun h j
      simp [oneBit, unitErr_apply] at this
  | some i =>
    cases o' with
    | none =>
      have := congrFun h i
      simp [oneBit, unitErr_apply] at this
    | some j =>
      have := congrFun h i
      simp only [oneBit, unitErr_apply, ite_true] at this
      by_cases hij : i = j
      · rw [hij]
      · rw [ite_eq_right hij] at this
        exact absurd this (by decide)

/-- The syndrome pair a CSS error is read as. -/
def cssSyn (e : CssErr) : SynPair := (syndrome (oneBit e.1), syndrome (oneBit e.2))

/-- ★ **The decoder tells the sixty-four errors apart**: distinct errors have distinct syndrome pairs. -/
theorem cssSyn_injective : Function.Injective cssSyn := by
  intro e e' h
  have h1 := congrArg (fun st : SynPair => decode st.1) h
  have h2 := congrArg (fun st : SynPair => decode st.2) h
  simp only [cssSyn, decode_syndrome_oneBit] at h1 h2
  exact Prod.ext (oneBit_injective h1) (oneBit_injective h2)

/-- A branch of the recovery circuit on a Pauli error the decoder inverts. -/
theorem recKraus_mul_pauliMat_mul_steaneProj_of_decode (st : SynPair) {a b : Fin 7 → Fin 2}
    (ha : decode (syndrome a) = a) (hb : decode (syndrome b) = b) :
    recKraus st * pauliMat a b * steaneProj
      = if st = (syndrome a, syndrome b) then pauliSign b a • steaneProj else 0 := by
  obtain ⟨s, t⟩ := st
  rw [recKraus_eq]
  have hassoc : pauliMat (decode s) (decode t) * phaseProj t * bitProj s
        * pauliMat a b * steaneProj
      = pauliMat (decode s) (decode t)
          * (phaseProj t * (bitProj s * pauliMat a b * steaneProj)) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, bitProj_mul_pauliMat_mul_steaneProj]
  by_cases hs : s = syndrome a
  · rw [ite_eq_left hs, ← Matrix.mul_assoc (phaseProj t), phaseProj_mul_pauliMat_mul_steaneProj]
    by_cases ht : t = syndrome b
    · rw [ite_eq_left ht, ite_eq_left (by rw [hs, ht]), hs, ht, ha, hb, ← Matrix.mul_assoc,
        pauliMat_mul]
      have ha' : a + a = 0 := by funext q; exact fin2_add_self _
      have hb' : b + b = 0 := by funext q; exact fin2_add_self _
      rw [ha', hb', pauliMat_zero, Matrix.smul_mul, Matrix.one_mul]
    · rw [ite_eq_right ht, ite_eq_right (by intro h; exact ht (Prod.mk.inj h).2), Matrix.mul_zero]
  · rw [ite_eq_right hs, ite_eq_right (by intro h; exact hs (Prod.mk.inj h).1), Matrix.mul_zero,
      Matrix.mul_zero]

/-- ★★★ **The recovery circuit corrects all sixty-four CSS errors, cross terms included**: the
Knill–Laflamme property for the family `X^a Z^b`, `wt a, wt b ≤ 1`, with the identity matrix of
scalars. The decoder inverts the two syndromes separately, so an `X` and a `Z` on different qubits are
corrected as well as on the same one. -/
theorem circuitRecovery_css_cross :
    ∀ ρ, ρ = steaneProj * ρ * steaneProj →
      ∀ e e' : CssErr, circuitRecovery.apply (cssPauli e * ρ * (cssPauli e')ᴴ)
        = (1 : Matrix CssErr CssErr ℂ) e' e • ρ := by
  intro ρ hρ e e'
  have hP : steaneProjᴴ = steaneProj := isCodeProjector_steaneProj.conjTranspose_eq
  have hrec : ∀ (st : SynPair) (f : CssErr), recKraus st * cssPauli f * steaneProj
      = if st = cssSyn f then pauliSign (oneBit f.2) (oneBit f.1) • steaneProj else 0 :=
    fun st f => recKraus_mul_pauliMat_mul_steaneProj_of_decode st (decode_syndrome_oneBit f.1)
      (decode_syndrome_oneBit f.2)
  have hterm : ∀ st : SynPair,
      recKraus st * (cssPauli e * ρ * (cssPauli e')ᴴ) * (recKraus st)ᴴ
        = (recKraus st * cssPauli e * steaneProj) * ρ
          * (recKraus st * cssPauli e' * steaneProj)ᴴ := by
    intro st
    rw [conjTranspose_mul, conjTranspose_mul, hP]
    conv_lhs => rw [hρ]
    simp only [Matrix.mul_assoc]
  show ∑ st : SynPair, recKraus st * _ * (recKraus st)ᴴ = _
  rw [Finset.sum_congr rfl fun st _ => hterm st]
  simp only [hrec]
  rw [Finset.sum_eq_single (cssSyn e)]
  · rw [ite_eq_left rfl]
    by_cases hee : e = e'
    · subst hee
      have hl : star (pauliSign (oneBit e.2) (oneBit e.1)) * pauliSign (oneBit e.2) (oneBit e.1)
          = 1 := by
        rw [Complex.star_def, conj_pauliSign, pauliSign_mul_self]
      rw [ite_eq_left rfl, Matrix.one_apply_eq, one_smul, conjTranspose_smul, hP]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hl, one_smul]
      exact hρ.symm
    · rw [ite_eq_right (fun h => hee (cssSyn_injective h)), conjTranspose_zero,
        Matrix.mul_zero, Matrix.one_apply_ne (Ne.symm hee), zero_smul]
  · intro st _ hst
    rw [ite_eq_right hst, Matrix.zero_mul, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The correctable set: mixtures of CSS errors -/

/-- The operators the CSS errors span. -/
def cssSpan : Submodule ℂ (Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :=
  Submodule.span ℂ (Set.range cssPauli)

theorem cssPauli_mem_cssSpan (e : CssErr) : cssPauli e ∈ cssSpan :=
  Submodule.subset_span ⟨e, rfl⟩

/-- Every single-qubit Pauli of the corpus's error family is a CSS error. -/
theorem exists_cssPauli_eq (i : SingleErr) : ∃ e, cssPauli e = pauliMat (errA i) (errB i) := by
  rcases i with _ | ⟨j, t⟩
  · exact ⟨(none, none), rfl⟩
  · fin_cases t
    · exact ⟨(some j, none), by simp [cssPauli, oneBit, errA, errB]⟩
    · exact ⟨(none, some j), by simp [cssPauli, oneBit, errA, errB]⟩
    · exact ⟨(some j, some j), by simp [cssPauli, oneBit, errA, errB]⟩

/-- ★ **Every operator on one qubit is in the CSS span.** -/
theorem gateOf_mem_cssSpan (q : Fin 7) (M : Matrix (Fin 2) (Fin 2) ℂ) : gateOf q M ∈ cssSpan := by
  rw [gateOf_eq_sum_pauliMat q M]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨e, he⟩ := exists_cssPauli_eq i
  rw [← he]
  exact cssPauli_mem_cssSpan e

/-- ★★ **The CSS correctable set**: the maps `ρ ↦ Σ_b K_b ρ K_bᴴ` whose Kraus operators are
combinations of the sixty-four CSS errors and which preserve the trace on the code,
`P (Σ_b K_bᴴ K_b) P = P`. A mixture of errors, each an `X` on at most one qubit times a `Z` on at most
one qubit — not necessarily the same one. -/
def cssMix : Set (Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :=
  {E | ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ),
    (∀ b, K b ∈ cssSpan) ∧ steaneProj * (∑ b, (K b)ᴴ * K b) * steaneProj = steaneProj
      ∧ E = fun ρ => ∑ b, K b * ρ * (K b)ᴴ}

/-- One Kraus operator `K` with `Kᴴ K = 1` on the code is a member. -/
theorem conj_mem_cssMix {K : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hK : K ∈ cssSpan)
    (htp : steaneProj * (Kᴴ * K) * steaneProj = steaneProj) :
    (fun ρ => K * ρ * Kᴴ) ∈ cssMix :=
  ⟨Unit, inferInstance, fun _ => K, fun _ => hK, by rw [Fintype.sum_unique]; exact htp,
    funext fun ρ => by rw [Fintype.sum_unique]⟩

/-- "No error" is correctable. -/
theorem id_mem_cssMix : id ∈ cssMix := by
  have h := conj_mem_cssMix (cssPauli_mem_cssSpan (none, none)) (by
    rw [cssPauli, pauliMat_conjTranspose_mul_self, Matrix.mul_one,
      isCodeProjector_steaneProj.mul_self])
  have he : cssPauli (none, none) = 1 := pauliMat_zero
  rw [he] at h
  convert h using 1
  funext ρ
  rw [id, Matrix.one_mul, conjTranspose_one, Matrix.mul_one]

/-- ★ **Each CSS error is correctable**, `X` and `Z` on different qubits included. -/
theorem conj_cssPauli_mem_cssMix (e : CssErr) :
    (fun ρ => cssPauli e * ρ * (cssPauli e)ᴴ) ∈ cssMix :=
  conj_mem_cssMix (cssPauli_mem_cssSpan e) (by
    rw [cssPauli, pauliMat_conjTranspose_mul_self, Matrix.mul_one,
      isCodeProjector_steaneProj.mul_self])

/-- ★★ **The weight-one unitary errors are CSS errors**: #207's correctable set sits inside this one. -/
theorem weightOne_subset_cssMix : weightOne ⊆ cssMix := by
  rintro _ ⟨q, M, hM, rfl⟩
  refine conj_mem_cssMix (gateOf_mem_cssSpan q M) ?_
  have hMM : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 hM
  rw [gateOf_conjTranspose, ← Controlled.gateOf_mul, hMM, gateOf_one, Matrix.mul_one,
    isCodeProjector_steaneProj.mul_self]

/-! ### The recovery corrects the class -/

/-- ★★★ **The recovery circuit is a recovery for the CSS mixtures**, in #96's sense: every Kraus
operator is a combination of the sixty-four errors, so the circuit returns a multiple of the code
state (`recovery_apply_lin_comb` on `circuitRecovery_css_cross`), and trace preservation on the code
makes the multiple `1`. -/
theorem isRecovery_cssMix : IsRecovery steaneProj circuitRecovery.apply cssMix := by
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩ ρ hρ
  show circuitRecovery.apply (∑ b, K b * ρ * (K b)ᴴ) = ρ
  choose a ha using fun b => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hK b)
  have happ : ∀ σ, σ = steaneProj * σ * steaneProj →
      circuitRecovery.apply (∑ b, K b * σ * (K b)ᴴ) = (∑ b, ∑ e, star (a b e) * a b e) • σ := by
    intro σ hσ
    rw [Channel.apply_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← ha b, recovery_apply_lin_comb circuitRecovery_css_cross (a b) hσ]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_eq_single e (fun e' _ he' => by rw [Matrix.one_apply_ne (Ne.symm he'), mul_zero])
      (fun h => absurd (Finset.mem_univ e) h), Matrix.one_apply_eq, mul_one]
  have hP := isCodeProjector_steaneProj
  have hone : (∑ b, ∑ e, star (a b e) * a b e) = 1 := by
    have h := congrArg Matrix.trace (happ steaneProj (by rw [hP.mul_self, hP.mul_self]))
    have htr : (∑ b, K b * steaneProj * (K b)ᴴ).trace = 2 := by
      rw [Matrix.trace_sum]
      simp_rw [Matrix.trace_mul_cycle (K _) steaneProj (K _)ᴴ]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, ← hP.mul_self, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, htp, trace_steaneProj]
    rw [Channel.apply_trace, htr, Matrix.trace_smul, trace_steaneProj, smul_eq_mul] at h
    linear_combination -h / 2
  rw [happ ρ hρ, hone, one_smul]

/-- ★★ **And so is Steane's method**, which is the same channel (`methodRecovery_apply`). -/
theorem isRecovery_methodRecovery_cssMix : IsRecovery steaneProj methodRecovery.apply cssMix := by
  have h : methodRecovery.apply = circuitRecovery.apply := funext methodRecovery_apply
  rw [h]
  exact isRecovery_cssMix

/-! ### The gadgets carry the class -/

/-- **A unitary commuting with the code projector and carrying CSS errors to CSS combinations carries
the class**: #96's `PropagatesD` for conjugation by `g`. -/
theorem propagatesD_cssMix_of_unitary {g : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hgg : gᴴ * g = 1) (hgP : g * steaneProj = steaneProj * g)
    (hspan : ∀ e, g * cssPauli e * gᴴ ∈ cssSpan) :
    PropagatesD steaneProj cssMix (fun ρ => g * ρ * gᴴ) := by
  have hP := isCodeProjector_steaneProj
  have hgg' : g * gᴴ = 1 := mul_eq_one_comm.1 hgg
  have hgP' : gᴴ * steaneProj = steaneProj * gᴴ := by
    have h := congrArg conjTranspose hgP
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq] at h
    exact h.symm
  have hmem : ∀ K, K ∈ cssSpan → g * K * gᴴ ∈ cssSpan := by
    intro K hK
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hK
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem _ _ (hspan e)
  rintro _ ⟨ι, _, K, hK, htp, rfl⟩ ρ _
  have hterm : ∀ b, (g * K b * gᴴ)ᴴ * (g * K b * gᴴ) = g * ((K b)ᴴ * K b) * gᴴ := by
    intro b
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc g * ((K b)ᴴ * gᴴ) * (g * K b * gᴴ) = g * (K b)ᴴ * (gᴴ * g) * K b * gᴴ := by
          simp only [Matrix.mul_assoc]
      _ = g * ((K b)ᴴ * K b) * gᴴ := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨fun σ => ∑ b, (g * K b * gᴴ) * σ * (g * K b * gᴴ)ᴴ,
    ⟨ι, inferInstance, fun b => g * K b * gᴴ, fun b => hmem _ (hK b), ?_, rfl⟩, ?_⟩
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

namespace Gadget

theorem blockKron_mul_steaneProj (G : Gadget) :
    blockKron (fun _ : Fin 7 => G.gate) * steaneProj = steaneProj * blockKron (fun _ : Fin 7 => G.gate) := by
  cases G with
  | had => exact steaneProj_mul_hadTransversal.symm
  | x =>
    show blockKron (fun _ : Fin 7 => pX) * steaneProj = steaneProj * blockKron (fun _ : Fin 7 => pX)
    rw [blockKron_pX_eq_pauliMat]
    exact logicalX_mul_steaneProj
  | z =>
    show blockKron (fun _ : Fin 7 => pZ) * steaneProj = steaneProj * blockKron (fun _ : Fin 7 => pZ)
    rw [blockKron_pZ_eq_pauliMat]
    exact logicalZ_mul_steaneProj

theorem conjTranspose_blockKron_mul (G : Gadget) :
    (blockKron fun _ : Fin 7 => G.gate)ᴴ * blockKron (fun _ : Fin 7 => G.gate) = 1 := by
  rw [blockKron_conjTranspose, blockKron_mul]
  simp only [G.gate_conjTranspose_mul]
  exact blockKron_one

/-- A transversal gadget carries a CSS error to a CSS error, up to a sign: the Hadamard swaps the
`X` and `Z` labels, the logical `X̄` and `Z̄` keep them. -/
theorem conj_cssPauli_mem_cssSpan (G : Gadget) (e : CssErr) :
    blockKron (fun _ : Fin 7 => G.gate) * cssPauli e * (blockKron fun _ : Fin 7 => G.gate)ᴴ
      ∈ cssSpan := by
  cases G with
  | had =>
    show hadTransversal 7 * cssPauli e * (hadTransversal 7)ᴴ ∈ cssSpan
    rw [hadTransversal_conjTranspose, cssPauli, hadTransversal_conj_pauliMat]
    exact Submodule.smul_mem _ _ (cssPauli_mem_cssSpan (e.2, e.1))
  | x =>
    show blockKron (fun _ : Fin 7 => pX) * cssPauli e * (blockKron fun _ : Fin 7 => pX)ᴴ ∈ cssSpan
    rw [blockKron_pX_eq_pauliMat, cssPauli, pauliMat_conj]
    exact Submodule.smul_mem _ _ (cssPauli_mem_cssSpan e)
  | z =>
    show blockKron (fun _ : Fin 7 => pZ) * cssPauli e * (blockKron fun _ : Fin 7 => pZ)ᴴ ∈ cssSpan
    rw [blockKron_pZ_eq_pauliMat, cssPauli, pauliMat_conj]
    exact Submodule.smul_mem _ _ (cssPauli_mem_cssSpan e)

/-- ★★ **Transversality for the CSS class**: every gadget of the set carries a CSS mixture on a code
state to a CSS mixture on its output — #96's `PropagatesD`, for the set the faulty recovery needs. -/
theorem propagatesD_cssMix (G : Gadget) : PropagatesD steaneProj cssMix G.ideal :=
  propagatesD_cssMix_of_unitary G.conjTranspose_blockKron_mul G.blockKron_mul_steaneProj
    G.conj_cssPauli_mem_cssSpan

end Gadget

/-! ### Steane's method with one fault -/

/-- **An operator on data qubit `q` and ancilla qubit `q` only**: a sum of products of an operator on
each. Every two-qubit operator on that pair has this form. -/
def OnPair (q : Fin 7)
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) : Prop :=
  ∃ (r : ℕ) (A B : Fin r → Matrix (Fin 2) (Fin 2) ℂ), F = ∑ k, gateOf q (A k) ⊗ₖ gateOf q (B k)

/-- **Steane's extraction with the operator `F` after the transversal `CNOT`.** -/
def faultReadOp
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * F * tCNOT
    * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

/-- The bit round with `F` at its extraction. -/
def bitFaultOp
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (decode (syndrome m)) 0 * faultReadOp F m

/-- The phase round with `F` at its extraction. -/
def phaseFaultOp
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat 0 (decode (syndrome m)) * (hadTransversal 7 * faultReadOp F m * hadTransversal 7)

theorem faultReadOp_one (m : Fin 7 → Fin 2) : faultReadOp 1 m = steaneRead m := by
  rw [faultReadOp, Matrix.mul_one]

theorem bitFaultOp_one (m : Fin 7 → Fin 2) : bitFaultOp 1 m = bitRound m := by
  rw [bitFaultOp, faultReadOp_one, bitRound]

theorem phaseFaultOp_one (m : Fin 7 → Fin 2) : phaseFaultOp 1 m = phaseRound m := by
  rw [phaseFaultOp, faultReadOp_one, phaseRound]

theorem faultReadOp_sum {r : ℕ}
    (F : Fin r → Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (m : Fin 7 → Fin 2) : faultReadOp (∑ k, F k) m = ∑ k, faultReadOp (F k) m := by
  simp only [faultReadOp, Matrix.mul_sum, Matrix.sum_mul]

/-- ★★ **One fault on the pair `q` in the bit round leaves an error on qubit `q` alone** — any
operator on the pair, by linearity from `atQubit_bitFault`. -/
theorem atQubit_bitFaultOp {q : Fin 7}
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : OnPair q F) (m : Fin 7 → Fin 2) : AtQubit q (bitFaultOp F m) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  rw [bitFaultOp, faultReadOp_sum, Matrix.mul_sum]
  exact AtQubit.sum _ fun k _ => atQubit_bitFault q (A k) (B k) m

/-- ★★ **And in the phase round.** -/
theorem atQubit_phaseFaultOp {q : Fin 7}
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : OnPair q F) (m : Fin 7 → Fin 2) : AtQubit q (phaseFaultOp F m) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  rw [phaseFaultOp, faultReadOp_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum]
  exact AtQubit.sum _ fun k _ => atQubit_phaseFault q (A k) (B k) m

/-! ### The faulty method is a channel -/

/-- Steane's ancilla is normalised. -/
theorem sum_plusAnc_sq : ∑ a, star (plusAnc a) * plusAnc a = 1 := by
  have h : ∀ a, star (plusAnc a) * plusAnc a = if syndrome a = 0 then (1 / 16 : ℂ) else 0 := by
    intro a
    by_cases h : syndrome a = 0
    · rw [plusAnc, ite_eq_left h, ite_eq_left h]; norm_num [Complex.ext_iff]
    · rw [plusAnc, ite_eq_right h, ite_eq_right h, star_zero, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, card_syndrome_fiber 0]
  norm_num

/-- ★ **The readout with a unitary fault is a complete measurement.** -/
theorem sum_faultReadOp_conjTranspose_mul
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : Fᴴ * F = 1) : ∑ m, (faultReadOp F m)ᴴ * faultReadOp F m = 1 := by
  set V : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := ancPrep plusAnc
  have hT : tCNOTᴴ * tCNOT = 1 := by
    rw [extractMat_conjTranspose id_add_self, extractMat_mul_self id_add_self]
  have hW : ∀ m, faultReadOp F m
      = (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
        * (F * tCNOT * V) := by
    intro m
    simp only [faultReadOp, V, Matrix.mul_assoc]
  simp only [hW, conjTranspose_mul (ancRead _)]
  have h2 : ∀ m : Fin 7 → Fin 2, (F * tCNOT * V)ᴴ
      * (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)ᴴ
      * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * (F * tCNOT * V))
      = (F * tCNOT * V)ᴴ
        * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)ᴴ * ancRead m)
        * (F * tCNOT * V) := by
    intro m
    simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun m _ => h2 m, ← Matrix.sum_mul, ← Matrix.mul_sum,
    sum_ancRead_conjTranspose_mul, Matrix.mul_one, conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Fᴴ F, hF, Matrix.one_mul, ← Matrix.mul_assoc tCNOTᴴ tCNOT, hT,
    Matrix.one_mul, ancPrep_conjTranspose_mul, sum_plusAnc_sq, one_smul]

theorem sum_bitFaultOp_conjTranspose_mul
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : Fᴴ * F = 1) : ∑ m, (bitFaultOp F m)ᴴ * bitFaultOp F m = 1 := by
  rw [← sum_faultReadOp_conjTranspose_mul hF]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bitFaultOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
    pauliMat_conjTranspose_mul_self, Matrix.one_mul]

theorem sum_phaseFaultOp_conjTranspose_mul
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : Fᴴ * F = 1) : ∑ m, (phaseFaultOp F m)ᴴ * phaseFaultOp F m = 1 := by
  have hterm : ∀ m, (phaseFaultOp F m)ᴴ * phaseFaultOp F m
      = hadTransversal 7 * ((faultReadOp F m)ᴴ * faultReadOp F m) * hadTransversal 7 := by
    intro m
    rw [phaseFaultOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
      pauliMat_conjTranspose_mul_self, Matrix.one_mul, conjTranspose_mul, conjTranspose_mul,
      hadTransversal_conjTranspose]
    calc hadTransversal 7 * ((faultReadOp F m)ᴴ * hadTransversal 7)
          * (hadTransversal 7 * faultReadOp F m * hadTransversal 7)
        = hadTransversal 7 * (faultReadOp F m)ᴴ * (hadTransversal 7 * hadTransversal 7)
          * faultReadOp F m * hadTransversal 7 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hadTransversal_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun m _ => hterm m, ← Matrix.sum_mul, ← Matrix.mul_sum,
    sum_faultReadOp_conjTranspose_mul hF, Matrix.mul_one, hadTransversal_mul_self]

/-- Which round of Steane's method holds the fault. -/
inductive MethodRound
  /-- The fault is at an extraction location of the bit round. -/
  | bit
  /-- The fault is at an extraction location of the phase round. -/
  | phase
  deriving DecidableEq

/-- **A branch of Steane's method with the operator `F` at an extraction location of round `r`**, the
other round fault-free. -/
def faultyKraus
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) :
    MethodRound → OutPair → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ
  | .bit, mm => phaseRound mm.2 * bitFaultOp F mm.1
  | .phase, mm => phaseFaultOp F mm.2 * bitRound mm.1

theorem faultyKraus_tp
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : Fᴴ * F = 1) (r : MethodRound) :
    ∑ mm : OutPair, (faultyKraus F r mm)ᴴ * faultyKraus F r mm = 1 := by
  have h1 : (1 : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)ᴴ
      * 1 = 1 := by rw [conjTranspose_one, Matrix.one_mul]
  cases r with
  | bit =>
    have hY := sum_phaseFaultOp_conjTranspose_mul h1
    simp only [phaseFaultOp_one] at hY
    exact sum_mul_conjTranspose_mul_of_tp (sum_bitFaultOp_conjTranspose_mul hF) hY
  | phase =>
    have hX := sum_bitFaultOp_conjTranspose_mul h1
    simp only [bitFaultOp_one] at hX
    exact sum_mul_conjTranspose_mul_of_tp hX (sum_phaseFaultOp_conjTranspose_mul hF)

/-- ★★ **Steane's method with one unitary fault, as a channel.** -/
def faultyMethod
    (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (hF : Fᴴ * F = 1) (r : MethodRound) : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) OutPair where
  kraus := faultyKraus F r
  tp := faultyKraus_tp hF r

/-- ★★ **Every branch of the faulty method acts on the code as an operator on qubit `q`.** -/
theorem atQubit_faultyKraus {q : Fin 7}
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hF : OnPair q F) : ∀ (r : MethodRound) (mm : OutPair), AtQubit q (faultyKraus F r mm)
  | .bit, mm => (atQubit_bitFaultOp hF mm.1).phaseRound_mul mm.2
  | .phase, mm => by
    obtain ⟨M, hM⟩ := atQubit_phaseFaultOp hF mm.2
    show AtQubit q (phaseFaultOp F mm.2 * bitRound mm.1)
    by_cases h : syndrome mm.1 = 0
    · refine ⟨(1 / 4 : ℂ) • M, ?_⟩
      rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_left h, Matrix.mul_smul, hM,
        gateOf_smul, Matrix.smul_mul]
    · refine ⟨0, ?_⟩
      rw [Matrix.mul_assoc, bitRound_mul_steaneProj, ite_eq_right h, Matrix.mul_zero, gateOf_zero,
        Matrix.zero_mul]

/-! ### The faulty method is a correctable deviation -/

/-- ★★★ **A channel whose every Kraus operator acts on the code as an operator on one qubit is a CSS
deviation of the identity** — #96's `DeviatesBy`. Trace preservation of the channel gives trace
preservation on the code. -/
theorem deviatesBy_cssMix_of_atQubit {ι : Type} [Fintype ι]
    (Φ : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) ι) {q : Fin 7} (h : ∀ b, AtQubit q (Φ.kraus b)) :
    DeviatesBy steaneProj cssMix id Φ.apply := by
  have hP := isCodeProjector_steaneProj
  choose M hM using h
  have hM' : ∀ b, steaneProj * (Φ.kraus b)ᴴ = steaneProj * (gateOf q (M b))ᴴ := by
    intro b
    have h2 := congrArg conjTranspose (hM b)
    rwa [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq] at h2
  intro ρ hρ
  refine ⟨fun σ => ∑ b, gateOf q (M b) * σ * (gateOf q (M b))ᴴ,
    ⟨ι, inferInstance, fun b => gateOf q (M b), fun b => gateOf_mem_cssSpan q (M b), ?_, rfl⟩, ?_⟩
  · have hterm : ∀ b, steaneProj * ((gateOf q (M b))ᴴ * gateOf q (M b)) * steaneProj
        = steaneProj * ((Φ.kraus b)ᴴ * Φ.kraus b) * steaneProj := by
      intro b
      calc steaneProj * ((gateOf q (M b))ᴴ * gateOf q (M b)) * steaneProj
          = (steaneProj * (gateOf q (M b))ᴴ) * (gateOf q (M b) * steaneProj) := by
            simp only [Matrix.mul_assoc]
        _ = (steaneProj * (Φ.kraus b)ᴴ) * (Φ.kraus b * steaneProj) := by rw [hM b, hM' b]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_congr rfl fun b _ => hterm b, ← Matrix.sum_mul,
      ← Matrix.mul_sum, Φ.tp, Matrix.mul_one, hP.mul_self]
  · show Φ.apply ρ = ∑ b, gateOf q (M b) * ρ * (gateOf q (M b))ᴴ
    rw [Channel.apply_def]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hρ' : ρ = steaneProj * ρ * steaneProj := hρ
    calc Φ.kraus b * ρ * (Φ.kraus b)ᴴ
        = (Φ.kraus b * steaneProj) * ρ * (steaneProj * (Φ.kraus b)ᴴ) := by
          conv_lhs => rw [hρ']
          simp only [Matrix.mul_assoc]
      _ = (gateOf q (M b) * steaneProj) * ρ * (steaneProj * (gateOf q (M b))ᴴ) := by
          rw [hM b, hM' b]
      _ = gateOf q (M b) * ρ * (gateOf q (M b))ᴴ := by
          conv_rhs => rw [hρ']
          simp only [Matrix.mul_assoc]

/-- ★★★ **Steane's method with one fault is a correctable deviation**: a unitary fault on data qubit
`q` and ancilla qubit `q` after the transversal `CNOT` of either round, the rest fault-free, leaves a
code state a CSS mixture of itself — #96's `DeviatesBy`, discharged for the recovery piece. -/
theorem deviatesBy_faultyMethod {q : Fin 7}
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hFu : Fᴴ * F = 1) (hF : OnPair q F) (r : MethodRound) :
    DeviatesBy steaneProj cssMix id (faultyMethod F hFu r).apply :=
  deviatesBy_cssMix_of_atQubit _ (atQubit_faultyKraus hF r)

/-- ★★★ **One fault in a recovery is removed by the next**: Steane's method with one extraction
fault, then Steane's method fault-free, returns every code state. -/
theorem methodRecovery_faultyMethod {q : Fin 7}
    {F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ}
    (hFu : Fᴴ * F = 1) (hF : OnPair q F) (r : MethodRound)
    {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hρ : IsCodeState steaneProj ρ) :
    methodRecovery.apply ((faultyMethod F hFu r).apply ρ) = ρ := by
  obtain ⟨E, hE, h⟩ := deviatesBy_faultyMethod hFu hF r ρ hρ
  rw [h, id, isRecovery_methodRecovery_cssMix E hE ρ hρ]

/-! ### The extended rectangle with a faulty recovery that is a circuit -/

/-- ★★★ **#96's extended rectangle at the Steane code, every piece a circuit.** With Steane's method
(`methodRecovery`) as both recoveries and the CSS class as the correctable set:

* **a fault in the leading recovery** — any unitary on data qubit `q` and ancilla qubit `q` after a
  transversal `CNOT` of either round — then the ideal gadget, then the method, is a corrected step;
  the faulty recovery enters as a theorem (`deviatesBy_faultyMethod`), not a hypothesis;
* **a faulty gadget** with a good pattern between two fault-free runs of the method is a corrected
  step;
* **a fault in the trailing recovery** hands on a CSS deviation of the ideal output, in the form the
  next rectangle's recovery consumes (`isRecovery_methodRecovery_cssMix`). -/
theorem steane_exRec_faultyMethod :
    (∀ (G : Gadget) (q : Fin 7)
        (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
        (hFu : Fᴴ * F = 1), OnPair q F → ∀ r : MethodRound,
          IsCorrectedStep steaneProj G.ideal
            (exRec (faultyMethod F hFu r).apply G.ideal methodRecovery.apply))
    ∧ (∀ (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ q, U q ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ b : ConcatPat 7 1, isBad 7 1 b = false →
          IsCorrectedStep steaneProj G.ideal
            (exRec methodRecovery.apply (G.faulty U (locPat b)) methodRecovery.apply))
    ∧ (∀ (G : Gadget) (q : Fin 7)
        (F : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
        (hFu : Fᴴ * F = 1), OnPair q F → ∀ r : MethodRound,
          DeviatesBy steaneProj cssMix G.ideal
            (exRec methodRecovery.apply G.ideal (faultyMethod F hFu r).apply)) := by
  have hrec := isRecovery_methodRecovery_cssMix
  refine ⟨fun G q F hFu hF r => ?_, fun G U hU b hb => ?_, fun G q F hFu hF r => ?_⟩
  · exact isCorrectedStep_exRec_leading (deviatesBy_faultyMethod hFu hF r) G.propagatesD_cssMix
      hrec fun _ hρ => G.isCodeState_ideal hρ
  · exact isCorrectedStep_exRec_gadget id_mem_cssMix hrec
      ((G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hb)).mono weightOne_subset_cssMix)
      hrec fun _ hρ => G.isCodeState_ideal hρ
  · exact deviatesBy_exRec_trailing id_mem_cssMix hrec (deviatesBy_faultyMethod hFu hF r)
      fun _ hρ => G.isCodeState_ideal hρ

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
