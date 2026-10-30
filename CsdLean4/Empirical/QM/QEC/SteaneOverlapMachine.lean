/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneVerifiedAncilla
public import CsdLean4.Mathlib.QuantumInfo.OverlappingRectangles

/-!
# The Steane machine with the recovery's locations counted

**Category:** 3-Local (Empirical, QM twin). BACKLOG #233 (split from ~~#229~~); fault model
completed by #235; the ancilla factories' locations counted by #238.

`SteaneMachine.lean` (~~#207~~) proved the level-one threshold statement with faults at the gadgets
and an ideal recovery. `SteaneFaultyRecovery.lean` (~~#232~~) made one faulty recovery a theorem
inside one extended rectangle. This module runs the whole machine with **every recovery a circuit with
its own fault locations**: gadget, Steane's method, gadget, Steane's method, …, one fault pattern over
all of them, and the extended rectangles overlapping as in Aliferis–Gottesman–Preskill.

## Steane's method under any fault pattern

* `card_methodRound`; `UnderIdx`, `underKraus`, `underKraus_tp`, ★★ `methodUnder` — **Steane's method
  with a channel at every faulty extraction location of a pattern** (BACKLOG ~~#235~~), the ancillas
  ideal; ★ `methodUnder_none`, ★★ `atQubit_underKraus_single`, ★★★ `deviatesBy_methodUnder_single`.
  The pattern helpers (`locFam`, `roundKraus`, `sum_prod_ofFn_conjTranspose_mul`) are in
  `SteaneFaultModel.lean`.

## Steane's method with its factories under a fault pattern (BACKLOG ~~#238~~)

* `RecLoc` — **the recovery's locations**: in each round the seven extraction locations and the
  forty-six locations of the round's ancilla factory (`FacLoc`, `SteaneVerifiedAncilla.lean`), `106`
  in all; `RoundIdx`;
* `extractOp`, `extractOp_smul`, `extractOp_one`, `extractOp_zero`,
  `sum_extractOp_conjTranspose_mul_eq`, ★ `sum_extractOp_family` — the extraction with an ancilla
  family and a fault family is a complete measurement; `roundOp`, `sum_roundOp_tp`;
* `recKraus'`, `recKraus'_tp`, ★★ `recUnder` — **Steane's method with both factories and both
  extractions under a pattern**, a channel for every pattern;
* `sum_mul_conj_of_prod`, `sum_smul_conj`, `eq_one_of_smul_one_eq_one`, `roundOp_none`,
  ★★ `recUnder_none` — **with no fault in the recovery it is `methodRecovery`**;
* ★★★ `exists_atQubit_recKraus'_single`, ★★★ `deviatesBy_recUnder_single` — **with one fault
  anywhere in the recovery — an extraction location, either encoder, a verification pair, a checker
  readout — it is a CSS deviation of the identity** (`goodAnc_facOut_single`, `exists_atQubit_ancKraus`,
  `atQubit_underKraus_single`).

## The machine

* `StepLoc`, `OvLoc N` — **one location space**: step `j` has its gadget's seven locations and its
  recovery's `106`, `113 N` in all; `gatePat`, `recPat` — a pattern read on one piece;
* `window k` — **the `k`-th extended rectangle's locations**: step `k`'s `113` and the recovery of
  step `k − 1` (for `k ≥ 1`), ★ `card_window_le` — at most `219`; `WindowsGood ω` — every window
  holds at most one fault;
* `ovGadget`, `ovFaultyGadget`, `ovRecovery`, `overlapRun` — the machine under a pattern;
  `recoveryFlag`, `gadgetFlag` — which pieces are faulty; ★ `ovIdeal_ovGadget` — its ideal run is
  #207's `machineIdeal`;
* ★★★ `isFaultChain_overlap` — **the machine is an `IsFaultChain` for the CSS class**: a faulty
  recovery deviates by `cssMix` (`deviatesBy_recUnder_single`), a fault-free one corrects it
  (`recUnder_none`, `isRecovery_methodRecovery_cssMix`), a gadget with one fault deviates by it, the
  ideal gadgets carry it; ★★ `exRecGood_of_windowsGood`;
* ★★★ `steane_machine_overlap` — **the level-one machine with nothing ideal in the recovery but its
  classical decoding**: for every circuit of `N` gadgets, unitary faults at every gadget location,
  channel faults on the pairs at every extraction location, faults at every location of every ancilla
  factory, and an encoded input, a pattern with at most one fault in each overlapping extended
  rectangle leaves the state a CSS deviation of the ideal one, exactly the ideal one if the last
  recovery is fault-free, and the ideal one after a final ideal decoding; under independent faults of
  rate at most `p` at the `113 N` locations, the decoded output is ideal with probability at least
  `1 − 23871 N p²` (`23871 = C(219, 2)`).

## Honest scope

⚠️ **The encoded input and the final decoding are ideal** (#236), and so is the classical decoding
inside each recovery. Every quantum location of the recovery is counted (BACKLOG ~~#238~~).

⚠️ **A rejected ancilla is replaced fault-free.** On a failing checker word the factory prepares a
fresh `|+̄⟩` without locations of its own; counting the retry's locations is #240.

⚠️ **A fault at an extraction location stays on its pair** (BACKLOG ~~#235~~); a fault in an encoder
or at a checker readout is any channel on the seven qubits; faults at the gadgets are still unitary
on one qubit (#207's model, #237).

⚠️ **One round per basis**, as in ~~#228~~; no repeated syndrome measurement.

⚠️ **One block, three gates**, as in ~~#207~~: `H̄`, `X̄`, `Z̄`. The two-block `CNOT̄` is #226.

⚠️ **Level one.** The concatenated machine with counted recoveries is #231.

⚠️ **The constant is `C(219, 2) = 23871`** from the union bound over each window's pairs; most pairs
are benign, and counting only the malignant ones is #239.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97; A. Steane,
PRL 78 (1997) 2252; `specs/BACKLOG.md` #233, #235, #238, #232, #229, #207, #96, #97, #234, #236,
#239, #240; `Empirical/QM/QEC/SteaneVerifiedAncilla.lean`,
`Mathlib/QuantumInfo/OverlappingRectangles.lean`, `Mathlib/QuantumInfo/ExtendedRectangle.lean`,
`Empirical/QM/QEC/SteaneFaultModel.lean`, `Empirical/QM/QEC/SteaneFaultyRecovery.lean`,
`Empirical/QM/QEC/SteaneMethod.lean`, `Empirical/QM/QEC/SteaneMachine.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
`specs/future-work.md`.
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

/-! ### Steane's method under any fault pattern -/

instance : Fintype MethodRound :=
  ⟨{.bit, .phase}, fun r => by cases r <;> simp⟩

theorem card_methodRound : Fintype.card MethodRound = 2 := rfl

variable {κ : Type}

/-- The branches of Steane's method under a pattern: each round's fault branch and read word. -/
abbrev UnderIdx (κ : Type) : Type :=
  ((Fin 7 → Option κ) × (Fin 7 → Fin 2)) × ((Fin 7 → Option κ) × (Fin 7 → Fin 2))

/-- A branch of Steane's method with the fault channels `F r q` at the faulty extraction locations of
`b`. -/
def underKraus (F : MethodRound → Fin 7 → κ → PairOp) (b : MethodRound × Fin 7 → Bool)
    (p : UnderIdx κ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  phaseFaultOp (roundKraus (F .phase) (fun q => b (.phase, q)) p.2.1) p.2.2
    * bitFaultOp (roundKraus (F .bit) (fun q => b (.bit, q)) p.1.1) p.1.2

theorem underKraus_tp [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp}
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (b : MethodRound × Fin 7 → Bool) :
    ∑ p, (underKraus F b p)ᴴ * underKraus F b p = 1 := by
  have h := sum_mul_conjTranspose_mul_of_tp
    (sum_bitFaultOp_family (roundKraus_tp (hF .bit) fun q => b (.bit, q)))
    (sum_phaseFaultOp_family (roundKraus_tp (hF .phase) fun q => b (.phase, q)))
  simpa only [underKraus] using h

/-- ★★ **Steane's method under a fault pattern**: at every extraction location `(r, q)` the pattern
marks faulty, the channel `F r q` — any trace-preserving Kraus family on data qubit `q` and ancilla
qubit `q` after the transversal `CNOT` of round `r`, which by `readAround_eq` and `aroundFam` covers a
fault before the `CNOT` too. A channel for every pattern. -/
def methodUnder [Fintype κ] (F : MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (b : MethodRound × Fin 7 → Bool) :
    Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (UnderIdx κ) where
  kraus := underKraus F b
  tp := underKraus_tp hF b

/-- ★ **With no fault, Steane's method under the pattern is `methodRecovery`.** -/
theorem methodUnder_none [Fintype κ] (F : MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) :
    (methodUnder F hF fun _ => false).apply = methodRecovery.apply := by
  set z : Fin 7 → Option κ := fun _ => none
  have hz : ∀ mm : OutPair, underKraus F (fun _ => false) ((z, mm.1), (z, mm.2)) = methodKraus mm := by
    intro mm
    rw [underKraus, roundKraus_none, roundKraus_none, phaseFaultOp_one, bitFaultOp_one, methodKraus]
  have hne : ∀ p : UnderIdx κ, ¬(p.1.1 = z ∧ p.2.1 = z) → underKraus F (fun _ => false) p = 0 := by
    rintro ⟨⟨s₁, m₁⟩, ⟨s₂, m₂⟩⟩ h
    rw [underKraus]
    by_cases h₁ : s₁ = z
    · rw [roundKraus_none_of_ne _ fun h₂ => h ⟨h₁, h₂⟩, phaseFaultOp_zero, Matrix.zero_mul]
    · rw [roundKraus_none_of_ne _ h₁, bitFaultOp_zero, Matrix.mul_zero]
  funext ρ
  rw [Channel.apply_def, Channel.apply_def]
  refine (Fintype.sum_of_injective (fun mm : OutPair => ((z, mm.1), (z, mm.2)))
    (fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1.2 h.2.2) _ _ ?_ ?_).symm
  · rintro ⟨⟨s₁, m₁⟩, ⟨s₂, m₂⟩⟩ hp
    have h : ¬(s₁ = z ∧ s₂ = z) := by
      rintro ⟨rfl, rfl⟩
      exact hp ⟨(m₁, m₂), rfl⟩
    show underKraus F (fun _ => false) _ * ρ * (underKraus F (fun _ => false) _)ᴴ = 0
    rw [hne _ h, Matrix.zero_mul, Matrix.zero_mul]
  · intro mm
    show methodKraus mm * ρ * (methodKraus mm)ᴴ
      = underKraus F (fun _ => false) _ * ρ * (underKraus F (fun _ => false) _)ᴴ
    rw [hz]

/-- ★★ **With one fault, at `(r, q)`, every branch acts on the code as an operator on qubit `q`.** -/
theorem atQubit_underKraus_single {F : MethodRound → Fin 7 → κ → PairOp}
    (hOn : ∀ r q k, OnPair q (F r q k)) (r : MethodRound) (q : Fin 7) (p : UnderIdx κ) :
    AtQubit q (underKraus F (fun l => decide (l = (r, q))) p) := by
  obtain ⟨⟨s₁, m₁⟩, ⟨s₂, m₂⟩⟩ := p
  cases r with
  | bit =>
    have h1 : (fun q' => decide (((MethodRound.phase, q') : MethodRound × Fin 7) = (.bit, q)))
        = fun _ => false := funext fun q' => by simp
    have h2 : (fun q' => decide (((MethodRound.bit, q') : MethodRound × Fin 7) = (.bit, q)))
        = fun q' => decide (q' = q) := funext fun q' => by simp
    have hG := onPair_roundKraus_single (hOn .bit q) s₁
    rw [underKraus, h1, h2]
    by_cases h : s₂ = fun _ => none
    · rw [h, roundKraus_none, phaseFaultOp_one]
      exact (atQubit_bitFaultOp hG m₁).phaseRound_mul m₂
    · rw [roundKraus_none_of_ne _ h, phaseFaultOp_zero, Matrix.zero_mul]
      exact AtQubit.zero
  | phase =>
    have h1 : (fun q' => decide (((MethodRound.bit, q') : MethodRound × Fin 7) = (.phase, q)))
        = fun _ => false := funext fun q' => by simp
    have h2 : (fun q' => decide (((MethodRound.phase, q') : MethodRound × Fin 7) = (.phase, q)))
        = fun q' => decide (q' = q) := funext fun q' => by simp
    have hG := onPair_roundKraus_single (hOn .phase q) s₂
    rw [underKraus, h1, h2]
    by_cases h : s₁ = fun _ => none
    · rw [h, roundKraus_none, bitFaultOp_one]
      have h' := atQubit_faultyKraus hG .phase (m₁, m₂)
      simp only [faultyKraus] at h'
      exact h'
    · rw [roundKraus_none_of_ne _ h, bitFaultOp_zero, Matrix.mul_zero]
      exact AtQubit.zero

/-- ★★★ **Steane's method with one faulty location, whatever its channel on the pair, is a CSS
deviation of the identity.** -/
theorem deviatesBy_methodUnder_single [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp}
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (hOn : ∀ r q k, OnPair q (F r q k))
    (r : MethodRound) (q : Fin 7) :
    DeviatesBy steaneProj cssMix id (methodUnder F hF fun l => decide (l = (r, q))).apply :=
  deviatesBy_cssMix_of_atQubit _ (atQubit_underKraus_single hOn r q)

/-! ### Steane's method with its factories under a fault pattern -/

/-- **The recovery's locations**: in each round, an extraction location or a location of the round's
ancilla factory — `2 × (7 + 46) = 106`. -/
abbrev RecLoc : Type := MethodRound × (Fin 7 ⊕ FacLoc)

instance instDecidableEqFacLoc : DecidableEq FacLoc :=
  inferInstanceAs (DecidableEq ((Fin 7 ⊕ Fin 9) ⊕ (Fin 7 ⊕ Fin 9) ⊕ Fin 7 ⊕ Fin 7))

instance instFintypeFacLoc : Fintype FacLoc :=
  inferInstanceAs (Fintype ((Fin 7 ⊕ Fin 9) ⊕ (Fin 7 ⊕ Fin 9) ⊕ Fin 7 ⊕ Fin 7))

instance instDecidableEqRecLoc : DecidableEq RecLoc :=
  inferInstanceAs (DecidableEq (MethodRound × (Fin 7 ⊕ FacLoc)))

instance instFintypeRecLoc : Fintype RecLoc :=
  inferInstanceAs (Fintype (MethodRound × (Fin 7 ⊕ FacLoc)))

/-- A round's branches: the extraction faults' and the factory's, then the read word. -/
abbrev RoundIdx (κ : Type) : Type := ((Fin 7 → Option κ) × FacIdx (FacBranch κ)) × (Fin 7 → Fin 2)

instance instFintypeRoundIdx {κ : Type} [Fintype κ] : Fintype (RoundIdx κ) := by
  unfold RoundIdx FacIdx FacBranch
  infer_instance

/-- **Steane's extraction with the ancilla `f` and the fault `G` after the `CNOT`**, read as `m`. -/
def extractOp (f : (Fin 7 → Fin 2) → ℂ) (G : PairOp) (m : Fin 7 → Fin 2) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * G * tCNOT
    * (ancPrep f : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

theorem extractOp_smul (c : ℂ) (f : (Fin 7 → Fin 2) → ℂ) (G : PairOp) (m : Fin 7 → Fin 2) :
    extractOp (c • f) G m = c • extractOp f G m := by
  rw [extractOp, extractOp, ancPrep_smul, Matrix.mul_smul]

theorem extractOp_plusAnc (G : PairOp) (m : Fin 7 → Fin 2) :
    extractOp plusAnc G m = faultReadOp G m := rfl

theorem extractOp_one (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    extractOp f 1 m = ancReadOp f m := by
  rw [extractOp, ancReadOp, Matrix.mul_one]

theorem extractOp_zero (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) : extractOp f 0 m = 0 := by
  rw [extractOp, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem sum_extractOp_conjTranspose_mul_eq (f : (Fin 7 → Fin 2) → ℂ) (G : PairOp) :
    ∑ m, (extractOp f G m)ᴴ * extractOp f G m
      = (G * tCNOT * (ancPrep f : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ))ᴴ
        * (G * tCNOT * (ancPrep f : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)) := by
  set W : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := G * tCNOT * ancPrep f
  have hW : ∀ m, extractOp f G m
      = (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W := by
    intro m
    simp only [extractOp, W, Matrix.mul_assoc]
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
    sum_ancRead_conjTranspose_mul, Matrix.mul_one]

/-- **The extraction under a trace-preserving family of faults and a family of ancillas is a complete
measurement.** -/
theorem sum_extractOp_family {ι σ : Type*} [Fintype ι] [Fintype σ] {out : ι → (Fin 7 → Fin 2) → ℂ}
    {G : σ → PairOp} (hn : ∑ i, ∑ a, star (out i a) * out i a = 1) (hG : ∑ s, (G s)ᴴ * G s = 1) :
    ∑ p : (σ × ι) × (Fin 7 → Fin 2), (extractOp (out p.1.2) (G p.1.1) p.2)ᴴ
      * extractOp (out p.1.2) (G p.1.1) p.2 = 1 := by
  have hT : tCNOTᴴ * tCNOT = 1 := tCNOT_conjTranspose_mul
  rw [Fintype.sum_prod_type]
  simp only [sum_extractOp_conjTranspose_mul_eq]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hterm : ∀ i, ∑ s, (G s * tCNOT * (ancPrep (out i) : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2))
        (Fin 7 → Fin 2) ℂ))ᴴ * (G s * tCNOT * (ancPrep (out i) : Matrix ((Fin 7 → Fin 2) ×
        (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ))
      = (∑ a, star (out i a) * out i a) • (1 : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) := by
    intro i
    set V : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := ancPrep (out i)
    have h1 : ∀ s, (G s * tCNOT * V)ᴴ * (G s * tCNOT * V) = Vᴴ * (tCNOTᴴ * ((G s)ᴴ * G s) * tCNOT) * V := by
      intro s
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun s _ => h1 s, ← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.sum_mul,
      ← Matrix.mul_sum, hG, Matrix.mul_one, hT, Matrix.mul_one, ancPrep_conjTranspose_mul]
  simp only [hterm]
  rw [← Finset.sum_smul, hn, one_smul]


/-- **One round of Steane's method under the pattern `b`**: the ancilla from its factory, the
extraction with its faults, read in branch `i`. -/
def roundOp (F : Fin 7 → κ → PairOp) (Φ : FacFaults κ) (b : Fin 7 ⊕ FacLoc → Bool) (i : RoundIdx κ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  extractOp (facOut Φ (fun ℓ => b (.inr ℓ)) i.1.2) (roundKraus F (fun q => b (.inl q)) i.1.1) i.2

theorem sum_roundOp_tp [Fintype κ] {F : Fin 7 → κ → PairOp} {Φ : FacFaults κ}
    (hF : ∀ q, ∑ k, (F q k)ᴴ * F q k = 1) (hΦ : Φ.Valid) (b : Fin 7 ⊕ FacLoc → Bool) :
    ∑ i, (roundOp F Φ b i)ᴴ * roundOp F Φ b i = 1 := by
  have h := sum_extractOp_family (facOut_norm hΦ fun ℓ => b (.inr ℓ))
    (roundKraus_tp hF fun q => b (.inl q))
  simp only [roundOp]
  exact h

/-- **A branch of Steane's method under the pattern `b`**, factories and extractions included. -/
def recKraus' (F : MethodRound → Fin 7 → κ → PairOp) (Φ : MethodRound → FacFaults κ)
    (b : RecLoc → Bool) (i : RoundIdx κ × RoundIdx κ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (pauliMat 0 (decode (syndrome i.2.2))
      * (hadTransversal 7 * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i.2 * hadTransversal 7))
    * (pauliMat (decode (syndrome i.1.2)) 0 * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i.1)

theorem recKraus'_tp [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp} {Φ : MethodRound → FacFaults κ}
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (hΦ : ∀ r, (Φ r).Valid) (b : RecLoc → Bool) :
    ∑ i, (recKraus' F Φ b i)ᴴ * recKraus' F Φ b i = 1 := by
  have hX : ∑ i : RoundIdx κ, (pauliMat (decode (syndrome i.2)) 0
      * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i)ᴴ
      * (pauliMat (decode (syndrome i.2)) 0 * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i) = 1 := by
    have h : ∀ i : RoundIdx κ, (pauliMat (decode (syndrome i.2)) 0
        * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i)ᴴ
        * (pauliMat (decode (syndrome i.2)) 0 * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i)
        = (roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i)ᴴ
          * roundOp (F .bit) (Φ .bit) (fun l => b (.bit, l)) i := by
      intro i
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
        pauliMat_conjTranspose_mul_self, Matrix.one_mul]
    simp only [h]
    exact sum_roundOp_tp (hF .bit) (hΦ .bit) _
  have hY : ∑ i : RoundIdx κ, (pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
      * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i * hadTransversal 7))ᴴ
      * (pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
        * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i * hadTransversal 7)) = 1 := by
    have h : ∀ i : RoundIdx κ, (pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
        * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i * hadTransversal 7))ᴴ
        * (pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
          * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i * hadTransversal 7))
        = hadTransversal 7 * ((roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i)ᴴ
          * roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i) * hadTransversal 7 := by
      intro i
      set X := roundOp (F .phase) (Φ .phase) (fun l => b (.phase, l)) i
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
        pauliMat_conjTranspose_mul_self, Matrix.one_mul, conjTranspose_mul, conjTranspose_mul,
        hadTransversal_conjTranspose]
      calc hadTransversal 7 * (Xᴴ * hadTransversal 7) * (hadTransversal 7 * X * hadTransversal 7)
          = hadTransversal 7 * Xᴴ * (hadTransversal 7 * hadTransversal 7) * X * hadTransversal 7 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hadTransversal_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [h]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_roundOp_tp (hF .phase) (hΦ .phase) _, Matrix.mul_one,
      hadTransversal_mul_self]
  have h := sum_mul_conjTranspose_mul_of_tp hX hY
  simp only [recKraus']
  exact h

/-- ★★ **Steane's method with its factories, under a fault pattern**: a channel for every pattern of
faults at the extraction locations and the factory locations of both rounds. -/
def recUnder [Fintype κ] (F : MethodRound → Fin 7 → κ → PairOp) (Φ : MethodRound → FacFaults κ)
    (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1) (hΦ : ∀ r, (Φ r).Valid) (b : RecLoc → Bool) :
    Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (RoundIdx κ × RoundIdx κ) where
  kraus := recKraus' F Φ b
  tp := recKraus'_tp hF hΦ b


/-- Two maps in sequence: the sum over pairs of branches is the second applied to the first's sum. -/
theorem sum_mul_conj_of_prod {n ι σ : Type*} [Fintype n] [Fintype ι] [Fintype σ]
    (X : ι → Matrix n n ℂ) (Y : σ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    ∑ p : ι × σ, (Y p.2 * X p.1) * ρ * (Y p.2 * X p.1)ᴴ
      = ∑ k, Y k * (∑ i, X i * ρ * (X i)ᴴ) * (Y k)ᴴ := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Branches that are scalar multiples, with weights summing to one, act as the unweighted family. -/
theorem sum_smul_conj {n ι σ : Type*} [Fintype n] [Fintype ι] [Fintype σ] {a : ι → ℂ}
    (ha : ∑ i, star (a i) * a i = 1) (X : σ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    ∑ p : ι × σ, (a p.1 • X p.2) * ρ * (a p.1 • X p.2)ᴴ = ∑ m, X m * ρ * (X m)ᴴ := by
  rw [Fintype.sum_prod_type]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum]
  rw [← Finset.sum_smul]
  simp only [ha, one_smul]

theorem eq_one_of_smul_one_eq_one {n : Type*} [DecidableEq n] [Nonempty n] {c : ℂ}
    (h : c • (1 : Matrix n n ℂ) = 1) : c = 1 := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have := congrFun (congrFun h i) i
  simpa using this

/-- **A fault-free round reads with a scalar multiple of `|+̄⟩`, independently of the word.** -/
theorem roundOp_none {F : Fin 7 → κ → PairOp} (Φ : FacFaults κ)
    (rest : (Fin 7 → Option κ) × FacIdx (FacBranch κ)) :
    ∃ c : ℂ, ∀ m, roundOp F Φ (fun _ => false) (rest, m) = c • steaneRead m := by
  obtain ⟨c, hc⟩ := facOut_none Φ rest.2
  rcases roundKraus_false_cases F rest.1 with h | h
  · refine ⟨c, fun m => ?_⟩
    simp only [roundOp]
    rw [hc, h, extractOp_smul, extractOp_one]
    rfl
  · refine ⟨0, fun m => ?_⟩
    simp only [roundOp]
    rw [h, extractOp_zero, zero_smul]

theorem sum_steaneRead_conjTranspose_mul : ∑ m, (steaneRead m)ᴴ * steaneRead m = 1 := by
  have h1 : (1 : PairOp)ᴴ * 1 = 1 := by rw [conjTranspose_one, Matrix.one_mul]
  have h := sum_faultReadOp_conjTranspose_mul h1
  simpa only [faultReadOp_one] using h

/-- ★★ **With no fault in the recovery, Steane's method with its factories is `methodRecovery`.** -/
theorem recUnder_none [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp}
    {Φ : MethodRound → FacFaults κ} (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1)
    (hΦ : ∀ r, (Φ r).Valid) : (recUnder F Φ hF hΦ fun _ => false).apply = methodRecovery.apply := by
  choose a ha using fun r (rest : (Fin 7 → Option κ) × FacIdx (FacBranch κ)) =>
    roundOp_none (F := F r) (Φ r) rest
  have hw : ∀ r, ∑ rest, star (a r rest) * a r rest = 1 := by
    intro r
    have h := sum_roundOp_tp (hF r) (hΦ r) (fun _ => false)
    rw [Fintype.sum_prod_type] at h
    simp only [ha, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Finset.smul_sum, sum_steaneRead_conjTranspose_mul] at h
    rw [← Finset.sum_smul, show (∑ i, a r i * star (a r i)) = ∑ rest, star (a r rest) * a r rest
      from Finset.sum_congr rfl fun _ _ => mul_comm _ _] at h
    exact eq_one_of_smul_one_eq_one h
  have hbit : ∀ i : RoundIdx κ, pauliMat (decode (syndrome i.2)) 0
      * roundOp (F .bit) (Φ .bit) (fun _ => false) i = a .bit i.1 • bitRound i.2 := by
    rintro ⟨rest, m⟩
    rw [ha, Matrix.mul_smul]
    rfl
  have hphase : ∀ i : RoundIdx κ, pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
      * roundOp (F .phase) (Φ .phase) (fun _ => false) i * hadTransversal 7)
      = a .phase i.1 • phaseRound i.2 := by
    rintro ⟨rest, m⟩
    rw [ha, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
    rfl
  funext ρ
  rw [Channel.apply_def, Channel.apply_def]
  have hk : ∀ i, (recUnder F Φ hF hΦ fun _ => false).kraus i
      = (pauliMat 0 (decode (syndrome i.2.2)) * (hadTransversal 7
          * roundOp (F .phase) (Φ .phase) (fun _ => false) i.2 * hadTransversal 7))
        * (pauliMat (decode (syndrome i.1.2)) 0 * roundOp (F .bit) (Φ .bit) (fun _ => false) i.1) :=
    fun _ => rfl
  simp only [hk]
  have hs := sum_mul_conj_of_prod
    (fun i : RoundIdx κ => pauliMat (decode (syndrome i.2)) 0
      * roundOp (F .bit) (Φ .bit) (fun _ => false) i)
    (fun i : RoundIdx κ => pauliMat 0 (decode (syndrome i.2)) * (hadTransversal 7
      * roundOp (F .phase) (Φ .phase) (fun _ => false) i * hadTransversal 7)) ρ
  rw [hs]
  simp only [hbit, hphase]
  rw [sum_smul_conj (hw .bit), sum_smul_conj (hw .phase)]
  rw [show (∑ mm : OutPair, methodRecovery.kraus mm * ρ * (methodRecovery.kraus mm)ᴴ)
      = ∑ mm : OutPair, (phaseRound mm.2 * bitRound mm.1) * ρ * (phaseRound mm.2 * bitRound mm.1)ᴴ
      from rfl, sum_mul_conj_of_prod bitRound phaseRound ρ]


theorem ancReadOp_plusAnc (m : Fin 7 → Fin 2) : ancReadOp plusAnc m = steaneRead m := rfl

theorem ancReadOp_smul (c : ℂ) (f : (Fin 7 → Fin 2) → ℂ) (m : Fin 7 → Fin 2) :
    ancReadOp (c • f) m = c • ancReadOp f m := by
  rw [ancReadOp, ancReadOp, ancPrep_smul, Matrix.mul_smul]

/-- ★★★ **With one fault in the recovery — at an extraction location, or anywhere in either round's
ancilla factory — every branch acts on the code on one data qubit.** -/
theorem exists_atQubit_recKraus'_single [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp}
    {Φ : MethodRound → FacFaults κ} (hOn : ∀ r q k, OnPair q (F r q k)) (hΦ : ∀ r, (Φ r).Valid)
    (l : RecLoc) (i : RoundIdx κ × RoundIdx κ) :
    ∃ q, AtQubit q (recKraus' F Φ (fun l' => decide (l' = l)) i) := by
  obtain ⟨⟨⟨s₁, p₁⟩, m₁⟩, ⟨⟨s₂, p₂⟩, m₂⟩⟩ := i
  obtain ⟨r, q | ℓ⟩ := l
  · -- a fault at an extraction location
    obtain ⟨c₁, hc₁⟩ := facOut_none (Φ .bit) p₁
    obtain ⟨c₂, hc₂⟩ := facOut_none (Φ .phase) p₂
    have hb : (fun l' : MethodRound × Fin 7 => decide (((l'.1, .inl l'.2) : RecLoc) = (r, .inl q)))
        = fun l' => decide (l' = (r, q)) := funext fun l' => by
      obtain ⟨r', q'⟩ := l'
      simp
    have hK : recKraus' F Φ (fun l' => decide (l' = (r, .inl q))) (((s₁, p₁), m₁), ((s₂, p₂), m₂))
        = (c₁ * c₂) • underKraus F (fun l' => decide (l' = (r, q))) ((s₁, m₁), (s₂, m₂)) := by
      rw [← hb]
      simp only [recKraus', roundOp, underKraus, bitFaultOp, phaseFaultOp, Prod.mk.injEq,
        reduceCtorEq, and_false, decide_false, hc₁, hc₂, extractOp_smul, extractOp_plusAnc,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [hK]
    exact ⟨q, (atQubit_underKraus_single hOn r q _).smul _⟩
  · -- a fault in a factory
    cases r with
    | bit =>
      have hg := goodAnc_facOut_single (hΦ .bit) ℓ p₁
      obtain ⟨c₂, hc₂⟩ := facOut_none (Φ .phase) p₂
      rcases roundKraus_false_cases (F .bit) s₁ with h₁ | h₁ <;>
        rcases roundKraus_false_cases (F .phase) s₂ with h₂ | h₂
      · obtain ⟨q, hq⟩ := exists_atQubit_ancKraus
          (out := fun _ : Unit => facOut (Φ .bit) (fun ℓ' => decide (ℓ' = ℓ)) p₁)
          (fun _ => hg) .bit ((), (m₁, m₂))
        have hK : recKraus' F Φ (fun l' => decide (l' = (.bit, .inr ℓ))) (((s₁, p₁), m₁), ((s₂, p₂), m₂))
            = c₂ • ancKraus (fun _ : Unit => facOut (Φ .bit) (fun ℓ' => decide (ℓ' = ℓ)) p₁) .bit
                ((), (m₁, m₂)) := by
          simp only [recKraus', roundOp, ancKraus, ancBitOp, phaseRound, Prod.mk.injEq,
            reduceCtorEq, and_false, false_and, decide_false, true_and, Sum.inr.injEq, h₁, h₂, hc₂,
            extractOp_one, ancReadOp_smul, ancReadOp_plusAnc, Matrix.mul_smul, Matrix.smul_mul]
        rw [hK]
        exact ⟨q, hq.smul _⟩
      all_goals
        refine ⟨0, ?_⟩
        simp only [recKraus', roundOp, Prod.mk.injEq, reduceCtorEq, and_false, false_and,
          decide_false, h₁, h₂, extractOp_zero, Matrix.mul_zero, Matrix.zero_mul]
        exact AtQubit.zero
    | phase =>
      have hg := goodAnc_facOut_single (hΦ .phase) ℓ p₂
      obtain ⟨c₁, hc₁⟩ := facOut_none (Φ .bit) p₁
      rcases roundKraus_false_cases (F .bit) s₁ with h₁ | h₁ <;>
        rcases roundKraus_false_cases (F .phase) s₂ with h₂ | h₂
      · obtain ⟨q, hq⟩ := exists_atQubit_ancKraus
          (out := fun _ : Unit => facOut (Φ .phase) (fun ℓ' => decide (ℓ' = ℓ)) p₂)
          (fun _ => hg) .phase ((), (m₁, m₂))
        have hK : recKraus' F Φ (fun l' => decide (l' = (.phase, .inr ℓ))) (((s₁, p₁), m₁), ((s₂, p₂), m₂))
            = c₁ • ancKraus (fun _ : Unit => facOut (Φ .phase) (fun ℓ' => decide (ℓ' = ℓ)) p₂) .phase
                ((), (m₁, m₂)) := by
          simp only [recKraus', roundOp, ancKraus, ancPhaseOp, bitRound, Prod.mk.injEq,
            reduceCtorEq, and_false, false_and, decide_false, true_and, Sum.inr.injEq, h₁, h₂, hc₁,
            extractOp_one, ancReadOp_smul, ancReadOp_plusAnc, Matrix.mul_smul]
        rw [hK]
        exact ⟨q, hq.smul _⟩
      all_goals
        refine ⟨0, ?_⟩
        simp only [recKraus', roundOp, Prod.mk.injEq, reduceCtorEq, and_false, false_and,
          decide_false, h₁, h₂, extractOp_zero, Matrix.mul_zero, Matrix.zero_mul]
        exact AtQubit.zero

/-- ★★★ **Steane's method with its factories and one fault anywhere in it is a CSS deviation of the
identity.** -/
theorem deviatesBy_recUnder_single [Fintype κ] {F : MethodRound → Fin 7 → κ → PairOp}
    {Φ : MethodRound → FacFaults κ} (hF : ∀ r q, ∑ k, (F r q k)ᴴ * F r q k = 1)
    (hOn : ∀ r q k, OnPair q (F r q k)) (hΦ : ∀ r, (Φ r).Valid) (l : RecLoc) :
    DeviatesBy steaneProj cssMix id (recUnder F Φ hF hΦ fun l' => decide (l' = l)).apply :=
  deviatesBy_cssMix_of_exists_atQubit _ (exists_atQubit_recKraus'_single hOn hΦ l)

/-! ### One location space -/

/-- **The locations of one step**: location `q` of the gadget, or a location of the recovery after
it — an extraction location or a location of either round's ancilla factory. -/
abbrev StepLoc : Type := Fin 7 ⊕ RecLoc

instance instDecidableEqStepLoc : DecidableEq StepLoc := inferInstanceAs (DecidableEq (Fin 7 ⊕ RecLoc))

instance instFintypeStepLoc : Fintype StepLoc := inferInstanceAs (Fintype (Fin 7 ⊕ RecLoc))

/-- **The machine's locations**: `N` steps of `113` (`7` at the gadget, `106` in the recovery). -/
abbrev OvLoc (N : ℕ) : Type := Fin N × StepLoc

variable {N : ℕ}

/-- The pattern read on gadget `j`. -/
def gatePat (ω : OvLoc N → Bool) (j : Fin N) : Fin 7 → Bool := fun q => ω (j, .inl q)

/-- The pattern read on recovery `j`. -/
def recPat (ω : OvLoc N → Bool) (j : Fin N) : RecLoc → Bool := fun l => ω (j, .inr l)

/-- The step before `k`, or `k` itself at `k = 0`. -/
def prevStep (k : Fin N) : Fin N := ⟨k.val - 1, by omega⟩

/-- The locations of the `k`-th extended rectangle, as the image of a fixed type: step `k`'s, then the
recovery of the step before. -/
def winLoc (k : Fin N) : StepLoc ⊕ RecLoc → OvLoc N
  | .inl s => (k, s)
  | .inr l => (prevStep k, .inr l)

/-- **The `k`-th extended rectangle's locations**: gadget `k`, recovery `k`, and recovery `k − 1` when
`k ≥ 1`. Windows `k` and `k + 1` share recovery `k`. -/
def window (k : Fin N) : Finset (OvLoc N) := Finset.univ.image (winLoc k)

/-- ★ **A window has at most `219` locations**: a step's `113` and the previous recovery's `106`. -/
theorem card_window_le (k : Fin N) : (window k).card ≤ 219 := by
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, card_methodRound]

theorem mem_window_step (k : Fin N) (s : StepLoc) : (k, s) ∈ window k :=
  Finset.mem_image.2 ⟨.inl s, Finset.mem_univ _, rfl⟩

theorem mem_window_prev {k : ℕ} (hk : k + 1 < N) (l : RecLoc) :
    ((⟨k, by omega⟩ : Fin N), (.inr l : StepLoc)) ∈ window ⟨k + 1, hk⟩ :=
  Finset.mem_image.2 ⟨.inr l, Finset.mem_univ _, by simp [winLoc, prevStep]⟩

/-- **Every extended rectangle holds at most one fault.** -/
def WindowsGood (ω : OvLoc N → Bool) : Prop :=
  ∀ k : Fin N, ((window k).filter fun x => ω x = true).card ≤ 1

theorem WindowsGood.eq {ω : OvLoc N → Bool} (hω : WindowsGood ω) (k : Fin N) {x y : OvLoc N}
    (hx : x ∈ window k) (hy : y ∈ window k) (hωx : ω x = true) (hωy : ω y = true) : x = y :=
  Finset.card_le_one.1 (hω k) x (Finset.mem_filter.2 ⟨hx, hωx⟩) y (Finset.mem_filter.2 ⟨hy, hωy⟩)

/-- A good pattern marks at most one location of a gadget. -/
theorem WindowsGood.card_gatePat {ω : OvLoc N → Bool} (hω : WindowsGood ω) (j : Fin N) :
    (Finset.univ.filter fun q => gatePat ω j q = true).card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb => by
    have := hω.eq j (mem_window_step j (.inl a)) (mem_window_step j (.inl b))
      (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    simpa using this

/-- A good pattern marks no location of a recovery, or exactly one. -/
theorem WindowsGood.recPat_cases {ω : OvLoc N → Bool} (hω : WindowsGood ω) (j : Fin N) :
    (recPat ω j = fun _ => false) ∨ ∃ l, recPat ω j = fun l' => decide (l' = l) := by
  by_cases h : ∃ l, recPat ω j l = true
  · obtain ⟨l, hl⟩ := h
    refine Or.inr ⟨l, funext fun l' => ?_⟩
    by_cases hl' : l' = l
    · subst hl'
      simpa using hl
    · have hne : recPat ω j l' ≠ true := fun h' => hl' (by
        have := hω.eq j (mem_window_step j (.inr l')) (mem_window_step j (.inr l)) h' hl
        simpa using this)
      simpa [hl'] using hne
  · refine Or.inl (funext fun l => ?_)
    simpa using fun h' => h ⟨l, h'⟩

/-! ### The machine under a pattern -/

/-- The ideal gadgets, indexed by step. -/
def ovGadget (gs : Fin N → Gadget) : ℕ →
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  fun k => if h : k < N then (gs ⟨k, h⟩).ideal else id

/-- The gadgets under the pattern. -/
def ovFaultyGadget (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : OvLoc N → Bool) : ℕ →
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  fun k => if h : k < N then (gs ⟨k, h⟩).faulty (U ⟨k, h⟩) (gatePat ω ⟨k, h⟩) else id

/-- The recoveries under the pattern: Steane's method with its factories and the pattern's faults. -/
def ovRecovery [Fintype κ] (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (Φ : Fin N → MethodRound → FacFaults κ)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1) (hΦ : ∀ j r, (Φ j r).Valid)
    (ω : OvLoc N → Bool) : ℕ →
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  fun k => if h : k < N then
    (recUnder (F ⟨k, h⟩) (Φ ⟨k, h⟩) (hF ⟨k, h⟩) (hΦ ⟨k, h⟩) (recPat ω ⟨k, h⟩)).apply else id

/-- Whether recovery `k` holds a fault. -/
def recoveryFlag (ω : OvLoc N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then decide (∃ l, recPat ω ⟨k, h⟩ l = true) else false

/-- Whether gadget `k` holds a fault. -/
def gadgetFlag (ω : OvLoc N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then decide (∃ q, gatePat ω ⟨k, h⟩ q = true) else false

/-- **The machine under a pattern**: gadget, Steane's method, gadget, Steane's method, …, every piece
with the pattern's faults. -/
def overlapRun (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    [Fintype κ] (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (Φ : Fin N → MethodRound → FacFaults κ)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1) (hΦ : ∀ j r, (Φ j r).Valid)
    (ω : OvLoc N → Bool) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  ovRun (ovRecovery F Φ hF hΦ ω) (ovFaultyGadget gs U ω) N ρ

/-- ★ **The machine's ideal run is #207's `machineIdeal`.** -/
theorem ovIdeal_ovGadget (gs : Fin N → Gadget) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    ovIdeal (ovGadget gs) N ρ = machineIdeal gs ρ := by
  rw [← runMaps_ofFn_eq_ovIdeal, machineIdeal]
  congr 2
  funext j
  simp [ovGadget, j.isLt]

/-- A gadget with no faulty location is the ideal gadget. -/
theorem Gadget.faulty_none (G : Gadget) (U : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ) :
    G.faulty U (fun _ => false) = G.ideal := by
  funext ρ
  simp [Gadget.faulty, Gadget.ideal]

/-! ### The machine is a chain of overlapping rectangles -/

/-- ★★★ **The Steane machine with counted recoveries is an `IsFaultChain` for the CSS class**: a
fault-free Steane's method corrects `cssMix` (`isRecovery_methodRecovery_cssMix`), one with a fault
deviates by it (`deviatesBy_methodUnder_single`), a gadget with one faulty location deviates by it
(`Gadget.deviatesBy_faulty`), and the ideal gadgets carry it (`Gadget.propagatesD_cssMix`). -/
theorem isFaultChain_overlap (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
    (hOn : ∀ j r q k, OnPair q (F j r q k)) (Φ : Fin N → MethodRound → FacFaults κ)
    (hΦ : ∀ j r, (Φ j r).Valid) {ω : OvLoc N → Bool} (hω : WindowsGood ω) :
    IsFaultChain steaneProj cssMix N (ovGadget gs) (ovRecovery F Φ hF hΦ ω) (ovFaultyGadget gs U ω)
      (recoveryFlag ω) (gadgetFlag ω) where
  id_mem := id_mem_cssMix
  recovery k hk hf := by
    have hnone : recPat ω ⟨k, hk⟩ = fun _ => false := by
      simp only [recoveryFlag, hk, ↓reduceDIte, decide_eq_false_iff_not, not_exists] at hf
      exact funext fun l => by simpa using hf l
    simp only [ovRecovery, hk, ↓reduceDIte, hnone, recUnder_none]
    exact isRecovery_methodRecovery_cssMix
  recovery_fault k hk hf := by
    rcases hω.recPat_cases ⟨k, hk⟩ with hnone | ⟨l, hone⟩
    · simp [recoveryFlag, hk, hnone] at hf
    · simp only [ovRecovery, hk, ↓reduceDIte, hone]
      exact deviatesBy_recUnder_single (hF ⟨k, hk⟩) (hOn ⟨k, hk⟩) (hΦ ⟨k, hk⟩) l
  gadget k hk hf := by
    have hnone : gatePat ω ⟨k, hk⟩ = fun _ => false := by
      simp only [gadgetFlag, hk, ↓reduceDIte, decide_eq_false_iff_not, not_exists] at hf
      exact funext fun q => by simpa using hf q
    simp only [ovFaultyGadget, ovGadget, hk, ↓reduceDIte, hnone, Gadget.faulty_none]
  gadget_fault k hk _ := by
    simp only [ovFaultyGadget, ovGadget, hk, ↓reduceDIte]
    exact ((gs ⟨k, hk⟩).deviatesBy_faulty (hU ⟨k, hk⟩) (hω.card_gatePat ⟨k, hk⟩)).mono
      weightOne_subset_cssMix
  propagates k hk := by
    simp only [ovGadget, hk, ↓reduceDIte]
    exact (gs ⟨k, hk⟩).propagatesD_cssMix
  preserves k hk ρ hρ := by
    simp only [ovGadget, hk, ↓reduceDIte]
    exact (gs ⟨k, hk⟩).isCodeState_ideal hρ

/-- ★★ **A good window pattern makes every extended rectangle good**: two faulty pieces in the `k`-th
extended rectangle would be two faults in window `k`. -/
theorem exRecGood_of_windowsGood {ω : OvLoc N → Bool} (hω : WindowsGood ω) :
    ∀ k < N, ExRecGood (recoveryFlag ω) (gadgetFlag ω) k := by
  intro k hk
  -- the faulty locations each flag points at, all inside window `k`
  have hG : gadgetFlag ω k = true → ∃ q, ω (⟨k, hk⟩, .inl q) = true := by
    intro h
    simp only [gadgetFlag, hk, ↓reduceDIte] at h
    exact of_decide_eq_true h
  have hR : recoveryFlag ω k = true → ∃ l, ω (⟨k, hk⟩, .inr l) = true := by
    intro h
    simpa [recoveryFlag, hk, recPat, decide_eq_true_eq] using h
  have hGR : gadgetFlag ω k = true → recoveryFlag ω k = true → False := by
    intro h1 h2
    obtain ⟨q, hq⟩ := hG h1
    obtain ⟨l, hl⟩ := hR h2
    have := hω.eq ⟨k, hk⟩ (mem_window_step _ (.inl q)) (mem_window_step _ (.inr l)) hq hl
    simp at this
  unfold ExRecGood
  cases k with
  | zero =>
    cases h1 : gadgetFlag ω 0 <;> cases h2 : recoveryFlag ω 0 <;> simp [lastFault]
    exact hGR h1 h2
  | succ k =>
    have hL : lastFault (recoveryFlag ω) (k + 1) = true →
        ∃ l, ω (⟨k, by omega⟩, .inr l) = true := by
      intro h
      simpa [lastFault, recoveryFlag, show k < N by omega, recPat, decide_eq_true_eq] using h
    have hLG : lastFault (recoveryFlag ω) (k + 1) = true → gadgetFlag ω (k + 1) = true → False := by
      intro h1 h2
      obtain ⟨l, hl⟩ := hL h1
      obtain ⟨q, hq⟩ := hG h2
      have := hω.eq ⟨k + 1, hk⟩ (mem_window_prev hk l) (mem_window_step _ (.inl q)) hl hq
      simp at this
    have hLR : lastFault (recoveryFlag ω) (k + 1) = true → recoveryFlag ω (k + 1) = true → False := by
      intro h1 h2
      obtain ⟨l, hl⟩ := hL h1
      obtain ⟨l', hl'⟩ := hR h2
      have := hω.eq ⟨k + 1, hk⟩ (mem_window_prev hk l) (mem_window_step _ (.inr l')) hl hl'
      simp at this
    cases h0 : lastFault (recoveryFlag ω) (k + 1) <;> cases h1 : gadgetFlag ω (k + 1) <;>
      cases h2 : recoveryFlag ω (k + 1) <;> simp
    exacts [hGR h1 h2, hLR h0 h2, hLG h0 h1, hLG h0 h1]

/-! ### The machine -/

/-- ★★★ **The level-one Steane machine with the recovery's locations counted.** For every circuit of
`N` gadgets from the set, unitary faults `U` at the gadgets' locations, channel faults `F` — any
trace-preserving Kraus families on the pairs, before or after the `CNOT` (`aroundFam`) — at Steane's
method's extraction locations, and every encoded input:

* **a pattern with at most one fault in each overlapping extended rectangle** leaves the state a CSS
  deviation of the ideal one — exactly the ideal one when the last recovery is fault-free — and a
  final ideal decoding returns the ideal output (`IsFaultChain.ovRun_spec`,
  `IsFaultChain.decode_ovRun`, fed by `isFaultChain_overlap` and `exRecGood_of_windowsGood`);
* **under independent faults of rate at most `p` at all `21 N` locations**, the decoded output is
  ideal with probability at least `1 − 595 N p²`, by the union bound over the `N` windows of at most
  `35` locations (`one_sub_le_measure_output_eq_windows`). -/
theorem steane_machine_overlap (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
    (hOn : ∀ j r q k, OnPair q (F j r q k)) (Φ : Fin N → MethodRound → FacFaults κ)
    (hΦ : ∀ j r, (Φ j r).Valid) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : IsCodeState steaneProj ρ) :
    (∀ ω : OvLoc N → Bool, WindowsGood ω →
        (∃ E ∈ cssMix, overlapRun gs U F Φ hF hΦ ω ρ = E (machineIdeal gs ρ))
        ∧ (lastFault (recoveryFlag ω) N = false → overlapRun gs U F Φ hF hΦ ω ρ = machineIdeal gs ρ)
        ∧ methodRecovery.apply (overlapRun gs U F Φ hF hΦ ω ρ) = machineIdeal gs ρ)
    ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
        ν {c | c = true} ≤ ENNReal.ofReal p →
        1 - (N : ℝ≥0∞) * ENNReal.ofReal (23871 * p ^ 2)
          ≤ Measure.pi (fun _ : OvLoc N => ν)
              {ω | methodRecovery.apply (overlapRun gs U F Φ hF hΦ ω ρ) = machineIdeal gs ρ} := by
  have hdet : ∀ ω : OvLoc N → Bool, WindowsGood ω →
      (∃ E ∈ cssMix, overlapRun gs U F Φ hF hΦ ω ρ = E (machineIdeal gs ρ))
      ∧ (lastFault (recoveryFlag ω) N = false → overlapRun gs U F Φ hF hΦ ω ρ = machineIdeal gs ρ)
      ∧ methodRecovery.apply (overlapRun gs U F Φ hF hΦ ω ρ) = machineIdeal gs ρ := by
    intro ω hω
    have hc := isFaultChain_overlap gs U hU F hF hOn Φ hΦ hω
    have hg := exRecGood_of_windowsGood hω
    obtain ⟨hdev, hex⟩ := hc.ovRun_spec hg hρ N le_rfl
    rw [ovIdeal_ovGadget] at hdev hex
    refine ⟨hdev, hex, ?_⟩
    rw [overlapRun, hc.decode_ovRun hg isRecovery_methodRecovery_cssMix hρ, ovIdeal_ovGadget]
  refine ⟨hdet, fun ν _ p hp hν => ?_⟩
  have h595 : ((Nat.choose 219 2 : ℕ) : ℝ) = 23871 := by norm_num [Nat.choose_two_right]
  have h := one_sub_le_measure_output_eq_windows ν hp hν (w := 219) window card_window_le
    (out := fun ω => methodRecovery.apply (overlapRun gs U F Φ hF hΦ ω ρ)) (ideal := machineIdeal gs ρ)
    fun ω hω => (hdet ω hω).2.2
  rwa [h595] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
