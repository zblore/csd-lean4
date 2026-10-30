/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneFaultyRecovery
public import CsdLean4.Mathlib.QuantumInfo.OverlappingRectangles

/-!
# The Steane machine with the recovery's locations counted

**Category:** 3-Local (Empirical, QM twin). BACKLOG #233 (split from ~~#229~~).

`SteaneMachine.lean` (~~#207~~) proved the level-one threshold statement with faults at the gadgets
and an ideal recovery. `SteaneFaultyRecovery.lean` (~~#232~~) made one faulty recovery a theorem
inside one extended rectangle. This module runs the whole machine with **every recovery a circuit with
its own fault locations**: gadget, Steane's method, gadget, Steane's method, …, one fault pattern over
all of them, and the extended rectangles overlapping as in Aliferis–Gottesman–Preskill.

## Steane's method under any fault pattern

* `card_methodRound`, `PairOp`; `prod_ofFn_eq_of_ne`, `prod_ofFn_eq_one` — ordered products with one or no factor
  different from `1`;
* `roundFault` — **the faults of one round under a pattern**: the product, over the faulty pairs, of
  their unitaries; `roundFault_mem`, `roundFault_none`, `roundFault_single`;
* `underKraus`, ★★ `methodUnder` — **Steane's method with a unitary at every faulty extraction
  location of a pattern**, a channel for every pattern; ★ `methodUnder_none` — with no fault it is
  `methodRecovery`; ★ `methodUnder_single` — with one fault it is ~~#232~~'s `faultyMethod`;
  `onPair_one` — the fault model is inhabited.

## The machine

* `StepLoc`, `OvLoc N` — **one location space**: step `j` has its gadget's seven locations and its
  recovery's fourteen extraction locations, `21 N` in all; `gatePat`, `recPat` — a pattern read on one
  piece;
* `window k` — **the `k`-th extended rectangle's locations**: step `k`'s twenty-one and the recovery
  of step `k − 1` (for `k ≥ 1`), ★ `card_window_le` — at most `35`; `WindowsGood ω` — every window
  holds at most one fault;
* `ovGadget`, `ovFaultyGadget`, `ovRecovery`, `overlapRun` — the machine under a pattern;
  `recoveryFlag`, `gadgetFlag` — which pieces are faulty; ★ `ovIdeal_ovGadget` — its ideal run is
  #207's `machineIdeal`;
* ★★★ `isFaultChain_overlap` — **the machine is an `IsFaultChain` for the CSS class**: a faulty
  recovery deviates by `cssMix` (`deviatesBy_faultyMethod`), a fault-free one corrects it
  (`isRecovery_methodRecovery_cssMix`), a gadget with one fault deviates by it, the ideal gadgets carry
  it; ★★ `exRecGood_of_windowsGood` — a good window pattern makes every extended rectangle good;
* ★★★ `steane_machine_overlap` — **the level-one machine with the recovery's locations counted**:
  for every circuit of `N` gadgets, unitary faults at every gadget location and every extraction
  location, and an encoded input, a pattern with at most one fault in each overlapping extended
  rectangle leaves the state a CSS deviation of the ideal one, exactly the ideal one if the last
  recovery is fault-free, and the ideal one after a final ideal decoding; under independent faults of
  rate at most `p` at the `21 N` locations, the decoded output is ideal with probability at least
  `1 − 595 N p²` (`595 = C(35, 2)`).

## Honest scope

⚠️ **Ancilla preparation is ideal** (#234), and so are the encoding of the input and the final
decoding (#236) and the classical decoding inside each recovery. The extraction locations are the only
recovery locations counted.

⚠️ **Faults after the transversal `CNOT`, unitary.** A fault at extraction location `(r, q)` is a
unitary on data qubit `q` and ancilla qubit `q` after the `CNOT` of round `r`; faults before it and
faults that are channels are #235.

⚠️ **One round per basis**, as in ~~#228~~; no repeated syndrome measurement.

⚠️ **One block, three gates**, as in ~~#207~~: `H̄`, `X̄`, `Z̄`. The two-block `CNOT̄` is #226.

⚠️ **Level one.** The concatenated machine with counted recoveries is #231.

⚠️ **The constant is `C(35, 2) = 595`** from the union bound over each window's pairs; it is not
claimed sharp.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97; A. Steane,
PRL 78 (1997) 2252; `specs/BACKLOG.md` #233, #232, #229, #207, #96, #97, #234, #235, #236;
`Mathlib/QuantumInfo/OverlappingRectangles.lean`, `Mathlib/QuantumInfo/ExtendedRectangle.lean`,
`Empirical/QM/QEC/SteaneFaultyRecovery.lean`, `Empirical/QM/QEC/SteaneMethod.lean`,
`Empirical/QM/QEC/SteaneMachine.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
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

/-! ### Ordered products with at most one factor different from `1` -/

/-- An ordered product whose factors are all `1` is `1`. -/
theorem prod_ofFn_eq_one {M : Type*} [Monoid M] {m : ℕ} (f : Fin m → M) (h : ∀ j, f j = 1) :
    (List.ofFn f).prod = 1 := by
  rw [show f = fun _ => 1 from funext h, List.ofFn_const, List.prod_replicate, one_pow]

/-- An ordered product whose factors are all `1` except at `i` is the factor at `i`. -/
theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | m + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [prod_ofFn_eq_one _ fun j => h _ (Fin.succ_ne_zero j), mul_one]
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_eq_of_ne (fun j => f j.succ) i fun j hj =>
        h _ fun h' => hj (Fin.succ_injective _ h')

/-! ### Steane's method under any fault pattern -/

instance : Fintype MethodRound :=
  ⟨{.bit, .phase}, fun r => by cases r <;> simp⟩

theorem card_methodRound : Fintype.card MethodRound = 2 := rfl

/-- Operators on the data block and the ancilla block together. -/
abbrev PairOp : Type :=
  Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ

/-- **The faults of one round under a pattern**: the ordered product, over the pairs `q` the pattern
marks faulty, of their faults `F q`. Stated in any monoid; at the pair register it is a `PairOp`. -/
def roundFault {α : Type*} [Monoid α] (F : Fin 7 → α) (b : Fin 7 → Bool) : α :=
  (List.ofFn fun q => if b q then F q else 1).prod

/-- A round's fault stays in any submonoid holding the pair faults — the unitary group in particular. -/
theorem roundFault_mem {α : Type*} [Monoid α] {S : Submonoid α} {F : Fin 7 → α} (hF : ∀ q, F q ∈ S)
    (b : Fin 7 → Bool) : roundFault F b ∈ S := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨q, rfl⟩ := List.mem_ofFn.1 hx
  split_ifs
  exacts [hF q, one_mem _]

theorem roundFault_conjTranspose_mul {F : Fin 7 → PairOp}
    (hF : ∀ q, F q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) (b : Fin 7 → Bool) :
    (roundFault F b)ᴴ * roundFault F b = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.1 (roundFault_mem hF b)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- With no faulty pair the round is fault-free. -/
theorem roundFault_none {α : Type*} [Monoid α] (F : Fin 7 → α) :
    roundFault F (fun _ => false) = 1 :=
  prod_ofFn_eq_one _ fun _ => by simp only [Bool.false_eq_true, ↓reduceIte]

/-- With one faulty pair `q` the round's fault is `F q`. -/
theorem roundFault_single {α : Type*} [Monoid α] (F : Fin 7 → α) (q : Fin 7) :
    roundFault F (fun q' => decide (q' = q)) = F q := by
  rw [roundFault, prod_ofFn_eq_of_ne _ q fun j hj => by simp [hj]]
  simp

/-- A branch of Steane's method with the faults `F r q` at the faulty extraction locations of `b`. -/
def underKraus (F : MethodRound → Fin 7 → PairOp) (b : MethodRound × Fin 7 → Bool) (mm : OutPair) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  phaseFaultOp (roundFault (F .phase) fun q => b (.phase, q)) mm.2
    * bitFaultOp (roundFault (F .bit) fun q => b (.bit, q)) mm.1

/-- ★★ **Steane's method under a fault pattern**: a unitary `F r q` on data qubit `q` and ancilla
qubit `q` after the transversal `CNOT` of round `r`, at every location the pattern marks faulty. A
channel for every pattern. -/
def methodUnder (F : MethodRound → Fin 7 → PairOp)
    (hF : ∀ r q, F r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (b : MethodRound × Fin 7 → Bool) : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) OutPair where
  kraus := underKraus F b
  tp := sum_mul_conjTranspose_mul_of_tp
    (sum_bitFaultOp_conjTranspose_mul (roundFault_conjTranspose_mul (hF .bit) _))
    (sum_phaseFaultOp_conjTranspose_mul (roundFault_conjTranspose_mul (hF .phase) _))

/-- ★ **With no fault, Steane's method under the pattern is `methodRecovery`.** -/
theorem methodUnder_none (F : MethodRound → Fin 7 → PairOp)
    (hF : ∀ r q, F r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) :
    (methodUnder F hF fun _ => false).apply = methodRecovery.apply := by
  have hk : (methodUnder F hF fun _ => false).kraus = methodRecovery.kraus := by
    funext mm
    show underKraus F (fun _ => false) mm = methodKraus mm
    rw [underKraus, roundFault_none, roundFault_none, phaseFaultOp_one, bitFaultOp_one, methodKraus]
  funext ρ
  rw [Channel.apply_def, Channel.apply_def, hk]

/-- ★ **With one fault, at `(r, q)`, it is ~~#232~~'s `faultyMethod`.** -/
theorem methodUnder_single (F : MethodRound → Fin 7 → PairOp)
    (hF : ∀ r q, F r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (r : MethodRound) (q : Fin 7) (hFu : (F r q)ᴴ * F r q = 1) :
    (methodUnder F hF fun l => decide (l = (r, q))).apply = (faultyMethod (F r q) hFu r).apply := by
  have hk : (methodUnder F hF fun l => decide (l = (r, q))).kraus = (faultyMethod (F r q) hFu r).kraus := by
    funext mm
    show underKraus F (fun l => decide (l = (r, q))) mm = faultyKraus (F r q) r mm
    cases r with
    | bit =>
      have h1 : (fun q' => decide (((MethodRound.phase, q') : MethodRound × Fin 7) = (.bit, q)))
          = fun _ => false := funext fun q' => by simp
      have h2 : (fun q' => decide (((MethodRound.bit, q') : MethodRound × Fin 7) = (.bit, q)))
          = fun q' => decide (q' = q) := funext fun q' => by simp
      rw [underKraus, h1, h2, roundFault_none, roundFault_single, phaseFaultOp_one, faultyKraus]
    | phase =>
      have h1 : (fun q' => decide (((MethodRound.bit, q') : MethodRound × Fin 7) = (.phase, q)))
          = fun _ => false := funext fun q' => by simp
      have h2 : (fun q' => decide (((MethodRound.phase, q') : MethodRound × Fin 7) = (.phase, q)))
          = fun q' => decide (q' = q) := funext fun q' => by simp
      rw [underKraus, h1, h2, roundFault_none, roundFault_single, bitFaultOp_one, faultyKraus]
  funext ρ
  rw [Channel.apply_def, Channel.apply_def, hk]

/-- The fault model is inhabited: the identity on the pair is an operator on the pair. -/
theorem onPair_one (q : Fin 7) : OnPair q 1 :=
  ⟨1, fun _ => 1, fun _ => 1, by simp [gateOf_one]⟩

/-! ### One location space -/

/-- **The locations of one step**: location `q` of the gadget, or extraction location `(r, q)` of the
recovery after it. -/
abbrev StepLoc : Type := Fin 7 ⊕ (MethodRound × Fin 7)

/-- **The machine's locations**: `N` steps of twenty-one. -/
abbrev OvLoc (N : ℕ) : Type := Fin N × StepLoc

variable {N : ℕ}

/-- The pattern read on gadget `j`. -/
def gatePat (ω : OvLoc N → Bool) (j : Fin N) : Fin 7 → Bool := fun q => ω (j, .inl q)

/-- The pattern read on recovery `j`. -/
def recPat (ω : OvLoc N → Bool) (j : Fin N) : MethodRound × Fin 7 → Bool := fun l => ω (j, .inr l)

/-- The step before `k`, or `k` itself at `k = 0`. -/
def prevStep (k : Fin N) : Fin N := ⟨k.val - 1, by omega⟩

/-- The locations of the `k`-th extended rectangle, as the image of a fixed type: step `k`'s, then the
recovery of the step before. -/
def winLoc (k : Fin N) : StepLoc ⊕ (MethodRound × Fin 7) → OvLoc N
  | .inl s => (k, s)
  | .inr l => (prevStep k, .inr l)

/-- **The `k`-th extended rectangle's locations**: gadget `k`, recovery `k`, and recovery `k − 1` when
`k ≥ 1`. Windows `k` and `k + 1` share recovery `k`. -/
def window (k : Fin N) : Finset (OvLoc N) := Finset.univ.image (winLoc k)

/-- ★ **A window has at most thirty-five locations.** -/
theorem card_window_le (k : Fin N) : (window k).card ≤ 35 := by
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, card_methodRound]

theorem mem_window_step (k : Fin N) (s : StepLoc) : (k, s) ∈ window k :=
  Finset.mem_image.2 ⟨.inl s, Finset.mem_univ _, rfl⟩

theorem mem_window_prev {k : ℕ} (hk : k + 1 < N) (l : MethodRound × Fin 7) :
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

/-- The recoveries under the pattern: Steane's method with the pattern's faults. -/
def ovRecovery (F : Fin N → MethodRound → Fin 7 → PairOp)
    (hF : ∀ j r q, F j r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (ω : OvLoc N → Bool) : ℕ →
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ → Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  fun k => if h : k < N then (methodUnder (F ⟨k, h⟩) (hF ⟨k, h⟩) (recPat ω ⟨k, h⟩)).apply else id

/-- Whether recovery `k` holds a fault. -/
def recoveryFlag (ω : OvLoc N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then decide (∃ l, recPat ω ⟨k, h⟩ l = true) else false

/-- Whether gadget `k` holds a fault. -/
def gadgetFlag (ω : OvLoc N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then decide (∃ q, gatePat ω ⟨k, h⟩ q = true) else false

/-- **The machine under a pattern**: gadget, Steane's method, gadget, Steane's method, …, every piece
with the pattern's faults. -/
def overlapRun (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (F : Fin N → MethodRound → Fin 7 → PairOp)
    (hF : ∀ j r q, F j r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (ω : OvLoc N → Bool) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  ovRun (ovRecovery F hF ω) (ovFaultyGadget gs U ω) N ρ

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
deviates by it (`deviatesBy_faultyMethod`), a gadget with one faulty location deviates by it
(`Gadget.deviatesBy_faulty`), and the ideal gadgets carry it (`Gadget.propagatesD_cssMix`). -/
theorem isFaultChain_overlap (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (F : Fin N → MethodRound → Fin 7 → PairOp)
    (hF : ∀ j r q, F j r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (hOn : ∀ j r q, OnPair q (F j r q)) {ω : OvLoc N → Bool} (hω : WindowsGood ω) :
    IsFaultChain steaneProj cssMix N (ovGadget gs) (ovRecovery F hF ω) (ovFaultyGadget gs U ω)
      (recoveryFlag ω) (gadgetFlag ω) where
  id_mem := id_mem_cssMix
  recovery k hk hf := by
    have hnone : recPat ω ⟨k, hk⟩ = fun _ => false := by
      simp only [recoveryFlag, hk, ↓reduceDIte, decide_eq_false_iff_not, not_exists] at hf
      exact funext fun l => by simpa using hf l
    simp only [ovRecovery, hk, ↓reduceDIte, hnone, methodUnder_none]
    exact isRecovery_methodRecovery_cssMix
  recovery_fault k hk hf := by
    rcases hω.recPat_cases ⟨k, hk⟩ with hnone | ⟨⟨r, q⟩, hone⟩
    · simp [recoveryFlag, hk, hnone] at hf
    · have hFu : (F ⟨k, hk⟩ r q)ᴴ * F ⟨k, hk⟩ r q = 1 := by
        have h := Matrix.mem_unitaryGroup_iff'.1 (hF ⟨k, hk⟩ r q)
        rwa [Matrix.star_eq_conjTranspose] at h
      simp only [ovRecovery, hk, ↓reduceDIte, hone, methodUnder_single _ _ r q hFu]
      exact deviatesBy_faultyMethod hFu (hOn ⟨k, hk⟩ r q) r
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
`N` gadgets from the set, unitary faults `U` at the gadgets' locations, unitary faults `F` on the
pairs at Steane's method's extraction locations, and every encoded input:

* **a pattern with at most one fault in each overlapping extended rectangle** leaves the state a CSS
  deviation of the ideal one — exactly the ideal one when the last recovery is fault-free — and a
  final ideal decoding returns the ideal output (`IsFaultChain.ovRun_spec`,
  `IsFaultChain.decode_ovRun`, fed by `isFaultChain_overlap` and `exRecGood_of_windowsGood`);
* **under independent faults of rate at most `p` at all `21 N` locations**, the decoded output is
  ideal with probability at least `1 − 595 N p²`, by the union bound over the `N` windows of at most
  `35` locations (`one_sub_le_measure_output_eq_windows`). -/
theorem steane_machine_overlap (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) (F : Fin N → MethodRound → Fin 7 → PairOp)
    (hF : ∀ j r q, F j r q ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)
    (hOn : ∀ j r q, OnPair q (F j r q)) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : IsCodeState steaneProj ρ) :
    (∀ ω : OvLoc N → Bool, WindowsGood ω →
        (∃ E ∈ cssMix, overlapRun gs U F hF ω ρ = E (machineIdeal gs ρ))
        ∧ (lastFault (recoveryFlag ω) N = false → overlapRun gs U F hF ω ρ = machineIdeal gs ρ)
        ∧ methodRecovery.apply (overlapRun gs U F hF ω ρ) = machineIdeal gs ρ)
    ∧ ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}, 0 ≤ p →
        ν {c | c = true} ≤ ENNReal.ofReal p →
        1 - (N : ℝ≥0∞) * ENNReal.ofReal (595 * p ^ 2)
          ≤ Measure.pi (fun _ : OvLoc N => ν)
              {ω | methodRecovery.apply (overlapRun gs U F hF ω ρ) = machineIdeal gs ρ} := by
  have hdet : ∀ ω : OvLoc N → Bool, WindowsGood ω →
      (∃ E ∈ cssMix, overlapRun gs U F hF ω ρ = E (machineIdeal gs ρ))
      ∧ (lastFault (recoveryFlag ω) N = false → overlapRun gs U F hF ω ρ = machineIdeal gs ρ)
      ∧ methodRecovery.apply (overlapRun gs U F hF ω ρ) = machineIdeal gs ρ := by
    intro ω hω
    have hc := isFaultChain_overlap gs U hU F hF hOn hω
    have hg := exRecGood_of_windowsGood hω
    obtain ⟨hdev, hex⟩ := hc.ovRun_spec hg hρ N le_rfl
    rw [ovIdeal_ovGadget] at hdev hex
    refine ⟨hdev, hex, ?_⟩
    rw [overlapRun, hc.decode_ovRun hg isRecovery_methodRecovery_cssMix hρ, ovIdeal_ovGadget]
  refine ⟨hdet, fun ν _ p hp hν => ?_⟩
  have h595 : ((Nat.choose 35 2 : ℕ) : ℝ) = 595 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_windows ν hp hν (w := 35) window card_window_le
    (out := fun ω => methodRecovery.apply (overlapRun gs U F hF ω ρ)) (ideal := machineIdeal gs ρ)
    fun ω hω => (hdet ω hω).2.2
  rwa [h595] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
