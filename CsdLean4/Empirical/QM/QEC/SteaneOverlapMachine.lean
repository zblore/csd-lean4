/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneFaultModel
public import CsdLean4.Mathlib.QuantumInfo.OverlappingRectangles

/-!
# The Steane machine with the recovery's locations counted

**Category:** 3-Local (Empirical, QM twin). BACKLOG #233 (split from ~~#229~~); fault model
completed by #235.

`SteaneMachine.lean` (~~#207~~) proved the level-one threshold statement with faults at the gadgets
and an ideal recovery. `SteaneFaultyRecovery.lean` (~~#232~~) made one faulty recovery a theorem
inside one extended rectangle. This module runs the whole machine with **every recovery a circuit with
its own fault locations**: gadget, Steane's method, gadget, Steane's method, …, one fault pattern over
all of them, and the extended rectangles overlapping as in Aliferis–Gottesman–Preskill.

## Steane's method under any fault pattern

* `sum_prod_ofFn_conjTranspose_mul` — **any number of channels in sequence is a channel**: ordered
  products of Kraus operators, one from each trace-preserving family; `prod_ofFn_eq_one`;
* `card_methodRound`; `locFam`, `locFam_tp`, `onPair_locFam`, `onPair_locFam_false` — **one
  extraction location under the pattern as a Kraus family**: the fault's channel if it is faulty, the
  identity if not;
* `roundKraus`, `roundKraus_tp`, `roundKraus_none`, `roundKraus_none_of_ne`,
  `onPair_roundKraus_single` — **the faults of one round under a pattern**, branch by branch;
  `faultReadOp_zero`, `bitFaultOp_zero`, `phaseFaultOp_zero`;
* `UnderIdx`, `underKraus`, `underKraus_tp`, ★★ `methodUnder` — **Steane's method with a channel at
  every faulty extraction location of a pattern** (`SteaneFaultModel.lean`, BACKLOG ~~#235~~: any
  trace-preserving family on the pair, before or after the `CNOT`), a channel for every pattern;
  ★ `methodUnder_none` — with no fault it is `methodRecovery`; ★★ `atQubit_underKraus_single`,
  ★★★ `deviatesBy_methodUnder_single` — with one fault it is a CSS deviation.

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
  recovery deviates by `cssMix` (`deviatesBy_methodUnder_single`), a fault-free one corrects it
  (`isRecovery_methodRecovery_cssMix`), a gadget with one fault deviates by it, the ideal gadgets carry
  it; ★★ `exRecGood_of_windowsGood` — a good window pattern makes every extended rectangle good;
* ★★★ `steane_machine_overlap` — **the level-one machine with the recovery's locations counted**:
  for every circuit of `N` gadgets, unitary faults at every gadget location, a channel fault on the
  pair at every extraction location, and an encoded input, a pattern with at most one fault in each overlapping extended
  rectangle leaves the state a CSS deviation of the ideal one, exactly the ideal one if the last
  recovery is fault-free, and the ideal one after a final ideal decoding; under independent faults of
  rate at most `p` at the `21 N` locations, the decoded output is ideal with probability at least
  `1 − 595 N p²` (`595 = C(35, 2)`).

## Honest scope

⚠️ **Ancilla preparation is ideal** (#234), and so are the encoding of the input and the final
decoding (#236) and the classical decoding inside each recovery. The extraction locations are the only
recovery locations counted.

⚠️ **A fault at an extraction location stays on its pair.** The fault at `(r, q)` is any
trace-preserving Kraus family on data qubit `q` and ancilla qubit `q`, after the `CNOT` of round `r`;
a fault before the `CNOT`, or on both sides, is one after it (`readAround_eq`, `aroundFam`,
BACKLOG ~~#235~~). Faults at the gadgets are still unitary on one qubit (#207's model).

⚠️ **One round per basis**, as in ~~#228~~; no repeated syndrome measurement.

⚠️ **One block, three gates**, as in ~~#207~~: `H̄`, `X̄`, `Z̄`. The two-block `CNOT̄` is #226.

⚠️ **Level one.** The concatenated machine with counted recoveries is #231.

⚠️ **The constant is `C(35, 2) = 595`** from the union bound over each window's pairs; it is not
claimed sharp.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97; A. Steane,
PRL 78 (1997) 2252; `specs/BACKLOG.md` #233, #235, #232, #229, #207, #96, #97, #234, #236;
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

namespace QuantumInfo

/-- **Any number of channels in sequence**: the ordered products of one Kraus operator from each of
`m` trace-preserving families form a trace-preserving family. -/
theorem sum_prod_ofFn_conjTranspose_mul {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] :
    ∀ {m : ℕ} (X : Fin m → ι → Matrix n n ℂ), (∀ i, ∑ a, (X i a)ᴴ * X i a = 1) →
      ∑ s : Fin m → ι, ((List.ofFn fun i => X i (s i)).prod)ᴴ * (List.ofFn fun i => X i (s i)).prod
        = 1
  | 0, X, _ => by simp
  | m + 1, X, hX => by
    have ih := sum_prod_ofFn_conjTranspose_mul (fun i => X i.succ) fun i => hX i.succ
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ι).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    rw [Finset.sum_comm]
    calc ∑ t : Fin m → ι, ∑ a, (X 0 a * (List.ofFn fun i => X i.succ (t i)).prod)ᴴ
          * (X 0 a * (List.ofFn fun i => X i.succ (t i)).prod)
        = ∑ t : Fin m → ι, ((List.ofFn fun i => X i.succ (t i)).prod)ᴴ * (∑ a, (X 0 a)ᴴ * X 0 a)
          * (List.ofFn fun i => X i.succ (t i)).prod := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by simp only [hX 0, Matrix.mul_one]; exact ih

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-- An ordered product whose factors are all `1` is `1`. -/
theorem prod_ofFn_eq_one {M : Type*} [Monoid M] {m : ℕ} (f : Fin m → M) (h : ∀ j, f j = 1) :
    (List.ofFn f).prod = 1 := by
  rw [show f = fun _ => 1 from funext h, List.ofFn_const, List.prod_replicate, one_pow]

/-! ### Steane's method under any fault pattern -/

instance : Fintype MethodRound :=
  ⟨{.bit, .phase}, fun r => by cases r <;> simp⟩

theorem card_methodRound : Fintype.card MethodRound = 2 := rfl

variable {κ : Type}

/-- **One extraction location under the pattern, as a Kraus family on `Option κ`**: the fault's
operators `K k` at `some k` if the location is faulty, the identity at `none` if it is not. -/
def locFam {α κ : Type*} [MonoidWithZero α] (K : κ → α) (b : Bool) : Option κ → α
  | none => if b then 0 else 1
  | some k => if b then K k else 0

theorem locFam_tp {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] {K : κ → Matrix n n ℂ}
    (hK : ∑ k, (K k)ᴴ * K k = 1)
    (b : Bool) : ∑ o, (locFam K b o)ᴴ * locFam K b o = 1 := by
  rw [Fintype.sum_option]
  cases b <;> simp [locFam, hK]

theorem onPair_locFam {q : Fin 7} {κ : Type*} {K : κ → PairOp} (hOn : ∀ k, OnPair q (K k))
    (b : Bool) : ∀ o, OnPair q (locFam K b o)
  | none => by cases b <;> simp [locFam, OnPair.zero, onPair_one]
  | some k => by cases b <;> simp [locFam, OnPair.zero, hOn k]

/-- A location without a fault is on every pair. -/
theorem onPair_locFam_false (q : Fin 7) {κ : Type*} (K : κ → PairOp) :
    ∀ o, OnPair q (locFam K false o)
  | none => by simp [locFam, onPair_one]
  | some _ => by simp [locFam, OnPair.zero]

/-- **The faults of one round under a pattern**, in branch `s`: the ordered product over the seven
pairs of their locations' Kraus operators. -/
def roundKraus {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α) (b : Fin 7 → Bool)
    (s : Fin 7 → Option κ) : α :=
  (List.ofFn fun q => locFam (K q) (b q) (s q)).prod

theorem roundKraus_tp {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    {K : Fin 7 → κ → Matrix n n ℂ}
    (hK : ∀ q, ∑ k, (K q k)ᴴ * K q k = 1) (b : Fin 7 → Bool) :
    ∑ s, (roundKraus K b s)ᴴ * roundKraus K b s = 1 :=
  sum_prod_ofFn_conjTranspose_mul (fun q => locFam (K q) (b q)) fun q => locFam_tp (hK q) (b q)

/-- With no faulty pair the round is the identity in the branch `none` everywhere… -/
theorem roundKraus_none {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α) :
    roundKraus K (fun _ => false) (fun _ => none) = 1 := by
  unfold roundKraus
  exact prod_ofFn_eq_one _ fun q => by simp [locFam]

/-- …and zero in every other branch. -/
theorem roundKraus_none_of_ne {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α)
    {s : Fin 7 → Option κ}
    (h : s ≠ fun _ => none) : roundKraus K (fun _ => false) s = 0 := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hq
  have h0 : locFam (K q) ((fun _ => false) q) (s q) = 0 := by simp [locFam, hk]
  unfold roundKraus
  exact List.prod_eq_zero (List.mem_ofFn.2 ⟨q, h0⟩)

/-- With one faulty pair `q`, every branch of the round is an operator on the pair `q`. -/
theorem onPair_roundKraus_single {κ : Type*} {K : Fin 7 → κ → PairOp} {q : Fin 7}
    (hOn : ∀ k, OnPair q (K q k)) (s : Fin 7 → Option κ) :
    OnPair q (roundKraus K (fun q' => decide (q' = q)) s) := by
  refine OnPair.list_prod _ fun F hF => ?_
  obtain ⟨q', rfl⟩ := List.mem_ofFn.1 hF
  by_cases h : q' = q
  · subst h
    simpa only [decide_true] using onPair_locFam hOn true (s q')
  · simpa only [decide_eq_false h] using onPair_locFam_false q (K q') (s q')

theorem faultReadOp_zero (m : Fin 7 → Fin 2) : faultReadOp 0 m = 0 := by
  simp [faultReadOp]

theorem bitFaultOp_zero (m : Fin 7 → Fin 2) : bitFaultOp 0 m = 0 := by
  rw [bitFaultOp, faultReadOp_zero, Matrix.mul_zero]

theorem phaseFaultOp_zero (m : Fin 7 → Fin 2) : phaseFaultOp 0 m = 0 := by
  rw [phaseFaultOp, faultReadOp_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero]

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
def ovRecovery [Fintype κ] (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
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
    [Fintype κ] (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
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
deviates by it (`deviatesBy_methodUnder_single`), a gadget with one faulty location deviates by it
(`Gadget.deviatesBy_faulty`), and the ideal gadgets carry it (`Gadget.propagatesD_cssMix`). -/
theorem isFaultChain_overlap (gs : Fin N → Gadget) (U : Fin N → Fin 7 → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j q, U j q ∈ Matrix.unitaryGroup (Fin 2) ℂ) [Fintype κ]
    (F : Fin N → MethodRound → Fin 7 → κ → PairOp)
    (hF : ∀ j r q, ∑ k, (F j r q k)ᴴ * F j r q k = 1)
    (hOn : ∀ j r q k, OnPair q (F j r q k)) {ω : OvLoc N → Bool} (hω : WindowsGood ω) :
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
    · simp only [ovRecovery, hk, ↓reduceDIte, hone]
      exact deviatesBy_methodUnder_single (hF ⟨k, hk⟩) (hOn ⟨k, hk⟩) r q
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
    (hOn : ∀ j r q k, OnPair q (F j r q k)) {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
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
