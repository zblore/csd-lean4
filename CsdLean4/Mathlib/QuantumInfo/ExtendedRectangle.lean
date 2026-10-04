/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.FaultTolerantComposition

/-!
# The extended rectangle

**Category:** 1-Mathlib (CSD-free). BACKLOG #96, split out of #62 (c3).

[`FaultTolerantComposition.lean`](FaultTolerantComposition.lean) (#62 (d1)) proved
★★★ `correctedRun_eq_idealRun`: a circuit whose every gadget is a **corrected step** computes what the
ideal circuit computes. It was deliberately abstract in the step, and said so, precisely so that this
row could hand it a step built from a *faulty recovery*. This file builds those steps.

## The three hypotheses, each about a different piece

The argument is Aharonov–Ben-Or / Aliferis–Gottesman–Preskill's rectangle argument, stripped to its
algebra. A **correctable set** `D` of deviations is a parameter — for a distance-3 code it is the
weight-`≤ 1` errors — and the three pieces each get their own named property:

* `IsRecovery P R D` — the recovery **corrects** every deviation in `D` from a code state. With
  `id ∈ D` this also gives ★ `IsRecovery.apply_of_isCodeState`: a recovery does nothing to a clean
  code state;
* `DeviatesBy P D ideal actual` — the **one-fault bound** on a piece: on code states the actual map is
  the ideal one followed by some deviation in `D`. This is what "at most one fault in this piece"
  buys, and it is a hypothesis about the piece, never about the conclusion;
* `PropagatesD P D ideal` — the gadget is **transversal**: it carries a `D`-deviation of a code state
  to a `D`-deviation of its own output. Without this a leading-recovery fault would be amplified by
  the gadget, which is exactly what transversality rules out.

Hypotheses about the pieces, conclusions about the composite: nothing here assumes the rectangle is
correct in order to prove it.

## What is proved

* `exRec R₁ G R₂` — leading recovery, gadget, trailing recovery, and `rect R G` for the
  two-piece rectangle;
* ★★★ `isCorrectedStep_rect` — **a faulty gadget with a correcting recovery is a corrected step**;
* ★★★ `isCorrectedStep_exRec_leading` — **the row's instance for a FAULTY RECOVERY**: the leading
  recovery is the faulty piece, the gadget and the trailing recovery act ideally, and the rectangle is
  still a corrected step. Transversality is what makes this work: the gadget carries the leading
  recovery's error along as another correctable error, and the trailing recovery removes it;
* ★★★ `isCorrectedStep_exRec_gadget` — the same when the **gadget** is the faulty piece;
* ★★★ `isCorrectedStep_exRec_of_good` — the two together: **a good extended rectangle, whose single
  fault is anywhere but the trailing recovery, is a corrected step**;
* ★★★ `deviatesBy_exRec_trailing` — and when the fault *is* in the trailing recovery, the rectangle's
  output is a `D`-deviation from the ideal: **not** corrected here, but handed on in exactly the form
  the next rectangle's `IsRecovery` consumes. That is the overlapping-rectangle convention, made
  explicit rather than assumed away;
* ★★★ `correctedRun_eq_idealRun_of_good_exRec` — **the payoff, with no restatement**: a circuit of
  good extended rectangles computes the ideal circuit's output, by `correctedRun_eq_idealRun` applied
  verbatim. #62 (d1)'s abstraction in the step is what makes this a corollary and not a second proof.

## Honest scope

⚠️ **"At most one fault" is a hypothesis, not a count.** It enters as `DeviatesBy` on one piece and
ideal behaviour on the others. Nothing here enumerates fault locations, assigns them probabilities, or
proves that a given gadget has at most one fault with any probability. The counting and the
probabilistic join are BACKLOG #97.

⚠️ **`D` is a parameter and is never computed.** No code is fixed, so nothing here says what the
correctable set is. In particular the link to #95 is **not** made: that row shows a shared-ancilla
fault leaves a weight-`w` error, which for `w > 1` is outside what a distance-3 recovery corrects —
the reason the cat architecture is needed — but connecting the two requires a concrete `D` and a
concrete recovery, and neither is built here.

⚠️ **A trailing-recovery fault is not corrected.** `deviatesBy_exRec_trailing` is the honest statement:
the rectangle hands on a correctable deviation. That the resulting *chain* of overlapping rectangles
closes — the level-reduction step — is **not** proved here and is #97.

⚠️ **Transversality is assumed.** `PropagatesD` is a hypothesis. The corpus has it concretely for the
Steane transversal `CNOT` (`cnotT_conj_pairEnc_code`), but no instance is plugged in below.

⚠️ **No instance at a concrete code.** The theorems *produce* `IsCorrectedStep` instances from the
piecewise hypotheses; they do not exhibit one for the Steane code, which would need its recovery map
and its weight-`≤ 1` error set in this shape.

⚠️ **Maps, not channels.** As in #62 (d1), the pieces are arbitrary maps on matrices with no
positivity or trace condition imposed; nothing below uses or claims complete positivity.

## References

`Mathlib/QuantumInfo/FaultTolerantComposition.lean` (#62 (d1), `IsCorrectedStep`,
`correctedRun_eq_idealRun`); `Mathlib/QuantumInfo/AncillaLadder.lean` (#95, the propagation bound this
does not yet consume); `specs/BACKLOG.md` #96, #94, #95, #97, #62; `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

namespace QuantumInfo

variable {n : Type*} [Fintype n]

/-! ### The three piecewise properties -/

/-- **A recovery for the correctable set `D`**: it removes every deviation in `D` from a code state. -/
def IsRecovery (P : Matrix n n ℂ) (R : Matrix n n ℂ → Matrix n n ℂ)
    (D : Set (Matrix n n ℂ → Matrix n n ℂ)) : Prop :=
  ∀ E ∈ D, ∀ ρ, IsCodeState P ρ → R (E ρ) = ρ

/-- ★ **A recovery does nothing to a clean code state** — provided "no error" counts as correctable,
which is the only thing `id ∈ D` is ever used for. -/
theorem IsRecovery.apply_of_isCodeState {P : Matrix n n ℂ} {R : Matrix n n ℂ → Matrix n n ℂ}
    {D : Set (Matrix n n ℂ → Matrix n n ℂ)} (hR : IsRecovery P R D) (hid : id ∈ D)
    {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) : R ρ = ρ :=
  hR id hid ρ hρ

/-- **The one-fault bound on a piece**: on code states, `actual` is `ideal` followed by a correctable
deviation. ⚠️ A hypothesis about the piece — nothing here counts faults. -/
def DeviatesBy (P : Matrix n n ℂ) (D : Set (Matrix n n ℂ → Matrix n n ℂ))
    (ideal actual : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ ρ, IsCodeState P ρ → ∃ E ∈ D, actual ρ = E (ideal ρ)

/-- **Transversality**: the gadget carries a correctable deviation of a code state to a correctable
deviation of its own output. This is what stops a leading-recovery fault from being amplified. -/
def PropagatesD (P : Matrix n n ℂ) (D : Set (Matrix n n ℂ → Matrix n n ℂ))
    (ideal : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ E ∈ D, ∀ ρ, IsCodeState P ρ → ∃ E' ∈ D, ideal (E ρ) = E' (ideal ρ)

/-! ### Rectangles -/

/-- **The rectangle**: a gadget followed by its recovery. -/
def rect (R G : Matrix n n ℂ → Matrix n n ℂ) : Matrix n n ℂ → Matrix n n ℂ := fun ρ => R (G ρ)

/-- **The extended rectangle**: leading recovery, gadget, trailing recovery. -/
def exRec (R₁ G R₂ : Matrix n n ℂ → Matrix n n ℂ) : Matrix n n ℂ → Matrix n n ℂ :=
  fun ρ => R₂ (G (R₁ ρ))

omit [Fintype n] in
@[simp] theorem rect_apply (R G : Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    rect R G ρ = R (G ρ) := rfl

omit [Fintype n] in
@[simp] theorem exRec_apply (R₁ G R₂ : Matrix n n ℂ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    exRec R₁ G R₂ ρ = R₂ (G (R₁ ρ)) := rfl

/-! ### A faulty gadget with a correcting recovery -/

/-- ★★★ **A faulty gadget followed by a correcting recovery is a corrected step.** The two-piece
rectangle, and the simplest form of the argument: the gadget's single fault leaves a correctable
deviation of the ideal output, and the recovery removes exactly that. -/
theorem isCorrectedStep_rect {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {R G ideal : Matrix n n ℂ → Matrix n n ℂ} (hR : IsRecovery P R D)
    (hG : DeviatesBy P D ideal G)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ)) :
    IsCorrectedStep P ideal (rect R G) where
  recovers ρ hρ := by
    obtain ⟨E, hED, hEq⟩ := hG ρ hρ
    rw [rect_apply, hEq, hR E hED (ideal ρ) (hpres ρ hρ)]
  preserves := hpres

/-! ### The extended rectangle, fault by fault -/

/-- ★★★ **The instance for a FAULTY RECOVERY.** The leading recovery is the faulty piece — it leaves a
correctable deviation instead of a clean code state — while the gadget and the trailing recovery act
ideally. The rectangle is still a corrected step: transversality carries the leading fault through the
gadget as another correctable error, and the trailing recovery removes it.

This is the step #62 (d1)'s `correctedRun_eq_idealRun` was left abstract for. -/
theorem isCorrectedStep_exRec_leading {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {R₁ R₂ ideal : Matrix n n ℂ → Matrix n n ℂ}
    (hR₁ : DeviatesBy P D id R₁) (hprop : PropagatesD P D ideal) (hR₂ : IsRecovery P R₂ D)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ)) :
    IsCorrectedStep P ideal (exRec R₁ ideal R₂) where
  recovers ρ hρ := by
    obtain ⟨E, hED, hEq⟩ := hR₁ ρ hρ
    simp only [id_eq] at hEq
    obtain ⟨E', hE'D, hEq'⟩ := hprop E hED ρ hρ
    rw [exRec_apply, hEq, hEq', hR₂ E' hE'D (ideal ρ) (hpres ρ hρ)]
  preserves := hpres

/-- ★★★ **The instance when the gadget is the faulty piece.** The leading recovery sees a clean code
state and does nothing; the gadget's fault is removed by the trailing recovery. -/
theorem isCorrectedStep_exRec_gadget {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {R₁ R₂ G ideal : Matrix n n ℂ → Matrix n n ℂ} (hid : id ∈ D)
    (hR₁ : IsRecovery P R₁ D) (hG : DeviatesBy P D ideal G) (hR₂ : IsRecovery P R₂ D)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ)) :
    IsCorrectedStep P ideal (exRec R₁ G R₂) where
  recovers ρ hρ := by
    obtain ⟨E, hED, hEq⟩ := hG ρ hρ
    rw [exRec_apply, hR₁.apply_of_isCodeState hid hρ, hEq,
      hR₂ E hED (ideal ρ) (hpres ρ hρ)]
  preserves := hpres

/-- ★★★ **A good extended rectangle is a corrected step.** "Good" here is the disjunction the two
cases above cover: the single fault is in the leading recovery, or in the gadget — anywhere but the
trailing recovery, which `deviatesBy_exRec_trailing` handles instead. -/
theorem isCorrectedStep_exRec_of_good {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {R₁ R₂ G ideal : Matrix n n ℂ → Matrix n n ℂ} (hid : id ∈ D)
    (hR₂ : IsRecovery P R₂ D) (hprop : PropagatesD P D ideal)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ))
    (hgood : (DeviatesBy P D id R₁ ∧ G = ideal) ∨ (IsRecovery P R₁ D ∧ DeviatesBy P D ideal G)) :
    IsCorrectedStep P ideal (exRec R₁ G R₂) := by
  rcases hgood with ⟨hR₁, hGid⟩ | ⟨hR₁, hG⟩
  · subst hGid
    exact isCorrectedStep_exRec_leading hR₁ hprop hR₂ hpres
  · exact isCorrectedStep_exRec_gadget hid hR₁ hG hR₂ hpres

/-- ★★★ **A fault in the trailing recovery is handed on, not corrected.** The rectangle's output is a
correctable deviation from the ideal — exactly the form the next rectangle's `IsRecovery` consumes.
This is the overlapping-rectangle convention stated rather than assumed away; that the resulting chain
closes is #97. -/
theorem deviatesBy_exRec_trailing {P : Matrix n n ℂ} {D : Set (Matrix n n ℂ → Matrix n n ℂ)}
    {R₁ R₂ ideal : Matrix n n ℂ → Matrix n n ℂ} (hid : id ∈ D)
    (hR₁ : IsRecovery P R₁ D) (hR₂ : DeviatesBy P D id R₂)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ)) :
    DeviatesBy P D ideal (exRec R₁ ideal R₂) := by
  intro ρ hρ
  obtain ⟨E, hED, hEq⟩ := hR₂ (ideal ρ) (hpres ρ hρ)
  refine ⟨E, hED, ?_⟩
  rw [exRec_apply, hR₁.apply_of_isCodeState hid hρ, hEq]
  simp only [id_eq]

/-! ### The payoff: #62 (d1) composes these with no restatement -/

/-- ★★★ **A circuit of good extended rectangles computes the ideal circuit's output.**
`correctedRun_eq_idealRun` applied verbatim: #62 (d1) left the step abstract, so a rectangle with a
faulty recovery drops straight in and the composition theorem needs no second proof. -/
theorem correctedRun_eq_idealRun_of_good_exRec {P : Matrix n n ℂ} {c : Circuit n}
    (hc : ∀ g ∈ c, IsCorrectedStep P g.1 g.2) {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) :
    correctedRun c ρ = idealRun c ρ :=
  correctedRun_eq_idealRun hc hρ

/-- ★★ **And a circuit of copies of one good extended rectangle.** -/
theorem correctedRun_replicate_exRec {P : Matrix n n ℂ}
    {D : Set (Matrix n n ℂ → Matrix n n ℂ)} {R₁ R₂ G ideal : Matrix n n ℂ → Matrix n n ℂ}
    (hid : id ∈ D) (hR₂ : IsRecovery P R₂ D) (hprop : PropagatesD P D ideal)
    (hpres : ∀ ρ, IsCodeState P ρ → IsCodeState P (ideal ρ))
    (hgood : (DeviatesBy P D id R₁ ∧ G = ideal) ∨ (IsRecovery P R₁ D ∧ DeviatesBy P D ideal G))
    (k : ℕ) {ρ : Matrix n n ℂ} (hρ : IsCodeState P ρ) :
    correctedRun (List.replicate k (ideal, exRec R₁ G R₂)) ρ
      = idealRun (List.replicate k (ideal, exRec R₁ G R₂)) ρ :=
  correctedRun_eq_idealRun
    (isCorrectedCircuit_replicate
      (g := ((ideal : Matrix n n ℂ → Matrix n n ℂ), exRec R₁ G R₂))
      (isCorrectedStep_exRec_of_good hid hR₂ hprop hpres hgood) k) hρ

end QuantumInfo

end

end
