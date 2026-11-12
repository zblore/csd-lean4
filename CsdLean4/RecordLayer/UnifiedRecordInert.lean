/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PointerInert
public import CsdLean4.RecordLayer.UnifiedClockMessenger

/-!
# The flow commutes with turning the pointers: nothing else depends on where one started

**Category:** 7-SigmaLayer (the record layer). BACKLOG #374 — the author's programme "From `Σ` to
physical spacetime", obligations UO-14 (b), UO-16 and UO-24; Remainder (a) of #372.

#372 put a clock on its own carrier beside the messenger and left the clock's count aligned with
the messenger's records only by the flow parameter. The next brick was to be a coupling of the
clock to the departure detector, so that a count belongs to a record. That coupling is not
built. This module gives what is proved in its place, on this arena, from the closed forms of
the two factors. `LF4/PointerInert.lean` has the same statement for one step and the pointer
that the step adds; this module does not use it, and the two halves are independent. The
statements are mathematically small. A moving angle is a cyclic coordinate.

A readout is a region of a pointer's **moving angle** (UA-4). The joint energy of this arena
(UA-16 (c), with UA-13 (c) for the messenger's two pointers and UA-12 / UA-5 for the clock's)
does not contain any moving angle. So the flow commutes with turning the pointers:

* `shiftPointers a b c` — turn the departure pointer by `a`, the arrival pointer by `b` and the
  clock's tick pointer by `c`;
* ★★ `clockMessengerFlow_shiftPointers` — **the joint flow commutes with `shiftPointers`**;
* `forgetMoving` — the arena state with the three moving angles left out: the two carriers and
  the three conserved angles;
* ★ `forgetMoving_clockMessengerFlow_congr` — **two starts that differ only in the moving
  angles have the same carriers and conserved angles at every time**;
* `clockMessengerFlow_shiftFst_snd`, `clockMessengerFlow_shiftFst_arrival` — turning the
  departure pointer (`shiftPointers a 0 0`) changes neither the clock's state nor the arrival
  pointer's, at any time. The first is weaker than #372's `clockMessengerFlow_snd`.

So, with the carriers and conserved angles held fixed, two starts that differ only in where the
departure pointer begins have the same clock history, the same carriers and the same arrival
pointer. Nothing but a pointer's own angle depends on where that pointer started. No other
degree of freedom tells two such runs apart, whether or not the readout comes to be displayed
in one and not in the other. Such a pair is not exhibited in Lean.

## Exact scope

* **About the energy's form.** The statement is a consequence of the moving angles being absent
  from the joint energy, which is assumed. It is an obstruction for that form, not for `Σ`.
* **This arena only.** It is proved for `clockMessengerFlow`. The same commutation is expected
  on the other arenas of UA-13 and on the arena of UA-15; it is not stated in Lean for them.
* **What it rules out**: a degree of freedom, other than the pointer itself, whose later value
  depends on where a pointer started, the carriers and conserved angles being the same.
* **What it does not rule out.** (i) A dependence through the occupancy that drives a pointer:
  a second degree of freedom driven by the same accumulated occupancy varies with the readout
  through that common cause. So "no register can hold the count at a record" does not follow
  from this module; nor does it follow with #358's `not_ae_count_advances_clockPointerFlow`,
  which is for measurable real functions and leaves an angle-valued register open. (ii) A
  pointer whose moving angle acts back (UO-24): not in the corpus. (iii) A pointer whose *rate*
  depends on the messenger and the clock together, such as the expectation of a product
  observable on a composite carrier: its displacement is a joint functional of both histories.
  That does not remove the obstruction. Its pointer is again cyclic, and it responds to the
  carriers and not to a record.
* **A term between the clock and a detector** of the kind of #212 (the clock's carrier detuned
  by a detector's conserved angle, and driving that detector's pointer) leaves every moving
  angle out of the energy, so the same commutation is expected. That is a calculation and not
  in Lean: the energy of #212 has two terms in one conserved angle and is not a `stepEnergy`,
  so `hamiltonianFlow_stepEnergy_shiftMoving` does not apply to it as stated. It is not built.
* **The statement is for the uncoupled energy of #372**, where the clock's independence of the
  messenger is already #372's.
* **No measure and no probability.** The statements are pointwise.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-13,
UA-15, UA-16, UO-14, UO-16, UO-24, UD-106, UD-107); `LF4/PointerInert.lean`
(`hamiltonianFlow_stepEnergy_shiftMoving`: the generic statement for one step);
`RecordLayer/UnifiedClockMessenger.lean` (`clockMessengerFlow`, `clockMessengerFlow_apply`);
`RecordLayer/UnifiedDepartureArrival.lean` (`regionTwoFlow_apply`);
`RecordLayer/UnifiedDiracClock.lean` (`clockPointerFlow_apply`);
`RecordLayer/UnifiedDiracClockTicks.lean` (`not_ae_count_advances_clockPointerFlow`: no function
of the state holds the count); `RecordLayer/ClockEchoCoupling.lean` (#212).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.RecordLayer

section Inert

variable {N K : ℕ}

/-- Turn the first pointer by `a`, the second by `b` and the pointer of the second factor by
`c`. -/
def shiftPointers (a b c : AddCircle (1 : ℝ)) (z : CrossSigma N K) : CrossSigma N K :=
  (((z.1.1.1, (z.1.1.2.1 + a, z.1.1.2.2)), (z.1.2.1 + b, z.1.2.2)),
    (z.2.1, (z.2.2.1 + c, z.2.2.2)))

/-- The arena state with the three moving angles left out: the two carriers and the three
conserved angles. -/
def forgetMoving (z : CrossSigma N K) :
    (CPN (N + 1) × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × (CPN (K + 1) × AddCircle (1 : ℝ)) :=
  ((z.1.1.1, z.1.1.2.2, z.1.2.2), (z.2.1, z.2.2.2))

/-- Two states with the same carriers and conserved angles differ by a turn of the pointers. -/
theorem exists_shiftPointers_of_forgetMoving_eq {z z' : CrossSigma N K}
    (h : forgetMoving z = forgetMoving z') : ∃ a b c, z' = shiftPointers a b c z := by
  obtain ⟨⟨⟨x, θ₁, θ₂⟩, ψ₁, ψ₂⟩, y, χ₁, χ₂⟩ := z
  obtain ⟨⟨⟨x', θ₁', θ₂'⟩, ψ₁', ψ₂'⟩, y', χ₁', χ₂'⟩ := z'
  simp only [forgetMoving, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
  exact ⟨θ₁' - θ₁, ψ₁' - ψ₁, χ₁' - χ₁, by simp [shiftPointers]⟩

/-- Turning the pointers does not change the carriers or the conserved angles. -/
theorem forgetMoving_shiftPointers (a b c : AddCircle (1 : ℝ)) (z : CrossSigma N K) :
    forgetMoving (shiftPointers a b c z) = forgetMoving z := rfl

end Inert

section Arena

variable {M Mc : ℕ} {f h fc : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ gc : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hfc : Function.Periodic fc 1)

/-- ★★ **The joint flow commutes with turning the pointers** (UA-16 (c), UA-13 (c)). On the
arena of a messenger with
two region pointers beside a clock device with its tick pointer: starting the three pointers
`a`, `b`, `c` further round leaves them `a`, `b`, `c` further round at every time and changes
nothing else. -/
theorem clockMessengerFlow_shiftPointers (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (a b c : AddCircle (1 : ℝ))
    (z : CrossSigma (2 * M + 1) (4 * Mc + 3)) :
    clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t
        (shiftPointers a b c z)
      = shiftPointers a b c
        (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z) := by
  obtain ⟨⟨⟨x, θ⟩, ψ⟩, y, χ⟩ := z
  obtain ⟨p, rfl⟩ := (idxArenaEquiv (diracIdx M)).surjective x
  obtain ⟨q, rfl⟩ := (clockArenaEquiv Mc).surjective y
  have e : shiftPointers a b c
      ((((idxArenaEquiv (diracIdx M)) p, θ), ψ), (clockArenaEquiv Mc) q, χ)
      = ((((idxArenaEquiv (diracIdx M)) p, (θ.1 + a, θ.2)), (ψ.1 + b, ψ.2)),
        (clockArenaEquiv Mc) q, (χ.1 + c, χ.2)) := rfl
  rw [e, clockMessengerFlow_apply, clockMessengerFlow_apply,
    regionTwoFlow_apply J μ g₁ g₂ A B hf hh hc hch t p (θ.1 + a, θ.2) (ψ.1 + b, ψ.2),
    regionTwoFlow_apply J μ g₁ g₂ A B hf hh hc hch t p θ ψ,
    clockPointerFlow_apply Jc μ₀ μ₁ gc hfc hcc t q (χ.1 + c, χ.2),
    clockPointerFlow_apply Jc μ₀ μ₁ gc hfc hcc t q χ]
  simp only [shiftPointers, add_right_comm]

/-- ★ **Two starts that differ only in the moving angles have the same carriers and conserved
angles at every time** (UA-16 (c), UA-13 (c)). -/
theorem forgetMoving_clockMessengerFlow_congr (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) {z z' : CrossSigma (2 * M + 1) (4 * Mc + 3)}
    (hz : forgetMoving z = forgetMoving z') :
    forgetMoving (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z)
      = forgetMoving
        (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z') := by
  obtain ⟨a, b, c, rfl⟩ := exists_shiftPointers_of_forgetMoving_eq hz
  rw [clockMessengerFlow_shiftPointers, forgetMoving_shiftPointers]

/-- **The clock does not see where the departure pointer is**: turning the departure pointer
leaves the clock's whole state, tick pointer included, as it was at every time. Weaker than
`clockMessengerFlow_snd`. -/
theorem clockMessengerFlow_shiftFst_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (a : AddCircle (1 : ℝ))
    (z : CrossSigma (2 * M + 1) (4 * Mc + 3)) :
    (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t
        (shiftPointers a 0 0 z)).2
      = (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z).2 := by
  rw [clockMessengerFlow_shiftPointers]
  simp [shiftPointers]

/-- **The arrival pointer does not see where the departure pointer is.** -/
theorem clockMessengerFlow_shiftFst_arrival (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (a : AddCircle (1 : ℝ))
    (z : CrossSigma (2 * M + 1) (4 * Mc + 3)) :
    (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t
        (shiftPointers a 0 0 z)).1.2
      = (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z).1.2 := by
  rw [clockMessengerFlow_shiftPointers]
  simp [shiftPointers]

end Arena

end CSD.RecordLayer

end
