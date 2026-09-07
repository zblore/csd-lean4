/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Darwinism
public import CsdLean4.RecordLayer.GlobalRecordClosure

/-!
# Empirical/CSD: record redundancy is agreement, not replication

**Category:** 3-Local (the CSD-side twin of `Empirical/QM/Darwinism.lean`).

Expert-review row **E** of `specs/BACKLOG.md`, CSD side. Scoped in
[`specs/quantum-darwinism-scoping.md`](../../../specs/quantum-darwinism-scoping.md) §5,
which is what this module is written against.

The QM side says a record is redundant when many environment fragments each hold a state
that identifies the outcome. Read naively into CSD that would be *replication*: many copies
of a classical bit, manufactured by decoherence, and objectivity grounded in how many there
are. **That is not CSD's account, and this module is what keeps the twin from reading as
though it were.**

In CSD there is one trajectory and one `Σ`-point. `globalOutcome c x` is the ontic selection
at that point — a function of the point and the context and, by `GlobalRecordClosure`
(CL-011), of nothing else. The fragments are extra *coordinates* of one configuration, and
the theorem is that they **agree**:

* `RecordStroke` — a record-writing stroke on the arena `Σ × (Fin k → outcome register)`: it
  leaves the ontic point where it is and ends with every register holding the outcome;
* ★ `RecordStroke.outcome_not_made` — such a stroke never *changes* the outcome. It records;
  it does not decide;
* ★★ `RecordStroke.registers_agree` — after the stroke every register reads the same thing.
  Redundancy, in the CSD vocabulary;
* ★★ `register_eq_of_same_point` — **the theorem §5 asks for.** Two registers agree even
  when they belong to *different strokes with different fragment counts*, provided the ontic
  point is the same. So the agreement does not come from the copying: it comes from there
  being one selection upstream of every register. Redundancy is a consequence of
  objectivity here, not its ground;
* ★ `RecordStroke.frozen_forces_prewritten` — the §4 vacuity test. A register the stroke
  never touches can satisfy the writing condition only if it *already* held the right
  outcome in every configuration, which is an assumption about the initial state and not a
  stroke doing anything;
* `copyStroke`, and ★ `copyStroke_zero_eq_id` — with **no fragments at all** the stroke is
  the identity, and `globalOutcome` is exactly as defined as it was. Definiteness owes
  nothing to redundancy, and this is the sharpest form of that.

## Honest scope

⚠️ **Frozen base.** `RecordStroke.base_fixed` says the stroke does not move the ontic point.
That is the fibrewise / frozen-base tier the corpus already knows (`pointerEvolve_fst`); a
back-reacting stroke would have to be an `IsJointLift` (`RecordLayer/JointLift.lean`) and the
statements here would need re-proving against `IsJointLift.pointer_eq` rather than a
projection. **Not done here.**

⚠️ **Kinematic, not dynamical.** Everything is pointwise. No measure on the fragment product
is built, nothing is proved measure-preserving, and no `a.e.` statement is made — so this is
*not* the measure-theoretic redundancy the scoping note's §3 costed. It is also why the
`k`-fold arena did not need to be a new species: with no invariance claim, the fragment
register is a plain product coordinate. ⚠️ The measure-theoretic version, and the question of
whether the fragment product preserves `μL`, is untouched.

⚠️ **No environment.** The registers are not physical environment fragments and nothing here
says an environment couples this way; which interaction is realised is `R-015`, a permanent
boundary. `copyStroke` is a witness that the class is inhabited, not a model of decoherence.

References: `specs/quantum-darwinism-scoping.md` §5; `CsdLean4/Empirical/QM/Darwinism.lean`
(the twin); `CsdLean4/RecordLayer/GlobalRecordClosure.lean` (`globalOutcome`, the ontic
selection, CL-011); `CsdLean4/RecordLayer/JointLift.lean` (the back-reacting tier this
module does not use).
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Darwinism

open CSD.RecordLayer

variable {N k : ℕ}

/-- The `k`-fragment arena: an ontic point of `Σ`, plus `k` registers each able to hold an
outcome. The registers are extra coordinates of one configuration — not copies of it. -/
abbrev FragmentArena (N k : ℕ) := LF4.KSigma N × (Fin k → Option (Fin N))

/-- **A record-writing stroke.** It leaves the ontic point alone and ends with every register
holding the outcome that point selects. -/
structure RecordStroke (N k : ℕ) (c : ContextField N) where
  /-- The action on the arena. -/
  act : FragmentArena N k → FragmentArena N k
  /-- ⚠️ **Frozen base**: the stroke does not move the ontic point (honest scope, above). -/
  base_fixed : ∀ y, (act y).1 = y.1
  /-- Every register ends holding the outcome selected at the ontic point. -/
  writes : ∀ (f : Fin k) (y : FragmentArena N k), (act y).2 f = globalOutcome c y.1

namespace RecordStroke

variable {c : ContextField N} (S : RecordStroke N k c)

/-- ★ **The stroke records; it does not decide.** The outcome after the stroke is the outcome
before it — a record-writing interaction cannot manufacture the selection it writes down. -/
theorem outcome_not_made (y : FragmentArena N k) :
    globalOutcome c (S.act y).1 = globalOutcome c y.1 := by
  rw [S.base_fixed y]

/-- ★★ **Redundancy.** After the stroke, every register reads the same outcome: consult any
fragment you like and you get the same answer. -/
theorem registers_agree (y : FragmentArena N k) (f g : Fin k) :
    (S.act y).2 f = (S.act y).2 g := by
  rw [S.writes f y, S.writes g y]

/-- Each register reads the ontic selection. -/
theorem register_eq_outcome (y : FragmentArena N k) (f : Fin k) :
    (S.act y).2 f = globalOutcome c y.1 :=
  S.writes f y

/-- ★ **The vacuity test** (`specs/quantum-darwinism-scoping.md` §4).

Suppose the stroke leaves register `f` exactly as it found it — the fragment the interaction
never touched. Then the writing condition forces every configuration to have arrived with
that register *already* holding the right outcome. That is a hypothesis about the initial
state, not a stroke doing work, and it is the sense in which `writes` is not free: it
excludes the untouched fragment unless the answer was written in advance. -/
theorem frozen_forces_prewritten {f : Fin k}
    (frozen : ∀ y : FragmentArena N k, (S.act y).2 f = y.2 f) (y : FragmentArena N k) :
    y.2 f = globalOutcome c y.1 := by
  rw [← frozen y, S.writes f y]

/-- The same, in refutation form: if two configurations agree on register `f` but select
different outcomes, no stroke that leaves `f` alone can be a `RecordStroke`. -/
theorem not_frozen_of_two_outcomes {f : Fin k} {y₁ y₂ : FragmentArena N k}
    (hreg : y₁.2 f = y₂.2 f)
    (hout : globalOutcome c y₁.1 ≠ globalOutcome c y₂.1)
    (frozen : ∀ y : FragmentArena N k, (S.act y).2 f = y.2 f) : False := by
  apply hout
  rw [← S.frozen_forces_prewritten frozen y₁, ← S.frozen_forces_prewritten frozen y₂, hreg]

end RecordStroke

/-- ★★ **The theorem the twin needs** (`specs/quantum-darwinism-scoping.md` §5).

Two registers hold the same value whenever the ontic point is the same — **even when they
belong to different strokes, with different numbers of fragments, started from different
register configurations**.

So the agreement between fragments is not produced by the copying. It is produced by there
being *one* selection at the point, which every register reads. In CSD the objectivity is
upstream of the redundancy; Darwinism's criterion is its operational twin, not its ground.
Read the other way round — redundancy as what makes a record objective — this theorem is
what the module denies. -/
theorem register_eq_of_same_point {k k' : ℕ} {c : ContextField N}
    (S : RecordStroke N k c) (S' : RecordStroke N k' c)
    (x : LF4.KSigma N) (r : Fin k → Option (Fin N)) (r' : Fin k' → Option (Fin N))
    (f : Fin k) (f' : Fin k') :
    (S.act (x, r)).2 f = (S'.act (x, r')).2 f' := by
  rw [S.writes f (x, r), S'.writes f' (x, r')]

/-! ### The witness -/

/-- The stroke that writes the outcome into every register. -/
noncomputable def copyStroke (k : ℕ) (c : ContextField N) : RecordStroke N k c where
  act := fun y => (y.1, fun _ => globalOutcome c y.1)
  base_fixed := fun _ => rfl
  writes := fun _ _ => rfl

/-- ★ **No redundancy at all, and the record is untouched.**

With zero fragments the stroke is the identity: there is nothing to copy the outcome into.
`globalOutcome c y.1` is exactly as defined as it ever was. Whatever makes a CSD record
definite, it is not the number of fragments that hold it — which is `register_eq_of_same_point`
seen from the other end. -/
theorem copyStroke_zero_eq_id (c : ContextField N) (y : FragmentArena N 0) :
    (copyStroke 0 c).act y = y := by
  refine Prod.ext rfl ?_
  funext f
  exact absurd f.2 (by omega)

end Darwinism
end CSDBridge
end Empirical
end CSD
