/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.OperationalNoSignalling

/-!
# Empirical/CSD: Local Friendliness — which assumption CSD denies, at the friend level

**Category:** 3-Local (CSD-side; the Local Friendliness row, `specs/BACKLOG.md` row C /
`qm-empirical-tests.md` D12).

Local Friendliness (Bong et al. 2020) derives a bound from three assumptions — Absoluteness of
Observed Events, Locality, and No-Superdeterminism — which quantum mechanics violates. The row
asks which one CSD denies, **as a theorem**.

The answer is not any of the three as usually listed. It is a **fourth thing the derivation uses
tacitly**: that the friends' records, once made, are *fixed* — that what the friend recorded is a
function of the microstate alone, unchanged by whatever the party does next. This module isolates
that assumption and shows it is what carries the Locality step.

## The statement

`FriendRecords` reads the two friends' outcomes **in a given measurement context**, because that
is what the LF protocol actually does: in one setting the party opens the lab and asks, in another
the party applies a coherent operation to the whole lab and asks something else. Then

* `Persistent` — the reading does not depend on the context: what the friends recorded is a
  function of the microstate alone;
* `JointLawInvariant` — the *joint law* of the two friends' outcomes is the same in every
  context. This is LF's Locality at the friend level, in its working form
  `p(a₁b₁|xy) = p(a₁b₁)`;
* ★ `jointLawInvariant_of_persistent` — **persistence forces it**. So in a single-`Σ`,
  single-`μ` model, fixed friend records *give you* LF Locality; you do not get to keep the first
  and deny the second.

Hence the elimination: a model that reproduces the quantum violation must deny persistence. ★★
`not_persistent_of_jointLaw_moves` is that contrapositive, and ★ `movingRecords_not_persistent`
exhibits a scenario where the joint law genuinely moves, so the implication is not vacuous.

## ⚠️ What CSD denies, and what it keeps

**CSD keeps Absoluteness of Observed Events.** A record is an ontic selection in `Σ`: at each
moment the friend's outcome is a definite fact about the trajectory, not something relative to an
observer. Nothing here touches that.

**CSD denies persistence.** In `Σ` there is one trajectory and it moves forward. The party's
coherent setting is not a time reversal — it is an apparatus applied, a *forward* interaction
whose effect on the Hilbert data is some unitary, and `U†` is a unitary like any other. The
trajectory moves forward into a configuration in which the friend's record is no longer what it
was. The record was absolute when it existed and is absolute now; it is not the *same* record.

That distinction — **definite at every moment, not invariant across the party's operation** — is
the whole of CSD's position on Local Friendliness, and `jointLawInvariant_of_persistent` is why
it is the assumption that has to give.

⚠️ **This is not superdeterminism and not retrocausality.** Persistence fails going *forward*:
nothing propagates backwards, and no correlation between settings and the initial microstate is
posited. Measurement independence is kept, exactly as in `specs/colbeck-renner-note.md`.

## ⚠️ Honest scope

* **No LF inequality is proved here**, and no violation is derived. The elimination is a
  conditional: *if* the joint law moves, persistence fails. Whether the CSD record layer's joint
  law moves is not shown — that needs the friends' labs modelled, which the corpus does not have.
* **The availability of the coherent branch rests on a posit.** That every unitary is realisable
  as a measure-preserving, `π`-equivariant `Σ`-flow is carried as *data*, not derived —
  `CSDUnitaryBundle` (`Empirical/CSD/Gates/Framework.lean`) holds `U` and `U_isometry` and nothing
  `Σ`-side, as `PLACEHOLDERS.md` §7 records. CSD's answer to LF stands on the same posit the gates
  layer stands on.
* **Three different statements are called "locality" in this corpus's neighbourhood** and this is
  the third. `specs/local-friendliness-scoping.md` §2 has the table; the short form is that
  operational no-signalling (`LF3/SettingLocality.lean`) is a *marginal* statement, Bell parameter
  independence (`LF6.no_product_partition_realises_singlet`) is about a factorisation through a
  hidden variable, and this one is a *joint* statement about records. Denying this one does not
  touch either of those.

## References

`specs/local-friendliness-scoping.md` (the scoping note, `csd-foundations`-checked; §2 the three
localities, §3 why the coherent branch is forward evolution rather than reversal);
`specs/BACKLOG.md` row C; `specs/qm-empirical-tests.md` D12;
`CsdLean4/LF3/OperationalNoSignalling.lean` (the marginal statement, and measurement independence
as a stated premise); `CsdLean4/LF6/ForcedContextuality.lean`
(`no_product_partition_realises_singlet`); `CsdLean4/Empirical/CSD/EraserSequential.lean`
(`sequential_no_revival` — about a later *measurement*, not about a forward unitary);
`specs/colbeck-renner-note.md`. Source: Bong et al., *Nature Physics* **16**, 1199 (2020).
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace LocalFriendliness

open CSD.LF3

variable {Sigma : Type*} [MeasurableSpace Sigma]

/-! ### The friends' records, as read in a context -/

/-- **The two friends' recorded outcomes, read in a measurement context.**

The context argument is the point. In the Local Friendliness protocol a party either opens the
lab and asks the friend, or applies a coherent operation to the whole lab; those are different
contexts, and whether the friend's record is the same object in both is precisely the assumption
under test. A structure that made `read` a bare function of `Sigma` would assume the answer. -/
structure FriendRecords (Sigma : Type*) where
  /-- The friends' joint outcome as read in a given context. -/
  read : MeasurementContext → Sigma → Sign × Sign

namespace FriendRecords

variable (R : FriendRecords Sigma)

/-- **Persistence**: what the friends recorded is a function of the microstate alone, unchanged
by which context the party goes on to realise.

This is the assumption the LF derivation uses tacitly, and the one CSD denies. It is **not**
Absoluteness of Observed Events: absoluteness says the outcome is a definite fact rather than an
observer-relative one, which CSD keeps. Persistence says something stronger — that the fact is
*invariant under what the party does next*. -/
def Persistent : Prop := ∀ C C' l, R.read C l = R.read C' l

/-- **LF Locality at the friend level**: the joint law of the two friends' outcomes is the same
in every context — the working form of `p(a₁b₁|xy) = p(a₁b₁)`.

A **joint** statement, not a marginal one. Operational no-signalling
(`LF3.OperationalNoSignalling`) constrains each wing's marginal separately and does not imply
this; that is why the two can be held apart, and why CSD proves the one and denies the other. -/
def JointLawInvariant (μ : Measure Sigma) : Prop :=
  ∀ (C C' : MeasurementContext) (st : Sign × Sign),
    μ {l | R.read C l = st} = μ {l | R.read C' l = st}

end FriendRecords

/-! ### Persistence forces LF Locality -/

/-- ★ **Fixed records give LF Locality for free.**

If the friends' records do not depend on the context, the sets `{l | read C l = st}` are literally
the same set in every context, so their measures agree. On a single `Σ` with a single `μ` there is
no room between "the record is a function of the microstate" and "the joint law is
setting-independent".

This is the step the LF derivation needs and the reason the three named assumptions cannot simply
be traded off against each other in a `Σ`-model: persistence *is* a locality assumption in
disguise, once the state space is shared. -/
theorem jointLawInvariant_of_persistent (R : FriendRecords Sigma) (μ : Measure Sigma)
    (h : R.Persistent) : R.JointLawInvariant μ := by
  intro C C' st
  have : {l | R.read C l = st} = {l | R.read C' l = st} := by
    ext l
    simp only [Set.mem_ofPred_eq, h C C' l]
  rw [this]

/-- ★★ **The elimination.** A model whose friends' joint law moves with the context does not have
persistent records — whatever else it keeps.

This is CSD's position on Local Friendliness, in the only form the corpus can state without
modelling the friends' labs: the quantum violation requires the joint law to move, so persistence
is what has to go. Absoluteness of Observed Events, measurement independence and operational
no-signalling are all untouched by it. -/
theorem not_persistent_of_jointLaw_moves (R : FriendRecords Sigma) (μ : Measure Sigma)
    (h : ¬ R.JointLawInvariant μ) : ¬ R.Persistent :=
  fun hp => h (jointLawInvariant_of_persistent R μ hp)

/-! ### Non-vacuity: records whose joint law genuinely moves -/

/-- A scenario in which the friends' reading depends on the party's setting: the A-friend's
record is `f C.a l`, so a party who changes setting reads a different record off the same
microstate. This is the shape CSD's forward-evolution answer has — the record is definite at
every moment and is not the same record after the party's operation. -/
def movingRecords (f : DetectorSetting → Sigma → Sign) (t : Sign) : FriendRecords Sigma where
  read := fun C l => (f C.a l, t)

omit [MeasurableSpace Sigma] in
/-- ★ **The implication is not vacuous**: moving records really do fail persistence, as soon as
two settings read the same microstate differently. Together with
`jointLawInvariant_of_persistent` this pins the direction — persistence is strictly stronger than
nothing, and it is exactly what a context-dependent record gives up. -/
theorem movingRecords_not_persistent (f : DetectorSetting → Sigma → Sign) (t : Sign)
    {a a' : DetectorSetting} {l : Sigma} (h : f a l ≠ f a' l) :
    ¬ (movingRecords f t).Persistent := by
  intro hp
  exact h (congrArg Prod.fst (hp ⟨a, a⟩ ⟨a', a⟩ l))

end LocalFriendliness
end CSDBridge
end Empirical
end CSD
