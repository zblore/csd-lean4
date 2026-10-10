/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.RecordInfluence

/-!
# The two-wing coupling graph: causal separation at every period count

**Category:** 3-Local (CV; the causal shape of the two-wing experiment).
BACKLOG #131, obligation **(3)** — the causal-separation half.

[`RecordInfluence.lean`](RecordInfluence.lean) states the record cone for an *arbitrary* coupling
graph `E`. #131's experiment supplies a particular one: four modes — each wing's system and its own
pointer — with **no A–B edge**, which is the sense in which the two wings are spacelike. This module
instantiates the cone machinery there and reads off what the row needs.

## The one fact everything follows from

`graphNeighborhood twoWingGraph wingAModes = wingAModes`: A's mode set is **closed** under the
graph's one-step neighbourhood, because the only edge touching it has both endpoints inside it. So
`graphBall twoWingGraph wingAModes n = wingAModes` for **every** `n` — A's cone never grows — and the
same for B. Causal separation is therefore not a bound that degrades with time:

* ★★★ `spacelike_twoWing` — the two wings are `Spacelike` at **every** period count, so every
  theorem of `RecordInfluence.lean` applies at every `n` with no budget to track;
* ★ `not_eventuallyInfluences_twoWing` — neither wing *ever* influences the other, in the graded
  relation's existential form;
* ★★★ `commute_record_twoWing` — the two wings' evolved observables commute at every `n`, so **the
  record layer may assign both wings outcomes at once**. This is what a two-wing experiment needs in
  order to *have* a joint outcome, and `TwoWingCoarsening`'s joint events are what it licenses;
* ★★★ `arenaObs_kick_twoWing` and ★★★ `recordStroke_comm_kick_twoWing` — **a B-wing intervention
  cannot steer A's reading or A's record write, exactly and at every period count.** No
  Lieb–Robinson error term: the evolved observable's support stays inside A's cone on the nose.

## Non-vacuity

The theorems are stated for any wing-supported observable and any wing-supported unitary, so they
would be empty if the wing algebras were trivial. They are not: ★ `supportedOn_wingAModes_modeOp`
gives every single-mode operator at A's system mode, ★ `supportedOn_wingBModes_phaseDiagU` gives a
diagonal phase unitary reading B's system mode only, and
★ `recordStroke_comm_kick_twoWing_witness` is the unsteerability statement at that explicit pair.

## Honest scope

⚠️ **The graph is supplied, as #131 intends.** `twoWingGraph` is a *modelling choice* — the
adjacency is put in by hand, not derived. Nothing here shows that spatial separation *emerges*; that
is `C-1`, and #131 says explicitly that it would not be established even with all five obligations
met. Read `twoWingGraph` as "the experiment's layout".

⚠️ **This is `Influences`, which is *permitted* influence.** Everything proved is of the form
*outside the cone ⇒ nothing happens*. The converse is not proved and is not true in general; see
`RecordInfluence.lean`'s own scope note.

⚠️ **This is the CV arena, not yet `LF4.KSigma`.** The statements live on
`FibredFieldArena 4 2`, whose fibre **is** `LF4.KTorus` (the same type, no transport needed) but
whose base is `ℙ ℂ (EuclideanSpace ℂ (FieldConfig 4 2))` rather than `CPN 16`. Those two bases are
the same space up to the index equivalence `FieldConfig 4 2 ≃ Fin 16`, and carrying these statements
across it is **not** the thin transport the audit expected: `dmVec`, `arenaObs`, `arenaKick` and
`SupportedOn` are all indexed by `FieldConfig K N` specifically, so the carry needs the CV arena API
generalised over its index type — which `CompositeArena.lean` already records as owed. That is
BACKLOG row 133 and it is not done here.

⚠️ **And the record-layer statement is about a different object.** The theorems here are about
a **wing-local observable** on the field arena. The record layer's wing reading is not one: under
option I1 it is a *coarsening of a joint code* — `globalBasin` reads the base through
`ContextField.rate`, and `momentContext`'s rate is the moment map in the configuration basis, a
reading of the **whole** configuration rather than of either wing. So the record-layer counterpart of
unsteerability is the *marginal* statement
(`LF6.toReal_measure_preimage_wingAEvent_eq_of_setting`), not this one, and the two are not the same
theorem. A record coordinate that is genuinely **wing-local** — a `ContextField` whose rates are a
wing-supported observable — is what would let this file's theorems be read as statements about
*records*; there is none, and building one is BACKLOG row 134 (and it bears on row 132, since under
I1 the two wings share one selector).

⚠️ Discrete periods of the fixed interacting unitary `graphInteractingU`, at the finite cutoff
`K = 4`, `N = 2`.

References: [`RecordInfluence.lean`](RecordInfluence.lean) (`Influences`, `Spacelike`,
`commute_record_of_spacelike`, `arenaObs_heisenberg_kick_of_spacelike`,
`recordStroke_heisenberg_comm_kick_of_spacelike`), [`SupportSpreading.lean`](SupportSpreading.lean)
(`graphBall`, `graphNeighborhood`, `phaseDiagU_supportedOn`),
[`ModeLocality.lean`](ModeLocality.lean) (`SupportedOn`, `modeOp_supportedOn`),
[`LocalAlgebra.lean`](LocalAlgebra.lean) (`SupportedOn.mono`),
[`FibredArenaBridge.lean`](FibredArenaBridge.lean) (`recordStroke`, `fibredKick`);
`specs/BACKLOG.md` #131 obligation (3), #133, #134;
`specs/two-wing-experiment-scoping.md` §3 and §6.
-/

@[expose] public section

open Matrix

noncomputable section

namespace CSD.CV

/-! ### The experiment's layout -/

/-- **A's modes**: A's system and A's pointer. -/
def wingAModes : Finset (Fin 4) := {0, 1}

/-- **B's modes**: B's system and B's pointer. -/
def wingBModes : Finset (Fin 4) := {2, 3}

/-- **The two-wing coupling graph**: each wing's system couples to its own pointer, and there is
**no A–B edge**. This is the adjacency #131 supplies — a modelling choice, the experiment's layout,
not something derived. -/
def twoWingGraph : Finset (Fin 4 × Fin 4) := {(0, 1), (2, 3)}

theorem disjoint_wingModes : Disjoint wingAModes wingBModes := by decide

theorem wingAModes_nonempty : wingAModes.Nonempty := by decide

theorem wingBModes_nonempty : wingBModes.Nonempty := by decide

/-! ### The cones never grow -/

/-- **A's mode set is closed under the graph's one-step neighbourhood**: the only edge touching it
has both endpoints inside it. Everything in this file follows from this and its mirror. -/
theorem graphNeighborhood_wingAModes :
    graphNeighborhood twoWingGraph wingAModes = wingAModes := by decide

theorem graphNeighborhood_wingBModes :
    graphNeighborhood twoWingGraph wingBModes = wingBModes := by decide

/-- ★★ **A's cone never grows.** -/
theorem graphBall_wingAModes (n : ℕ) :
    graphBall twoWingGraph wingAModes n = wingAModes := by
  induction n with
  | zero => rfl
  | succ n ih => rw [graphBall_succ, ih, graphNeighborhood_wingAModes]

/-- ★★ **B's cone never grows.** -/
theorem graphBall_wingBModes (n : ℕ) :
    graphBall twoWingGraph wingBModes n = wingBModes := by
  induction n with
  | zero => rfl
  | succ n ih => rw [graphBall_succ, ih, graphNeighborhood_wingBModes]

/-- ★★★ **The two wings are spacelike at every period count.** Causal separation here is not a
bound that degrades with time: because the graph has no A–B edge, neither cone ever reaches the
other, however long the interaction runs. -/
theorem spacelike_twoWing (n : ℕ) : Spacelike twoWingGraph wingAModes wingBModes n := by
  rw [Spacelike, graphBall_wingAModes, graphBall_wingBModes]
  exact disjoint_wingModes

/-- ★ **Neither wing influences the other within any budget.** -/
theorem not_influences_twoWing (n : ℕ) :
    ¬Influences twoWingGraph wingAModes wingBModes n :=
  not_influences_of_spacelike (spacelike_twoWing n) wingBModes_nonempty

/-- ★ **Neither wing *ever* influences the other**, in the existential form that is a genuine
preorder. -/
theorem not_eventuallyInfluences_twoWing :
    ¬EventuallyInfluences twoWingGraph wingAModes wingBModes := by
  rintro ⟨n, hn⟩
  exact not_influences_twoWing n hn

/-! ### What that buys the experiment -/

variable (τ lam : ℝ) (gc : Fin 4 × Fin 4 → Fin 2 → Fin 2 → ℝ)

/-- ★★★ **The two wings are jointly measurable, at every period count.** Their evolved observables
commute, so the record layer may assign both wings outcomes at once — which is what a two-wing
experiment needs in order to *have* a joint outcome at all. -/
theorem commute_record_twoWing
    {A B : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ}
    (hA : SupportedOn wingAModes A) (hB : SupportedOn wingBModes B) (n : ℕ) :
    heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A
        * heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) B
      = heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) B
        * heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A :=
  commute_record_of_spacelike τ lam twoWingGraph gc n (spacelike_twoWing n) hA hB

/-- ★★★ **A B-wing intervention cannot steer A's reading — exactly.** No Lieb–Robinson error term:
after any number of interacting periods the evolved A-observable's support is still inside A's cone,
which is A's own modes. -/
theorem arenaObs_kick_twoWing
    {A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ} (hA : SupportedOn wingAModes A)
    {W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ} (hW : SupportedOn wingBModes W.val)
    (n : ℕ) (p : FieldArena 4 2) :
    arenaObs (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) (arenaKick W p)
      = arenaObs (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) p :=
  arenaObs_heisenberg_kick_of_spacelike τ lam twoWingGraph gc n (spacelike_twoWing n) hA hW p

/-- ★★★ **A B-wing intervention cannot steer A's record write — exactly.** Kick B's modes and write
A's record, or write it and then kick: the same point of the fibred arena, at every period count.
This is the unsteerability statement #131's obligation (3) asks for. -/
theorem recordStroke_comm_kick_twoWing
    {A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ} (hA : SupportedOn wingAModes A)
    {W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ} (hW : SupportedOn wingBModes W.val)
    (n : ℕ) (g : ℝ → RecordFibre) (x : FibredFieldArena 4 2) :
    recordStroke (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) g
        (fibredKick W x)
      = fibredKick W
        (recordStroke (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) g x) :=
  recordStroke_heisenberg_comm_kick_of_spacelike τ lam twoWingGraph gc n (spacelike_twoWing n)
    hA hW g x

/-! ### Non-vacuity: the wing algebras are inhabited -/

/-- ★ **An explicit A-wing observable**: any single-mode operator at A's system mode. -/
theorem supportedOn_wingAModes_modeOp (a : Matrix (Fin 2) (Fin 2) ℂ) :
    SupportedOn wingAModes (modeOp (0 : Fin 4) a) :=
  (modeOp_supportedOn (0 : Fin 4) a).mono (by decide)

/-- ★ **An explicit B-wing unitary**: a diagonal phase reading B's system mode only. -/
theorem supportedOn_wingBModes_phaseDiagU (f : Fin 2 → ℝ) :
    SupportedOn wingBModes (phaseDiagU (fun c : FieldConfig 4 2 => f (c 2))).val :=
  phaseDiagU_supportedOn fun c c' h => by rw [h 2 (by decide)]

/-- ★ **Unsteerability at an explicit pair**, so the statement above is not vacuous: a phase kick on
B's system mode leaves A's record write at A's system mode exactly unchanged, at every period
count. -/
theorem recordStroke_comm_kick_twoWing_witness (a : Matrix (Fin 2) (Fin 2) ℂ) (f : Fin 2 → ℝ)
    (n : ℕ) (g : ℝ → RecordFibre) (x : FibredFieldArena 4 2) :
    recordStroke
        (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) (modeOp (0 : Fin 4) a)) g
        (fibredKick (phaseDiagU fun c : FieldConfig 4 2 => f (c 2)) x)
      = fibredKick (phaseDiagU fun c : FieldConfig 4 2 => f (c 2))
        (recordStroke
          (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) (modeOp (0 : Fin 4) a)) g
          x) :=
  recordStroke_comm_kick_twoWing τ lam gc (supportedOn_wingAModes_modeOp a)
    (supportedOn_wingBModes_phaseDiagU f) n g x

end CSD.CV

end

end
