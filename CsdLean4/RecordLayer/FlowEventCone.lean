/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GraphCone

/-!
# Events at flow times, and what the graph permits between them

**Category:** 7-SigmaLayer. BACKLOG #442, first brick (Task 4 of the author's plan "Unified
records, quantum measurement and emergent spacetime", the causal bridge;
`specs/unified-records-spacetime-task-plans.md` §2; the author's decision of 2026-11-19:
the events keep their real flow times and the graph relation is stated for them directly,
with no map to whole periods).

`CV/RecordCausalOrder.lean` orders events whose time is a number of periods. The radar's
readings are at real flow times. This module states the graph relation for an event with a
real time, with no rounding.

* `FlowEvent` — a set of sites and a flow time;
* `HopSeparated adj d X Y` — `d` steps of growth from `X` miss `Y`;
* `disjoint_growG_comm`, `growIterG_growG`, `growIterG_add`, ★★ `hopSeparated_comm` — the
  separation is symmetric, and growth composes;
* `FlowEvent.PermittedWithin adj d e₁ e₂` — `e₁` is not later than `e₂` and the two regions
  are within `d` hops: what the graph permits. A statement about the graph and the two
  times; it derives neither;
* ★★★ `FlowEvent.kick_response_le` — *permitted against demonstrated*: for a carrier moving
  by `exp (u S)` with `S` hopping along the graph, a kick on the region of `e₁` at its time
  changes an observable on the region of `e₂`, read at its time, by at most
  `2 (2 ‖S‖ (t₂ − t₁))^d / d! · ‖D‖` when the regions are `d` hops apart;
* ★★ `FlowEvent.kick_response_eq_of_time_eq` — at equal times and `d ≥ 1` the response is
  zero.

## Honest scope

⚠️ **Three notions, kept apart.** `PermittedWithin` is the graph's relation.
`kick_response_le` bounds a response from above; it demonstrates no influence. The order of
the two flow times is a hypothesis of both and is the order of the flow parameter, which is
not a record (UA-7).

⚠️ **No sharp cone.** With real times and a continuous flow the bound is a factorial tail in
the hop distance, not a region outside which the response vanishes (except at equal times).
No speed is chosen and no relation "inside the cone" is defined from one.

⚠️ **The graph is assumed.** That `S` hops along `adj` is a hypothesis; the order of events
does not derive the graph. Hop distance counts links and is not a metric of spacetime.

⚠️ **Not the radar.** The five readings of the radar are not yet stated as `FlowEvent`s with
their gate regions, and the kick here is on the carrier, not a pointer's record.

References: `specs/BACKLOG.md` #442; `specs/unified-record-spacetime-plan.md` (UA-7, UD-230,
UD-239); `specs/unified-records-spacetime-task-plans.md` (§2);
`RecordLayer/GraphCone.lean` (`growIterG`, `abs_arenaObs_flow_kick_sub_graph_le`);
`CV/RecordCausalOrder.lean` (`RecordEvent`, `CausalPrecedes`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.RecordLayer

section Graph

variable {V n : Type*}

/-- **An event at a flow time**: a set of sites and a real time of the flow. -/
structure FlowEvent (V : Type*) where
  /-- The sites the event reads or acts on. -/
  region : Set V
  /-- The flow time of the event. -/
  time : ℝ

/-- **`d` hops apart**: `d` steps of growth from `X` miss `Y`. -/
def HopSeparated (adj : V → V → Prop) (d : ℕ) (X Y : Set V) : Prop :=
  Disjoint (growIterG adj X d) Y

theorem HopSeparated.mono {adj : V → V → Prop} {X Y : Set V} {j d : ℕ} (h : j ≤ d)
    (hd : HopSeparated adj d X Y) : HopSeparated adj j X Y :=
  Set.disjoint_of_subset_left (growIterG_mono adj X h) hd

/-- One step of growth can be moved from one side of a disjointness to the other. -/
theorem disjoint_growG_comm (adj : V → V → Prop) (A B : Set V) :
    Disjoint (growG adj A) B ↔ Disjoint A (growG adj B) := by
  have key : ∀ A B : Set V, Disjoint (growG adj A) B → Disjoint A (growG adj B) := by
    intro A B h
    rw [Set.disjoint_left] at h ⊢
    rintro x hxA (hxB | ⟨b, hbB, hadj⟩)
    · exact h (subset_growG adj A hxA) hxB
    · exact h (Or.inr ⟨x, hxA, hadj.symm⟩) hbB
  refine ⟨key A B, fun h => ?_⟩
  rw [disjoint_comm] at h ⊢
  exact key B A h

/-- Growing first and then `d` times is growing `d` times and then once. -/
theorem growIterG_growG (adj : V → V → Prop) (X : Set V) (d : ℕ) :
    growIterG adj (growG adj X) d = growG adj (growIterG adj X d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change growG adj (growIterG adj (growG adj X) d) = growG adj (growG adj (growIterG adj X d))
    rw [ih]

/-- **Growth composes.** -/
theorem growIterG_add (adj : V → V → Prop) (X : Set V) (d₁ d₂ : ℕ) :
    growIterG adj (growIterG adj X d₁) d₂ = growIterG adj X (d₁ + d₂) := by
  induction d₂ with
  | zero => rfl
  | succ d ih =>
    change growG adj (growIterG adj (growIterG adj X d₁) d) = growG adj (growIterG adj X (d₁ + d))
    rw [ih]

/-- ★★ **Being `d` hops apart is symmetric.** -/
theorem hopSeparated_comm (adj : V → V → Prop) (d : ℕ) (X Y : Set V) :
    HopSeparated adj d X Y ↔ HopSeparated adj d Y X := by
  induction d generalizing X Y with
  | zero => exact disjoint_comm
  | succ d ih =>
    have h1 : HopSeparated adj (d + 1) X Y ↔ Disjoint (growIterG adj X d) (growG adj Y) :=
      disjoint_growG_comm adj _ _
    have h2 : HopSeparated adj (d + 1) Y X ↔ HopSeparated adj d (growG adj Y) X := by
      unfold HopSeparated
      rw [growIterG_growG]
      exact Iff.rfl
    rw [h1, h2]
    exact ih X (growG adj Y)

/-- **What the graph permits**: `e₁` is not later than `e₂` in flow time, and the two regions
are not `d` hops apart. -/
def FlowEvent.PermittedWithin (adj : V → V → Prop) (d : ℕ) (e₁ e₂ : FlowEvent V) : Prop :=
  e₁.time ≤ e₂.time ∧ ¬ HopSeparated adj d e₁.region e₂.region

theorem FlowEvent.PermittedWithin.mono {adj : V → V → Prop} {e₁ e₂ : FlowEvent V} {j d : ℕ}
    (h : j ≤ d) (hp : FlowEvent.PermittedWithin adj j e₁ e₂) :
    FlowEvent.PermittedWithin adj d e₁ e₂ :=
  ⟨hp.1, fun hd => hp.2 (hd.mono h)⟩

/-- ★★★ **Permitted against demonstrated, for events at flow times.** The carrier moves by
`exp (u S)`, with `S` hopping along the graph. A kick `W`, the identity off the region of
`e₁`, is applied at the time of `e₁`. An observable `D` on the region of `e₂`, read at the
time of `e₂`, moves by at most `2 (2 ‖S‖ (t₂ − t₁))^d / d! · ‖D‖` when the two regions are
`d` hops apart. -/
theorem FlowEvent.kick_response_le [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hhop : HopsG adj σ S) {e₁ e₂ : FlowEvent V} (hle : e₁.time ≤ e₂.time) {d : ℕ}
    (hsep : HopSeparated adj d e₁.region e₂.region) {D : Matrix n n ℂ}
    (hD : SiteSuppG σ e₂.region D) {W : Matrix.unitaryGroup n ℂ}
    (hW : IdOffG σ e₁.region W.val) {U₁ U : Matrix.unitaryGroup n ℂ}
    (hU : U.val = exp ((e₂.time - e₁.time) • S)) (p : GenArena n) :
    |arenaObs D (arenaKick U (arenaKick W (arenaKick U₁ p)))
        - arenaObs D (arenaKick U (arenaKick U₁ p))|
      ≤ 2 * ((2 * ‖S‖ * (e₂.time - e₁.time)) ^ d / d.factorial) * ‖D‖ :=
  abs_arenaObs_flow_kick_sub_graph_le hS hhop hD hW
    ((hopSeparated_comm adj d _ _).1 hsep) (sub_nonneg.2 hle) hU (arenaKick U₁ p)

/-- ★★ **At equal flow times a kick one hop or more away is not felt at all.** -/
theorem FlowEvent.kick_response_eq_of_time_eq [Fintype n] [DecidableEq n] [Nonempty n]
    {adj : V → V → Prop} {σ : n → V} {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    (hhop : HopsG adj σ S) {e₁ e₂ : FlowEvent V} (heq : e₁.time = e₂.time) {d : ℕ}
    (hd : 1 ≤ d) (hsep : HopSeparated adj d e₁.region e₂.region) {D : Matrix n n ℂ}
    (hD : SiteSuppG σ e₂.region D) {W : Matrix.unitaryGroup n ℂ}
    (hW : IdOffG σ e₁.region W.val) {U₁ U : Matrix.unitaryGroup n ℂ}
    (hU : U.val = exp ((e₂.time - e₁.time) • S)) (p : GenArena n) :
    arenaObs D (arenaKick U (arenaKick W (arenaKick U₁ p)))
      = arenaObs D (arenaKick U (arenaKick U₁ p)) := by
  have h := FlowEvent.kick_response_le hS hhop heq.le hsep hD hW (U₁ := U₁) hU p
  rw [heq, sub_self, mul_zero, zero_pow (Nat.pos_iff_ne_zero.1 hd), zero_div, mul_zero,
    zero_mul] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

end Graph

end CSD.RecordLayer

end
