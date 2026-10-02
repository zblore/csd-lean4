/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Authors: Zayn Blore
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CsdLean4.CV.RecordInfluence

/-!
# The causal order on record events

**Category:** 3-Local (CV; the event layer of `ST-1`).
BACKLOG #38, the event-order piece recorded in the row on 2026-10-02.

[`RecordInfluence.lean`](RecordInfluence.lean) (`ST-1`) relates **regions** with a period budget
supplied separately, so its relation is *graded*: two reaches within `n` compose into one within
`2n`, and the word *preorder* belongs only to the existentially quantified `EventuallyInfluences`.
The object a causal structure actually wants is an **event**, which carries its own time — and then
the budget is inside the relation and the grading disappears:

* `RecordEvent K` — a read region together with the period index at which its record is written;
* `CausalPrecedes E e₁ e₂ := e₁.time ≤ e₂.time ∧ Influences E e₁.region e₂.region (e₂.time − e₁.time)`;
* ★★ `causalPrecedes_trans` — the elapsed periods of the two legs add to the elapsed periods of the
  whole, which is `ST-1`'s `graphBall_add` with the ℕ arithmetic discharged;
* ★★ `causalPrecedes_antisymm` — equal times force a zero budget, and at zero the cone is the region
  itself, so the two regions contain one another;
* ★★★ `isPartialOrder_causalPrecedes` — **the record events of a coupling graph carry a partial
  order**: a causal set, reflexive, transitive and antisymmetric, with no budget left dangling. This
  is the object `ST-1`'s graded relation was an approximation to;
* `causalPrecedes_same_region` — a record of the same region later is in the causal future;
* `EventSpacelike` — neither event in the other's causal past, with ★★
  `eventSpacelike_of_spacelike`: **geometry gives order**, if the regions are spacelike at a budget
  covering the gap either way;
* ★★★ `arenaObs_kick_of_eventSpacelike` — **the order's dynamical content**: under that same
  hypothesis the first event's record reading is *exactly* unchanged by any unitary kick on the
  second's region, after `n` periods. The dynamical half is `ST-1`'s exact cone theorem; what is new
  is that one hypothesis both orders the events and protects the record.

## Honest scope

⚠️ **This is not spacetime, and the order is not derived from the records.** `CausalPrecedes` is the
order an **assumed** coupling graph `E` induces on events. Nothing here derives `E`, and nothing here
is a metric, a signature, or a continuum. What a spacetime reading would need in addition is the
macroscopic-coordinate projection `π'`, which is a decision the papers do not make
(`specs/records-to-spacetime-scoping.md` §8, `ST-3`); the four candidates now named in
`specs/BACKLOG.md` #38 include the one this module would serve — the macroscopic coordinates *being*
the causal order.

⚠️ **Permitted, not demonstrated, influence**, inherited from `ST-1`: `e₁ ⪯ e₂` says the graph
*allows* influence within the elapsed periods. Everything proved from it has the form *unordered
⇒ nothing happens*; the converse is neither proved nor true in general.

⚠️ **`EventSpacelike` is weaker than `Spacelike`.** Being unordered compares two cones of
*different* radii; the dynamical theorems consume the geometric hypothesis (equal radii, disjoint
cones), so the implication runs geometry → order and not back. That is why
`arenaObs_kick_of_eventSpacelike` carries `Spacelike` and not `EventSpacelike`.

⚠️ The time index is the **period count** of the fixed interacting unitary, not a physical time,
and regions are `Finset`-indexed at a finite mode cutoff.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-1`,
`ST-3`; `RecordInfluence.lean`; `specs/BACKLOG.md` #38, #39.
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {K N : ℕ}

/-! ### Events -/

/-- A **record event**: a read region together with the period index at which its record is
written. `ST-1` relates regions with a duration supplied separately; an event carries its own. -/
@[ext]
structure RecordEvent (K : ℕ) where
  /-- The region the context reads. -/
  region : Finset (Fin K)
  /-- The period at which the record is written. -/
  time : ℕ

/-- **Causal precedence of record events**: the later event's read region lies inside the cone of
the earlier one's, with the elapsed periods as the budget. Because the duration is *inside* the
relation rather than a parameter of it, this is an honest order and not a graded family
(`isPartialOrder_causalPrecedes`). -/
def CausalPrecedes (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : Prop :=
  e₁.time ≤ e₂.time ∧ Influences E e₁.region e₂.region (e₂.time - e₁.time)

theorem causalPrecedes_time {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : CausalPrecedes E e₁ e₂) : e₁.time ≤ e₂.time := h.1

theorem causalPrecedes_influences {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : CausalPrecedes E e₁ e₂) : Influences E e₁.region e₂.region (e₂.time - e₁.time) := h.2

/-! ### It is a partial order -/

theorem causalPrecedes_refl (E : Finset (Fin K × Fin K)) (e : RecordEvent K) :
    CausalPrecedes E e e := by
  refine ⟨le_refl _, ?_⟩
  rw [Nat.sub_self]
  exact influences_refl E e.region

/-- ★★ **Transitivity, with no budget bookkeeping left over**: the elapsed periods of the two legs
add to the elapsed periods of the whole, which is exactly what `graphBall_add` gives. -/
theorem causalPrecedes_trans {E : Finset (Fin K × Fin K)} {e₁ e₂ e₃ : RecordEvent K}
    (h₁ : CausalPrecedes E e₁ e₂) (h₂ : CausalPrecedes E e₂ e₃) : CausalPrecedes E e₁ e₃ := by
  obtain ⟨ht₁, hI₁⟩ := h₁
  obtain ⟨ht₂, hI₂⟩ := h₂
  refine ⟨ht₁.trans ht₂, ?_⟩
  have harith : e₂.time - e₁.time + (e₃.time - e₂.time) = e₃.time - e₁.time := by omega
  rw [← harith]
  exact influences_trans hI₁ hI₂

/-- ★★ **Antisymmetry**: two events each inside the other's cone are the same event. Equal times
force a zero budget, and at a zero budget the cone is the region itself, so the regions are
contained in one another. -/
theorem causalPrecedes_antisymm {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h₁ : CausalPrecedes E e₁ e₂) (h₂ : CausalPrecedes E e₂ e₁) : e₁ = e₂ := by
  obtain ⟨ht₁, hI₁⟩ := h₁
  obtain ⟨ht₂, hI₂⟩ := h₂
  have htime : e₁.time = e₂.time := le_antisymm ht₁ ht₂
  have hz₁ : e₂.time - e₁.time = 0 := by omega
  have hz₂ : e₁.time - e₂.time = 0 := by omega
  rw [hz₁] at hI₁
  rw [hz₂] at hI₂
  exact RecordEvent.ext (Finset.Subset.antisymm hI₂ hI₁) htime

/-- ★★★ **The record events of a coupling graph carry a partial order** — a causal set: reflexive,
transitive and antisymmetric, with no period budget left dangling. This is the object `ST-1`'s graded
relation was an approximation to. -/
theorem isPartialOrder_causalPrecedes (E : Finset (Fin K × Fin K)) :
    IsPartialOrder (RecordEvent K) (CausalPrecedes E) where
  refl := causalPrecedes_refl E
  trans := fun _ _ _ h₁ h₂ => causalPrecedes_trans h₁ h₂
  antisymm := fun _ _ h₁ h₂ => causalPrecedes_antisymm h₁ h₂

theorem isPreorder_causalPrecedes (E : Finset (Fin K × Fin K)) :
    IsPreorder (RecordEvent K) (CausalPrecedes E) :=
  (isPartialOrder_causalPrecedes E).toIsPreorder

/-- A record of the same region at a later period is in the causal future: the region sits inside
its own cone. -/
theorem causalPrecedes_same_region (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) {t₁ t₂ : ℕ}
    (h : t₁ ≤ t₂) : CausalPrecedes E ⟨R, t₁⟩ ⟨R, t₂⟩ :=
  ⟨h, subset_graphBall E R (t₂ - t₁)⟩

/-! ### Spacelike events -/

/-- Two events, neither in the other's causal past. -/
def EventSpacelike (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K) : Prop :=
  ¬CausalPrecedes E e₁ e₂ ∧ ¬CausalPrecedes E e₂ e₁

theorem eventSpacelike_symm {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K}
    (h : EventSpacelike E e₁ e₂) : EventSpacelike E e₂ e₁ := ⟨h.2, h.1⟩

/-- ★★ **Geometry gives order**: if the two read regions are spacelike at a budget covering the
elapsed periods either way, neither event precedes the other. The implication runs this way only —
`EventSpacelike` is a statement about two cones of *different* radii and does not give back the
`Spacelike` hypothesis the dynamical theorems consume. -/
theorem eventSpacelike_of_spacelike {E : Finset (Fin K × Fin K)} {e₁ e₂ : RecordEvent K} {n : ℕ}
    (h : Spacelike E e₁.region e₂.region n) (h₁ : e₁.region.Nonempty) (h₂ : e₂.region.Nonempty)
    (hn₁ : e₂.time - e₁.time ≤ n) (hn₂ : e₁.time - e₂.time ≤ n) : EventSpacelike E e₁ e₂ := by
  constructor
  · intro hc
    exact not_influences_of_spacelike (spacelike_of_le h hn₁) h₂ hc.2
  · intro hc
    exact not_influences_of_spacelike (spacelike_of_le (spacelike_symm h) hn₂) h₁ hc.2

/-- ★★★ **The order's dynamical content, on events**: when two events' regions are spacelike at the
budget `n`, the first event's record reading is **exactly** unchanged by any unitary kick on the
second's region after `n` periods — and the two events are unordered. The dynamical half is
`ST-1`'s exact cone theorem; what is new here is that the same hypothesis orders the events. -/
theorem arenaObs_kick_of_eventSpacelike [NeZero N] {e₁ e₂ : RecordEvent K} {n : ℕ}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    (h : Spacelike E e₁.region e₂.region n) (hA : SupportedOn e₁.region A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn e₂.region W.val)
    (p : FieldArena K N) :
    arenaObs (heisenberg (graphInteractingU K N τ lam E g ^ n) A) (arenaKick W p)
      = arenaObs (heisenberg (graphInteractingU K N τ lam E g ^ n) A) p :=
  arenaObs_heisenberg_kick_of_spacelike τ lam E g n h hA hW p

end CSD.CV

end
