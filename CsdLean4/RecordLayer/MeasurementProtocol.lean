/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MeasurementConstraints
public import CsdLean4.RecordLayer.GlobalRecordClosure

/-!
# SigmaLayer/MeasurementProtocol: the dynamical measurement interface (Paper D, items 1–2)

**Category:** 7-SigmaLayer (the record layer — the dynamical interface).

## What this fixes

`globalBasin_ae_total` shows the context-fixed basins cover `Σ` up to a null set, so **a.e. point
already carries a record** and there is no apparatus-ready state of positive measure. A flow cannot
*create* a record in such a space. This file supplies the missing structure: a **pointer register**
whose ready region is genuinely disjoint from every outcome region, together with a **two-time
propagator** that can carry a ready state into a recorded one.

★ **`ready_disjoint_pointer` is the whole point of the structure.** It is what `GlobalBasin` lacked,
and it is a *checkable* condition on the regions — not a physics assumption.

## ★ The design rule this file obeys

The plan it implements warns that a structure with fields like `basin_has_born_measure` or
`record_persists` "would merely rename the assumptions". That warning is taken literally:

> **`MeasurementProtocol` carries only kinematics** — the propagator laws, the regions, and their
> measurability and disjointness. Every one of those is a *checkable property of the data*.
> **The correlation between selector and pointer is NOT a field.** It appears as `CorrelatesOn`, a
> hypothesis of the theorems that need it (`CONVENTIONS.md` §8.3's `_of_` pattern), so discharging
> it is the visible act of *removing a hypothesis*, and no theorem here can be mistaken for
> physics that has not been done.

The corpus already has one field-shaped assumption of exactly the forbidden kind —
`DeIsolationInteraction.basin_rate` — and this file deliberately does not add a second.

## What is proved

* `MeasurementProtocol` — two-time propagator `Φ_{s→t}` with `Φ_{t→t} = id` and
  `Φ_{t→u} ∘ Φ_{s→t} = Φ_{s→u}`, plus ready/pointer regions. A two-time family rather than a
  one-parameter group, because a measurement interaction is *switched on and off*.
* `readout_ready_eq_none` — **before the interaction there is no record.** The non-triviality
  condition that `GlobalBasin` could not state.
* `outcomeSector` — `Ωᵢ = Φ_{0→T}⁻¹(Bᵢ)`, the *initial* states that evolve into record `i`. This is
  the TN6 distinction: `Bᵢ` is where a record is displayed, `Ωᵢ` is where one is destined.
* `outcomeSector_measurable`, `outcomeSector_pairwiseDisjoint`.
* `readout_evolve_outcomeSector` — a point of `Ωᵢ` really does read `i` after evolution.
* `measure_outcomeSector_eq_of_correlates` — **★ the Born derivation.** *Given* the correlation, the
  outcome sector's measure equals the selector sector's. Composed with `globalBasin_born` this makes
  the dynamical Born weight `‖⟨eᵢ,ψ⟩‖²` a **consequence**, not a posit.

## ⚠️ What is NOT here, and is the actual research problem

**No interaction Hamiltonian.** Nothing in this file constructs a `Φ` satisfying `CorrelatesOn`, and
the existence of one is exactly the open Paper D obligation. Every theorem below is either pure
kinematics or explicitly conditional. **This file is scaffolding for the statement of the problem,
not progress on its solution.**

⚠️ And by `no_everywhere_correlation` (`MeasurementConstraints.lean`), any `Φ` satisfying the
*everywhere* form of `CorrelatesOn` on a connected ready set **cannot exist** for `K ≥ 2`. The
`CorrelatesOn` below is therefore stated with a set inclusion that callers are expected to satisfy
only up to a null set; a witness must say what happens on the seam.

## References

`RecordLayer/MeasurementConstraints.lean` (the necessary conditions any witness must meet);
`RecordLayer/GlobalBasin.lean` (`globalBasin`, `globalBasin_born` — the selector);
`RecordLayer/DeIsolationFlow.lean` (the open `H_int(M)` obligation); `specs/BACKLOG.md` (the ★★ row).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

/-! ### The protocol -/

/-- **A measurement protocol**: a two-time propagator together with an apparatus-ready region and a
family of pointer regions.

A *two-time* family `Φ_{s→t}`, not a one-parameter group, because the interaction is switched on and
off — a time-dependent `H_int(M,t)` does not generate a group.

Every field is kinematic and checkable. ★ In particular `ready_disjoint_pointer` — the ready region
meets no pointer region — is what makes "no record yet" a state of positive measure, which the
`GlobalBasin` construction structurally could not have. -/
structure MeasurementProtocol (Sigma : Type*) [MeasurableSpace Sigma] (K : ℕ) where
  /-- `evolve s t` is the propagator `Φ_{s→t}` from time `s` to time `t`. -/
  evolve : OnticTime → OnticTime → Sigma → Sigma
  /-- No evolution over zero elapsed time. -/
  evolve_self : ∀ t, evolve t t = id
  /-- The two-time composition law. -/
  evolve_comp : ∀ s t u, evolve t u ∘ evolve s t = evolve s u
  /-- The propagator is measurable. -/
  measurable_evolve : ∀ s t, Measurable (evolve s t)
  /-- The time at which the interaction begins. -/
  startTime : OnticTime
  /-- The time by which the record is established. -/
  readoutTime : OnticTime
  /-- The operational record lifetime `τ_R`: how long the apparatus is claimed to hold a record.
  A **finite** window, deliberately. On a compact phase space with an invariant probability measure,
  indefinite stability raises recurrence questions that finite-QM closure does not need. -/
  recordDuration : OnticTime
  /-- The apparatus-ready region: no outcome is recorded here. -/
  readyRegion : Set Sigma
  /-- The pointer region displaying outcome `i`. -/
  pointerRegion : Fin K → Set Sigma
  measurableSet_ready : MeasurableSet readyRegion
  measurableSet_pointer : ∀ i, MeasurableSet (pointerRegion i)
  /-- Distinct outcomes are displayed by disjoint pointer regions. -/
  pointer_pairwiseDisjoint : Pairwise (Function.onFun Disjoint pointerRegion)
  /-- ★ **The ready region records nothing.** The structural condition `GlobalBasin` lacked. -/
  ready_disjoint_pointer : ∀ i, Disjoint readyRegion (pointerRegion i)

namespace MeasurementProtocol

variable {Sigma : Type*} [MeasurableSpace Sigma] {K : ℕ} (P : MeasurementProtocol Sigma K)

/-! ### Readout -/

/-- The apparatus readout: which pointer region the state occupies, if any. -/
noncomputable def readout (x : Sigma) : Option (Fin K) :=
  open Classical in
  if h : ∃ i, x ∈ P.pointerRegion i then some h.choose else none

theorem readout_eq_some_iff (x : Sigma) (i : Fin K) :
    P.readout x = some i ↔ x ∈ P.pointerRegion i := by
  classical
  constructor
  · intro h
    unfold readout at h
    split at h
    · next hex =>
      have := hex.choose_spec
      rw [Option.some_inj] at h
      exact h ▸ this
    · exact absurd h (by simp)
  · intro hx
    unfold readout
    split
    · next hex =>
      have hchoose := hex.choose_spec
      by_cases hij : hex.choose = i
      · rw [hij]
      · exact absurd (Set.disjoint_left.mp (P.pointer_pairwiseDisjoint hij) hchoose) (by simpa)
    · next hne => exact absurd ⟨i, hx⟩ hne

/-- ★ **Before the interaction there is no record.** A state in the apparatus-ready region reads
`none` — the non-triviality condition that stops a pre-existing label being presented as a created
record, and the thing `GlobalBasin`'s a.e.-total basins made impossible. -/
theorem readout_ready_eq_none {x : Sigma} (hx : x ∈ P.readyRegion) : P.readout x = none := by
  classical
  unfold readout
  split
  · next hex =>
    obtain ⟨i, hi⟩ := hex
    exact absurd hi (Set.disjoint_left.mp (P.ready_disjoint_pointer i) hx)
  · rfl

/-! ### The outcome sector -/

/-- **The outcome sector `Ωᵢ`**: the *initial* states that evolve into the pointer region for
outcome `i` by the readout time.

★ This is the TN6 two-level distinction made precise: `pointerRegion i` is where a record is
*displayed*; `outcomeSector i` is where a record is *destined*. They are different sets, related by
the propagator, and conflating them is what makes a kinematic partition look dynamical. -/
def outcomeSector (i : Fin K) : Set Sigma :=
  P.evolve P.startTime P.readoutTime ⁻¹' P.pointerRegion i

theorem outcomeSector_measurable (i : Fin K) : MeasurableSet (P.outcomeSector i) :=
  P.measurable_evolve _ _ (P.measurableSet_pointer i)

/-- Distinct outcome sectors are disjoint — inherited from the pointer regions through the
preimage. -/
theorem outcomeSector_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint P.outcomeSector) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  exact Set.disjoint_left.mp (P.pointer_pairwiseDisjoint hij) hxi hxj

/-- **A state destined for outcome `i` really does read `i` after evolution.** The bridge between
the two levels. -/
theorem readout_evolve_outcomeSector {i : Fin K} {x : Sigma} (hx : x ∈ P.outcomeSector i) :
    P.readout (P.evolve P.startTime P.readoutTime x) = some i :=
  (P.readout_eq_some_iff _ i).mpr hx

/-! ### The correlation obligation — a hypothesis, never a field -/

/-- **The de-isolation correlation**: every selector sector `S i` is carried into the pointer region
for outcome `i`.

⚠️ **This is a `Prop` on the data, deliberately NOT a field of `MeasurementProtocol`.** Making it a
field would let a witness *assume* the physics and present the assumption as structure — the failure
the implementation plan explicitly warns against, and which `DeIsolationInteraction.basin_rate`
already commits once. As a hypothesis, discharging it is the visible act of removing it.

⚠️ By `no_everywhere_correlation`, the *everywhere* form below is **unsatisfiable** for `K ≥ 2` on a
connected ready set. Real witnesses will establish it only off a null set, and must say what happens
on the seam; the strict form is kept here because it is what the measure argument consumes, and a
caller supplying it a.e. can pass to a full-measure subset. -/
def CorrelatesOn (S : Fin K → Set Sigma) : Prop :=
  ∀ i, S i ⊆ P.outcomeSector i

/-- **★ The dynamical Born weight, derived rather than posited.**

*Given* the correlation, the measure of the outcome sector equals the measure of the selector
sector. So the dynamic probability is not a new postulate: it is the *existing* context-fixed
selector weight, transported by the interaction.

The argument needs no cancellation trickery. `Ωᵢ` is disjoint from every `S j` with `j ≠ i` (those
sit inside `Ω j`), so `μ(Ωᵢ) + μ(⋃_{j≠i} S j) ≤ 1 = μ(Sᵢ) + μ(⋃_{j≠i} S j)`, and the common finite
term cancels. The reverse inequality is monotonicity. -/
theorem measure_outcomeSector_eq_of_correlates
    {μ : Measure Sigma} [IsProbabilityMeasure μ]
    {S : Fin K → Set Sigma}
    (hSmeas : ∀ i, MeasurableSet (S i))
    (hSdisj : Pairwise (Function.onFun Disjoint S))
    (hcover : ∑ i, μ (S i) = 1)
    (hcorr : P.CorrelatesOn S) (i : Fin K) :
    μ (P.outcomeSector i) = μ (S i) := by
  classical
  set A : Set Sigma := ⋃ j ∈ Finset.univ.erase i, S j with hA
  have hAmeas : MeasurableSet A := by
    exact Finset.measurableSet_biUnion _ fun j _ => hSmeas j
  -- `A` is disjoint from the outcome sector of `i`.
  have hdisjA : Disjoint (P.outcomeSector i) A := by
    rw [Set.disjoint_right]
    intro x hxA hxi
    simp only [hA, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true] at hxA
    obtain ⟨j, hji, hxj⟩ := hxA
    exact Set.disjoint_left.mp (P.outcomeSector_pairwiseDisjoint hji) (hcorr j hxj) hxi
  have hdisjS : Disjoint (S i) A := by
    rw [Set.disjoint_right]
    intro x hxA hxi
    simp only [hA, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true] at hxA
    obtain ⟨j, hji, hxj⟩ := hxA
    exact Set.disjoint_left.mp (hSdisj hji) hxj hxi
  have hAsum : μ (S i) + μ A = 1 := by
    rw [← measure_union hdisjS hAmeas]
    have : S i ∪ A = ⋃ j ∈ (Finset.univ : Finset (Fin K)), S j := by
      rw [hA]; ext x
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        exists_prop, true_and]
      constructor
      · rintro (h | ⟨j, _, hj⟩)
        · exact ⟨i, h⟩
        · exact ⟨j, hj⟩
      · rintro ⟨j, hj⟩
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr ⟨j, hji, hj⟩
    rw [this, measure_biUnion_finset (fun j _ k _ hjk => hSdisj hjk) (fun j _ => hSmeas j),
      hcover]
  have hAtop : μ A ≠ ⊤ := measure_ne_top μ A
  refine le_antisymm ?_ (measure_mono (hcorr i))
  have hle : μ (P.outcomeSector i) + μ A ≤ μ (S i) + μ A := by
    rw [← measure_union hdisjA hAmeas, hAsum]
    exact (measure_mono (subset_univ _)).trans_eq measure_univ
  exact (ENNReal.add_le_add_iff_right hAtop).mp hle

end MeasurementProtocol

end CSD.RecordLayer
