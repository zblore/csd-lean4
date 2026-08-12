/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.RecordDegradation
public import CsdLean4.CV.CarrierPersistence

/-!
# H7 level 2: the event is invariant; only the carrier has a lifetime

**Category:** 3-Local (CSD-ontic record layer; `specs/BACKLOG.md` H7).

The framing half of H7 (binding per the row): the record **event** — that
the trajectory's readout showed value `v` at step `k₀` — is a fact *about
the trajectory*, indexed by when it happened. Under evolution it **reindexes,
never decays** (`recordEvent_preimage_step`), and its probability is exactly
conserved (`recordEvent_measure_invariant`). By contrast the **carrier** —
present readout-cylinder membership, `recordIntact` — is genuinely
perishable: intactness is antitone in time (`recordIntact_antitone`), and
its erosion is priced by the §H half-life bound
(`recordIntact_compl_measure_le`) and, at level 1, by field locality
(`CV/CarrierPersistence.lean`: exact in the cone-complement, the Duhamel
rate after — `carrier_persistence_window`).

Clause (d), operational fixedness, is the finite-arena repeatability theorem
`csd_repeatability_same` (`Empirical/CSD/SequentialMeasurement.lean`):
measuring an isolated carrier in the pointer basis returns the recorded
value with probability `1` — cited, not re-proved; its CV-mode analogue
rides the `OscillatorBorn` truncation and is not restated here.

Information is never lost under any of these dynamics
(`perturbed_overlap_invariant`, `inner_iterate_iterate`): carrier erosion is
relocation of correlations, not destruction — so nothing in this module (or
in level 1) is a statement about "the past changing". Everything is
present-tense checkable.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.QuantumChaos

variable {A V : Type*}

/-! ### The record event: trajectory-indexed, invariant -/

/-- **The record event**: the trajectory's readout showed value `v` at step
`k₀`. A predicate on the trajectory (equivalently its initial condition),
indexed by *when it happened* — not a stored, perishable structure. -/
def recordEvent (Φ : A → A) (ρ : A → V) (k₀ : ℕ) (v : V) : Set A :=
  {x | ρ (Φ^[k₀] x) = v}

/-- ★ **Events reindex, never decay**: evolving the initial condition one
step turns "showed `v` at step `k₀`" into "showed `v` at step `k₀ + 1`" —
the same fact, relabelled. Contrast `recordIntact_antitone`: carriers are
genuinely lost; events are only re-addressed. -/
theorem recordEvent_preimage_step (Φ : A → A) (ρ : A → V) (k₀ : ℕ) (v : V) :
    Φ ⁻¹' recordEvent Φ ρ k₀ v = recordEvent Φ ρ (k₀ + 1) v := by
  ext x
  show ρ (Φ^[k₀] (Φ x)) = v ↔ ρ (Φ^[k₀ + 1] x) = v
  rw [Function.iterate_succ_apply]

/-- ★ **The event's probability is exactly conserved** under any
measure-preserving evolution: what changes with time is only the index of
the fact, never its weight. -/
theorem recordEvent_measure_invariant [MeasurableSpace A] {μ : Measure A}
    {Φ : A → A} (hΦ : MeasurePreserving Φ μ μ) {ρ : A → V} {k₀ : ℕ} {v : V}
    (hE : MeasurableSet (recordEvent Φ ρ k₀ v)) :
    μ (recordEvent Φ ρ (k₀ + 1) v) = μ (recordEvent Φ ρ k₀ v) := by
  rw [← recordEvent_preimage_step Φ ρ k₀ v]
  exact hΦ.measure_preimage hE.nullMeasurableSet

/-! ### The carrier: genuinely perishable -/

/-- **Carriers are antitone**: readout intactness over a longer window is a
stronger condition — carriers can only be lost, never spontaneously
regained. The precise counterpoint to `recordEvent_preimage_step`. -/
theorem recordIntact_antitone (Φ : A → A) (ρ : A → V) {n m : ℕ}
    (hnm : n ≤ m) :
    recordIntact Φ ρ m ⊆ recordIntact Φ ρ n :=
  fun _ ha k hk => ha k (hk.trans hnm)

end CSD.Empirical.QuantumChaos
