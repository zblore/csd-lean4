/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MeasurementProtocol
public import Mathlib.Probability.ConditionalProbability

/-!
# SigmaLayer/RecordPersistence: persistence and the post-measurement ensemble (items 5–6)

**Category:** 7-SigmaLayer (the record layer — the dynamical interface).

Two things a measurement must do beyond producing an outcome:

* **persist** — the record must still be there after it is made (item 5);
* **disturb** — the selected ensemble must be carried *through* the interaction, which is what makes
  a repeated measurement agree and what the Lüders update describes (item 6).

## ★ Both use the evolution, which is the point

The plan is explicit that reusing the same set at every time does not count as persistence. So
`record_persists_on_interval` is stated about `P.evolve P.startTime t` for a *range* of `t`, and its
proof goes through `evolve_comp` — it is a statement about the propagator, not about a set that
happens not to depend on time. Likewise `postMeasure` is a genuine pushforward along the propagator,
not a relabelling of the conditioned measure.

## What is proved

* `PointerInvariantOn` — the post-readout invariance hypothesis. **A hypothesis, not a field**, for
  the same reason `CorrelatesOn` is: it is an assumption *about the dynamics*, and burying it in a
  structure would let a witness assume what it should prove.
* `record_persists_on_interval` — a state destined for outcome `i` is in the pointer region for
  outcome `i` at **every** time of `[T_M, T_M + τ_R]`.
* `readout_persists_on_interval` — the same, at the level of the readout: the apparatus reads `i`
  throughout the window. ★ This *is* the pointer-level repeatability statement — a second look
  during the record lifetime returns the same outcome.
* `postMeasure` — the post-measurement ensemble `(Φ_{0→T})_* (μ | Ωᵢ)`.
* `postMeasure_supported_pointerRegion` — **it is supported entirely on `Bᵢ`.**

## ★ Selection versus disturbance

`measure_outcomeSector_eq_of_correlates` (previous module) answers *which initial sector produced
outcome `i`* — selection. `postMeasure` answers *where the selected ensemble ends up* — disturbance.
They are different operations on different measures, and the corpus previously had no way to say the
second at all.

`postMeasure_supported_pointerRegion` is close to definitional, and that is a good sign rather than a
weak one: `Φ⁻¹(Bᵢ)` **is** `Ωᵢ` by construction, so conditioning on `Ωᵢ` and pushing forward lands in
`Bᵢ` with probability one, for *any* propagator. The content is in the definitions lining up, which
is what a correct interface looks like.

## ⚠️ Scope

* **No interaction Hamiltonian.** `PointerInvariantOn` is assumed, not constructed. Nothing here
  makes progress on the open Paper D obligation.
* **The Lüders bridge is NOT here.** Item 6 also asks that, after the system-reduction map `r_S` and
  the epistemic projection, this reproduce `ρ ↦ Π_i ρ Π_i / Tr(ρ Π_i)`. That needs a reduction map
  from `Σ_meas` to the system's density operator, which the corpus does not have for this arena. The
  measure-theoretic half is done; the bridge to `LF5`'s Lüders result is not, and is not claimed.
* The finite window `[T_M, T_M + τ_R]` is deliberate — see `recordDuration`.

## References

`RecordLayer/MeasurementProtocol.lean` (`MeasurementProtocol`, `outcomeSector`, `CorrelatesOn`);
`RecordLayer/MeasurementConstraints.lean`; `SigmaLayer/ConditioningLuders.lean` (the *operational*
Lüders result this does not yet connect to); `specs/BACKLOG.md` (the ★★ row).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

namespace MeasurementProtocol

variable {Sigma : Type*} [MeasurableSpace Sigma] {K : ℕ} (P : MeasurementProtocol Sigma K)

/-! ### Item 5 — persistence -/

/-- **Post-readout invariance of the pointer regions.** Once the record is made, the evolution keeps
the state inside the region displaying it, for the whole operational lifetime.

⚠️ **A hypothesis, deliberately not a field of `MeasurementProtocol`.** This is an assumption *about
the dynamics* — exactly the kind the implementation plan warns must not be hidden inside a structure.
A concrete witness must establish it, either by showing `Bᵢ` is forward invariant under the
post-interaction flow or by exhibiting a conserved pointer observable. -/
def PointerInvariantOn : Prop :=
  ∀ (i : Fin K) (s t : OnticTime), P.readoutTime ≤ s → s ≤ t →
    t ≤ P.readoutTime + P.recordDuration →
    ∀ x ∈ P.pointerRegion i, P.evolve s t x ∈ P.pointerRegion i

/-- **★ The record persists across the operational window.**

A state destined for outcome `i` sits in the pointer region for outcome `i` at **every** time of
`[T_M, T_M + τ_R]`, not merely at the readout time.

★ The proof runs through `evolve_comp`: `Φ_{0→t} = Φ_{T→t} ∘ Φ_{0→T}`, so persistence is genuinely a
statement about the *propagator*. It is not the observation that a time-independent set is
time-independent. -/
theorem record_persists_on_interval (hinv : P.PointerInvariantOn)
    {i : Fin K} {x : Sigma} (hx : x ∈ P.outcomeSector i)
    {t : OnticTime} (ht₁ : P.readoutTime ≤ t) (ht₂ : t ≤ P.readoutTime + P.recordDuration) :
    P.evolve P.startTime t x ∈ P.pointerRegion i := by
  have hsplit : P.evolve P.startTime t x
      = P.evolve P.readoutTime t (P.evolve P.startTime P.readoutTime x) := by
    have := congrFun (P.evolve_comp P.startTime P.readoutTime t) x
    simpa [Function.comp] using this.symm
  rw [hsplit]
  exact hinv i P.readoutTime t le_rfl ht₁ ht₂ _ hx

/-- **★ The apparatus reads the same outcome throughout the record's lifetime.**

The readout-level form of persistence — and therefore the pointer-level **repeatability** statement:
looking again at any time in `[T_M, T_M + τ_R]` returns the outcome that was recorded. -/
theorem readout_persists_on_interval (hinv : P.PointerInvariantOn)
    {i : Fin K} {x : Sigma} (hx : x ∈ P.outcomeSector i)
    {t : OnticTime} (ht₁ : P.readoutTime ≤ t) (ht₂ : t ≤ P.readoutTime + P.recordDuration) :
    P.readout (P.evolve P.startTime t x) = some i :=
  (P.readout_eq_some_iff _ i).mpr (P.record_persists_on_interval hinv hx ht₁ ht₂)

/-! ### Item 6 — the post-measurement ensemble -/

/-- **The selected ensemble**: the initial measure conditioned on having produced outcome `i`.

This is *selection* — it identifies which initial states were responsible. It says nothing yet about
where they end up. -/
noncomputable def selectedMeasure (μ : Measure Sigma) (i : Fin K) : Measure Sigma :=
  ProbabilityTheory.cond μ (P.outcomeSector i)

/-- **The post-measurement ensemble**: the selected ensemble carried *through* the interaction.

This is *disturbance*, as against selection — and it is a genuine pushforward along the propagator,
which is what distinguishes it from merely relabelling `selectedMeasure`. -/
noncomputable def postMeasure (μ : Measure Sigma) (i : Fin K) : Measure Sigma :=
  Measure.map (P.evolve P.startTime P.readoutTime) (P.selectedMeasure μ i)

/-- **★ After the measurement, the ensemble is supported on the pointer region for the outcome
observed.**

The whole selected ensemble lands in `Bᵢ`: `postMeasure μ i (Bᵢ) = 1`.

★ Almost definitional, and that is the right shape rather than a weakness: `Φ⁻¹(Bᵢ)` **is** `Ωᵢ` by
the definition of `outcomeSector`, so conditioning on `Ωᵢ` and pushing forward must land in `Bᵢ`.
The content lies in the definitions lining up — which is what a correct interface looks like — and it
holds for *any* propagator, needing neither `CorrelatesOn` nor `PointerInvariantOn`. -/
theorem postMeasure_supported_pointerRegion {μ : Measure Sigma} (i : Fin K)
    (hpos : μ (P.outcomeSector i) ≠ 0) (hfin : μ (P.outcomeSector i) ≠ ⊤) :
    P.postMeasure μ i (P.pointerRegion i) = 1 := by
  rw [postMeasure,
    Measure.map_apply (P.measurable_evolve _ _) (P.measurableSet_pointer i)]
  have hpre : P.evolve P.startTime P.readoutTime ⁻¹' P.pointerRegion i = P.outcomeSector i := rfl
  rw [hpre, selectedMeasure, ProbabilityTheory.cond_apply (P.outcomeSector_measurable i),
    Set.inter_self]
  exact ENNReal.inv_mul_cancel hpos hfin

end MeasurementProtocol

end CSD.RecordLayer
