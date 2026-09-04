/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MomentMapRace
public import CsdLean4.LF1.GeneralFrequency

/-!
# SigmaLayer/Measurement: the measurement architecture in one object (MD-1)

**Category:** 7-SigmaLayer (the record layer — the measurement as context + microstate → record).

The record-layer architecture assembled into a single object `Measurement`, exactly the intended shape:

* the **context** `m.context` is the *measurement type* — it fixes the basin partition of the fibre,
  and therefore the outcome probabilities (the moment-map/Born weights);
* the **microstate** `ξ : ℝ` is the *unknown* ontic fibre point (typical under `fibreTypicality`);
* the microstate selects an **outcome** `m.outcome ξ` — the basin it occupies (`outcome_eq_some_iff`);
* the **basins set the probabilities**: `m.prob i = fibreTypicality (m.basin i)`, which for the Born
  measurement is `‖ψ i‖²` = the Kähler moment map (`bornMeasurement_prob`,
  `bornMeasurement_prob_momentMap`);
* the combined **result is the record** `m.record ξ = ⟨context, outcome, time⟩` (`record_of_mem_basin`).

So one microstate + one context deterministically yields one record. The probabilistic content is
*nothing special* — it is the **law of large numbers over the unknown initial microstate**: each run
is deterministic given its microstate, and across repeated preparations the microstate is typical
(`fibreTypicality`), so the outcome-`i` frequency converges a.s. to the basin measure `‖ψ i‖²`
(`bornMeasurement_frequency`, via the strong law `freq_tendsto_of_iid`). Randomness = ignorance of the
initial condition; Born = the LLN limit = the basin measure = the Kähler moment map.

**Honest scope.** Every fact here is grounded in the proven pieces (`BornFibrePartition`,
`DeIsolationFlow`, `FibreRecord`, `MomentMapRace`, `LF1/GeneralFrequency`); the probabilities are the
*typicality of the basins*, the basins carry the *moment map*, and the frequencies are the *strong
law* — no injected probability vector and no extra dynamical postulate. The de-isolation flow is just
the deterministic map from microstate to basin (which is what a measurement context *is*); there is no
separate "derive the flow" problem, only the standard typicality+LLN story of Papers A/D.
Foundational-triple, no `sorry`.

## References
`specs/record-layer-plan.md` (record layer, MD-1); `RecordLayer/FibreRecord.lean` (the P5
`RecordSemantics`, `bornContext`); `RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap`,
the rates = the Kähler moment map); `RecordLayer/DeIsolationFlow.lean` (`fibreTypicality`).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer CSD.LF4

namespace CSD.RecordLayer

variable {n : ℕ}

/-- **A measurement: a context (measurement type) awaiting an unknown microstate.** The context fixes
the fibre's basin partition (hence the outcome probabilities); a microstate `ξ` then selects the basin
it occupies, and the combined result is the record. -/
structure Measurement (n : ℕ) where
  /-- The measurement context — the measurement type; fixes the basins and the probabilities. -/
  context : FibreContext n
  /-- The ontic time at which the record is established. -/
  time : OnticTime

namespace Measurement

variable (m : Measurement n)

/-- The **basin** of outcome `i`: the fibre region (record event) the context assigns to `i`. The
basins are the measurement type's partition of the fibre. -/
def basin (i : Fin n) : Set ℝ := (fibreRecordSemantics n).event ⟨m.context, i, m.time⟩

/-- The **outcome** the unknown microstate `ξ` selects: the basin it occupies (`none` off the basins,
a `fibreTypicality`-null set). -/
noncomputable def outcome (ξ : ℝ) : Option (Fin n) := fibreOutcome m.context.rate ξ

/-- The **record**: the combined result the microstate `ξ` produces — the recorded fact
`⟨context, outcome, time⟩`, when the outcome is determined. -/
noncomputable def record (ξ : ℝ) : Option (RecordedFact (fibreSignature n)) :=
  (m.outcome ξ).map (fun i => ⟨m.context, i, m.time⟩)

/-- The **probability** of outcome `i`: the fibre typicality of its basin. The basins set the
probabilities. -/
noncomputable def prob (i : Fin n) : ENNReal := fibreTypicality (m.basin i)

/-- The basin is the context's CDF cell. -/
theorem basin_eq (i : Fin n) : m.basin i = cdfCell m.context.rate i :=
  fibreRecordSemantics_event m.context i m.time

/-- **The microstate selects the basin it occupies:** the outcome is `i` exactly when `ξ` lies in
basin `i`. -/
theorem outcome_eq_some_iff (i : Fin n) (ξ : ℝ) : m.outcome ξ = some i ↔ ξ ∈ m.basin i :=
  fibreOutcome_eq_record m.context i m.time ξ

/-- **The combined result is the record:** a microstate in basin `i` produces the record
`⟨context, i, time⟩`. -/
theorem record_of_mem_basin (i : Fin n) (ξ : ℝ) (h : ξ ∈ m.basin i) :
    m.record ξ = some ⟨m.context, i, m.time⟩ := by
  rw [record, (outcome_eq_some_iff m i ξ).mpr h]; rfl

/-- **The Born measurement** of a state `ψ`: the context whose rates are the Born weights `‖ψ i‖²`
(= the Kähler moment map), established at time `t`. -/
noncomputable def bornMeasurement (ψ : EuclideanSpace ℂ (Fin n)) (t : OnticTime) : Measurement n :=
  ⟨bornContext ψ, t⟩

/-- **The basins set the probabilities = Born.** For a unit state the probability of outcome `i` of
the Born measurement is exactly `‖ψ i‖²`. -/
theorem bornMeasurement_prob (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n)
    (t : OnticTime) :
    (bornMeasurement ψ t).prob i = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  rw [prob, basin]
  exact fibreTypicality_bornRecord ψ hψ i t

/-- **The probability is the Kähler moment map.** The Born measurement's outcome-`i` probability is
the `i`-th torus moment-map coordinate at `[ψ]` — the probabilities are forced by the Kähler geometry,
not injected. -/
theorem bornMeasurement_prob_momentMap (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin n) (t : OnticTime) :
    (bornMeasurement ψ t).prob i = ENNReal.ofReal (momentMap (Projectivization.mk ℂ ψ hψ0) i) := by
  rw [bornMeasurement_prob ψ hψ i t]
  congr 1
  exact bornRate_eq_momentMap ψ hψ0 hψ i

/-- **The unknown microstate almost surely produces a record.** For a unit state the Born
measurement's basins cover the fibre up to a `fibreTypicality`-null set: a.e. microstate lands in some
basin, so a.e. microstate yields a record. -/
theorem bornMeasurement_ae_total (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (t : OnticTime) :
    fibreTypicality (Ico (0 : ℝ) 1 \ ⋃ i, (bornMeasurement ψ t).basin i) = 0 :=
  fibreTypicality_uncovered ψ hψ

/-- **The Born rule as the law of large numbers over the unknown microstate.** This is the whole
probabilistic content, and it is *nothing special*: the microstate is unknown, each run is
deterministic given it, and across repeated preparations the microstate is typical (`fibreTypicality`),
so the outcome-`i` frequency converges almost surely to the basin measure `‖ψ i‖²` — the Born weight.
Randomness = ignorance of the initial condition; the limit is the strong law (`freq_tendsto_of_iid`).

For i.i.d. trials `X k` with law `fibreTypicality`, the frequency of trials whose microstate lands in
basin `i` converges a.s. to `‖ψ i‖²`. -/
theorem bornMeasurement_frequency (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (t : OnticTime)
    (i : Fin n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hlaw : ∀ k, Measure.map (X k) P = fibreTypicality)
    (hindep : Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g P)
      (fun k => Set.indicator (X k ⁻¹' (bornMeasurement ψ t).basin i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P, Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N,
        Set.indicator (X k ⁻¹' (bornMeasurement ψ t).basin i) (fun _ => (1 : ℝ)) ω) / (N : ℝ))
      Filter.atTop (nhds (‖ψ i‖ ^ 2)) := by
  have hmeas : MeasurableSet ((bornMeasurement ψ t).basin i) :=
    (fibreRecordSemantics n).measurable_event _
  have hval : (fibreTypicality ((bornMeasurement ψ t).basin i)).toReal = ‖ψ i‖ ^ 2 := by
    have hp : fibreTypicality ((bornMeasurement ψ t).basin i) = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
      bornMeasurement_prob ψ hψ i t
    rw [hp, ENNReal.toReal_ofReal (by positivity)]
  have h := CSD.LF1.freq_tendsto_of_iid hX hlaw hmeas hindep
  rwa [hval] at h

end Measurement

end CSD.RecordLayer
