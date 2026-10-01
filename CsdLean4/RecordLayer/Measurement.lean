/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MomentMapRace
public import CsdLean4.LF1.GeneralFrequency

/-!
# RecordLayer/Measurement: context, fibre outcome and recorded fact

**Category:** 7-SigmaLayer (measurement on the real fibre).

A `Measurement` pairs a nonnegative rate vector with a time label. Its disjoint CDF cells
select an optional outcome from a real fibre point and package that outcome as a `RecordedFact`.
The event semantics does not depend on the time label. Rates need not sum to one, so an
arbitrary context can leave a set of positive `fibreTypicality` measure without a record.

* `prob_eq_rate` identifies basin probabilities with rates when the rates sum to one.
* `ae_record_of_sum_eq_one` proves almost-sure record production under that normalization.
* `bornMeasurement_prob` specializes the probability identity to a unit vector's squared
  component norms, and `bornMeasurement_prob_momentMap` identifies these with the moment map.
* `bornMeasurement_frequency` proves the frequency limit for measurable trials with the
  specified fibre law and pairwise independent outcome indicators.

The Born constructor supplies the rate vector from the state. Identifying it with the moment
map does not by itself force an arbitrary context to have those rates; the separate generation
hypothesis and theorem are in `RecordLayer/CellLawForced.lean`. Likewise, a deterministic
selector does not establish independence between preparations: the frequency theorem takes
that assumption explicitly.

This file packages a readout and its law. An interaction that changes an apparatus register
is constructed separately in `RecordLayer/SwapWitness.lean`; sequential register laws are in
`RecordLayer/DrivenTwoTime.lean`. The CDF packaging here does not prove those interaction laws.

## References

`RecordLayer/FibreRecord.lean` (record semantics and Born context);
`RecordLayer/DeIsolationFlow.lean` (restricted Lebesgue typicality);
`RecordLayer/MomentMapRace.lean` (moment-map identification);
`LF1/GeneralFrequency.lean` (strong law for the outcome indicators).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer CSD.LF4

namespace CSD.RecordLayer

variable {n : ℕ}

/-- **A measurement: a context (measurement type) awaiting an unknown microstate.** The context fixes
disjoint fibre cells and their probabilities; a microstate `ξ` selects an outcome when it lies
in a cell, and that outcome is packaged as the record. -/
structure Measurement (n : ℕ) where
  /-- The measurement context; fixes the disjoint cells and their probabilities. -/
  context : FibreContext n
  /-- The ontic time at which the record is established. -/
  time : OnticTime

namespace Measurement

variable (m : Measurement n)

/-- The **basin** of outcome `i`: the fibre region (record event) the context assigns to `i`. The
basins are disjoint CDF cells. Normalized rates give full typicality coverage. -/
def basin (i : Fin n) : Set ℝ := (fibreRecordSemantics n).event ⟨m.context, i, m.time⟩

/-- The **outcome** the unknown microstate `ξ` selects: the basin it occupies (`none` off the basins,
which need not be a `fibreTypicality`-null set for an unnormalized context). -/
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

/-- For normalized context rates, each basin probability equals its rate. -/
theorem prob_eq_rate (hsum : ∑ i, m.context.rate i = 1) (i : Fin n) :
    m.prob i = ENNReal.ofReal (m.context.rate i) := by
  have hsub : cdfCell m.context.rate i ⊆ Ico (0 : ℝ) 1 := by
    simpa only [hsum] using
      cdfCell_subset_Ico m.context.rate m.context.rate_nonneg i
  rw [prob, basin_eq, fibreTypicality,
    Measure.restrict_apply (measurableSet_cdfCell _ _),
    inter_eq_left.mpr hsub, volume_cdfCell]

/-- Normalized contexts produce a record almost surely under `fibreTypicality`.
Nonnegativity alone, the requirement in `FibreContext`, does not imply this. -/
theorem ae_record_of_sum_eq_one (hsum : ∑ i, m.context.rate i = 1) :
    ∀ᵐ ξ ∂fibreTypicality, ∃ i, m.record ξ = some ⟨m.context, i, m.time⟩ := by
  have hcells (i : Fin n) : MeasurableSet (m.basin i) :=
    (fibreRecordSemantics n).measurable_event ⟨m.context, i, m.time⟩
  have hmeas : MeasurableSet (⋃ i, m.basin i) := MeasurableSet.iUnion hcells
  have hdisj : Pairwise (Function.onFun Disjoint m.basin) :=
    cdfCell_pairwiseDisjoint m.context.rate m.context.rate_nonneg
  have hmass : fibreTypicality (⋃ i, m.basin i) = 1 := by
    rw [measure_iUnion hdisj hcells, tsum_fintype]
    change (∑ i, m.prob i) = 1
    simp_rw [m.prob_eq_rate hsum]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => m.context.rate_nonneg i),
      hsum, ENNReal.ofReal_one]
  have hmem : ∀ᵐ ξ ∂fibreTypicality, ξ ∈ ⋃ i, m.basin i :=
    (mem_ae_iff_prob_eq_one hmeas).2 hmass
  filter_upwards [hmem] with ξ hξ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hξ
  exact ⟨i, m.record_of_mem_basin i ξ hi⟩

/-- **The Born measurement** of a state `ψ`: the context whose rates are the Born weights `‖ψ i‖²`
(= the Kähler moment map), established at time `t`. -/
noncomputable def bornMeasurement (ψ : EuclideanSpace ℂ (Fin n)) (t : OnticTime) : Measurement n :=
  ⟨bornContext ψ, t⟩

/-- **The basins set the probabilities = Born.** For a unit state the probability of outcome `i` of
the Born measurement is exactly `‖ψ i‖²`. -/
theorem bornMeasurement_prob (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n)
    (t : OnticTime) :
    (bornMeasurement ψ t).prob i = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  exact (bornMeasurement ψ t).prob_eq_rate (sum_bornRate_unit ψ hψ) i

/-- **The probability is the Kähler moment map.** The Born measurement's outcome-`i` probability is
the `i`-th torus moment-map coordinate at `[ψ]` — read off the context, not injected. That the moment map is the
*right* rate field is pinned by torus *generation* (`torusGenerated_eq_momentMap`, `RecordLayer/CellLawForced.lean`): a context field whose rates generate the coordinate phase
rotations is exactly the moment map. What remains posited is that the rates are generators
(`specs/POSITS.md` Posit 1, restated). -/
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

/-- For measurable trials with law `fibreTypicality` and pairwise independent outcome-`i`
indicators, the outcome-`i` frequency converges almost surely to the unit state's Born weight.
The common law and indicator independence are hypotheses on the repeated preparations. -/
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
