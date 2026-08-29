/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Probability.ConditionalProbability
public import CsdLean4.Mathlib.MeasureTheory.MapProbability
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional-probability toolkit: pushforward, products, full-measure events

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

Four small lemmas about `ProbabilityTheory.cond` that Mathlib does not currently provide:

- `cond_map` — conditioning commutes with pushforward:
  `cond (f_*μ) S = f_* (cond μ (f⁻¹S))`.
- `cond_prod_prod` — conditioning a product measure on a product event conditions the
  factors independently.
- `cond_eq_self` — conditioning a probability measure on a full-measure event does nothing.
- `cond_finsetSum` — **Bayes for finite mixtures**: conditioning a finite mixture is the
  posterior-weighted mixture of the conditionings,
  `cond (∑ⱼ cⱼ•μⱼ) S = ∑ⱼ (cⱼ·μⱼ(S) / (∑ₖ cₖ•μₖ)(S)) • cond μⱼ S`. The degenerate cases
  ride the `ℝ≥0∞` conventions: zero-mass components drop out of both sides, and a
  zero-mass (or infinite-mass) mixture makes both sides the zero measure.

## Provenance

`cond_map`/`cond_prod_prod`/`cond_eq_self` extracted 2026-08-02 from
`CsdLean4/RecordLayer/JoinLuders.lean` (the degenerate-Lüders conditioning bookkeeping);
`cond_finsetSum` added 2026-08-03 for the outcome-conditioned mixed update
(`CsdLean4/RecordLayer/MixedLuders.lean`). Staged here for upstream. Naming and import
discipline track Mathlib idiom; intended target `Mathlib.Probability.ConditionalProbability`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Conditioning commutes with pushforward: `cond (f_*μ) S = f_* (cond μ (f⁻¹S))`. -/
theorem cond_map (μ : Measure X) {f : X → Y} (hf : Measurable f) {S : Set Y}
    (hS : MeasurableSet S) :
    ProbabilityTheory.cond (Measure.map f μ) S
      = Measure.map f (ProbabilityTheory.cond μ (f ⁻¹' S)) := by
  show ((Measure.map f μ) S)⁻¹ • (Measure.map f μ).restrict S
    = Measure.map f ((μ (f ⁻¹' S))⁻¹ • μ.restrict (f ⁻¹' S))
  -- `Measure.map_smul'` is the compat spelling: master's `map_smul` takes a
  -- measurability hypothesis the pin's does not (2026-08-29 canary).
  rw [Measure.map_apply hf hS, Measure.restrict_map hf hS, Measure.map_smul' _ _ hf]

/-- Conditioning a product on a product event conditions the factors independently. -/
theorem cond_prod_prod (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [SFinite μ] (A : Set X) (B : Set Y) :
    ProbabilityTheory.cond (μ.prod ν) (A ×ˢ B)
      = (ProbabilityTheory.cond μ A).prod (ProbabilityTheory.cond ν B) := by
  show ((μ.prod ν) (A ×ˢ B))⁻¹ • (μ.prod ν).restrict (A ×ˢ B)
    = ((μ A)⁻¹ • μ.restrict A).prod ((ν B)⁻¹ • ν.restrict B)
  rw [Measure.prod_prod, ← Measure.prod_restrict,
    ENNReal.mul_inv (Or.inr (measure_ne_top ν B)) (Or.inl (measure_ne_top μ A)),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- Conditioning a probability measure on a full-measure event does nothing. -/
theorem cond_eq_self (μ : Measure X) [IsProbabilityMeasure μ] {S : Set X}
    (hS : MeasurableSet S) (h : μ Sᶜ = 0) :
    ProbabilityTheory.cond μ S = μ := by
  have hfull : μ S = 1 := by
    have := measure_add_measure_compl (μ := μ) hS
    rw [h, add_zero] at this
    rw [this, measure_univ]
  show (μ S)⁻¹ • μ.restrict S = μ
  rw [hfull, inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem]
  rw [MeasureTheory.ae_iff]
  exact h

/-- **Bayes for finite mixtures**: conditioning a finite mixture of finite measures on an
event is the posterior-weighted mixture of the conditioned components — the posterior of
component `j` being its prior weight `cⱼ` times its likelihood `μⱼ S`, normalised by the
mixture's total mass on `S`. Zero-mass components contribute zero to both sides, and a
zero-mass mixture makes both sides the zero measure, so no positivity hypothesis is
needed. -/
theorem cond_finsetSum {ι : Type*} (s : Finset ι) (μ : ι → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (c : ι → ℝ≥0∞) {S : Set X} (hS : MeasurableSet S) :
    ProbabilityTheory.cond (∑ j ∈ s, c j • μ j) S
      = ∑ j ∈ s, (c j * μ j S / (∑ k ∈ s, c k • μ k) S)
          • ProbabilityTheory.cond (μ j) S := by
  ext A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    ProbabilityTheory.cond_apply hS]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : μ j S = 0
  · have hm : μ j (S ∩ A) = 0 := measure_mono_null Set.inter_subset_left hj
    simp [hj, hm]
  · have hfin : μ j S ≠ ⊤ := measure_ne_top _ _
    have hss : μ j S * (μ j S)⁻¹ = 1 := ENNReal.mul_inv_cancel hj hfin
    rw [div_eq_mul_inv]
    have hre : c j * μ j S * (∑ k ∈ s, c k * μ k S)⁻¹ * ((μ j S)⁻¹ * μ j (S ∩ A))
        = c j * (μ j S * (μ j S)⁻¹) * ((∑ k ∈ s, c k * μ k S)⁻¹ * μ j (S ∩ A)) := by
      ring
    rw [hre, hss, mul_one]
    ring

end ProbabilityTheory
