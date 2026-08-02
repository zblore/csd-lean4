/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional-probability toolkit: pushforward, products, full-measure events

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

Three small lemmas about `ProbabilityTheory.cond` that Mathlib does not currently provide:

- `cond_map` — conditioning commutes with pushforward:
  `cond (f_*μ) S = f_* (cond μ (f⁻¹S))`.
- `cond_prod_prod` — conditioning a product measure on a product event conditions the
  factors independently.
- `cond_eq_self` — conditioning a probability measure on a full-measure event does nothing.

## Provenance

Extracted 2026-08-02 from `CsdLean4/SigmaLayer/JoinLuders.lean` (where they were proved for
the degenerate-Lüders conditioning bookkeeping); staged here for upstream. Naming and import
discipline track Mathlib idiom; intended target `Mathlib.Probability.ConditionalProbability`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Conditioning commutes with pushforward: `cond (f_*μ) S = f_* (cond μ (f⁻¹S))`. -/
theorem cond_map (μ : Measure X) {f : X → Y} (hf : Measurable f) {S : Set Y}
    (hS : MeasurableSet S) :
    ProbabilityTheory.cond (Measure.map f μ) S
      = Measure.map f (ProbabilityTheory.cond μ (f ⁻¹' S)) := by
  show ((Measure.map f μ) S)⁻¹ • (Measure.map f μ).restrict S
    = Measure.map f ((μ (f ⁻¹' S))⁻¹ • μ.restrict (f ⁻¹' S))
  rw [Measure.map_apply hf hS, Measure.restrict_map hf hS, Measure.map_smul]

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

end ProbabilityTheory
