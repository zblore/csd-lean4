/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Pushforward compat shims: probability of a map, and map of a smul

**Category:** 1-Mathlib (CSD-free). **Forward-compat shims.**

Mathlib master (2026-08-29) reworked `Measure.map`'s junk value for non-measurable
maps, with two knock-on breaks against the pin (both caught by the Compat canary):

* The pinned tree's named theorem for "pushforward of a probability measure is a
  probability measure" (spelled `Measure.isProbabilityMeasure_map` there) was removed on
  master in favour of an unconditional `instance` on `μ.map f`, with no deprecation
  alias; the pin has the theorem and not the instance. `isProbabilityMeasure_map'`
  states the fact once, proved from the stable `map_apply_of_aemeasurable` API.
* `Measure.map_smul` gained a measurability hypothesis (the unconditional form is
  false under the new junk value), so pin-shaped `rw`/`simp` uses stop firing on
  master. `map_smul'` takes `Measurable f` — every corpus site has it in hand — and is
  proved by `ext` from the stable `map_apply`/`smul_apply` API.

All corpus call sites route through these spellings. When the pin advances past the
master change, the shims collapse to `inferInstance` / master's `Measure.map_smul` and
this file can be deleted — noted in `specs/validation-hardening-plan.md`'s canary log.
-/

@[expose] public section

namespace MeasureTheory

/-- The pushforward of a probability measure along an a.e.-measurable map is a probability
measure. Compat spelling of the fact that Mathlib master provides as an instance and the
pinned Mathlib as `Measure.isProbabilityMeasure_map`. -/
theorem Measure.isProbabilityMeasure_map' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  ⟨by rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

/-- Pushforward of a scaled measure along a measurable map, compat spelling: the pinned
Mathlib's `Measure.map_smul` is unconditional, master's takes a measurability
hypothesis — this form compiles against both. -/
theorem Measure.map_smul' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ENNReal) (μ : Measure α) {f : α → β} (hf : Measurable f) :
    (c • μ).map f = c • μ.map f := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hf hs, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hf hs]

end MeasureTheory
