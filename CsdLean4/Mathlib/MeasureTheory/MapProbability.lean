/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Pushforward of a probability measure is a probability measure (compat spelling)

**Category:** 1-Mathlib (CSD-free). **Forward-compat shim.**

Mathlib master (2026-08-29) removed the named theorem
`Measure.isProbabilityMeasure_map` in favour of an unconditional `instance` on `μ.map f`
(no deprecation alias), while the pinned Mathlib has the theorem and not the instance.
This file states the fact once under a prime name, proved from the stable
`map_apply_of_aemeasurable` API so that it compiles against **both** trees; the five
corpus call sites route through it. When the pin advances past the master change, this
shim and its call sites collapse to `inferInstance` and the file can be deleted — noted
in `specs/validation-hardening-plan.md`'s canary discipline.
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

end MeasureTheory
