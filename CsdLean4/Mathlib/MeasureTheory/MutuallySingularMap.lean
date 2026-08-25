/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Mutual singularity pulls back along a measurable map

**Category:** 1-Mathlib (CSD-free upstream candidates).

`Measure.MutuallySingular.of_map` — if the pushforwards of `μ` and `ν` along a measurable
`f : α → β` are mutually singular, then `μ` and `ν` are mutually singular.

## Why this is not already in Mathlib

`Mathlib.MeasureTheory.Measure.MutuallySingular` carries the *forward* direction, and only for
embeddings: `MeasurableEmbedding.mutuallySingular_map` sends `μ ⟂ₘ ν` to `μ.map f ⟂ₘ ν.map f`,
using injectivity to push a separating set forward through `f '' ·`.

The direction here goes the other way and needs no embedding hypothesis, because a separating set is
*pulled back* rather than pushed forward: `f ⁻¹' B` is measurable whenever `B` is, preimage commutes
with complement, and `Measure.map_apply` converts each mapped-measure statement into a statement
about the preimage. Injectivity would be needed only to go forwards.

No finiteness, σ-finiteness or probability hypothesis is required.

## Provenance

Staged as upstream Mathlib material; no `CsdLean4`-namespace content.
-/

@[expose] public section

open Set

namespace MeasureTheory
namespace Measure
namespace MutuallySingular

variable {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}

/-- **Mutual singularity pulls back along a measurable map.** If `f` is measurable and the
pushforwards `f_* μ` and `f_* ν` are mutually singular, then so are `μ` and `ν`.

The separating set is the preimage of the one separating the pushforwards. -/
theorem of_map {μ ν : Measure α} {f : α → β} (hf : Measurable f)
    (h : (μ.map f).MutuallySingular (ν.map f)) :
    μ.MutuallySingular ν := by
  refine ⟨f ⁻¹' h.nullSet, hf h.measurableSet_nullSet, ?_, ?_⟩
  · rw [← Measure.map_apply hf h.measurableSet_nullSet]
    exact h.measure_nullSet
  · rw [← Set.preimage_compl, ← Measure.map_apply hf h.measurableSet_nullSet.compl]
    exact h.measure_compl_nullSet

end MutuallySingular
end Measure
end MeasureTheory
