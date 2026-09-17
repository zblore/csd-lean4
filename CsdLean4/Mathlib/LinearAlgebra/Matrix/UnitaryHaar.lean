/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Haar probability measure on the matrix unitary group

**Category:** 1-Mathlib (CSD-free).

`Matrix.unitaryGroup ι ℂ` is a compact Hausdorff topological group with a Borel structure
(`UnitaryCompact.lean`), so Mathlib's Haar measure is available on it, and `haarMeasure ⊤` — the
Haar measure normalised to give the whole group mass `1` — is its Haar probability measure.

* `unitaryHaarProb` — that measure, under the name every consumer uses (the Fubini–Study measure
  on `ℂℙ^{N-1}` is its pushforward along an orbit map, `Projectivization/FubiniStudy.lean`);
* `instIsProbabilityMeasureUnitaryHaarProb`, `unitaryHaarProb_isHaarMeasure` — the two instances,
  both inherited from Mathlib (`haarMeasure_self`, `isHaarMeasure_haarMeasure`). Right-invariance,
  from uniqueness on a compact group, is `instIsMulRightInvariantUnitaryHaarProb`
  (`FubiniStudyUnique.lean`).

Until 2026-09-16 this file re-built the measure by hand (`(haar univ)⁻¹ • haar`) and re-proved both
instances; the external review of the Physlib closure flagged the duplication.
-/

@[expose] public section

open MeasureTheory

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Haar probability measure on `U(N)`**: Mathlib's `haarMeasure ⊤`, the Haar measure
normalised so that the whole (compact) group has mass `1`. -/
noncomputable def unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ) :=
  Measure.haarMeasure ⊤

/-- `unitaryHaarProb` is a probability measure: `haarMeasure K₀ K₀ = 1` at `K₀ = ⊤`. -/
instance instIsProbabilityMeasureUnitaryHaarProb :
    IsProbabilityMeasure (unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ)) where
  measure_univ := by
    rw [unitaryHaarProb, ← TopologicalSpace.PositiveCompacts.coe_top]
    exact Measure.haarMeasure_self

/-- `unitaryHaarProb` is a Haar measure (Mathlib's `isHaarMeasure_haarMeasure`). -/
instance unitaryHaarProb_isHaarMeasure :
    Measure.IsHaarMeasure (unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ)) :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure ⊤))

end Matrix.UnitaryGroup
