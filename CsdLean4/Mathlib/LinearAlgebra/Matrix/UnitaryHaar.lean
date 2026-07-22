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
# Haar measure on the matrix unitary group

**Category:** 1-Mathlib (CSD-free Mathlib smoke test).

This file verifies that Mathlib's Haar measure infrastructure
(`MeasureTheory.Measure.haar`) is callable on
`Matrix.unitaryGroup (Fin N) ℂ` once the topology/compactness/measurability
instances from `UnitaryCompact.lean` are in place.

## The chain

For `haar : Measure G` to typecheck, Lean needs:
1. `Group G` — Mathlib's `Matrix.unitaryGroup` is a `Group` (subgroup of units).
2. `TopologicalSpace G` — inherited from `Matrix _ _ ℂ` via the subtype topology.
3. `IsTopologicalGroup G` — Mathlib generic from `Topology/Algebra/Star/Unitary.lean`.
4. `MeasurableSpace G` — installed by `UnitaryCompact.instMeasurableSpace`.
5. `BorelSpace G` — installed by `UnitaryCompact.instBorelSpace`.
6. `LocallyCompactSpace G` — chains automatically: `CompactSpace`
   (`UnitaryCompact.instCompactSpace`) gives `WeaklyLocallyCompactSpace`
   (Mathlib priority-100 instance), which gives `LocallyCompactSpace`
   in the presence of `R1Space` (implied by `T2Space`, which the
   subtype inherits from `Matrix _ _ ℂ`).

## Verified

- `unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ)` — the chosen
  Haar measure.
- `IsHaarMeasure unitaryHaar` — left-invariant + finite on compacts +
  positive on nonempty opens.
- `IsFiniteMeasure unitaryHaar` — the whole space is compact, so the
  Haar measure is finite.

## What this unlocks

With Mathlib's Haar measure callable, the next steps for LF4 are
normalisation to a probability measure (deferred to a follow-up
tranche) and the Fubini-Study pushforward to `ℂℙ^{N-1}`.

## Tags

unitary group, Haar measure, compact group
-/

@[expose] public section

open MeasureTheory

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-- A chosen Haar measure on the matrix unitary group `Matrix.unitaryGroup (Fin N) ℂ`.
This is `MeasureTheory.Measure.haar` specialised. -/
noncomputable def unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
  Measure.haar

/-- `unitaryHaar` is a Haar measure (left-invariant + regular + positive on opens + finite on compacts). -/
instance unitaryHaar_isHaarMeasure :
    Measure.IsHaarMeasure (unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ)) :=
  inferInstanceAs (Measure.IsHaarMeasure Measure.haar)

/-- `unitaryHaar` is finite (because the whole group is compact). -/
instance instIsFiniteMeasureUnitaryHaar :
    IsFiniteMeasure (unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ)) := by
  unfold unitaryHaar
  infer_instance

/-! ## Smoke-test usage

Confirms that the typeclass chain (CompactSpace → WeaklyLocallyCompactSpace
→ LocallyCompactSpace given T2; plus IsTopologicalGroup, MeasurableSpace,
BorelSpace) fires correctly. The four examples below all elaborate via
`inferInstance`; each is a witness that Lean can synthesise the
corresponding fact about the Haar measure. -/

example {N : ℕ} : LocallyCompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

example {N : ℕ} : IsTopologicalGroup (Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

example {N : ℕ} : T2Space (Matrix.unitaryGroup (Fin N) ℂ) := inferInstance

example {N : ℕ} : Measure.IsHaarMeasure (Measure.haar : Measure (Matrix.unitaryGroup (Fin N) ℂ)) :=
  inferInstance

/-! ## Normalisation to a probability measure

`unitaryHaar` is finite (compact group) and gives positive mass to
the whole space (Haar measure on a nonempty open set is positive).
We can therefore rescale by `(unitaryHaar Set.univ)⁻¹` to obtain a
probability measure that is still Haar (Haar property is preserved
under positive finite scaling).

The resulting `unitaryHaarProb` is the canonical SU(N)-invariant
probability measure on the matrix unitary group, and the
ingredient that the Fubini-Study measure on `ℂℙ^{N-1}` will be
constructed from via pushforward (next tranche).
-/

/-- The total mass `unitaryHaar Set.univ` is nonzero, because `Set.univ`
is a nonempty open set and Haar measure is `IsOpenPosMeasure`. -/
lemma unitaryHaar_univ_ne_zero :
    unitaryHaar (Set.univ : Set (Matrix.unitaryGroup (Fin N) ℂ)) ≠ 0 :=
  isOpen_univ.measure_ne_zero unitaryHaar Set.univ_nonempty

/-- The total mass `unitaryHaar Set.univ` is finite, because the group
is compact and Haar measure is `IsFiniteMeasureOnCompacts`. -/
lemma unitaryHaar_univ_ne_top :
    unitaryHaar (Set.univ : Set (Matrix.unitaryGroup (Fin N) ℂ)) ≠ ⊤ :=
  measure_ne_top _ _

/-- The probability-normalised Haar measure on the matrix unitary group.

Defined as `(unitaryHaar Set.univ)⁻¹ • unitaryHaar`. Both `IsProbabilityMeasure`
and `IsHaarMeasure` are instances; see `instIsProbabilityMeasureUnitaryHaarProb`
and `unitaryHaarProb_isHaarMeasure` below. -/
noncomputable def unitaryHaarProb : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
  ((unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ)) Set.univ)⁻¹ •
    (unitaryHaar : Measure (Matrix.unitaryGroup (Fin N) ℂ))

/-- `unitaryHaarProb` is a probability measure. -/
instance instIsProbabilityMeasureUnitaryHaarProb :
    IsProbabilityMeasure
      (unitaryHaarProb : Measure (Matrix.unitaryGroup (Fin N) ℂ)) where
  measure_univ := by
    unfold unitaryHaarProb
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel unitaryHaar_univ_ne_zero unitaryHaar_univ_ne_top

/-- `unitaryHaarProb` is a Haar measure (scaling by a finite positive
constant preserves the Haar property via `IsHaarMeasure.smul`). -/
instance unitaryHaarProb_isHaarMeasure :
    Measure.IsHaarMeasure
      (unitaryHaarProb : Measure (Matrix.unitaryGroup (Fin N) ℂ)) := by
  unfold unitaryHaarProb
  exact Measure.IsHaarMeasure.smul unitaryHaar
    (ENNReal.inv_ne_zero.mpr unitaryHaar_univ_ne_top)
    (ENNReal.inv_ne_top.mpr unitaryHaar_univ_ne_zero)

end Matrix.UnitaryGroup
