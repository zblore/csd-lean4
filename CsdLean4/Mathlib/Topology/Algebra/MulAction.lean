/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Topology.Algebra.MulAction

/-!
# Continuity of the action on a `SubMulAction`

**Category:** 1-Mathlib (CSD-free; staged for upstream).

Two instances that Mathlib's `Mathlib/Topology/Algebra/MulAction.lean` does not carry at this
pin: a `SubMulAction` inherits the continuity of each element's action, and the units of `R`
therefore act continuously on the nonzero elements of `M` whenever they act continuously on `M`
(through Mathlib's own `Units.nonZeroSubMul`). The second is what makes the quotient map of
`Projectivization` an open map with no hypothesis beyond continuity of the scalar action.

* `SubMulAction.continuousConstSMul`
* `Units.continuousConstSMul_nonZero`

## Provenance

**This file is the Mathlib pull-request text verbatim** (the fourteen lines appended after
`Submonoid.continuousSMul` in `Mathlib/Topology/Algebra/MulAction.lean`), carried here so that
this repository and the pull request are the same code. Only the module-system header
(`module`, `public import`, `@[expose] public section`) and this docstring differ, both required
by this repository's lints. **Delete this file and drop the import when the pull request merges
and the pin moves**; nothing else here changes.
-/

@[expose] public section

/-- A `SubMulAction` inherits the continuity of the action of each element. -/
@[to_additive /-- A `SubAddAction` inherits the continuity of the action of each element. -/]
instance SubMulAction.continuousConstSMul {M X : Type*} [TopologicalSpace X] [Monoid M]
    [MulAction M X] [ContinuousConstSMul M X] (p : SubMulAction M X) :
    ContinuousConstSMul M p :=
  ⟨fun c ↦ ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

/-- The units of `R` act continuously on the nonzero elements of `M` when they act continuously
on `M`. -/
instance Units.continuousConstSMul_nonZero {R M : Type*} [TopologicalSpace M] [Monoid R]
    [AddCommMonoid M] [DistribMulAction R M] [ContinuousConstSMul Rˣ M] :
    ContinuousConstSMul Rˣ {x : M // x ≠ 0} :=
  inferInstanceAs (ContinuousConstSMul Rˣ (Units.nonZeroSubMul R M))
