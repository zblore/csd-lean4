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

* `SubMulAction.continuousConstSMul_staged`
* `Units.continuousConstSMul_nonZero_staged`

**Merged upstream; the names carry `_staged` until the pin moves.** Mathlib master declares both
instances under the unsuffixed names (`SubMulAction.continuousConstSMul`,
`Units.continuousConstSMul_nonZero`, `Mathlib/Topology/Algebra/MulAction.lean`), which made the
unsuffixed copies here a redeclaration error against master (Compat canary, 2026-10-26). With the
suffix the file builds on the pin, where it is the only source of the instances, and on master,
where it is a harmless duplicate. When the pin reaches a Mathlib containing the merge, delete this
file and its import, as below.

## Provenance

**This file is the Mathlib pull-request text verbatim** (the fourteen lines appended after
`Submonoid.continuousSMul` in `Mathlib/Topology/Algebra/MulAction.lean`), carried here so that
this repository and the pull request are the same code. Only the module-system header
(`module`, `public import`, `@[expose] public section`), this docstring and the two `_staged`
instance names differ, the first two required by this repository's lints. **Delete this file and drop the import when the pull request merges
and the pin moves**; nothing else here changes.
-/

@[expose] public section

/-- A `SubMulAction` inherits the continuity of the action of each element. -/
@[to_additive /-- A `SubAddAction` inherits the continuity of the action of each element. -/]
instance SubMulAction.continuousConstSMul_staged {M X : Type*} [TopologicalSpace X] [Monoid M]
    [MulAction M X] [ContinuousConstSMul M X] (p : SubMulAction M X) :
    ContinuousConstSMul M p :=
  ⟨fun c ↦ ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

/-- The units of `R` act continuously on the nonzero elements of `M` when they act continuously
on `M`. -/
instance Units.continuousConstSMul_nonZero_staged {R M : Type*} [TopologicalSpace M] [Monoid R]
    [AddCommMonoid M] [DistribMulAction R M] [ContinuousConstSMul Rˣ M] :
    ContinuousConstSMul Rˣ {x : M // x ≠ 0} :=
  inferInstanceAs (ContinuousConstSMul Rˣ (Units.nonZeroSubMul R M))
