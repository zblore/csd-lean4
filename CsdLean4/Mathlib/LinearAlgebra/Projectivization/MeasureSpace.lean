import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable structure on projectivization

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidates).

Under `[RCLike K]` and finite-dimensional normed `V`, the projectivization
`ℙ K V` carries a canonical Borel `MeasurableSpace` structure derived from
its quotient topology (`Topology.lean`). This file installs:

- `Projectivization.instMeasurableSpace`: the Borel σ-algebra from the
  quotient topology.
- `Projectivization.instBorelSpace`: witness that the installed
  measurable space coincides with `borel _` (definitionally `rfl`).
- `Projectivization.instMeasurableSingletonClass`: every singleton is
  measurable, from `T2Space` (closed singletons) + `BorelSpace`.
- `Projectivization.measurable_mk'`: the canonical surjection is
  measurable, from its continuity (`Topology.lean`'s `continuous_mk'`)
  via `Continuous.measurable`.

The coincidence lemma (Borel σ-algebra equals the coinduced σ-algebra
from `mk'`), `lift_measurable`, and the measurability-characterisation
lemma are deferred to a follow-up; see `specs/projectivization-plan.md`
§4.2, §4.5, §4.6.

## Provenance

Staged as upstream Mathlib material. All declarations live under
`namespace Projectivization` with no `CsdLean4`-namespace prefix; the
file is intended to land in
`Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` once usage
stabilises. Discharges items 4.1, 4.3, 4.4 of `specs/projectivization-plan.md`.

## Hypothesis pattern

`[RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]`,
matching the `Topology.lean` `NormedFiniteDim` section. Under these
hypotheses, `ℙ K V` is a compact Hausdorff space; the Borel σ-algebra is
the natural measurable structure.

## Tags

projectivization, projective space, Borel measurable space
-/

open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

/-- Second-countability of `Projectivization K V`. Free consequence of
the open-quotient-map structure (`Topology.lean`'s `isOpenMap_mk'` +
`isQuotientMap_mk'`) and second-countability of the source: `V` is
second-countable (finite-dim normed over `RCLike` is proper via
`FiniteDimensional.proper_rclike`, and proper metric spaces are
second-countable via `secondCountable_of_proper`), so the open subtype
`{v : V // v ≠ 0}` is second-countable
(`Subtype.secondCountableTopology`), and the open quotient map carries
that to `ℙ K V` (`Topology.IsQuotientMap.secondCountableTopology`). -/
instance instSecondCountableTopology : SecondCountableTopology (ℙ K V) := by
  haveI : ProperSpace V := FiniteDimensional.proper_rclike K V
  exact isQuotientMap_mk'.secondCountableTopology isOpenMap_mk'

/-- The Borel σ-algebra on `Projectivization K V`, derived from its
quotient topology (`Topology.lean`).

Gated on `[RCLike K]` and finite-dim normed `V` so it does not shadow
the generic `Quotient.instMeasurableSpace` in algebraic-geometry
contexts (where `K` is an abstract field and the analytic structure is
not relevant). -/
instance instMeasurableSpace : MeasurableSpace (ℙ K V) := borel _

/-- `Projectivization K V` is a `BorelSpace`: the installed measurable
space agrees with `borel _` by definition. -/
instance instBorelSpace : BorelSpace (ℙ K V) := ⟨rfl⟩

/-- Singletons in `ℙ K V` are measurable. Follows from T2 (closed
singletons; established in `Topology.lean`'s
`Projectivization.instT2Space`) plus the Borel structure (closed sets
are measurable). -/
instance instMeasurableSingletonClass : MeasurableSingletonClass (ℙ K V) :=
  ⟨fun _ => (isClosed_singleton).measurableSet⟩

omit [FiniteDimensional K V] in
/-- The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is measurable.
Follows from continuity (`Topology.lean`'s `continuous_mk'`) via
`Continuous.measurable`.

Stated under additional `[MeasurableSpace V] [BorelSpace V]` hypotheses
so the source subtype `{v : V // v ≠ 0}` inherits a Borel `MeasurableSpace`
via `Subtype.borelSpace`. Most callers will supply these (typically via
`borelize V`); the resulting `MeasurableSpace V` agrees with `borel V`. -/
theorem measurable_mk' [MeasurableSpace V] [BorelSpace V] :
    Measurable (mk' K : { v : V // v ≠ 0 } → ℙ K V) :=
  continuous_mk'.measurable

end Projectivization
