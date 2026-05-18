import CsdLean4.LF2.MeasureBridge
import CsdLean4.LF2.EffectFn

/-!
# OP-from-preparation construction (pre-LF4 Phase 3)

**Category:** 3-Local (pre-LF4 plan Phase 3 sub-component 3a —
`MeasureBridgeData` bundle).

This module hosts the structural composition of LF2's two named axioms
through which `OperationalPackage.fromPreparation` will route in
sub-phase 3c. The current sub-phase 3a defines:

- `MeasureBridgeData D μFS` — a structure bundling the projective
  reference measure `μFS`, its G-invariance, the bridge constant
  `c : ENNReal`, and the bridge equality
  `Measure.map D.π D.μL = c • μFS`.
- `MeasureBridgeData.ofSectorData` — the primary constructor, fed by
  `measure_bridge`. Cites `invariant_measure_uniqueness`.

The architectural commitment per `specs/pre-LF4-plan.md` (option (b)):
the only callable construction route to a `MeasureBridgeData` for a
`SectorData`-derived setup is `ofSectorData`, so the symmetry axiom
propagates by type signature into any consumer of
`MeasureBridgeData D μFS`. Sub-phase 3c will use this to thread the
axiom citation into `OperationalPackage.fromPreparation` and thereby
into the LF3 chain capstones (Phase 7).
-/

open MeasureTheory

namespace CSD
namespace LF2

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **Measure-bridge data.** Bundles the projective reference measure
    `μFS`, its G-invariance, the bridge constant `c : ENNReal`, and the
    bridge equality `Measure.map D.π D.μL = c • μFS`. The primary
    constructor `ofSectorData` cites `invariant_measure_uniqueness` via
    `measure_bridge`; downstream consumers (notably
    `OperationalPackage.fromPreparation`) take a `MeasureBridgeData`
    argument and thereby propagate the symmetry-axiom citation by type
    signature.

    `μFS` is taken as an explicit (Type-level) field rather than carried
    in the structure because callers may want to instantiate the same
    `SectorData` with different reference measures; the
    `MeasureBridgeData` ties a specific `μFS` to its bridge facts. -/
structure MeasureBridgeData (D : SectorData SigmaSpace P G) (μFS : Measure P) where
  /-- Each epistemic action map `g • ·` preserves `μFS`. -/
  is_inv : ∀ g : G, MeasurePreserving ((g • ·) : P → P) μFS μFS
  /-- The bridge constant: `π_*μL = c • μFS`. -/
  c : ENNReal
  /-- The bridge equality. -/
  bridge_eq : Measure.map D.π D.μL = c • μFS

/-- **Primary constructor for `MeasureBridgeData`.** Given a `SectorData`,
    a G-invariant probability measure `μFS` on `P`, and the invariance
    hypothesis, extracts the bridge data from `measure_bridge`. This
    construction cites `invariant_measure_uniqueness` (via
    `measure_bridge`); any caller of `MeasureBridgeData.ofSectorData`
    inherits the axiom dependency. -/
noncomputable def MeasureBridgeData.ofSectorData
    (D : SectorData SigmaSpace P G) (μFS : Measure P)
    [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g : G, MeasurePreserving ((g • ·) : P → P) μFS μFS) :
    MeasureBridgeData D μFS where
  is_inv := hμFS_inv
  c := (measure_bridge D μFS hμFS_inv).choose
  bridge_eq := (measure_bridge D μFS hμFS_inv).choose_spec

end LF2
end CSD
