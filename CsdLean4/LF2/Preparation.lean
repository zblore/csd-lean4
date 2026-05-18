import CsdLean4.LF2.MeasureBridge
import CsdLean4.LF2.EffectFn
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-! ### Operational package from a preparation

`OperationalPackage.fromPreparation` constructs the operational
probability assignment by integrating the volume-forward effect function
`effectProjFn rep E` against the pushforward `Measure.map D.π μprep`.
The four operational-axiom fields (`nonneg`, `le_one`, `total_one`,
`additivity`) follow from the pointwise content of `effectProjFn` plus
standard Bochner integration facts.

The `MeasureBridgeData` argument is structural: even though the
`fromPreparation` proof body does not extensionally invoke
`bridge.bridge_eq` for the operational-axiom checks, callers must
construct a `MeasureBridgeData` to instantiate this definition, and
`MeasureBridgeData.ofSectorData` cites `invariant_measure_uniqueness`.
By the option (b) architectural commitment, this propagates the
symmetry axiom into the chain capstones.
-/

variable {N : ℕ}

/-- **`OperationalPackage.fromPreparation` (the volume-forward Born
    wrapper, structural form).** Given a `SectorData`, the bridge data
    `bridge : MeasureBridgeData D μFS`, a probability preparation
    measure `μprep`, and a unit-norm measurable representative
    `rep : P → EuclideanSpace ℂ (Fin N)`, the operational probability
    assignment is integration of `effectProjFn rep E` against the
    pushforward `π_*μprep`. -/
noncomputable def OperationalPackage.fromPreparation
    (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (rep : P → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep) :
    OperationalPackage N :=
  -- `bridge` is structurally present (its type propagates the symmetry-axiom
  -- citation by signature) but its bridge_eq content is not extensionally
  -- invoked by the operational-axiom field proofs. This is by design per
  -- the option (b) architectural commitment.
  let _ : MeasureBridgeData D μFS := bridge
  let μP : Measure P := Measure.map D.π μprep
  haveI : IsProbabilityMeasure μP :=
    Measure.isProbabilityMeasure_map D.measurable_π.aemeasurable
  {
    p := fun E => ∫ p, effectProjFn rep E p ∂μP
    nonneg := fun E =>
      MeasureTheory.integral_nonneg (fun p => effectProjFn_nonneg rep E p)
    le_one := fun E => by
      have h_le : ∀ p, effectProjFn rep E p ≤ 1 :=
        effectProjFn_le_one rep hrep_unit E
      have h_int_E : Integrable (effectProjFn rep E) μP :=
        effectProjFn_integrable rep hrep_unit hrep_meas E μP
      have h_int_one : Integrable (fun _ : P => (1 : ℝ)) μP :=
        integrable_const 1
      calc ∫ p, effectProjFn rep E p ∂μP
          ≤ ∫ _ : P, (1 : ℝ) ∂μP :=
            MeasureTheory.integral_mono h_int_E h_int_one h_le
        _ = (μP.real Set.univ) * 1 := by
            rw [MeasureTheory.integral_const, smul_eq_mul]
        _ = 1 := by simp
    total_one := by
      show ∫ p, effectProjFn rep Effect.one p ∂μP = 1
      have h_const : (fun p => effectProjFn rep Effect.one p) = (fun _ : P => (1 : ℝ)) := by
        funext p
        rw [effectProjFn_one, hrep_unit p]
        norm_num
      rw [h_const, MeasureTheory.integral_const, smul_eq_mul]
      simp
    additivity := fun E F hLe => by
      show ∫ p, effectProjFn rep (Effect.add E F hLe) p ∂μP
            = (∫ p, effectProjFn rep E p ∂μP) + (∫ p, effectProjFn rep F p ∂μP)
      have h_add : (fun p => effectProjFn rep (Effect.add E F hLe) p)
                 = (fun p => effectProjFn rep E p + effectProjFn rep F p) :=
        funext (fun p => effectProjFn_add rep E F hLe p)
      rw [h_add]
      exact MeasureTheory.integral_add
        (effectProjFn_integrable rep hrep_unit hrep_meas E μP)
        (effectProjFn_integrable rep hrep_unit hrep_meas F μP)
  }

end LF2
end CSD
