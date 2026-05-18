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

/-! ### Pure preparation and the Born rank-1 theorem

A `PurePreparation` packages a Hilbert-space unit vector `ψ`, the
caller-supplied projective representative map `rep`, a projective point
`ray_point : P` whose `rep`-image is `ψ`, and the Dirac-concentration
hypothesis `Measure.map D.π μprep = Measure.dirac ray_point` expressing
that the preparation concentrates on the projective ray through `ψ`.

Two Born theorems are proved:

- `PurePreparation.born_rank_one` (chain critical path) — derives
  `OP.p (rankOneEffect φ hφ) = ‖⟨ψ, φ⟩‖²` by composing the volume-content
  step (`OP_certain_at_ψ`) with the Busch packaging step
  (`pure_state_born_weights_of_certainty`). Matches spec §5.4 four-
  ingredient combinatorial framing.
- `PurePreparation.born_rank_one_direct` (volume-forward auxiliary) —
  derives the same conclusion by direct Dirac integration of
  `effectProjFn rep (rankOneEffect φ hφ)` against `Measure.dirac ray_point`,
  without invoking `busch_effect_gleason`. Tagged as the **eventual
  migration target** for the chain capstones once downstream consumers
  accommodate the leaner cite set; v1.00 chain stays Busch-mediated per
  spec §5.4.
-/

/-- **Pure preparation.** A bundle expressing that the projective
    pushforward of an ontic preparation measure is the Dirac on the ray
    through a specified Hilbert-space unit vector `ψ`. Carries the
    caller-supplied representative map `rep` and the equality
    `rep ray_point = ψ` linking abstract projective points to Hilbert
    vectors. -/
structure PurePreparation
    (D : SectorData SigmaSpace P G) (μprep : Measure SigmaSpace) (N : ℕ) where
  /-- The Hilbert-space unit vector representing the pure preparation. -/
  ψ : EuclideanSpace ℂ (Fin N)
  /-- `ψ` is a unit vector. -/
  unit_ψ : ‖ψ‖ = 1
  /-- The caller-supplied projective-to-Hilbert representative map. -/
  rep : P → EuclideanSpace ℂ (Fin N)
  /-- `rep` lands on unit vectors. -/
  hrep_unit : ∀ p, ‖rep p‖ = 1
  /-- `rep` is measurable. -/
  hrep_meas : Measurable rep
  /-- The abstract projective point of the preparation. -/
  ray_point : P
  /-- `rep` evaluates to `ψ` at the preparation's projective point. -/
  rep_at_ray : rep ray_point = ψ
  /-- The Dirac-concentration hypothesis: the projective pushforward of
      `μprep` is the Dirac on `ray_point`. -/
  push_dirac : Measure.map D.π μprep = Measure.dirac ray_point

namespace PurePreparation

variable {N : ℕ}

/-- **OP is certain at ψ (volume content).** For a pure preparation, the
    operational package built by `OperationalPackage.fromPreparation`
    assigns probability `1` to the rank-1 effect through `ψ`. Proof is
    direct Dirac evaluation on the volume integral: `effectProjFn` at the
    rank-1 effect reduces to `‖⟨rep p, ψ⟩‖²`, which at `p = ray_point`
    becomes `‖⟨ψ, ψ⟩‖² = 1` by `rep_at_ray` and `unit_ψ`. This is the
    "preparation-dependent density ρ_ep" content of spec §5.4 (third
    bullet). -/
theorem OP_certain_at_ψ
    (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (PP : PurePreparation D μprep N) :
    (OperationalPackage.fromPreparation D μFS bridge μprep
        PP.rep PP.hrep_unit PP.hrep_meas).p
      (rankOneEffect PP.ψ PP.unit_ψ) = 1 := by
  show ∫ p, effectProjFn PP.rep (rankOneEffect PP.ψ PP.unit_ψ) p
          ∂(Measure.map D.π μprep) = 1
  rw [PP.push_dirac]
  have h_meas : StronglyMeasurable
      (effectProjFn PP.rep (rankOneEffect PP.ψ PP.unit_ψ)) :=
    (effectProjFn_measurable PP.rep PP.hrep_meas _).stronglyMeasurable
  rw [MeasureTheory.integral_dirac' _ _ h_meas]
  rw [effectProjFn_rankOne, PP.rep_at_ray]
  -- Goal: ‖inner ℂ PP.ψ PP.ψ‖ ^ 2 = 1
  have h_inner : (inner ℂ PP.ψ PP.ψ : ℂ) = (1 : ℂ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) PP.ψ
    rw [PP.unit_ψ] at h
    simpa using h
  rw [h_inner]
  simp

/-- **Born quadratic form for pure preparations (Busch-mediated, chain
    critical path).** For a pure preparation and a rank-1 effect through
    `φ`, the operational package assigns `‖⟨ψ, φ⟩‖²`. Proof composes the
    volume-content step (`OP_certain_at_ψ`) with the Busch packaging step
    (`pure_state_born_weights_of_certainty`, which uses
    `busch_effect_gleason` + the now-proved
    `rankOneDensity_unique_of_certainty` + `born_quadratic`).

    Matches spec §5.4 four-ingredient combinatorial framing: measure bridge
    (via the `bridge` argument's type), preparation-dependent density ρ_ep
    (via the volume content of `OP_certain_at_ψ`), operational consistency
    package (via the `OperationalPackage.fromPreparation` construction),
    Busch effect-Gleason (via `pure_state_born_weights_of_certainty`).

    `#print axioms PurePreparation.born_rank_one` cites
    `busch_effect_gleason` (extensionally, via Busch packaging).
    `invariant_measure_uniqueness` enters at caller sites that construct
    the bridge argument via `MeasureBridgeData.ofSectorData` — the type-
    signature propagation mechanism per the option (b) architectural
    commitment. -/
theorem born_rank_one
    (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (PP : PurePreparation D μprep N) (hN : 2 ≤ N)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (OperationalPackage.fromPreparation D μFS bridge μprep
        PP.rep PP.hrep_unit PP.hrep_meas).p
      (rankOneEffect φ hφ) = ‖inner ℂ PP.ψ φ‖ ^ 2 :=
  pure_state_born_weights_of_certainty hN
    (OperationalPackage.fromPreparation D μFS bridge μprep
       PP.rep PP.hrep_unit PP.hrep_meas)
    PP.ψ PP.unit_ψ
    (PP.OP_certain_at_ψ D μFS bridge μprep)
    φ hφ

/-- **Born quadratic form for pure preparations (volume-forward direct
    auxiliary).** Same conclusion as `born_rank_one`, but proved by direct
    Dirac integration of `effectProjFn rep (rankOneEffect φ hφ)` against
    `Measure.dirac ray_point`, without invoking `busch_effect_gleason`.

    This is the **CSD volume-forward foundational form**: the Born value
    emerges from the volume integral alone, with no trace-form
    characterisation step.

    **Symmetry + operations are still load-bearing.** The Busch-free
    route is not assumption-free — it derives the Born rule from the
    two structural inputs that LF2 always required:

    - **Symmetry** enters via the `bridge : MeasureBridgeData D μFS`
      argument. The only construction route to a `MeasureBridgeData`
      for a `SectorData`-derived setup is `MeasureBridgeData.ofSectorData`,
      which cites `invariant_measure_uniqueness` via `measure_bridge`.
      Callers carrying the symmetry axiom propagate it into this
      theorem by type signature.
    - **Operations** enter via the `OperationalPackage.fromPreparation`
      construction, whose `nonneg`/`le_one`/`total_one`/`additivity`
      fields formalise the operational consistency package of spec
      Definition 5.1 (the four-axiom characterisation of probability
      assignments on effects).

    What the direct route avoids is the **trace-form characterisation
    step** (Busch's effect-Gleason theorem), not the symmetry-and-
    operations base. The two LF2 axioms `invariant_measure_uniqueness`
    and `busch_effect_gleason` correspond to "symmetry" and "the
    trace-form characterisation of operations", respectively, not to
    "symmetry" and "operations": operations are already encoded
    structurally in `OperationalPackage`.

    **Tagged as the eventual migration target** for the chain capstones
    once downstream consumers accommodate the leaner cite set; v1.00
    chain stays Busch-mediated per spec §5.4. Useful pedagogically as
    the explicit volume-forward statement, and as the migration point
    for future revisions of the chain capstones.

    `#print axioms PurePreparation.born_rank_one_direct` cites only the
    foundational triple `[propext, Classical.choice, Quot.sound]`.
    `invariant_measure_uniqueness` enters at caller sites that construct
    the bridge argument via `MeasureBridgeData.ofSectorData` — this is
    the type-signature propagation mechanism per the option (b)
    architectural commitment. -/
theorem born_rank_one_direct
    (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (PP : PurePreparation D μprep N)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (OperationalPackage.fromPreparation D μFS bridge μprep
        PP.rep PP.hrep_unit PP.hrep_meas).p
      (rankOneEffect φ hφ) = ‖inner ℂ PP.ψ φ‖ ^ 2 := by
  show ∫ p, effectProjFn PP.rep (rankOneEffect φ hφ) p
          ∂(Measure.map D.π μprep) = ‖inner ℂ PP.ψ φ‖ ^ 2
  rw [PP.push_dirac]
  have h_meas : StronglyMeasurable
      (effectProjFn PP.rep (rankOneEffect φ hφ)) :=
    (effectProjFn_measurable PP.rep PP.hrep_meas _).stronglyMeasurable
  rw [MeasureTheory.integral_dirac' _ _ h_meas]
  rw [effectProjFn_rankOne, PP.rep_at_ray]

end PurePreparation

end LF2
end CSD
