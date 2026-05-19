import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF2.Interface

/-!
# LF3 PureSingletPreparation: option (B) singlet OP-bridge bundle

**Category:** 3-Local (LF3 `PureSingletPreparation` bundle: pure-state
data + measurement-context joint eigenstate data + ontic-weight ↔ OP.p
bridge, hLF2 discharge target for LF4).

Paper boundary at the LF1 ↔ LF2 ↔ LF3 capstone (spec §10.5 / LF4-todo
§2 + §7).

The three `LF3_singlet_frequency_convergence*` capstones in
`Interface.lean` each take a load-bearing external hypothesis tying the
ontic outcome weight to the singlet kernel value `P_st ctx.a ctx.b s t`.
This module bundles that hypothesis under the **option (B) chain
design** (2026-05-18): the bridge is the LF1 ontic weight to LF2 OP.p
identity, not the direct projective-measure form of v1.x. This matches
CSD's volume-ratio reading (probability is OP integration of
`effectProjFn` against the projective measure bridge) and preserves the
structural separation between the static pure preparation
(`LF2.PurePreparation`) and the measurement-context joint eigenstate
data (`LF3.MeasurementJointEig`).

LF4 will eventually supply a concrete constructor
`PureSingletPreparation.ofKählerPreparation` from a concrete Kähler
`SectorData` instantiation (per LF4-todo §8) plus the preparation-to-
Hilbert correspondence (LF4-todo §2). At v1.x the bundle is the carrier
for the structural hypotheses.

## Three-category posture

- **Proved internally.** The structure definition and a transitional
  constructor `ofHypothesis`. No theorems proved here; the module
  bundles hypotheses.
- **Imported from upstream.** `MeasurementContext`, `MeasurementJointEig`,
  `LF2.PurePreparation`, `LF2.MeasureBridgeData`,
  `LF2.OperationalPackage.fromPreparation`.
- **Axiomatised at an explicit boundary.** Indirectly via the bridge:
  the LF3 chain capstones, after Phase 7, cite both
  `busch_effect_gleason` (via `pure_state_born_weights_of_certainty`
  inside the chain proof's OP.p ↔ Born identity step) and the foundational
  triple. `invariant_measure_uniqueness` propagates by type signature
  when callers construct `MeasureBridgeData` via
  `MeasureBridgeData.ofSectorData`.

## API shape

Six fields plus the auxiliary OP-construction data:
- `μFS : Measure P` — projective reference measure for the OP integral.
- `hμFS_prob : IsProbabilityMeasure μFS` — μFS is a probability measure.
- `bridge : LF2.MeasureBridgeData D μFS` — the measure bridge.
- `PP : LF2.PurePreparation D prepMeasure N` — the static pure
  preparation (ψ = singlet after re-indexing).
- `hN : 2 ≤ N` — dimension bound (needed for `busch_effect_gleason`).
- `jed : MeasurementJointEig ctx PP.ψ` — joint spin eigenstate data
  for the measurement context, with the Born identity
  `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`.
- `O_region : Sign → Sign → D.toOntic.OutcomeRegion` — ontic outcome
  regions for the (s, t) sectors.
- `bridge_op_p : ∀ s t, prepMeasure((O_region s t).preEvent)
                      = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))`
  — the ontic weight ↔ OP.p bridge. **LF4 discharge target.**

The transitional constructor `ofHypothesis` accepts the raw field set
for migrating existing callsites.
-/

open MeasureTheory

namespace CSD
namespace LF3

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- Bundled LF2 ↔ LF3 calibration data under the option (B) design:
    static pure preparation `PP`, measurement-context joint eigenstate
    data `jed`, ontic outcome regions, and the ontic-weight ↔ OP.p
    bridge `bridge_op_p` tying `prepMeasure((O_region s t).preEvent)` to
    the operational-package probability of the rank-1 sector effect
    through `jed.eig s t`.

    A v1.x carrier of the LF4 discharge target. LF4 will supply a
    concrete constructor; the transitional `ofHypothesis` constructor
    below lets callers migrate without yet having the LF4 content. -/
structure PureSingletPreparation
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) (N : ℕ) where
  /-- Projective reference measure for the OP construction. -/
  μFS              : Measure P
  /-- `μFS` is a probability measure. -/
  hμFS_prob        : IsProbabilityMeasure μFS
  /-- Measure bridge data. -/
  bridge           : CSD.LF2.MeasureBridgeData D μFS
  /-- LF2 pure preparation: ψ = singlet (after re-indexing into `Fin N`),
      with rep and Dirac-concentration content. -/
  PP               : CSD.LF2.PurePreparation D
    ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) N
  /-- Dimension bound, required for `busch_effect_gleason`. -/
  hN               : 2 ≤ N
  /-- Measurement-context joint eigenstate data: the four (s, t) joint
      spin eigenstates with unit-norm, distinctness, and Born identity
      `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`. -/
  jed              : MeasurementJointEig ctx PP.ψ
  /-- Per-sector ontic outcome regions. -/
  O_region         : Sign → Sign → D.toOntic.OutcomeRegion
  /-- **Major empirical hypothesis (LF4 discharge target): ontic-weight
      ↔ OP.p bridge.** The ontic `prepMeasure` of the pulled-back
      outcome event equals the operational-package probability of the
      rank-1 sector effect through `jed.eig s t`. Combined with
      `LF3.OP_p_at_jointEig_eq_P_st`, this gives convergence of trial
      frequencies to `P_st ctx.a ctx.b s t`.

      **Status: load-bearing, externally supplied, undischarged.**
      This field is the *single largest external hypothesis* in the
      LF1↔LF2↔LF3 empirical chain pre-LF4. It encodes the
      preparation-to-projective bridge plus the
      preparation-to-Hilbert correspondence (LF4-todo §2) plus the
      projective-first outcome construction (LF4-todo §7); the
      LF3 chain capstones are conditional on this hypothesis until
      LF4 supplies a concrete `SectorData` instantiation from which
      `bridge_op_p` follows. Callers should treat this field with
      the same scrutiny they would apply to an `axiom` — the bundle
      defers the question rather than answering it. -/
  bridge_op_p      : ∀ s t,
    ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        (O_region s t).preEvent
    = ENNReal.ofReal
        ((haveI := hμFS_prob
          CSD.LF2.OperationalPackage.fromPreparation D μFS bridge
            ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
            PP.rep PP.hrep_unit PP.hrep_meas).p
          (CSD.LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t)))

namespace PureSingletPreparation

/-- Transitional constructor: build a `PureSingletPreparation` from the
    raw field set. Existing callsites migrate by supplying their bridge
    + PP + jed + outcome regions + bridge_op_p hypothesis explicitly.
    LF4 will replace its use with `PureSingletPreparation.ofKählerPreparation`
    or similar, derived from a concrete `SectorData` instantiation plus
    the preparation-to-Hilbert correspondence. -/
def ofHypothesis
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext} {N : ℕ}
    (μFS : Measure P) (hμFS_prob : IsProbabilityMeasure μFS)
    (bridge : CSD.LF2.MeasureBridgeData D μFS)
    (PP : CSD.LF2.PurePreparation D
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace) N)
    (hN : 2 ≤ N)
    (jed : MeasurementJointEig ctx PP.ψ)
    (O_region : Sign → Sign → D.toOntic.OutcomeRegion)
    (bridge_op_p : ∀ s t,
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
          (O_region s t).preEvent
      = ENNReal.ofReal
          ((haveI := hμFS_prob
            CSD.LF2.OperationalPackage.fromPreparation D μFS bridge
              ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
              PP.rep PP.hrep_unit PP.hrep_meas).p
            (CSD.LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t)))) :
    PureSingletPreparation D ctx N :=
  { μFS := μFS
    hμFS_prob := hμFS_prob
    bridge := bridge
    PP := PP
    hN := hN
    jed := jed
    O_region := O_region
    bridge_op_p := bridge_op_p }

/-- **Ontic weight ↔ `P_st` identity (composed).** Combines
    `bridge_op_p` (the LF4 discharge target tying ontic outcome weight to
    the OP-derived integral) with `LF3.OP_p_at_jointEig_eq_P_st` (the
    Born-mediated algebra inside the OP integral). Result: the ontic
    `prepMeasure` of the pulled-back outcome event equals
    `ENNReal.ofReal (P_st ctx.a ctx.b s t)`. Cites `busch_effect_gleason`
    (via `OP_p_at_jointEig_eq_P_st`). -/
theorem weight_eq_P_st
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext} {N : ℕ}
    (prep : PureSingletPreparation D ctx N) (s t : Sign) :
    ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        (prep.O_region s t).preEvent
      = ENNReal.ofReal (P_st ctx.a ctx.b s t) := by
  haveI := prep.hμFS_prob
  rw [prep.bridge_op_p s t,
      OP_p_at_jointEig_eq_P_st D prep.μFS prep.bridge
        ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        prep.PP prep.hN prep.jed s t]

end PureSingletPreparation

end LF3
end CSD
