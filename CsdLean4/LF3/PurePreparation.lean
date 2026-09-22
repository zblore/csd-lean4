/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.ContextMap
public import CsdLean4.LF3.SingletProjective
public import CsdLean4.LF2.Interface

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
design** (2026-05-18): the bridge is the ontic-weight to LF2 OP.p
identity, not the direct projective-measure form of v1.x. This matches
CSD's volume-ratio reading (probability is OP integration of
`effectProjFn` against the projective measure bridge) and preserves the
structural separation between the static pure preparation
(`LF2.PurePreparation`) and the measurement-context joint eigenstate
data (`LF3.MeasurementJointEig`).

**Posited-fibre-measure form (2026-05-25).** The ontic weight is now the
**posited fibre trial law** `μψ` (Paper A / Σ0, revised), not the
ambient `μL`-conditional `D.toOntic.prepMeasure`. The `μL`-conditional
form was *uninhabitable* alongside the measure bridge: a continuous
`π∗μL = c·μFS` makes every state's fibre `μL`-null, so a positive-measure
`μL`-conditional cannot push to the Dirac on `[ψ]`. `μψ` is posited extra
ontic structure on the fibre (no disintegration needed); it is the trial
law consumed directly by `LF1.freq_tendsto_of_iid`. See `LF4-todo §8`.

Concrete constructors now exist in `LF4/SingletKahler.lean`
(`LF4.ofKählerPreparation`) and `LF4/SingletKahlerFlow.lean`
(`LF4.ofKählerPreparationFlow`). They prove the calibration by carving
fibre regions with the prescribed weights. The latter also proves that
its fibre translation preserves the preparation law. The abstract bundle
still requires calibration from each caller.

## Proof boundary

`weight_eq_P_st` composes the supplied calibration with the direct
pure-state Born identity. `ofWeights` performs the reverse conversion
for constructors that already prove the pre-event masses. Both use
`OP_p_at_jointEig_eq_P_st_direct`; neither needs the effect-Gleason
representation theorem. The bridge structure introduces no axiom.

## API shape

Posited fibre law plus the auxiliary OP-construction data:
- `μψ : Measure SigmaSpace` + `hμψ_prob` — the **posited fibre trial
  law** over `[ψ]` (the preparation primitive; pushes to a Dirac on the
  ray, not a `μL`-conditional).
- `μFS : Measure P` — ambient projective reference measure; the OP integrates against `π_*μψ`.
- `hμFS_prob : IsProbabilityMeasure μFS` — μFS is a probability measure.
- `bridge : LF2.MeasureBridgeData D μFS` — the measure bridge.
- `PP : LF2.PurePreparation D μψ N` — the static pure preparation
  (ψ = singlet after re-indexing) over the posited fibre law.
- `hN : 2 ≤ N` — dimension bound retained for the trace-form API; unused by the direct chain.
- `jed : MeasurementJointEig ctx PP.ψ` — joint spin eigenstate data
  for the measurement context, with the Born identity
  `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`.
- `O_region : Sign → Sign → D.toOntic.OutcomeRegion` — ontic outcome
  regions for the (s, t) sectors.
- `bridge_op_p : ∀ s t, μψ((O_region s t).preEvent)
                      = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))`
  — the ontic weight ↔ OP.p calibration, proved by the concrete LF4 constructors.

`ofHypothesis` accepts the raw field set. `ofWeights` instead accepts
pre-event masses and derives the OP calibration once for both LF4 constructors.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace LF3

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- Bundled LF2 ↔ LF3 calibration data under the option (B) design,
    **posited-fibre-measure form** (2026-05-25): a posited pure-state
    trial law `μψ`, the static pure preparation `PP` over `μψ`, the
    measurement-context joint eigenstate data `jed`, ontic outcome
    regions, and the ontic-weight ↔ OP.p bridge `bridge_op_p` tying
    `μψ((O_region s t).preEvent)` to the operational-package probability
    of the rank-1 sector effect through `jed.eig s t`.

    ## Why `μψ` and not the `μL`-conditional `prepMeasure`

    Earlier revisions set the preparation law to `D.toOntic.prepMeasure`
    (the ambient `μL`-conditional on `Ω₀`). That form is **uninhabitable**
    in the presence of the measure bridge: under `π∗μL = c·μFS` (continuous
    projective reference), every single quantum state's fibre `π⁻¹([ψ])`
    is `μL`-null, so a `μL`-conditional cannot push through `π` to the
    Dirac on `[ψ]` that `PP.push_dirac` demands (that would force
    `μL(Ω₀) = 0`, contradicting `hΩ0_nonzero`). See `LF4-todo §8`.

    The fix (Paper A / Σ0, revised): the pure-state preparation is a
    **posited fibre probability measure** `μψ` — extra ontic structure
    concentrated on the fibre, *not* an `μL`-conditional. `μψ` pushes to
    the Dirac on `[ψ]` (so `PP.push_dirac` is satisfiable) while the
    ambient `μL` keeps its continuous bridge, separately. No
    disintegration machinery is required; `μψ` is the trial law directly,
    consumed by `LF1.freq_tendsto_of_iid` in the chain capstones.

    The concrete LF4 constructors inhabit this bundle for generic singlet
    contexts. No disjointness or coverage of `O_region` is required, and
    no fixed-ray condition on the flow is assumed: calibration concerns
    the actual pre-events `Φ⁻¹' Ω`. -/
structure PureSingletPreparation
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) (N : ℕ) where
  /-- **Posited fibre trial law** over the ray `[ψ]` (Paper A / Σ0,
      revised). A probability measure concentrated on the fibre
      `π⁻¹([ψ])`; pushes through `D.π` to the Dirac on the ray by
      `PP.push_dirac`. **Not** a `μL`-conditional — extra ontic
      structure, so no disintegration is needed. This is the trial law
      consumed by `LF1.freq_tendsto_of_iid`. -/
  μψ               : Measure SigmaSpace
  /-- `μψ` is a probability measure. -/
  hμψ_prob         : IsProbabilityMeasure μψ
  /-- Ambient projective reference measure; the OP integral uses `π_*μψ`. -/
  μFS              : Measure P
  /-- `μFS` is a probability measure. -/
  hμFS_prob        : IsProbabilityMeasure μFS
  /-- Measure bridge data (ambient `μL` ↔ `μFS`), supplied as proved
      structure fields. This is separate from the preparation pushforward. -/
  bridge           : CSD.LF2.MeasureBridgeData D μFS
  /-- LF2 pure preparation over the posited fibre law `μψ`: ψ = singlet
      (after re-indexing into `Fin N`), with rep and Dirac-concentration
      content `Measure.map D.π μψ = Measure.dirac ray_point`. -/
  PP               : CSD.LF2.PurePreparation D μψ N
  /-- Dimension bound retained for the trace-form API; the direct chain does not use it. -/
  hN               : 2 ≤ N
  /-- Measurement-context joint eigenstate data: the four (s, t) joint
      spin eigenstates with unit-norm, distinctness, and Born identity
      `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`. -/
  jed              : MeasurementJointEig ctx PP.ψ
  /-- Per-sector measurable ontic regions; disjointness and coverage are not fields. -/
  O_region         : Sign → Sign → D.toOntic.OutcomeRegion
  /-- Calibration of each pulled-back outcome event against its rank-one
      OP probability. `weight_eq_P_st` combines this field with the direct
      Born identity. Abstract callers must supply it; the LF4 stationary
      and fibre-flow constructors prove it from their carved-region masses.
      It does not assert that the regions form an outcome partition. -/
  bridge_op_p      : ∀ s t,
    μψ (O_region s t).preEvent
    = ENNReal.ofReal
        ((haveI := hμFS_prob
          haveI := hμψ_prob
          CSD.LF2.OperationalPackage.fromPreparation D μFS bridge μψ
            PP.rep PP.hrep_unit PP.hrep_meas).p
          (CSD.LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t)))

namespace PureSingletPreparation

/-- Build the bundle from its raw fields, including the OP calibration.
    Use `ofWeights` when pre-event masses have already been calculated. -/
def ofHypothesis
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext} {N : ℕ}
    (μψ : Measure SigmaSpace) (hμψ_prob : IsProbabilityMeasure μψ)
    (μFS : Measure P) (hμFS_prob : IsProbabilityMeasure μFS)
    (bridge : CSD.LF2.MeasureBridgeData D μFS)
    (PP : CSD.LF2.PurePreparation D μψ N)
    (hN : 2 ≤ N)
    (jed : MeasurementJointEig ctx PP.ψ)
    (O_region : Sign → Sign → D.toOntic.OutcomeRegion)
    (bridge_op_p : ∀ s t,
      μψ (O_region s t).preEvent
      = ENNReal.ofReal
          ((haveI := hμFS_prob
            haveI := hμψ_prob
            CSD.LF2.OperationalPackage.fromPreparation D μFS bridge μψ
              PP.rep PP.hrep_unit PP.hrep_meas).p
            (CSD.LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t)))) :
    PureSingletPreparation D ctx N :=
  { μψ := μψ
    hμψ_prob := hμψ_prob
    μFS := μFS
    hμFS_prob := hμFS_prob
    bridge := bridge
    PP := PP
    hN := hN
    jed := jed
    O_region := O_region
    bridge_op_p := bridge_op_p }

/-- Build the bundle from calibrated pre-event masses. The direct pure-state
    Born identity derives the OP bridge, so callers need only prove their
    measure calculation. This accepts arbitrary sector flow; the supplied
    weights must concern its actual pre-events. No partition is inferred. -/
def ofWeights
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext} {N : ℕ}
    (μψ : Measure SigmaSpace) (hμψ_prob : IsProbabilityMeasure μψ)
    (μFS : Measure P) (hμFS_prob : IsProbabilityMeasure μFS)
    (bridge : CSD.LF2.MeasureBridgeData D μFS)
    (PP : CSD.LF2.PurePreparation D μψ N)
    (hN : 2 ≤ N)
    (jed : MeasurementJointEig ctx PP.ψ)
    (O_region : Sign → Sign → D.toOntic.OutcomeRegion)
    (hweight : ∀ s t, μψ (O_region s t).preEvent
      = ENNReal.ofReal (P_st ctx.a ctx.b s t)) :
    PureSingletPreparation D ctx N := by
  haveI := hμψ_prob
  haveI := hμFS_prob
  refine ofHypothesis μψ hμψ_prob μFS hμFS_prob bridge PP hN jed O_region ?_
  intro s t
  rw [OP_p_at_jointEig_eq_P_st_direct D μFS bridge μψ PP jed s t]
  exact hweight s t

/-- Compose the supplied OP calibration with the direct pure-state Born
    identity to compute each pre-event's mass under `μψ`. The proof uses
    Dirac integration against `π_*μψ` and the bundle's Born-overlap identity;
    it does not derive the calibration from independent geometry. -/
theorem weight_eq_P_st
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext} {N : ℕ}
    (prep : PureSingletPreparation D ctx N) (s t : Sign) :
    prep.μψ (prep.O_region s t).preEvent
      = ENNReal.ofReal (P_st ctx.a ctx.b s t) := by
  have := prep.hμFS_prob
  have := prep.hμψ_prob
  rw [prep.bridge_op_p s t,
      OP_p_at_jointEig_eq_P_st_direct D prep.μFS prep.bridge prep.μψ
        prep.PP prep.jed s t]

end PureSingletPreparation

end LF3
end CSD
