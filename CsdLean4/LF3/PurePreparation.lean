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

Posited fibre law plus the auxiliary OP-construction data:
- `μψ : Measure SigmaSpace` + `hμψ_prob` — the **posited fibre trial
  law** over `[ψ]` (the preparation primitive; pushes to a Dirac on the
  ray, not a `μL`-conditional).
- `μFS : Measure P` — projective reference measure for the OP integral.
- `hμFS_prob : IsProbabilityMeasure μFS` — μFS is a probability measure.
- `bridge : LF2.MeasureBridgeData D μFS` — the measure bridge.
- `PP : LF2.PurePreparation D μψ N` — the static pure preparation
  (ψ = singlet after re-indexing) over the posited fibre law.
- `hN : 2 ≤ N` — dimension bound (needed for `busch_effect_gleason`).
- `jed : MeasurementJointEig ctx PP.ψ` — joint spin eigenstate data
  for the measurement context, with the Born identity
  `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`.
- `O_region : Sign → Sign → D.toOntic.OutcomeRegion` — ontic outcome
  regions for the (s, t) sectors.
- `bridge_op_p : ∀ s t, μψ((O_region s t).preEvent)
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

    A v1.x carrier of the LF4 discharge target. LF4 will supply a
    concrete constructor; the transitional `ofHypothesis` constructor
    below lets callers migrate without yet having the LF4 content. -/
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
  /-- Projective reference measure for the OP construction. -/
  μFS              : Measure P
  /-- `μFS` is a probability measure. -/
  hμFS_prob        : IsProbabilityMeasure μFS
  /-- Measure bridge data (ambient `μL` ↔ `μFS`). Type-level in the OP;
      carries the symmetry axiom by the canonical-constructor discipline. -/
  bridge           : CSD.LF2.MeasureBridgeData D μFS
  /-- LF2 pure preparation over the posited fibre law `μψ`: ψ = singlet
      (after re-indexing into `Fin N`), with rep and Dirac-concentration
      content `Measure.map D.π μψ = Measure.dirac ray_point`. -/
  PP               : CSD.LF2.PurePreparation D μψ N
  /-- Dimension bound, required for `busch_effect_gleason`. -/
  hN               : 2 ≤ N
  /-- Measurement-context joint eigenstate data: the four (s, t) joint
      spin eigenstates with unit-norm, distinctness, and Born identity
      `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`. -/
  jed              : MeasurementJointEig ctx PP.ψ
  /-- Per-sector ontic outcome regions. -/
  O_region         : Sign → Sign → D.toOntic.OutcomeRegion
  /-- **Major empirical hypothesis (LF4 discharge target): ontic-weight
      ↔ OP.p bridge.** The posited-fibre-law `μψ` of the pulled-back
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
    μψ (O_region s t).preEvent
    = ENNReal.ofReal
        ((haveI := hμFS_prob
          haveI := hμψ_prob
          CSD.LF2.OperationalPackage.fromPreparation D μFS bridge μψ
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
    prep.μψ (prep.O_region s t).preEvent
      = ENNReal.ofReal (P_st ctx.a ctx.b s t) := by
  haveI := prep.hμFS_prob
  haveI := prep.hμψ_prob
  rw [prep.bridge_op_p s t,
      OP_p_at_jointEig_eq_P_st D prep.μFS prep.bridge prep.μψ
        prep.PP prep.hN prep.jed s t]

end PureSingletPreparation

end LF3
end CSD
