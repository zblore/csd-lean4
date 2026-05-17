import CsdLean4.LF3.ContextMap
import CsdLean4.LF2.Interface

/-!
# LF3 PurePreparation: bundled hLF2 discharge target

Paper boundary at the LF1 ↔ LF2 ↔ LF3 capstone (spec §10.5 / LF4-todo §2 + §7).

The three `LF3_singlet_frequency_convergence*` capstones in `Interface.lean`
each take a load-bearing external hypothesis tying the LF2 projective weight
of the pointer-sector outcome region to the singlet kernel value
`P_st ctx.a ctx.b s t`. This module bundles that hypothesis, together with
the ontic ↔ projective outcome correspondence, into a single structure
`PureSingletPreparation D ctx`. The chain capstones consume the bundle;
LF4 will eventually supply a concrete constructor
`PureSingletPreparation.ofKählerPreparation` from a concrete Kähler
`SectorData` instantiation (per LF4-todo §8, Q1 answer 2026-05-17) plus
the preparation-to-Hilbert correspondence (LF4-todo §2).

## Three-category posture

- **Proved internally.** The structure definition and the transitional
  constructor `ofHypothesis`. No theorems proved here; the module
  bundles hypotheses.
- **Imported from upstream.** `MeasurementContext` (LF3.ContextMap),
  `P_st` (LF3.Singlet.Kernel), `CSD.LF2.SectorData`,
  `CSD.LF2.projectiveWeight`, LF1 `OutcomeRegion` and `prepMeasure`.
- **Axiomatised at an explicit boundary.** None. This module carries no
  axioms; it carries the LF2 ↔ LF3 calibration as a structural
  hypothesis bundle, with discharge deferred to LF4. See
  [`AXIOMS.md`](../../AXIOMS.md) §3.6 for the corresponding entry.

## API shape

The structure has four fields:
- `O_st : Sign → Sign → Set P` (projective outcome regions),
- `O_st_measurable` (measurability),
- `O_region : Sign → Sign → D.toOntic.OutcomeRegion` (ontic outcomes),
- `correspondence : ∀ s t, (O_region s t).preEvent = D.π ⁻¹' (O_st s t)`,
- `weight_eq_P_st : ∀ s t, projectiveWeight D μprep (O_st s t)
                          = ENNReal.ofReal (P_st ctx.a ctx.b s t)`.

The transitional constructor `ofHypothesis` accepts the raw field set so
existing call sites of the old verbose capstone signatures can be
migrated mechanically.
-/

open MeasureTheory

namespace CSD
namespace LF3

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]

/-- Bundled LF2 ↔ LF3 calibration data: the projective outcome family,
    its ontic counterpart, the correspondence between them, and the Born
    identity `projectiveWeight (O_st s t) = P_st ctx.a ctx.b s t`.

    A v1.x carrier of the LF4 discharge target. LF4 will supply a concrete
    constructor; the transitional `ofHypothesis` constructor below lets
    existing callers migrate without yet having the LF4 content. -/
structure PureSingletPreparation
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : MeasurementContext) where
  /-- Projective outcome region, indexed by pointer sector `(s, t)`. -/
  O_st           : Sign → Sign → Set P
  /-- Each projective outcome region is measurable in `P`. -/
  O_st_measurable : ∀ s t, MeasurableSet (O_st s t)
  /-- LF1 ontic outcome region, paralleling the projective family. -/
  O_region       : Sign → Sign → D.toOntic.OutcomeRegion
  /-- The ontic outcome's pulled-back event is the `π`-preimage of the
      projective outcome (LF4-todo §7: projective-first outcomes). -/
  correspondence : ∀ s t, (O_region s t).preEvent = D.π ⁻¹' (O_st s t)
  /-- The Born identity: the LF2 projective weight of `O_st s t` under
      the LF1 preparation measure equals `P_st ctx.a ctx.b s t`
      (LF4-todo §2: preparation-to-Hilbert correspondence). -/
  weight_eq_P_st : ∀ s t,
    CSD.LF2.projectiveWeight D
      ((D.toOntic.prepMeasure :
          ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
      (O_st s t)
    = ENNReal.ofReal (P_st ctx.a ctx.b s t)

namespace PureSingletPreparation

/-- Transitional constructor: build a `PureSingletPreparation` from the
    raw field set that the old `LF3_singlet_frequency_convergence*`
    signatures consumed as separate hypotheses. Existing callsites
    migrate by wrapping their four hypotheses in this constructor. LF4
    will replace its use with `PureSingletPreparation.ofKählerPreparation`
    or similar, derived from a concrete `SectorData` instantiation plus
    the preparation-to-Hilbert correspondence. -/
def ofHypothesis
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {ctx : MeasurementContext}
    (O_st : Sign → Sign → Set P)
    (O_st_measurable : ∀ s t, MeasurableSet (O_st s t))
    (O_region : Sign → Sign → D.toOntic.OutcomeRegion)
    (correspondence : ∀ s t, (O_region s t).preEvent = D.π ⁻¹' (O_st s t))
    (weight_eq_P_st : ∀ s t,
      CSD.LF2.projectiveWeight D
        ((D.toOntic.prepMeasure :
            ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        (O_st s t)
      = ENNReal.ofReal (P_st ctx.a ctx.b s t)) :
    PureSingletPreparation D ctx :=
  { O_st := O_st
    O_st_measurable := O_st_measurable
    O_region := O_region
    correspondence := correspondence
    weight_eq_P_st := weight_eq_P_st }

end PureSingletPreparation

end LF3
end CSD
