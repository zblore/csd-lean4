/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.Interface
import CsdLean4.LF2.Preparation

/-!
# Empirical/CSD: shared framework bundle for CSD-side empirical readings

**Category:** 3-Local (currently placed under `Empirical/CSD/`). The
bundle is purely structural (it carries LF2-discharge data; no theorems
inside the file). Promotion-readiness depends on LF4 stabilising the
discharge interfaces.

## Why this file exists

Per `specs/empirical-csd-bridge-plan.md`, every empirical prediction in
`Empirical/QM/<phenomenon>.lean` (Bell, no-cloning, GHZ, KS, future
gates/algorithms) has a paired CSD-side reading in
`Empirical/CSD/<phenomenon>.lean`. The CSD-side reading expresses the
phenomenon in terms of CSD's ontic substrate (Σ, μL, π, prepMeasure,
SectorData) and the volume-ratio account of probability.

Each CSD-side reading needs the same LF2-level discharge data: a
projective reference measure `μFS`, a probability witness for it, and
the bridge `Measure.map D.π D.μL = c • μFS`. This file packages those
into a single shared structure `CSDBridgeContext D`. Per-phenomenon
files extend it with phenomenon-specific bundles (joint eigenstates,
outcome regions, ontic-weight ↔ OP.p bridges, etc.) matching the
working `PureSingletPreparation` template in
`CsdLean4/LF3/PurePreparation.lean`.

## What it carries

Three fields, all LF2-only:

- `μFS : Measure P` — projective reference measure for the OP integral.
- `hμFS_prob : IsProbabilityMeasure μFS` — `μFS` is a probability measure.
- `bridge : MeasureBridgeData D μFS` — the measure bridge data
  (`π_*μL = c • μFS` + G-invariance), supplied directly; the concrete
  instances build it **axiom-free** (`CSD.LF4.cp_measure_bridge`,
  `k_measure_bridge`).

## What this file deliberately does *not* carry

- LF3 content. The `Singlet/*` machinery, `PureSingletPreparation`,
  `MeasurementJointEig`, `MeasurementContext` etc. all live downstream
  of this file in `Empirical/CSD/Bell.lean` (and would also live in
  GHZ/KS/NoCloning companions when those land). The framework is
  LF2-only by design.
- Phenomenon-specific outcome regions, joint eigenstates, or
  measurement structures. Each per-item file declares its own bundle
  extending `CSDBridgeContext D` with the relevant additions.
- Theorems. The file is structural-data only. Composition theorems
  live in per-item files.

## Extensibility (per the bridge plan §6)

The structural template — preparation bundle (extending a shared
LF2-level context) + theorem composition + named discharge targets —
is interpretation-agnostic. Future companions for other foundational
interpretations (`Empirical/Bohmian/`, `Empirical/Everettian/`,
`Empirical/Operational/`) would each have their own framework module
analogous to this one, carrying *their* interpretation-specific
discharge data. The CSD framework here does not leak across that
boundary because it is import-isolated to `Empirical/CSD/`.

## Discipline

Any field added to `CSDBridgeContext` or a downstream
`Pure<Phenomenon>Preparation` bundle that is **load-bearing and not
yet discharged** must:

1. Carry the docstring marker
   `**Status: load-bearing, externally supplied, undischarged.**`.
2. Cross-reference a numbered item in `specs/LF4-todo.md`.
3. Appear in `BRIDGE-OBLIGATIONS.md`'s ledger with the same citation.

The existing `PureSingletPreparation.bridge_op_p` is the working
example of this discipline. See `specs/empirical-csd-bridge-plan.md`
§5 for the full rule set.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge

/-- **Shared LF2-level discharge context for CSD-side empirical
readings.** Every `Empirical/CSD/<phenomenon>.lean` bundle extends
this structure with phenomenon-specific additions. Carries the
projective reference measure `μFS`, the probability witness, and the
measure bridge data — the three LF2-level ingredients common to every
CSD-side reading of a QM construct.

The bridge data is supplied directly; the concrete instances build it
axiom-free (`CSD.LF4.cp_measure_bridge`, `k_measure_bridge`). -/
structure Context
    {SigmaSpace P G : Type*}
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    [MeasurableSpace P]
    [Group G]
    [MulAction G SigmaSpace] [MulAction G P]
    [MulAction.IsPretransitive G P]
    (D : CSD.LF2.SectorData SigmaSpace P G) where
  /-- Projective reference measure for the OP construction. -/
  μFS         : Measure P
  /-- `μFS` is a probability measure. -/
  hμFS_prob   : IsProbabilityMeasure μFS
  /-- The measure-bridge data (`π_*μL = c • μFS` + G-invariance); supplied
      directly, axiom-free on the concrete instances. -/
  bridge      : CSD.LF2.MeasureBridgeData D μFS

end CSDBridge
end Empirical
end CSD
