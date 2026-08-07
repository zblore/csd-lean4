/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Tests.AxiomAudit.Foundations
public import CsdLean4.Tests.AxiomAudit.EmpiricalQM
public import CsdLean4.Tests.AxiomAudit.EmpiricalCSD
public import CsdLean4.Tests.AxiomAudit.LF4
public import CsdLean4.Tests.AxiomAudit.Dynamics
public import CsdLean4.Tests.AxiomAudit.SigmaLayer
public import CsdLean4.Tests.AxiomAudit.MathlibStaging
public import CsdLean4.Tests.AxiomAudit.Extensions
public import CsdLean4.Tests.AxiomAudit.Incubator

/-!
# Axiom regression suite (umbrella)

**Category:** Special (cross-layer axiom-posture regression for all headline theorems).

`#guard_msgs` + `#print axioms` for every theorem in `AXIOMS.md §5`. Build
fails on regression: if any theorem acquires (or sheds) an axiom, the
expected `info:` string no longer matches `#print axioms`'s output, and
the affected part fails to compile.

The intent is **not** to forbid axiom changes; legitimate changes are
welcome and require updating both the pin and `AXIOMS.md §5` in the
same commit. The intent is to make axiom drift impossible without an
explicit, visible diff.

## G9 split (2026-08-06)

The pins live in eight per-part files under `Tests/AxiomAudit/`, classified
by the pinned constant's namespace (blocks keep their original relative
order): `Foundations` (LF1–LF3, incl. relative-name pins), `EmpiricalQM`,
`EmpiricalCSD`, `LF4`, `Dynamics` (LF5+LF6), `SigmaLayer` (+RecordLayer),
`MathlibStaging` (the Cat-1 tree incl. Reversible arithmetic), `Extensions`
(CV+Thermo), `Incubator` (§H workstream staging; added 2026-08-07). This umbrella imports them all, so `lake build CsdLeanTests`
is the unchanged full gate; a layer touch gates locally on its own part
(`lake build CsdLean4.Tests.AxiomAudit.<Part>`), and the parts build in
parallel. **New pins go in the part matching the constant's namespace.**

## How to update a pin

When discharging an axiom or introducing a new one, update the
`/-- info: ... -/` docstring above the corresponding `#print axioms` (in
the part file) to match the new output, in lockstep with the corresponding
`AXIOMS.md §5` row.
-/
