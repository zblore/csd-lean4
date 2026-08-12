/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Tests.Witnesses.IIDSampling
public import CsdLean4.Tests.Witnesses.LF1Trial
public import CsdLean4.Tests.Witnesses.Dynamics

/-!
# Concrete-witness suite (umbrella)

**Category:** Special (validation-hardening witness suite;
`specs/validation-hardening-plan.md`).

Explicit, nontrivial inhabitants of the corpus's assumption packages
(`OnticSetup`, `TrialModel`, `SectorData`, `PureSingletPreparation`, …),
driven through the actual headline theorem chains. The suite strengthens the
**sufficiency/inhabitation leg** of validation: current tests are strong at
`assumptions → theorem`; this suite establishes
`explicit nontrivial model → assumptions → theorem`.

## Standing rules (binding for every module here)

1. **Anti-duplication.** A witness module *instantiates and applies*
   production theorems through their public interfaces. It never restates,
   re-proves, or shadows a production theorem, and it never adds parallel
   mathematics. Production non-vacuity theorems are cited, not re-derived.
2. **Nontriviality is explicit.** Each witness carries a stated
   nontriviality clause ruling out degenerate inhabitants (singleton spaces,
   zero maps, identity-only dynamics, certainty-weight outcomes, vacuous
   hypotheses).
3. **Theorem-chain execution.** Each witness fires at least one load-bearing
   production theorem of its layer on the concrete model — construction
   alone closes nothing.
4. **Tests-target only.** Nothing here enters the production dependency
   graph; headline witnesses are axiom-pinned in
   `Tests/AxiomAudit/Witnesses.lean`.
5. **Witness ≠ result.** This suite is validation machinery on the
   sufficiency leg. It is not reconstruction progress, and it does not bear
   on the necessity-audit conditionality gap (2026-08-09).
-/
