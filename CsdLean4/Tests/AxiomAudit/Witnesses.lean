/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4
public import CsdLean4.Tests.Witnesses

/-!
# AxiomAudit part: Witnesses

**Category:** Special (axiom-posture regression pins; added 2026-08-12 with the
validation-hardening witness suite, `specs/validation-hardening-plan.md`).

Pins for the `Tests/Witnesses/` concrete-witness suite. The witnesses
instantiate production assumption packages and fire production headline
theorems on them, so their axiom posture must stay exactly the foundational
triple — a witness that acquires an axiom is a witness that stopped
witnessing. Layer-local gate: `lake build CsdLean4.Tests.AxiomAudit.Witnesses`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD.Tests.Witnesses

-- WS-C shared infrastructure (IIDSampling.lean, 2026-08-12): the honest i.i.d.
-- trial model on Measure.infinitePi, for every OnticSetup — LF1 fired with no
-- abstract hypotheses left.
/-- info: 'CSD.Tests.Witnesses.iidTrialModel_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.iidTrialModel_frequency_convergence

-- WS-C witness (LF1Trial.lean, 2026-08-12): the fully concrete coin model —
-- explicit product trials, weight 1/2 computed from Liouville volumes,
-- convergence to 1/2 a.s.
/-- info: 'CSD.Tests.Witnesses.coin_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.coin_frequency_convergence

/-- info: 'CSD.Tests.Witnesses.coin_witness_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.coin_witness_nontrivial

-- WS-J witnesses (Dynamics.lean, 2026-08-12): the dynamics assumption package
-- is inhabited by the production non-identity flows (cite-don't-construct);
-- the frequency capstone fired on honest infinitePi trials.
/-- info: 'CSD.Tests.Witnesses.exists_cpSectorData_nontrivial_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.exists_cpSectorData_nontrivial_flow

/-- info: 'CSD.Tests.Witnesses.exists_kSectorData_nontrivial_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.exists_kSectorData_nontrivial_flow

/-- info: 'CSD.Tests.Witnesses.qubit_dynamics_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.qubit_dynamics_witness

/-- info: 'CSD.Tests.Witnesses.cpSectorDataFlow_frequency_convergence_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Tests.Witnesses.cpSectorDataFlow_frequency_convergence_concrete

end CSD.Tests.AxiomAudit
