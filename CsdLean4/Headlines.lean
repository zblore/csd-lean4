/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF1.MainTheorem
public import CsdLean4.LF1.GeneralFrequency
public import CsdLean4.LF2.Preparation
public import CsdLean4.LF2.EffectGleason
public import CsdLean4.LF2.POVM
public import CsdLean4.LF2.QuantumChannel
public import CsdLean4.LF3.Interface
public import CsdLean4.LF4.MomentBornN
public import CsdLean4.LF4.BornFrequencyN
public import CsdLean4.LF4.TypicalityForcing
public import CsdLean4.LF4.ProjectedDynamics
public import CsdLean4.LF4.PhaseLift
public import CsdLean4.LF4.ManyToOnePillars
public import CsdLean4.LF5.DilationFromFlow
public import CsdLean4.LF5.Capstone
public import CsdLean4.LF6.Decoherence
public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF6.GHZContextuality
public import CsdLean4.LF6.C1BellConsistency
public import CsdLean4.Mathlib.QuantumInfo.Subadditivity
public import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.SigmaLayer.SwapLuders
public import CsdLean4.SigmaLayer.PovmDynamics
public import CsdLean4.SigmaLayer.MeasurementCapstone
public import CsdLean4.CV.ModeLocality
public import CsdLean4.Thermo.SecondLaw
public import CsdLean4.Thermo.Landauer

/-!
# Headlines: the curated consumer facade (G8)

**Category:** Special (facade — the reconstruction's actual API in one import).

`import CsdLean4.Headlines` gives a reviewer or downstream consumer exactly the
modules carrying the corpus's **31 headline claims** — the rows of
`specs/validation-claims.tsv` (canonical; human view `specs/VALIDATION-LEDGER.md`)
— without pulling the full 400+-module implementation surface through a single
flat root. Created 2026-08-06 (BACKLOG G8, the adopted half of the 2026-08-06
external review's facade recommendation). The exhaustive root `CsdLean4` remains
available for whole-corpus consumers; `Tests/AxiomAudit.lean` remains the axiom
gate.

The `example := @…` block at the bottom is the **drift guard**: it elaborates
every ledger constant by its full name, so a rename, namespace move, or deletion
of any headline breaks this module's build (stronger than
`scripts/check-validation-ledger.sh`'s per-file leaf grep — on creation day this
guard immediately caught FOUR wrong ledger constants: three rows recording
`CSD.SigmaLayer.*` for theorems living in `CSD.RecordLayer.*`, and CL-001's
missing `OnticSetup.TrialModel` prefix; all fixed in the tsv same day).
`check-validation-ledger.sh` also enforces that every ledger module is imported
above, so the facade cannot silently drop a headline.

## The 31 headline claims, by layer

* **LF1 — typicality → frequencies:** `CSD.LF1.OnticSetup.TrialModel.main_theorem_ae` (CL-001),
  `CSD.LF1.freq_tendsto_of_iid` (CL-002).
* **LF2 — operational stratum:** `CSD.LF2.OperationalPackage.fromPreparation`
  (CL-003), `CSD.LF2.PurePreparation.born_rank_one_direct` (CL-004),
  `CSD.LF2.OperationalPackage.effect_gleason_representation` (CL-005 — Busch's
  effect-Gleason, proved), `CSD.LF2.weights_sum_eq_one` (CL-006),
  `CSD.LF2.QuantumChannel.cptp_capstone` (CL-007).
* **LF3 — the singlet chain:** `CSD.LF3.LF3_main_theorem` (CL-008),
  `CSD.LF3.LF3_singlet_frequency_convergence_born` (CL-009).
* **LF4 — Born from Kähler volume:** `CSD.LF4.fs_volume_eq_dirichlet` (CL-010),
  `CSD.LF4.born_frequency_convergence_N` (CL-011),
  `CSD.LF4.fubiniStudy_forced_by_symmetry` (CL-012),
  `CSD.LF4.obsFlow_not_ergodic` (CL-013),
  `CSD.LF4.projectedFlow_eq_unitary_family` (CL-014),
  `CSD.LF4.projectedFlow_phase_lift` (CL-015),
  `CSD.LF4.manyToOneSetup_born_frequency` (CL-016).
* **LF5 — measurement dynamics:** `CSD.LF5.measurementFlow_realises_dilation`
  (CL-017), `CSD.LF5.measurement_flow_born_frequency` (CL-018).
* **LF6 — entanglement / open systems:**
  `CSD.LF6.decoherence_offdiagonal_vanish` (CL-019),
  `CSD.LF6.no_product_partition_realises_singlet` (CL-020),
  `CSD.LF6.no_product_partition_realises_ghz` (CL-021).
* **C1 shared-domain obstruction:**
  `CSD.LF6.no_compatible_global_chsh_assignment_realises_singlet` (CL-031 — no
  measurable shared-context outcome family compatible with any global CHSH
  assignment reproduces the singlet at the four CHSH settings; added 2026-08-10,
  **replacing** the false type-separation claim, see `specs/publication-errata.md`).
* **Mathlib-staged (CSD-free):** `QuantumInfo.vonNeumannEntropy_subadditive`
  (CL-022), `QuantumInfo.strong_subadditivity_of_relEntropy_monotone` (CL-023 —
  SSA **from** the explicit `hDPI` premise, by design),
  `Projectivization.wigner_rigidity` (CL-024 — existence clause; see the module
  scope note).
* **Record layer (Σ):** `CSD.RecordLayer.swap_luders_marginal` (CL-025),
  `CSD.RecordLayer.povm_selector_born` (CL-026),
  `CSD.RecordLayer.projectiveMeasurementCapstone` (CL-027).
* **CV / Thermo:** `CSD.CV.commute_of_disjointSupport` (CL-028),
  `CSD.Thermo.vonNeumannEntropy_le_pinching` (CL-029),
  `CSD.Thermo.landauer_bound` (CL-030).

Claim-status vocabulary, scope qualifications, and the open-work queue live in
`specs/VALIDATION-LEDGER.md`, `specs/reconstruction-status.md`, and
`specs/future-work.md` / `specs/BACKLOG.md`; no import here upgrades a
`qualified` claim.
-/

@[expose] public section

namespace CSD.Headlines

/-! ### Drift guard — every ledger constant, by full name (CL-001 … CL-031) -/

/-! The drift guard: each `example` elaborates one ledger constant by its full
name (universe metavariables generalized at top level; the one noncomputable
data def marked as such). A rename, namespace move, or deletion of any
headline fails this build. -/

example := @CSD.LF1.OnticSetup.TrialModel.main_theorem_ae -- CL-001
example := @CSD.LF1.freq_tendsto_of_iid -- CL-002
noncomputable example := @CSD.LF2.OperationalPackage.fromPreparation -- CL-003
example := @CSD.LF2.PurePreparation.born_rank_one_direct -- CL-004
example := @CSD.LF2.OperationalPackage.effect_gleason_representation -- CL-005
example := @CSD.LF2.weights_sum_eq_one -- CL-006
example := @CSD.LF2.QuantumChannel.cptp_capstone -- CL-007
example := @CSD.LF3.LF3_main_theorem -- CL-008
example := @CSD.LF3.LF3_singlet_frequency_convergence_born -- CL-009
example := @CSD.LF4.fs_volume_eq_dirichlet -- CL-010
example := @CSD.LF4.born_frequency_convergence_N -- CL-011
example := @CSD.LF4.fubiniStudy_forced_by_symmetry -- CL-012
example := @CSD.LF4.obsFlow_not_ergodic -- CL-013
example := @CSD.LF4.projectedFlow_eq_unitary_family -- CL-014
example := @CSD.LF4.projectedFlow_phase_lift -- CL-015
example := @CSD.LF4.manyToOneSetup_born_frequency -- CL-016
example := @CSD.LF5.measurementFlow_realises_dilation -- CL-017
example := @CSD.LF5.measurement_flow_born_frequency -- CL-018
example := @CSD.LF6.decoherence_offdiagonal_vanish -- CL-019
example := @CSD.LF6.no_product_partition_realises_singlet -- CL-020
example := @CSD.LF6.no_product_partition_realises_ghz -- CL-021
example := @QuantumInfo.vonNeumannEntropy_subadditive -- CL-022
example := @QuantumInfo.strong_subadditivity_of_relEntropy_monotone -- CL-023
example := @Projectivization.wigner_rigidity -- CL-024
example := @CSD.RecordLayer.swap_luders_marginal -- CL-025
example := @CSD.RecordLayer.povm_selector_born -- CL-026
example := @CSD.RecordLayer.projectiveMeasurementCapstone -- CL-027
example := @CSD.CV.commute_of_disjointSupport -- CL-028
example := @CSD.Thermo.vonNeumannEntropy_le_pinching -- CL-029
example := @CSD.Thermo.landauer_bound -- CL-030
example := @CSD.LF6.no_compatible_global_chsh_assignment_realises_singlet -- CL-031

end CSD.Headlines
