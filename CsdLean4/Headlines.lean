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
public import CsdLean4.Mathlib.Analysis.Matrix.ProjectiveLift
public import CsdLean4.LF3.SettingLocality
public import CsdLean4.Mathlib.QuantumInfo.Fidelity
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerPotential
public import CsdLean4.Mathlib.Dynamics.CatMapWitness
public import CsdLean4.Mathlib.Analysis.CStarAlgebra.OperatorConvexCFC
public import CsdLean4.LF4.ManyToOnePillars
public import CsdLean4.LF5.DilationFromFlow
public import CsdLean4.LF5.Capstone
public import CsdLean4.LF6.Decoherence
public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF6.GHZContextuality
public import CsdLean4.LF6.C1BellConsistency
public import CsdLean4.Mathlib.Probability.IidClockRace
public import CsdLean4.Mathlib.QuantumInfo.Subadditivity
public import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.RecordLayer.GlobalRecordClosure
public import CsdLean4.RecordLayer.SwapLuders
public import CsdLean4.RecordLayer.PovmDynamics
public import CsdLean4.RecordLayer.MeasurementCapstone
public import CsdLean4.CV.ModeLocality
public import CsdLean4.Thermo.SecondLaw
public import CsdLean4.Thermo.Landauer
public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1
public import CsdLean4.CV.ApproxCCR
public import CsdLean4.CV.LiebRobinson
public import CsdLean4.CV.Propagator
public import CsdLean4.SigmaLayer.TensorReconstruction
public import CsdLean4.RecordLayer.MeasurementConstraints
public import CsdLean4.RecordLayer.NoRecordGeometry
public import CsdLean4.RecordLayer.NullSeamGeneralN
public import CsdLean4.RecordLayer.StatisticsRigidity
public import CsdLean4.RecordLayer.PovmSectorBorn
public import CsdLean4.RecordLayer.PointerLudersMarginal
public import CsdLean4.LF4.QubitBorn
public import CsdLean4.Empirical.CSD.QuantumChaos.DerivedCoupling
public import CsdLean4.Empirical.CSD.QuantumChaos.EntropyLedger
public import CsdLean4.Empirical.QM.QEC.ShorNine
public import CsdLean4.LF6.LindbladSemigroup
public import CsdLean4.Thermo.ReducedSecondMoment
public import CsdLean4.Thermo.EnergyWindow
public import CsdLean4.Thermo.Equilibration
public import CsdLean4.Mathlib.Dynamics.CorrelationDecay
public import CsdLean4.Mathlib.Dynamics.CorrelationDecayWitness
public import CsdLean4.RecordLayer.ShearDeIsolation
public import CsdLean4.Empirical.CSD.PointerCommutation
public import CsdLean4.Mathlib.QuantumInfo.PhaseEstimation
public import CsdLean4.SigmaLayer.Equivariance
public import CsdLean4.RecordLayer.NStepChain
public import CsdLean4.SigmaLayer.MovingFibreWitness
public import CsdLean4.RecordLayer.BasinFrequency

/-!
# Headlines: the curated consumer facade (G8)

**Category:** Special (facade — the reconstruction's actual API in one import).

`import CsdLean4.Headlines` gives a reviewer or downstream consumer exactly the
modules carrying the corpus's **68 headline claims** (count as of 2026-09-04, and
enforced: `check-validation-ledger.sh` reports it, and the drift guard below
elaborates every one) — the rows of
`specs/validation-claims.tsv` (canonical; human view `specs/VALIDATION-LEDGER.md`)
— without pulling the full 400+-module implementation surface through a single
flat root. Created 2026-08-06 (BACKLOG G8, the adopted half of the 2026-08-06
external review's facade recommendation); **extended 2026-08-13 (Q17 census):
CL-032…CL-051**, admitted under the criteria in `VALIDATION-LEDGER.md` — the
necessity audit's named strongest-direction omissions, the 2026-08-12/13
tranche's starred headliners, and the Q18 conversions. The exhaustive root
`CsdLean4` remains available for whole-corpus consumers; `Tests/AxiomAudit.lean`
remains the axiom gate.

The `example := @…` block at the bottom is the **drift guard**: it elaborates
every ledger constant by its full name, so a rename, namespace move, or deletion
of any headline breaks this module's build (stronger than
`scripts/check-validation-ledger.sh`'s per-file leaf grep — on creation day this
guard immediately caught FOUR wrong ledger constants: three rows recording
`CSD.SigmaLayer.*` for theorems living in `CSD.RecordLayer.*`, and CL-001's
missing `OnticSetup.TrialModel` prefix; all fixed in the tsv same day).
`check-validation-ledger.sh` also enforces that every ledger module is imported
above, so the facade cannot silently drop a headline.

## The headline claims, by layer

⚠️ **This listing is a reader's orientation, not the authority, and it lags.** The exhaustive,
machine-checked list is the `example := @…` drift-guard block at the bottom — it covers all 68
rows and breaks the build if any is renamed or deleted. The by-layer prose below covers 50 of
them; it is deliberately left without a count, because a number here drifts every time the ledger
grows and this heading said "31" for long enough to be wrong twice over
(`specs/prose-audit.md`, pass 5).

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
  `CSD.RecordLayer.globalRecordClosure_born` (CL-011, replacing
  `CSD.LF4.born_frequency_convergence_N` 2026-08-24 -- preparation-indexing removed),
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
  **replacing** the false type-separation claim, see `specs/publication-errata.md`)
  and `CSD.LF6.c1_singlet_contextual_capstone` (CL-052, added 2026-08-13, Q19 —
  the **positive half**: an explicit measurable shared-context family on
  `(KSigma 4, kMuPsi)` reproduces the singlet, the full `P_st` table at every
  context, and no global CHSH assignment is compatible with it — the C1
  separation two-sided, existence and obstruction in one statement).
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

## The 2026-08-13 census extension (Q17): CL-032 … CL-051

* **Forcing / no-go tier (the necessity audit's named omissions):**
  `Matrix.StoneC1.stone_continuous` (CL-032 — the second unconditional
  necessity), `CSD.CV.no_exact_finite_ccr` (CL-033),
  `CSD.RecordLayer.no_everywhere_correlation` /
  `no_exact_collapse` / `collapse_accuracy_bound` (CL-034/035/036 — the
  trilemma price list), `CSD.SigmaLayer.compositeAlgReconstruction` (CL-037 —
  tensor forcing), `CSD.RecordLayer.posMeasure_noRecord_pointer` (CL-038 —
  the third leg on the pointer).
* **Record layer / measurement:** `CSD.LF4.qubitBorn` (CL-039 — the
  A7-faithful context-fixed qubit Born),
  `CSD.RecordLayer.nullSeamGenClosure` (CL-047 — the third horn at every `N`),
  `CSD.RecordLayer.recordKernel_eq_transProb` (CL-048) and
  `CSD.RecordLayer.measure_eq_fubiniStudy_of_record_statistics_invariant`
  (CL-049) — the Q18 conditioner conversions,
  `CSD.RecordLayer.povm_sector_born` (CL-050 — the dynamical POVM Born),
  `CSD.RecordLayer.pointer_luders_born_prep` (CL-051 — records and update on
  one arena).
* **Chaos / records tranche:**
  `CSD.Empirical.QuantumChaos.deficitKick_record_halfLife` (CL-040 — derived
  coupling), `deficitKick_phaseFlip_halfLife` (CL-041 — DH-exact rate),
  `ledgerEntropy_le` (CL-042 — the entropy ledger).
* **QI / open systems / CV:** `CSD.Empirical.QM.QEC.shor_corrects_Z_degenerate`
  (CL-043 — Shor-9 degeneracy as a theorem),
  `CSD.LF6.lindbladSemigroup_hasDerivAt` (CL-044 — the master equation),
  `CSD.CV.norm_commutator_velocity_le` (CL-045 — the explicit LR velocity),
  `CSD.CV.vacuum_clustering` (CL-046).

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
example := @CSD.RecordLayer.globalRecordClosure_born -- CL-011
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
example := @Matrix.StoneC1.stone_continuous -- CL-032
example := @CSD.CV.no_exact_finite_ccr -- CL-033
example := @CSD.RecordLayer.no_everywhere_correlation -- CL-034
example := @CSD.RecordLayer.no_exact_collapse -- CL-035
example := @CSD.RecordLayer.collapse_accuracy_bound -- CL-036
noncomputable example := @CSD.SigmaLayer.compositeAlgReconstruction -- CL-037
example := @CSD.RecordLayer.posMeasure_noRecord_pointer -- CL-038
example := @CSD.LF4.qubitBorn -- CL-039
example := @CSD.Empirical.QuantumChaos.deficitKick_record_halfLife -- CL-040
example := @CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_halfLife -- CL-041
example := @CSD.Empirical.QuantumChaos.ledgerEntropy_le -- CL-042
example := @CSD.Empirical.QM.QEC.shor_corrects_Z_degenerate -- CL-043
example := @CSD.LF6.lindbladSemigroup_hasDerivAt -- CL-044
example := @CSD.CV.norm_commutator_velocity_le -- CL-045
example := @CSD.CV.vacuum_clustering -- CL-046
example := @CSD.RecordLayer.nullSeamGenClosure -- CL-047
example := @CSD.RecordLayer.recordKernel_eq_transProb -- CL-048
example := @CSD.RecordLayer.measure_eq_fubiniStudy_of_record_statistics_invariant -- CL-049
example := @CSD.RecordLayer.povm_sector_born -- CL-050
example := @CSD.RecordLayer.pointer_luders_born_prep -- CL-051
example := @CSD.LF6.c1_singlet_contextual_capstone -- CL-052
example := @CSD.Thermo.fs_hsDeviationNormSq -- CL-053
example := @CSD.Thermo.energyWindow_ne_zero -- CL-054
example := @MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq -- CL-055
example := @CSD.Thermo.hsDeviationNormSq_timeAverage_tendsto -- CL-056
example := @MeasureTheory.circ_hasCorrelationDecay -- CL-057
example := @ProbabilityTheory.hasRaceProperty_iff_exists_expMeasure -- CL-058
example := @CSD.RecordLayer.shearDeIsolation_born -- CL-059
example := @CSD.Empirical.CSDBridge.Einselection.pointer_invariant_iff_commute -- CL-060
example := @QuantumInfo.phase_estimation_lower_bound -- CL-061
example := @Matrix.ProjectiveLift.exists_continuous_phase_trivialisation -- CL-062
example := @CSD.LF4.projectedFlow_schrodinger_form_of_continuous_flow -- CL-063
example := @CSD.LF3.operationalNoSignalling_of_settingLocality -- CL-064
example := @QuantumInfo.fidelity_le_one -- CL-065
example := @Kahler.fsChartForm_apply -- CL-066
example := @MeasureTheory.cat_hasCorrelationDecay -- CL-067
example := @OperatorConvexCFC.convexOn_mul_log -- CL-068
example := @CSD.SigmaLayer.csd_equivariance -- CL-069
example := @CSD.RecordLayer.csd_nstep_born -- CL-070
example := @CSD.SigmaLayer.movingFibreEnergy_not_projectable -- CL-071
example := @CSD.RecordLayer.globalBasin_born_frequency -- CL-072
example := @CSD.LF4.projectedFlow_unitary_of_flow_continuous -- CL-073

end CSD.Headlines
