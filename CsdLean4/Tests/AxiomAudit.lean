import CsdLean4.LF1.MainTheorem
import CsdLean4.LF1.GeneralFrequency
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.ReducedDensity
import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd
import CsdLean4.LF2.Interface
import CsdLean4.LF2.Preparation
import CsdLean4.LF3.Interface
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.Singlet.JointProjector
import CsdLean4.LF3.Singlet.JointEig
import CsdLean4.LF3.Projectors.TensorModel
import CsdLean4.LF4.Instance
import CsdLean4.LF4.KahlerInstance
import CsdLean4.LF4.KahlerFlow
import CsdLean4.LF4.MomentMap
import CsdLean4.LF4.BornVolume
import CsdLean4.LF4.MomentPushforward
import CsdLean4.LF4.BornFS
import CsdLean4.LF4.QubitBornFrequency
import CsdLean4.LF4.BornFrequencyPartition
import CsdLean4.LF4.MomentMarginal
import CsdLean4.LF4.DuistermaatHeckman
import CsdLean4.LF4.GaussianFS
import CsdLean4.LF4.GaussianCP
import CsdLean4.LF4.GaussianCPN
import CsdLean4.LF4.MomentMarginalUniform
import CsdLean4.LF4.MomentRatioUniform
import CsdLean4.LF4.MomentRatioUniformN
import CsdLean4.LF4.MomentUniform
import CsdLean4.LF4.MomentBridgeN
import CsdLean4.LF4.MomentDirichletN
import CsdLean4.LF4.MomentBornN
import CsdLean4.LF4.BornFrequencyN
import CsdLean4.LF4.QubitConsistency
import CsdLean4.Mathlib.MeasureTheory.PiCurry
import CsdLean4.LF4.SingletKahler
import CsdLean4.LF4.SingleQubitKahler
import CsdLean4.LF4.SingletObservables
import CsdLean4.LF4.HardyKahler
import CsdLean4.LF4.SpectralExpansion
import CsdLean4.LF4.SpectralCarving
import CsdLean4.LF4.SpectralVariance
import CsdLean4.LF4.UncertaintyKahler
import CsdLean4.LF4.PauliRobertson
import CsdLean4.LF4.PauliDotRobertson
import CsdLean4.LF4.OnticBorn
import CsdLean4.LF2.POVM
import CsdLean4.LF2.EffectAux
import CsdLean4.LF4.POVMDilation
import CsdLean4.LF4.POVMVolume
import CsdLean4.LF4.POVMNaimark
import CsdLean4.Empirical.QM.Bell
import CsdLean4.Empirical.QM.NoCloning
import CsdLean4.Empirical.QM.NoDeleting
import CsdLean4.Empirical.QM.Resources.SuperdenseCoding
import CsdLean4.Empirical.QM.Resources.Teleportation
import CsdLean4.Empirical.QM.NoCommunication
import CsdLean4.Empirical.QM.NoBroadcasting
import CsdLean4.Empirical.QM.Crypto.QuantumMoney
import CsdLean4.Empirical.QM.Crypto.E91
import CsdLean4.Empirical.QM.USD
import CsdLean4.Empirical.QM.Uncertainty
import CsdLean4.Empirical.QM.Multipartite.GHZ
import CsdLean4.Empirical.QM.Contextuality.KS18
import CsdLean4.Empirical.QM.Contextuality.MerminPeres
import CsdLean4.Empirical.QM.Hardy
import CsdLean4.Empirical.QM.SternGerlach
import CsdLean4.Empirical.QM.Malus
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.CSD.Bell
import CsdLean4.Empirical.CSD.NoCloning
import CsdLean4.Empirical.CSD.NoDeleting
import CsdLean4.Empirical.CSD.NoBroadcasting
import CsdLean4.Empirical.CSD.NoCommunication
import CsdLean4.Empirical.CSD.Uncertainty
import CsdLean4.Empirical.CSD.SternGerlach
import CsdLean4.Empirical.CSD.SternGerlachVolume
import CsdLean4.Empirical.CSD.MalusVolume
import CsdLean4.Empirical.CSD.BellVolume
import CsdLean4.Empirical.CSD.GHZVolume
import CsdLean4.Empirical.CSD.HardyVolume
import CsdLean4.Empirical.CSD.TrineVolume
import CsdLean4.Empirical.CSD.USDVolume
import CsdLean4.Empirical.CSD.SICVolume
import CsdLean4.Empirical.CSD.Resources.SuperdenseCoding
import CsdLean4.Empirical.CSD.Resources.Teleportation
import CsdLean4.Empirical.CSD.Crypto.QuantumMoney
import CsdLean4.Empirical.CSD.Crypto.E91
import CsdLean4.Empirical.CSD.Contextuality.MerminPeres
import CsdLean4.Empirical.CSD.Hardy
import CsdLean4.Empirical.CSD.Contextuality.KS18
import CsdLean4.Empirical.CSD.Multipartite.GHZ
import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import CsdLean4.Empirical.QM.Gates.BellPrep
import CsdLean4.Empirical.QM.Gates.MultiQubit
import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# Axiom regression suite

**Category:** Special (cross-layer axiom-posture regression for all headline theorems).

`#guard_msgs` + `#print axioms` for every theorem in `AXIOMS.md §5`. Build
fails on regression: if any theorem acquires (or sheds) an axiom, the
expected `info:` string no longer matches `#print axioms`'s output, and
this module fails to compile.

The intent is **not** to forbid axiom changes; legitimate changes are
welcome and require updating both this module and `AXIOMS.md §5` in the
same commit. The intent is to make axiom drift impossible without an
explicit, visible diff.

## How to update

When discharging an axiom (e.g., LF4 proves `rankOneDensity_unique_of_certainty`)
or introducing a new one, update the `/-- info: ... -/` line above the
corresponding `#print axioms` to match the new output, in lockstep with
the corresponding `AXIOMS.md §5` row.
-/

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3

/-! ### LF1 -/

/-- info: 'CSD.LF1.OnticSetup.LF1_main_theorem_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_ae

/-- info: 'CSD.LF1.freq_tendsto_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF1.freq_tendsto_of_iid

/-! ### LF2 -/

/-- info: 'CSD.LF2.LF1_main_theorem_projective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_projective

/-- info: 'CSD.LF2.lf1_weight_eq_projective_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lf1_weight_eq_projective_weight

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective_preEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_preEvent

/--
info: 'CSD.LF2.SectorData.outcomeOfProjective_weight_eq_projectiveWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_weight_eq_projectiveWeight

/-- info: 'CSD.LF2.measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound, invariant_measure_uniqueness] -/
#guard_msgs in #print axioms measure_bridge

/-- info: 'CSD.LF2.born_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms born_quadratic

-- Partial trace (Cat-1 Mathlib staging) + the reduced density operator (LF2).
-- traceRight/traceLeft trace out a tensor factor; the API (kronecker defining
-- property, trace-preservation, Hermitian/PSD preservation) sends a density
-- operator to its reduced density operator. Foundational triple. Unblocks E3b/E2.
/-- info: 'Matrix.traceRight_kronecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Matrix.traceRight_kronecker

/-- info: 'Matrix.trace_traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.trace_traceRight

/-- info: 'Matrix.PosSemidef.traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.PosSemidef.traceRight

/-- info: 'CSD.LF2.DensityOperatorIx.reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF2.DensityOperatorIx.reduced

-- General-N DH Slice D.5a: Tonelli for a product over a finite index (lintegral).
-- ∫⁻ ∏ᵢ fᵢ(xᵢ) ∂(pi μ) = ∏ᵢ ∫⁻ fᵢ ∂μᵢ — the lintegral analogue of the Bochner
-- integral_fintype_prod_eq_prod (Mathlib has only the Bochner version). Cat-1
-- staging; needed for the pi-withDensity bridge (D.5b). Foundational triple.
/-- info: 'MeasureTheory.lintegral_fin_nat_prod_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.lintegral_fin_nat_prod_eq_prod

/-- info: 'MeasureTheory.lintegral_fintype_prod_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.lintegral_fintype_prod_eq_prod

-- General-N DH Slice D.5b: the pi-withDensity bridge. Measure.pi (μ.withDensity gᵢ)
-- = (Measure.pi μ).withDensity (∏ gᵢ) — the pi analogue of prod_withDensity (absent
-- from Mathlib), via Measure.pi_eq on rectangles + D.5a. Foundational triple.
/-- info: 'MeasureTheory.pi_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.pi_withDensity

/-- info: 'CSD.LF2.pure_state_born_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights

/--
info: 'CSD.LF2.pure_state_born_weights_of_certainty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms pure_state_born_weights_of_certainty

/-- info: 'CSD.LF2.PurePreparation.OP_certain_at_ψ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.OP_certain_at_ψ

/-- info: 'CSD.LF2.PurePreparation.born_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one

/-- info: 'CSD.LF2.PurePreparation.born_rank_one_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one_direct

/-! ### LF3 -/

/-- info: 'CSD.LF3.LF3_main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_main_theorem

/-- info: 'CSD.LF3.LF3_finite_leakage_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_finite_leakage_theorem

-- Re-routed off Busch (2026-06-02): the chain bridge now goes through the
-- foundational-triple `weight_eq_P_st` → `OP_p_at_jointEig_eq_P_st_direct` (the
-- ontic-stratum, volume-ratio Born step). All six capstones are now
-- foundational-triple-only; the Busch-mediated `OP_p_at_jointEig_eq_P_st` stays as
-- the operational-stratum statement. See AXIOMS.md §2.4.
/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_joint

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_joint

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner_joint

/-- info: 'CSD.LF3.PureSingletPreparation.ofHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PureSingletPreparation.ofHypothesis

-- The genuine joint-spin-projector Born identity (LF4 §3 groundwork):
-- ⟨ψ⁻ | Πˢ(a)⊗Πᵗ(b) | ψ⁻⟩ = P_st. Pure matrix algebra, foundational triple only.
/-- info: 'CSD.LF3.singlet_jointSpinProj_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms singlet_jointSpinProj_expectation

-- The Born identity for the GENUINE joint spin eigenstate (LF4-todo §3 discharged):
-- ‖⟨ψ⁻, singletJointEig s t⟩‖² = P_st, with singletJointEig the actual normalised
-- projection of the singlet onto the sector. Foundational triple only.
/-- info: 'CSD.LF3.singletJointEig_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms singletJointEig_born

/-- info: 'CSD.LF3.PureSingletPreparation.weight_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PureSingletPreparation.weight_eq_P_st

/-- info: 'CSD.LF3.ProjectorAlgebra.ofTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProjectorAlgebra.ofTensorEmbedding

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_measurable

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st_direct

/-- info: 'CSD.LF3.MeasurementUnitary.ofUnitaryTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasurementUnitary.ofUnitaryTensorEmbedding

/-! ### Empirical predictions (Bell family, Phase A1-A5)

All Phase A1-A5 predictions cite only the foundational triple: the LF3
content they re-export does too (LF3 algebraic core in `Singlet/Kernel.lean`
is axiom-clean), and the new CHSH-at-Tsirelson computation is pure
arithmetic. -/

/-- info: 'CSD.Empirical.Bell.correlation_eq_neg_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.correlation_eq_neg_dot

/-- info: 'CSD.Empirical.Bell.no_signalling_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_alice

/-- info: 'CSD.Empirical.Bell.no_signalling_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_bob

/-- info: 'CSD.Empirical.Bell.singlet_marginal_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_alice

/-- info: 'CSD.Empirical.Bell.singlet_marginal_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_bob

/-- info: 'CSD.Empirical.Bell.chsh_classical_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_classical_bound_violated

/-- info: 'CSD.Empirical.Bell.chsh_singlet_at_optimal_angles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_at_optimal_angles

/-- info: 'CSD.Empirical.Bell.chsh_singlet_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_tsirelson_bound

/-- info: 'CSD.Empirical.Bell.chsh_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_inner_bound

/-- info: 'CSD.Empirical.Bell.chsh_qm_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_qm_tsirelson_bound

/-! ### Empirical predictions (no-cloning, Phase B2) -/

/-- info: 'CSD.Empirical.NoCloning.no_cloning_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_cloning_two_state

/-- info: 'CSD.Empirical.NoCloning.no_universal_cloner_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_universal_cloner_of_witness

/-- info: 'CSD.Empirical.NoDeleting.no_deleting_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_deleting_two_state

/-- info: 'CSD.Empirical.NoDeleting.no_universal_deleter_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_universal_deleter_of_witness

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_X

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_Z

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_XZ

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_I

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.bell_basis_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SuperdenseCoding.bell_basis_orthonormal

-- E5: Quantum teleportation (branch-conditional form). teleState = |ψ⟩⊗|Φ⁺⟩
-- factorises; the Bell-basis expansion sends each branch to a Pauli image of ψ;
-- the four corrections {I,Z,X,ZX} recover ψ exactly. QM-validity; foundational triple.
/-- info: 'CSD.Empirical.QM.Teleportation.teleState_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleState_factorises

/-- info: 'CSD.Empirical.QM.Teleportation.teleportation_bell_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleportation_bell_expansion

/-- info: 'CSD.Empirical.QM.Teleportation.teleportation_branch_recovers_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleportation_branch_recovers_input

-- E3a: No-communication (marginal form). Alice's local unitary U⊗I cannot change
-- any Bob-side expectation ⟨φ,(I⊗Q)φ⟩; via the Kronecker mixed-product collapse
-- (U⊗I)ᴴ(I⊗Q)(U⊗I) = I⊗Q. No partial trace. QM-validity; foundational triple.
/-- info: 'CSD.Empirical.QM.NoCommunication.aliceOp_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.aliceOp_conjugate

/-- info: 'CSD.Empirical.QM.NoCommunication.no_communication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.no_communication

/-- info: 'CSD.Empirical.QM.NoCommunication.bob_expectation_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.bob_expectation_invariant

-- E3b: No-communication, reduced-density form. Alice's local unitary U⊗I leaves
-- Bob's reduced state (traceLeft ρ) invariant, via the partial-trace cyclicity
-- lemma. The structured form lands on the LF2 DensityOperatorIx.reducedLeft.
-- Foundational triple.
/-- info: 'Matrix.traceLeft_conjTranspose_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_conjTranspose_kronecker_one

/-- info: 'CSD.Empirical.QM.NoCommunication.no_communication_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.no_communication_reduced

/-- info: 'CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq

-- E2: No-broadcasting, pure-marginal confinement core. A bipartite PSD operator
-- with a pure first-factor marginal |ψ⟩⟨ψ| is confined to that pure sector
-- ((P⊗I)·ρ·(P⊗I) = ρ) — the obstruction to broadcasting a pure state. Built on the
-- partial-trace module laws + PSD block-vanishing. Foundational triple. The full
-- BCFJS commuting-states theorem is fidelity-gated (deferred QI-infra tranche).
/-- info: 'CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_inner

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_nonorthogonal

/-- info: 'CSD.Empirical.QuantumMoney.quantum_money_unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.quantum_money_unforgeable

-- E91 device-independent security: the local-hidden-variable CHSH bound |S| ≤ 2
-- (Bell 1964 / CHSH 1969, the previously un-formalised premise behind
-- bellClassicalBoundValue), every LHV value strictly below the Tsirelson 2√2, and
-- the device-independent witness (singlet attains 2√2; every LHV capped at 2).
-- Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.lhvCHSH_abs_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.lhvCHSH_abs_le_two

/-- info: 'CSD.Empirical.QM.E91.lhvCHSH_lt_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.lhvCHSH_lt_tsirelson

/-- info: 'CSD.Empirical.QM.E91.e91_no_lhv_reproduces_singlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_no_lhv_reproduces_singlet

-- USD (unambiguous state discrimination), the POVM-essential QM-validity result:
-- the unambiguity zeros ⟨ψ₂,E₁ψ₂⟩ = ⟨ψ₁,E₂ψ₁⟩ = 0 (zero-error discrimination,
-- impossible projectively) and the IDP success probability 1 − s. Foundational
-- triple only.
/-- info: 'CSD.Empirical.QM.USD.usd_unambiguous_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_unambiguous_1

/-- info: 'CSD.Empirical.QM.USD.usd_unambiguous_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_unambiguous_2

/-- info: 'CSD.Empirical.QM.USD.usd_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_success

/-- info: 'CSD.Empirical.QM.USD.usd_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_complete

/-- info: 'CSD.Empirical.QM.USD.usdPOVM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usdPOVM

/-- info: 'CSD.Empirical.Uncertainty.robertson_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_core

/-- info: 'CSD.Empirical.Uncertainty.robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_uncertainty

/-! ### Empirical predictions (GHZ paradox, Phase D6 / Mermin all-or-nothing) -/

/-- info: 'CSD.Empirical.GHZ.ghz_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_norm

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xxx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xxx

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xyy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xyy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yxy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yxy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yyx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yyx

/-- info: 'CSD.Empirical.GHZ.no_lhv_assignment_for_ghz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.no_lhv_assignment_for_ghz

/-! ### Empirical predictions (Kochen-Specker, Phase D9 / Cabello 1996 18-vector form)

The abstract combinatorial impossibility and the concrete Cabello-18
instance. The abstract form is genuinely Cat-2 (CSD-free, Hilbert-
space-free); the instance is Cat-3 only because it lives under
`Empirical/`. Both pinned to the foundational triple. -/

/-- info: 'CSD.Empirical.KochenSpecker.no_value_assignment_18_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.no_value_assignment_18_9

/-- info: 'CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice

/-- info: 'CSD.Empirical.MerminPeres.no_lhv_mermin_peres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.no_lhv_mermin_peres

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaZ_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaZ_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R2

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C2

/-- info: 'CSD.Empirical.Hardy.no_lhv_hardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.no_lhv_hardy

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_cube

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_value

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq

/-- info: 'CSD.Empirical.SternGerlach.born_zPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_zMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_z_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_z_basis_complete

/-- info: 'CSD.Empirical.SternGerlach.born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_x_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_law

/-- info: 'CSD.Empirical.Malus.malus_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_pi_div_two

/--
info: 'CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18

/--
info: 'CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis

/-! ### Empirical/CSD bridge readings

CSD-side companions to the Empirical/QM/ predictions. Each cites the
foundational triple and the LF4-discharge axioms threaded through the
shared `CSDBridge.Context` bundle.

The Bell-family CSD readings are re-exports of LF3 chain capstones;
their axiom citations match the corresponding LF3 capstones. -/

/-- info: 'CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence

/--
info: 'CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle

/--
info: 'CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle

/--
info: 'CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty

-- Phase-E CSD bridges (transport readings; foundational-triple only).
/--
info: 'CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting

/--
info: 'CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication

/--
info: 'CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input

/--
info: 'CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound

-- Stern-Gerlach: representative pin (the iconic 1/2 split) + completeness.
-- All six transport theorems share the same foundational-triple axiom set.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus

/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete

-- Stern-Gerlach Born values as DERIVED Kähler-volume frequencies (carving-free,
-- Gleason-free CSD-ontic layer): the moment-sublevel frequency → Born number
-- via fs_moment_pushforward_uniform (DH theorem). Strictly above both the
-- transport tag (csd_sg_*) and the carved LF4 capstone (sg_frequency_convergence).
-- Foundational triple only; NO busch_effect_gleason, NO invariant_measure_uniqueness.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain

/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half

-- Malus's law (parametric generalisation of the two SG values) as a DERIVED
-- Kähler-volume frequency: freq → cos²(θ/2) via the same volume route.
-- Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law

-- Bell singlet joint frequencies as DERIVED Kähler-volume convergence (N=4
-- surfacing of born_frequency_convergence_N): carving-free, Gleason-free, and
-- UNCONDITIONAL (no PureSingletPreparation bundle). Plus the recovered singlet
-- correlation -cos θ. Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation

-- GHZ three-qubit joint frequencies as DERIVED Kähler-volume convergence (N=8
-- surfacing of born_frequency_convergence_N, generic xy-plane basis): carving-free,
-- Gleason-free, unconditional. Plus the recovered three-point correlation cos Φ
-- (Mermin values are the excluded Φ=0,π boundary). Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation

-- Hardy's maximal probability (5√5−11)/2 ≈ 9.017% as a DERIVED Kähler-volume
-- frequency (N=4 surfacing of born_frequency_convergence_N at the golden-ratio
-- Hardy state, an interior simplex point — no boundary obstruction): carving-free,
-- Gleason-free, unconditional. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability

-- Trine POVM: the first non-projective (POVM) entry in the volume-frequency series.
-- A concrete qubit trine POVM (completeness ∑ Eₖ = I), its canonical Naimark
-- dilation, and the frequency-volume capstone — POVM outcome frequencies on the
-- dilated Σ' = ℂℙ⁵ → the trine Born weight as a sum of FS volumes. Foundational
-- triple only (carving-free, Gleason-free; POVM Born = Kähler volume).
/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_complete

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq

-- USD volume capstone: the second non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free).
/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume

-- SIC volume capstone: the third non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free); includes the equiangular
-- SIC property and the tetrahedral tight-frame completeness.
/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume

-- Superdense coding: representative pins (one encoding + the orthonormality).
/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X

/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal

/--
info: 'CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger

/--
info: 'CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment

/--
info: 'CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment

/--
info: 'CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle

/-- info: 'CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle

/-! ### Tranche 1 Tier A gates (added 2026-05-22)

Pure linear-algebra gate identities + CSD-side bundle framework.
The unitarity proofs cite only the foundational triple; the
`CSDUnitaryBundle` is a structure (no axioms). -/

/-- info: 'CSD.Empirical.QM.Gates.qmH_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmH_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmS_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmS_sq

/-- info: 'CSD.Empirical.QM.Gates.qmT_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmT_sq

/-- info: 'CSD.Empirical.QM.Gates.qmCNOT_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCNOT_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmSWAP_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmSWAP_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmCZ_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCZ_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_factorisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_factorisation

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus

/-- info: 'CSD.Empirical.QM.Gates.qmToffoli_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmToffoli_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmFredkin_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmFredkin_mul_self

/-! ### Mathlib upstream candidates (Projectivization, §12)

These are CSD-free Mathlib-track lemmas staged under
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/`. They cite the
foundational triple only — any axiom acquisition would be an upstream
regression and a blocker for the eventual Mathlib PR. -/

/-- info: 'Projectivization.continuous_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_mk'

/-- info: 'Projectivization.isOpenMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenMap_mk'

/-- info: 'Projectivization.isOpenQuotientMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenQuotientMap_mk'

/-- info: 'Projectivization.instT2Space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instT2Space

/-- info: 'Projectivization.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instCompactSpace

/-- info: 'Projectivization.instMeasurableSingletonClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMeasurableSingletonClass

/-- info: 'Projectivization.borel_eq_map_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.borel_eq_map_mk'

/-- info: 'Projectivization.lift_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.lift_measurable

/-- info: 'Projectivization.measurable_iff_measurable_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.measurable_iff_measurable_comp_mk'

/-- info: 'Projectivization.continuous_iff_continuous_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_iff_continuous_comp_mk'

/-- info: 'Projectivization.continuous_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_lift

/-- info: 'Projectivization.mapOfInjective_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapOfInjective_continuous

/-- info: 'Projectivization.mapEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv

/-- info: 'Projectivization.mapEquiv_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_continuous

/-- info: 'Projectivization.mapEquiv_continuous_of_finiteDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_continuous_of_finiteDim

/-- info: 'Projectivization.mapEquiv_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_one

/-- info: 'Projectivization.mapEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_mul

/-- info: 'Projectivization.instMulAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMulAction

/-- info: 'Projectivization.instContinuousConstSMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instContinuousConstSMul

/-- info: 'Matrix.UnitaryGroup.toEuclideanLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLinearEquiv

/-- info: 'Matrix.UnitaryGroup.toEuclideanLinearEquivHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLinearEquivHom

/-- info: 'Matrix.UnitaryGroup.instProjectivizationMulAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instProjectivizationMulAction

/-- info: 'Matrix.UnitaryGroup.instProjectivizationContinuousConstSMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instProjectivizationContinuousConstSMul

/-- info: 'Matrix.UnitaryGroup.sum_norm_sq_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.sum_norm_sq_col

/-- info: 'Matrix.UnitaryGroup.val_norm_apply_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.val_norm_apply_le_one

/-- info: 'Matrix.UnitaryGroup.val_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.val_norm_le_one

/-- info: 'Matrix.UnitaryGroup.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instCompactSpace

/-- info: 'Matrix.UnitaryGroup.instMeasurableSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instMeasurableSpace

/-- info: 'Matrix.UnitaryGroup.instBorelSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instBorelSpace

/-- info: 'Matrix.UnitaryGroup.unitaryHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_isHaarMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_isHaarMeasure

/-- info: 'Matrix.UnitaryGroup.instIsFiniteMeasureUnitaryHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsFiniteMeasureUnitaryHaar

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_univ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_univ_ne_zero

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_univ_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_univ_ne_top

/-- info: 'Matrix.UnitaryGroup.unitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.instIsProbabilityMeasureUnitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsProbabilityMeasureUnitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.unitaryHaarProb_isHaarMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaarProb_isHaarMeasure

/-- info: 'Matrix.UnitaryGroup.toEuclideanLin_apply_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLin_apply_continuous

/-- info: 'Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero

/-- info: 'Matrix.UnitaryGroup.orbitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbitMap

/-- info: 'Matrix.UnitaryGroup.orbit_map_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbit_map_continuous

/-- info: 'Matrix.UnitaryGroup.orbit_map_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbit_map_measurable

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure

/--
info: 'Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure

/-- info: 'Matrix.UnitaryGroup.smul_comp_orbitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.smul_comp_orbitMap

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_smul_invariant

/-- info: 'Matrix.UnitaryGroup.exists_unitary_e_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_e_zero_eq

/-- info: 'Matrix.UnitaryGroup.exists_unitary_map_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_map_unit

/-- info: 'Matrix.UnitaryGroup.exists_unitary_mapping_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_mapping_nonzero

/-- info: 'Matrix.UnitaryGroup.smul_mk_eq_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.smul_mk_eq_mk

/-- info: 'Matrix.UnitaryGroup.instIsPretransitive_projectivization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsPretransitive_projectivization

/-- info: 'Matrix.UnitaryGroup.instContinuousSMul_projectivization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instContinuousSMul_projectivization

/-- info: 'Matrix.UnitaryGroup.instIsMulRightInvariantUnitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsMulRightInvariantUnitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.haar_orbit_indicator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.haar_orbit_indicator_eq

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_unique

-- `whitespace := lax` because the long theorem names push the axiom list
-- past the pretty-printer width, wrapping it across lines; lax collapses
-- the wrap so a single-line docstring matches.
/-- info: 'Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy

/-- info: 'Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn

/-! ### LF4 §8 ontic-shell instantiation

The first concrete `SectorData` instance and its axiom-free measure bridge.
Both cite only the foundational triple — in particular `cp_measure_bridge`
does **not** carry `invariant_measure_uniqueness` (cf. the abstract
`measure_bridge`, which does). -/

/-- info: 'CSD.LF4.cpSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorData

/-- info: 'CSD.LF4.cp_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cp_measure_bridge

-- The non-trivial-fibre compact-Kähler instance Σ = ℂℙ^{N-1} × T² and its
-- axiom-free marginal bridge π∗μL = μFS (c = 1). No invariant_measure_uniqueness.
/-- info: 'CSD.LF4.kSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorData

/-- info: 'CSD.LF4.k_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.k_measure_bridge

-- Tranche A: a non-trivial measure-preserving flow on the Kähler fibre (Φ ≠ id),
-- making the LF1 deterministic-typicality theorem non-vacuous on the instance.
/-- info: 'CSD.LF4.kFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_measurePreserving

/-- info: 'CSD.LF4.kFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_ne_id

/-- info: 'CSD.LF4.kFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_frequency_convergence

-- Tranche 1: the Born weights as the torus moment map on ℂℙ^{N-1} (a forced
-- symplectic invariant of the Kähler structure, not a carving). Headline:
-- momentMap_mk_eq_inner_sq — Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖² at a unit preparation.
/-- info: 'CSD.LF4.momentMap_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_sum_eq_one

/-- info: 'CSD.LF4.momentMap_mk_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_mk_eq_inner_sq

-- Tranche M slice 3: the Born weight as a barycentric volume ratio. The i-th
-- subdivision region of the moment polytope at Φ([ψ]) has Lebesgue-volume
-- fraction ‖⟨eᵢ,ψ⟩‖² (vertex-replacement map det = barycentric coord, via Cramer
-- + addHaar_image_linearMap). Geometric region, not carved; no operational axiom.
/-- info: 'CSD.LF4.replaceMap_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_det

/-- info: 'CSD.LF4.replaceMap_image_volume_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_image_volume_sum

/-- info: 'CSD.LF4.born_eq_volume_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_eq_volume_ratio

-- Tranche M slice 2 (reduction): the moment map along the U(N) orbit reduces the
-- Fubini-Study pushforward to the Haar law of the squared-moduli of U·rep (the
-- Dirichlet keystone; N=2 = "|U₀₀|² uniform"). Bridge lemma toward Φ∗μ_FS=uniform.
/-- info: 'CSD.LF4.momentMap_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_orbit

-- Tranche M slice 2 (option C): Born = Fubini-Study volume ratio on the ontic
-- Kähler Σ = ℂℙ¹, modulo the explicit N=2 Duistermaat-Heckman hypothesis
-- (the 0-coordinate marginal of the genuine FS measure is uniform[0,1]).
-- Axiom-clean (hypothesis-gated); momentMap measurable via the §12 lift API.
/-- info: 'CSD.LF4.momentMap_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_measurable

/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit

-- Busch-free empirical capstone: i.i.d. sampling from fubiniStudyMeasure on ℂℙ¹,
-- frequencies of the moment-sublevel outcome → the Born weight ‖⟨e₀,ψ⟩‖² via the
-- volume route (foundational triple + h_uniform hypothesis; NO busch_effect_gleason).
/-- info: 'CSD.LF4.qubit_born_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence

-- General-N joint Busch-free Born frequency convergence over a finite outcome
-- family (Born = ontic volume as hypothesis hborn). Closes LF4-todo §9.
/-- info: 'CSD.LF4.born_frequency_convergence_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_partition

-- Plan B step 1: the moment marginal of μ_FS = the Haar law of the
-- squared-modulus ratio of U·rep. Reduces h_uniform to the (deferred) Dirichlet
-- marginal "|U₀₀|² ~ Uniform[0,1] for Haar U(2)".
/-- info: 'CSD.LF4.momentMap_pushforward_eq_haar_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_pushforward_eq_haar_marginal

-- (The qubit Duistermaat–Heckman fact `fs_moment_pushforward_uniform` is now a
-- THEOREM, discharged in MomentUniform.lean; its foundational-triple pin lives in
-- the Slice 4 block below, together with the two unconditional Born consumers.)

-- Plan B Part 1 step: a unitary matrix's toEuclideanLin preserves the Euclidean
-- norm (the matrix-analytic core for the Gaussian unitary-invariance step).
/-- info: 'CSD.LF4.unitary_norm_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitary_norm_preserving

-- Plan B Part 1 (Option 2) C1: the hand-built real coordinate isometry ℝ⁴ ≃ₗᵢ[ℝ] ℂ²
-- (keeps stdGaussian on the clean real space, avoiding the ℝ/ℂ instance diamond).
/-- info: 'CSD.LF4.coords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.coords

-- Plan B Part 1 (Option 2) C4-C5: gaussianCP = fubiniStudyMeasure on ℂℙ¹, via the
-- by-hand real conjugate isometry conjR (restrictScalars ℝ diamonds in the full LF4
-- import context), unitary-invariance of the Gaussian-induced measure, and the
-- axiom-free Fubini-Study uniqueness theorem. All foundational-triple-only.
/-- info: 'CSD.LF4.conjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.conjR

/-- info: 'CSD.LF4.gaussianH_map_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianH_map_unitary

/-- info: 'CSD.LF4.gaussianCP_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_smul_invariant

/-- info: 'CSD.LF4.gaussianCP_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_eq_fubiniStudy

-- General-N Part 1 (Slice B): the projectivised standard Gaussian on ℂ^N is the
-- Fubini-Study measure on ℂℙ^{N-1}, via the real coordinate isometry
-- coordsN : ℝ^{N×2} ≃ₗᵢ ℂ^N + stdGaussian U(N)-invariance + fubiniStudyMeasure_unique.
-- The N-general analogue of gaussianCP_eq_fubiniStudy. Foundational triple.
/-- info: 'CSD.LF4.gaussianCPN_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCPN_eq_fubiniStudy

-- Plan B Part 2, Slice 1 (L5.1): the single-block squared-norm law is Exp(1/2).
-- `‖·‖²∗ N(0,I₂) = Exp(1/2)` on plain ℝ × ℝ, via polarCoord + the 1-D s=r²
-- Jacobian change of variables. Foundational triple; entry slice of the route
-- discharging `fs_moment_pushforward_uniform`.
/-- info: 'CSD.LF4.gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2

/-- info: 'CSD.LF4.expHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expHalf

/-- info: 'CSD.LF4.sqNorm_map_gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sqNorm_map_gaussian2

-- Plan B Part 2, Slice 2 (L5.2): block product = independence.
-- `gaussian2` is the product of two 1-D standard Gaussians, and the joint law of
-- the two block squared-norms factors as `expHalf × expHalf` (the independence
-- statement; the product measure carries it). Foundational triple.
/-- info: 'CSD.LF4.gaussian2_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2_eq_prod

/-- info: 'CSD.LF4.blockSqNorm_map_gaussian2_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussian2_prod

-- General-N DH Slice C (Part 2a): the N-fold block law. The joint law of the N
-- block squared-norms factors as Exp(1/2)^{⊗N} (Measure.pi_map_pi + Slice 1 per
-- block) — the independence statement at general N. Foundational triple.
/-- info: 'CSD.LF4.blockSqNorm_map_gaussianN_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussianN_pi

-- Plan B Part 2, Slice 3 (L5.3, the crux): the ratio map sends expHalf × expHalf
-- to uniform on (0,1). 2-D change of variables through the diffeo Ψ(T,S) =
-- (T·S,(1−T)·S) (Jacobian det = S), with the radial S-integral collapsing to 1.
-- Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_const

-- General-N DH Slice D.1: the radial moment ∫⁻_{S>0} Sⁿ e^{−S/2} = 2^{n+1}·n!
-- (Γ(n+1)=n!), the normalisation the post-substitution S-integral collapses to in
-- the Gamma→Dirichlet change of variables. Generalises lintegral_radial_const
-- (n=1). Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_moment

-- General-N DH Slice D.3 (the crux/gate): the Jacobian determinant of the
-- stick-breaking substitution Ψ_{M+1} is S^M. The bordered matrix (S·I block +
-- border) via the row operation "add all castSucc rows into the last" (det
-- invariant, psiMat_col_sum) → two-block-triangular. The genuine general-N content
-- (no direct Mathlib lemma). Foundational triple.
/-- info: 'CSD.LF4.psiMat_col_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_col_sum

/-- info: 'CSD.LF4.psiMat_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_det

-- General-N DH Slice D.2: the stick-breaking diffeo Ψ_N + its Fréchet derivative.
-- hasFDerivAt_PsiN (componentwise via hasFDerivAt_pi; derivative = toLin' psiMat)
-- and psiFDerivN_det = (y last)^M (LinearMap.det_toLin' + psiMat_det). Foundational
-- triple.
/-- info: 'CSD.LF4.hasFDerivAt_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hasFDerivAt_PsiN

/-- info: 'CSD.LF4.psiFDerivN_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDerivN_det

-- General-N DH Slice D.5c (capstone): the ratio map sends Exp(1/2)^{⊗N} to the
-- Dirichlet(1,…,1) law — M! times uniform on the open simplex (free coords). The
-- general-N analogue of ratioSqNorm_map_expHalf_prod; the genuine general-N DH
-- content, composing D.1-D.5b. Foundational triple. Closes Slice D.
/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_pi

-- General-N DH Slice D.4: Ψ_N is a bijection domainN (open simplex × Ioi 0) →
-- posQuadrant. PsiN_sum (∑ᵢ Ψ_N(y)ᵢ = S, the inverse-map crux), injOn_PsiN,
-- image_PsiN. Foundational triple.
/-- info: 'CSD.LF4.PsiN_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.PsiN_sum

/-- info: 'CSD.LF4.injOn_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.injOn_PsiN

/-- info: 'CSD.LF4.image_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.image_PsiN

/-- info: 'CSD.LF4.psiFDeriv_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDeriv_det

/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_prod

-- Plan B Part 2, Slice 4 (assembly + discharge): `fs_moment_pushforward_uniform`
-- (the qubit Duistermaat–Heckman fact) is now a THEOREM, not an axiom. The bridge
-- `regroup4∗ (pi gaussianReal) = gaussian2 × gaussian2` (finSumFinEquiv reindex),
-- the moment marginal `Tpi∗ (pi gaussianReal) = uniform`, and the discharge all
-- depend only on the foundational triple.
/-- info: 'CSD.LF4.regroupPi_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.regroupPi_map

/-- info: 'CSD.LF4.moment_marginal_uniform_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.moment_marginal_uniform_pi

/-- info: 'CSD.LF4.fs_moment_pushforward_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform

-- Now foundational-triple-only (the DH input is discharged); previously these
-- carried `fs_moment_pushforward_uniform` as an axiom.
/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit_uncond

/-- info: 'CSD.LF4.qubit_born_frequency_convergence_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence_uncond

-- General-N DH Slice E (Cat-1 gap): currying a product index preserves Measure.pi.
-- Mathlib proves piCurry measurable but has no measure-preserving statement; both
-- the sigma-index and product-index forms are proved here (pi_eq_generateFrom on the
-- box-of-boxes π-system). Foundational triple. Upstream candidate.
/-- info: 'MeasureTheory.map_curryProd_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.map_curryProd_pi

/-- info: 'MeasureTheory.measurePreserving_piCurry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measurePreserving_piCurry

-- General-N DH Slice E (bridge): the per-block squared-norm map sends the ℝ^{N×2}
-- standard Gaussian to Exp(1/2)^{⊗N}, via the product-index curry + Measure.pi_map_pi
-- + the single-block fact gBlock_map_pi. Bypasses Slice C. Foundational triple.
/-- info: 'CSD.LF4.blockSqNormCurry_map_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNormCurry_map_pi

-- General-N DH Slice E (headline): the free-coordinate moment map ratioN ∘ momentMap
-- pushes the genuine Fubini–Study measure on ℂℙ^M to M! · uniform on the open simplex
-- (the joint Dirichlet(1,…,1) law). The general-N analogue of fs_moment_pushforward_uniform
-- (the qubit could give only the scalar Beta marginal). Foundational triple; no Busch.
/-- info: 'CSD.LF4.fs_moment_joint_dirichlet_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_joint_dirichlet_N

-- General-N DH Slice E (Born lift). E4a: the Duistermaat–Heckman volume law on Σ
-- (μ_FS of a moment region = M!·its Lebesgue volume). E4b: the standard simplex has
-- volume (M!)⁻¹ (forced by μ_FS being a probability measure). E4c: Born weight =
-- FS volume ratio of the i-th barycentric region, for the N-1 free coordinates,
-- now UNCONDITIONAL (the qubit h_uniform is the proved headline). Foundational triple;
-- no busch_effect_gleason.
/-- info: 'CSD.LF4.fs_volume_eq_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_volume_eq_dirichlet

/-- info: 'CSD.LF4.volume_openSimplexFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.volume_openSimplexFree

/-- info: 'CSD.LF4.fs_born_volume_ratio_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N

-- Apex coordinate (the dropped vertex, index M): the affine apex map (det = 1 - ∑b
-- = b_last via det_one_sub_mul_comm) closes the last Born coordinate. With
-- fs_born_volume_ratio_N this covers all N coordinates. Foundational triple.
/-- info: 'CSD.LF4.fs_born_volume_ratio_N_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_apex

-- General-N Busch-free capstone: i.i.d. trials from μ_FS on ℂℙ^M, empirical frequencies
-- of the N barycentric Born regions → the Born weights ‖⟨eᵢ,ψ⟩‖² jointly a.s. The Born
-- values come from fs_born_volume_ratio_N(_apex) (the volume route), so the chain is
-- foundational-triple-only — NO busch_effect_gleason. The general-N analogue of
-- qubit_born_frequency_convergence_uncond; the headline empirical payoff.
/-- info: 'CSD.LF4.born_frequency_convergence_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N

-- N=2 consistency cross-check: the qubit fs_moment_pushforward_uniform is kernel-derived
-- from the general-N fs_moment_joint_dirichlet_N (M:=1). Machine-confirms the general-N
-- statement faithfully generalises the independently-proved qubit result. Foundational triple.
/-- info: 'CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet

-- The ofKählerPreparation constructor: a concrete LF3.PureSingletPreparation
-- on the non-trivial-fibre compact-Kähler instance. bridge_op_p is proved
-- Busch-free via born_rank_one_direct + the carving identity kMuPsi_kRegion,
-- so the constructor stays foundational-triple only.
/-- info: 'CSD.LF4.ofKählerPreparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation

-- Applying the LF3 chain capstone to the concrete prep gives a non-vacuous
-- empirical statement. Now foundational-triple-only (2026-06-02): the chain bridge
-- was re-routed off Busch onto the volume-ratio Born step, so this end-to-end
-- ontic capstone no longer cites busch_effect_gleason.
/-- info: 'CSD.LF4.ofKählerPreparation_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation_singlet_frequency_convergence

-- LF4 §14 discharge (projector observables, single-qubit Stern-Gerlach):
-- the Hilbert ↔ ontic-measure identity, foundational triple only.
/-- info: 'CSD.LF4.sg_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_observable_correspondence

-- The non-vacuous LF3-chain Stern-Gerlach capstone (N = 2 analog of
-- ofKählerPreparation_singlet_frequency_convergence). Foundational triple only.
/-- info: 'CSD.LF4.sg_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_frequency_convergence

-- LF4 §14.2 first step beyond projectors: Pauli observable σ·a via the
-- spectral-decomposition signed-indicator construction. Foundational triple only.
/-- info: 'CSD.LF4.pauliDot_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_observable_correspondence

-- LF4 §14.2 at N = 4: two-qubit Pauli observables on the singlet (covering
-- all 9 Mermin-Peres observables and the 4 Hardy single-qubit Paulis).
/-- info: 'CSD.LF4.sigmaDotLeft_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotLeft_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotRight_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotRight_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotJoint_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotJoint_observable_correspondence

-- Hardy LF3-chain capstones: the four Hardy probability constraints lifted to
-- ontic frequency-convergence theorems on the Hardy-state Kähler preparation.
-- Headline pin (positive coincidence) + load-bearing zero (A'=+1, B'=+1).
/-- info: 'CSD.LF4.hardy_freq_convergence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_AB

/-- info: 'CSD.LF4.hardy_freq_convergence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_A'_B'

-- Hardy §14 observable correspondence (Hilbert ↔ ontic): closes the QM ↔ LF4
-- amplitude loop. Headline pin (the positive-coincidence Hilbert ↔ ontic match)
-- + the load-bearing zero observable correspondence.
/-- info: 'CSD.LF4.hardy_observable_correspondence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_AB

/-- info: 'CSD.LF4.hardy_observable_correspondence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_A'_B'

-- LF4 §14.2 general N×N spectral expansion of the Hilbert expectation.
-- The Hilbert-side spectral identity ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²
-- for any Hermitian A and any state ψ — unlocks variance / uncertainty
-- ontic correspondences beyond the projector / ±1-eigenvalue case.
/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion

/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion_re

-- LF4 §14.2 ontic-side multi-region spectral carving (Phase A foundation
-- + Phase C carving identity + Phase D integration headline).
/-- info: 'CSD.LF4.fibreShiftedArc_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fibreShiftedArc_volume

/-- info: 'CSD.LF4.diracProd_spectralRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.diracProd_spectralRegion

/-- info: 'CSD.LF4.integral_spectralOntic_eq_inner_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOntic_eq_inner_re

-- LF4 §14.2 variance: Hilbert-side norm-squared, spectral variance,
-- Hilbert ↔ spectral identity, and ontic ↔ Hilbert variance correspondence.
/-- info: 'CSD.LF4.hilbert_norm_sq_apply_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hilbert_norm_sq_apply_hermitian

/-- info: 'CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_variance

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff

-- LF4 §14.2 Robertson uncertainty on the Kähler instance: ontic-variance
-- bridge to QM variance, and the headline ontic-variance Robertson bound.
/-- info: 'CSD.LF4.QM_variance_eq_spectralVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.QM_variance_eq_spectralVariance

/-- info: 'CSD.LF4.kahler_robertson_ontic_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kahler_robertson_ontic_variance

-- LF4 §14.2 concrete instance: σ_x, σ_y Robertson saturation on |0⟩.
/-- info: 'CSD.LF4.pauli_xy_robertson_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauli_xy_robertson_saturation

-- LF4 §14.2 parametric: Robertson for σ·â, σ·b̂ on |0⟩, geometric form.
/-- info: 'CSD.LF4.pauliDot_robertson_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_robertson_zPlus

-- The pure-state ontic Born capstone composes LF1 frequency convergence with the
-- LF2 operational Born derivation, so it cites the Busch axiom (and only it,
-- beyond the foundational triple).
/-- info: 'CSD.LF4.ontic_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ontic_born_frequency

-- POVM tranche P.1 (POVM type + Born-weight completeness) and P.2 (Naimark
-- dilation + Born transfer: POVM Born weight = projective Born weight of the
-- dilated state against the ancilla block projector). Both foundational triple
-- only — the dilation is supplied data, no Busch / invariant-measure axiom.
/-- info: 'CSD.LF2.POVM.weights_sum_eq_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF2.POVM.weights_sum_eq_normSq

/-- info: 'CSD.LF2.POVM.weights_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF2.POVM.weights_sum_eq_one

/-- info: 'CSD.LF4.NaimarkDilation.born_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.NaimarkDilation.born_transfer

-- POVM tranche P.3a (block decomposition): the POVM Born weight is the sum, over
-- the i-th ancilla block, of the dilated computational-basis (rank-1) Born
-- weights — each of which the general-N result reads as a Fubini-Study volume.
-- Foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_block_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_block_sum

-- POVM tranche P.3b (FS-volume identification): the POVM Born weight is the sum,
-- over the i-th ancilla block, of the genuine Fubini-Study typicality volumes of
-- the dilated barycentric cells on Σ' = ℂℙ^{N·|ι|−1}. Composes P.3a with the
-- general-N Born = FS-volume result through the reindex isometry. Carving-free,
-- Gleason-free (no busch_effect_gleason); foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_dilated_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_dilated_volume

-- POVM tranche P.4 (empirical capstone): i.i.d. Fubini-Study trials on the dilated
-- Σ' have the i-th POVM outcome's empirical frequency (the block sum of dilated
-- cell frequencies) converge a.s. to the POVM Born weight pᵢ(ψ). The empirical →
-- Born chain for a general POVM, carving-free and Gleason-free. Foundational triple.
/-- info: 'CSD.LF4.povm_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume

-- POVM tranche P.5 (existence): the canonical Naimark dilation built from the CFC
-- square roots √Eᵢ inhabits NaimarkDilation P for every POVM, making the Phase-1
-- POVM Born = Kähler-volume results unconditional (no longer needing a supplied
-- dilation). Foundational triple only — the CFC sqrt and isometry/pullback proofs
-- add no axioms.
/-- info: 'CSD.LF4.naimarkV_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_isom

/-- info: 'CSD.LF4.naimarkV_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_pullback

/-- info: 'CSD.LF4.canonicalNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.canonicalNaimark

end CSD.Tests.AxiomAudit
