/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: Foundations

**Category:** Special (axiom-posture regression pins; G9 split part).

LF1/LF2/LF3 pins (typicality, operational stratum, singlet chain), incl. relative-name pins resolved through the LF1-LF3 opens.

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.Foundations`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

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

-- (The abstract `measure_bridge` + the `invariant_measure_uniqueness` axiom it carried
-- were removed 2026-06-04; the bridge holds axiom-free on the concrete instances —
-- `cp_measure_bridge` / `k_measure_bridge`, pinned below. `busch_effect_gleason` was the
-- last imported axiom; it was DISCHARGED 2026-07-21 — see below — so the corpus now imports
-- ZERO axioms beyond the foundational triple.)
/-- info: 'CSD.LF2.born_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms born_quadratic

-- QuantumChannel (general CPTP maps, 2026-07-18): channels in Kraus form (∑ₖ Kₖ†Kₖ=1). T1 CPTP-forward:
-- channelApply sends density operators to density operators (apply_posSemidef via mul_mul_conjTranspose_same
-- + posSemidef_sum; apply_trace via trace cyclicity + the constraint), unitaryChannel, comp (channels
-- compose). T2 Stinespring: dilation_isometry (V†V=1) + stinespring (Φ(ρ) = Tr_E(VρV†) via partialTraceRight).
-- T3 Choi: choiMatrix_posSemidef (the Choi-Jamiolkowski completely-positive witness, ∑ₖ vec(Kₖ)vec(Kₖ)† PSD).
-- T4 Choi converse (ChoiConverse.lean, 2026-07-19): choi_iff_posSemidef — a matrix on Fin M × Fin N is the
-- Choi matrix of some Kraus family iff it is PSD; choiOfKraus_krausOfChoi reconstructs the family Kᵢ=√λᵢ·unvec(eᵢ)
-- from the spectral decomposition (IsHermitian.eq_eigen_outer). Closes Choi's theorem (CP ⟺ PSD Choi).
/-- info: 'CSD.LF2.QuantumChannel.channelApply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.channelApply

/-- info: 'CSD.LF2.QuantumChannel.apply_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.apply_trace

/-- info: 'CSD.LF2.QuantumChannel.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.comp

/-- info: 'CSD.LF2.QuantumChannel.dilation_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.dilation_isometry

/-- info: 'CSD.LF2.QuantumChannel.stinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.stinespring

/-- info: 'CSD.LF2.QuantumChannel.choiMatrix_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.choiMatrix_posSemidef

/-- info: 'CSD.LF2.IsHermitian.eq_eigen_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.IsHermitian.eq_eigen_outer

/-- info: 'CSD.LF2.choiOfKraus_krausOfChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.choiOfKraus_krausOfChoi

/-- info: 'CSD.LF2.choi_iff_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.choi_iff_posSemidef

/-- info: 'CSD.LF2.DensityOperatorIx.reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF2.DensityOperatorIx.reduced

/-- info: 'CSD.LF2.pure_state_born_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights

-- `busch_effect_gleason` discharged 2026-07-21: this is now foundational-triple only.
/-- info: 'CSD.LF2.pure_state_born_weights_of_certainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights_of_certainty

/-- info: 'CSD.LF2.PurePreparation.OP_certain_at_ψ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.OP_certain_at_ψ

/-- info: 'CSD.LF2.PurePreparation.born_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one

/-- info: 'CSD.LF2.PurePreparation.born_rank_one_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one_direct

-- Direct pin (CL-005 audit recommendation, 2026-08-06): the effect-Gleason theorem itself,
-- previously pinned only transitively via pure_state_born_weights_of_certainty.
/-- info: 'CSD.LF2.OperationalPackage.effect_gleason_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OperationalPackage.effect_gleason_representation

-- Direct pin (landing-surface axiom reconciliation, 2026-08-09): the rank-one density
-- uniqueness lemma. It was carried as a named axiom in earlier revisions and in the
-- published LF-series papers, discharged 2026-05-18 via
-- Matrix.PosSemidef.dotProduct_mulVec_zero_iff, but never pinned -- so CI could not have
-- caught drift in the one remaining paper-vs-repo axiom item that lacked coverage.
-- See specs/papers-vs-repo.md.
/-- info: 'CSD.LF2.rankOneDensity_unique_of_certainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rankOneDensity_unique_of_certainty

-- F-01 discharge (G1, 2026-08-06): the bridge is load-bearing via the transport theorems —
-- integral_comp_pi carries an ontic Σ-integral into the projective μFS-integral through
-- bridge_eq, and fromPreparation_liouville_apply computes the Liouville-prepared operational
-- probability AS the μFS-integral (c = 1). fromPreparation itself still carries the bridge
-- type-level only (its own #print-axioms hygiene note is unchanged); check-semantic-mutations.sh
-- guards all three facts.
/-- info: 'CSD.LF2.MeasureBridgeData.integral_comp_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureBridgeData.integral_comp_pi

/-- info: 'CSD.LF2.OperationalPackage.fromPreparation_liouville_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OperationalPackage.fromPreparation_liouville_apply

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

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st_direct

/-- info: 'CSD.LF3.MeasurementUnitary.ofUnitaryTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasurementUnitary.ofUnitaryTensorEmbedding

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

-- Trial-witness tranche (2026-06-11): the canonical i.i.d. FS trial process.
-- Until this tranche every volume-frequency capstone quantified over an
-- abstract trial bundle (Ω, Pr, X, hX, hlaw, hindep) that no corpus theorem
-- constructed. The canonical coordinate process (Ω = ℕ → ℂℙ^{N−1},
-- Pr = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀), X n = (· n))
-- inhabits the bundle: marginal law via Measure.infinitePi_map_eval, joint
-- independence via iIndepFun_infinitePi, indicator pairwise independence via
-- IndepFun.comp (the Cat-1 glue iIndepFun.pairwise_indepFun_indicator_preimage).
-- The _canonical capstones are the originals with the trial bundle discharged,
-- conclusions verbatim. Measure-theoretic existence of the sampling law only:
-- the physical i.i.d.-preparation reading remains the LF1 typicality posit
-- (SO-1). Foundational triple throughout; Gleason-free.
/-- info: 'Set.indicator_const_preimage_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Set.indicator_const_preimage_comp

-- Mixed-Born on the COMPOSITE INDEXED density type (2026-07-19, SL-T3 T9 residual closed): the
-- MixedEnsemble content (affine Born + spectral ensemble) ported from DensityOperator (Fin N) to
-- DensityOperatorIx ι (arbitrary Fintype index — the type the bipartite/composite interface uses via
-- reduced/reducedLeft). traceForm_ensemble = affine; mixedEnsemble_capstone = Born is the
-- eigenvalue-weighted avg of pure Born rules, on the indexed type. Closes the reported density-matrix gap.
/-- info: 'CSD.LF2.DensityOperatorIx.traceForm_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.traceForm_ensemble

/-- info: 'CSD.LF2.DensityOperatorIx.mixedEnsemble_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.mixedEnsemble_capstone

end CSD.Tests.AxiomAudit
