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

-- CL-001's ledger constant is the UNDERLYING theorem; the pin above names the top-level
-- alias that matches the manuscript. The alias is defined by the theorem, so its footprint
-- already covered it transitively, but the ledger row pointed at a name nothing pinned
-- directly. Pinned in its own right 2026-08-19 so the row is evidenced by its own constant.
/-- info: 'CSD.LF1.OnticSetup.TrialModel.main_theorem_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF1.OnticSetup.TrialModel.main_theorem_ae

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

-- Rule-of-two hoists for the composites premise conversion (2026-09-02, brick 2): outerProduct and its
-- API generalised from Fin N to an arbitrary Fintype index in LF2/BornWrapper.lean (the ChoiConverse copy
-- of IsHermitian.eq_eigen_outer retired, density_eq_eigen_ensemble now consumes it);
-- outerProduct_mul_outerProduct_trace (Tr(|ψ⟩⟨ψ| |φ⟩⟨φ|) = |⟨ψ,φ⟩|², the kernel of born_quadratic);
-- DensityOperatorIx.rankOne (pure preparations on an arbitrary index, the Ix-form of rankOneDensity) with
-- traceForm_rankOne_outerProduct (its Born rate on a rank-one effect is the squared overlap).
/-- info: 'CSD.LF2.outerProduct_mul_outerProduct_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.outerProduct_mul_outerProduct_trace

/-- info: 'CSD.LF2.DensityOperatorIx.rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.rankOne

/-- info: 'CSD.LF2.DensityOperatorIx.traceForm_rankOne_outerProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.traceForm_rankOne_outerProduct

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

-- CL-007 (added 2026-08-19): the CPTP capstone was a LEDGER HEADLINE with no axiom pin.
-- Found by a mechanical sweep of the 43 non-validated claims against the pin set, not by
-- any guard: `check-validation-ledger` verifies that a claim's module and constant are
-- linked, not that the constant is pinned. Promotion criterion 2 (`#print axioms` shows
-- only the foundational footprint) was therefore unevidenced for this row.
/-- info: 'CSD.LF2.QuantumChannel.cptp_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.cptp_capstone

-- CL-003 (added 2026-08-19, same sweep): the ledger headline itself was unpinned. Its
-- CONSEQUENCES were pinned (bridge_eq, fromPreparation_liouville_apply, the F-01 row),
-- which is how it went unnoticed — the neighbourhood looked covered.
/-- info: 'CSD.LF2.OperationalPackage.fromPreparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.OperationalPackage.fromPreparation

-- The detector-axis spinors (2026-08-10, LF3/Spinor.lean). Built for the C1
-- nudge-locality correction: `nudgedSinglet` is the vector of sqrt(P_st), all phases
-- stripped, so it is NOT a local-unitary image of the singlet (at a perp b it is a
-- PRODUCT state while the singlet is maximally entangled). These supply the genuine
-- local eigenbasis. `spinProj_eq_outer` is the load-bearing one: it gives
-- Pi^s(a) (x) Pi^t(b) = (u (x) w)(u (x) w)^H, hence the Born identity on the local object.
/-- info: 'CSD.LF3.two_mul_spinProj_eq_raw_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.two_mul_spinProj_eq_raw_outer

/-- info: 'CSD.LF3.spinor_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.spinor_normSq

/-- info: 'CSD.LF3.spinProj_eq_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.spinProj_eq_outer

/-- info: 'CSD.LF3.wingBasisUnitary_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.wingBasisUnitary_mem_unitaryGroup

/-- info: 'CSD.LF3.jointSpinProj_eq_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.jointSpinProj_eq_outer

-- Operational no-signalling at the MEASURE level (2026-08-10). The pointwise form
-- (F_A(a,b,x) = F_A(a,b',x) on both wings) is not merely too strong -- over a
-- deterministic shared state it IS the setting-local response pair that
-- no_product_partition_realises_singlet rules out, so it is inconsistent with the corpus.
-- Equality of MARGINAL MEASURES is the correct condition. WARNING: stated relative to one
-- fixed mu across all four contexts, and that fixture IS measurement independence -- a
-- genuine Bell premise, previously invisible.
/-- info: 'CSD.LF3.singlet_operational_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF3.singlet_operational_no_signalling

-- CL-008 UNPOPULATED INTERFACE CLOSED (2026-08-25, LF3/PointerWitness.lean).
-- LF3_main_theorem takes S : SystemApparatusSetup, and until now NO TERM OF THAT TYPE EXISTED
-- anywhere in the corpus -- every occurrence was a hypothesis binder.  Same defect class as
-- RecordLayer.DeIsolationInteraction before Q12-a: an interface whose antecedent is never shown
-- satisfiable.  Found by the CL-008 premise-to-constructor trace (S3, 2026-08-24).
-- ⚠️ NOT the degenerate witness.  proj .plus = 1, proj .minus = 0 satisfies EVERY field
-- (self-adjoint, idempotent, orthogonal, complete) and would populate the interface while proving
-- nothing -- it describes a pointer that always reads +.  spinPointerProjectors is the genuine
-- two-outcome algebra Pi^±(a) = (1 ± sigma.a)/2, both projectors rank one.
-- ★ Built entirely from the corpus's own concrete spin layer: spinProj plus three of the four field
-- obligations were already proved in LF3/Setup.lean (spinProj_isHermitian, spinProj_idem,
-- spinProj_complete).  Only ORTHOGONALITY was missing, and it falls out of pauliDot_sq:
-- Pi^+ Pi^- = (1 - (sigma.a)^2)/4 = 0.  Matrix.toEuclideanCLM is a STAR-algebra equivalence, so each
-- field transports by the structure map it corresponds to -- map_mul for idempotence and
-- orthogonality, map_add/map_one for completeness, map_star for self-adjointness.
-- ⚠️ INHABITATION ONLY.  This does not change what the bundle CONTRIBUTES: CL-008's trace found the
-- singlet content of LF3_main_theorem rides entirely on ctx : MeasurementContext (conjuncts 1-6),
-- while S enters only conjuncts 7-8, which are its own axioms echoed back (pointer_a_complete S is
-- literally S.ptrA.complete).  The row's old load-bearing text "bundled singlet preparation
-- hypotheses" misdescribed that and was corrected.
/-- info: 'CSD.LF3.spinProj_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF3.spinProj_orthogonal

/-- info: 'CSD.LF3.spinSystemApparatusSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF3.spinSystemApparatusSetup

end CSD.Tests.AxiomAudit
