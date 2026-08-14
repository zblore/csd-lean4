/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: Dynamics

**Category:** Special (axiom-posture regression pins; G9 split part).

LF5 + LF6 pins (measurement dynamics, entangled de-isolation, decoherence, contextuality no-gos).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.Dynamics`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- LF5-A (von Neumann measurement coupling unitary): the adder permutation
-- σ(j,k) = (j, j+k) on Fin N × Fin N (system × apparatus), its manifestly-unitary
-- permutation matrix, and the ground-apparatus copy σ(j,0) = (j,j). First file of
-- the LF5 measurement-dynamics layer (the D1 frontier). Foundational triple.
/-- info: 'CSD.LF5.vnUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnUnitary_unitary

/-- info: 'CSD.LF5.vnPerm_ground' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnPerm_ground

-- LF5-B (measurement flow): the reindexed vN coupling unitary acting on the
-- dilated projective ontic space ℙ ℂ (EuclideanSpace ℂ (Fin m)) (canonically
-- ℂℙ^{N·N−1} at e = finProdFinEquiv). FS-invariance (the Liouville / hΦ_pres
-- content), Φ_vN ≠ id (genuine measurement dynamics, the D1 increment), and the
-- basis-ray adder action (the LF5-C input). Foundational triple.
/-- info: 'CSD.LF5.measurementFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_measurePreserving

/-- info: 'CSD.LF5.measurementFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_ne_id

/-- info: 'CSD.LF5.measurementFlow_mk_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_mk_single

-- LF5-C (de-isolation realises the dilation): the dynamically-realised Naimark
-- dilation isometry V = U_vN ∘ (· ⊗ a₀) of the computational-basis projective
-- POVM — isometry, pointer-block pullback Vᴴ Πᵢ V = |eᵢ⟩⟨eᵢ|, the NaimarkDilation
-- inhabitant, the post-flow coordinates U_vN(ψ⊗a₀) = ∑ⱼ ψⱼ·(eⱼ⊗aⱼ), the block-i
-- Born weight ‖⟨eᵢ,ψ⟩‖², and the projective-level realisation theorem tying the
-- LF5-B flow Φ_vN to the dilation. Foundational triple.
/-- info: 'CSD.LF5.vnNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnNaimark

/-- info: 'CSD.LF5.vnDilationV_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_pullback

/-- info: 'CSD.LF5.vnDilationV_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_isom

/-- info: 'CSD.LF5.vnDilation_block_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_block_weight

/-- info: 'CSD.LF5.measurementFlow_realises_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_realises_dilation

/-- info: 'CSD.LF5.vnDilationV_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_mulVec

/-- info: 'CSD.LF5.basisPOVM_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.basisPOVM_weight

-- LF5-D part 2 (pointer frequencies of the de-isolation flow → Born): the
-- unconditional engine instantiated at the dynamically-realised dilation
-- vnNaimark, at the non-generic post-flow state Vψ (off-diagonal cells FS-null).
-- Pointer-i committed FS volume = Born weight ‖⟨eᵢ,ψ⟩‖² for every unit ψ, and
-- the empirical capstone: i.i.d. FS trials on the dilated ℂℙ^{N²−1} have
-- pointer-block frequencies → Born a.s. Foundational triple.
/-- info: 'CSD.LF5.vnDilation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_pointer_volume

/-- info: 'CSD.LF5.vnDilation_pointer_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_pointer_frequency

-- LF5-E (capstone): the LF5 layer headline measurement_flow_born_frequency —
-- the single named chain theorem: Φ_vN ≠ id (genuine measurement dynamics),
-- FS measure-preserving (Liouville admissibility), context-fixed (the same
-- flow realises the dilation for every preparation), pointer-i committed FS
-- volume = Born weight, and a.s. pointer-block frequencies → Born, for every
-- unit ψ. Pure assembly of the LF5-B/C/D theorems (no new mathematical
-- content); closes the single-system projective tier of D1. Foundational
-- triple.
/-- info: 'CSD.LF5.measurement_flow_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_born_frequency

/--
info: 'CSD.LF5.measurement_flow_born_frequency_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_born_frequency_canonical

/-- info: 'CSD.LF5.vnPointerOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnPointerOutcome_preimage_some

/--
info: 'CSD.LF5.measurement_flow_outcome_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_outcome_frequency

/--
info: 'CSD.LF5.measurement_flow_outcome_frequency_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_outcome_frequency_canonical

-- LF5 QEC tranche (SyndromeFlow): the three-qubit bit-flip code's syndrome
-- measurement as a coarse-grained de-isolation flow. The stabilisers Z₁Z₂, Z₂Z₃
-- are diagonal in the computational basis, so the syndrome is a coarse-graining
-- (synClass) of the LF5 N=8 Z-basis measurement flow; the syndrome-block FS
-- volume equals the block sum of computational-basis Born weights = a sum of
-- Fubini–Study volumes (vnDilation_pointer_volume at N=8 + finite additivity);
-- the codeword corollary gives the deterministic syndrome + matrix-transport
-- recovery. Projective / coherent-error tier only; Born numbers reused from the
-- FS-volume engine; the CSD sector is posited (SO-1); decoherence/partial-trace NOT here (gated
-- entangled tier). Foundational triple only.
/-- info: 'CSD.LF5.synClass_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.synClass_fiber_card

/-- info: 'CSD.LF5.errorSyndrome_synClass3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.errorSyndrome_synClass3

/-- info: 'CSD.LF5.syndromeRegion_fs_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeRegion_fs_volume

/-- info: 'CSD.LF5.syndromeWeight_eq_fs_volume_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeWeight_eq_fs_volume_sum

/-- info: 'CSD.LF5.syndromeWeight_X1_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeWeight_X1_logical

/-- info: 'CSD.LF5.syndrome_flow_born_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_volume

-- LF5 QEC syndrome tranche (SyndromeOutcome): the mechanical syndrome-granularity
-- coarse-graining (synClass) of the pointer-level LF5-D frequency
-- (vnDilation_pointer_frequency) and LF5-F outcome map (vnPointerOutcome). At N=8:
-- the syndrome-class block frequencies converge a.s. to syndromeWeight (a finite
-- class sum of pointer-block limits, tendsto_finsetSum); synOutcome is the
-- per-microstate syndrome outcome function (vnPointerOutcome.map synClass) whose
-- some-s fibre is the class-block union; the syndrome outcome event frequency
-- (a single event per syndrome) converges a.s. to syndromeWeight (union-indicator
-- split over the genuinely disjoint class cells via bornRegion_pairwiseDisjoint +
-- e injectivity). Projective / coherent-error tier; Born numbers reused; the CSD sector is posited (SO-1);
-- decoherence NOT here. Foundational triple only.
/-- info: 'CSD.LF5.syndrome_flow_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_frequency

/-- info: 'CSD.LF5.syndrome_flow_born_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_frequency_canonical

/-- info: 'CSD.LF5.synOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.synOutcome_preimage_some

/-- info: 'CSD.LF5.syndrome_flow_outcome_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_outcome_frequency

/-- info: 'CSD.LF5.syndrome_flow_outcome_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_outcome_frequency_canonical

-- LF6-A.1 (ForcedContextuality): the conceptual crux of the entangled-singlet
-- de-isolation tier (first concrete attack on D1's entangled frontier). A product
-- (setting-local, non-contextual) outcome-partition of Σ on a shared (Λ,μ) IS a
-- deterministic LHV model; by Bell/CHSH no such partition reproduces the singlet,
-- so any de-isolation carve realising the singlet is jointly contextual (FORCED,
-- not posited). no_product_partition_realises_singlet routes through E91
-- lhvCHSH_abs_le_two (the LHV |S|≤2 cap) + Bell.chsh_singlet_at_optimal_angles
-- (the singlet 2√2); it REUSES the corpus Bell machinery, no Bell re-proof.
-- engine_joint_nonfactorises (P_st(s,t) ≠ P_A·P_B = 1/4 at aligned axes) and
-- engine_marginal_factorises (each marginal = 1/2, no-signalling, reusing LF3
-- marginal_*/no_signalling_*) are the Σ-volume engine's non-factorising-joint /
-- factorising-marginal pair. productPartition_nonvacuous: product partitions exist
-- and reproduce SOME (non-singlet) correlation, so the no-go is non-vacuous.
-- Residue SO-1 (entangled sector posited); LF6-A.2 (full ℂℙ¹⁵ de-isolation flow)
-- deferred. Foundational triple only.
/-- info: 'CSD.LF6.no_product_partition_realises_singlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_singlet

/-- info: 'CSD.LF6.productPartition_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.productPartition_nonvacuous

/-- info: 'CSD.LF6.engine_joint_nonfactorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.engine_joint_nonfactorises

/-- info: 'CSD.LF6.engine_marginal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.engine_marginal_factorises

-- LF6-C.1 (GHZContextuality): the multipartite analogue of A.1; the first
-- general-N-tier instance of D1's entangled frontier. GHZ forces contextuality
-- DETERMINISTICALLY (Mermin all-or-nothing: no LHV plus/minus 1 assignment at all),
-- a qualitatively stronger forcing than the singlet's statistical CHSH bound.
-- no_product_partition_realises_ghz: a product (setting-local, non-contextual)
-- plus/minus 1 partition reproducing the four GHZ perfect correlations forces each
-- product integrand pointwise-determinate a.e. (pm_ae_eq, where the plus/minus 1
-- hypothesis is load-bearing), yielding ONE microstate with a deterministic local
-- assignment that CSD.Empirical.GHZ.no_lhv_assignment_for_ghz forbids; it ROUTES
-- THROUGH that no-go, no GHZ re-proof. ghz_each_correlation_locally_realisable
-- isolates locality as the other load-bearing leg (each correlation alone is
-- locally realisable). ghz_engine_joint_nonfactorises (<XXX>=1 != 0*0*0) and
-- ghz_engine_marginal_factorises (each single-wing marginal = 0, no-signalling)
-- are the Sigma-volume engine's non-factorising-joint / factorising-marginal pair.
-- productPartition_ghz_nonvacuous: product partitions exist. Residue SO-1 (GHZ
-- entangled sector posited); LF6-C.2 (full GHZ de-isolation flow) built below.
-- Foundational triple only.
/-- info: 'CSD.LF6.no_product_partition_realises_ghz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghz

/-- info: 'CSD.LF6.productPartition_ghz_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.productPartition_ghz_nonvacuous

/-- info: 'CSD.LF6.ghz_engine_joint_nonfactorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_engine_joint_nonfactorises

/-- info: 'CSD.LF6.ghz_engine_marginal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_engine_marginal_factorises

/-- info: 'CSD.LF6.ghz_each_correlation_locally_realisable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_each_correlation_locally_realisable

/-- info: 'CSD.LF6.ghz_forced_contextuality_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_forced_contextuality_capstone

-- LF6-C.2 (GHZDeisolationFlow): the DYNAMICAL realisation of the multipartite GHZ
-- de-isolation tier, mirroring A.2 at three parties. A genuine deterministic
-- FS-measure-preserving de-isolation flow Φ ≠ id (LF5 measurementFlow @ N=8 on the
-- dilated Σ' = ℂℙ^{63} = ℙ(ℂ⁸⊗ℂ⁸)) whose context-fixed BornRegion pointer-block volumes
-- are the GHZ Born weights. ghzDeisolation_pointer_volume (the headline) COMPOSES LF5
-- vnDilation_pointer_volume @ N=8 (pointer-block FS volume = ‖⟨e_i, φ⟩‖², Gleason-free,
-- Born = volume IMPORTED from the DH/FS-volume engine, not re-derived) with the reindex
-- coordinate-Born identity nudgedGHZ_born (nudgedGHZ = ghzState in the Fin 8 computational
-- basis; ghz_normSq_eq_weight GENUINELY COMPUTES the diagonal weights 1/2 on (0,0,0)/(1,1,1),
-- 0 elsewhere). ghzDeisolation_frequency: a.s. block frequencies → the GHZ Born weight (LF5
-- vnDilation_pointer_frequency @ N=8 + nudgedGHZ_born). This is the MINIMAL computational-basis
-- carve (diagonal weights); ghzDeisolation_contextuality_anchor RE-EXPORTS C.1
-- no_product_partition_realises_ghz as the contextuality anchor of the Mermin-context carve
-- (the diagonal carve is NOT itself contextual). The Mermin X/Y carve tying block correlations
-- to C.1 -- the three-party analogue of A.2's blockVolume_correlation -- is C.3
-- (GHZMerminCarve.lean), and the local product flow V_0(x)V_1(x)V_2 is C.4 (GHZLocalFlow.lean);
-- both have landed. Flow REALISES (not derives) the GHZ
-- measurement. Residue SO-1 (GHZ entangled sector posited). Foundational triple only, no busch.
/-- info: 'CSD.LF6.ghzDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_pointer_volume

/-- info: 'CSD.LF6.ghzDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_frequency

/-- info: 'CSD.LF6.ghzDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_ne_id

/-- info: 'CSD.LF6.ghzDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_measurePreserving

/-- info: 'CSD.LF6.ghzDeisolation_contextuality_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_contextuality_anchor

/-- info: 'CSD.LF6.ghzDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_flow_capstone

-- LF6-C.3 (GHZMerminCarve, 2026-07-01): the GHZ Mermin-context carve — the GENUINE
-- contextual increment C.2 deferred. NEW infrastructure: the GHZ Pauli-context joint
-- eigenstructure (ghzMerminEig, the tensor of the genuine single-qubit sigma_x/sigma_y
-- eigenstates; localEig_eigenvector proves each local factor is a real Pauli eigenvector
-- with eigenvalue signC o = ±1 — the three-party analogue of LF3 singletJointEig), plus
-- the Born identity ghzMerminEig_born (‖⟨ghz, ghzMerminEig ctx o⟩‖² = (1/16)(1+signProd o·pv)²,
-- genuinely computed from the 8 GHZ basis evaluations + the local amplitudes).
-- ghzDeisolation_blockVolume_correlation (THE headline): for every Mermin context with real
-- phase product pv, the carve's sign-product-weighted pointer-block FS-volume sum = pv = the
-- Mermin expectation (⟨XXX⟩=+1, ⟨XYY⟩=⟨YXY⟩=⟨YYX⟩=−1). GENUINELY COMPUTED (LF5
-- vnDilation_pointer_volume @ N=8 block volumes composed with the Mermin Born identity), NOT
-- asserted — this is what C.2's diagonal re-export lacked. carveBlockCorrelation_eq_xxx ties the
-- carve's ⟨XXX⟩ to the QM Hilbert Mermin expectation (via ghz_expectation_xxx) through distinct
-- machinery meeting at +1. ghzDeisolation_carve_not_product (the dynamical carve-tie, FOUR-CONTEXT
-- tie CLOSED): feeds the carve's OWN four achieved Mermin correlations into C.1
-- no_product_partition_realises_ghz — no setting-local ±1 product partition reproduces them,
-- triggering Mermin's +1=−1 all-or-nothing contradiction; upgrades C.2's bare re-export
-- ghzDeisolation_contextuality_anchor to a genuine carve-tied theorem. Born = FS-volume IMPORTED
-- from the DH/moment-map engine, not re-derived; flow realises not derives; only the local
-- single-qubit eigen-equation proved (tripartite eigen-eq is the tensor, definitional). Residue SO-1
-- (GHZ entangled sector posited). Foundational triple only, no busch, no native_decide.
/-- info: 'CSD.LF6.localEig_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localEig_eigenvector

/-- info: 'CSD.LF6.ghzMerminEig_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzMerminEig_born

/-- info: 'CSD.LF6.ghzDeisolation_blockVolume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_blockVolume_correlation

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_xxx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_xxx

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_xyy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_xyy

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_yxy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_yxy

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_yyx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_yyx

/-- info: 'CSD.LF6.ghzDeisolation_carve_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_carve_not_product

/-- info: 'CSD.LF6.ghzMermin_carve_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzMermin_carve_capstone

-- LF6-A.2 (SingletDeisolationFlow): the DYNAMICAL realisation of the entangled
-- de-isolation tier. A genuine deterministic FS-measure-preserving de-isolation
-- flow Φ ≠ id (LF5 measurementFlow @ N=4 on the dilated Σ' = ℂℙ¹⁵ = ℙ(ℂ²⊗ℂ²⊗ℂ²⊗ℂ²))
-- whose CONTEXTUAL joint-BornRegion carve reproduces the LF3 singlet kernel P_st.
-- singletDeisolation_pointer_volume (the headline) COMPOSES LF5 vnDilation_pointer_volume
-- @ N=4 (pointer-block FS volume = ‖⟨e_i, φ⟩‖², Gleason-free, Born=volume IMPORTED from
-- the DH/FS-volume engine) with the nudge coordinate-Born identity nudgedSinglet_born
-- (unitary-invariance step + LF3 singletJointEig_born), at the prepared state
-- φ = (U_A^x⊗U_B^y)† ψ⁻ (singlet in the rotated axis-context basis). The carve is the
-- joint moment subdivision, NEVER a setting-local {ptr_A=i}∩{ptr_B=j} product region.
-- singletDeisolation_blockVolume_correlation: the carve's block-volume correlation is
-- the singlet's −a·b (block volume = P_st + LF3 correlation_eq_neg_dot).
-- singletDeisolation_carve_contextual: ROUTES THROUGH A.1 no_product_partition_realises_singlet
-- — no setting-local ±1 product partition reproduces the carve's −a·b correlation, so the
-- carve is contextual (the safety anchor; does NOT assume the forbidden product structure).
-- singletDeisolation_frequency: a.s. block frequencies → P_st (LF5 vnDilation_pointer_frequency
-- @ N=4 + nudgedSinglet_born). Flow LOCAL (LF5 @ N=4); carve CONTEXTUAL (A.1). Flow
-- factorisation Φ = Φ_A ⊗ Φ_B deferred to LF6-A.3. Residue SO-1 (entangled sector posited);
-- generic context (P_st > 0, every Bell setting). Foundational triple only, no busch.
/-- info: 'CSD.LF6.singletDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_pointer_volume

/-- info: 'CSD.LF6.singletDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_frequency

/-- info: 'CSD.LF6.singletDeisolation_blockVolume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_blockVolume_correlation

/-- info: 'CSD.LF6.singletDeisolation_carve_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_carve_contextual

/-- info: 'CSD.LF6.singletDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_flow_capstone

-- LF6-A.2 contextuality juxtaposition CLOSED: singletDeisolation_carve_not_product composes
-- the EXHIBITED carve's achieved block-volume correlation (carveBlockCorrelation, the s·t-weighted
-- sum of bornRegion FS volumes, discharged to −a·b via singletDeisolation_blockVolume_correlation)
-- with A.1 no_product_partition_realises_singlet in ONE theorem (no free −a·b; the carve's own
-- value is fed in). Foundational-triple-only.
/-- info: 'CSD.LF6.singletDeisolation_carve_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_carve_not_product

-- LF6-A.3 (2026-06-28): the LOCAL product de-isolation flow V_A ⊗ V_B realising the singlet.
-- The de-isolation can be local (factorises); the non-locality is entirely in the contextual
-- carve (A.2) and the entangled preparation (SO-1). Foundational triple only, no busch.
/-- info: 'CSD.LF6.localDeisolation_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_factorises

/-- info: 'CSD.LF6.localDeisolation_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_pullback

/-- info: 'CSD.LF6.localDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_pointer_volume

/-- info: 'CSD.LF6.localDeisolation_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_capstone

-- C1 support (2026-08-10, Phase 0 of the C1 correction): the flow-level
-- measure preservation was the one C1 support theorem with no pin. The other nine
-- listed in the C1 work order were already pinned in their namespace-matched parts
-- (EmpiricalQM, Dynamics, LF4), per the G9 rule, so no duplicate C1 part is created.
/-- info: 'CSD.LF6.localDeisolationFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolationFlow_measurePreserving

-- LF6-A.3 flow ↔ dilation tie (2026-06-28): the LOCAL flow realises the local Naimark
-- dilation, Φ_loc [ψ ⊗ (a₀⊗a₀)] = [V_loc ψ] for every nonzero ψ (matches LF5's
-- measurementFlow_realises_dilation). Closes the auditor Minor: the capstone now ties
-- the bundled flow and dilation. Foundational triple only, no busch.
/-- info: 'CSD.LF6.localDeisolationFlow_realises_localNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolationFlow_realises_localNaimark

-- LF6-C.4 (GHZLocalFlow, 2026-07-02): the manifestly LOCAL product de-isolation flow
-- V_loc = V_0 ⊗ V_1 ⊗ V_2 (three genuine N=2 wings) realising the three-qubit GHZ
-- measurement, the three-party analogue of A.3. ghzLocal_pullback GENUINELY composes the
-- three wing LF5 vnDilationV_pullback (via conjTranspose/mul_kronecker_mul + A.3's 2-wing
-- localDeisolation_pullback for the inner factor); the pointer-block FS volume = ghzWeight
-- (povm_born_eq_dilated_volume_uncond ∘ nudgedGHZ_born); the projectivised product flow
-- U_0 ⊗ U_1 ⊗ U_2 is FS-measure-preserving and ≠ id; the flow realises the local dilation.
-- The de-isolation CAN be local (three-party product, no non-local interaction); the GHZ
-- non-locality lives in the contextual carve (C.1/C.3) and the entangled preparation (SO-1).
-- Born = FS-volume imported, not re-derived. Foundational triple only, no busch.
/-- info: 'CSD.LF6.ghzLocal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_factorises

/-- info: 'CSD.LF6.ghzLocal_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_pullback

/-- info: 'CSD.LF6.ghzLocal_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_pointer_volume

/-- info: 'CSD.LF6.ghzLocalFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_measurePreserving

/-- info: 'CSD.LF6.ghzLocalFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_ne_id

/-- info: 'CSD.LF6.ghzLocalFlow_realises_localNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_realises_localNaimark

/-- info: 'CSD.LF6.ghzLocal_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_capstone

-- LF6-B.1 (Decoherence, 2026-06-28): decoherence as coarse-graining over a CONSERVATIVE
-- de-isolation flow — the first result on the open-system / partial-trace stratum of D1.
-- decohereReduced ψ = partialTraceRight (V |ψ⟩⟨ψ| Vᴴ) GENUINELY COMPUTES to the
-- Born-weighted diagonal mixture ∑ⱼ ‖⟨eⱼ,ψ⟩‖² • |eⱼ⟩⟨eⱼ| (dephases); off-diagonal
-- coherences are explicit zeros; diagonal weights are the Born weights, TIED to the
-- LF5/LF6 pointer-block FS typicality volumes (decoherence_diagonal_eq_pointer_volume,
-- vnDilation_pointer_volume); the de-isolation V is an isometry (conservative on the
-- joint, dissipative only on the marginal). Foundational triple only, no busch (the
-- partial-trace + dilation machinery is measure-theoretic / linear-algebraic, off the
-- ontic Born path). DEFERRED: continuous-time Lindblad / T1-T2; system-marginal
-- FS-volume-drift geometry; purity/entropy. Residue SO-1 (FS-typicality posited).
/-- info: 'CSD.LF6.decoherence_dephases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_dephases

/-- info: 'CSD.LF6.decoherence_offdiagonal_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_offdiagonal_vanish

/-- info: 'CSD.LF6.decoherence_diagonal_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_diagonal_born

/-- info: 'CSD.LF6.decoherence_diagonal_eq_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_diagonal_eq_pointer_volume

/-- info: 'CSD.LF6.deisolation_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.deisolation_conservative

/-- info: 'CSD.LF6.decoherence_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_capstone

-- LF6-B.2 (Decoherence, 2026-06-29): the QUANTITATIVE purity-drop / irreversibility witness.
-- The reduced state is a genuine density operator (decohereReduced_trace, Tr = ‖ψ‖², via
-- partialTraceRight_trace + deisolation_conservative Vᴴ V = 1); its purity Tr(ρ_red²) =
-- ∑ⱼ (‖⟨eⱼ,ψ⟩‖²)² (decohere_purity_eq, the reduced state being diagonal); purity ≤ 1
-- (decohere_purity_le_one, linear entropy ≥ 0); and STRICTLY < 1 for a measurement-basis
-- superposition with ≥2 nonzero Born weights (decohere_purity_lt_one_of_superposition) —
-- the pure input |ψ⟩⟨ψ| (purity 1) decoheres to a strictly mixed state. The irreversibility
-- narrated in B.1 is now theorem-backed (linear-entropy witness 1 − Tr(ρ²) > 0). The
-- superposition hypothesis is load-bearing (single eigenstate ⟹ purity stays 1). Foundational
-- triple only, no busch. DEFERRED: von Neumann entropy increase; continuous-time Lindblad /
-- environment growth. Residue SO-1 (FS-typicality posited).
/-- info: 'CSD.LF6.decohereReduced_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohereReduced_trace

/-- info: 'CSD.LF6.decohere_purity_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_eq

/-- info: 'CSD.LF6.decohere_purity_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_le_one

/-- info: 'CSD.LF6.decohere_purity_lt_one_of_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_lt_one_of_superposition

/-- info: 'CSD.LF6.decoherence_irreversibility_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_irreversibility_capstone

-- LF6-B.3 (Decoherence, 2026-07-01): the von Neumann (Shannon-of-the-Born-vector) entropy-increase
-- witness. The decohered reduced state is diagonal with the Born vector pⱼ = ‖⟨eⱼ,ψ⟩‖² on the
-- diagonal, so its von Neumann entropy is GENUINELY DERIVED (decohereReduced_eq_diagonal ∘
-- QuantumInfo.vonNeumannEntropy_diagonal) to be the Shannon entropy ∑ⱼ negMulLog(pⱼ) = −∑ pⱼ log pⱼ
-- (decohere_vonNeumann_entropy_eq); non-negative (decohere_vonNeumann_entropy_nonneg); and STRICTLY
-- positive for a measurement-basis superposition with ≥2 nonzero Born weights
-- (decohere_vonNeumann_entropy_pos_of_superposition). The pure input |ψ⟩⟨ψ| has S = 0
-- (vonNeumannEntropy_eq_zero_of_pure); the conservative de-isolation + pointer trace jumps it to
-- S > 0 — the entropy-increase irreversibility witness (0 → S > 0), completing B.1/B.2's
-- linear-entropy / purity account. The superposition hypothesis is load-bearing (single eigenstate
-- ⟹ S = 0, one pⱼ = 1 rest 0, negMulLog(1) = negMulLog(0) = 0). Foundational triple only, no busch.
-- DEFERRED: continuous-time Lindblad / environment growth. Residue SO-1 (FS-typicality posited).
/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_eq

/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_nonneg

/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_pos_of_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_pos_of_superposition

/-- info: 'CSD.LF6.decoherence_vonNeumann_irreversibility_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_vonNeumann_irreversibility_capstone

-- LF6-D (MaxEntangledDeisolationFlow, 2026-07-03): the first genuinely DIMENSION-GENERAL entangled
-- de-isolation instance. Before this the tier had only two hand-built instances (2x2 singlet A-tier,
-- 3-qubit GHZ C-tier); this makes "general-N" actually general — the d x d maximally-entangled state
-- Ψ_d = (1/√d)∑ᵢ|i⟩|i⟩, every d ≥ 2. maxEntangled d + medWeight (Born = 1/d on the diagonal, 0 off);
-- maxEntangled_normSq_eq_weight / sum_medWeight (unit-norm) / maxEntangled_marginal_uniform (the DIAGONAL
-- Born-weight marginal is uniform 1/d — not the full ρ_A = I/d). The de-isolation flow + Born-from-volume
-- REUSES the LF5 general-N engine at N = d·d: maxEntangledDeisolation_pointer_volume (the headline)
-- COMPOSES LF5 vnDilation_pointer_volume @ N=d·d (pointer-block FS volume = ‖⟨eᵢ,φ⟩‖², Gleason-free,
-- Born=volume IMPORTED from the DH/FS-volume engine) with the reindex coordinate-Born identity
-- nudgedMaxEntangled_born; maxEntangledDeisolation_frequency (a.s. block frequencies → medWeight);
-- ne_id (Φ≠id, 1<d·d) + measurePreserving. This is the LOAD-BEARING content: the LF6 de-isolation
-- dynamics + Born-from-volume is now genuinely DIMENSION-GENERAL, not tied to 2x2/GHZ. Forced
-- non-factorisation (no_product_partition_realises_maxEntangled, 2026-07-03 rewrite): DERIVED and
-- maxEntangled-specific, no longer a verbatim singlet re-export. (b) maxEntangledSector_eq_phiPlus:
-- Ψ_d's {0,1}² Schmidt sector IS the Bell Φ⁺ state up to √2/√d (FULL state, coherences included,
-- d-dependent). phiPlus_pauli_correlation: ⟨Φ⁺|σ·a⊗σ·b|Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z, COMPUTED
-- from the Hilbert space (mirrors LF3.expectation_formula on Φ⁺'s (0,0)/(1,1) support). (c)
-- no_product_partition_realises_phiPlus: no product partition reproduces Φ⁺'s OWN correlation — the
-- orthogonal xz-reflection reflectXZ of Bob's axis carries E_{Φ⁺} to the singlet's −a·b
-- (phiPlusCorrelation_reflectXZ), so Φ⁺ reaches the same 2√2 > 2 (LHV cap |S|≤2, lhvCHSH_abs_le_two),
-- reducing to no_product_partition_realises_singlet on the relabeled partition. So the CHSH violation is
-- DERIVED for Φ⁺ (not the singlet's imported by prose). Scope: forced by the CHSH-violating 2x2 Φ⁺
-- sector; a full general-d CGLMP result is NOT claimed. Born IMPORTED not derived (DH engine); flow
-- realises not derives. Residue SO-1 (entangled sector posited). Foundational triple only, no busch, no
-- native_decide.
/-- info: 'CSD.LF6.maxEntangledDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_pointer_volume

/-- info: 'CSD.LF6.maxEntangledDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_frequency

/-- info: 'CSD.LF6.maxEntangledDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_ne_id

/-- info: 'CSD.LF6.maxEntangledDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_measurePreserving

/-- info: 'CSD.LF6.maxEntangled_sector_marginal_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangled_sector_marginal_uniform

/-- info: 'CSD.LF6.maxEntangledSector_eq_phiPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledSector_eq_phiPlus

/-- info: 'CSD.LF6.phiPlus_pauli_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_pauli_correlation

/-- info: 'CSD.LF6.no_product_partition_realises_phiPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_phiPlus

-- LF6-7 (2026-07-12): the Φ⁺↔ψ⁻ transport recompute. reflectXZ (Bob's xz-axis flip) lifted to the
-- Hilbert-space level: phiPlus_pauli_correlation_reflectXZ recomputes the singlet's −a·b from Φ⁺'s OWN
-- derived expectation; phiPlus_transport_eq_singlet_expectation proves this equals LF3's independently
-- derived ⟨ψ⁻|σ·a⊗σ·b|ψ⁻⟩ — the two independent Bell derivations are one under reflectXZ (consolidation).
/-- info: 'CSD.LF6.phiPlus_pauli_correlation_reflectXZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_pauli_correlation_reflectXZ

/-- info: 'CSD.LF6.phiPlus_transport_eq_singlet_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_transport_eq_singlet_expectation

-- LF6-6 partial (2026-07-12): the partial-Schmidt (non-maximally-entangled) two-qubit correlation,
-- extending the LF6 correlation beyond equal Schmidt coefficients. Ψ(c,s)=c|00⟩+s|11⟩ gives
-- ⟨σ·a⊗σ·b⟩ = a_z b_z + 2cs(a_x b_x − a_y b_y) (psQubit_pauli_correlation), 2cs = concurrence; at
-- c=s=1/√2 it collapses to Φ⁺ (psQubit_pauli_correlation_maximal).
/-- info: 'CSD.LF6.psQubit_pauli_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation

/-- info: 'CSD.LF6.psQubit_pauli_correlation_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation_maximal

-- LF6-6 residual DISCHARGED — Gisin's theorem (GisinTheorem.lean, 2026-07-19): the non-factorisation
-- witness for unequal Schmidt coefficients. Every pure entangled two-qubit state Ψ(c,s) (0<c,0<s,
-- c²+s²=1) violates CHSH: gisin_chsh_violation gives settings whose CHSH combination of the genuine
-- Hilbert-space expectations ⟨Ψ(c,s)|σ·a⊗σ·b|Ψ(c,s)⟩ exceeds 2. gisin_chsh_value: the closed form is
-- 2√(1+(2cs)²) (Horodecki optimum for T=diag(2cs,−2cs,1)); >2 since concurrence 2cs>0; =2√2 at c=s=1/√2.
/-- info: 'CSD.LF6.gisin_chsh_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.gisin_chsh_value

/-- info: 'CSD.LF6.gisin_chsh_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.gisin_chsh_violation

-- LF6-2 bounded core (2026-07-12): the qubit T2 dephasing quantum dynamical semigroup — the
-- continuous-time open-system de-isolation frontier. Φ_t(ρ) damps coherences by e^{-γt}, preserves
-- populations; dephasingChannel_semigroup (Φ_s∘Φ_t = Φ_{s+t}, the Markovian composition law) and
-- dephasingChannel_coherence_tendsto_zero (coherence → 0 as t→∞, γ>0: continuous-time einselection to
-- the pointer basis). Residual: the general Lindblad generator + complete positivity + T1 damping.
/-- info: 'CSD.LF6.dephasingChannel_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_semigroup

/-- info: 'CSD.LF6.dephasingChannel_coherence_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_coherence_tendsto_zero

-- LF6-2 T1 amplitude damping (2026-07-14): the population-transferring companion of T2 dephasing.
-- dampingChannel Φ_t(ρ) = [[ρ₀₀+(1-e)ρ₁₁, √e·ρ₀₁],[√e·ρ₁₀, e·ρ₁₁]] (e = e^{-γt}). dampingChannel_
-- semigroup (Φ_s∘Φ_t = Φ_{s+t}), dampingChannel_trace (channel), dampingChannel_ground_population (the
-- T1 signature: population flows 1→0), dampingChannel_excited_tendsto_zero + _coherence_tendsto_zero
-- (relaxation to the ground state as t→∞, γ>0). Foundational triple.
/-- info: 'CSD.LF6.dampingChannel_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_semigroup

/-- info: 'CSD.LF6.dampingChannel_ground_population' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_ground_population

/-- info: 'CSD.LF6.dampingChannel_excited_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_excited_tendsto_zero

-- LF6-9 generator tier (LindbladGenerator.lean, 2026-07-20): the general Lindblad/GKSL generator
-- ℒ(ρ)=−i[H,ρ]+Σₖ(LₖρLₖ†−½{Lₖ†Lₖ,ρ}), previously undefined. lindbladGenerator_trace (trace annihilation
-- tr ℒ=0 ⟹ trace-preserving), lindbladGenerator_isHermitian (Hermiticity preservation), and
-- lindblad_dissipation_posSemidef (the jump part ΣₖLₖρLₖ† preserves PSD — the Choi/Kraus CP witness). The
-- dephasing instance: dephasingGenerator_eq_lindblad ((γ/2)(σzρσz−ρ) is GKSL with H=0, L=√(γ/2)σz) and
-- dephasingChannel_master_equation (the exhibited T2 channel solves d/dt Φ = ℒ_deph(Φ) — the Φ_t=e^{tℒ}
-- content). Foundational triple. Deferred: CP of e^{tℒ} for arbitrary generators (matrix-exp positivity).
/-- info: 'CSD.LF6.lindbladGenerator_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladGenerator_trace

/-- info: 'CSD.LF6.lindbladGenerator_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladGenerator_isHermitian

/-- info: 'CSD.LF6.lindblad_dissipation_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindblad_dissipation_posSemidef

/-- info: 'CSD.LF6.dephasingGenerator_eq_lindblad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingGenerator_eq_lindblad

/-- info: 'CSD.LF6.dephasingChannel_master_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_master_equation

-- Lindblad semigroup tier (LindbladSemigroup.lean, Q5/LF6-9, 2026-08-13):
-- Phi_t = exp(t.L) for an ARBITRARY GKSL generator -- semigroup law, the
-- master equation, trace preservation, and Hermiticity preservation at the
-- flow level. CP of exp(t.L) remains the recorded Mathlib-scale gap.
/-- info: 'CSD.LF6.lindbladSemigroup_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladSemigroup_add

/-- info: 'CSD.LF6.lindbladSemigroup_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladSemigroup_hasDerivAt

/-- info: 'CSD.LF6.lindbladSemigroup_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladSemigroup_trace

/-- info: 'CSD.LF6.lindbladGenerator_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladGenerator_conjTranspose

/-- info: 'CSD.LF6.lindbladSemigroup_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladSemigroup_conjTranspose

/-- info: 'CSD.LF6.lindbladSemigroup_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladSemigroup_isHermitian

/-- info: 'CSD.LF6.no_product_partition_realises_maxEntangled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_maxEntangled

/-- info: 'CSD.LF6.maxEntangledDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_flow_capstone

-- LF6-D QM side (CGLMPQutrit, 2026-07-03): the genuinely d=3-INTRINSIC CGLMP violation for the
-- maximally-entangled qutrit Ψ_3, the QM payoff of the CGLMP infrastructure. pQM x y c = P(A_x−B_y=c)
-- is the GENUINE outcome-difference Born table: bornPair x y k l = ‖⟨outcome_{k,l}, maxEntangled 3⟩‖²
-- (squared inner product with Ψ_3), the outcome vectors the CGLMP phase-basis measurement vectors
-- (aVec_unit/bVec_unit unit vectors), pQM the k−l marginal (bornPair_periodic: Born depends only on
-- k−l). bornPair_value computes it via the roots-of-unity geometric sum ‖1+w+w²‖²=3+4cosφ+2cos2φ
-- (normSq_geom) + the diagonal Ψ_3 contraction (inner_outcome_collapse). Under offsets α₁=0,α₂=1/2,
-- β₁=−1/4,β₂=1/4 the four CGLMP-positive entries are (4+2√3)/9, the four negative 1/9, giving the
-- EXACT value cglmp_maxEntangled_qutrit_eq: cglmp 3 pQM = (12+8√3)/9 ≈ 2.8729. cglmp_maxEntangled_qutrit_gt_two:
-- > 2 (the √3 irrational; no rational/half-integer setting violates — those give exactly 2). The
-- d-intrinsic no-go no_lhv_realises_maxEntangled_cglmp: any LHV reproducing pQM would give
-- cglmpLHV = cglmp 3 pQM > 2, contradicting cglmp_lhv_bound_three (I_3 ≤ 2). SUPERSEDES the 2×2 Φ⁺
-- CHSH sector routing of no_product_partition_realises_maxEntangled for d=3 (that theorem is untouched;
-- this is additive). Scope: d=3 only; general-d (d≥4) CGLMP is the residual. Foundational triple only,
-- no busch, no native_decide (decide for finite ZMod facts only).
/-- info: 'CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_eq

/-- info: 'CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two

/-- info: 'CSD.LF6.CGLMPQutrit.no_lhv_realises_maxEntangled_cglmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.no_lhv_realises_maxEntangled_cglmp

-- LF6-D QM side GENERAL-d (CGLMPQudit, 2026-07-04): the CGLMP violation for the maximally-entangled
-- qudit Ψ_d = maxEntangled d extended to EVERY d ≥ 2, closing the statistical non-locality axis at
-- full dimensional generality (the d=3 qutrit result above is untouched; this is additive). The Born
-- table is GENUINE: bornPair x y k l = ‖⟨outcome_{k,l}, maxEntangled d⟩‖² (squared inner product with
-- Ψ_d), and pQM_closed derives the standard maximally-entangled closed form
-- pQM x y c = 1/(2 d² sin²(π(c.val+δ)/d)) via the d-th-roots-of-unity Dirichlet/Fejér kernel
-- (dirichlet_kernel: ‖∑_{j<d} e^{ijφ}‖² = sin²(dφ/2)/sin²(φ/2), the general-d analogue of the qutrit
-- normSq_geom), the quarter-integer numerator sin²(π(m+δ))=1/2, and the diagonal Ψ_d contraction. The
-- cglmp value is the closed-form sum cglmp_maxEntangled_qudit_closed = ∑_{k<⌊d/2⌋}(1−2k/(d−1))·
-- (2/d²)(csc²(π(k+1/4)/d)−csc²(π(k+3/4)/d)). cglmp_maxEntangled_qudit_gt_two (hd:2≤d): cglmp d pQM > 2
-- is a REAL analytic inequality for ALL d ≥ 2 (NOT decide over finite d, NOT axiomatised): every
-- bracket term is nonneg (sin-monotonicity) and every coefficient nonneg, so the sum dominates its k=0
-- term, and that term alone is ≥ 32/π²−8/9 > 2 uniformly in d (sin x ≤ x on the π/(4d) arm, Jordan's
-- sin x ≥ 2x/π on the 3π/(4d) arm, π < 3.15). The general-d Bell force
-- no_lhv_realises_maxEntangled_cglmp_d: any LHV reproducing pQM gives cglmpLHV = cglmp d pQM > 2,
-- contradicting cglmp_lhv_bound (I_d ≤ 2, all d). Foundational triple only, no busch, no native_decide.
/-- info: 'CSD.LF6.CGLMPQudit.pQM_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.pQM_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmpBracket_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmpBracket_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_gt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_gt_two

/-- info: 'CSD.LF6.CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d

-- LF6-1 (2026-07-09): the flow capstone with conjunct 7 REROUTED through the d-intrinsic CGLMP force
-- (no LHV table reproduces pQM d, since cglmp d pQM > 2 in dimension d) instead of the 2×2 Φ⁺/CHSH
-- sector. Conjuncts 1–6 inherited from maxEntangledDeisolation_flow_capstone; still foundational-triple.
/-- info: 'CSD.LF6.maxEntangledDeisolation_flow_capstone_cglmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_flow_capstone_cglmp

-- GHZ_n tranche (GHZnDeisolationFlow, 2026-07-03): the DETERMINISTIC (Mermin) all-or-nothing forcing
-- axis at general PARTY number n, complementing the statistical (CGLMP) axis at general dimension d
-- (MaxEntangledDeisolationFlow + Mathlib/Probability/CGLMP). ghzN n = (|0..0⟩+|1..1⟩)/√2 on Fin (2^n)
-- (support 0 / topIdx n = 2^n−1); ghzNWeight (Born = 1/2 on the two all-equal outcomes, 0 else),
-- ghzN_normSq_eq_weight / sum_ghzNWeight (unit-norm, n≥1) / ghzN_born. The de-isolation flow +
-- Born-from-volume at N = 2^n (the clean general-PARTY core) REUSES the LF5 general-N engine:
-- ghzNDeisolation_pointer_volume COMPOSES LF5 vnDilation_pointer_volume @ N=2^n (pointer-block FS
-- volume = ‖⟨eᵢ,φ⟩‖², Gleason-free, Born=volume IMPORTED from the DH/FS-volume engine) with ghzN_born;
-- ghzNDeisolation_frequency (a.s. block freq → GHZ_n Born); ne_id (Φ≠id, 1<2^n) + measurePreserving.
-- The n-party DETERMINISTIC (Mermin) forcing (the load-bearing thesis part): no_lhvN_assignment_for_ghzN
-- (general n, combinatorial) + no_product_partition_realises_ghzN (general n, measure-theoretic —
-- generalises C.1's no_product_partition_realises_ghz via pm_ae_eq → l₀ → no_lhvN). Mechanism: the
-- three-party Mermin dance on parties {0,1,2}, spectators ≥3 measure X; the full-n product PARITY
-- contradiction (each party's ±1 appears squared → 4 correlations multiply to +1 while product of QM
-- values is −1) is a GENUINE n-party statement (product over Fin n, n-party contexts), NOT a hollow
-- re-export. no_lhv_assignment_for_ghz4 is the essentially-FOUR-party witness (all parties participate,
-- no spectator; via decide-free parity). Honest caveat: general-n forcing routes the contradiction
-- through the 3-party paradox embedded via X-spectators (does not exhibit essential n-party
-- entanglement beyond 3); physical regime n≥3 (targets = GHZ_n's Mermin correlations). Residual: the
-- uniform essentially-all-n-parties construction (n mod 4). Born IMPORTED not derived (DH engine);
-- flow realises not derives. Residue SO-1.
-- Foundational triple only, no busch, no native_decide (decide not used on headlines; ghz4 via ring/norm_num).
-- GHZ_n QM-link (deliverable 5, 2026-07-03): CLOSES the general-n QM-confirmation residual. The four ±1
-- targets of ReproducesGHZN / no_lhvN_assignment_for_ghzN are DERIVED to be GHZ_n's OWN tensor-Pauli
-- Mermin correlations ⟨GHZ_n|σ_{a_1}⊗…⊗σ_{a_n}|GHZ_n⟩ for every n≥3, NO LONGER n=3-anchored to
-- Empirical.GHZ. ghzN_expectation_corner: the genuine two-corner Hilbert reducer on Fin (2^n) (GHZ_n
-- supported on {0, topIdx n}, half-sum of four corner entries, ((√2)⁻¹)²=1/2 via the smul/single
-- expansion + toELin_single_coord). tensorPauliFin: the n-fold tensor Pauli via the product-of-factor-
-- entries Kronecker formula on the bit-decomposition basis (finFunctionFinEquiv). ghzN_mermin_correlations:
-- ⟨XXX…⟩=+1, ⟨XYY…⟩=⟨YXY…⟩=⟨YYX…⟩=−1 (spectator X-factors → +1 via prod_ghzNCtx; twisted 2-Y → cos π=−1
-- via Complex.I_mul_I). reproducesGHZN_QM_iff: ReproducesGHZN_QM ↔ ReproducesGHZN (the ±1 targets ARE the
-- .re QM correlations). no_product_partition_realises_ghzN_qm: the LF6-E forcing ROUTED through GHZ_n's
-- actual QM correlations, so general-n non-locality is genuinely GHZ_n-specific. Genuine derived Hilbert
-- computation, not asserted; foundational triple only, no busch, no native_decide (decide only on the finite
-- PauliAxis inequality PauliAxis.x ≠ PauliAxis.y). Residual sub-point: fully-general arbitrary-Pauli-tensor
-- reducer (Z factors, arbitrary axis patterns) not delivered; only the X/Y Mermin family the forcing needs.
/-- info: 'CSD.LF6.ghzN_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_norm

/-- info: 'CSD.LF6.sum_ghzNWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.sum_ghzNWeight

/-- info: 'CSD.LF6.ghzN_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_born

/-- info: 'CSD.LF6.ghzNDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_ne_id

/-- info: 'CSD.LF6.ghzNDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_measurePreserving

/-- info: 'CSD.LF6.ghzNDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_pointer_volume

/-- info: 'CSD.LF6.ghzNDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_frequency

/-- info: 'CSD.LF6.no_lhvN_assignment_for_ghzN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_lhvN_assignment_for_ghzN

/-- info: 'CSD.LF6.no_product_partition_realises_ghzN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghzN

/-- info: 'CSD.LF6.no_lhv_assignment_for_ghz4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_lhv_assignment_for_ghz4

/-- info: 'CSD.LF6.ghzNDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_flow_capstone

/-- info: 'CSD.LF6.ghzN_expectation_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_expectation_corner

/-- info: 'CSD.LF6.ghzN_mermin_correlations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_mermin_correlations

/-- info: 'CSD.LF6.reproducesGHZN_QM_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.reproducesGHZN_QM_iff

/-- info: 'CSD.LF6.no_product_partition_realises_ghzN_qm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghzN_qm

-- LF6-3/LF6-4 Bloch-volume contraction (2026-08-09, LF6/BlochContraction.lean). The
-- geometric open-vs-closed signature on the two proved dissipators: dephasing acts as
-- diag(e,e,1) and damping as diag(sqrt(e),sqrt(e),e) + trace-weighted pole offset on the
-- Bloch vector (blochVec_dephasing/_damping) -- and BOTH determinants equal e^{-2 gamma t}:
-- the marginal volume drift is a dissipation invariant, blind to how the contraction is
-- distributed over axes. Metrology A4: gamma*t = 0 gives factor 1 (closed = drift-free),
-- gamma*t > 0 strictly contracts (openness detected), the initial drift rate is exactly
-- -2 gamma, and one drift sample at any t > 0 identifies gamma. HONEST SCOPE: the two
-- exhibited dissipators; the general-generator form waits on LF6-9's exponential-CP
-- residual (Mathlib-scale).
/-- info: 'CSD.LF6.det_blochLinearDephasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.det_blochLinearDephasing

/-- info: 'CSD.LF6.det_blochLinearDamping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.det_blochLinearDamping

/-- info: 'CSD.LF6.bloch_volume_decay_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.bloch_volume_decay_rate

/-- info: 'CSD.LF6.volume_drift_determines_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.volume_drift_determines_rate

-- The LOCAL nudge (2026-08-10, LF6/NudgeLocality.lean). `nudgedSinglet` is the vector of
-- sqrt(P_st) -- all phases stripped -- so it is NOT a local-unitary image of the singlet
-- (at a perp b it is a PRODUCT state while the singlet is maximally entangled). `localNudge`
-- is the object `nudgedSinglet` was DESCRIBED as: defined as the action of the product
-- unitary (wingBasisUnitary a) (x) (wingBasisUnitary b) on the singlet, so locality is
-- definitional. `localNudge_born` shows it reproduces the same Born statistics, and carries
-- NO genericity hypothesis (no hgen).
--
-- Added 2026-08-11 (external review, recommended hardening): the modules called wingPairUnitary
-- a "product unitary" in prose while only its FACTORS carried an exported unitarity theorem
-- (LF3.wingBasisUnitary_mem_unitaryGroup), leaving the word "unitary" as an inference sitting in
-- documentation. Mathematically immediate from Matrix.kronecker_mem_unitary, but the repository is
-- eliminating prose-only property claims, so it is now machine-checked and pinned.
/-- info: 'CSD.LF6.wingPairUnitary_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.wingPairUnitary_mem_unitary

/-- info: 'CSD.LF6.wingPairUnitary_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.wingPairUnitary_mem_unitaryGroup

/-- info: 'CSD.LF6.localNudge_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localNudge_coord

/-- info: 'CSD.LF6.localNudge_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localNudge_born

-- The re-route, and with it the endpoint case. localDeisolation_pointer_volume carries
-- hgen (so it EXCLUDES a.b = +-1, perfect anticorrelation); the local version does not.
-- The genericity restriction was never intrinsic to the volume machinery --
-- povm_born_eq_dilated_volume_uncond is already hpos-free -- it entered only through
-- singletJointEig's division by sqrt(P_st). Work-order item 12 closes as a side effect.
/-- info: 'CSD.LF6.localNudgeVec_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localNudgeVec_born

/-- info: 'CSD.LF6.localNudgeVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localNudgeVec_norm

/-- info: 'CSD.LF6.localDeisolation_pointer_volume_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_pointer_volume_local

-- Work-order item 8: the whole setting-dependent chain is a product of wing-local maps,
-- (V_A (x) V_B)(U_A(a) (x) U_B(b))^H = (V_A U_A(a)^H) (x) (V_B U_B(b)^H). Available only
-- because localNudge replaced nudgedSinglet: the old object is not a product-unitary image
-- of the singlet at all, so no such factorisation existed for it. DYNAMICAL locality of the
-- chain, NOT Bell factorisation of outcomes (impossible, no_product_partition_realises_singlet).
-- Scope: the finite dilated construction, not arbitrary ontic Sigma.
/-- info: 'CSD.LF6.localMeasurementChain_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localMeasurementChain_factorises

-- The C1 four-answer obstruction (2026-08-10, LF6/C1BellConsistency.lean). LF3/ContextMap
-- used to claim that ContextIndexedOutcomeMaps and GlobalCHSHAssignment being DIFFERENT
-- TYPES carries the Bell-consistency content. That is false -- different structures give
-- only definitional separation. This is the actual obstruction, on the ONE shared state
-- space C1 posits: no measurable shared-context outcome family compatible with any global
-- CHSH assignment reproduces the singlet at the four CHSH settings. Measurability is assumed
-- only of the posited object S; the four setting-local responses are DERIVED from it plus
-- compatibility. The non-vacuity companion makes it a separation rather than an artefact,
-- mirroring productPartition_nonvacuous.
/-- info: 'CSD.LF6.no_compatible_global_chsh_assignment_realises_singlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_compatible_global_chsh_assignment_realises_singlet

-- Q19 (2026-08-13): the POSITIVE half of the C1 separation. Until Q19 the obstruction
-- above was conditional in its reproduction slot -- nothing inhabited
-- ReproducesSingletAtCHSH, and the recorded non-vacuity covered only the compatibility
-- conjunct (the all-plus family, constant correlation 1). The explicit contextual model
-- closes it: for each context the first torus coordinate of (KSigma 4, kMuPsi) is read
-- through the four cumulative arcs (RecordLayer.circleCell) whose lengths are the
-- context's own singlet weights, so every joint outcome carries EXACTLY P_st -- the FULL
-- TABLE, at every context, not only the four CHSH ones (a correlation-only witness could
-- cheat with degenerate marginals; the table cannot -- the E-1 lesson applied in
-- advance). integral_wing_mul_of_table converts the table into the correlation form
-- (correlation IS the weighted table sum by definition), and the capstone conjoins
-- existence with the obstruction: contextual families carry the singlet, no globally
-- CHSH-compatible family can. Scope unchanged: the incompatibility half constrains only
-- the four CHSH settings; does not subsume no_product_partition_realises_singlet.
/-- info: 'CSD.LF6.integral_wing_mul_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.integral_wing_mul_of_table

/-- info: 'CSD.LF6.kMuPsi_singletCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.kMuPsi_singletCell

/-- info: 'CSD.LF6.singletContextualModel_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletContextualModel_table

/-- info: 'CSD.LF6.singletContextualModel_reproduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletContextualModel_reproduces

/-- info: 'CSD.LF6.c1_singlet_contextual_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.c1_singlet_contextual_capstone

-- Q20: the operational no-signalling predicate, inhabited by the same model. Until now
-- `LF3.OperationalNoSignalling` had no inhabitant anywhere; C1 §4 cites it while the only
-- available theorems were finite sums over the closed-form kernel.
/-- info: 'CSD.LF6.singletContextualModel_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletContextualModel_no_signalling

-- Q20: the every-setting no-go, discharged against the exhibited model.
/-- info: 'CSD.LF6.singletContextualModel_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletContextualModel_not_product

/-- info: 'CSD.LF6.compatibleGlobalCHSH_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.compatibleGlobalCHSH_nonvacuous

-- Item 15: operational no-signalling of the EXPLICIT construction. Equalities of marginal
-- VOLUMES, never of the underlying outcome partitions -- the microscopic regions differ
-- between contexts (the two sides are built from different prepared states); only their
-- measures agree. Under measurement independence, per LF3/OperationalNoSignalling.
/-- info: 'CSD.LF6.localDeisolation_A_marginal_volume_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_A_marginal_volume_eq_half

/-- info: 'CSD.LF6.localDeisolation_B_marginal_volume_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_B_marginal_volume_eq_half

/-- info: 'CSD.LF6.localDeisolation_no_signalling_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_no_signalling_A

/-- info: 'CSD.LF6.localDeisolation_no_signalling_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_no_signalling_B

end CSD.Tests.AxiomAudit
