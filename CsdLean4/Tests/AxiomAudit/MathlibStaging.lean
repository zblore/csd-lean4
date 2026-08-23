/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: MathlibStaging

**Category:** Special (axiom-posture regression pins; G9 split part).

Cat-1 Mathlib-staged pins (Projectivization/Wigner, UnitaryGroup/FS measure, QuantumInfo incl. Reversible arithmetic, probability/measure support).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.MathlibStaging`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- Partial trace (Cat-1 Mathlib staging) + the reduced density operator (LF2).
-- traceRight/traceLeft trace out a tensor factor; the API (kronecker defining
-- property, trace-preservation, Hermitian/PSD preservation) sends a density
-- operator to its reduced density operator. Foundational triple. Unblocks E3b/E2.
-- (2026-07-20 Mathlib v4.33 upgrade: traceRight_kronecker gained Classical.choice — a
-- transitively-used Mathlib lemma became classical upstream; still the foundational triple.)
/-- info: 'Matrix.traceRight_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.traceRight_kronecker

/-- info: 'Matrix.trace_traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.trace_traceRight

/-- info: 'Matrix.PosSemidef.traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.PosSemidef.traceRight

-- Quantum channels in Kraus form (Cat-1 Mathlib staging; phase C1 of
-- specs/channels-plan.md). The action is trace-preserving (apply_trace),
-- PSD-preserving (apply_posSemidef), and Hermiticity-preserving — so a channel
-- sends density operators to density operators. Foundational triple. On-ramp to Φ≠id.
/-- info: 'QuantumInfo.Channel.apply_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_trace

/-- info: 'QuantumInfo.Channel.apply_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_posSemidef

/-- info: 'QuantumInfo.Channel.apply_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_isHermitian

-- Stinespring dilation (Cat-1 staging; phase C2 of specs/channels-plan.md). The
-- Kraus ↔ Stinespring bridge: every channel's stacked-Kraus matrix is an isometry
-- (stinespringIsom_isom) whose dilate-then-trace action is the Kraus action
-- (apply_eq_traceRight_stinespring), and conversely the env-blocks of an isometry
-- form a channel (ofIsometry_apply). The on-ramp to Φ≠id. Foundational triple.
/-- info: 'QuantumInfo.Channel.stinespringIsom_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.stinespringIsom_isom

/-- info: 'QuantumInfo.Channel.apply_eq_traceRight_stinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_eq_traceRight_stinespring

/-- info: 'QuantumInfo.Channel.ofIsometry_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.ofIsometry_apply

-- Canonical channels (Cat-1 staging; phase C3 of specs/channels-plan.md). The
-- unitary channel (ρ ↦ UρUᴴ), the trace-out channel (ρ ↦ traceRight ρ, the literal
-- discard-the-environment from C2's ofIsometry 1), and the mixed-unitary channel
-- (ρ ↦ ∑ᵢ pᵢ • Uᵢ ρ Uᵢᴴ, the dephasing/depolarizing/bit-flip generaliser).
-- Foundational triple.
/-- info: 'QuantumInfo.Channel.unitaryChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.unitaryChannel_apply

/-- info: 'QuantumInfo.Channel.traceOutChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.traceOutChannel_apply

/-- info: 'QuantumInfo.Channel.mixedUnitaryChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.mixedUnitaryChannel_apply

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

/-- info: 'MeasureTheory.measurePreserving_swapSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measurePreserving_swapSlot

-- A5 STEP ONE: THE DUHAMEL BOUND (2026-08-02, Mathlib/Analysis/Matrix/DuhamelBound.lean).
-- The quantitative engine of (eps,T)-projectability: for skew-Hermitian generators,
-- ||exp(tC) - exp(tA)|| <= |t| ||C - A|| in the L2 operator norm; Hermitian corollary
-- ||exp(t(-iH)) - exp(t(-iH_0))|| <= |t| ||H - H_0||. Proved WITHOUT integrals: the interpolant
-- phi(s) = exp(sC) exp((t-s)A) has derivative exp(sC)(C-A)exp((t-s)A), of norm <= ||C-A|| because
-- both exponential factors are UNITARY (l2_opNorm_exp_smul_skew; unitarity inlined when the file
-- was GENERALIZED 2026-08-07 from Fin n to any finite index for the CV-9 pricing route + the
-- L2 norm being a C*-norm), and the mean-value inequality finishes. CSD-free, upstream candidate.
-- READING FOR A5: a Hamiltonian eps-close in operator norm to a sector-projectable one generates
-- dynamics that sector dynamics SHADOWS to within eps*T over [-T, T] -- what makes a Hamiltonian
-- QUANTUM-EFFECTIVE. The predicate + exact-case-iff + shadowing packaging is the next step
-- (SigmaLayer/ApproxProjectability.lean, not yet written).
/-- info: 'Matrix.l2_opNorm_exp_smul_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.l2_opNorm_exp_smul_skew

/-- info: 'Matrix.norm_exp_smul_sub_exp_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_exp_smul_sub_exp_smul_le

/-- info: 'Matrix.norm_exp_smul_neg_I_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_exp_smul_neg_I_sub_le

/-- info: 'Projectivization.connectedSpace_of_isConnected_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.connectedSpace_of_isConnected_nonzero

-- (conditioning toolkit moved to CsdLean4/Mathlib/Probability/ConditionalProbability.lean,
-- 2026-08-02 -- the S-item extraction for upstream)
/-- info: 'ProbabilityTheory.cond_prod_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.cond_prod_prod

-- E3b: No-communication, reduced-density form. Alice's local unitary U⊗I leaves
-- Bob's reduced state (traceLeft ρ) invariant, via the partial-trace cyclicity
-- lemma. The structured form lands on the LF2 DensityOperatorIx.reducedLeft.
-- Foundational triple.
/-- info: 'Matrix.traceLeft_conjTranspose_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_conjTranspose_kronecker_one

/-- info: 'Matrix.traceLeft_sum_conjTranspose_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_sum_conjTranspose_kronecker_one

/-- info: 'QuantumInfo.Channel.tensorRight_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.tensorRight_apply

-- Trace distance foundation (Cat-1 staging; K3 of specs/qi-qec-roadmap.md). Trace norm
-- = ∑|λᵢ| and trace distance ½‖ρ-σ‖₁; the distinguishability headline traceDist = 0 ↔ ρ=σ,
-- and traceNorm of a PSD operator = its trace. Foundational triple. (K3 metric set + the
-- data-processing inequality are both closed — see channel_traceDist_le pinned below.)
/-- info: 'QuantumInfo.traceDist_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_eq_zero_iff

/-- info: 'QuantumInfo.traceDist_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_comm

-- Trace-norm subadditivity ‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁ and the trace-distance triangle inequality
-- D(ρ,τ) ≤ D(ρ,σ) + D(σ,τ) (K3 metric core completed; specs/trace-distance-triangle-plan.md).
-- Jordan decomposition via Matrix.IsHermitian.cfc + the PSD-product trace bound. Foundational
-- triple, Gleason-free.
/-- info: 'QuantumInfo.tr_psd_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.tr_psd_mul_nonneg

/-- info: 'QuantumInfo.traceNorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceNorm_add_le

/-- info: 'QuantumInfo.traceDist_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_triangle

-- CPTP data-processing inequality traceDist (Φρ) (Φσ) ≤ traceDist ρ σ (K3; channels cannot
-- increase distinguishability). Channel adjoint Φ†(P) = ∑ Kᵢᴴ P Kᵢ (unital + positive ⟹
-- 0 ≤ Φ†P ≤ I), variational form D = Re Tr(D₊) for traceless Hermitian D, and the L6 key bound.
-- Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.Channel.adjoint_unital' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_unital

/-- info: 'QuantumInfo.Channel.adjoint_trace_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_trace_mul

/-- info: 'QuantumInfo.channel_traceDist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.channel_traceDist_le

/-- info: 'QuantumInfo.traceDist_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_le_one

/-- info: 'QuantumInfo.traceDist_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_conj_unitary

-- Helstrom bound: minimum-error state discrimination (K3, Mathlib/QuantumInfo/Helstrom.lean).
-- The OPERATIONAL meaning of the trace distance, and the converse companion to
-- channel_traceDist_le above: channels cannot increase distinguishability, and the Helstrom
-- bound is exactly how much distinguishability a measurement can extract. Both halves are
-- pinned -- the bound (successProb_le, over every two-outcome test 0 ≤ E ≤ 1) AND its
-- ATTAINMENT (successProb_helstromTest, at the positive-eigenspace projector of the Helstrom
-- operator), so ½(1 + D) is the optimum, not merely an upper bound. Equal-prior form
-- errorProb_helstromTest: P_error = ½(1 − D(ρ₀,ρ₁)); general-prior form successProbPrior_le:
-- P_success ≤ ½(1 + ‖p₀ρ₀ − p₁ρ₁‖₁). Extremes: D = 0 forces a coin flip for EVERY E
-- (helstrom_indistinguishable), D = 1 permits an error-free test (helstrom_perfect).
-- Foundational triple, no `sorry`, no `native_decide`. Complements Empirical/QM/USD.lean
-- (zero error at the cost of an inconclusive outcome) -- the other end of the trade-off.
/-- info: 'QuantumInfo.re_trace_posPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_posPart_eq

/-- info: 'QuantumInfo.re_trace_mul_le_helstrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_mul_le_helstrom

/-- info: 'QuantumInfo.re_trace_mul_helstrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_mul_helstrom

/-- info: 'QuantumInfo.helstromTest_isTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstromTest_isTest

/-- info: 'QuantumInfo.successProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProb_le

/-- info: 'QuantumInfo.successProb_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProb_helstromTest

/-- info: 'QuantumInfo.errorProb_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.errorProb_ge

/-- info: 'QuantumInfo.errorProb_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.errorProb_helstromTest

/-- info: 'QuantumInfo.helstrom_indistinguishable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstrom_indistinguishable

/-- info: 'QuantumInfo.helstrom_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstrom_perfect

/-- info: 'QuantumInfo.successProbPrior_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProbPrior_le

/-- info: 'QuantumInfo.successProbPrior_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProbPrior_helstromTest

-- Spectral von Neumann entropy S(ρ) = ∑ᵢ negMulLog(λᵢ) = −Tr(ρ log ρ) (K1-A of specs/k1-plan.md).
-- Cat-1 staging beside TraceDistance; the operator-form identity (via re_trace_cfc), S ≥ 0 for a
-- density operator (eigenvalues in [0,1]), pure-state vanishing (rank-1 projection), and unitary
-- invariance (charpoly conjugation-invariance). Foundational triple, Gleason-free. Additivity on
-- tensor products is stated under an explicit eigenvalue-product hypothesis (no Kronecker spectral
-- theorem in Mathlib); discharging it is the deferred K1-A.2 item.
/-- info: 'QuantumInfo.vonNeumannEntropy_eq_re_trace_cfc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_re_trace_cfc

/-- info: 'QuantumInfo.vonNeumannEntropy_eq_neg_re_trace_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_neg_re_trace_mul_log

/-- info: 'QuantumInfo.cfc_id_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_id_mul_log

/-- info: 'QuantumInfo.negMulLog_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.negMulLog_mul

/-- info: 'QuantumInfo.charpoly_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.charpoly_conj_unitary

/-- info: 'QuantumInfo.vonNeumannEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_nonneg

/-- info: 'QuantumInfo.vonNeumannEntropy_eq_zero_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_zero_of_pure

/-- info: 'QuantumInfo.vonNeumannEntropy_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_conj_unitary

/-- info: 'QuantumInfo.vonNeumannEntropy_kronecker_of_eigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_kronecker_of_eigenvalues

-- K1-A.2 (specs/k1-plan.md): the Kronecker spectrum discharges the eigenvalue-product
-- hypothesis, making tensor additivity UNCONDITIONAL. spectral_sum_kronecker is the
-- load-bearing fact (eigenvalues of ρ⊗σ are the products λρ·λσ, in permutation-invariant
-- spectral-sum form); vonNeumannEntropy_kronecker is the headline S(ρ⊗σ) = S(ρ)+S(σ) for
-- density operators (PSD + unit trace), no spectral hypothesis. Foundational triple.
/-- info: 'QuantumInfo.spectral_sum_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.spectral_sum_kronecker

/-- info: 'QuantumInfo.vonNeumannEntropy_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_kronecker

-- General diagonal entropy (Cat-1, LF6-B.3 prerequisite): S(diagonal ↑d) = ∑ negMulLog(dᵢ),
-- via charpoly_diagonal + spectral_sum_eq_of_charpoly_prod (the const-smul-one route generalised).
-- Consumed by the LF6-B.3 Born-vector entropy witness (the decohered reduced state is diagonal).
/-- info: 'QuantumInfo.vonNeumannEntropy_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_diagonal

-- K1-B.1 (specs/k1-plan.md): matrix partial trace (Mathlib has none). Load-bearing results:
-- trace preservation (partialTraceRight_trace), tensor reduction with the trace of the
-- TRACED-OUT factor multiplying the surviving one (partialTraceRight_kronecker), PSD
-- preservation via the v⊗eₖ witness vectors (partialTraceRight_posSemidef /
-- partialTraceLeft_posSemidef), and the reduced-state-of-a-density-is-a-density corollaries
-- (partialTraceRight_density / partialTraceLeft_density). Foundational triple. Shared
-- prerequisite with the gated decoherence / entangled D1 tier and the Landauer touchpoint.
/-- info: 'QuantumInfo.partialTraceRight_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_trace

/-- info: 'QuantumInfo.partialTraceRight_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_kronecker

/-- info: 'QuantumInfo.partialTraceLeft_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_kronecker

/-- info: 'QuantumInfo.partialTraceRight_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_posSemidef

/-- info: 'QuantumInfo.partialTraceLeft_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_posSemidef

/-- info: 'QuantumInfo.partialTraceRight_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_density

/-- info: 'QuantumInfo.partialTraceLeft_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_density

-- K1-B.2 (specs/k1-plan.md): quantum relative entropy + Klein's inequality. relEntropy_nonneg /
-- klein_inequality are Klein's inequality D(ρ‖σ) ≥ 0 for σ POSITIVE-DEFINITE (load-bearing: the
-- junk-log finite expression can be negative when supp ρ ⊄ supp σ). The technical core is the
-- DOUBLY-STOCHASTIC overlap matrix Dᵢⱼ = ‖Vᵢⱼ‖² (overlapV_row_sum / overlapV_col_sum) and the
-- cross-term spectral expansion Tr(ρ · cfc g σ) = ∑ᵢⱼ pᵢ g(qⱼ) ‖Vᵢⱼ‖² (trace_mul_cfc_eq), which
-- expresses a trace of a product of two operators in DIFFERENT eigenbases. The reduced-trace
-- identities (trace_mul_kronecker_one_right / _left, Tr(M(X⊗I)) = Tr(Tr_B M · X)) are the
-- subadditivity prerequisites (rehomed to PartialTrace.lean 2026-08-20, the Q27 arc; same
-- names, same namespace). Foundational triple. The Kronecker-log split and the resulting
-- subadditivity headline are the remaining K1-B.2 wall (see specs/k1-plan.md).
/-- info: 'QuantumInfo.relEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.relEntropy_nonneg

/-- info: 'QuantumInfo.klein_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.klein_inequality

/-- info: 'QuantumInfo.trace_mul_cfc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.trace_mul_cfc_eq

/-- info: 'QuantumInfo.overlapV_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.overlapV_row_sum

/-- info: 'QuantumInfo.overlapV_col_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.overlapV_col_sum

/-- info: 'QuantumInfo.trace_mul_kronecker_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.trace_mul_kronecker_one_right

-- K1-B.2 wall closure: the Kronecker-log operator split (cfc_log_kronecker, via the
-- decomposition-independent cfc_eq_conj_diagonal / Lagrange-interpolation route) and the
-- von Neumann subadditivity headline S(ρ_AB) ≤ S(ρ_A) + S(ρ_B) (marginals positive-definite,
-- ρ_AB only PSD -- pure entangled states covered). Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.cfc_eq_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_eq_conj_diagonal

/-- info: 'QuantumInfo.cfc_log_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_log_kronecker

/-- info: 'QuantumInfo.vonNeumannEntropy_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_subadditive

-- K1-A/B remainder (2026-06-17): the maximum-entropy bound S ≤ log d (concave Jensen),
-- Schmidt symmetry (pure-state marginals have equal entropy, via MMᴴ/MᴴM cospectrum),
-- purification existence, and Araki–Lieb |S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB) (for ρ_AB
-- positive-definite; the pure-entangled saturating case is excluded, by design).
-- Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.vonNeumannEntropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_le_log_card

/-- info: 'QuantumInfo.pure_marginal_entropy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pure_marginal_entropy_eq

/-- info: 'QuantumInfo.exists_purification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_purification

/-- info: 'QuantumInfo.araki_lieb_one_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.araki_lieb_one_side

/-- info: 'QuantumInfo.vonNeumannEntropy_araki_lieb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_araki_lieb

-- K1-C strong subadditivity (specs/k1-plan.md §K1-C): the mutual-information identity
-- D(ρ ‖ ρ_X⊗ρ_Y) = S(ρ_X)+S(ρ_Y)−S(ρ) (relEntropy_kronecker_eq_entropy_sub, unconditional)
-- and the CONDITIONAL reduction strong_subadditivity_of_relEntropy_monotone: SSA derived from
-- the data-processing inequality (DPI) carried as an EXPLICIT hypothesis hDPI. The deep
-- operator-convexity input (Lieb concavity / joint convexity of relative entropy / DPI) is NOT
-- in Mathlib and is isolated as hDPI; no axiom is introduced. Foundational triple on what lands.
/-- info: 'QuantumInfo.relEntropy_kronecker_eq_entropy_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.relEntropy_kronecker_eq_entropy_sub

/-- info: 'QuantumInfo.strong_subadditivity_of_relEntropy_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.strong_subadditivity_of_relEntropy_monotone

-- n-qubit register (R1 of specs/nqubit-register-plan.md): QReg n = EuclideanSpace ℂ
-- (Fin n → Fin 2); Born prob as a squared inner product (prob_eq_inner_sq), normalisation
-- of a unit state (sum_prob_eq_one), basis state measured with certainty (prob_basisState).
-- Foundational triple. The enabling infra for the quantum-algorithm branch.
/-- info: 'QuantumInfo.prob_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.prob_eq_inner_sq

/-- info: 'QuantumInfo.sum_prob_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sum_prob_eq_one

/-- info: 'QuantumInfo.prob_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.prob_basisState

-- Hadamard transform (R2): Hn = H^⊗n with product entries; Hn|0ⁿ⟩ = uniform superposition
-- (Hn_apply_zero, every amplitude = (1/√2)ⁿ). First step of every Hadamard algorithm.
-- Foundational triple.
/-- info: 'QuantumInfo.Hn_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_apply_zero

-- Hadamard unitarity (R3): character orthogonality ⟹ Hnᴴ * Hn = 1 (Hn_unitary), factored
-- per-qubit through the single-qubit orthogonality; Hn is also an involution (Hn_mul_self,
-- Hn * Hn = 1). Makes any Hadamard circuit's full output a legitimate probability vector.
-- Foundational triple.
/-- info: 'QuantumInfo.Hn_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_unitary

/-- info: 'QuantumInfo.Hn_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_mul_self

-- Quantum Fourier transform (R5): F j k = (1/√N) ω^{jk}, ω = exp(2πi/N) a primitive N-th
-- root of unity; unitary (qft_unitary, Fᴴ * F = 1) via roots-of-unity orthogonality
-- ∑ₖ ζᵏ = N·[ζ=1] (the ℂ-analogue of the Hadamard character sum). A finite N×N unitary.
-- Foundational triple.
/-- info: 'QuantumInfo.qft_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.qft_unitary

/-- info: 'QuantumInfo.traceNorm_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceNorm_of_posSemidef

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

-- MG-1 (2026-08-22, Projectivization/Metric.lean, specs/mathlib-gaps-plan.md): the first
-- METRIC on Projectivization anywhere — the rank-one projection embedding p -> P_p (scale-
-- invariant, descends by lift), injective, continuous off the staged quotient topology,
-- hence a CLOSED embedding from the compact P into the Hausdorff operator space; the metric
-- pulls back via IsEmbedding.comapMetricSpace, whose replaceTopology makes the metric
-- topology DEFINITIONALLY the staged quotient topology (no diamond).
-- dist p q = ||P_p - P_q|| (dist_eq). Unlocks the epsilon-ball forms of the C2 arc (Q28).
/-- info: 'Projectivization.injective_toProjCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.injective_toProjCLM

/-- info: 'Projectivization.isClosedEmbedding_toProjCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isClosedEmbedding_toProjCLM

/-- info: 'Projectivization.instMetricSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMetricSpace

/-- info: 'Projectivization.dist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.dist_eq

-- MG-2 bricks a/b (2026-08-22, Projectivization/FubiniStudyLebesgue.lean): Fubini-Study as a
-- LEBESGUE-ABSOLUTELY-CONTINUOUS pushforward. The normalized Lebesgue measure on the punctured
-- unit ball of C^N is U(N)-invariant (unitaries act by isometries, which preserve the canonical
-- volume and the ball), so its projectivization IS fubiniStudyMeasure by the staged uniqueness
-- theorem. Payoff: the null-transport principle -- a ray set whose vector cone is Lebesgue-null
-- is Fubini-Study-null -- plus the elementary Fubini-slicing lemmas (coordinate hyperplanes and
-- the coordinate quadratic's zero set are null; NO polynomial-zero-set theory needed).
/-- info: 'Matrix.UnitaryGroup.pi_quadratic_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.pi_quadratic_null

/-- info: 'Matrix.UnitaryGroup.volume_ofLp_preimage_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.volume_ofLp_preimage_null

/-- info: 'Matrix.UnitaryGroup.map_ballMeasure_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.map_ballMeasure_eq_fubiniStudy

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_null_of_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_null_of_cone

-- E3 spike (2026-08-22, equilibration-arc-plan.md): the rays of a PROPER subspace are
-- Fubini-Study-null. Their cone is the subspace, and a proper subspace is Lebesgue-null
-- (Measure.addHaar_submodule). Reusable, and the reason a microcanonical restriction to an
-- exact spectral sector cannot be defined by restricting mu_FS -- see
-- Thermo/SectorRestriction.lean for the arena-level consequence.
/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_subspaceRays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_subspaceRays

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

-- Q28 item 1 (2026-08-21, FubiniStudyUnique.lean): FUBINI-STUDY ATOMLESSNESS by pigeonhole,
-- no stabiliser Haar measure. Transitivity + invariance make all singletons equal in mass
-- (fubiniStudyMeasure_singleton_eq); the projective space is infinite for 2 <= N
-- (projectivization_infinite -- the rays [e0 + t*e1], t : NAT, pairwise distinct); a
-- probability measure cannot give arbitrarily many disjoint points a common positive mass.
-- Retires KahlerInstance.lean's "Haar-of-subgroup" caveat; feeds the null-fibre corollary
-- (SigmaLayer/PreparationDensity.lean) that makes the pure-state Dirac wrapper unreachable
-- as a physical preparation (the C2 region-preparation proposition's last step).
/-- info: 'Matrix.UnitaryGroup.projectivization_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.projectivization_infinite

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_singleton

-- Pointwise Kähler fundamental form (2026-07-10): the form-level analogue of fubiniStudyMeasure. On a
-- complex inner-product space (the tangent model ψ^⊥ of ℂℙ^{N-1}) the flat Hermitian structure gives the
-- Kähler triple g = re⟪·,·⟫, ω = im⟪·,·⟫, J = i•·. Proved pointwise & axiom-free: J²=-1, ω alternating
-- ℝ-bilinear, J-compatibility ω u v = g(Ju) v, dual g u v = ω u (Jv), ω J-invariant (a (1,1)-form),
-- positivity ω u (Ju) = ‖u‖². This is the "compatible with J + positive" half of Kähler. Closedness dω=0
-- and the global ω^∧n/n! = μ_FS need manifold exterior calculus (absent from Mathlib) and stay blocked.
/-- info: 'Kahler.fubiniStudy_pointwise_kahler_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fubiniStudy_pointwise_kahler_compatibility

/-- info: 'Kahler.fundamentalForm_eq_metric_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_eq_metric_complexStructure

/-- info: 'Kahler.fundamentalForm_complexStructure_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_complexStructure_self_pos

/-- info: 'Kahler.inner_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.inner_complexStructure

/-- info: 'Kahler.fundamentalForm_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_antisymm

-- Tangent-space tie (2026-07-11): the projective tangent model ψ^⊥ = (span ℂ {ψ})ᗮ is J-invariant, so
-- it is a complex subspace on which the pointwise Kähler triple restricts — the flat form INDUCES the
-- Fubini–Study structure on each tangent space of ℂℙ^{N-1} (still pointwise; no manifold needed).
/-- info: 'Kahler.tangent_complexStructure_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.tangent_complexStructure_invariant

-- Schrödinger flow = Kähler symplectomorphism (2026-07-11): ties the pointwise Kähler form to the
-- Schrödinger pillar. Any ℂ-linear isometry preserves g = re⟪·,·⟫ and ω = im⟪·,·⟫
-- (kahler_structure_isometry_invariant), so exp(-itH) (schrodingerUnitary, unitary) preserves the FS
-- metric AND symplectic form — QM evolution is a symplectic isometry of the CP^{N-1} Kähler geometry
-- (Kibble/Ashtekar–Schilling picture, pointwise/linear level). The converse X_H = ω⁻¹dH (KG-2) stays
-- Mathlib-blocked (manifold symplectic-gradient API).
/-- info: 'Kahler.kahler_structure_isometry_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.kahler_structure_isometry_invariant

-- `whitespace := lax` because the long theorem names push the axiom list
-- past the pretty-printer width, wrapping it across lines; lax collapses
-- the wrap so a single-line docstring matches.
/-- info: 'Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy

/-- info: 'Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn

/-! ### Transition probability on ℂℙ^{N-1} (Wigner / FS rigidity foundation)

The transition-probability API plus the forward (realisability) direction
`U(N) ⊆ transition-preservers`, and the coincidence / orthogonality
characterisations. All foundational-triple-only. The Wigner / FS converse is
now PROVED (`wigner_rigidity`, W6), pinned below. -/

/-- info: 'Projectivization.transProb_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_smul_unitary

/-- info: 'Projectivization.transProb_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_eq_one_iff

/-- info: 'Projectivization.transProb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_eq_zero_iff

/-! #### Step (1) of the Wigner / FS rigidity converse

The `TransProbPreserving` predicate (injectivity + orthogonality preservation)
and the `U(N) → TransProbPreserving` realisability inclusion. All
foundational-triple-only. The Wigner converse itself is now PROVED
(`wigner_rigidity`, W6, pinned below); ℂ-linearity is DERIVED (not assumed) and
the antiunitary branch is genuinely present, so no branch elimination is needed. -/

/-- info: 'Projectivization.TransProbPreserving.injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.injective

/-- info: 'Projectivization.transProbPreserving_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProbPreserving_unitary

/-- info: 'Projectivization.TransProbPreserving.orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.orthogonal

-- Wigner converse step (2a): the image ONB vector's ray is the image ray
-- (`mk (imageOrthonormalBasis i) = f (mk (b i))`).
/-- info: 'Projectivization.mk_imageOrthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_imageOrthonormalBasis

-- Wigner converse step (2b) headline: the candidate unitary agrees with `f` on
-- the source basis points (`mk (candidateUnitary (b i)) = f (mk (b i))`).
/-- info: 'Projectivization.candidateUnitary_agrees_on_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.candidateUnitary_agrees_on_basis

-- Wigner converse step (2c) frame reduction: the frame-reduced map
-- `projMap (candidateUnitary hf b).symm ∘ f` is `TransProbPreserving` ...
/-- info: 'Projectivization.reducedMap_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_transProbPreserving

-- ... and fixes every source basis ray (`reducedMap hf b (mk (b i)) = mk (b i)`),
-- reducing the open converse to the single Wigner normal-form lemma. Fixing the
-- basis rays does NOT make the map the identity (diagonal-phase freedom is genuine).
/-- info: 'Projectivization.reducedMap_fixes_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_fixes_basis

-- Wigner converse Stage 1 (moduli-preservation kernel): a preserving map fixing
-- a point `q` preserves the transition probability from every point to `q`.
/-- info: 'Projectivization.TransProbPreserving.transProb_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.transProb_of_fixed

-- Wigner converse Stage 1: transition probability to the `i`-th basis ray is the
-- normalised squared modulus of the `i`-th coordinate `b.repr ψ i`.
/-- info: 'Projectivization.transProb_srcPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_srcPoint

-- Wigner converse Stage 1 HEADLINE: the frame-reduced map preserves the modulus
-- profile of the coordinates, `‖b.repr φ i‖²/‖φ‖² = ‖b.repr ψ i‖²/‖ψ‖²`. No
-- ℂ-linearity assumed.
/-- info: 'Projectivization.reducedMap_coord_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_coord_modulus

-- Wigner converse Stage 2 support infrastructure.
/-- info: 'Projectivization.add_basis_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.add_basis_ne_zero

/-- info: 'Projectivization.repr_eq_pair_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.repr_eq_pair_of_support

/-- info: 'Projectivization.mk_eq_two_level_of_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_eq_two_level_of_profile

-- Wigner converse Stage 2 HEADLINE: `reducedMap hf b (mk (b i₀ + b i)) =
-- mk (b i₀ + ε • b i)` for a unimodular `ε`. The image ray is pinned up to the
-- single phase `ε`; the phase cocycle (Stage 3) remains the documented open target
-- (stated neither as an axiom nor a sorry). No ℂ-linearity assumed.
/-- info: 'Projectivization.reducedMap_two_level_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_two_level_normal_form

-- Wigner W2 (A) HEADLINE: the concrete antiunitary witness. `conjProj`
-- (coordinatewise complex conjugation as a ray map) is `TransProbPreserving`,
-- an inhabitant of the ANTIUNITARY class (`conjVec` is conjugate-linear, not the
-- underlying map of any `≃ₗᵢ[ℂ]`), so the eventual Wigner dichotomy is non-vacuous
-- on the antiunitary side. Foundational-triple only.
/-- info: 'Projectivization.conjProj_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_transProbPreserving

-- Wigner W2 (B) HEADLINE: Stage 3 piece 1 (the diagonal-phase reduction). The
-- diagonally-reduced map (frame reduction post-composed with the inverse diagonal
-- isometry built FROM the extracted Stage-2 phases) fixes the two-level rays
-- `mk (b i₀ + b i)`. ℂ-linearity is DERIVED not assumed (`D` is constructed from
-- the phases, not posited of `f`). The residual is pieces 2-3 (the 2-cocycle +
-- the unitary/antiunitary dichotomy). Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_fixes_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_two_level

-- Wigner W3 HEADLINE (heart of piece 2): the two-level relative-phase constraint.
-- `diagReducedMap` preserves `Re(conj d_{i₀} · d_i)/‖φ‖²` (the real part of the
-- relative phase between the anchor coordinate and any other), so
-- `arg(d_i/d_{i₀}) = ± arg(c_i/c_{i₀})` with the ± sign (the cocycle's ℤ/2 datum)
-- genuinely FREE. Derived from the transProb overlap algebra; NO ℂ-linearity of
-- `f`/`h` is assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_two_level_relphase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_two_level_relphase

-- Wigner W3 (general form + moduli + conditional pairwise leg).
/-- info: 'Projectivization.two_level_relphase_of_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_relphase_of_fixes

/-- info: 'Projectivization.diagReducedMap_coord_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_coord_modulus

-- Conditional (i, j) leg of the 2-cocycle: holds whenever `mk (b i + b j)` is
-- fixed. The non-anchored fixing is discharged by W4 below.
/-- info: 'Projectivization.diagReducedMap_pairwise_relphase_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_pairwise_relphase_of_fixed

-- Wigner W4 HEADLINE (piece 2 closure, triple-support fixing): the equal triple
-- ray `mk (b i₀ + b i + b j)` is fixed by `diagReducedMap`. Route: Stage-1 moduli
-- (support {i₀,i,j}, equal moduli) + the two anchored two-level relphase relations
-- + saturation (`norm_eq_re_imp_eq`) forcing phase alignment + triple-support
-- reconstruction. The probe is REAL-coordinate, so the fixing is consistent with
-- BOTH the unitary and antiunitary branches: it establishes cocycle coboundary
-- structure, NOT the global sign. NO ℂ-linearity assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_fixes_three_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_three_level

-- Wigner W4 HEADLINE (non-anchored two-level fixing): `mk (b i + b j)` fixed for
-- every `i, j ≠ i₀`, using the fixed triple as a both-coordinate probe through
-- `transProb_of_fixed`. Discharges the residual input of piece 2. Foundational-triple.
/-- info: 'Projectivization.diagReducedMap_fixes_two_level_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_two_level_general

-- Wigner W4 HEADLINE (unconditional pairwise relative phase, the 2-cocycle
-- coboundary): `Re(conj d_i d_j)/‖φ‖² = Re(conj c_i c_j)/‖ψ‖²` for ALL `i,j ≠ i₀`,
-- unconditionally. The ± sign of the imaginary parts stays free (resolved only by
-- piece 3). NO ℂ-linearity assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_pairwise_relphase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_pairwise_relphase

-- Wigner W3 owed helper: the representative-independent ray-map identity for the
-- antiunitary witness `conjProj`, needed for the eventual antiunitary assembly.
/-- info: 'Projectivization.conjProj_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_mk

-- Wigner W5 (piece 3): the complex probe pins the IMAGINARY part of the relative
-- phase (the datum invisible to the real probes of pieces 1-2). Fixed complex ray
-- ⟹ Im preserved; flipped complex ray ⟹ Im negated (the antiunitary reading).
-- Pure overlap algebra; NO ℂ-linearity. Foundational-triple only.
/-- info: 'Projectivization.two_level_imrelphase_of_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_imrelphase_of_fixes

/-- info: 'Projectivization.two_level_imrelphase_of_flips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_imrelphase_of_flips

-- Wigner W5 HEADLINE (reconstruction, unitary branch): a preserving map fixing all
-- basis, real two-level AND complex two-level rays is the IDENTITY on rays. The full
-- Gram datum `conj dᵢ dⱼ ‖ψ‖² = conj cᵢ cⱼ ‖φ‖²` forces `φ = λ • ψ`. ℂ-linearity is
-- an OUTPUT, never an input. Foundational-triple only.
/-- info: 'Projectivization.eq_id_of_fixes_all_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_id_of_fixes_all_two_level

-- Wigner W5 HEADLINE (reconstruction, antiunitary branch): fixing the real rays but
-- FLIPPING the complex rays gives coordinatewise conjugation in the basis `b`. The
-- genuine antiunitary branch; ℂ-linearity is an OUTPUT. Foundational-triple only.
/-- info: 'Projectivization.eq_bconj_of_flips_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_bconj_of_flips_complex

-- Wigner W5 HEADLINE (the branch-distinguishing complex probe): the diagonally
-- reduced map sends `mk (b i₀ + I • b i)` to itself (+ branch) OR to
-- `mk (b i₀ - I • b i)` (− branch). Unlike the real probes, this ray is NOT
-- conjugation-invariant, so it distinguishes the unitary from the antiunitary
-- branch. The ± is forced by `Re ε = 0`, `‖ε‖ = 1`. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_complex_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_complex_probe

-- Wigner W5 HEADLINE (the reduced-map dichotomy): given the GLOBAL complex-sign
-- closure (all complex two-level rays fixed, or all flipped), the diagonally reduced
-- map is GLOBALLY the identity on rays, or GLOBALLY coordinatewise conjugation. Both
-- branches genuine; ℂ-linearity an OUTPUT. The residual to an unconditional Wigner
-- converse is exactly the global-sign closure. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_dichotomy_of_complexSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_dichotomy_of_complexSign

-- Wigner W6 HEADLINE (global-sign closure): the per-pair `± I` complex-probe datum
-- is globally consistent (all complex two-level rays fixed, or all flipped),
-- discharged from transition-probability preservation alone via the master witness
-- `masterVec` and the abstract Gram-triple core `sign_link_core`. No `Complex.arg`
-- choice, no linearity; both branches stay alive. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_complexSign_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_complexSign_closure

-- Wigner W6 HEADLINE (unconditional reduced-map dichotomy): the diagonally reduced
-- map is GLOBALLY the identity on rays, or GLOBALLY coordinatewise conjugation in `b`
-- (the global-sign residual discharged). Both branches genuine; ℂ-linearity an
-- OUTPUT. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_dichotomy

-- Wigner W6 HEADLINE (the converse): every `TransProbPreserving` self-map of
-- `ℂℙ^{N-1}` is `projMap e` for a `≃ₗᵢ[ℂ]` `e` (UNITARY) or `projMap e ∘ conjProj`
-- (ANTIUNITARY). The honest Wigner disjunction. ℂ-linearity of `e` is an OUTPUT of
-- the dichotomy landing on the identity, never assumed; the antiunitary branch is
-- genuinely present; the global sign is forced from transProb preservation alone.
-- No `busch`, no `sorry`, no `native_decide`. Foundational-triple only.
/-- info: 'Projectivization.wigner_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wigner_rigidity

-- Wigner rigidity, `Matrix.unitaryGroup` reformulation (2026-07-02): the classic
-- `∃ U : unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p` (UNITARY) ∨ `f p = U • conjProj p`
-- (ANTIUNITARY) form, via the isometry→matrix bridge `unitaryOfIsometry` /
-- `projMap_eq_smul_unitary`; the `U • ·` action is the one used by
-- `transProbPreserving_unitary`. Foundational-triple only.
/-- info: 'Projectivization.wigner_rigidity_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wigner_rigidity_unitaryGroup

-- LF4-todo §13.2 discharge via Wigner (2026-07-02). The `CSDUnitaryBundle.U_isometry`
-- obligation is derived (not posited) from the intrinsic transition-probability
-- condition. `conjProj_ne_projMap`: coordinatewise conjugation is not a unitary
-- projective map (N ≥ 2). `transProbPreserving_isometry_dichotomy`: the honest
-- Hilbert-level dichotomy (unitary isometry ∨ antiunitary anti-isometry; the
-- antiunitary branch is exposed, not dropped). `smul_action_not_antiunitary`: the
-- sector action `g • ·` is not time-reversal (the no-time-reversal selection holds).
-- `u_isometry_of_transProbPreserving` / `ofTransProbPreserving`: Wigner OUTPUTS the
-- isometry `U`, discharging `U_isometry`. `cpSectorActionBundle`: non-vacuous
-- instantiation on the concrete Kähler instance via the sector action. All
-- foundational-triple only; no `busch`, no `sorry`, no `native_decide`. §13.2
-- discharges modulo the posited sector symmetry (SO-1); the measure-⟹-metric route is false
-- and not used.
/-- info: 'Projectivization.conjProj_ne_projMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_ne_projMap

/-- info: 'Projectivization.transProbPreserving_isometry_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProbPreserving_isometry_dichotomy

/-- info: 'Projectivization.smul_action_not_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_action_not_antiunitary

-- W5-S1: the projective-to-vector phase lift. Phase rigidity (the kernel of
-- U(N) → PU(N) is the circle: unitaries acting identically on every ray differ
-- by a unit phase) extracts the U(1) cocycle of the projected-flow family
-- (projectedFlow_phase_cocycle, the named obstruction), which obeys the
-- 2-cocycle law (phase_cocycle_identity). The coboundary datum b (the honest
-- S1 residual input: H²(ℝ,U(1)) ≠ 0 algebraically, so some input is genuinely
-- required) upgrades the family to a GENUINE vector-level one-parameter
-- unitary group realising the same flow (projectedFlow_phase_lift). Wired to
-- the S2 C^1 Stone theorem this gives the W5 capstone: the projected flow is
-- exp(-itH)-conjugation on rays for a Hermitian H
-- (projectedFlow_schrodinger_form). Non-vacuity: the whole chain fires
-- end-to-end on trivialKahlerOnticSetup with U = 1, c = 1, b = 1, H = 0.
/-- info: 'Projectivization.exists_unit_smul_of_smul_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_unit_smul_of_smul_eq_smul

/-- info: 'Projectivization.smul_eq_smul_of_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_eq_smul_of_eq_smul

/-- info: 'Matrix.UnitaryGroup.unit_smul_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.unit_smul_mem

-- W3 clopen-datum closure: the Bargmann discriminator. The Bargmann invariant
-- (normalised triple product on ℙ³) is preserved by unitaries and CONJUGATED
-- by the antiunitary conjProj; on a probe triple with Im Δ ≠ 0 (exists for
-- N ≥ 2) the two Wigner branches sit at the distinct values Δ vs conj Δ of one
-- scalar observable of the flow. This PROVES the branch separation ((ii) of
-- the W3 staged residual, incl. exclusivity of the Wigner disjunction) and
-- DERIVES the clopen datum from a scalar continuity hypothesis ((i) reduced:
-- continuity of t ↦ Δ(Φ_t p, Φ_t q, Φ_t r), the named remaining physical
-- input; deriving IT from flow continuity needs continuity of Δ on ℙ³ = local
-- sections of mk, the named follow-on). N ≤ 1 needs no datum
-- (projUnitary_of_dim_le_one). Non-vacuity: the constant observable of the
-- trivial witness fires the full selection.
/-- info: 'Projectivization.bargmann_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_smul_unitary

/-- info: 'Projectivization.bargmann_conjProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_conjProj

/-- info: 'Projectivization.bargmann_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_probe

/-- info: 'Projectivization.exists_bargmann_im_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_bargmann_im_ne_zero

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

/--
info: 'ProbabilityTheory.iIndepFun.pairwise_indepFun_indicator_preimage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.iIndepFun.pairwise_indepFun_indicator_preimage

/-- info: 'ProbabilityTheory.iIndepFun_eval_infinitePi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.iIndepFun_eval_infinitePi

/-! ### Operator-convexity ladder (Cat-1; L.0 predicate + L.1 inverse operator convexity
+ L.2 shifted-resolvent concavity rungs) -/

/-- info: 'Matrix.fromBlocks_inv_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.fromBlocks_inv_posSemidef

/-- info: 'Matrix.operatorConvexOn_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConvexOn_inv

/-- info: 'Matrix.inv_loewner_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inv_loewner_convex

/-- info: 'Matrix.cfc_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_inv_posDef

/-- info: 'Matrix.add_smul_one_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.add_smul_one_posDef

/-- info: 'Matrix.cfc_add_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_add_inv_posDef

/-- info: 'Matrix.inv_shift_loewner_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inv_shift_loewner_convex

/-- info: 'Matrix.cfc_neg_add_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_neg_add_inv_posDef

/-- info: 'Matrix.operatorConcaveOn_neg_add_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_neg_add_inv

/-- info: 'Matrix.cfc_affine_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_affine_output

/-- info: 'Matrix.OperatorConcaveOn.affine_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.OperatorConcaveOn.affine_output

/-! ### Reframing lemma : operator concavity ↔ ordinary `ConcaveOn` of `A ↦ cfc f A` (L.3a unlock) -/

/-- info: 'Matrix.convex_spectralSet_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.convex_spectralSet_Ioi

/-- info: 'Matrix.operatorConcaveOn_of_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_of_concaveOn

/-- info: 'Matrix.concaveOn_of_operatorConcaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.concaveOn_of_operatorConcaveOn

/-- info: 'Matrix.operatorConcaveOn_iff_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_iff_concaveOn

/-- info: 'Matrix.operatorConcaveOn_rpow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_rpow_zero

/-- info: 'Matrix.operatorConcaveOn_rpow_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_rpow_one

/-! ### A1 cfc-integral commutation + Löwner-order topology (OperatorConvex.lean `Integral`) -/

/-- info: 'Matrix.cfc_integral_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_integral_commute

/-- info: 'Matrix.isClosed_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isClosed_posSemidef

/-! ### `CStarMatrix ↔ Matrix` transport bridge (OperatorConvexBridge.lean) -/

/-- info: 'Matrix.cstar_cfc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_cfc

/-- info: 'Matrix.cstar_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_le_iff

/-- info: 'Matrix.cstar_isStrictlyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_isStrictlyPositive

/-- info: 'Matrix.matrix_log_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_log_le_log

-- B.4 (2026-08-22, MG-3): the rpow wall dissolved. The MG-3 probe found the obstruction was
-- exactly two generic instances not firing through the discrimination tree (the R-CFC over
-- IsSelfAdjoint — the existing shim — and NonnegSpectrumClass R, the second shim); with both
-- registered the upstream monotonicity tier (Rpow/Order.lean, post-dating the wall note)
-- fires on CStarMatrix, and B.4 transports it: the R>=0-cfcn naturality across the synonym
-- equiv, operator monotonicity of x^p (p in [0,1]) on the Loewner order, and sqrt
-- monotonicity, all on the bare Matrix carrier.
/-- info: 'Matrix.cstar_cfcₙ_nnreal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_cfcₙ_nnreal

/-- info: 'Matrix.matrix_nnrpow_le_nnrpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_nnrpow_le_nnrpow

/-- info: 'Matrix.matrix_sqrt_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_sqrt_le_sqrt

/-! ### C^1 finite-dimensional Stone theorem (StoneC1.lean, W5-S2 under smoothness) -/

/-- info: 'Matrix.StoneC1.eq_exp_of_hasDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.eq_exp_of_hasDeriv

/-- info: 'Matrix.StoneC1.exp_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.exp_smul_unitary

/-- info: 'Matrix.StoneC1.stone_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.stone_c1

-- Continuity-only Stone (2026-07-23): differentiability derived (FTC + integral averaging), not assumed.
/-- info: 'Matrix.StoneC1.stone_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.stone_continuous

/-- info: 'Matrix.StoneC1.trivial_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.trivial_group

/-- info: 'Matrix.StoneC1.skew_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.StoneC1.skew_witness

/-! ### ECDLP reversible-circuit substrate (Reversible/{Circuit,Cost}.lean) -/

/-- info: 'Reversible.denoteGate_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteGate_involutive

/-- info: 'Reversible.reversible_inverse_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reversible_inverse_correct

/-- info: 'Reversible.reversible_inverse_correct'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reversible_inverse_correct'

/-- info: 'Reversible.denote_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_bijective

/-- info: 'Reversible.cost_comp_toffoli_count' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cost_comp_toffoli_count

/-- info: 'Reversible.cost_comp_toffoli_depth_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cost_comp_toffoli_depth_le

/-- info: 'Reversible.denoteGate_apply_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteGate_apply_of_not_mem

/-- info: 'Reversible.denote_apply_of_forall_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_apply_of_forall_not_mem

/-! ### ECDLP reversible modular addition (Reversible/ModAdd.lean, Tranche 2) -/

/-- info: 'Reversible.regVal_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regVal_lt_two_pow

/-- info: 'Reversible.regVal_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regVal_update_eq

/-- info: 'Reversible.fullAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_correct

/-- info: 'Reversible.fullAdder_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_cost

/-- info: 'Reversible.rippleAdder_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleAdder_toffoli

/-- info: 'Reversible.rippleAdder_cnot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleAdder_cnot

/-- info: 'Reversible.fullAdder_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_apply_of_ne

/-- info: 'Reversible.fullAdder_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_correct_general

/-! ### ECDLP ripple carry-chain arithmetic correctness (ModAdd.lean, Tranche 2 Pass 2 Stage B) -/

/-- info: 'Reversible.regValRange_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_lt

/-- info: 'Reversible.rippleCirc_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_invariant

/-- info: 'Reversible.rippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_correct

/-! ### ECDLP reversible modular multiplication (ModMul.lean, Tranche 3 Stage A + B.1) -/

/-- info: 'Reversible.mulConst_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_bijective

/-- info: 'Reversible.multiplier_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.multiplier_toffoli

/-- info: 'Reversible.rippleCirc_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_toffoli

/-- info: 'Reversible.multiplier_ripple_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.multiplier_ripple_toffoli

/-! #### Stage B.1: per-step multiplication-accumulation correctness -/

/-- info: 'Reversible.regValRange_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_split

/-- info: 'Reversible.rippleCirc_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_preserves_external

/-- info: 'Reversible.accStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.accStep

/-! #### Stage B.2: the fold to `Acc = a · Y` -/

/-- info: 'Reversible.mulCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulCircuit_correct

/-- info: 'Reversible.mulLayout1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLayout1

/-- info: 'Reversible.mulCircuit_correct_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulCircuit_correct_zmod

/-! ### ECDLP reversible modular inverse (ModInv.lean, Tranche 4) -/

/-- info: 'Reversible.mul_modInv_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_modInv_of_unit

/-- info: 'Reversible.modInv_modInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modInv_modInv

/-- info: 'Reversible.modInv_isUnit_iff_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modInv_isUnit_iff_coprime

/-- info: 'Reversible.mulConst_modInv_leftInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_modInv_leftInverse

/-- info: 'Reversible.mulConst_modInv_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_modInv_bijective

/-! ### ECDLP layered-circuit depth (Depth.lean, Phase 2 S1) -/

/-- info: 'Reversible.denoteLayered_eq_denote_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteLayered_eq_denote_flatten

/-- info: 'Reversible.layeredToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.layeredToffoli_eq

/-- info: 'Reversible.rippleCirc_sequential_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_sequential_depth

/-- info: 'Reversible.sequential_rippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sequential_rippleCirc_correct

/-- info: 'Reversible.reduceTree4_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reduceTree4_wf

/-- info: 'Reversible.reduceTree4_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reduceTree4_correct

/-- info: 'Reversible.parallelXLayer_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.parallelXLayer_wf

/-! ### ECDLP modular reduction (Reversible/ModReduce.lean, Phase 2 S4) -/

/-- info: 'Reversible.rippleCirc_carryout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_carryout

/-- info: 'Reversible.rippleCirc_modReduce_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_modReduce_ge

/-! ### ECDLP S6.3a complete single-step modular reduction (Reversible/ModReduceCtrl.lean) -/

/-- info: 'Reversible.modReduce_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduce_correct

/-- info: 'Reversible.modReduce_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduce_in_range

/-- info: 'Reversible.modReduceCtrl_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduceCtrl_toffoli

/-! ### ECDLP S6.3b modular adder (Reversible/ModularAdd.lean) -/

/-- info: 'Reversible.modAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_correct

/-- info: 'Reversible.modAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_preserves_operand

/-- info: 'Reversible.modAdd_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_in_range

/-- info: 'Reversible.modularAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modularAdd_toffoli

/-! ### ECDLP S6.3c controlled modular adder (Reversible/ModularAddCtrl.lean) -/

/-- info: 'Reversible.cModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_correct

/-- info: 'Reversible.cModAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_operand

/-- info: 'Reversible.cModAdd_preserves_ctrl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_ctrl

/-- info: 'Reversible.cModAdd_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_in_range

/-- info: 'Reversible.cModularAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModularAdd_toffoli

/-! ### ECDLP S6.3d-1 modular doubling (Reversible/ModularDouble.lean) -/

/-- info: 'Reversible.modDouble_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_correct

/-- info: 'Reversible.modDouble_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_in_range

/-- info: 'Reversible.copyReg_correct_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_correct_operand

/-- info: 'Reversible.copyReg_correct_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_correct_B

/-- info: 'Reversible.modDouble_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_toffoli

/-- info: 'Reversible.copyReg_cnot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_cnot

/-! ### ECDLP S6.3d-2a Horner step + proven n=2 modular multiply (Reversible/ModularMul.lean) -/

/-- info: 'Reversible.hornerStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_correct

/-- info: 'Reversible.hornerStep_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_in_range

/-- info: 'Reversible.hornerStep_preserves_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_Y

/-- info: 'Reversible.mulStep2_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulStep2_correct

/-- info: 'Reversible.hornerStep_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_toffoli

/-- info: 'Reversible.modDouble_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_preserves_external

/-- info: 'Reversible.cModAdd_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_external

/-- info: 'Reversible.hornerStep_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_external

/-! ### ECDLP S6.3d-2b general-n modular field multiply X·Y mod N (Reversible/ModularMulLoop.lean) -/

/-- info: 'Reversible.mulLoop_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_correct

/-- info: 'Reversible.mulLoop_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_invariant

/-- info: 'Reversible.mulLoop_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_toffoli

/-- info: 'Reversible.regValRange_eq_hornerVal_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_eq_hornerVal_bits

/-- info: 'Reversible.horner_mod_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.horner_mod_step

/-- info: 'Reversible.mulLoopUpto_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoopUpto_preserves

/-! ### ECDLP S6.3-36a adder-parametric modular multiplier (Reversible/VerifiedAdder.lean) -/

/-- info: 'Reversible.genMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_correct

/-- info: 'Reversible.genMul_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_toffoli

/-- info: 'Reversible.genMul_corpusAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_correct

/-- info: 'Reversible.genMul_corpusAdder_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_toffoli

/-- info: 'Reversible.genMul_corpusAdder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_eq

/-! ### ECDLP S6.3e-1 modular subtraction a-b mod N (Reversible/ModularSub.lean) -/

/-- info: 'Reversible.modSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_correct

/-- info: 'Reversible.modSub_preserves_subtrahend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_subtrahend

/-- info: 'Reversible.modSub_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_in_range

/-- info: 'Reversible.modSub_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_toffoli

/-- info: 'Reversible.rippleSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleSub_correct

/-- info: 'Reversible.rippleSub_borrowout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleSub_borrowout

/-- info: 'Reversible.fullSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullSub_correct

/-! ### ECDLP S6.3e-2a modular const-multiply c*a mod N + negation -b mod N (Reversible/ModularConst.lean) -/

/-- info: 'Reversible.modConstMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_correct

/-- info: 'Reversible.modConstMul_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_preserves_operand

/-- info: 'Reversible.modConstMul_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_in_range

/-- info: 'Reversible.modConstMul_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_toffoli

/-- info: 'Reversible.modNeg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_correct

/-- info: 'Reversible.modNeg_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_in_range

/-- info: 'Reversible.modNeg_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_toffoli

/-! ### ECDLP fast Array-based circuit evaluator + bridge (Reversible/Eval.lean) -/

/-- info: 'Reversible.applyGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.applyGate_apply

/-- info: 'Reversible.runArr_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.runArr_apply

/-- info: 'Reversible.regValRangeArr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRangeArr_eq

/-! ### ECDLP controlled addition (Reversible/CtrlAdd.lean, Phase 2 S2) -/

/-- info: 'Reversible.cfullAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cfullAdder_correct

/-- info: 'Reversible.cfullAdder_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cfullAdder_correct_general

/-- info: 'Reversible.cRippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_correct

/-- info: 'Reversible.cRippleCirc_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_toffoli

/-- info: 'Reversible.cRippleCirc_anc_restored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_anc_restored

/-- info: 'Reversible.cRippleCirc_ctrl_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_ctrl_preserved

/-- info: 'Reversible.cRippleCirc_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_preserves_external

/-! ### ECDLP quantum x quantum multiply (Reversible/CtrlMul.lean, Phase 2 S2.3) -/

/-- info: 'Reversible.cAccStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cAccStep

/-- info: 'Reversible.cMulCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cMulCircuit_correct

/-- info: 'Reversible.cMulCircuit_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cMulCircuit_eq_mul

/-- info: 'Reversible.ctrlSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.ctrlSum_eq

/-! ### ECDLP carry-clean (Cuccaro) in-place adder (Reversible/CuccaroAdd.lean, Phase 2 Stage 1) -/

/-- info: 'Reversible.cuccaroAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_correct

/-- info: 'Reversible.cuccaroAdd_preserves_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_preserves_B

/-- info: 'Reversible.cuccaroAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_ancilla_clean

/-- info: 'Reversible.cuccaroAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_toffoli

/-! ### ECDLP carry-clean (Cuccaro) MODULAR adder (Reversible/CuccaroModAdd.lean, Phase 2 Stage 2) -/

/-- info: 'Reversible.cuccaroModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_correct

/-- info: 'Reversible.cuccaroModAdd_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_clean

/-- info: 'Reversible.cuccaroModAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_preserves_operand

/-- info: 'Reversible.cuccaroModAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_toffoli

/-! ### ECDLP carry-clean (Cuccaro) MODULAR multiply (Reversible/CuccaroModMul.lean, Phase 2 Stage 2b)

The Θ(n)-reusable-scratch modular multiply `X·Y mod N` and its two clean sub-gadgets
(`cuccaroModDouble` via in-place shift + parity flag-uncompute, `cuccaroCModAdd` via the masked
operand). All foundational-triple-only. -/

/-- info: 'Reversible.cuccaroModDouble_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_correct

/-- info: 'Reversible.cuccaroModDouble_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_clean

/-- info: 'Reversible.cuccaroModDouble_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_toffoli

/-- info: 'Reversible.cuccaroCModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_correct

/-- info: 'Reversible.cuccaroCModAdd_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_clean

/-- info: 'Reversible.cuccaroCModAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_toffoli

/-- info: 'Reversible.cuccaroModMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_correct

/-- info: 'Reversible.cuccaroModMul_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_clean

/-- info: 'Reversible.cuccaroModMul_preserves_XY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_preserves_XY

/-- info: 'Reversible.cuccaroModMul_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_toffoli

/-! ### ECDLP S6.3-36b carry-clean adder-parametric modular multiplier
(Reversible/VerifiedAdderCarryClean.lean)

The carry-clean (`Θ(n)`-qubit) counterpart of the 36a keystone: a restored-clean step interface
(`clean` precondition + restoration postcondition, single reused scratch bank), the parametric
multiplier + cost, and the faithfulness instance recovering `cuccaroModMul`'s `(X·Y) mod N`
correctness and `20·n²+14·n` Toffoli figure by instantiation. All foundational-triple-only. -/

/-- info: 'Reversible.genMulCC_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_correct

/-- info: 'Reversible.genMulCC_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_toffoli

/-- info: 'Reversible.genMulCC_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_clean

/-- info: 'Reversible.cuccaroModMulStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMulStep_spec

/-- info: 'Reversible.genMulCC_cuccaroAdder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_eq

/-- info: 'Reversible.genMulCC_cuccaroAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_correct

/-- info: 'Reversible.genMulCC_cuccaroAdder_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_toffoli

/-! ### AND-based reversible adder with explicit fresh per-carry AND temporaries (Reversible/AndAdd.lean,
Tier-X / L5-c prerequisite). The fresh-AND compute / uncompute attachment point + the full AND-based
ripple adder (separate sum register, fresh carry ancillas, explicit `inverse` uncompute pass).
Foundational-triple-only; the uncompute half (`andAdd_uncompute_toffoli`) is the measurement-route
saving target for L5-d. No amplitude bridge / no measurement (those are #31 / L5-d). -/

/-- info: 'Reversible.andCarry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCarry_correct

/-- info: 'Reversible.andUncompute_restores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andUncompute_restores

/-- info: 'Reversible.andCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_correct

/-- info: 'Reversible.andCell_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_ancilla_clean

/-- info: 'Reversible.andCarryCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCarryCell_correct

/-- info: 'Reversible.andAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_correct

/-- info: 'Reversible.andAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_ancilla_clean

/-- info: 'Reversible.andCell_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_toffoli

/-- info: 'Reversible.andAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_toffoli

/-- info: 'Reversible.andAdd_uncompute_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_uncompute_toffoli

-- The two reusable circuit-semantics infra lemmas (Mathlib-upstream candidates, cited by #31/L5-d):
-- pin their axiom footprint at the definition site (auditor recommendation).
/-- info: 'Reversible.denote_apply_of_forall_not_mem_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_apply_of_forall_not_mem_target

/-- info: 'Reversible.denote_agree_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_agree_on

/-! ### Gidney 1-Toffoli-per-carry adder (Reversible/GidneyAdder.lean, Build #35) -/

/-- info: 'Reversible.majCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.majCell_correct

/-- info: 'Reversible.majCell_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.majCell_toffoli

/-- info: 'Reversible.gidneyAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_correct

/-- info: 'Reversible.gidneyAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_ancilla_clean

/-- info: 'Reversible.gidneyAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_toffoli

-- Build 15e (ChannelCapacity, 2026-06-30): channel capacities of the de-isolation /
-- dephasing channel Φ_deph = decohereReducedN (15a), on the K1-A von Neumann entropy.
-- CLASSICAL info survives: computational-basis states are FIXED POINTS
-- (dephasing_fixes_basis_state), single-letter Holevo χ of the basis ensemble = log 2
-- (holevo_classical_eq_log_two, S(½I)−½·0−½·0). QUANTUM coherence destroyed: |+⟩⟨+| ↦ ½I
-- (dephasing_plus_eq_half_one), entropy jump 0 → log 2 (dephasing_destroys_coherence).
-- S(½I)=log 2 via the maximally-mixed value vonNeumannEntropy_const_smul_one (charpoly route).
-- Single-shot Holevo / coherent-information, NOT the regularized capacity; entropy concavity
-- (the general χ≥0 bound) gated on the open SSA fork. Ontic Σ-volume capacity D1-gated (LF6).

/-- info: 'QuantumInfo.vonNeumannEntropy_const_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_const_smul_one

/-- info: 'QuantumInfo.vonNeumannEntropy_maximally_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_maximally_mixed

-- CGLMP qudit Bell inequality (Cat-1, Mathlib/Probability/CGLMP.lean): the
-- general-d deterministic reduction (LHV = mixture of product strategies) + the
-- LHV-to-finite-optimisation bound, and the numeric CGLMP LHV bound I_d <= 2 for
-- d = 2, 3, 4 (finite check via decide on the division-cleared integer functional).
-- All foundational-triple-only. The general-d numeric bound is the named residual.

/-- info: 'ProbabilityTheory.CGLMP.cglmpLHV_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmpLHV_eq_integral

/-- info: 'ProbabilityTheory.CGLMP.cglmpLHV_le_of_det_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmpLHV_le_of_det_le

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound_three

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound_four

-- Tightness: the LHV bound is EXACTLY 2 (achieved), not loose -- guards the
-- bound-is-tight claim against future decide / ZMod churn.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_three_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_three_tight

/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_four_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_four_tight

-- The GENERAL-d CGLMP classical bound (the sawtooth counting argument, all d >= 2,
-- no decide) -- closes the general-d LHV-bound residual. scaledDetZ_eq_sawtooth is
-- the genuine equality reduction; scaledDetZ_le_general the general-d numeric bound
-- (val-wraparound handled via mod-d divisibility, auditor-verified tight + matching
-- the d=2,3,4 decide anchors); cglmp_lhv_bound the general-d LHV bound.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_eq_sawtooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_eq_sawtooth

/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_le_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_le_general

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound

-- LF6-5 tightness (2026-07-11): the general-d bound I_d ≤ 2 is TIGHT for all d. The all-zero local
-- strategy attains scaledDetZ = 2(d-1) (scaledDetZ_tight_general) hence cglmp = I_d = 2
-- (cglmp_detTable_tight_general), so 2 is the EXACT LHV optimum in every dimension (generalising the
-- decide anchors scaledDetZ_three_tight/_four_tight). No decide; sawtooth reduction only.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_tight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_tight_general

/-- info: 'ProbabilityTheory.CGLMP.cglmp_detTable_tight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_detTable_tight_general

-- ECDLP value-exact CONSTPROP pass (2026-07-17, Reversible/ConstProp.lean, the frontier's Toffoli lever):
-- cprop folds provably-determined CCX (known-0 control -> drop; known-1 -> CX). cprop_denote MACHINE-CHECKS
-- value-exactness (denote (cprop α c) s = denote c s for s the seed α describes), via foldGate_denote
-- (per-gate fold is value-exact) + stepAbs_agree (the forward abstract state stays sound). The informal
-- frontier lever, here a proved circuit-to-circuit transform.
/-- info: 'Reversible.cprop_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.cprop_denote

/-- info: 'Reversible.foldGate_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.foldGate_denote

/-- info: 'Reversible.stepAbs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.stepAbs_agree

-- CONSTPROP is a sound REDUCING optimization (cost side, 2026-07-18): the value-exact lever, now proved
-- BENEFICIAL. cprop_toffoli_le: the pass never increases the emitted Toffoli count ((circuitCost (cprop α c))
-- .toffoli ≤ (circuitCost c).toffoli) -- so with cprop_denote it is a valid Toffoli-reducing optimization.
-- foldGate_ccx_known_false: a non-degenerate CCX with a control known false folds AWAY (to []) -- where the
-- reduction is bought. andCell_constprop_reduces: the AND-adder carry cell [CCX a b g, CCX a c g, CCX b c g]
-- with carry-in known 0 constant-propagates 3 Toffoli -> 1, a value-exact 67% reduction on a real gadget.
/-- info: 'Reversible.cprop_toffoli_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.cprop_toffoli_le

/-- info: 'Reversible.foldGate_ccx_known_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.foldGate_ccx_known_false

/-- info: 'Reversible.andCell_constprop_reduces' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.andCell_constprop_reduces

/-- info: 'Matrix.norm_entry_le_l2_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_entry_le_l2_opNorm

-- The diagonal bound for the L2 operator norm (2026-08-07, L2OpNormDiagonal.lean): a diagonal
-- matrix with uniformly bounded entries has L2 opnorm at most that bound -- what turns the
-- Duhamel price ||lam . V|| into |lam| . sup|v| for the CV-9 diagonal interacting drive.
-- <=-direction only (what pricing consumes); equality is a separate upstream item.
/-- info: 'Matrix.l2_opNorm_diagonal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.l2_opNorm_diagonal_le

-- MixedLuders (2026-08-03, SigmaLayer/MixedLuders.lean; the outcome-conditioned mixed update,
-- MixedSwap's recorded extension + the fourth review's row). Spine: mixedSwapPrep FACTORS
-- (mixedSwapPrep_eq_prod — the mixture lives on system-and-register, bank common), so the pure
-- swap_luders_born (stated for arbitrary probability μ12) applies verbatim; positivity is a
-- theorem (mixed_outcome_pos, from Tr(ρ|e_i⟩⟨e_i|) ≠ 0 through the spectral bridge).
-- ★ mixed_post_bayes — the conditioned post-ensemble IS the Bayes-posterior mixture: component
-- j carries λ_j·p_i|j / Tr(ρ|e_i⟩⟨e_i|) (prior × likelihood / evidence); engine = the newly
-- staged ProbabilityTheory.cond_finsetSum (Bayes for finite mixtures, hypothesis-free by
-- ℝ≥0∞ conventions).
-- ★★ mixed_luders_followup — THE RECORD, NOT THE PEDIGREE, FIXES THE POST-STATE: follow-up
-- statistics after outcome i on the mixture are c'.rate [e_i] — the pure rank-one Lüders
-- update; at rank one the record erases the classical ignorance. ρ ↦ Π_iρΠ_i/Tr(ρΠ_i)
-- dynamically. Degenerate-on-mixed = recorded extension (rides JoinClosure; posteriors do NOT
-- coincide at rank ≥ 2 and no claim is made that they do).
/-- info: 'ProbabilityTheory.cond_finsetSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.cond_finsetSum

-- HamiltonianVectorField + PointerHamiltonianField (2026-08-06,
-- Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean +
-- SigmaLayer/PointerHamiltonianField.lean; BACKLOG A4's LINEAR FRAGMENT -- the manifold
-- form stays the section-2a wall, now NARROWED: upstream extDeriv exists on normed
-- spaces, manifold forms are upstream's own TODO).
-- hamiltonianVectorFieldOf w = -(J w) -- the omega-dual of a gradient representative;
-- the word is EARNED by the defining-equation theorem, not asserted:
-- ★ fundamentalForm_hamiltonianVectorFieldOf — omega (X w) v = g w v, pure algebra.
-- ★ hamiltonian_duality — X_H = omega^{-1} dH for ANY observable whose differential is
-- g-represented; no inverse is ever formed.
-- ★★ quadraticEnergy_hamiltonian_duality — the Hamiltonian vector field of the quantum
-- energy (1/2)<x,Ax> IS the Schroedinger field -(i·Ax): Kibble/Ashtekar-Schilling
-- "Schroedinger evolution is Hamiltonian flow" as a theorem, linear level.
-- ★★ coupling_hamiltonian_duality — the same on the smooth witness's OWN fixed-weight
-- generator couplingH w. With rampedU_schrodinger (the field generates the stroke) and
-- schrodinger_flow_kahler_symplectomorphism (the flow preserves omega), the fixed-weight
-- loop energy -> field -> flow -> form-preservation is closed at the formalisable level.
-- Honest scope: FLAT model, FIXED weights, constant omega. The joint-arena manifold
-- statement (H = sum w_j(x) h_j(q) on the product, X_H on the quotient) remains prose.
/-- info: 'Kahler.fundamentalForm_hamiltonianVectorFieldOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_hamiltonianVectorFieldOf

/-- info: 'Kahler.hamiltonian_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.hamiltonian_duality

/-- info: 'Kahler.hasFDerivAt_quadraticEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.hasFDerivAt_quadraticEnergy

/-- info: 'Kahler.quadraticEnergy_hamiltonian_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.quadraticEnergy_hamiltonian_duality

-- Flat closedness of the Fubini-Study fundamental form (A4 residue brick, 2026-08-06,
-- KahlerClosed.lean): extDeriv_const (constant differential forms are closed - the generic
-- Mathlib-gap lemma), the packaged alternating 2-form fundamentalFormAlt, and the headline
-- d(omega) = 0 on the flat tangent model. Manifold-level closedness on CP^{N-1} stays the
-- honest open residual (connectivity L1); this discharges its formalisable fragment.
/-- info: 'extDeriv_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extDeriv_const

/-- info: 'Kahler.fundamentalFormAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fundamentalFormAlt

/-- info: 'Kahler.extDeriv_fundamentalFormAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.extDeriv_fundamentalFormAlt

-- MG-4 (2026-08-22, KahlerPotential.lean): the NON-CONSTANT step. A form presented as dd^c of
-- a potential is closed for free (d^2 = 0, extDeriv_extDeriv), so the genuine Fubini-Study
-- form of an affine chart -- potential log(1 + ||z||^2), smooth because the argument stays
-- >= 1 -- is closed. dForm_eq_extDeriv checks the 1-form packaging really is the exterior
-- derivative of the 0-form (extDeriv_constOfIsEmpty), so the construction is not ad hoc.
-- HONEST SCOPE: the chart form is DEFINED by its potential; identifying it with the pullback
-- of Kahler.fundamentalForm is a second-derivative computation NOT done here, and the
-- manifold statement on CP^{N-1} remains Mathlib-blocked.
/-- info: 'Kahler.dForm_eq_extDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.dForm_eq_extDeriv

/-- info: 'Kahler.extDeriv_ddcForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.extDeriv_ddcForm

/-- info: 'Kahler.contDiff_fsPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.contDiff_fsPotential

/-- info: 'Kahler.extDeriv_fsChartForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.extDeriv_fsChartForm

-- Wigner uniqueness clause (CL-024 follow-up, 2026-08-06, WignerUniqueness.lean): the
-- inducing (anti)unitary of wigner_rigidity is unique up to a global phase, in the
-- theorem's own projMap/conjProj vocabulary. The matrix-vocabulary sibling
-- (exists_unit_smul_of_smul_eq_smul, PhaseRigidity.lean) predates it. Together with the
-- existence clause and the downstream exclusivity facts this completes the classical
-- Wigner/Bargmann statement.
/-- info: 'Projectivization.exists_unit_smul_of_projMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_unit_smul_of_projMap_eq

/-- info: 'Projectivization.conjProj_conjProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_conjProj

/-- info: 'Projectivization.exists_unit_smul_of_projMap_conjProj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_unit_smul_of_projMap_conjProj_eq

-- projMap functoriality (2026-08-07, added with the H2 interface): identity and
-- composition laws for the ray map of a linear isometry equivalence.
/-- info: 'Projectivization.projMap_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.projMap_refl

/-- info: 'Projectivization.projMap_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.projMap_trans

-- The Lie-Trotter product formula, skew-Hermitian case (2026-08-09,
-- TrotterProduct.lean; NO Trotter statement exists in Mathlib at the pin, checked).
-- The chain: the quantitative second-order remainder ||exp X - 1 - X|| <= ||X||^2 e^||X||
-- (series tail, termwise dominated); the one-step defect
-- ||exp X exp Y - exp(X+Y)|| <= (||X||+||Y||)^2 (3+||X||+||Y||) e^(||X||+||Y||) (four-term
-- split; only Y's skewness is needed); growth-free unitary telescoping
-- ||S^n - T^n|| <= n ||S - T||; and the formula: (exp(A/n) exp(B/n))^n -> exp(A+B) --
-- defect O(1/n^2), telescoping x n, total O(1/n) squeezed. CV-12: arbitrary-Hermitian
-- interacting drives become limits of constructible steps. CSD-free, upstream candidate.
/-- info: 'Matrix.norm_exp_sub_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_exp_sub_one_sub_le

/-- info: 'Matrix.norm_pow_sub_pow_le_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_pow_sub_pow_le_of_unitary

/-- info: 'Matrix.trotter_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.trotter_skew

-- The fundamental group of the circle (2026-08-10, CircleFundamentalGroup.lean).
-- Mathlib has the covering-space apparatus (path lifting, monodromy,
-- IsAddQuotientCoveringMap.fundamentalGroupEquiv) and exhibits Circle.exp as a quotient
-- covering with deck group 2piZ, but nowhere states that pi_1(S^1) is Z or even that it
-- is nontrivial -- checked at the pin. These three supply it: the deck-group equivalence,
-- and the nontriviality that downstream obstruction arguments consume (a time-one flow
-- map is homotopic to the identity, hence acts trivially on pi_1; a factor exchange on a
-- product arena does not). First brick of the relocation-generation obstruction.
/-- info: 'Circle.fundamentalGroupEquivZMultiples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Circle.fundamentalGroupEquivZMultiples

/-- info: 'Circle.fundamentalGroup_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Circle.fundamentalGroup_nontrivial

/-- info: 'Circle.not_simplyConnectedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Circle.not_simplyConnectedSpace

-- Non-contractibility, and the homotopy obstruction it powers (2026-08-10,
-- CircleFundamentalGroup.lean + FactorExchangeObstruction.lean). A self-map joined to the
-- identity by a flow is homotopic to the identity; if it collapses a section of a retract
-- onto a constant, that retract is forced contractible. One non-contractible retract
-- therefore obstructs. Stated basepoint-free: the usual pi_1 route must conjugate by the
-- path the basepoint traces under the homotopy, and none of that is needed here.
/-- info: 'Circle.not_contractibleSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Circle.not_contractibleSpace

/-- info: 'AddCircle.not_contractibleSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.not_contractibleSpace

/-- info: 'not_homotopic_id_of_section_collapsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_homotopic_id_of_section_collapsed

/-- info: 'not_isFlowTimeOne_of_section_collapsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_isFlowTimeOne_of_section_collapsed

-- CR-1 (2026-08-18, Mathlib\QuantumInfo\UnitaryPerturbation.lean, CV-26): the bridge between
-- the two norms a perturbative quantum argument uses -- drives are estimated in the L2
-- operator norm (Duhamel, Trotter), states are compared in the trace distance (where the DPI
-- lives). traceDist_conj_sub_le: D(U rho U+, V rho V+) <= 2||U - V||, uniform in the state and
-- free of dimension factors. Route: the difference is Hermitian AND traceless, so the
-- variational collapse applies and D+ = D P+; splitting (U-V)rho U+ + V rho (U-V)+ and cycling
-- the trace reduces to the Hoelder-lite |re tr(rho M)| <= ||M|| re tr rho, proved by
-- diagonalising rho (spectral_theorem) and bounding each rotated diagonal entry by the
-- operator norm (norm_entry_le_l2_opNorm). norm_cfc_le is the general functional-calculus norm
-- bound that gives ||P+|| <= 1. Named and feasibility-checked in specs\channel-rg-scoping.md
-- Sec 6 before any Lean was written; consumed by CV\ChannelRG.lean (CR-3).
/-- info: 'QuantumInfo.norm_cfc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.norm_cfc_le

/-- info: 'QuantumInfo.abs_re_trace_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.abs_re_trace_mul_le

/-- info: 'QuantumInfo.traceDist_conj_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.traceDist_conj_sub_le

-- Q16 CP brick, staging half (2026-08-20, Mathlib/Analysis/NormedSpace/TrotterGeneral.lean):
-- the Lie-Trotter product formula in a general complete normed R-algebra with ||1|| = 1 --
-- the de-skewed trotter_skew. Skewness entered the staged proof exactly twice and both
-- uses generalize: ||exp Y|| = 1 becomes <= e^||Y|| (absorbed by the same final constant),
-- and the norm-one telescoping becomes n*C^n with C = e^(s/n), so C^n = e^s stays bounded.
-- Explicit rate (1/n) s^2 (3+s) e^(2s). Consumed by LF6/LindbladPositivity.lean in the
-- endomorphism algebra of matrix space.
/-- info: 'NormedSpace.trotter_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NormedSpace.trotter_product

-- MG-5 (2026-08-22, QuantumInfo/RegisterTensor.lean): the REGISTER TENSOR FACTORISATION that
-- MATHLIB-GAPS recorded as missing. Mathlib has the inner product on E (x) F but nothing tying
-- it to the concrete EuclideanSpace/PiLp model QReg uses. Two reindexings plus
-- OrthonormalBasis.tensorProduct (the tensor of orthonormal bases is orthonormal, so both
-- sides carry ONBs indexed by the product and the isometry is the change of basis) give
-- regTensorEquiv : QReg (a+b) = QReg a (x) QReg b, with the basis-state computation rule.
-- tensorFirst is the consumer-facing payoff: an operator on the first block extended by the
-- identity, with its action on basis states. NOTE the honest boundary: this supplies the
-- INFRASTRUCTURE the measurement-gadget wall named; the n-fold hybrid amplitude equality is
-- separate work and is NOT claimed here.
/-- info: 'QuantumInfo.prodTensorEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.prodTensorEquiv

/-- info: 'QuantumInfo.regTensorEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.regTensorEquiv

/-- info: 'QuantumInfo.regTensorEquiv_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.regTensorEquiv_basisState

/-- info: 'QuantumInfo.tensorFirst_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.tensorFirst_basisState

-- The Boolean -> amplitude lift of reversible circuits (2026-08-21,
-- Mathlib/QuantumInfo/Reversible/Lift.lean): a reversible gate acts on the quantum register
-- QReg n as a permutation matrix on computational basis states, and the permutation is exactly
-- the gate's Boolean denote semantics modulo the Bool <-> Fin 2 recast. Extracted from
-- Empirical/QM/Measurement{UncomputeLift,Adder}.lean (Builds #31/#21), where the generic bridge
-- between two Cat-1 layers was invisibly filed as 3-Local regression content. Fixed-wire form
-- (andUncompMat_lifts_denote) and arbitrary-wire any-width form (ccxAtMat_lifts_denote).
/-- info: 'Reversible.andUncompMat_lifts_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.andUncompMat_lifts_denote

/-- info: 'Reversible.ccxAtMat_lifts_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.ccxAtMat_lifts_denote

-- E4's generic engine (2026-08-23, Mathlib/Dynamics/CorrelationDecay.lean): quantitative
-- correlation decay forces time averages to the space average, with an explicit rate.
-- ROUTE DECISION, and it is the whole feasibility question: the antecedent is stated as an
-- explicit bound |<(f.Phi^s)(f.Phi^t)> - <f>^2| <= eps(dist s t), NOT as abstract mixing.
-- Mathlib has no mixing definition and no pointwise Birkhoff, so the abstract route stops at
-- once. WALL NOTE CORRECTED AT SOURCE: Mathlib DOES have the von Neumann mean ergodic theorem
-- (ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection); the arc plan said
-- otherwise and was stale. It is still not what E4 needs -- no rate, and its limit is the
-- invariant projection, which is the space average only under an ergodicity hypothesis.
-- sum_sum_nat_dist_le is the only combinatorial content: within a row the map to the distance
-- is injective on each side of the diagonal SEPARATELY (truncated subtraction collapses the
-- left half to 0), hence the factor two.
-- Convergence is L^2. The in-measure form is NOT stated; a.e. convergence is what pointwise
-- Birkhoff would buy and is not available.
/-- info: 'MeasureTheory.sum_sum_nat_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.sum_sum_nat_dist_le

/-- info: 'MeasureTheory.integral_birkhoffAverage_sub_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.integral_birkhoffAverage_sub_sq_le

/-- info: 'MeasureTheory.integral_birkhoffAverage_sub_sq_le_cesaro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.integral_birkhoffAverage_sub_sq_le_cesaro

/-- info: 'MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq

/-- info: 'MeasureTheory.HasCorrelationDecay.of_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.HasCorrelationDecay.of_measurePreserving

-- E5(a) (2026-08-23, Mathlib/Dynamics/CorrelationDecayWitness.lean): the NON-VACUITY witness.
-- E4 is a conditional, so somebody must show its antecedent is satisfiable at all.
-- WHY THE WITNESS LOOKS LIKE THIS, and it is forced: a summable envelope makes the correlations
-- converge to <f>^2, so eps cannot be chosen large enough to cheat; and
-- integral_mul_self_eq_of_periodic says a PERIODIC map forces <f^2> = <f>^2. Every
-- measure-preserving map of a finite or countable probability space is periodic on its support,
-- so no atomic space carries a witness -- a genuine one needs a NON-ATOMIC space and a
-- non-periodic map. The doubling map on R/Z is the minimal such object.
-- Every correlation is computed by the Q24 SIGN-FLIP argument, not by integration: rotating by
-- 2^-(s+1) sends 2^s x to 2^s x + 1/2 (so circObs, being odd under the half-turn, flips) while
-- sending 2^t x to 2^t x + an INTEGER (so it is fixed) whenever s < t.  <circObs^2> = 1/2 comes
-- from the quarter-turn exchanging real and imaginary parts -- Q24's phaseFlip move.
-- circ_nontrivial is what makes this a certificate rather than a restatement of "constants have
-- no correlations"; doubling_not_periodic cross-checks the witness against the no-go.
-- SCOPE: this witnesses the ENGINE, not CSD. Periodic Sigma-flows provably CANNOT satisfy the
-- antecedent (CSD.Thermo.not_hasCorrelationDecay_blockPop_of_periodic).
/-- info: 'MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_periodic

/-- info: 'MeasureTheory.circ_hasCorrelationDecay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.circ_hasCorrelationDecay

/-- info: 'MeasureTheory.integral_circObs_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.integral_circObs_sq

/-- info: 'MeasureTheory.circ_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.circ_nontrivial

/-- info: 'MeasureTheory.doubling_not_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.doubling_not_periodic

-- The almost-periodicity route (2026-08-23), two of its three pieces.
-- integral_mul_self_eq_of_recurrent GENERALISES the periodic no-go: what actually kills decay is
-- that the correlation RETURNS near its lag-zero value at arbitrarily large lags.  The periodic
-- case is now a corollary (it returns exactly).  Three-term triangle inequality, nothing more.
-- exists_le_pow_mem_of_compactSpace is the classical pigeonhole behind almost periodicity: in a
-- compact topological group the powers of any element return to EVERY neighbourhood of 1 at
-- arbitrarily large exponents (cluster point of U^n, then continuity of (x,y) |-> y * x^-1 at
-- (g,g), then two exponents far apart; powers of one element commute so the quotient IS U^(j-i)).
-- Matrix.unitaryGroup IS a compact topological group (UnitaryGroup.instCompactSpace -- a wall
-- label that had rotted; an earlier grep missed it).
-- STILL MISSING, and it is the only gap left in the general statement: the uniform estimate
-- |f (V . p) - f p| <= c * sqrt (dev V) transferring group recurrence to the correlation.
-- Uniform rather than dominated-convergence because FirstCountableTopology does NOT synthesize
-- for Matrix.unitaryGroup, so continuous_of_dominated is unavailable.  Queued in BACKLOG.
/-- info: 'MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_recurrent

/-- info: 'exists_le_pow_mem_of_compactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_le_pow_mem_of_compactSpace

-- Q12-b (2026-08-23, Mathlib/Probability/CompetingExponentials.lean): the ORDER-FREE Born
-- partition.  RecordLayer's cdfCell reproduces Born by stacking intervals in INDEX ORDER;
-- record-layer-plan.md §3b asks instead for the symmetric race, in which no outcome is
-- privileged.  measure_raceCell: for independent exponential clocks at rates b, clock i fires
-- first with probability b_i / sum_j b_j; measure_raceCell_of_sum_eq_one specialises to a
-- probability vector.  Proof route: split coordinate i off the product
-- (measurePreserving_piFinSuccAbove), read the remaining clocks' survival as a BOX
-- (Measure.pi_pi on Set.pi univ (Ioi t)), then integrate e^{-St} against clock i.
-- lintegral_exp_neg_expMeasure evaluates NO improper integral: the integrand times the Exp r
-- density is a constant multiple of the Exp (r+S) density, whose mass is one.
-- ⚠️ TWO FINDINGS.  (1) The race does NOT fit RecordLayer.DeIsolationInteraction, whose pointer
-- is ℝ → Fin n (a ONE-dimensional fibre) while the race needs Fin (n+1) → ℝ; §3b says the minimal
-- fibre dimension is n-1, so the existing interface is committed to the ordered construction and
-- would have to be generalised.  cdfDeIsolationInteraction (Q12-a) remains the only instance.
-- (2) Strictly positive rates only -- an exponential clock needs r > 0, so a zero amplitude
-- (a clock that never fires) is outside expMeasure's domain.
/-- info: 'ProbabilityTheory.measure_raceCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.measure_raceCell

/-- info: 'ProbabilityTheory.measure_raceCell_of_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.measure_raceCell_of_sum_eq_one

/-- info: 'ProbabilityTheory.raceCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.raceCell_pairwiseDisjoint

-- Q12-d ROUTE 2 (2026-08-23): the FINITE-HORIZON antecedent, which E6 does not reach.
-- HasCorrelationDecayUpTo bounds the correlations only on lags BELOW T.  E6
-- (not_hasCorrelationDecay_blockPop_of_unitary) kills the asymptotic antecedent for every unitary
-- flow -- its powers recur, so the correlations recur -- but that argument needs the bound at
-- ARBITRARILY LARGE lags and says nothing over a bounded window.  A unitary flow on a large space
-- can decorrelate for a very long time before recurring, which is what a physical environment
-- does, and the finite-horizon estimate is exactly what survives.
-- The weakening was nearly free: hdec was only ever applied at s, t in Finset.range T, so binding
-- the membership hypotheses (previously discarded) sufficed.  HasCorrelationDecay.upTo makes the
-- asymptotic theorems corollaries, so nothing downstream changed.
-- ⚠️ STILL CONDITIONAL AND STILL NOT EXHIBITED: nothing shows any particular Sigma-flow has small
-- eps on lags below T.  What changed is that the hypothesis is no longer PROVABLY UNSATISFIABLE,
-- which is what E6 established for the asymptotic version.  Q12-d as originally scoped -- derive
-- the race from a MIXING flow -- remains blocked (specs/q12-fibre-mechanism-scoping.md, W1).
/-- info: 'MeasureTheory.integral_birkhoffAverage_sub_sq_le_cesaro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.integral_birkhoffAverage_sub_sq_le_cesaro

/-- info: 'MeasureTheory.HasCorrelationDecay.upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.HasCorrelationDecay.upTo

-- Q12-c2 step 3 (2026-08-23, Mathlib/MeasureTheory/MomentDeterminacy.lean): HAUSDORFF MOMENT
-- DETERMINACY on a compact interval -- two finite Borel measures with the same moment sequence are
-- equal.  Mathlib provisions both halves (polynomialFunctions_closure_eq_top and
-- ext_of_forall_integral_eq_of_IsFiniteMeasure) but does not state the conclusion.
-- This is the key assembly named by specs/q12c-exponential-characterisation-route.md: that memo
-- turns the race property into a moment sequence on [0,1] via the k-CLOCK family, and determinacy
-- is what converts it back into a distributional identity.
-- Proof is elementary: equal moments give equal integrals of polynomials by linearity; polynomials
-- are uniformly dense; the integral against a finite measure is sup-norm-Lipschitz; so equality
-- passes to every continuous function and then to the measures.  A three-term triangle inequality,
-- no functional-analytic packaging.
-- ⚠️ This is ONE STEP of Q12-c2, not Q12-c2.  §3c's "the exponential fibre measure is FORCED"
-- remains unproved in the corpus; the remaining chain (the general iid-clock race, the probability
-- integral transform, and monotone-equal-in-law) is mapped in the route memo.
/-- info: 'MeasureTheory.ext_of_forall_integral_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.ext_of_forall_integral_pow_eq

end CSD.Tests.AxiomAudit
