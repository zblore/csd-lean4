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

-- ChannelComp (2026-09-11, W5): channels compose, index-generic, with the composed action.
/-- info: 'QuantumInfo.Channel.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.comp

/-- info: 'QuantumInfo.Channel.comp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.comp_apply

-- PureState (2026-09-11, W4): zero von Neumann entropy characterises pure states (the converse of
-- vonNeumannEntropy_eq_zero_of_pure): eigenvalues in [0,1] summing to one with vanishing negMulLog
-- terms are {0,1}-valued with exactly one 1; the spectral theorem in projector form finishes it.
/-- info: 'QuantumInfo.negMulLog_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.negMulLog_eq_zero_iff

/-- info: 'QuantumInfo.isHermitian_eq_sum_eigenvalues_smul_vecMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.isHermitian_eq_sum_eigenvalues_smul_vecMulVec

/-- info: 'QuantumInfo.vonNeumannEntropy_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.vonNeumannEntropy_eq_zero_iff

-- Concavity (2026-09-11, W8): S(sum p_i rho_i) >= sum p_i S(rho_i) under Klein's full-support
-- condition on the mixture, via S(sigma) - sum p_i S(rho_i) = sum p_i D(rho_i || sigma) >= 0;
-- the Holevo quantity and its non-negativity.
/-- info: 'QuantumInfo.vonNeumannEntropy_congr_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.vonNeumannEntropy_congr_of_eq

/-- info: 'QuantumInfo.re_trace_self_log_eq_neg_vonNeumannEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.re_trace_self_log_eq_neg_vonNeumannEntropy

/-- info: 'QuantumInfo.re_trace_finset_sum_smul_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.re_trace_finset_sum_smul_mul

/-- info: 'QuantumInfo.vonNeumannEntropy_mixture_ge_of_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.vonNeumannEntropy_mixture_ge_of_posDef

/-- info: 'QuantumInfo.holevoChi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoChi

/-- info: 'QuantumInfo.holevoChi_nonneg_of_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoChi_nonneg_of_posDef

-- HolevoBound (2026-09-11, W10): mixtures of density matrices are density matrices; the Holevo
-- bound chi <= S(average) <= log dim (no support hypothesis); the single-letter Holevo range of a
-- channel and its log-dim bound.
/-- info: 'QuantumInfo.isHermitian_finset_sum_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.isHermitian_finset_sum_smul

/-- info: 'QuantumInfo.posSemidef_finset_sum_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.posSemidef_finset_sum_smul

/-- info: 'QuantumInfo.trace_finset_sum_smul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.trace_finset_sum_smul_eq_one

/-- info: 'QuantumInfo.holevoChi_le_vonNeumannEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoChi_le_vonNeumannEntropy

/-- info: 'QuantumInfo.holevoChi_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoChi_le_log_card

/-- info: 'QuantumInfo.holevoRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoRange

/-- info: 'QuantumInfo.holevoRange_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoRange_le_log_card

-- ConcavityFull (2026-09-11): the full-support hypothesis of concavity removed by mixing with the
-- maximally mixed state (explicit spectrum, vonNeumannEntropy_mixOne) and closedness in epsilon.
/-- info: 'QuantumInfo.mixOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.mixOne

/-- info: 'QuantumInfo.mixOne_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.mixOne_posDef

/-- info: 'QuantumInfo.sum_smul_mixOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.sum_smul_mixOne

/-- info: 'QuantumInfo.vonNeumannEntropy_mixOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.vonNeumannEntropy_mixOne

/-- info: 'QuantumInfo.vonNeumannEntropy_mixture_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.vonNeumannEntropy_mixture_ge

/-- info: 'QuantumInfo.holevoChi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.holevoChi_nonneg

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
-- (RecordLayer/ApproxProjectability.lean, not yet written).
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

-- The named CP witness (stated 2026-08-30, audit pass): for every idle factor b, the
-- local channel Phi (x) id_b is positive -- complete positivity as a theorem, immediate
-- from tensorRight being a Channel + apply_posSemidef. Closes the "open upstream-prep
-- work" item Channel.lean's C1 header carried since 2026-06-05.
/-- info: 'QuantumInfo.Channel.tensorRight_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.tensorRight_posSemidef

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

/-! ### Broadcasting: BCFJS BC1-BC2 (Mathlib/QuantumInfo/Broadcasting.lean, 2026-09-12) -/

-- Channel.Broadcasts Phi rho: both marginals of Phi rho are rho. Support confinement
-- (P (x) P) K_i rho = K_i rho for a projector P with P rho = rho; the classical copier in an
-- orthonormal basis broadcasts everything diagonal in it; commuting Hermitian matrices have a
-- joint eigenbasis (Mathlib's joint eigenspaces restricted to the finite eigenvalue pairs), so
-- they can be broadcast (the easy half of BCFJS); two broadcast pure states are orthogonal or
-- parallel (the rank-one case of the hard half: no-cloning at channel level). The partial-trace
-- module laws over I (x) X are the traceLeft twins of the traceRight ones above.

/-- info: 'Matrix.traceLeft_one_kronecker_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_one_kronecker_mul

/-- info: 'Matrix.traceLeft_mul_one_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_mul_one_kronecker

/-- info: 'Matrix.traceRight_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceRight_sum

/-- info: 'Matrix.traceLeft_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_sub

/-- info: 'QuantumInfo.Channel.Broadcasts.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.sub

/-- info: 'Matrix.PosSemidef.mul_mul_conjTranspose_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mul_mul_conjTranspose_eq_zero_iff

/-- info: 'Matrix.PosSemidef.eq_zero_of_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.eq_zero_of_sum_eq_zero

/-- info: 'QuantumInfo.Channel.Broadcasts.kronecker_one_mul_kraus_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.kronecker_one_mul_kraus_mul

/-- info: 'QuantumInfo.Channel.Broadcasts.one_kronecker_mul_kraus_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.one_kronecker_mul_kraus_mul

/-- info: 'QuantumInfo.Channel.Broadcasts.kronecker_mul_kraus_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.kronecker_mul_kraus_mul

/-- info: 'QuantumInfo.sum_onbProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sum_onbProj

/-- info: 'QuantumInfo.copierChannel_broadcasts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.copierChannel_broadcasts

/-- info: 'QuantumInfo.exists_orthonormalBasis_mulVec_eq_smul_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_orthonormalBasis_mulVec_eq_smul_of_commute

/-- info: 'QuantumInfo.exists_channel_broadcasts_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_channel_broadcasts_of_commute

/-- info: 'QuantumInfo.Channel.Broadcasts.kraus_mulVec_eq_smul_kronVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.kraus_mulVec_eq_smul_kronVec

/-- info: 'QuantumInfo.Channel.star_dotProduct_eq_sum_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.star_dotProduct_eq_sum_kraus

/-- info: 'QuantumInfo.norm_star_dotProduct_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.norm_star_dotProduct_sq_le

/-- info: 'QuantumInfo.Channel.Broadcasts.star_dotProduct_eq_zero_or_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.star_dotProduct_eq_zero_or_norm_eq_one

-- BC3 (2026-09-13): broadcast states with disjoint supports have orthogonal supports. The
-- support projector suppProj A (starProjection onto the range, as a matrix), the top eigenvalue
-- of a Hermitian matrix with its attaining unit eigenvector, the projector contraction with its
-- equality case, the tensor bound <x|Q (x) Q|x> <= mu^2 |x|^2, and the mu <= mu sqrt(mu) squeeze
-- through support confinement and trace preservation. BC2 is the rank-one case.

/-- info: 'QuantumInfo.suppProj_mulVec_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.suppProj_mulVec_eq_self_iff

/-- info: 'QuantumInfo.suppProj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.suppProj_mul_self

/-- info: 'QuantumInfo.suppProj_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.suppProj_isHermitian

/-- info: 'QuantumInfo.suppProj_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.suppProj_mul

/-- info: 'QuantumInfo.mul_suppProj_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.mul_suppProj_of_isHermitian

/-- info: 'QuantumInfo.nsq_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.nsq_eq_zero_iff

/-- info: 'QuantumInfo.nsq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.nsq_mulVec

/-- info: 'QuantumInfo.star_dotProduct_onbProj_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.star_dotProduct_onbProj_mulVec

/-- info: 'QuantumInfo.IsHermitian.exists_top_eigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.IsHermitian.exists_top_eigenvalue

/-- info: 'QuantumInfo.posSemidef_of_isHermitian_of_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.posSemidef_of_isHermitian_of_re_nonneg

/-- info: 'QuantumInfo.nsq_proj_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.nsq_proj_mulVec_le

/-- info: 'QuantumInfo.proj_mulVec_eq_self_of_nsq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.proj_mulVec_eq_self_of_nsq_eq

/-- info: 'QuantumInfo.re_star_dotProduct_kronecker_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_star_dotProduct_kronecker_mulVec_le

/-- info: 'QuantumInfo.Channel.sum_nsq_kraus_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.sum_nsq_kraus_mulVec

/-- info: 'QuantumInfo.Channel.Broadcasts.mul_eq_zero_of_range_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.mul_eq_zero_of_range_disjoint

-- BC4-BC5 (2026-09-13): a cloned subspace V of the support of a broadcast state splits it into
-- V- and (supp - V)-blocks, each broadcast (the dual Phi^dagger(P_V (x) 1) fixes V and its excess
-- over P_V is PSD with zero trace against tau; the cross blocks are sandwiched between
-- P_V (x) P_V and P_W (x) P_W, whose partial traces vanish since P_W P_V = 0); and the segment
-- through two distinct trace-one states meets the boundary of the PSD cone at a state with a
-- kernel vector outside ker(rho + sigma) (closed bounded set of admissible l, its supremum, and a
-- perturbation through the eigen-expansion). The partial-trace cyclicity in the traced factor
-- lives in PartialTrace.lean.

/-- info: 'Matrix.traceRight_one_kronecker_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceRight_one_kronecker_mul_comm

/-- info: 'Matrix.traceLeft_kronecker_one_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_kronecker_one_mul_comm

/-- info: 'Matrix.PosSemidef.mul_eq_zero_of_trace_mul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mul_eq_zero_of_trace_mul_eq_zero

/-- info: 'QuantumInfo.Channel.star_dotProduct_adjoint_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.star_dotProduct_adjoint_mulVec

/-- info: 'QuantumInfo.Channel.adjoint_kronecker_one_mulVec_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_kronecker_one_mulVec_eq_self

/-- info: 'QuantumInfo.Channel.adjoint_one_kronecker_mulVec_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_one_kronecker_mulVec_eq_self

/-- info: 'QuantumInfo.Channel.Broadcasts.kronecker_mulVec_kraus_mulVec_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.kronecker_mulVec_kraus_mulVec_sub

/-- info: 'QuantumInfo.traceRight_kronecker_mul_mul_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceRight_kronecker_mul_mul_kronecker

/-- info: 'QuantumInfo.traceLeft_kronecker_mul_mul_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceLeft_kronecker_mul_mul_kronecker

/-- info: 'QuantumInfo.kraus_block_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.kraus_block_sandwich

/-- info: 'QuantumInfo.Channel.Broadcasts.block_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.block_split

/-- info: 'QuantumInfo.nsq_eq_sum_onb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.nsq_eq_sum_onb

/-- info: 'QuantumInfo.re_star_dotProduct_mulVec_eq_sum_onb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_star_dotProduct_mulVec_eq_sum_onb

/-- info: 'QuantumInfo.onbProjSet_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.onbProjSet_mul_self

/-- info: 'QuantumInfo.star_dotProduct_onbProjSet_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.star_dotProduct_onbProjSet_mulVec

/-- info: 'QuantumInfo.exists_re_star_dotProduct_neg_of_trace_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_re_star_dotProduct_neg_of_trace_eq_zero

/-- info: 'QuantumInfo.exists_boundary_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_boundary_point

-- BC6 (2026-09-13): the BCFJS theorem. Broadcast PSD matrices commute, by strong induction on
-- rank(rho + sigma): normalise, take the two boundary points of the segment (BC5), intersect
-- their supports with interProj (1 - suppProj((1 - P_1) + (1 - P_2))); V = 0 is BC3, V /= 0 is
-- cloned by every Kraus operator (intersections of tensor squares), BC4 splits both boundary
-- states, the block pairs have strictly smaller rank of the sum (rank_lt_rank_of_ker: a strict
-- kernel inclusion is a strict rank inequality) and commute by induction, the cross products
-- vanish. With BC1: exists_channel_broadcasts_iff_commute.

/-- info: 'QuantumInfo.suppProj_mulVec_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.suppProj_mulVec_eq_zero_iff

/-- info: 'Matrix.PosSemidef.add_mulVec_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.add_mulVec_eq_zero_iff

/-- info: 'QuantumInfo.smul_mulVec_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.smul_mulVec_eq_zero_iff

/-- info: 'QuantumInfo.rank_lt_rank_of_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.rank_lt_rank_of_ker

/-- info: 'QuantumInfo.one_sub_proj_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.one_sub_proj_posSemidef

/-- info: 'QuantumInfo.interProj_mulVec_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.interProj_mulVec_eq_self_iff

/-- info: 'QuantumInfo.mul_interProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.mul_interProj

/-- info: 'QuantumInfo.interProj_kronecker_mulVec_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.interProj_kronecker_mulVec_eq_self

/-- info: 'Matrix.PosSemidef.exists_smul_trace_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.exists_smul_trace_one

/-- info: 'QuantumInfo.Channel.Broadcasts.mul_comm_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.Broadcasts.mul_comm_of_posSemidef

/-- info: 'QuantumInfo.exists_channel_broadcasts_iff_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_channel_broadcasts_iff_commute

-- BCFJS for finite families (2026-09-13): a joint eigenbasis of a pairwise-commuting family
-- (iSup_iInf_eq_top_of_commute restricted to the finite joint eigenvalue functions), the copier,
-- and the pair theorem applied pairwise.

/-- info: 'QuantumInfo.exists_orthonormalBasis_mulVec_eq_smul_of_pairwise_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_orthonormalBasis_mulVec_eq_smul_of_pairwise_commute

/-- info: 'QuantumInfo.exists_channel_broadcasts_of_pairwise_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_channel_broadcasts_of_pairwise_commute

/-- info: 'QuantumInfo.exists_channel_broadcasts_family_iff_pairwise_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_channel_broadcasts_family_iff_pairwise_commute

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

-- K1-B.1 (specs/k1-plan.md): matrix partial trace (Mathlib has none; MATHLIB-ABSENT(Matrix.partialTrace)). Load-bearing results:
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

-- Kronecker factor embeddings as algebra homs (2026-09-02, Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom.lean;
-- Mathlib has kroneckerAlgEquiv but no bundled A ↦ A ⊗ₖ 1 / B ↦ 1 ⊗ₖ B): kroneckerLeftAlgHom /
-- kroneckerRightAlgHom (kroneckerAlgEquiv ∘ includeLeft / includeRight), their commutation, star-preservation,
-- and GENERATION (adjoin_range_kroneckerLeftAlgHom_union_eq_top) via the matrix-unit criterion
-- Subalgebra.eq_top_of_forall_single_mem (a subalgebra containing every single i j 1 is ⊤ -- stdBasis spans).
-- Consumed by CV/CompositeArena.lean (leftHom / rightHom, composite_generate) and
-- SigmaLayer/TensorTomography.lean (aliceHom / bobHom). Foundational triple.
/-- info: 'Subalgebra.eq_top_of_forall_single_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Subalgebra.eq_top_of_forall_single_mem

/-- info: 'Matrix.kroneckerLeftAlgHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.kroneckerLeftAlgHom

/-- info: 'Matrix.commute_kroneckerLeftAlgHom_kroneckerRightAlgHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.commute_kroneckerLeftAlgHom_kroneckerRightAlgHom

/-- info: 'Matrix.kroneckerLeftAlgHom_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.kroneckerLeftAlgHom_star

/-- info: 'Matrix.adjoin_range_kroneckerLeftAlgHom_union_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.adjoin_range_kroneckerLeftAlgHom_union_eq_top

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

-- Quantum phase estimation (Mathlib/QuantumInfo/PhaseEstimation.lean, relocated from
-- Empirical/QM/Algorithms/ShorCore.lean 2026-08-29 — entirely generic in the register size T,
-- no statement changed, no new mathematics). The exact case: the inverse QFT inverts the QFT
-- (applyQFTinv_phaseColumn), so a QFT column is read with certainty (phase_estimation_exact).
-- The general case (Nielsen-Chuang 5.2): for an ARBITRARY real phase φ read at the closest
-- counting index c (|φ - c/T| ≤ 1/(2T)), the probability is ≥ 4/π²
-- (phase_estimation_lower_bound) — the Dirichlet amplitude (applyQFTinv_phaseStateR_apply)
-- closed by geom_sum_eq, reduced to a sine ratio (prob_phaseStateR_eq) via
-- Complex.norm_exp_I_mul_ofReal_sub_one, bounded by the Jordan inequality
-- Real.mul_abs_le_abs_sin against |sin t| ≤ |t|. Single-phase statement only: a consumer
-- racing several eigenvalue branches controls its own cross-terms (ShorCore documents the
-- deferred two-register marginal). Foundational triple.
/-- info: 'QuantumInfo.phase_estimation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.phase_estimation_exact

/-- info: 'QuantumInfo.phase_estimation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.phase_estimation_lower_bound

-- Amplitude amplification, BHMT (Mathlib/QuantumInfo/AmplitudeAmplification.lean, 2026-08-29;
-- specs/amplitude-amplification-plan.md AA-1..AA-3). The theorem Grover's algorithm is an
-- instance of, generic in the register basis and the good set: the amplification step
-- reflect(phi) . oracleFlip(G) acts on the good/bad plane as a rotation by 2*theta
-- (ampStep_ampState, the two-reflection heart), so j rounds give success EXACTLY
-- sin^2((2j+1) arcsin sqrt(a)) (amplitude_amplification, closed form, no asymptotics; hypotheses
-- 0 < a < 1 are the honest degenerate boundary). floor(pi/(4 theta)) rounds succeed with
-- probability >= 1 - a (amplitude_amplification_succeeds -- the bound Grover analyses defer),
-- and the round count is <= pi/(4 sqrt a) (amplification_query_bound, the quadratic speedup,
-- via sqrt a = sin theta <= theta). Round counting is abstract-step counting; no oracle model or
-- gate decomposition claimed. Grover.lean re-derives its headline from this module and gains the
-- k-marked instance. Foundational triple.
/-- info: 'QuantumInfo.ampStep_ampState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ampStep_ampState

/-- info: 'QuantumInfo.amplitude_amplification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_amplification

/-- info: 'QuantumInfo.amplitude_amplification_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_amplification_succeeds

/-- info: 'QuantumInfo.amplification_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplification_query_bound

-- AA-5a (2026-08-29, same file): the eigenstructure of the amplification step and the
-- estimate's error algebra -- the two halves of amplitude ESTIMATION (BHMT Thm 12) that need
-- no two-register tensor plumbing. On the rotation plane the step has eigenvectors g +- i*b
-- with eigenvalues e^{+-2i*theta} (ampStep_eigenPlus/eigenMinus, via the newly-proved
-- linearity of the step), so j rounds scale the + eigenvector by e^{2ij*theta}
-- (ampStep_iterate_eigenPlus) -- the phase a counting register would estimate. And the error
-- propagation: an angle estimate within eps of theta gives an amplitude estimate within
-- 2*sqrt(a(1-a))*eps + eps^2 of a = sin^2 theta (amplitude_estimation_error, BHMT Lemma 7,
-- via sin^2 x - sin^2 y = sin(x+y) sin(x-y) and the Lipschitz bound on sin). The remaining
-- half -- the kickback state's counting marginal and the 8/pi^2 assembly -- is AA-5b in the
-- plan, gated on generalizing the Shor two-register tensor infrastructure. Foundational triple.
/-- info: 'QuantumInfo.ampStep_eigenPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ampStep_eigenPlus

/-- info: 'QuantumInfo.ampStep_iterate_eigenPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ampStep_iterate_eigenPlus

/-- info: 'QuantumInfo.amplitude_estimation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_error

-- The two-factor joint register (Mathlib/QuantumInfo/JointRegister.lean, 2026-08-29; plan
-- AA-5b step 1). The generic tensor/partial-operator/marginal layer every two-register
-- algorithm argument consumes, extracted from ShorCore's Fin T x ZMod N originals (now
-- delegating instances): tensorState (product state), matrixLeft (a matrix kernel on the
-- first factor -- "inverse QFT on the counting register" is the instance), sliceLeft, and
-- probLeft (the Born marginal on the first register). Headlines: matrixLeft_tensorState (a
-- first-factor kernel acts through the tensor) and -- the load-bearing new fact --
-- probLeft_sum_tensor_orthogonal: for a sum of product states with PAIRWISE-ORTHOGONAL second
-- factors, the first-register marginal is the MIXTURE of branch marginals, every cross-term
-- dead. This is what turns a multi-branch kickback state into a classical mixture of
-- single-phase counting distributions (the 8/pi^2 assembly of AA-5b consumes it; Shor's
-- deferred r-not-dividing-T marginal is its other customer). Foundational triple.
/-- info: 'QuantumInfo.matrixLeft_tensorState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.matrixLeft_tensorState

/-- info: 'QuantumInfo.probLeft_sum_tensor_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.probLeft_sum_tensor_orthogonal

-- Amplitude ESTIMATION, BHMT Thm 12 (Mathlib/QuantumInfo/AmplitudeEstimation.lean,
-- 2026-08-29; plan AA-5b assembly -- the module where all three prepared layers meet: the
-- eigenstructure of the amplification step, the joint-register mixture law, and the 4/pi^2
-- phase-estimation bound). kickbackState (1/sqrt T) sum_x |x> tensor Q^x psi is proved to be
-- EXACTLY the two-branch phase form c+ (phaseStateR(theta/pi)) tensor v+ + c- (...) tensor v-
-- (kickbackState_ampState, |c+-| = 1/2, orthogonal eigenvector companions), so the counting
-- marginal after the partial inverse QFT is EXACTLY the half-half mixture of the two
-- single-phase distributions (amplitude_estimation_marginal -- an equality, not a bound).
-- Headlines: amplitude_estimation -- at any index in the closest-index window of theta/pi the
-- marginal carries >= 2/pi^2 (the + branch's 4/pi^2, halved by the branch weight; the -
-- branch kept only as >= 0) -- and amplitude_estimation_close: any such index yields the
-- estimate sin^2(pi c/T) within pi sqrt(a(1-a))/T + pi^2/(4T^2) of a (BHMT Lemma 7 at
-- eps = pi/(2T); sharper than the paper's pi/T constant). MIRROR REFINEMENT (2026-08-29,
-- same day): the - branch's distribution is the exact mirror image of the + branch's
-- (prob_applyQFTinv_phaseStateR_neg, a conjugation symmetry), the mirror index -c decodes to
-- the SAME estimate (sin_sq_mirror), and the pair {c, -c} jointly carries >= 4/pi^2
-- (amplitude_estimation_pair; degenerate c = -c double-count noted in the docstring).
-- HONEST SCOPE, CORRECTED: the earlier note here called the full 8/pi^2 "downstream
-- arithmetic" -- WRONG for the both-rounding half: it needs a two-index lower bound on the
-- Dirichlet kernel (a single index at distance up to 1/T can carry probability 0), a genuine
-- new kernel inequality, recorded in the plan as R-001 and PROVED 2026-09-23 (the block after
-- the pair pin below). No controlled-gate decomposition claimed. Foundational triple.
/-- info: 'QuantumInfo.prob_applyQFTinv_phaseStateR_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.prob_applyQFTinv_phaseStateR_neg

/-- info: 'QuantumInfo.amplitude_estimation_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_pair

-- 2026-09-23, R-001 DISCHARGED (BACKLOG #12): the two-index Dirichlet bound and BHMT Thm 11
-- (k = 1) with the paper's literal constants. PhaseEstimation.lean: the kernel inequality
-- sin^2(pi x)(x^2 + (1-x)^2) >= 8 (x(1-x))^2 on (0,1) (eight_mul_sq_le_sin_sq_pi_mul; by
-- symmetry on (0, 1/2], split at 1/4: sin t >= t - t^3/6 below, cos t >= 1 - t^2/2 at
-- t = pi(1/2 - x) above, polynomial estimates with 3.1415 < pi < 3.1416); the phase state is
-- 1-periodic (phaseStateR_add_one) and reading index c is reading index 0 at phase phi - c/T
-- (prob_applyQFTinv_phaseStateR_sub); dirichlet_two_index: f(delta) + f(delta - 1/T) >= 8/pi^2
-- for 0 <= delta <= 1/T; phase_estimation_two_index: the indices c and c + 1 (mod T) carry
-- >= 8/pi^2 when 0 <= phi - c/T <= 1/T; exists_straddle_index. AmplitudeEstimation.lean:
-- straddleIndices T c = {c, c+1, -c, -(c+1)} (a Finset, so coincidences merge);
-- amplitude_estimation_straddle (>= 8/pi^2 on it, each branch through the two-index bound,
-- the - branch via the mirror), amplitude_estimation_straddle_close (every accepted index
-- decodes within 2 pi sqrt(a(1-a))/T + pi^2/T^2, the wrap c = T-1 -> 0 decoding to
-- sin^2(0) = sin^2(pi)), amplitude_estimation_bhmt (the conjunction). Foundational triple.
/-- info: 'QuantumInfo.eight_mul_sq_le_sin_sq_pi_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.eight_mul_sq_le_sin_sq_pi_mul

/-- info: 'QuantumInfo.phaseStateR_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.phaseStateR_add_one

/-- info: 'QuantumInfo.dirichlet_two_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.dirichlet_two_index

/-- info: 'QuantumInfo.phase_estimation_two_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.phase_estimation_two_index

/-- info: 'QuantumInfo.exists_straddle_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_straddle_index

/-- info: 'QuantumInfo.straddleIndices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.straddleIndices

/-- info: 'QuantumInfo.amplitude_estimation_straddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_straddle

/-- info: 'QuantumInfo.amplitude_estimation_straddle_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_straddle_close

/-- info: 'QuantumInfo.amplitude_estimation_bhmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_bhmt

-- QSearch engine, BHMT Lemma 2 (AmplitudeAmplification.lean final section, 2026-08-29; plan
-- AA-6 in engine form). When a is UNKNOWN the optimal count cannot be computed; BHMT's
-- remedy is a uniformly random round count below a guess M. The odd-angle sin^2 sum
-- telescopes to an exact closed form (sum_sin_sq_odd_mul, product form, no division), and
-- once M sin(2 theta) >= 1 the average success probability is >= 1/4 independent of a
-- (sum_sin_sq_odd_ge); on the register: qsearch_average -- for any unit state with unknown
-- 0 < a < 1 and M with M * 2 sqrt(a(1-a)) >= 1, the rounds 0..M-1 have total success
-- probability >= M/4. The exponential-doubling schedule wrapping this (BHMT Thm 3, expected
-- O(1/sqrt a) total) was recorded as R-002 and is QSearch.lean, pinned right below
-- (discharged 2026-09-23). Foundational triple.
/-- info: 'QuantumInfo.qsearch_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.qsearch_average

-- 2026-09-23, R-002 DISCHARGED (BACKLOG #13): Mathlib/QuantumInfo/QSearch.lean, BHMT Thm 3
-- (the upper bound). The schedule qsearchGuess l = ceil((6/5)^l); the stage law stageProbAt
-- (direct measurement of psi, else a fresh copy amplified j rounds: a + (1-a) sin^2((2j+1)
-- theta)) and its average stageProb over uniform j < M, >= 1/4 once M sin(2 theta) >= 1
-- (quarter_le_stageProb, from qsearch_average) and >= a always (le_stageProb). The run as a
-- random process: QSearchRun bundles, on a probability space, the round counts J l and the
-- successes W l with iIndepFun across stages, J l uniform below M l, and the Born law given
-- J l = j. The bookkeeping: reach l = every earlier stage failed, of probability
-- prod_{k<l} (1 - p_k) (meas_reach, iIndepFun.meas_biInter); the fresh draw is independent of
-- the past (meas_J_inter_reach), so a reached stage costs M_l + 1 in expectation
-- (lintegral_stageCost: 2 + 2j charged, j uniform has mean (M-1)/2); the expected cost is the
-- series (lintegral_cost, lintegral_tsum); past a critical stage the reach probabilities decay
-- like (3/4)^(l - l0) (meas_reach_le); the series is bounded by explicit geometric weights
-- (5/6)^(l0-l) before and (9/10)^(l-l0) after the critical stage (qsearch_partial_sum_le:
-- 45 (6/5)^l0). Headline QSearchRun.qsearch_expected_cost: for 0 < a < 1 the expected number
-- of applications is <= 54/sqrt(a) (a <= 3/4: the first stage with (6/5)^l0 > 1/sin(2 theta),
-- so (6/5)^l0 <= (6/5)/sin(2 theta) <= (6/5)/sqrt(a); a > 3/4: every stage succeeds with
-- probability > 3/4). exists_qsearchRun: the model is consistent -- Measure.infinitePi of the
-- stage laws stageMeasure carries a run (iIndepFun_infinitePi, infinitePi_map_eval).
-- HONEST SCOPE: the upper bound only (the Omega(1/sqrt a) is BBBV optimality, not here); the
-- stage cost 2 + 2j is an upper bound when the direct measurement already succeeds; the
-- constant 54 is not optimised. Foundational triple.
/-- info: 'QuantumInfo.qsearchGuess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.qsearchGuess

/-- info: 'QuantumInfo.stageProbAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stageProbAt

/-- info: 'QuantumInfo.stageProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stageProb

/-- info: 'QuantumInfo.quarter_le_stageProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.quarter_le_stageProb

/-- info: 'QuantumInfo.le_stageProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.le_stageProb

/-- info: 'QuantumInfo.QSearchRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun

/-- info: 'QuantumInfo.QSearchRun.meas_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.meas_reach

/-- info: 'QuantumInfo.QSearchRun.meas_J_inter_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.meas_J_inter_reach

/-- info: 'QuantumInfo.QSearchRun.meas_W_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.meas_W_true

/-- info: 'QuantumInfo.QSearchRun.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.cost

/-- info: 'QuantumInfo.QSearchRun.lintegral_stageCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.lintegral_stageCost

/-- info: 'QuantumInfo.QSearchRun.lintegral_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.lintegral_cost

/-- info: 'QuantumInfo.QSearchRun.meas_reach_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.meas_reach_le

/-- info: 'QuantumInfo.qsearch_partial_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.qsearch_partial_sum_le

/-- info: 'QuantumInfo.QSearchRun.lintegral_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.lintegral_cost_le

/-- info: 'QuantumInfo.QSearchRun.qsearch_expected_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.QSearchRun.qsearch_expected_cost

/-- info: 'QuantumInfo.stageMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stageMeasure

/-- info: 'QuantumInfo.exists_qsearchRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_qsearchRun

-- The Pauli/Clifford layer -- the Gottesman-Knill mechanism (Mathlib/QuantumInfo/Pauli.lean
-- + Clifford.lean, 2026-08-29; plan specs/gottesman-knill-plan.md, GK-1/GK-2; candidate 3 of
-- the 2026-08-28 five). Pauli.lean: X^a Z^b as concrete coordinate operators with the group
-- law X^a Z^b . X^a' Z^b' = (-1)^{b.a'} X^{a+a'} Z^{b+b'} (pauliOp_mul), commutation
-- governed by the F_2 symplectic form (pauliOp_comm), character orthogonality
-- sum_z (-1)^{b.z} = 2^n [b=0] hence non-identity Paulis traceless (pauliOp_trace -- the
-- seed of the stabiliser-uniqueness trace argument), and inner-product preservation.
-- Clifford.lean: the three generator families as coordinate operators, and the theorem
-- family that IS Gottesman-Knill -- conjugation by each generator maps every Pauli to a
-- phase times a Pauli with EXPLICIT F_2-linear label maps: CNOT (cnotGate_conj_pauliOp, no
-- phase), S (sGate_conj_pauliOp, phase i^{a_j} -- S X S+ = Y), H (hGate_conj_pauliOp, sign
-- (-1)^{a_j b_j}, swaps a_j <-> b_j). HONEST SCOPE: the Heisenberg-picture closure is
-- proved in full; the "classically simulable in polynomial time" reading is a complexity
-- claim about the update rule -- no computation model, no circuit datatype, no measurement
-- update (stabiliser layer = GK-3, gated in the plan). No priority claim of any kind
-- (CL-061 rule; the Coq/stabiliser landscape was not surveyed). Foundational triple.
/-- info: 'QuantumInfo.pauliOp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pauliOp_mul

/-- info: 'QuantumInfo.pauliOp_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pauliOp_comm

/-- info: 'QuantumInfo.pauliOp_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pauliOp_trace

/-- info: 'QuantumInfo.cnotGate_conj_pauliOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cnotGate_conj_pauliOp

/-- info: 'QuantumInfo.sGate_conj_pauliOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sGate_conj_pauliOp

/-- info: 'QuantumInfo.hGate_conj_pauliOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.hGate_conj_pauliOp

-- The stabiliser layer, GK-3 (Mathlib/QuantumInfo/Stabilizer.lean, 2026-08-29; plan
-- specs/gottesman-knill-plan.md). A stabiliser family indexed by F_2^m directly: linear
-- label maps A B and a sign function sigma under ONE coherence law
-- sigma(x+y) = sigma(x) + sigma(y) + B(x).A(y) -- exactly the condition that the signed
-- Paulis form a group (the pairing is pauliOp_mul's phase), i.e. "-I not in S"; coherence
-- at (x,y) and (y,x) IMPLIES the family is abelian (stab_symp_zero). Headlines: absorption
-- (every signed element fixes the group average; one reindex), idempotence (three lines
-- from absorption), the trace 2^n/2^m (the code-space dimension count; 1 for a full
-- stabiliser), and stabState_exists -- a nonzero state fixed by the average and by EVERY
-- group element, extracted from tr P != 0 + idempotence with no spectral machinery.
-- HONEST RESIDUES (named in the plan): uniqueness/dimension needs rank-equals-trace for
-- self-adjoint idempotents (spectral machinery not built); the measurement-update rule is
-- not attempted. Foundational triple.
/-- info: 'QuantumInfo.stabProjector_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stabProjector_idem

/-- info: 'QuantumInfo.stabProjector_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stabProjector_trace

/-- info: 'QuantumInfo.stabState_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stabState_exists

-- GK COMPLETION (2026-08-29, same file, later the same day): both residues named at the
-- GK-3 landing are DISCHARGED. (i) Rank/uniqueness: the group average is a genuine linear
-- projection (stabProjectorL, IsProj onto its range = the fixed space), so Mathlib's
-- rank-equals-trace for projections turns the trace count into finrank(fixed space) =
-- 2^(n-m) (stabProjector_rank) -- and for a full stabiliser the stabilised state is UNIQUE
-- up to scalar (stabState_unique). (ii) The measurement-update rule (measProj section):
-- measuring an involutive Pauli on a stabilised state -- deterministic outcome when the
-- signed observable is in the group (meas_deterministic); when it anticommutes with a group
-- element, the expectation vanishes (meas_expectation_zero) and both outcomes carry
-- probability EXACTLY 1/2 (meas_prob_half); the post-measurement branch is stabilised by
-- the signed observable itself (pauliOp_measProj) and by every commuting group element
-- (meas_update_fixes) -- the standard stabiliser update, operator-free. Foundational triple.
/-- info: 'QuantumInfo.stabProjector_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stabProjector_rank

/-- info: 'QuantumInfo.stabState_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.stabState_unique

/-- info: 'QuantumInfo.meas_prob_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.meas_prob_half

/-- info: 'QuantumInfo.meas_update_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.meas_update_fixes

-- The magic layer, candidate 5 of the 2026-08-28 five (Mathlib/QuantumInfo/Magic.lean,
-- 2026-08-29; plan specs/magic-plan.md). The precise complement of Gottesman-Knill: T^2 = S
-- (the hierarchy descends, tGate_tGate); the level-3 identity T X T+ = (X + i XZ)/sqrt 2
-- (tGate_conj_X -- out of the Pauli family, into its two-term span); and the NO-GO
-- tGate_conj_X_not_pauli: no c, a, b give T X T+ = c X^a Z^b -- pinning two basis columns
-- forces 1 = +-i. Together with the GK-2 closure this brackets the Clifford boundary from
-- both sides. The magic state |T> = T H |0> with closed coordinates and unit norm
-- (inner_magicState_self). HONEST SCOPE: distillation (Bravyi-Kitaev 15-to-1), universality
-- (gate-synthesis density), and the T-injection circuit are named residues in the plan, not
-- attempted. Foundational triple.
/-- info: 'QuantumInfo.tGate_conj_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.tGate_conj_X

/-- info: 'QuantumInfo.tGate_conj_X_not_pauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.tGate_conj_X_not_pauli

/-- info: 'QuantumInfo.inner_magicState_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.inner_magicState_self
/-- info: 'QuantumInfo.kickbackState_ampState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.kickbackState_ampState

/-- info: 'QuantumInfo.amplitude_estimation_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_marginal

/-- info: 'QuantumInfo.amplitude_estimation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation

/-- info: 'QuantumInfo.amplitude_estimation_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.amplitude_estimation_close

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

-- Mathlib pull request 1 (2026-09-19): the quotient topology on projective space, the
-- pull-request text verbatim. The unit-multiple criterion and the saturation lemma replace
-- this repository's own scaleNonzero reimplementation; the Kˣ-action on the nonzero vectors
-- is Mathlib's, and its continuity instance is staged in Topology/Algebra/MulAction.lean.
/-- info: 'Projectivization.mk'_eq_mk'_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.mk'_eq_mk'_iff

/-- info: 'Projectivization.preimage_image_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.preimage_image_mk'

/-- info: 'Projectivization.isQuotientMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.isQuotientMap_mk'

/-- info: 'SubMulAction.continuousConstSMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SubMulAction.continuousConstSMul

/-- info: 'Units.continuousConstSMul_nonZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Units.continuousConstSMul_nonZero

/-- info: 'Projectivization.instT2Space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instT2Space

/-- info: 'Projectivization.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instCompactSpace

-- Projectivization/MomentMap.lean (2026-09-16, moved from LF4/MomentMap.lean so that the manifold
-- tree's closure is Category 1): the coordinate moment map [z] ↦ ‖zᵢ‖²/‖z‖² on ℙ ℂ (ℂᴺ), its
-- simplex constraints, the squared-overlap identity at a unit vector, and regularity by descent
-- through mk'. CSD.LF4 re-exports the names; these are the constants the aliases resolve to.
/-- info: 'Projectivization.momentMap_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.momentMap_sum_eq_one

/-- info: 'Projectivization.momentMap_mk_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.momentMap_mk_eq_inner_sq

/-- info: 'Projectivization.momentMap_mk_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.momentMap_mk_of_norm_eq

/-- info: 'Projectivization.continuous_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_momentMap

/-- info: 'Projectivization.measurable_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.measurable_momentMap

-- Analysis/Matrix/SchrodingerUnitary.lean (2026-09-16, moved from LF4/ProjectedDynamics.lean and
-- LF4/ManyToOneSchrodingerDerived.lean so that the manifold Schrödinger flow is Category 1 by
-- closure): exp(-itH) is unitary for Hermitian H, a one-parameter group, and C¹ with derivative
-- U t · (-iH). CSD.LF4 re-exports the names.
/-- info: 'Matrix.schrodingerGen_exp_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.schrodingerGen_exp_mem_unitaryGroup

/-- info: 'Matrix.expNegITH_unitary_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.expNegITH_unitary_group

/-- info: 'Matrix.schrodingerUnitary_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.schrodingerUnitary_hasDerivAt

-- Analysis/InformationGeometry (2026-09-16, the Fubini–Study → Fisher–Rao bridge for Physlib
-- PR #1652). FisherRao.lean mirrors Nava-Hernandez's OpenSimplex / fisherRaoInner verbatim
-- (deleted when the PR merges); FubiniStudyFisherRao.lean is the vector-level bridge (and,
-- since the 2026-09-18 split, BraunsteinCaves.lean the inequality and the homogeneous
-- coordinates): along a
-- torus-horizontal direction u (every conj(ψ i) * u i real) the Fisher–Rao inner product of the
-- Born displacements is 4 Re ⟪u, v⟫ — constant ONE against the repo's fsMetric normalisation —
-- and the algebraic bound fisherInfo ≤ 4 ‖u‖² with equality iff torus-horizontal. Braunstein–Caves
-- proper (2026-09-16, after external review): along the projective horizontal lift the readout's
-- Fisher information is ≤ fsInnerHom ψ u u, the quantum Fisher information 4(‖u‖² − ‖⟪ψ,u⟫‖²)
-- for unit ψ, with equality iff the lift is torus-horizontal.
/-- info: 'FisherRao.OpenSimplex.fisherRao_cauchy_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.OpenSimplex.fisherRao_cauchy_schwarz

/-- info: 'FisherRao.fisherInfo_eq_fisherRaoSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherInfo_eq_fisherRaoSq

/-- info: 'FisherRao.hasFDerivAt_bornWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.hasFDerivAt_bornWeight

/-- info: 'FisherRao.sum_bornDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.sum_bornDeriv

/-- info: 'FisherRao.fisherRaoInner_bornDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherRaoInner_bornDeriv

/-- info: 'FisherRao.fisherRaoSq_bornDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherRaoSq_bornDeriv

/-- info: 'FisherRao.fisherInfo_bornDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherInfo_bornDeriv_le

/-- info: 'FisherRao.fisherInfo_bornDeriv_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherInfo_bornDeriv_eq_iff

-- Homogeneous coordinates (same file): the bridge at normalize ψ along horizontal lifts, and the
-- identification 4 Re ⟪hLift u, hLift v⟫ = fsInnerHom ψ u v.
/-- info: 'FisherRao.inner_horizontalLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.inner_horizontalLift

/-- info: 'FisherRao.fisherRaoInner_bornDeriv_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fisherRaoInner_bornDeriv_normalize

/-- info: 'FisherRao.fsInnerHom_self_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FisherRao.fsInnerHom_self_of_norm_eq_one

/-- info: 'FisherRao.fisherInfo_bornDeriv_horizontalLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FisherRao.fisherInfo_bornDeriv_horizontalLift_le

/-- info: 'FisherRao.fisherInfo_bornDeriv_horizontalLift_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FisherRao.fisherInfo_bornDeriv_horizontalLift_eq_iff

-- Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean (2026-09-16): the manifold bridge.
-- fsMetric at x IS the homogeneous Fubini–Study formula on the lifts to insertOne (idx x) w
-- (the recognition lemma), the moment map is differentiable with momentDeriv killing the torus
-- orbits and tangent to the simplex, horizontal = moduli-only in the chart, and ★★ on the regular
-- stratum fsMetric x u v = fisherRaoInner (toOpenSimplex x) (momentDeriv x u) (momentDeriv x v)
-- for u horizontal — constant ONE.
/-- info: 'Projectivization.fsMetric_eq_fsInnerHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.fsMetric_eq_fsInnerHom

/-- info: 'Projectivization.hasMFDerivAt_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.hasMFDerivAt_momentMap

/-- info: 'Projectivization.mfderiv_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mfderiv_momentMap

/-- info: 'Projectivization.sum_momentDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.sum_momentDeriv

/-- info: 'Projectivization.momentDeriv_eq_zero_of_mem_verticalSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.momentDeriv_eq_zero_of_mem_verticalSpace

/-- info: 'Projectivization.mem_horizontalSpace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mem_horizontalSpace_iff

/-- info: 'Projectivization.fsMetric_eq_fisherRaoInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.fsMetric_eq_fisherRaoInner

-- Injectivity on the horizontal space (2026-09-16, after external review): the bridge is an
-- isometric embedding into the zero-sum tangent space, not only a pairing identity.
/-- info: 'Projectivization.momentDeriv_eq_zero_iff_of_mem_horizontalSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.momentDeriv_eq_zero_iff_of_mem_horizontalSpace

/-- info: 'Projectivization.momentDeriv_injOn_horizontalSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.momentDeriv_injOn_horizontalSpace

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
-- volume and the ball), so its projectivization IS fsMeasure by the staged uniqueness
-- theorem. Payoff: the null-transport principle -- a ray set whose vector cone is Lebesgue-null
-- is Fubini-Study-null -- plus the elementary Fubini-slicing lemmas (coordinate hyperplanes and
-- the coordinate quadratic's zero set are null; NO polynomial-zero-set theory needed).
/-- info: 'Matrix.UnitaryGroup.pi_quadratic_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.pi_quadratic_null

/-- info: 'Matrix.UnitaryGroup.volume_ofLp_preimage_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.volume_ofLp_preimage_null

/-- info: 'Matrix.UnitaryGroup.map_ballMeasure_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.map_ballMeasure_eq_fubiniStudy

/-- info: 'Matrix.UnitaryGroup.fsMeasure_null_of_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fsMeasure_null_of_cone

-- E3 spike (2026-08-22, equilibration-arc-plan.md): the rays of a PROPER subspace are
-- Fubini-Study-null. Their cone is the subspace, and a proper subspace is Lebesgue-null
-- (Measure.addHaar_submodule). Reusable, and the reason a microcanonical restriction to an
-- exact spectral sector cannot be defined by restricting mu_FS -- see
-- Thermo/SectorRestriction.lean for the arena-level consequence.
/-- info: 'Matrix.UnitaryGroup.fsMeasure_subspaceRays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fsMeasure_subspaceRays

-- Projectivization.instMeasurableSingletonClass removed 2026-09-16 (Mathlib's
-- OpensMeasurableSpace.toMeasurableSingletonClass covers it).

/-- info: 'Projectivization.borel_eq_map_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.borel_eq_map_mk'

/-- info: 'Projectivization.lift_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.lift_measurable

-- UnitSection (2026-09-11, W6''): the canonical measurable unit section of the ray map of a
-- finite-dimensional EuclideanSpace -- unit-norm representative with first non-zero coordinate
-- real and positive; scale-invariant so it descends through Projectivization.lift, measurable
-- as a finite sum of candidate representatives on the measurable sets "first index = i".
/-- info: 'Projectivization.firstIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.firstIndex

/-- info: 'Projectivization.firstIndex_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.firstIndex_eq_iff

/-- info: 'Projectivization.unitRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.unitRep

/-- info: 'Projectivization.unitRep_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.unitRep_smul

/-- info: 'Projectivization.unitSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.unitSection

/-- info: 'Projectivization.norm_unitSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_unitSection

/-- info: 'Projectivization.mk_unitSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_unitSection

/-- info: 'Projectivization.measurableSet_firstIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.measurableSet_firstIndex_eq

/-- info: 'Projectivization.measurable_unitRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.measurable_unitRep

/-- info: 'Projectivization.measurable_unitSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.measurable_unitSection

/-- info: 'Projectivization.measurable_iff_measurable_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.measurable_iff_measurable_comp_mk'

/-- info: 'Projectivization.continuous_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.continuous_iff

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

/-- info: 'Projectivization.mapEquiv_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_smul_eq

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

-- unitaryHaar and its four lemmas removed 2026-09-16: unitaryHaarProb is Mathlib's haarMeasure ⊤ directly.
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

/-- info: 'Matrix.UnitaryGroup.fsMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fsMeasure

/-- info: 'Matrix.UnitaryGroup.instIsProbabilityMeasureFsMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsProbabilityMeasureFsMeasure

/-- info: 'Matrix.UnitaryGroup.smul_comp_orbitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.smul_comp_orbitMap

/-- info: 'Matrix.UnitaryGroup.fsMeasure_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fsMeasure_smul_invariant

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

/-- info: 'Matrix.UnitaryGroup.fsMeasure_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fsMeasure_unique

-- Q28 item 1 (2026-08-21, FubiniStudyUnique.lean): FUBINI-STUDY ATOMLESSNESS by pigeonhole,
-- no stabiliser Haar measure. Transitivity + invariance make all singletons equal in mass
-- (fsMeasure_singleton_eq); the projective space is infinite for 2 <= N
-- (projectivization_infinite -- the rays [e0 + t*e1], t : NAT, pairwise distinct); a
-- probability measure cannot give arbitrarily many disjoint points a common positive mass.
-- Retires KahlerInstance.lean's "Haar-of-subgroup" caveat; feeds the null-fibre corollary
-- (SigmaLayer/PreparationDensity.lean) that makes the pure-state Dirac wrapper unreachable
-- as a physical preparation (the C2 region-preparation proposition's last step).
/-- info: 'Matrix.UnitaryGroup.projectivization_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.projectivization_infinite

/-- info: 'Matrix.UnitaryGroup.fsMeasure_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.fsMeasure_singleton

-- Pointwise Kähler fundamental form (2026-07-10): the form-level analogue of fsMeasure. On a
-- complex inner-product space (the tangent model ψ^⊥ of ℂℙ^{N-1}) the flat Hermitian structure gives the
-- Kähler triple g = re⟪·,·⟫, ω = im⟪·,·⟫, J = i•·. Proved pointwise & axiom-free: J²=-1, ω alternating
-- ℝ-bilinear, J-compatibility ω u v = g(Ju) v, dual g u v = ω u (Jv), ω J-invariant (a (1,1)-form),
-- positivity ω u (Ju) = ‖u‖². This is the "compatible with J + positive" half of Kähler. Closedness dω=0
-- and the global ω^∧n/n! = μ_FS need manifold exterior calculus (absent from Mathlib) and stay blocked.
-- Kahler.fubiniStudy_pointwise_kahler_compatibility removed 2026-09-16 (conjunction capstone; the conjuncts are pinned).

/-- info: 'Kahler.metric_eq_real_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.metric_eq_real_inner

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
-- Kahler.tangent_complexStructure_invariant removed 2026-09-16 (conjunction capstone; the conjuncts are pinned).

-- Schrödinger flow = Kähler symplectomorphism (2026-07-11): ties the pointwise Kähler form to the
-- Schrödinger pillar. Any ℂ-linear isometry preserves g = re⟪·,·⟫ and ω = im⟪·,·⟫
-- (kahler_structure_isometry_invariant), so exp(-itH) (schrodingerUnitary, unitary) preserves the FS
-- metric AND symplectic form — QM evolution is a symplectic isometry of the CP^{N-1} Kähler geometry
-- (Kibble/Ashtekar–Schilling picture, pointwise/linear level). The converse X_H = ω⁻¹dH (KG-2) stays
-- Mathlib-blocked (manifold symplectic-gradient API).
-- Kahler.kahler_structure_isometry_invariant removed 2026-09-16 (conjunction capstone; the conjuncts are pinned).

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

-- B.5/B.6 (2026-09-01): operator CONCAVITY, transported the same way as monotonicity.
-- Upstream proved the C*-generic statements (CFC.concaveOn_log, CFC.concaveOn_rpow) and
-- CStarAlgebra (Matrix n n C) exists as a SCOPED instance (Matrix.Norms.L2Operator), so the
-- plan's L.2 wall ("Matrix is not a CStarAlgebra") was a scope question, not an absence.
-- operatorConcaveOn_log is the L.2 summit in the corpus's all-dimensions predicate;
-- matrix_rpow_concave is the L.3a interior, superseding the endpoints-only rungs.
/-- info: 'Matrix.smul_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.smul_transport

/-- info: 'Matrix.matrix_log_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_log_concave

/-- info: 'Matrix.operatorConcaveOn_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_log

/-- info: 'Matrix.matrix_rpow_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_rpow_concave

-- ★ L.4 (2026-09-01): x^p operator CONVEX on Icc 1 2, and x*log x operator convex.  Both close
-- named TODOs in Mathlib's own source (Rpow/Order.lean, ExpLog/Order.lean).  The x*log x proof
-- needs NO new analysis: Tendsto.const_mul on the existing CFC.tendsto_cfc_rpow_sub_one_log,
-- then isClosed_setOfPred_convexOn.mem_of_tendsto -- the same shape as CFC.concaveOn_log.  The
-- x^p rung works because rpowIntegrand-12 is affine plus a nonneg multiple of the RESOLVENT,
-- whose operator convexity is already upstream.
-- ⚠️ THIS IS NOT DPI.  L.4 is an INPUT to the Effros/Lieb summit (L.5), which is untouched,
-- absent from Mathlib entirely, and scoped at 3-5 months in specs/lieb-dpi-scoping.md.  The
-- hDPI hypothesis of strong_subadditivity_of_relEntropy_monotone REMAINS explicit, which is its
-- recorded terminal status (CL-023, qualified-by-design).
/-- info: 'OperatorConvexCFC.convexOn_rpow_Ioo12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OperatorConvexCFC.convexOn_rpow_Ioo12

/-- info: 'OperatorConvexCFC.convexOn_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OperatorConvexCFC.convexOn_mul_log

/-- info: 'Matrix.matrix_mul_log_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_mul_log_convex

/-! ### Uhlmann fidelity core (Fidelity.lean, 2026-09-01)

The sandwich is PSD, so the spectral definition is real; the headline is SYMMETRY, which
is not obvious (the two sandwiches are different matrices) and comes from the corpus's
rectangular-spectrum lemma at M = sqrt-sigma * sqrt-rho. F <= 1 and Uhlmann are NOT here:
they need a polar decomposition, absent from the pin. -/
/-- info: 'QuantumInfo.posSemidef_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.posSemidef_sandwich

/-- info: 'QuantumInfo.fidelity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.fidelity_nonneg

/-- info: 'QuantumInfo.fidelity_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.fidelity_comm

-- ★★ THE UPPER BOUND (2026-09-01).  F <= 1 for positive-definite states.  Route: X = sqrt-sigma
-- sqrt-rho has X^H X = the sandwich, so the polar factor of X has trace F; writing that trace as
-- a Hilbert-Schmidt pairing and applying Cauchy-Schwarz gives F <= ||sqrt-sigma U||_2 ||sqrt-rho||_2
-- = sqrt(Tr sigma) sqrt(Tr rho) = 1.  BOTH ingredients had to be BUILT, not imported: Mathlib gives
-- Matrix only a Frobenius NORM (no inner product), so norm_trace_conjTranspose_mul_le transports to
-- EuclideanSpace C (n x n); and Mathlib has singular VALUES but no polar/SVD factorisation, so
-- exists_unitary_conjTranspose_mul_eq_sqrt builds U = X P^{-1} for invertible X.
-- ⚠️ PosDef is load-bearing, not decorative: it is what makes X invertible.  Same posture as
-- klein_inequality.  Uhlmann and Fuchs-van de Graaf remain not attempted.
/-- info: 'QuantumInfo.norm_trace_conjTranspose_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.norm_trace_conjTranspose_mul_le

/-- info: 'QuantumInfo.exists_unitary_conjTranspose_mul_eq_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_unitary_conjTranspose_mul_eq_sqrt

/-- info: 'QuantumInfo.fidelity_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.fidelity_le_one

/-! ### Kahler chart-form identification (KahlerPotential.lean, 2026-09-01)

extDeriv_fsChartForm previously asserted closedness of a form whose pointwise value was never
computed anywhere. fsChartForm_apply supplies the second-derivative computation on
log(1 + |z|^2) -- the residue the module named as NOT ATTEMPTED -- and fsChartForm_zero
identifies the result at the chart origin with the constant fundamental form of KahlerForm.lean
up to the normalisation -4. So the closedness is now closedness of an identified object. -/
/-- info: 'Kahler.hasFDerivAt_fsPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.hasFDerivAt_fsPotential

/-- info: 'Kahler.dcForm_fsPotential_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.dcForm_fsPotential_apply

/-- info: 'Kahler.fsChartForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fsChartForm_apply

/-- info: 'Kahler.fsChartForm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fsChartForm_zero

/-! ### Projective one-parameter lift (ProjectiveLift.lean, 2026-09-01)

A continuous projective one-parameter unitary group in finite dimensions has a COBOUNDARY
phase cocycle -- so it lifts to a genuine unitary group. Not Bargmann's theorem: for R the
obstruction group is trivial, and the proof is determinants (reducing N phases to one on
the circle) + the covering lift through Circle.exp (R is simply connected) + constancy of a
continuous map into the finite N-th roots of unity on a connected domain. -/
/-- info: 'Matrix.ProjectiveLift.const_of_finite_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.ProjectiveLift.const_of_finite_range

/-- info: 'Matrix.ProjectiveLift.norm_det_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.ProjectiveLift.norm_det_eq_one

/-- info: 'Matrix.ProjectiveLift.exists_continuous_phase_trivialisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.ProjectiveLift.exists_continuous_phase_trivialisation

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

-- MixedLuders (2026-08-03, RecordLayer/MixedLuders.lean; the outcome-conditioned mixed update,
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
-- RecordLayer/PointerHamiltonianField.lean; BACKLOG A4's LINEAR FRAGMENT -- the manifold
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

/-- info: 'Kahler.fundamentalForm_sub_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_sub_left

/-- info: 'Kahler.eq_hamiltonianVectorFieldOf_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.eq_hamiltonianVectorFieldOf_of_forall

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

/-! ### The continuous exterior product (Wedge.lean / KahlerWedge.lean, 2026-09-07) -/

-- Step (1) of the manifold exterior-calculus plan (MATHLIB-GAPS.md, BACKLOG XL). Mathlib's
-- exterior product is AlternatingMap-only and is valued in the TENSOR product of the
-- codomains, which carries no topology at the pin -- so the continuous analogue cannot even
-- be stated in that form. Pairing the codomains through a continuous bilinear map is the
-- standard fix and is what these pins cover. The payoff is that omega ^ omega is now a term:
-- before this, a top-power identity was not expressible in Lean at all.

/-- info: 'ContinuousAlternatingMap.continuous_liftTensor_summand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.continuous_liftTensor_summand

/-- info: 'ContinuousAlternatingMap.wedge_toAlternatingMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_toAlternatingMap

/-- info: 'ContinuousAlternatingMap.wedge_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_apply

/-- info: 'ContinuousAlternatingMap.domDomCongr_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.domDomCongr_apply

/-- info: 'Kahler.fundamentalFormSq_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fundamentalFormSq_apply

/-- info: 'Kahler.extDeriv_fundamentalFormSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.extDeriv_fundamentalFormSq

/-! ### dd^c calculus: pluriharmonicity and naturality (KahlerPluriharmonic.lean, 2026-09-07) -/

-- The flat lemmas a chart-invariance argument for the Fubini-Study form composes: Cauchy-Riemann
-- in the d^c vocabulary, hence Re(holomorphic) is pluriharmonic; log|L .| pluriharmonic off the
-- kernel via a LOCAL holomorphic logarithm (no global branch); and dd^c natural under holomorphic
-- maps, whose d-half is upstream's extDeriv_pullback.

/-- info: 'Kahler.dcForm_re_eq_neg_dForm_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.dcForm_re_eq_neg_dForm_im

/-- info: 'Kahler.ddcForm_re_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_re_eq_zero

/-- info: 'Kahler.ddcForm_log_norm_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_log_norm_eq_zero

/-- info: 'Kahler.ddcForm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_comp

/-- info: 'Kahler.ddcForm_sub'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_sub'

/-! ### The alternating pullback is jointly analytic (Alternating/Pullback.lean, 2026-09-07) -/

-- The lemma step (2a) ran aground on. Smooth differential forms on a MANIFOLD need a
-- ContMDiffVectorBundle instance for the alternating-map bundle, whose crux is smoothness of
-- the coordinate change, which reduces to joint smoothness of the pullback (g, omega) |-> omega
-- after g. Upstream has that for the MULTILINEAR pullback and, for the alternating one, only
-- continuity and the first derivative. ⚠️ The obvious reduction fails: the alternating pullback
-- is the DIAGONAL of the multilinear one, degree (card iota) in g rather than linear.
-- What unlocks it is a RETRACTION: alternatization is continuous linear (built here; upstream
-- has only the AddMonoidHom) and multiplies an already-alternating map by (card iota)!, so in
-- characteristic zero it inverts the inclusion and analyticity reflects along it.
-- ⚠️ Three layers still remain before step (2a) itself: the ContMDiffOn coordinate change, the
-- bundle instance, and forms as smooth sections.

/-- info: 'ContinuousMultilinearMap.continuous_alternatization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousMultilinearMap.continuous_alternatization

/-- info: 'ContinuousMultilinearMap.alternatizationCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousMultilinearMap.alternatizationCLM

/-- info: 'ContinuousMultilinearMap.alternatizationCLM_of_alternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousMultilinearMap.alternatizationCLM_of_alternating

/-- info: 'ContinuousAlternatingMap.compContinuousLinearMap_eq_smul_alternatization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.compContinuousLinearMap_eq_smul_alternatization

/-- info: 'ContinuousAlternatingMap.analyticAt_uncurry_compContinuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.analyticAt_uncurry_compContinuousLinearMap

/-- info: 'ContinuousAlternatingMap.contDiff_uncurry_compContinuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.contDiff_uncurry_compContinuousLinearMap

-- The operator-valued layer (2026-09-07, same file): what a bundle coordinate change is
-- actually built from. ⚠️ The layer above these stops on an INSTANCE-PATH mismatch, not a
-- theorem -- the decomposition of the coordinate change is `rfl` and the proof is three lines,
-- but the bundled maps elaborate on the topological-module instances where the normed path is
-- wanted. Recorded in the module header; deliberately not papered over.

/-- info: 'ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM

-- ContinuousLinearMap.compContinuousAlternatingMapL removed 2026-09-16 (Mathlib's
-- compContinuousAlternatingMapCLM is the same map).

/-! ### The alternating-map bundle is a `C^n` vector bundle (VectorBundle/AlternatingMap.lean) -/

-- Step (2a), layers three and four. ⚠️ The blocker recorded in the previous commit as an
-- "instance-path mismatch needing plumbing" was DIAGNOSED WRONG: the two topologies on a
-- continuous-linear-map space are the same instance (checked by rfl). The real cause is
-- elaboration order -- a type ASCRIPTION re-synthesises instances down the normed path while
-- the term carries the topological-module path. Stating the ContDiff fact through the term
-- (`ContDiff k n (coe f)`) instead of through an ascription fixes it outright, and both layers
-- then land. The correction is written up in the module header.

/-- info: 'contMDiffOn_continuousAlternatingMapCoordChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contMDiffOn_continuousAlternatingMapCoordChange

/-- info: 'ContMDiffVectorBundle.continuousAlternatingMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContMDiffVectorBundle.continuousAlternatingMap

-- ★ STEP (2a) COMPLETE (DifferentialForm.lean): a differential form on a manifold is a smooth
-- section of the alternating-map bundle on the tangent bundle, and CP^n carries ANALYTIC forms
-- of every degree -- the whole chain from step (0) in one statement. ⚠️ The witness HERE is the
-- ZERO form; the Fubini-Study form as a section landed later the same day (chart-overlap
-- agreement + bundle assembly: ProjectiveSpaceFubiniStudy{,Form}.lean, pinned below). ⚠️ And
-- the exterior derivative landed later still (ExteriorDerivative.lean, pinned below); at the
-- time of this pin there was none: that was
-- step (2b), upstream's own TODO, so the top-power identity is SAYABLE and no more provable
-- than it was this morning.

-- projectiveDifferentialForm_nonempty (the zero-form witness) removed 2026-09-16; the genuine
-- non-vacuity certificate is Projectivization.fsForm_ne_zero, pinned below.

/-! ### Complex projective space as an analytic manifold (ProjectiveSpace.lean, 2026-09-07) -/

-- Step (0) of the manifold exterior-calculus plan. Before this, `Projectivization` had a
-- topology, a measurable space and a metric in this repository and a charted-space instance
-- NOWHERE -- so the space the reconstruction is stated over was not a manifold in Lean and
-- nothing on it could be differentiated. The transition maps are ratios of coordinates of
-- `Fin.insertNth i 1 w`, hence analytic, so the instance is `omega`, not merely `C^infinity`.

/-- info: 'Projectivization.isOpen_chartSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isOpen_chartSource

/-- info: 'Projectivization.chartInv_chartFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartInv_chartFun

/-- info: 'Projectivization.continuousOn_chartFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.continuousOn_chartFun

/-- info: 'Projectivization.instChartedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.instChartedSpace

/-- info: 'Projectivization.contDiffOn_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiffOn_transition

/-- info: 'Projectivization.instIsManifold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.instIsManifold

-- The same atlas over R (2026-09-07): a C-analytic manifold is R-analytic, and the real
-- structure is where a REAL 2-form -- the Fubini-Study form is R-bilinear, not C-bilinear --
-- has to live.
/-- info: 'Projectivization.instIsManifoldReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.instIsManifoldReal

-- Q33 (2026-09-11), Instances/AddCircle.lean: a charted space and all its groupoids transport
-- along a homeomorphism (the transported atlas's transitions ARE the source's, on the nose), so
-- AddCircle T (T != 0) is an analytic manifold via AddCircle.homeomorphCircle -- Mathlib charts
-- Circle, not AddCircle, and lists the quotient IsManifold as a TODO -- and the torus
-- AddCircle T x AddCircle T' is one by the product instance.
/-- info: 'Homeomorph.transportChartedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Homeomorph.transportChartedSpace

/-- info: 'Homeomorph.transport_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Homeomorph.transport_transition

/-- info: 'Homeomorph.hasGroupoid_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Homeomorph.hasGroupoid_transport

/-- info: 'Homeomorph.isManifold_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Homeomorph.isManifold_transport

/-- info: 'AddCircle.instChartedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddCircle.instChartedSpace

/-- info: 'AddCircle.instIsManifold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddCircle.instIsManifold

/-- info: 'AddCircle.instIsManifoldProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddCircle.instIsManifoldProd

-- Q29(a) (2026-09-11), IntegralCurve/GlobalFlow.lean: global flows of a C^1 vector field on a
-- compact manifold. Mathlib has local existence, uniqueness and the uniform-time principle
-- (exists_isMIntegralCurve_of_isMIntegralCurveOn) but not the uniform epsilon. Route: Picard-
-- Lindelof with the Lipschitz ball inside a prescribed neighbourhood and the solution's
-- confinement exposed (ContDiffAt.isPicardLindelof_subset, ..._mem_closedBall, ..._mem), so one
-- epsilon serves a whole chart ball of initial points with the chart curves staying in the
-- chart target (exists_nhds_forall_exists_isMIntegralCurveOn_Ioo); a finite subcover and the
-- minimum epsilon give every point a global curve (exists_isMIntegralCurve_of_compactSpace);
-- uniqueness makes it a flow with the group law (integralFlow, integralFlow_add). Joint
-- continuity in (t, x) is not stated (Q29(a')). The Hamiltonian instance:
-- IsSymplectic.exists_isMIntegralCurve_hamiltonianVectorField.
/-- info: 'ContDiffAt.isPicardLindelof_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.isPicardLindelof_subset

/-- info: 'IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall

/-- info: 'ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt_mem

/-- info: 'exists_nhds_forall_exists_isMIntegralCurveOn_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nhds_forall_exists_isMIntegralCurveOn_Ioo

/-- info: 'exists_isMIntegralCurve_of_compactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isMIntegralCurve_of_compactSpace

/-- info: 'integralFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlow

/-- info: 'integralFlow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlow_zero

/-- info: 'isMIntegralCurve_integralFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isMIntegralCurve_integralFlow

/-- info: 'integralFlow_eq_of_isMIntegralCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlow_eq_of_isMIntegralCurve

/-- info: 'integralFlow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlow_add

/-- info: 'continuous_integralFlow_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_integralFlow_time

-- Q29(a') (2026-09-12), IntegralCurve/FlowContinuity.lean: the flow is JOINTLY continuous.
-- Picard-Lindelof with Lipschitz dependence on the initial point plus confinement; a jointly
-- continuous local flow in the chart; uniqueness identifies it with integralFlow near t = 0;
-- compactness gives a uniform small time, iteration of the group law gives continuity in the
-- initial point at every time, and the group law gives joint continuity everywhere.
/-- info: 'IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_mem

/-- info: 'ContDiffAt.exists_localFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.exists_localFlow

/-- info: 'isMIntegralCurveOn_extChartAt_symm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isMIntegralCurveOn_extChartAt_symm_comp

/-- info: 'exists_nhds_continuousOn_integralFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nhds_continuousOn_integralFlow

/-- info: 'exists_forall_continuous_integralFlow_of_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_forall_continuous_integralFlow_of_abs_lt

/-- info: 'integralFlow_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlow_nsmul

/-- info: 'continuous_integralFlow_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_integralFlow_point

/-- info: 'continuous_integralFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_integralFlow

-- Q29(b') (2026-09-12), Analysis/ODE/FlowDerivative.lean: DIFFERENTIABLE dependence of the local
-- flow on the initial point, with the variational equation (Gronwall for approximate
-- trajectories + the mean value inequality + uniform continuity of Df on a compact thickening;
-- the variational solution from Picard-Lindelof on the operator space), and flat Liouville: a C^1
-- 2-form with vanishing flat Lie derivative is pulled back to itself by the local flow.
/-- info: 'gronwallBound_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gronwallBound_zero_le

/-- info: 'exists_linearODE_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_linearODE_solution

/-- info: 'hasFDerivAt_flow_of_variational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_flow_of_variational

/-- info: 'ContDiffAt.exists_localFlow_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.exists_localFlow_hasFDerivAt

/-- info: 'flatLieDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flatLieDeriv

/-- info: 'form_invariant_of_flatLieDeriv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms form_invariant_of_flatLieDeriv_eq_zero

/-- info: 'ContDiffAt.exists_localFlow_form_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.exists_localFlow_form_invariant

-- BACKLOG #8 landing (2026-09-18), Analysis/ODE/FlowDerivative.lean, time-dependent fields: the
-- variational equation for a non-autonomous C^1 field (the autonomous statement is now its
-- corollary), transport of a time-dependent 2-form along the flow of X_t when
-- d/dt Omega_t + L_{X_t} Omega_t = 0, the flow up to a prescribed time T of a field with
-- |Df| <= M, M T <= 1/2, vanishing at the centre (confinement, Gronwall separation, variational
-- derivative), and the linear ODE solved under a product bound.
/-- info: 'exists_linearODE_solution_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_linearODE_solution_of_le

/-- info: 'hasFDerivAt_flow_of_variational_timeDependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_flow_of_variational_timeDependent

/-- info: 'form_invariant_of_flatLieDeriv_eq_zero_timeDependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms form_invariant_of_flatLieDeriv_eq_zero_timeDependent

/-- info: 'exists_flow_hasFDerivAt_of_norm_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_flow_hasFDerivAt_of_norm_fderiv_le

-- BACKLOG #49 (2026-09-23), Analysis/ODE/FlowDerivative.lean: continuous dependence of the
-- variational solution on the initial point. norm_le_exp_of_linearODE: a solution of the
-- operator-valued Y' = A(t) Y, Y 0 = 1, |A| <= M has |Y t| <= exp(M t) (Gronwall against the zero
-- solution); dist_le_of_linearODE_coeff_close: two such solutions with coefficients eps-close on
-- [0, T] are within eps exp(MT) T exp(MT) (Gronwall for approximate trajectories on the operator
-- space). exists_flow_hasFDerivAt_of_norm_fderiv_le now also states that x -> Y x t is continuous
-- on the half-ball, i.e. the time-t map is C^1 there (uniform continuity of (t, z) -> D(f t)(z) on
-- the compact [0, T] x closedBall, plus the Gronwall separation of trajectories).
/-- info: 'norm_le_exp_of_linearODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_le_exp_of_linearODE

/-- info: 'dist_le_of_linearODE_coeff_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dist_le_of_linearODE_coeff_close

-- BACKLOG #8 landing (2026-09-18), Analysis/Calculus/DifferentialForm/Poincare.lean: the Poincare
-- lemma for closed C^1 2-forms on a ball by the radial homotopy operator, built from scalar
-- parametric integrals (hasFDerivAt_integral_of_dominated_of_fderiv_le,
-- continuousAt_of_dominated_interval) and packaged as a C^1 1-form through a basis; the
-- primitive of a form vanishing at the centre has zero derivative there.
/-- info: 'isBoundedBilinearMap_apply_vecCons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isBoundedBilinearMap_apply_vecCons

/-- info: 'hasFDerivAt_evalPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_evalPair

/-- info: 'hasFDerivAt_radialPrimitiveVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_radialPrimitiveVal

/-- info: 'contDiffOn_radialPrimitiveVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitiveVal

/-- info: 'contDiffOn_radialPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitive

/-- info: 'contDiffOn_radialPrimitiveForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitiveForm

/-- info: 'hasFDerivAt_radialPrimitiveForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_radialPrimitiveForm

/-- info: 'fderiv_radialPrimitive_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fderiv_radialPrimitive_self

/-- info: 'hasFDerivAt_radialPrimitiveForm_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_radialPrimitiveForm_self

/-- info: 'extDeriv_radialPrimitiveForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extDeriv_radialPrimitiveForm

-- BACKLOG #8 assembly (2026-09-21), Geometry/Manifold/Darboux.lean: Darboux's theorem by Moser's
-- trick. Non-degeneracy is open (invertibility of curryLeft), Moser's field X_t = -(omega_t)^flat^-1
-- beta is jointly C^1 and vanishes to second order at the centre, its flow to time 1 transports the
-- interpolation (flat Cartan + Poincare), and the time-1 map approximates the identity with
-- constant e^{1/4}/4 < 1, so it is an OpenPartialHomeomorph (Mathlib's inverse function theorem)
-- pulling omega back to the constant form omega(x_0); the same on a symplectic manifold through
-- localRep. The chart is C^1 with C^1 inverse (BACKLOG #49, 2026-09-23) and the standard form
-- sum dp_i wedge dq_i is Geometry/Manifold/DarbouxStandardForm.lean (BACKLOG #50, 2026-09-23);
-- the chart is C^n for a C^n form and C^infty on a symplectic manifold (BACKLOG #60,
-- 2026-09-23, Analysis/ODE/FlowSmooth.lean).
/-- info: 'isOpen_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isOpen_nondegenerate

/-- info: 'exists_nondegenerate_of_norm_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_nondegenerate_of_norm_sub_lt

/-- info: 'extDeriv_moserPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extDeriv_moserPrimitive

/-- info: 'curryLeft_moserForm_moserField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms curryLeft_moserForm_moserField

/-- info: 'contDiffOn_moserFieldJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms contDiffOn_moserFieldJoint

/-- info: 'hasFDerivAt_moserField_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasFDerivAt_moserField_self

/-- info: 'exists_moser_small_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_moser_small_ball

/-- info: 'approximatesLinearOn_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms approximatesLinearOn_flow

/-- info: 'injective_of_compContinuousLinearMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms injective_of_compContinuousLinearMap_eq

/-- info: 'exists_openPartialHomeomorph_pullback_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_openPartialHomeomorph_pullback_eq

/-- info: 'exists_openPartialHomeomorph_symm_pullback_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_openPartialHomeomorph_symm_pullback_eq

/-- info: 'DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_eq

-- BACKLOG #49 (2026-09-23), Geometry/Manifold/Darboux.lean: the Darboux chart is C^1. The three
-- Darboux theorems above now carry ContDiffOn 1 of Phi on its source and of Phi.symm on its target
-- (contDiffAt_one_iff on the continuous derivative x -> Y x 1, Mathlib's
-- OpenPartialHomeomorph.contDiffAt_symm for the inverse), and on a symplectic manifold the Darboux
-- chart Phi^-1 o chartAt contains x0 and is a member of the C^1 maximal atlas.
-- mem_contDiffGroupoid_of_contDiffOn: a C^n open partial homeomorphism of the model space with
-- C^n inverse is in the C^n groupoid; StructureGroupoid.trans_mem_maximalAtlas: a maximal-atlas
-- chart composed with a groupoid member stays in the maximal atlas.
/-- info: 'mem_contDiffGroupoid_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_contDiffGroupoid_of_contDiffOn

/-- info: 'StructureGroupoid.trans_mem_maximalAtlas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureGroupoid.trans_mem_maximalAtlas

-- BACKLOG #14(a) (2026-09-21), QuantumInfo/KnillLaflamme.lean: the Knill-Laflamme theorem. A family
-- of errors is correctable on a code projector P (some channel inverts every error on the code up
-- to a scalar) iff P E_i^H E_j P = c_ij P. Recovery: diagonalise the Hermitian c, the canonical
-- errors F_k = sum_i U_ik E_i have orthogonal images of the code, R_k = d_k^{-1/2} P F_k^H completed
-- by 1 - sum R_k^H R_k. Converse: each R_k E_i P is a scalar on the code (sandwiched rank-one
-- identity), and trace preservation assembles the condition.
/-- info: 'QuantumInfo.IsCodeProjector.nonneg_of_smul_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.IsCodeProjector.nonneg_of_smul_posSemidef

/-- info: 'QuantumInfo.KnillLaflamme.isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.KnillLaflamme.isHermitian

/-- info: 'QuantumInfo.recoveryKraus_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.recoveryKraus_tp

/-- info: 'QuantumInfo.recoveryChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.recoveryChannel_apply

/-- info: 'QuantumInfo.knillLaflamme_canonicalError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.knillLaflamme_canonicalError

/-- info: 'QuantumInfo.exists_recovery_of_knillLaflamme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.exists_recovery_of_knillLaflamme

/-- info: 'QuantumInfo.exists_recovery_channel_of_knillLaflamme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.exists_recovery_channel_of_knillLaflamme

/-- info: 'QuantumInfo.exists_smul_of_sum_conj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.exists_smul_of_sum_conj_eq

/-- info: 'QuantumInfo.knillLaflamme_of_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.knillLaflamme_of_recovery

/-- info: 'QuantumInfo.knillLaflamme_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.knillLaflamme_iff

-- BACKLOG #14(b) general half (2026-09-21), QuantumInfo/StabilizerRecovery.lean: stabiliser codes meet
-- Knill-Laflamme. Pauli matrices on the register (group law, commutation, adjoint transported from
-- pauliOp through Matrix.ext_of_mulVec), the group average as a code projector (every signed element
-- is Hermitian because coherence forces B_x . A_x = 0), a Pauli anticommuting with a generator is
-- killed by the code, and a detected Pauli error family satisfies Knill-Laflamme with c = 1 -- so the
-- recovery channel exists.
/-- info: 'QuantumInfo.pauliMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.pauliMat_mul

/-- info: 'QuantumInfo.pauliMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.pauliMat_conjTranspose

/-- info: 'QuantumInfo.isCodeProjector_stabMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.isCodeProjector_stabMat

/-- info: 'QuantumInfo.stabMat_mul_genMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.stabMat_mul_genMat

/-- info: 'QuantumInfo.stabMat_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.stabMat_ne_zero

/-- info: 'QuantumInfo.stabMat_mul_pauliMat_mul_stabMat_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.stabMat_mul_pauliMat_mul_stabMat_eq_zero

/-- info: 'QuantumInfo.stabMat_knillLaflamme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.stabMat_knillLaflamme

/-- info: 'QuantumInfo.exists_recovery_stabMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms QuantumInfo.exists_recovery_stabMat

-- BACKLOG #10 BP-1 (2026-09-21), Analysis/InnerProductSpace/GeometricPhase.lean: the Aharonov-Anandan
-- geometric phase of a cyclic evolution, on the sphere (no bundles at the pin). The connection form
-- Im<psi, psi'> shifts by theta' under a rephasing e^{i theta}, so the geometric phase
-- phi - int A is gauge invariant (a function of the closed curve of rays); the horizontal lift
-- e^{-i int A} psi has A = 0 and returns as e^{i beta}: the geometric phase is the holonomy; for a
-- Schrodinger evolution the energy is conserved and beta = phi + T <H>.
/-- info: 'GeometricPhase.connectionForm_rephase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.connectionForm_rephase

/-- info: 'GeometricPhase.geometricPhase_rephase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.geometricPhase_rephase

/-- info: 'GeometricPhase.connectionForm_horizontalLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.connectionForm_horizontalLift

/-- info: 'GeometricPhase.horizontalLift_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.horizontalLift_cyclic

/-- info: 'GeometricPhase.connectionForm_of_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.connectionForm_of_schrodinger

/-- info: 'GeometricPhase.inner_self_const_of_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.inner_self_const_of_schrodinger

/-- info: 'GeometricPhase.geometricPhase_of_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GeometricPhase.geometricPhase_of_schrodinger

-- Q29(c') (2026-09-12), Geometry/Manifold/HamiltonianLieDerivative.lean: Cartan's formula on a
-- normed space (L_X omega = d(iota_X omega) + iota_X d omega, from extDeriv_apply), and for the
-- local representative of a symplectic form along its local Hamiltonian vector both terms
-- vanish (iota_X omega_loc = d(H o chart^-1) so d of it is d d = 0; d omega_loc = 0 from closedness
-- through localRep_mextDerivFamily): the flat Lie derivative is zero on the chart's target.
/-- info: 'flatInteriorProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flatInteriorProduct

/-- info: 'differentiableAt_flatInteriorProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableAt_flatInteriorProduct

/-- info: 'fderiv_apply_vecCons_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fderiv_apply_vecCons_const

/-- info: 'ContinuousAlternatingMap.apply_swap_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.apply_swap_two

/-- info: 'flatLieDeriv_eq_extDeriv_flatInteriorProduct_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flatLieDeriv_eq_extDeriv_flatInteriorProduct_add

/-- info: 'DifferentialForm.localRep_apply_localHamiltonianVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_apply_localHamiltonianVector

/-- info: 'DifferentialForm.flatInteriorProduct_localHamiltonianVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatInteriorProduct_localHamiltonianVector

/-- info: 'DifferentialForm.extDeriv_flatInteriorProduct_localHamiltonianVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.extDeriv_flatInteriorProduct_localHamiltonianVector

/-- info: 'DifferentialForm.extDeriv_localRep_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.extDeriv_localRep_eq_zero

/-- info: 'DifferentialForm.flatLieDeriv_localHamiltonianVector_localRep_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatLieDeriv_localHamiltonianVector_localRep_eq_zero

/-- info: 'DifferentialForm.IsSymplectic.exists_isMIntegralCurve_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.exists_isMIntegralCurve_hamiltonianVectorField

/-! ### Q29(d'): the Hamiltonian flow preserves the symplectic volume (HamiltonianFlowVolume.lean,
Instances/ProjectiveSpaceHamiltonianFlow.lean, 2026-09-12) -/

-- The assembly of Q29(a)-(c'). In a chart the manifold flow is the Picard-Lindelof local flow
-- (uniqueness of integral curves), whose derivative solves the variational equation; the flat
-- Liouville theorem with the vanishing Lie derivative of (c') gives the pullback identity for the
-- 2-form near every point for a short time, the wedge power is natural under pullback, a finite
-- subcover and the two-chart lemma feed topFormMeasure_map_eq, and the group law extends to all
-- times. On CP^n: every smooth Hamiltonian flow preserves the Fubini-Study volume.

/-- info: 'chartField_eq_trivializationAt_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartField_eq_trivializationAt_snd

/-- info: 'ContinuousAlternatingMap.compContinuousLinearMap_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.compContinuousLinearMap_comp

/-- info: 'DifferentialForm.forall_chart_of_forall_exists_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.forall_chart_of_forall_exists_chart

/-- info: 'DifferentialForm.chartField_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartField_hamiltonianVectorField

/-- info: 'DifferentialForm.exists_nhds_forall_integralFlow_localRep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.exists_nhds_forall_integralFlow_localRep_eq

/-- info: 'integralFlowHomeomorph_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralFlowHomeomorph_apply

/-- info: 'map_integralFlow_eq_of_forall_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms map_integralFlow_eq_of_forall_Icc

/-- info: 'DifferentialForm.IsSymplectic.contMDiff_hamiltonianVectorField_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.contMDiff_hamiltonianVectorField_tangent

/-- info: 'DifferentialForm.exists_forall_map_integralFlow_topFormMeasure_wedgePow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.exists_forall_map_integralFlow_topFormMeasure_wedgePow_eq

/-- info: 'DifferentialForm.IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow

/-- info: 'Projectivization.fsVolume_map_hamiltonianFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_map_hamiltonianFlow

/-- info: 'Projectivization.fsVolumeNormalized_map_hamiltonianFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolumeNormalized_map_hamiltonianFlow

/-! ### The Fubini-Study chart form is chart-invariant (ProjectiveSpaceFubiniStudy.lean, 2026-09-07) -/

-- The mathematical heart of "the Fubini-Study form is a global object on CP^n": under the affine
-- chart transition i -> j the potential log(1+|z|^2) changes by -2 log|z_j|, a pluriharmonic
-- correction, so dd^c naturality (KahlerPluriharmonic.lean) carries the chart form in chart j to
-- the chart form in chart i on the overlap. Stated on the Euclidean model (fsChartForm_transE)
-- and on the Fin n -> C model the manifold is charted on (fsModelForm_transP), which is the form
-- the bundle argument below consumes.

/-- info: 'Kahler.ddcForm_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_congr

/-- info: 'Projectivization.norm_sq_insertOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sq_insertOne

/-- info: 'Projectivization.norm_sq_toLp_coordRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sq_toLp_coordRatio

/-- info: 'Projectivization.fsPotential_toLp_coordRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPotential_toLp_coordRatio

/-- info: 'Projectivization.contDiffAt_transE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiffAt_transE

/-- info: 'Projectivization.coordRatio_insertOne_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.coordRatio_insertOne_self

/-- info: 'Projectivization.transE_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transE_self

/-- info: 'Projectivization.fsPotential_transE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPotential_transE

/-- info: 'Projectivization.fsChartForm_transE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsChartForm_transE

/-- info: 'Projectivization.transE_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transE_eq

/-- info: 'Projectivization.fsModelForm_transP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_transP

/-! ### The Fubini-Study form as a global smooth 2-form on CP^n (ProjectiveSpaceFubiniStudyForm.lean, 2026-09-07) -/

-- ★★ Step (2a)'s witness is no longer the zero form. `fsForm` is a C^infinity section of the
-- alternating bundle on the tangent bundle of CP^n -- a term of `DifferentialForm` -- built from
-- the chart forms through the local-representative identity `localRep_fsSection`: the tangent
-- coordinate change is the derivative of the chart transition
-- (`VectorBundleCore.trivializationAt_symmL`) and the pullback of the chart form along it is the
-- chart form (`fsModelForm_transP`). Non-vacuity: `fsForm_ne_zero` (n >= 1) -- at a chart origin
-- it is -4 times the flat fundamental form. ⚠️ C^infinity, not omega (the potential is only
-- known C^infinity); ⚠️ at the time of this pin there was no `d` on the manifold -- it landed the
-- same evening (ExteriorDerivative.lean, below) and `d fsForm = 0` is `fsForm_mextDeriv`; neither
-- non-degeneracy nor the top-power identity is attempted.

/-- info: 'Projectivization.extChartAt_trans_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.extChartAt_trans_eq

/-- info: 'Projectivization.localRep_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.localRep_fsSection

/-- info: 'Projectivization.contDiff_fsChartForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_fsChartForm

/-- info: 'Projectivization.contDiff_fsModelForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_fsModelForm

/-- info: 'Projectivization.contMDiffAt_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiffAt_fsSection

/-- info: 'Projectivization.contMDiff_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_fsSection

/-- info: 'Projectivization.fsForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_apply

/-- info: 'Projectivization.rep_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.rep_origin

/-- info: 'Projectivization.idx_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.idx_origin

/-- info: 'Projectivization.chartFun_idx_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartFun_idx_origin

/-- info: 'Projectivization.fsSection_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsSection_origin

/-- info: 'Projectivization.fsModelForm_zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_zero_apply

/-- info: 'Projectivization.fsForm_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_ne_zero

/-! ### The exterior derivative on a manifold (ExteriorDerivative.lean, 2026-09-07) -/

-- ★★ STEP (2b) -- upstream's own TODO -- route A of specs/exterior-derivative-scoping.md, built
-- the same evening the Fubini-Study section landed, because the section's local-representative
-- identity IS route A's step 3.1 for one form. `mextDeriv s x` is the flat `extDeriv` of the local
-- representative of `s` in the chart at `x`; `localRep_mextDerivFamily` says the local representative
-- of `d s` in EVERY chart is the flat `d` of the local representative of `s` (extDeriv_pullback on
-- the chart transition + the tangent-bundle cocycle), which is chart-independence in the only
-- form a consumer needs; `contMDiff_mextDerivFamily` makes `d` iterate; `mextDeriv_mextDeriv` is
-- `d ∘ d = 0`. Scope: real boundaryless model 𝓘(ℝ, E), smoothness ∞, degrees Fin k -- the
-- finite-dimensional real manifolds the corpus uses, and none of the C^n / corners bookkeeping.
-- ⚠️ No Palais formula, no naturality under maps of manifolds, no Leibniz rule (needs the wedge
-- of sections).

/-- info: 'minSmoothness_two_le_infty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms minSmoothness_two_le_infty

/-- info: 'ContDiffAt.extDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.extDeriv

/-- info: 'extChartAt_comp_symm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extChartAt_comp_symm_eq

/-- info: 'tangent_symmL_eq_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tangent_symmL_eq_fderiv

/-- info: 'contDiffAt_chart_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffAt_chart_transition

/-- info: 'fderiv_chart_transition_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fderiv_chart_transition_comp

/-- info: 'DifferentialForm.toFlat_mextDerivFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.toFlat_mextDerivFamily

/-- info: 'DifferentialForm.trivializationAt_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_snd

/-- info: 'DifferentialForm.localRep_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_transition

/-- info: 'DifferentialForm.contDiffAt_localRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contDiffAt_localRep

/-- info: 'DifferentialForm.localRep_mextDerivFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_mextDerivFamily

/-- info: 'contMDiff_mextDerivFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contMDiff_mextDerivFamily

/-- info: 'mextDerivFamily_mextDerivFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mextDerivFamily_mextDerivFamily

/-- info: 'DifferentialForm.mextDeriv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.mextDeriv_apply

/-- info: 'DifferentialForm.mextDeriv_mextDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.mextDeriv_mextDeriv

-- ★★★ THE PAYOFF: `d ω_FS = 0` on CP^n (ProjectiveSpaceFubiniStudyForm.lean, same commit). The
-- local representative of `fsSection` in every chart is the flat chart form (localRep_fsSection),
-- whose flat `d` is zero (extDeriv_fsChartForm, MG-4) -- so the manifold closedness is the flat
-- closedness read through the chart, which is exactly what `mextDeriv` is. First manifold-level
-- Kahler statement in the corpus; the top-power identity is still not attempted.

/-- info: 'Projectivization.extDeriv_fsModelForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.extDeriv_fsModelForm

/-- info: 'Projectivization.mextDerivFamily_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mextDerivFamily_fsSection

/-- info: 'Projectivization.fsForm_mextDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_mextDeriv

/-! ### CP^n with the Fubini-Study form is a symplectic manifold (SymplecticForm.lean, ProjectiveSpaceFubiniStudySymplectic.lean, 2026-09-07) -/

-- ★★★ `fsForm_isSymplectic`: closed (fsForm_mextDeriv) AND non-degenerate at every point.
-- Non-degeneracy is taming in the chart: fsChartForm x (v, Jv) = -4 (1+|x|^2)^-2 ((1+|x|^2)|v|^2
-- - |<x,v>|^2) < 0 for v ≠ 0 by Cauchy-Schwarz (fsChartForm_complexStructure_self_neg), and the
-- section at x IS the model form at x's own chart coordinate, so the witness is i·v in the model.
-- `IsSymplectic` (SymplecticForm.lean) is a predicate demanding exactly those two obligations;
-- registered in check-claims' symplectic-vocabulary inventory with parity 2n (EVEN).
-- ⚠️ Not a manifold-level Kahler predicate (metric + complex structure not packaged), no volume
-- (top-power identity, step 3), nothing derived from the structure (Darboux, generators, moment maps).

/-- info: 'Kahler.metric_mul_fundamentalForm_complexStructure_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.metric_mul_fundamentalForm_complexStructure_sub

/-- info: 'Kahler.fsChartForm_apply_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fsChartForm_apply_complexStructure

/-- info: 'Kahler.fsChartForm_complexStructure_self_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.fsChartForm_complexStructure_self_neg

/-- info: 'Projectivization.fsModelForm_smul_I_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_smul_I_neg

/-- info: 'Projectivization.fsSection_smul_I_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsSection_smul_I_neg

/-- info: 'Projectivization.fsForm_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_nondegenerate

/-- info: 'Projectivization.fsForm_isSymplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_isSymplectic

/-! ### Top forms: the Jacobian rule (TopForm.lean) and the measure of a top form on a manifold (TopFormMeasure.lean, ProjectiveSpaceChartCover.lean, 2026-09-08) -/

-- Milestones M1 and M3 of specs/top-power-scoping.md. M1: a top-degree continuous alternating
-- form is (its value on a basis) times the basis determinant, and pulling it back along an
-- endomorphism multiplies that value by the determinant -- the factor the change-of-variables
-- formula carries. M3 (the genuine upstream gap: NO measure/integration on manifolds at the pin):
-- a top-form family has a density in every chart (|coefficient|); the chart measures are pushed
-- to M and ★★ agree on overlaps (chartMeasure_congr) by
-- lintegral_image_eq_lintegral_abs_det_fderiv_mul along the chart transition + the Jacobian rule
-- through localRep_transition; glued along the measurable partition of a FINITE chart cover given
-- as data (ChartCover) into ★★ topFormMeasure, which on any chart domain is that chart's measure
-- and ★ does not depend on the cover. The affine atlas of CP^n is such a cover
-- (affineChartCover). ⚠️ No naturality under diffeomorphisms yet (M5), no wedge of sections (M2),
-- nothing evaluated on the Fubini-Study form (M6). The plan's stop condition held:
-- chart-independence was a direct application, no new measure-theoretic lemma.

/-- info: 'ContinuousAlternatingMap.apply_eq_mul_basis_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.apply_eq_mul_basis_det

/-- info: 'ContinuousAlternatingMap.ext_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.ext_basis

/-- info: 'ContinuousAlternatingMap.compContinuousLinearMap_apply_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.compContinuousLinearMap_apply_basis

/-- info: 'MeasurableSet.inter_preimage_of_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasurableSet.inter_preimage_of_continuousOn

/-- info: 'ChartCover.piece_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartCover.piece_subset

/-- info: 'ChartCover.measurableSet_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartCover.measurableSet_piece

/-- info: 'ChartCover.pairwise_disjoint_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartCover.pairwise_disjoint_piece

/-- info: 'ChartCover.iUnion_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartCover.iUnion_piece

/-- info: 'ChartCover.iUnion_inter_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartCover.iUnion_inter_piece

/-- info: 'DifferentialForm.measurableSet_target_inter_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.measurableSet_target_inter_preimage

/-- info: 'DifferentialForm.chartMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartMeasure_apply

/-- info: 'DifferentialForm.chartMeasure_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartMeasure_congr

/-- info: 'DifferentialForm.topFormMeasure_apply_of_subset_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.topFormMeasure_apply_of_subset_source

/-- info: 'DifferentialForm.topFormMeasure_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.topFormMeasure_congr_cover

-- B12 (2026-09-16): the measure of a top form against the basis' own Haar measure is canonical.
/-- info: 'DifferentialForm.apply_basis_eq_mul_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_basis_eq_mul_det

/-- info: 'DifferentialForm.addHaar_basis_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.addHaar_basis_eq_smul

/-- info: 'DifferentialForm.chartDensity_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartDensity_basis

/-- info: 'DifferentialForm.chartMeasure_addHaar_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartMeasure_addHaar_basis

/-- info: 'DifferentialForm.topFormMeasure_addHaar_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.topFormMeasure_addHaar_basis

/-- info: 'Projectivization.affineChartCover_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.affineChartCover_m

/-- info: 'Projectivization.affineChartCover_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.affineChartCover_pt

/-! ### The wedge of sections (WedgeCLM.lean, WedgeForm.lean, 2026-09-08) -/

-- Milestone M2 of specs/top-power-scoping.md. Flat (WedgeCLM.lean): the wedge of Wedge.lean is
-- bilinear and BOUNDED in the pair of forms (norm_wedge_le, the bound Wedge.lean's honest scope
-- listed as a follow-up), hence a continuous bilinear map (wedgeL) and C^n in the pair; ★ pullback
-- commutes with the wedge (wedge_compContinuousLinearMap); reindexing is a norm-1 continuous
-- linear map (domDomCongrL). Manifold (WedgeForm.lean): the wedge of two C^infinity sections is
-- C^infinity (★★ contMDiff_wedgeFamily -- its trivialisation in a chart is the wedge of the local
-- representatives), likewise reindexing and the constant 0-form; ★★ DifferentialForm.wedge,
-- DifferentialForm.domDomCongr, DifferentialForm.constZero, DifferentialForm.wedgePow (the k-th
-- power of a real 2-form, a 2k-form). Consumer: Projectivization.fsTopForm n := wedgePow fsForm n,
-- the top power of the Fubini-Study form (ProjectiveSpaceFubiniStudyForm.lean). ⚠️ No algebraic
-- law of the wedge (associativity, graded commutativity, Leibniz) at either level, and nothing
-- says the power is nonzero -- that is M6.

/-- info: 'ContinuousAlternatingMap.liftTensor_summand_mk''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.liftTensor_summand_mk''

/-- info: 'ContinuousAlternatingMap.wedge_compContinuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_compContinuousLinearMap

/-- info: 'ContinuousAlternatingMap.wedge_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_add_left

/-- info: 'ContinuousAlternatingMap.wedge_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_smul_left

/-- info: 'ContinuousAlternatingMap.wedge_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_add_right

/-- info: 'ContinuousAlternatingMap.wedge_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_smul_right

/-- info: 'ContinuousAlternatingMap.norm_wedge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.norm_wedge_le

/-- info: 'ContinuousAlternatingMap.wedgeL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedgeL_apply

/-- info: 'ContinuousAlternatingMap.contDiff_wedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.contDiff_wedge

/-- info: 'ContDiff.wedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiff.wedge

/-- info: 'ContDiffAt.wedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.wedge

/-- info: 'ContinuousAlternatingMap.domDomCongr_compContinuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.domDomCongr_compContinuousLinearMap

/-- info: 'ContinuousAlternatingMap.norm_domDomCongr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.norm_domDomCongr_le

/-- info: 'ContinuousAlternatingMap.domDomCongrL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.domDomCongrL_apply

/-- info: 'ContDiff.domDomCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiff.domDomCongr

/-- info: 'ContDiffAt.domDomCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContDiffAt.domDomCongr

/-- info: 'DifferentialForm.toFlat_wedgeFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.toFlat_wedgeFamily

/-- info: 'DifferentialForm.trivializationAt_wedgeFamily_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_wedgeFamily_snd

/-- info: 'DifferentialForm.localRep_wedgeFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_wedgeFamily

/-- info: 'DifferentialForm.contMDiff_wedgeFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_wedgeFamily

/-- info: 'DifferentialForm.wedge_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.wedge_apply

/-- info: 'DifferentialForm.toFlat_domDomCongrFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.toFlat_domDomCongrFamily

/-- info: 'DifferentialForm.trivializationAt_domDomCongrFamily_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_domDomCongrFamily_snd

/-- info: 'DifferentialForm.localRep_domDomCongrFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_domDomCongrFamily

/-- info: 'DifferentialForm.contMDiff_domDomCongrFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_domDomCongrFamily

/-- info: 'DifferentialForm.domDomCongr_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.domDomCongr_apply

/-- info: 'DifferentialForm.trivializationAt_constZeroFamily_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_constZeroFamily_snd

/-- info: 'DifferentialForm.contMDiff_constZeroFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_constZeroFamily

/-- info: 'DifferentialForm.wedgePow_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.wedgePow_succ

/-! ### The Fubini-Study volume: unitary invariance, finiteness, and the identity up to non-vanishing (ProjectiveSpaceUnitaryAction.lean, TopFormMeasure.lean, WedgeForm.lean, ProjectiveSpaceFubiniStudyVolume.lean, 2026-09-08) -/

-- Milestones M4, M5, M6(a),(c) of specs/top-power-scoping.md. M4 (chart half): the unitary
-- action read from affine chart i to affine chart j is the linear-fractional map uTrans U i j,
-- holomorphic on its domain; the potential shifts by -2 log|affine coordinate|, pluriharmonic
-- (ddcForm_log_norm_eq_zero_of_holomorphic generalises the linear lemma to any holomorphic f),
-- so ★★ fsChartForm_uTransE / fsModelForm_uTrans: the chart form is U(n+1)-invariant. M5
-- (generic, TopFormMeasure.lean): ★★ topFormMeasure_map_eq -- a homeomorphism that preserves
-- the form in charts preserves the measure (chart-independence with the transition replaced by
-- the map's chart expression, summed over the double partition by the cover's pieces and their
-- images); the local representative of the k-th power is the k-th power of the local
-- representative (localRep_wedgePow) and pullback commutes with powers, which lifts the 2-form
-- invariance to the top power. M6(a): the measure of a smooth top form is locally finite (a
-- compact ball in a chart, continuous density), hence finite on a compact manifold -- no decay
-- estimate. M6(c): ★★★ fsVolumeNormalized_eq_fsMeasure -- the NORMALISED volume of
-- the top power of the Fubini-Study form IS fsMeasure p₀ for every p₀, by
-- fsMeasure_unique applied to a U(n+1)-invariant probability measure -- ⚠️ UNDER THE
-- PREMISE fsVolume n ≠ 0 (M6(b), the flat non-vanishing of the n-th power of the standard
-- symplectic form on the standard basis; the premise is in the statement). ⚠️ The premise was
-- discharged later the same day (M6(b) block below); the two premise theorems were renamed
-- `_of_ne_zero` and the unconditional names now carry the identity.
-- ⚠️ No constant (M7); no general pullback of forms (the invariance is consumed in chart form).

/-- info: 'Kahler.ddcForm_log_norm_eq_zero_of_holomorphic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.ddcForm_log_norm_eq_zero_of_holomorphic

/-- info: 'Projectivization.norm_toEuclideanLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_toEuclideanLinearEquiv

/-- info: 'Projectivization.uTransE_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.uTransE_eq

/-- info: 'Projectivization.smul_chartInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_chartInv

/-- info: 'Projectivization.chartFun_smul_chartInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartFun_smul_chartInv

/-- info: 'Projectivization.contDiff_uAct_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_uAct_coord

/-- info: 'Projectivization.contDiffOn_uTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiffOn_uTrans

/-- info: 'Projectivization.isOpen_uDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isOpen_uDomain

/-- info: 'Projectivization.contDiffAt_uTransE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiffAt_uTransE

/-- info: 'Projectivization.fsPotential_uTransE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPotential_uTransE

/-- info: 'Projectivization.fsChartForm_uTransE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsChartForm_uTransE

/-- info: 'Projectivization.fsModelForm_uTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_uTrans

/-- info: 'DifferentialForm.chartMeasure_preimage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.chartMeasure_preimage_eq

/-- info: 'DifferentialForm.topFormMeasure_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.topFormMeasure_map_eq

/-- info: 'DifferentialForm.continuousOn_localRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.continuousOn_localRep

/-- info: 'DifferentialForm.isLocallyFiniteMeasure_topFormMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.isLocallyFiniteMeasure_topFormMeasure

/-- info: 'DifferentialForm.isFiniteMeasure_topFormMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.isFiniteMeasure_topFormMeasure

/-- info: 'ContinuousAlternatingMap.wedgePow_compContinuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedgePow_compContinuousLinearMap

/-- info: 'DifferentialForm.localRep_constZeroFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_constZeroFamily

/-- info: 'DifferentialForm.localRep_wedgePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_wedgePow

/-- info: 'Projectivization.chartAt_smul_comp_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartAt_smul_comp_symm

/-- info: 'Projectivization.smul_symm_mem_source_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_symm_mem_source_iff

/-- info: 'Projectivization.localRep_fsSection'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.localRep_fsSection'

/-- info: 'Projectivization.localRep_fsTopForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.localRep_fsTopForm

/-- info: 'Projectivization.fsVolume_map_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_map_smul

/-- info: 'Projectivization.isFiniteMeasure_fsVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isFiniteMeasure_fsVolume

/-- info: 'Projectivization.fsVolumeNormalized_map_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolumeNormalized_map_smul

/-- info: 'Projectivization.isProbabilityMeasure_fsVolumeNormalized_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isProbabilityMeasure_fsVolumeNormalized_of_ne_zero

/-- info: 'Projectivization.fsVolumeNormalized_eq_fsMeasure_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolumeNormalized_eq_fsMeasure_of_ne_zero

/-! ### M6(b): the flat count, and the top-power identity WITHOUT premise (WedgeShuffle.lean, TopFormMeasure.lean, WedgeForm.lean, ProjectiveSpaceFubiniStudyVolume.lean, 2026-09-08) -/

-- Milestone M6(b) of specs/top-power-scoping.md, discharging the premise of the block above.
-- Two halves. GENERIC (TopFormMeasure.lean): ★ topFormMeasure_ne_zero_of_localRep_ne_zero --
-- a smooth top form whose coefficient against the basis is nonzero at ONE chart point has
-- nonzero measure (the density is continuous, so bounded below on a ball, and Haar measure
-- gives balls positive measure). FLAT (WedgeShuffle.lean, then the Volume module): (α ∧ β) u
-- with β a 2-form is a sum over the shuffle classes Perm.ModSumCongr (Fin 2k) (Fin 2); on a
-- PAIR FAMILY (β = ±1 within a pair, 0 across pairs) only the k+1 classes sending the two
-- β-slots into one pair survive, and each has a representative made of TWO DISJOINT
-- TRANSPOSITIONS (sign +1), so no sign is ever computed: ★★ wedge_mul_apply_pairs,
-- (α ∧ β) u = ∑ⱼ α (u ∘ pairRep j ∘ inl). Then ★★ wedgePow_stdForm_pairFamily by induction: the
-- k-th power of the standard symplectic form on k distinct standard pairs (e_a, i e_a) is k!,
-- and on the standard basis of Fin n → ℂ the top power of the model form at the origin is
-- (-4)^n n! (fsModelForm_zero: the model form at 0 is -4 • stdForm). Hence ★★ fsVolume_ne_zero,
-- and ★★★ fsVolumeNormalized_eq_fsMeasure UNCONDITIONALLY: the normalised volume of
-- the top power of the Fubini-Study form IS fsMeasure p₀, for every p₀.
-- ⚠️ Still no constant at this block: the identity is for the normalised measure; (-4)^n n! is
-- one chart coefficient, not the total mass. The constant is the M7 block below (same day).

/-- info: 'ContinuousAlternatingMap.slotPair_slotOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.slotPair_slotOf

/-- info: 'ContinuousAlternatingMap.slotMem_slotOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.slotMem_slotOf

/-- info: 'ContinuousAlternatingMap.slotOf_slotPair_slotMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.slotOf_slotPair_slotMem

/-- info: 'ContinuousAlternatingMap.slot_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.slot_ext

/-- info: 'ContinuousAlternatingMap.pairRep_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.pairRep_inr

/-- info: 'ContinuousAlternatingMap.pairRep_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.pairRep_inl

/-- info: 'ContinuousAlternatingMap.sign_pairRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.sign_pairRep

/-- info: 'ContinuousAlternatingMap.modSumCongr_mk_eq_of_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.modSumCongr_mk_eq_of_inr

/-- info: 'ContinuousAlternatingMap.exists_inr_eq_of_mk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.exists_inr_eq_of_mk_eq

/-- info: 'ContinuousAlternatingMap.classTerm_mk''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.classTerm_mk''

/-- info: 'ContinuousAlternatingMap.wedge_mul_apply_eq_sum_classTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_mul_apply_eq_sum_classTerm

/-- info: 'ContinuousAlternatingMap.beta_inr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.beta_inr_eq

/-- info: 'ContinuousAlternatingMap.slotPair_eq_of_classTerm_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.slotPair_eq_of_classTerm_ne_zero

/-- info: 'ContinuousAlternatingMap.mk_eq_pairRep_of_classTerm_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.mk_eq_pairRep_of_classTerm_ne_zero

/-- info: 'ContinuousAlternatingMap.classTerm_pairRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.classTerm_pairRep

/-- info: 'ContinuousAlternatingMap.wedge_mul_apply_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_mul_apply_pairs

-- The weighted shuffle sum (2026-09-17, #32): pair j contributes its weight c j.
/-- info: 'ContinuousAlternatingMap.classTerm_pairRep_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.classTerm_pairRep_weighted

/-- info: 'ContinuousAlternatingMap.wedge_mul_apply_weightedPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedge_mul_apply_weightedPairs

-- ContinuousAlternatingMap.continuous_eval_const (a local duplicate of Mathlib's `continuous_eval_const`
-- via the `ContinuousEvalConst` instance) removed 2026-09-16; nothing to pin.

/-- info: 'DifferentialForm.topFormMeasure_ne_zero_of_localRep_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.topFormMeasure_ne_zero_of_localRep_ne_zero

/-- info: 'ContinuousAlternatingMap.wedgePow_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedgePow_smul

/-- info: 'Projectivization.fsModelForm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_zero

/-- info: 'Projectivization.stdForm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.stdForm_single

/-- info: 'Projectivization.im_conj_mul_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.im_conj_mul_pairs

/-- info: 'ContinuousAlternatingMap.coe_powEquiv_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.coe_powEquiv_inl

/-- info: 'ContinuousAlternatingMap.coe_powEquiv_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.coe_powEquiv_inr

/-- info: 'ContinuousAlternatingMap.pairIdx_powEquiv_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.pairIdx_powEquiv_inl

/-- info: 'ContinuousAlternatingMap.memIdx_powEquiv_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.memIdx_powEquiv_inl

/-- info: 'ContinuousAlternatingMap.pairIdx_powEquiv_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.pairIdx_powEquiv_inr

/-- info: 'ContinuousAlternatingMap.memIdx_powEquiv_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.memIdx_powEquiv_inr

-- WedgePowPairs (2026-09-17, #32): the top power of a real 2-form on a WEIGHTED pair tuple
-- (β = ± c j within pair j, 0 across pairs) is k! · ∏ c j — the shuffle sum on a weighted pair
-- family, each pair moved into the last two slots in turn. Foundational triple.
/-- info: 'ContinuousAlternatingMap.pairIdx_powEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.pairIdx_powEquiv

/-- info: 'ContinuousAlternatingMap.memIdx_powEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.memIdx_powEquiv

/-- info: 'ContinuousAlternatingMap.IsWeightedPairTuple.pairRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.IsWeightedPairTuple.pairRep

/-- info: 'ContinuousAlternatingMap.wedgePow_apply_of_isWeightedPairTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedgePow_apply_of_isWeightedPairTuple

/-- info: 'ContinuousAlternatingMap.wedgePow_apply_of_isPairTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.wedgePow_apply_of_isPairTuple

/-- info: 'Projectivization.isWeightedPairTuple_pairFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isWeightedPairTuple_pairFamily

/-- info: 'Projectivization.wedgePow_stdForm_pairFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_stdForm_pairFamily

/-- info: 'Projectivization.stdBasis_eq_pairFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.stdBasis_eq_pairFamily

/-- info: 'Projectivization.wedgePow_fsModelForm_zero_stdBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_fsModelForm_zero_stdBasis

/-- info: 'Projectivization.wedgePow_fsModelForm_zero_stdBasis_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_fsModelForm_zero_stdBasis_ne_zero

/-- info: 'Projectivization.fsVolume_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_ne_zero

/-- info: 'Projectivization.isProbabilityMeasure_fsVolumeNormalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isProbabilityMeasure_fsVolumeNormalized

/-- info: 'Projectivization.fsVolumeNormalized_eq_fsMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolumeNormalized_eq_fsMeasure

/-! ### M7: the constant -- the mass of the Fubini-Study volume is (4π)^n (JapaneseBracketIntegral.lean, ProjectiveSpaceFubiniStudyMass.lean, 2026-09-08; 30 pins) -/

-- Milestone M7 of specs/top-power-scoping.md, the last one. Analytic half
-- (Analysis/SpecialFunctions/JapaneseBracketIntegral.lean; upstream has integrability of the
-- Japanese bracket, never a value): the radial integral by the fundamental theorem of calculus on
-- [0, ∞), the planar integral by polar coordinates, and ★★ lintegral_pi_pow_inv_one_add_sum_norm_sq,
-- ∫_{ℂⁿ} (1 + ∑|wⱼ|²)^{-(n+1)} = πⁿ/n!, by splitting one coordinate off (piFinSuccAbove) and
-- induction. Geometric half (Instances/ProjectiveSpaceFubiniStudyMass.lean): the density of the
-- top power EVERYWHERE on the chart -- rotate w to the first axis by a unitary matrix (the real
-- determinant of a complex matrix is |det|², LinearMap.det_restrictScalars + Algebra.norm_complex_apply,
-- so a unitary has Jacobian 1), where the model form is the diagonal pullback
-- diag(t⁻¹, t^{-1/2}, …) of the form at the origin, hence by the Jacobian rule and the M6(b) count
-- ★★ wedgePow_fsModelForm_stdBasis = (-4)ⁿ n! (1+‖w‖²)^{-(n+1)}; the hyperplane z₀ = 0 is null (a
-- coordinate hyperplane in every other chart, addHaar_submodule), so the mass is one chart integral;
-- ★★ fsVolume_univ = (4π)ⁿ; and ★★★ fsVolume_eq_smul_fsMeasure:
-- fsVolume n = (4π)ⁿ • fsMeasure p₀ -- THE TOP POWER OF THE FUBINI-STUDY FORM IS THE
-- FUBINI-STUDY MEASURE, with its constant. The (4π)ⁿ is convention-bound (the chart form carries
-- the potential's -4, the wedge its own normalisation); every factor is visible in the statement.
-- Every milestone of the scoping note is now built.

/-- info: 'MeasureTheory.hasDerivAt_bracketAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.hasDerivAt_bracketAnti

/-- info: 'MeasureTheory.continuous_bracketAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.continuous_bracketAnti

/-- info: 'MeasureTheory.tendsto_bracketAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.tendsto_bracketAnti

/-- info: 'MeasureTheory.integrableOn_Ioi_mul_pow_inv_add_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.integrableOn_Ioi_mul_pow_inv_add_sq

/-- info: 'MeasureTheory.integral_Ioi_mul_pow_inv_add_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.integral_Ioi_mul_pow_inv_add_sq

/-- info: 'MeasureTheory.lintegral_complex_pow_inv_add_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.lintegral_complex_pow_inv_add_norm_sq

/-- info: 'MeasureTheory.lintegral_pi_pow_inv_one_add_sum_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.lintegral_pi_pow_inv_one_add_sum_norm_sq

/-- info: 'Projectivization.mulVecCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mulVecCLM_apply

/-- info: 'Projectivization.det_mulVecCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_mulVecCLM

/-- info: 'Projectivization.normSq_det_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.normSq_det_unitary

/-- info: 'Projectivization.norm_toEuclideanLin_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_toEuclideanLin_unitary

/-- info: 'Projectivization.toLpCLM_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.toLpCLM_mulVec

/-- info: 'Projectivization.toLpCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.toLpCLM_apply

/-- info: 'Projectivization.fsModelForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_apply

/-- info: 'Projectivization.fsModelForm_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_mulVec

/-- info: 'Projectivization.fsScale_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsScale_mulVec_apply

/-- info: 'Projectivization.fsScaleEntry_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsScaleEntry_mul_self

/-- info: 'Projectivization.inner_fsScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.inner_fsScale

/-- info: 'Projectivization.fsModelForm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_single

/-- info: 'Projectivization.normSq_det_fsScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.normSq_det_fsScale

-- ★ fsModelForm_eq_comp (2026-09-17, #32): the model form at every w is the pullback of the model
-- form at the origin along a real linear map of determinant (1 + ‖w‖²)^{-(n+1)}.
/-- info: 'Projectivization.fsModelForm_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_eq_comp

/-- info: 'Projectivization.wedgePow_fsModelForm_stdBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_fsModelForm_stdBasis

/-- info: 'Projectivization.chartDensity_fsTopForm_origin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartDensity_fsTopForm_origin_zero

/-- info: 'Projectivization.chartAt_origin_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartAt_origin_source

/-- info: 'Projectivization.chartAt_origin_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartAt_origin_symm

/-- info: 'Projectivization.fsVolume_chartSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_chartSource_zero

/-- info: 'Projectivization.fsVolume_compl_chartSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_compl_chartSource_zero

/-- info: 'Projectivization.fsVolume_univ_eq_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_univ_eq_lintegral

/-- info: 'Projectivization.fsVolume_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_univ

/-- info: 'Projectivization.fsVolume_eq_smul_fsMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_eq_smul_fsMeasure

/-- info: 'Projectivization.measurable_chartDensity_fsTopForm_origin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.measurable_chartDensity_fsTopForm_origin_zero

-- ★ The hyperplane z₀ = 0 is null for fsMeasure too (2026-09-17, #32).
/-- info: 'Projectivization.fsMeasure_compl_chartSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsMeasure_compl_chartSource_zero

/-- info: 'Projectivization.fsMeasure_chartSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsMeasure_chartSource_zero

-- ProjectiveSpaceTorusVolume (2026-09-17, #32): THE VOLUME OF ℂℙⁿ × T². The product basis is a
-- weighted pair tuple for π₁^*(-4 ω_std) + π₂^*(dθ₁ ∧ dθ₂) (weights -4 on the n sector pairs,
-- 1 on the torus pair), so the top power of π₁^* ω_FS + π₂^*(dθ₁ ∧ dθ₂) has coefficient
-- (-4)ⁿ (n+1)! (1 + ‖w‖²)^{-(n+1)} on the product chart — (n+1) times the Fubini–Study density —
-- and its measure on a product chart domain is (n+1)(4π)ⁿ · T T' (Tonelli, fsVolume_univ, the
-- torus chart area). Foundational triple.
/-- info: 'Projectivization.isWeightedPairTuple_prodTorusBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isWeightedPairTuple_prodTorusBasis

/-- info: 'Projectivization.wedgePow_prodSum_stdForm_areaForm_prodTorusBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_prodSum_stdForm_areaForm_prodTorusBasis

/-- info: 'Projectivization.wedgePow_prodSum_fsModelForm_areaForm_prodTorusBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wedgePow_prodSum_fsModelForm_areaForm_prodTorusBasis

/-- info: 'Projectivization.chartDensity_prodTorus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartDensity_prodTorus

/-- info: 'AddCircle.volume_compl_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddCircle.volume_compl_singleton

/-- info: 'Projectivization.topFormMeasure_prodTorus_chartAt_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.topFormMeasure_prodTorus_chartAt_source

/-- info: 'Projectivization.topFormMeasure_prodTorus_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.topFormMeasure_prodTorus_ne_zero

/-! ### G1: Hamiltonian vector fields on a manifold -- the defining equation (HamiltonianVectorField.lean, 2026-09-08) -/

-- Brick G1 of specs/generator-layer-scoping.md. `IsHamiltonianVectorField α X H` is the
-- equation `α x (X x, v) = mfderiv H x v` at every point, for a 2-form FAMILY α and a vector
-- field FAMILY X (no smoothness asserted or needed); `IsLocallyHamiltonian α X` is `d (ι_X α) = 0`
-- (the notion the flux correction of RecordLayer/PiecewiseHamiltonian.lean needs -- meaningful
-- when the family is smooth, brick G3). `interiorProduct` is `curryLeft` pointwise, forced onto
-- the model space E because `TangentSpace` carries no normed instance at the pin. What follows
-- from the equation by alternation and linearity alone: ★ dH (X) = 0 (energy conserved along its
-- own field), ★ uniqueness of X_H where α is non-degenerate, hence for a symplectic form
-- (`unique_of_isSymplectic`), and linearity in H. ⚠️ NO existence (G2/G3), NO "Hamiltonian ⇒
-- locally Hamiltonian" (needs `mextDeriv` of a 0-form = `mfderiv`, first item of G3), NO
-- inhabitant on CP^n (G6, the moment map of the torus action).

/-- info: 'DifferentialForm.interiorProduct_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.interiorProduct_apply

/-- info: 'DifferentialForm.curryLeft_apply_vecCons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.curryLeft_apply_vecCons

/-- info: 'DifferentialForm.apply_sub_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_sub_left

/-- info: 'DifferentialForm.apply_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_add_left

/-- info: 'DifferentialForm.apply_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_smul_left

/-- info: 'DifferentialForm.apply_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_zero_left

/-- info: 'DifferentialForm.IsHamiltonianVectorField.interiorProduct_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.interiorProduct_eq

/-- info: 'DifferentialForm.IsHamiltonianVectorField.mfderiv_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.mfderiv_apply_self

/-- info: 'DifferentialForm.IsHamiltonianVectorField.eq_of_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.eq_of_nondegenerate

/-- info: 'DifferentialForm.IsHamiltonianVectorField.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.add

/-- info: 'DifferentialForm.IsHamiltonianVectorField.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.smul

/-- info: 'DifferentialForm.IsHamiltonianVectorField.const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.const

/-- info: 'DifferentialForm.IsHamiltonianVectorField.unique_of_isSymplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.unique_of_isSymplectic

/-! ### G6: the moment map of the torus action on CP^n, at manifold level (ProjectiveSpaceMomentMap.lean, 2026-09-08) -/

-- Brick G6 of specs/generator-layer-scoping.md. The torus acts on CP^n by p ↦ diag(e^{iθ}) • p; in
-- the affine chart i this is the coordinatewise phase rotation w_j ↦ e^{i(θ_{s j} − θ_i)} w_j
-- (chartFun_torusUnitary_smul), whose t-derivative at 0 is the explicit field
-- torusChartField (★ hasDerivAt_chartFun_torusUnitary — so torusField IS the fundamental vector
-- field of the action, not a field named after it). The Hamiltonian is torusHamiltonian θ p =
-- 2 ∑ θ_k · CSD.LF4.momentMap p k, the corpus's cell law; its chart expression is the rational
-- function 2N/D with N = θ_i + ∑ θ_{s j}|w_j|², D = 1 + ∑|w_j|², differentiated by the product and
-- inverse rules (no quotient rule at the pin for HasFDerivAt), and ★ hasMFDerivAt_torusHamiltonian
-- reads the manifold derivative off the chart. The whole content is the chart identity ★★
-- fsModelForm_torusChartField, ω_w(X_w, v) = dH_w v, a real computation through fsModelForm_apply
-- (M7). Result: ★★★ torusField_isHamiltonianVectorField — THE TORUS ACTION ON CP^n IS HAMILTONIAN
-- FOR THE FUBINI-STUDY FORM, WITH 2 ∑ θ_k momentMap AS ITS HAMILTONIAN: the moment-map equation of
-- the corpus's most load-bearing object, at manifold level. ⚠️ The factor 2 is the -4 convention of
-- fsChartForm. ⚠️ A family, not a smooth section (G3). ⚠️ Not the convexity statement. ⚠️ Torus only.

/-- info: 'Projectivization.chartDen_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartDen_pos

/-- info: 'Projectivization.normSqCoordDeriv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.normSqCoordDeriv_apply

/-- info: 'Projectivization.hasFDerivAt_normSq_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_normSq_coord

/-- info: 'Projectivization.hasFDerivAt_torusChartNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_torusChartNum

/-- info: 'Projectivization.hasFDerivAt_chartDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_chartDen

/-- info: 'Projectivization.hasFDerivAt_torusChartHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_torusChartHam

/-- info: 'Projectivization.torusChartHamDeriv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusChartHamDeriv_apply

/-- info: 'Projectivization.fsModelForm_torusChartField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_torusChartField

/-- info: 'Projectivization.continuous_torusHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.continuous_torusHamiltonian

/-- info: 'Projectivization.torusHamiltonian_chartInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusHamiltonian_chartInv

/-- info: 'Projectivization.hasMFDerivAt_torusHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasMFDerivAt_torusHamiltonian

/-- info: 'Projectivization.torusField_isHamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusField_isHamiltonianVectorField

/-- info: 'Projectivization.torusUnitary_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusUnitary_val

/-- info: 'Projectivization.chartFun_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartFun_torusUnitary_smul

/-- info: 'Projectivization.hasDerivAt_chartFun_torusUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasDerivAt_chartFun_torusUnitary

/-! ### G8: a moment map is unique up to a constant, and the normalisation pins it (HamiltonianVectorField.lean, ProjectiveSpaceMomentMap.lean, 2026-09-08) -/

-- Brick G8 of specs/generator-layer-scoping.md §8. (A) ★★ eq_add_const_of_isHamiltonianVectorField:
-- on CP^n two MDifferentiable Hamiltonians of the same field for the same 2-form family differ by
-- a constant. NO connectedness lemma: their difference has zero mfderiv (mfderiv_eq, a CLM
-- extensionality), which in the chart at origin i is a zero fderiv of D ∘ chartInv i on ALL of
-- Fin n → ℂ (mfderiv_comp with the chart inverse, mfderiv_eq_fderiv), so Mathlib's
-- is_const_of_fderiv_eq_zero makes D constant on each chart domain, and the point [1 : ⋯ : 1]
-- (allOnes) lies in every chart domain, so the constants agree. (B) ★★★
-- eq_torusHamiltonian_of_nonneg_of_sum: a family of Hamiltonians for the phase fields
-- torusField (Pi.single k 1), non-negative and summing to 2 (the form's scale), IS
-- 2 · momentMap: by (A) and G6 each is 2 μ_k + c_k; momentMap_sum_eq_one gives ∑ c_k = 0;
-- μ_k vanishes at the chart origin j ≠ k (momentMap_origin_of_ne), so c_k ≥ 0; hence all c_k = 0
-- (n = 0 by the one-term sum). This is the "standard symplectic argument, unformalised" of
-- specs/POSITS.md bullet 1, formalised. ⚠️ POSIT 1 IS UNCHANGED: it asserts that the DYNAMICS
-- is the source of the torus action; G8 says only which map that action has.

/-- info: 'DifferentialForm.IsHamiltonianVectorField.mfderiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.mfderiv_eq

/-- info: 'Projectivization.chartAt_origin_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartAt_origin_target

/-- info: 'Projectivization.allOnes_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.allOnes_ne_zero

/-- info: 'Projectivization.mk_allOnes_mem_chartSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_allOnes_mem_chartSource

/-- info: 'Projectivization.momentMap_origin_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.momentMap_origin_of_ne

/-- info: 'Projectivization.torusHamiltonian_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusHamiltonian_single

/-- info: 'Projectivization.mdifferentiable_torusHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mdifferentiable_torusHamiltonian

/-- info: 'Projectivization.eq_add_const_of_isHamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_add_const_of_isHamiltonianVectorField

/-- info: 'Projectivization.eq_torusHamiltonian_of_nonneg_of_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_torusHamiltonian_of_nonneg_of_sum

/-! ### G9 + G10: the image of the moment map is the simplex; the torus flow preserves the Fubini-Study volume (ProjectiveSpaceMomentMap.lean, 2026-09-09) -/

-- Bricks G9 and G10 of specs/generator-layer-scoping.md §8. G9: ★★ range_momentMap — the image
-- of momentMap on CP^n is EXACTLY stdSimplex ℝ (Fin (n+1)): ⊆ is momentMap_nonneg +
-- momentMap_sum_eq_one (momentMap_mem_stdSimplex); ⊇ is the ray of (√t₀, …, √tₙ) (sqrtVec,
-- momentMap_mk_sqrtVec). The image polytope of THIS action by direct computation; the
-- Atiyah–Guillemin–Sternberg convexity theorem is neither used nor proved. G10: ★
-- fsVolume_map_torusUnitary_smul — every map p ↦ diag(e^{iθ}) • p, hence every time-t map of the
-- flow G6 built (torusUnitary_add_smul is its group law), preserves fsVolume n: a one-line
-- corollary of fsVolume_map_smul, also as MeasurePreserving. Liouville in the dynamics sense for
-- this ONE flow; no manifold-level flow theory (G5 stays unscheduled), and Posit 3 (the constraint
-- dynamics preserves μL) is untouched — the measurement pieces are not globally Hamiltonian.

/-- info: 'Projectivization.momentMap_mem_stdSimplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.momentMap_mem_stdSimplex

/-- info: 'Projectivization.norm_sqrtVec_apply_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sqrtVec_apply_sq

/-- info: 'Projectivization.norm_sqrtVec_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sqrtVec_sq

/-- info: 'Projectivization.sqrtVec_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.sqrtVec_ne_zero

/-- info: 'Projectivization.momentMap_mk_sqrtVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.momentMap_mk_sqrtVec

/-- info: 'Projectivization.range_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.range_momentMap

/-- info: 'Projectivization.torusUnitary_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusUnitary_zero

/-- info: 'Projectivization.torusUnitary_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusUnitary_add

/-- info: 'Projectivization.torusUnitary_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusUnitary_add_smul

/-- info: 'Projectivization.fsVolume_map_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_map_torusUnitary_smul

/-- info: 'Projectivization.measurePreserving_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.measurePreserving_torusUnitary_smul

/-! ### G11: Hamiltonian implies locally Hamiltonian, via d of a 0-form (ExteriorDerivative.lean, HamiltonianVectorField.lean, 2026-09-09) -/

-- Brick G11 of specs/generator-layer-scoping.md §8. The 0-form API that ExteriorDerivative.lean's
-- header listed as "not here": zeroFormFamily f (a function as a 0-form family, x ↦ constOfIsEmpty
-- (f x)), its local representative (the function read in the chart, via trivializationAt_snd —
-- compContinuousLinearMap is invisible on an empty index), its smoothness as a section
-- (contMDiffAt_section + constOfIsEmptyLIE ∘ f), and ★ toFlat_mextDerivFamily_zeroFormFamily: d of a
-- 0-form IS its differential, (df)_x = ofSubsingleton 0 (mfderiv f x), transported from Mathlib's
-- extDeriv_constOfIsEmpty with the chart bridge MDifferentiableAt.mfderiv + writtenInExtChartAt on
-- the boundaryless model. Then ★ IsHamiltonianVectorField.isLocallyHamiltonian: ι_X α = dH as
-- families (pointwise, through toFlat — never a rw across the TangentSpace/Trivial instance
-- path), so d(ι_X α) = d(dH) = 0 by mextDeriv_mextDeriv, for a C^∞ energy. The converse is
-- FALSE and not stated (closed-not-exact = the flux obstruction, RecordLayer/PiecewiseHamiltonian).

/-- info: 'DifferentialForm.trivializationAt_zeroFormFamily_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_zeroFormFamily_snd

/-- info: 'DifferentialForm.localRep_zeroFormFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_zeroFormFamily

/-- info: 'DifferentialForm.contMDiff_zeroFormFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_zeroFormFamily

/-- info: 'DifferentialForm.toFlat_mextDerivFamily_zeroFormFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.toFlat_mextDerivFamily_zeroFormFamily

/-- info: 'DifferentialForm.toFlat_mextDeriv_zeroForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.toFlat_mextDeriv_zeroForm

/-- info: 'DifferentialForm.IsHamiltonianVectorField.interiorProduct_eq_mextDeriv_zeroFormFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.interiorProduct_eq_mextDeriv_zeroFormFamily

/-- info: 'DifferentialForm.IsHamiltonianVectorField.isLocallyHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.isLocallyHamiltonian

/-! ### G13: the Schrödinger flow on CP^n is Hamiltonian, with Hamiltonian -2 ⟨H⟩ (ProjectiveSpaceSchrodingerFlow.lean, 2026-09-09) -/

-- Brick G13 of specs/generator-layer-scoping.md §8, the U(n+1) moment map. For a Hermitian H,
-- ★★★ schrodingerField_isHamiltonianVectorField: the velocity field of p ↦ exp(-itH) • p — the
-- corpus's projected Schrödinger flow, and proved to be that velocity
-- (hasDerivAt_chartFun_schrodingerUnitary, through Matrix.schrodingerUnitary_hasDerivAt under the
-- L2Operator norm and a matrix-entry functional) — satisfies ι_X ω_FS = dH on the MANIFOLD with
-- H = schrodingerHamiltonian = -2 ⟨H⟩ = -2 ⟪z, Hz⟫.re/‖z‖². The chart identity
-- (★★ fsModelForm_schrodingerChartField) is proved in the AMBIENT inner product, not by coordinate
-- sums as G6 was: the chart tangent lift insertZeroCLM preserves the inner products the model
-- form is written in, the lifted velocity is -i (Hv - (Hv)_i v), the (Hv)_i terms cancel, and what
-- remains is Im (i z) = Re z plus the symmetry of H (isSymmetric_toEuclideanLin_iff). The chart
-- Hamiltonian is differentiated by HasFDerivAt.inner along the affine lift. G6's torus is the
-- diagonal case: schrodingerChartField_neg_diagonal, schrodingerHamiltonian_neg_diagonal. The sign
-- and the factor 2 are the -4 convention of fsChartForm plus the corpus's exp(-itH). Posit 1 is
-- untouched (which Hamiltonian a GIVEN flow has, not what generates it).

/-- info: 'Projectivization.expectation_ratio_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.expectation_ratio_smul

/-- info: 'Projectivization.expectation_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.expectation_mk

/-- info: 'Projectivization.continuous_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.continuous_expectation

/-- info: 'Projectivization.continuous_schrodingerHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.continuous_schrodingerHamiltonian

/-- info: 'Projectivization.insertZeroCLM_apply_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertZeroCLM_apply_same

/-- info: 'Projectivization.insertZeroCLM_apply_succAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertZeroCLM_apply_succAbove

/-- info: 'Projectivization.insertOne_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertOne_eq_add

/-- info: 'Projectivization.hasFDerivAt_insertOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_insertOne

/-- info: 'Projectivization.inner_insertZeroCLM_insertZeroCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.inner_insertZeroCLM_insertZeroCLM

/-- info: 'Projectivization.inner_insertZeroCLM_insertOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.inner_insertZeroCLM_insertOne

/-- info: 'Projectivization.inner_insertOne_insertZeroCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.inner_insertOne_insertZeroCLM

/-- info: 'Projectivization.norm_sq_insertOne_toLpCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sq_insertOne_toLpCLM

/-- info: 'Projectivization.insertZeroCLM_schrodingerChartField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertZeroCLM_schrodingerChartField

/-- info: 'Projectivization.schrodingerHamiltonian_chartInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerHamiltonian_chartInv

/-- info: 'Projectivization.norm_sq_insertOne_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.norm_sq_insertOne_pos

/-- info: 'Projectivization.hasFDerivAt_schrodingerChartHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_schrodingerChartHam

/-- info: 'Projectivization.schrodingerChartHamDeriv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerChartHamDeriv_apply

/-- info: 'Projectivization.fsModelForm_schrodingerChartField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_schrodingerChartField

/-- info: 'Projectivization.hasMFDerivAt_schrodingerHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasMFDerivAt_schrodingerHamiltonian

/-- info: 'Projectivization.schrodingerField_isHamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerField_isHamiltonianVectorField

/-- info: 'Projectivization.mulVecEntryCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mulVecEntryCLM_apply

/-- info: 'Projectivization.schrodingerUnitary_zero_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerUnitary_zero_val

/-- info: 'Projectivization.hasDerivAt_chartFun_schrodingerUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasDerivAt_chartFun_schrodingerUnitary

/-- info: 'Projectivization.schrodingerChartField_neg_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerChartField_neg_diagonal

/-- info: 'Projectivization.schrodingerHamiltonian_neg_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerHamiltonian_neg_diagonal

/-! ### G2: existence and uniqueness of the Hamiltonian vector field from non-degeneracy (HamiltonianVectorField.lean, ProjectiveSpaceSchrodingerFlow.lean, 2026-09-09) -/

-- Brick G2 of specs/generator-layer-scoping.md. Pointwise, finite-dimensional linear algebra:
-- flatAt α x : E →ₗ[ℝ] Module.Dual ℝ E is v ↦ α x (v, ·) (LinearMap.mk₂ on the four slot-linearity
-- lemmas; the right-slot ones come from map_update_add/smul through update_vecCons_one);
-- non-degeneracy at x is exactly its injectivity, so with Subspace.dual_finrank_eq it is a
-- LinearEquiv (LinearMap.linearEquivOfInjective) and hamiltonianVectorAt α x hnd L := (ω♭ₓ)⁻¹ L is
-- THE vector with α x (X_L, w) = L w (★ apply_hamiltonianVectorAt; eq_hamiltonianVectorAt). Then
-- ★★ hamiltonianVectorField α hnd H := x ↦ (ω♭ₓ)⁻¹ (dH_x) with
-- hamiltonianVectorField_isHamiltonianVectorField (EXISTENCE) and
-- IsHamiltonianVectorField.eq_hamiltonianVectorField (UNIQUENESS); IsSymplectic.hamiltonianVectorField
-- specialises to a symplectic form. Corollaries on CP^n: the torus field (G6) and the Schrödinger
-- field (G13) are THE Hamiltonian vector fields of their Hamiltonians for fsForm. Pointwise only:
-- smoothness of the constructed family as a section is G3, not here. Every rw across the
-- TangentSpace/E instance path was replaced by exact/trans (the module-system trap again).

/-- info: 'DifferentialForm.update_vecCons_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.update_vecCons_one

/-- info: 'DifferentialForm.apply_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_add_right

/-- info: 'DifferentialForm.apply_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_smul_right

/-- info: 'DifferentialForm.flatAt_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatAt_apply

/-- info: 'DifferentialForm.flatAt_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatAt_injective

/-- info: 'DifferentialForm.flatEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatEquiv_apply

/-- info: 'DifferentialForm.apply_hamiltonianVectorAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_hamiltonianVectorAt

/-- info: 'DifferentialForm.eq_hamiltonianVectorAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.eq_hamiltonianVectorAt

/-- info: 'DifferentialForm.hamiltonianVectorField_isHamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.hamiltonianVectorField_isHamiltonianVectorField

/-- info: 'DifferentialForm.IsHamiltonianVectorField.eq_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.eq_hamiltonianVectorField

/-- info: 'DifferentialForm.IsSymplectic.hamiltonianVectorField_isHamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.hamiltonianVectorField_isHamiltonianVectorField

/-- info: 'DifferentialForm.IsHamiltonianVectorField.eq_isSymplectic_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.eq_isSymplectic_hamiltonianVectorField

/-- info: 'Projectivization.torusField_eq_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusField_eq_hamiltonianVectorField

/-- info: 'Projectivization.schrodingerField_eq_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerField_eq_hamiltonianVectorField

/-! ### G3: the Hamiltonian vector field is a C^∞ section (HamiltonianVectorField.lean, ProjectiveSpaceSchrodingerFlow.lean, 2026-09-09) -/

-- Brick G3 of specs/generator-layer-scoping.md. ★★★ contMDiff_hamiltonianVectorField: for a C^∞
-- 2-form family non-degenerate everywhere and a C^∞ energy, G2's field x ↦ (ω♭ₓ)⁻¹ (dH_x) is a C^∞
-- section of the tangent bundle. Route (the VectorBundle/Hom pattern): in the tangent
-- trivialisation at x₀ the field is localHamiltonianVector — ContinuousLinearMap.inverse of
-- curryLeft (localRep α x₀ w) applied to ofSubsingletonLIE (fderiv (H ∘ chart⁻¹) w) — by uniqueness
-- at the flat level (★★ trivializationAt_hamiltonianVectorField_snd: the trivialisation intertwines
-- α with its local representative, trivializationAt_snd, and dH with the chart derivative,
-- mfderiv_comp); the local representative is non-degenerate on the chart target
-- (localRep_nondegenerate, through symmL/continuousLinearMapAt); and ★★
-- contDiffAt_localHamiltonianVector is contDiffAt_map_inverse at the invertible point (flatCLE:
-- G2's flatEquiv on the model, made continuous by finite dimension), curryLeft a bounded linear map,
-- contDiffAt_localRep, and fderiv_right. Corollaries on CP^n: both Hamiltonians are C^∞
-- (inner-product calculus in the chart, contMDiffAt_iff), so the torus field (G6) and the
-- Schrödinger field (G13) are C^∞ vector fields. Shelf facts: the alternating-map space has no
-- FiniteDimensional instance and `→L` types over it pick the raw topological-module instances, so
-- the flat map is stated through curryLeft and boundedness, never as a CLM on that space; a
-- constant family `fun _ => ξ` must be wrapped (flatFamily) to be syntactically fibre-typed.

/-- info: 'DifferentialForm.flatFamily_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatFamily_nondegenerate

/-- info: 'DifferentialForm.apply_flatVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_flatVec

/-- info: 'DifferentialForm.eq_flatVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.eq_flatVec

/-- info: 'DifferentialForm.flatCLE_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatCLE_apply

/-- info: 'DifferentialForm.coe_flatCLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.coe_flatCLE

/-- info: 'DifferentialForm.inverse_curryLeft_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.inverse_curryLeft_apply

/-- info: 'DifferentialForm.localRep_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.localRep_nondegenerate

/-- info: 'DifferentialForm.trivializationAt_hamiltonianVectorField_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.trivializationAt_hamiltonianVectorField_snd

/-- info: 'DifferentialForm.contDiffAt_localHamiltonianVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contDiffAt_localHamiltonianVector

/-- info: 'DifferentialForm.contMDiff_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_hamiltonianVectorField

-- B11′ (2026-09-17): one smoothness proof at every infinite order; ∞ and ω are corollaries.

/-- info: 'DifferentialForm.contDiffAt_localHamiltonianVector_of_contMDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contDiffAt_localHamiltonianVector_of_contMDiff

/-- info: 'DifferentialForm.contMDiff_hamiltonianVectorField_of_contMDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_hamiltonianVectorField_of_contMDiff

/-- info: 'Projectivization.contMDiff_schrodingerField_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_schrodingerField_of_le

/-- info: 'Projectivization.contMDiff_torusField_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_torusField_of_le

/-- info: 'DifferentialForm.IsSymplectic.contMDiff_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.contMDiff_hamiltonianVectorField

/-- info: 'Projectivization.contDiff_schrodingerChartHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_schrodingerChartHam

/-- info: 'Projectivization.contMDiff_schrodingerHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_schrodingerHamiltonian

/-- info: 'Projectivization.contMDiff_torusHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_torusHamiltonian

/-- info: 'Projectivization.contMDiff_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_schrodingerField

/-- info: 'Projectivization.contMDiff_torusField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_torusField

/-! ### G4: integral curves -- existence, uniqueness, energy conservation; the Schrödinger flow is one (HamiltonianVectorField.lean, ProjectiveSpaceSchrodingerFlow.lean, 2026-09-09) -/

-- Brick G4 of specs/generator-layer-scoping.md. Generic: ★ hasDerivAt_comp_of_isMIntegralCurve
-- (H ∘ γ has zero derivative along an integral curve of a Hamiltonian vector field of H, by G1's
-- dH (X) = 0), ★★ comp_eq_of_isMIntegralCurve (ENERGY CONSERVATION, is_const_of_deriv_eq_zero), ★★
-- exists_isMIntegralCurveAt_hamiltonianVectorField (LOCAL EXISTENCE: Picard–Lindelöf in the chart,
-- exists_isMIntegralCurveAt_of_contMDiffAt on the C^1 section G3 provides, boundaryless model), ★★
-- isMIntegralCurve_hamiltonianVectorField_eq (UNIQUENESS of global integral curves on a Hausdorff
-- manifold, isMIntegralCurve_eq_of_contMDiff); the IsSymplectic forms specialise. On CP^n: the same
-- three for schrodingerField, ★★ expectation_eq_of_isMIntegralCurve_schrodingerField (⟨H⟩ is
-- conserved along every integral curve), and ★★★ isMIntegralCurve_schrodingerUnitary_smul — THE
-- SCHRÖDINGER FLOW t ↦ exp(-itH) • p IS THE INTEGRAL CURVE OF ITS FIELD: in the chart at
-- exp(-itH) • p the curve is s ↦ chartFun (exp(-i(s-t)H) • q) by the group law
-- expNegITH_unitary_group, whose derivative at s = t is the chart velocity of G13
-- (hasDerivAt_chartFun_schrodingerUnitary) through the scalar chain rule; continuity from
-- schrodingerUnitary_hasDerivAt and the ContinuousSMul instance. Hence ★★
-- expectation_schrodingerUnitary_smul: ⟨H⟩ is conserved by the flow. NOT stated: a global flow of
-- a general Hamiltonian field (no flows on manifolds in Mathlib — G5's wall), and the torus orbits
-- (would follow the same way from hasDerivAt_chartFun_torusUnitary + torusUnitary_add_smul).

/-- info: 'DifferentialForm.IsHamiltonianVectorField.hasDerivAt_comp_of_isMIntegralCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.hasDerivAt_comp_of_isMIntegralCurve

/-- info: 'DifferentialForm.IsHamiltonianVectorField.comp_eq_of_isMIntegralCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsHamiltonianVectorField.comp_eq_of_isMIntegralCurve

/-- info: 'DifferentialForm.exists_isMIntegralCurveAt_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.exists_isMIntegralCurveAt_hamiltonianVectorField

/-- info: 'DifferentialForm.isMIntegralCurve_hamiltonianVectorField_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.isMIntegralCurve_hamiltonianVectorField_eq

/-- info: 'DifferentialForm.IsSymplectic.exists_isMIntegralCurveAt_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.exists_isMIntegralCurveAt_hamiltonianVectorField

/-- info: 'DifferentialForm.IsSymplectic.isMIntegralCurve_hamiltonianVectorField_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.isMIntegralCurve_hamiltonianVectorField_eq

/-- info: 'DifferentialForm.IsSymplectic.comp_eq_of_isMIntegralCurve_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.comp_eq_of_isMIntegralCurve_hamiltonianVectorField

/-- info: 'Projectivization.schrodingerUnitary_zero_val'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.schrodingerUnitary_zero_val'

/-- info: 'Projectivization.exists_isMIntegralCurveAt_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_isMIntegralCurveAt_schrodingerField

/-- info: 'Projectivization.isMIntegralCurve_schrodingerField_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isMIntegralCurve_schrodingerField_eq

/-- info: 'Projectivization.expectation_eq_of_isMIntegralCurve_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.expectation_eq_of_isMIntegralCurve_schrodingerField

/-- info: 'Projectivization.isMIntegralCurve_schrodingerUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isMIntegralCurve_schrodingerUnitary_smul

/-- info: 'Projectivization.expectation_schrodingerUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.expectation_schrodingerUnitary_smul

/-! ### G7: the almost Kähler predicate, and CP^n with J = i· as its inhabitant (HamiltonianVectorField.lean, ProjectiveSpaceFubiniStudySymplectic.lean, 2026-09-09) -/

-- Brick G7 of specs/generator-layer-scoping.md. DifferentialForm.IsAlmostKahler β J: a symplectic
-- form with a compatible almost complex structure — J² = -1, J-invariance, and taming
-- β (J v, v) > 0 — whose metric g = β (J ·, ·) is symmetric (metric_comm: J-invariance, J² = -1
-- and the antisymmetry apply_swap, itself from alternation + bilinearity) and positive definite;
-- β = g (·, J ·) (apply_eq_metric). On CP^n: fsJ = i· on each tangent space (through the
-- reducible cast tangentToModel — the tangent space exposes no ℂ-action), fsJ_fsJ, ★
-- fsForm_smul_I_smul_I (the Fubini–Study form is a (1,1)-form, by fsModelForm_apply), and ★★
-- fsForm_isAlmostKahler: CP^n WITH THE FUBINI–STUDY FORM AND J = i· IS ALMOST KÄHLER — the taming
-- is fsSection_smul_I_neg with the sign of the -4 convention absorbed by g = ω (J ·, ·). ★
-- fderiv_chart_transition_smul_I / fsJ_symmL: the chart transitions are holomorphic
-- (contDiffOn_uTrans, chart_transition_eq_uTrans identifies them with uTrans 1), so their
-- derivatives are ℂ-linear and J = i· is the complex structure of the ATLAS, chart-independent.
-- NOT stated: integrability of J as a vanishing Nijenhuis tensor (what "Kähler" adds to "almost
-- Kähler"), J as a smooth section of the endomorphism bundle, and analyticity (G12).

/-- info: 'DifferentialForm.apply_neg_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_neg_left

/-- info: 'DifferentialForm.apply_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.apply_swap

/-- info: 'DifferentialForm.IsAlmostKahler.metric_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsAlmostKahler.metric_comm

/-- info: 'DifferentialForm.IsAlmostKahler.metric_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsAlmostKahler.metric_self_pos

/-- info: 'DifferentialForm.IsAlmostKahler.apply_eq_metric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsAlmostKahler.apply_eq_metric

/-- info: 'Projectivization.fsJ_fsJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsJ_fsJ

/-- info: 'Projectivization.fsModelForm_smul_I_smul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_smul_I_smul_I

/-- info: 'Projectivization.fsForm_smul_I_smul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_smul_I_smul_I

/-- info: 'Projectivization.fsForm_isAlmostKahler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_isAlmostKahler

/-- info: 'Projectivization.fsForm_metric_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_metric_self_pos

/-- info: 'Projectivization.chart_transition_eq_uTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chart_transition_eq_uTrans

/-- info: 'Projectivization.fderiv_chart_transition_smul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fderiv_chart_transition_smul_I

/-- info: 'Projectivization.fsJ_symmL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsJ_symmL

-- G12 (2026-09-10): the Fubini-Study form is analytic. The potential log(1 + |z|^2) is
-- real-analytic (ContDiff.log and contDiff_norm_sq are generic in the order), and every step
-- of the C^infinity chain -- d^c, dd^c, the pullback along toLpCLM, the chart -- is generic in
-- the order too, so the same chain at omega makes fsSection an analytic section:
-- contMDiff_omega_fsForm, and fsFormAnalytic is the section as a term of the omega type.
-- Nothing downstream is restated at omega; fsFormAnalytic_apply is rfl.
/-- info: 'Kahler.contDiff_omega_dcForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.contDiff_omega_dcForm

/-- info: 'Kahler.contDiff_omega_fsPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.contDiff_omega_fsPotential

/-- info: 'Kahler.analyticAt_fsPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kahler.analyticAt_fsPotential

/-- info: 'Projectivization.fsChartForm_eq_alternatizeUncurryFinCLM_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsChartForm_eq_alternatizeUncurryFinCLM_fderiv

/-- info: 'Projectivization.contDiff_omega_fsChartForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_omega_fsChartForm

/-- info: 'Projectivization.contDiff_omega_fsModelForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiff_omega_fsModelForm

/-- info: 'Projectivization.contMDiffAt_omega_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiffAt_omega_fsSection

/-- info: 'Projectivization.contMDiff_omega_fsSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_omega_fsSection

/-- info: 'Projectivization.contMDiff_omega_fsForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_omega_fsForm

/-- info: 'Projectivization.fsFormAnalytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsFormAnalytic

/-- info: 'Projectivization.fsFormAnalytic_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsFormAnalytic_apply

-- G14a (2026-09-10): the Kahler predicate in the atlas sense. IsKahler beta J J0 is
-- IsAlmostKahler plus one field: J is the model's complex structure J0 through the tangent
-- trivialisation of every chart. From it: J y = J0 in y's own chart (apply_eq), and every chart
-- transition has J0-linear derivative (fderiv_chart_transition_comm, the Cauchy-Riemann
-- equations of the atlas) -- the textbook definition of a Kahler manifold. CP^n with the
-- Fubini-Study form and J = i. is one (fsForm_isKahler, from G7's fsJ_symmL). The tensor
-- form of integrability (Nijenhuis) is G14b, queued.
/-- info: 'DifferentialForm.IsAlmostKahler.metric_J_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsAlmostKahler.metric_J_J

/-- info: 'DifferentialForm.IsKahler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler

/-- info: 'DifferentialForm.IsKahler.fderiv_chart_transition_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.fderiv_chart_transition_self

/-- info: 'DifferentialForm.IsKahler.apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.apply_eq

/-- info: 'DifferentialForm.IsKahler.fderiv_chart_transition_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.fderiv_chart_transition_comm

/-- info: 'DifferentialForm.IsKahler.J₀_J₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.J₀_J₀

/-- info: 'Projectivization.modelJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.modelJ

/-- info: 'Projectivization.modelJ_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.modelJ_apply

/-- info: 'Projectivization.fsForm_isKahler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_isKahler

-- B5 (2026-09-17): IsKahler constrains every chart of the atlas; the chartAt form is derived.

/-- info: 'extChartAt_comp_extend_symm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extChartAt_comp_extend_symm_eq

/-- info: 'tangent_localTriv_symmL_eq_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tangent_localTriv_symmL_eq_fderiv

/-- info: 'DifferentialForm.IsKahler.J_symmL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.J_symmL

/-- info: 'DifferentialForm.contMDiff_hom_section_of_localTriv_symmL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_hom_section_of_localTriv_symmL

/-- info: 'DifferentialForm.IsKahler.fderiv_atlas_transition_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.fderiv_atlas_transition_eq

/-- info: 'DifferentialForm.IsKahler.fderiv_atlas_transition_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.fderiv_atlas_transition_comm

/-- info: 'Projectivization.chartAtIdx_transition_eq_uTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartAtIdx_transition_eq_uTrans

/-- info: 'Projectivization.fderiv_chartAtIdx_transition_smul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fderiv_chartAtIdx_transition_smul_I

/-- info: 'Projectivization.fsJ_localTriv_symmL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsJ_localTriv_symmL

-- G15 + G16 (2026-09-10). G15: the complex structure of a Kahler structure, given as continuous
-- linear maps, is a C^infinity section of Hom(TM, TM) -- constant J0 in every chart
-- (IsKahler.contMDiff_hom_section); on CP^n, fsJL and contMDiff_fsJL. G16: the torus orbit
-- t |-> diag(e^{it theta}) . p is THE integral curve of torusField theta (the G4 route with
-- hasDerivAt_chartFun_torusUnitary and the group law), unique through p at 0, and the torus
-- Hamiltonian 2 sum theta_k mu_k is conserved along it and by the flow.
/-- info: 'DifferentialForm.IsKahler.contMDiff_hom_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.contMDiff_hom_section

/-- info: 'Projectivization.fsJL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsJL

/-- info: 'Projectivization.fsJL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsJL_apply

/-- info: 'Projectivization.contMDiff_fsJL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_fsJL

/-- info: 'Projectivization.continuous_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.continuous_torusUnitary_smul

/-- info: 'Projectivization.isMIntegralCurve_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isMIntegralCurve_torusUnitary_smul

/-- info: 'Projectivization.isMIntegralCurve_torusField_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isMIntegralCurve_torusField_eq

/-- info: 'Projectivization.eq_torusUnitary_smul_of_isMIntegralCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_torusUnitary_smul_of_isMIntegralCurve

/-- info: 'Projectivization.torusHamiltonian_eq_of_isMIntegralCurve_torusField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusHamiltonian_eq_of_isMIntegralCurve_torusField

/-- info: 'Projectivization.torusHamiltonian_torusUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.torusHamiltonian_torusUnitary_smul

-- G19 (2026-09-10): the Hamiltonian fields are analytic. G3's chain re-run at omega on an
-- analytic manifold: a C^omega section has C^omega local representatives
-- (contDiffAt_omega_localRep), the local Hamiltonian vector is C^omega (inversion of curryLeft,
-- contDiffAt_map_inverse, is order-generic), so the Hamiltonian vector field of a C^omega energy
-- for a C^omega non-degenerate 2-form is a C^omega section (contMDiff_omega_hamiltonianVectorField;
-- ofOmega reads the omega form as the infinity form G3's constructions are typed on). On CP^n both
-- Hamiltonians are C^omega (the inner-product calculus is order-generic), so the Schrodinger and
-- torus fields are analytic vector fields, for the analytic form fsFormAnalytic of G12.
/-- info: 'DifferentialForm.ofOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.ofOmega

/-- info: 'DifferentialForm.ofOmega_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.ofOmega_apply

/-- info: 'DifferentialForm.contMDiff_omega_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.contMDiff_omega_hamiltonianVectorField

-- The three ω Hamiltonian twins were merged into the order-generic contDiff_schrodingerChartHam /
-- contMDiff_schrodingerHamiltonian / contMDiff_torusHamiltonian on 2026-09-16 (pinned above).
/-- info: 'Projectivization.contMDiff_omega_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_omega_schrodingerField

/-- info: 'Projectivization.contMDiff_omega_torusField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_omega_torusField

-- Q29(e) (2026-09-12): the Schrodinger flow exp(-itH) . p and the torus flow ARE the Hamiltonian
-- flows IsSymplectic.hamiltonianFlow of -2<H> and 2 sum theta_k mu_k (uniqueness of integral
-- curves, integralFlow_eq_of_isMIntegralCurve), so Liouville for the Schrodinger flow follows from
-- the manifold-level theorem fsVolume_map_hamiltonianFlow rather than from unitary invariance.

/-- info: 'Projectivization.hamiltonianFlow_schrodingerHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hamiltonianFlow_schrodingerHamiltonian

/-- info: 'Projectivization.hamiltonianFlow_torusHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hamiltonianFlow_torusHamiltonian

/-- info: 'Projectivization.fsVolume_map_schrodingerUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_map_schrodingerUnitary_smul

/-- info: 'Projectivization.fsVolumeNormalized_map_schrodingerUnitary_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolumeNormalized_map_schrodingerUnitary_smul

-- B12′ (2026-09-17): Lebesgue measure is the standard basis' own Haar measure, so fsVolume is canonical.

/-- info: 'parallelepiped_pi_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parallelepiped_pi_basis

/-- info: 'Complex.volume_parallelepiped_basisOneI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.volume_parallelepiped_basisOneI

/-- info: 'Projectivization.stdBasis_addHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.stdBasis_addHaar

/-- info: 'Projectivization.fsVolume_eq_topFormMeasure_addHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsVolume_eq_topFormMeasure_addHaar

-- B13 (2026-09-17): the Japanese bracket integral on any real inner-product space of dimension 2n.

/-- info: 'Complex.addHaar_pi_basisOneI_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.addHaar_pi_basisOneI_reindex

/-- info: 'Complex.euclideanOrthonormalBasis_toBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.euclideanOrthonormalBasis_toBasis

/-- info: 'Complex.measurePreserving_ofLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.measurePreserving_ofLp

/-- info: 'Complex.lintegral_euclideanSpace_pow_inv_one_add_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.lintegral_euclideanSpace_pow_inv_one_add_norm_sq

/-- info: 'lintegral_pow_inv_one_add_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lintegral_pow_inv_one_add_norm_sq

-- G14b (2026-09-10): Kahler in the tensor sense. nijenhuis J V W is the Nijenhuis tensor
-- [JV, JW] - J[JV, W] - J[V, JW] - [V, W] with Mathlib's manifold Lie bracket mlieBracket; on
-- a Kahler manifold (IsKahler, atlas sense) it vanishes on vector fields differentiable at the
-- point: in the chart at x0 every bracket is the flat bracket of the chart pullbacks
-- (mlieBracketWithin_apply, the chart's derivative being the identity at its base point), J
-- pulls back to the constant J0 (mpullback_extChartAt_symm_apply_J), and the flat expression
-- for a constant J0 with J0^2 = -1 cancels (flat_nijenhuis_eq_zero). The easy direction of
-- Newlander-Nirenberg; the converse is not stated. CP^n: nijenhuis_fsJ_eq_zero.
/-- info: 'DifferentialForm.nijenhuis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.nijenhuis

/-- info: 'DifferentialForm.inverse_mfderiv_extChartAt_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.inverse_mfderiv_extChartAt_symm

/-- info: 'DifferentialForm.flat_nijenhuis_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flat_nijenhuis_eq_zero

/-- info: 'DifferentialForm.flatField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.flatField

/-- info: 'DifferentialForm.IsKahler.mpullback_extChartAt_symm_apply_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.mpullback_extChartAt_symm_apply_J

/-- info: 'DifferentialForm.IsKahler.nijenhuis_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsKahler.nijenhuis_eq_zero

/-- info: 'Projectivization.nijenhuis_fsJ_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.nijenhuis_fsJ_eq_zero

-- G17 (2026-09-11): the Riemannian volume of a metric on a manifold (Geometry/Manifold/
-- RiemannianVolume.lean: chart Gram densities sqrt(det G) glued along a ChartCover, the
-- TopFormMeasure construction with the Gram density in place of the top-form coefficient;
-- riemannianVolume_eq_smul_topFormMeasure is the chart-by-chart bridge to a top-form measure),
-- and on CP^n (Instances/ProjectiveSpaceFubiniStudyRiemannian.lean) the Fubini-Study metric
-- g = omega(J., .) has Gram determinant (4^n (1+|w|^2)^{-(n+1)})^2 against the standard basis
-- (rotate to the first axis by a unitary, scale to the origin where the Gram matrix is 4.1), so
-- its Riemannian chart density is 1/n! times the density of omega^{wedge n}:
-- riemannianVolume_fsMetric (vol_g = fsVolume n / n!, the Kahler identity at the level of
-- measures) and riemannianVolume_fsMetric_eq_smul_fsMeasure (vol_g = ((4 pi)^n/n!) mu_FS:
-- the Fubini-Study measure IS the normalised Riemannian volume of the Fubini-Study metric).
-- No chart-independence theorem for the Gram construction itself (G17b, queued).
/-- info: 'MetricFamily.localRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep

/-- info: 'MetricFamily.gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.gram

/-- info: 'MetricFamily.chartDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartDensity

/-- info: 'MetricFamily.chartMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartMeasure

/-- info: 'MetricFamily.chartMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartMeasure_apply

/-- info: 'MetricFamily.riemannianVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.riemannianVolume

/-- info: 'MetricFamily.riemannianVolume_eq_smul_topFormMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.riemannianVolume_eq_smul_topFormMeasure

/-- info: 'Projectivization.fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsMetric

/-- info: 'Projectivization.fsMetric_eq_metric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsMetric_eq_metric

/-- info: 'Projectivization.fsModelMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelMetric

/-- info: 'Projectivization.fsForm_symmL_symmL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_symmL_symmL

/-- info: 'Projectivization.localRep_fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.localRep_fsMetric

/-- info: 'Projectivization.gram_fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.gram_fsMetric

/-- info: 'Projectivization.mulVecL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mulVecL

/-- info: 'Projectivization.det_mulVecL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_mulVecL

/-- info: 'Projectivization.fsModelMetric_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelMetric_mulVec

/-- info: 'Projectivization.det_toMatrix_fsModelMetric_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_toMatrix_fsModelMetric_mulVec

/-- info: 'Projectivization.fsModelMetric_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelMetric_single

/-- info: 'Projectivization.det_toMatrix_fsModelMetric_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_toMatrix_fsModelMetric_single

/-- info: 'Projectivization.fsModelMetric_zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelMetric_zero_apply

/-- info: 'Projectivization.stdBasis_inner_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.stdBasis_inner_re

/-- info: 'Projectivization.toMatrix_fsModelMetric_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.toMatrix_fsModelMetric_zero

/-- info: 'Projectivization.det_toMatrix_fsModelMetric_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_toMatrix_fsModelMetric_zero

/-- info: 'Projectivization.det_toMatrix_fsModelMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.det_toMatrix_fsModelMetric

/-- info: 'Projectivization.chartDensity_fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartDensity_fsMetric

/-- info: 'Projectivization.riemannianVolume_fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.riemannianVolume_fsMetric

/-- info: 'Projectivization.riemannianVolume_fsMetric_eq_smul_fsMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.riemannianVolume_fsMetric_eq_smul_fsMeasure

-- Q30 / G17b (2026-09-11): the Riemannian volume is canonical. For a bilinear metric family
-- (IsBilinear, four pointwise equations) the local representative pulls back along a chart
-- transition's derivative (localRep_transition), so the Gram matrix transforms by congruence
-- A^T G A and sqrt(det G) by |det A| (chartDensity_transition, the Jacobian rule for Gram
-- densities); change of variables then gives chart-independence (chartMeasure_congr) and
-- cover-independence (riemannianVolume_congr_cover), by the TopFormMeasure proofs with the Gram
-- rule in place of the top-form rule. The Fubini-Study metric is bilinear (isBilinear_fsMetric),
-- so vol_g = fsVolume n / n! for EVERY cover (riemannianVolume_fsMetric_congr_cover).
/-- info: 'MetricFamily.IsBilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.IsBilinear

/-- info: 'MetricFamily.localRep_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep_add_left

/-- info: 'MetricFamily.localRep_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep_smul_left

/-- info: 'MetricFamily.localRep_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep_add_right

/-- info: 'MetricFamily.localRep_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep_smul_right

/-- info: 'MetricFamily.localRepBilin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRepBilin

/-- info: 'MetricFamily.gram_eq_toMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.gram_eq_toMatrix

/-- info: 'MetricFamily.localRep_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.localRep_transition

/-- info: 'MetricFamily.chartDensity_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartDensity_transition

/-- info: 'MetricFamily.chartMeasure_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartMeasure_congr

/-- info: 'MetricFamily.riemannianVolume_apply_of_subset_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.riemannianVolume_apply_of_subset_source

/-- info: 'MetricFamily.riemannianVolume_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.riemannianVolume_congr_cover

-- B9 (2026-09-17): the Riemannian volume of Mathlib's `Bundle.RiemannianMetric` / `ContMDiffRiemannianMetric`.

/-- info: 'Bundle.RiemannianMetric.toMetricFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.toMetricFamily

/-- info: 'Bundle.RiemannianMetric.isBilinear_toMetricFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.isBilinear_toMetricFamily

/-- info: 'Bundle.RiemannianMetric.riemannianVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.riemannianVolume

/-- info: 'Bundle.RiemannianMetric.riemannianVolume_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.riemannianVolume_congr_cover

/-- info: 'Bundle.RiemannianMetric.riemannianVolume_eq_smul_topFormMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.riemannianVolume_eq_smul_topFormMeasure

/-- info: 'Bundle.ContMDiffRiemannianMetric.riemannianVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.ContMDiffRiemannianMetric.riemannianVolume

/-- info: 'Bundle.ContMDiffRiemannianMetric.riemannianVolume_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.ContMDiffRiemannianMetric.riemannianVolume_congr_cover

-- Brief C (2026-09-17): the canonical Riemannian volume (basis' own Haar measure).

/-- info: 'MetricFamily.det_gram_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.det_gram_basis

/-- info: 'MetricFamily.chartDensity_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.chartDensity_basis

/-- info: 'MetricFamily.riemannianVolume_addHaar_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MetricFamily.riemannianVolume_addHaar_basis

/-- info: 'Bundle.RiemannianMetric.canonicalVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.canonicalVolume

/-- info: 'Bundle.RiemannianMetric.canonicalVolume_congr_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.canonicalVolume_congr_basis

/-- info: 'Bundle.RiemannianMetric.canonicalVolume_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.RiemannianMetric.canonicalVolume_congr_cover

/-- info: 'Projectivization.isBilinear_fsMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.isBilinear_fsMetric

/-- info: 'Projectivization.riemannianVolume_fsMetric_congr_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.riemannianVolume_fsMetric_congr_cover

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

-- BACKLOG #36(a) (2026-09-19): the sum over paths at finite dimension. LinearAlgebra/Matrix/PathSum.lean
-- gives the entries of a matrix power as sums over index paths weighted by the product of the
-- entries traversed (Mathlib has only the adjacency-matrix walk count); Analysis/Matrix/SumOverPaths.lean
-- reads trotter_skew entry by entry through it: the matrix element of exp(A+B), and of the
-- propagator exp(-it(H1+H2)) of a split Hamiltonian, is the limit of sums over discrete paths of
-- products of one-step amplitudes -- Feynman's formulation as a theorem.
/-- info: 'Matrix.pathWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.pathWeight

/-- info: 'Matrix.pathWeight_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.pathWeight_cons

/-- info: 'Matrix.pow_succ_apply_eq_sum_pathWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.pow_succ_apply_eq_sum_pathWeight

/-- info: 'Matrix.trotterStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.trotterStep

/-- info: 'Matrix.tendsto_apply_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.tendsto_apply_of_tendsto

/-- info: 'Matrix.trotterStep_pow_apply_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.trotterStep_pow_apply_tendsto

/-- info: 'Matrix.exp_add_apply_tendsto_sum_pathWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.exp_add_apply_tendsto_sum_pathWeight

/-- info: 'Matrix.conjTranspose_neg_I_mul_smul_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.conjTranspose_neg_I_mul_smul_of_isHermitian

/-- info: 'Matrix.exp_neg_I_mul_smul_add_apply_tendsto_sum_pathWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.exp_neg_I_mul_smul_add_apply_tendsto_sum_pathWeight

-- BACKLOG #36(b)(ii) (2026-09-19), Analysis/Matrix/DysonSeries.lean: the Dyson series of a
-- perturbed unitary group at finite dimension. Terms by the interaction-picture Volterra
-- recursion D_{n+1}(t) = exp(tA) * int_0^t exp(-sA) B D_n(s) ds (matrix-valued Bochner integrals
-- under the L2 operator norm), the Duhamel identity by the fundamental theorem of calculus on
-- the interpolant exp(-sA) exp(s(A+B)), term and remainder bounds (|B| t)^n / n! from the
-- unitarity of the exponential factors, and convergence of the series to exp(t(A+B)).
/-- info: 'Matrix.dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTerm

/-- info: 'Matrix.continuous_dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.continuous_dysonTerm

/-- info: 'Matrix.norm_dysonTerm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_dysonTerm_le

/-- info: 'Matrix.hasDerivAt_exp_neg_smul_mul_exp_smul_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.hasDerivAt_exp_neg_smul_mul_exp_smul_add

/-- info: 'Matrix.exp_add_sub_exp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.exp_add_sub_exp_eq

/-- info: 'Matrix.dysonRemainder_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonRemainder_succ

/-- info: 'Matrix.norm_dysonRemainder_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_dysonRemainder_le

/-- info: 'Matrix.summable_dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.summable_dysonTerm

/-- info: 'Matrix.hasSum_dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.hasSum_dysonTerm

/-- info: 'Matrix.hasSum_dysonTerm_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.hasSum_dysonTerm_of_isHermitian

-- BACKLOG #36(b)(iii) (2026-09-20), Analysis/Matrix/DysonVertex.lean: the vertex bookkeeping of
-- the Dyson series. The interaction picture and the time-ordered recursion (the n vertices at
-- ordered times), the sum over vertex labellings for an interaction that is a sum of vertex
-- types, entries of matrix-valued interval integrals, and in the eigenbasis of a diagonal free
-- generator the old-fashioned perturbation theory recursion (a free propagation between
-- consecutive vertices, a sum over the intermediate state) with its first-order transition
-- amplitude and two-vertex amplitude.
/-- info: 'Matrix.intervalIntegral_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.intervalIntegral_apply

/-- info: 'Matrix.interactionPicture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.interactionPicture

/-- info: 'Matrix.dysonTermI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermI

/-- info: 'Matrix.dysonTermI_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermI_succ

/-- info: 'Matrix.dysonTermLabelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermLabelled

/-- info: 'Matrix.dysonTerm_sum_eq_sum_dysonTermLabelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTerm_sum_eq_sum_dysonTermLabelled

/-- info: 'Matrix.interactionPicture_diagonal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.interactionPicture_diagonal_apply

/-- info: 'Matrix.dysonTermI_succ_apply_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermI_succ_apply_diagonal

/-- info: 'Matrix.dysonTerm_one_apply_diagonal_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTerm_one_apply_diagonal_self

/-- info: 'Matrix.dysonTerm_one_apply_diagonal_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTerm_one_apply_diagonal_of_ne

/-- info: 'Matrix.dysonTermI_two_apply_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermI_two_apply_diagonal

/-- info: 'Matrix.dysonTermI_two_apply_diagonal_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.dysonTermI_two_apply_diagonal_self

-- BACKLOG #36(b)(iv') (2026-09-20), Combinatorics/PairingSum.lean: the pairing sum over perfect
-- matchings of Fin m (fixed-point-free involutions), its first-contraction recursion (a matching
-- of Fin (n+2) is the pair {0, j.succ} plus a matching of the complement, via the gluing
-- bijection built from Fin.cons and Fin.insertNth), transport along m = m', and the count
-- (2n-1)!! of perfect matchings of Fin (2n) (none for odd m).
/-- info: 'Fin.IsPerfectMatching' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Fin.IsPerfectMatching

/-- info: 'Fin.pairingSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.pairingSum

/-- info: 'Fin.pairingSum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.pairingSum_zero

/-- info: 'Fin.pairingSum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.pairingSum_one

/-- info: 'Fin.glue_isPerfectMatching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.glue_isPerfectMatching

/-- info: 'Fin.glueSigma_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.glueSigma_bijective

/-- info: 'Fin.prod_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.prod_glue

/-- info: 'Fin.pairingSum_succ_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.pairingSum_succ_succ

/-- info: 'Fin.pairingSum_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.pairingSum_cast

/-- info: 'Fin.card_isPerfectMatching_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.card_isPerfectMatching_even

/-- info: 'Fin.card_isPerfectMatching_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fin.card_isPerfectMatching_odd

-- BACKLOG #36(c) FC-1 (2026-09-20), Analysis/Semigroup/BoundedPerturbation.lean: a bounded
-- perturbation of a strongly continuous contraction semigroup, with no generator named. The
-- vector-valued Dyson series and its bounds, the Duhamel equation and its uniqueness, the
-- semigroup law of the sum, the bundled perturbed semigroup, and the Trotter product formula
-- (S(t/n) exp((t/n)B))^n psi -> S_pert(t) psi by telescoping against the semigroup law along
-- the compact orbit. Three constructions of one operator, proved to agree.
/-- info: 'IsContractionSemigroup.continuous_uncurry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IsContractionSemigroup.continuous_uncurry

/-- info: 'IsContractionSemigroup.of_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IsContractionSemigroup.of_group

/-- info: 'ContractionSemigroup.dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.dysonTerm

/-- info: 'ContractionSemigroup.norm_dysonTerm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.norm_dysonTerm_le

/-- info: 'ContractionSemigroup.dysonSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.dysonSum

/-- info: 'ContractionSemigroup.hasSum_dysonTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.hasSum_dysonTerm

/-- info: 'ContractionSemigroup.norm_dysonSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.norm_dysonSum_le

/-- info: 'ContractionSemigroup.continuous_dysonSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.continuous_dysonSum

/-- info: 'ContractionSemigroup.dysonSum_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.dysonSum_eq_add_integral

/-- info: 'ContractionSemigroup.eq_dysonSum_of_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.eq_dysonSum_of_duhamel

/-- info: 'ContractionSemigroup.dysonSum_add_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.dysonSum_add_time

/-- info: 'IsContractionSemigroup.perturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IsContractionSemigroup.perturbed

/-- info: 'ContractionSemigroup.perturbed_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.perturbed_add

/-- info: 'ContractionSemigroup.norm_trotterStep_apply_sub_dysonSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.norm_trotterStep_apply_sub_dysonSum_le

/-- info: 'ContractionSemigroup.exists_delta_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.exists_delta_of_isCompact

/-- info: 'ContractionSemigroup.tendsto_trotterStep_pow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ContractionSemigroup.tendsto_trotterStep_pow_apply

-- BACKLOG #36(c) FC-2 (2026-09-20), Analysis/Semigroup/HeatSemigroup.lean: the heat semigroup on
-- L^2(R) as the Bochner integral of translates against the Gaussian of variance t. Contraction,
-- semigroup law by Gaussian convolution of measures, strong continuity by continuity of
-- translation in L^2 and concentration of the Gaussians; an IsContractionSemigroup, so FC-1
-- applies: the perturbed heat semigroup e^{-t(H_0+V)} for a bounded potential, its Duhamel
-- equation and the Trotter product formula. The pointwise formula (P_t f)(x) = int f(x+y) dgamma
-- a.e. by pairing with indicators and Fubini, and its Wiener form E[f(x + B_t)].
/-- info: 'HeatSemigroup.gaussian_conv_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.gaussian_conv_gaussian

/-- info: 'HeatSemigroup.translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.translate

/-- info: 'HeatSemigroup.continuous_translate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.continuous_translate_apply

/-- info: 'HeatSemigroup.translate_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.translate_translate

/-- info: 'HeatSemigroup.heatSemigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.heatSemigroup

/-- info: 'HeatSemigroup.norm_heatSemigroup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.norm_heatSemigroup_le

/-- info: 'HeatSemigroup.heatSemigroup_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.heatSemigroup_add

/-- info: 'HeatSemigroup.tendsto_integral_norm_translate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.tendsto_integral_norm_translate_sub

/-- info: 'HeatSemigroup.continuous_heatSemigroup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.continuous_heatSemigroup_apply

/-- info: 'HeatSemigroup.isContractionSemigroup_heatSemigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.isContractionSemigroup_heatSemigroup

/-- info: 'HeatSemigroup.integrable_shift_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.integrable_shift_prod

/-- info: 'HeatSemigroup.heatSemigroup_apply_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.heatSemigroup_apply_ae_eq

/-- info: 'HeatSemigroup.heatConv_eq_integral_brownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.heatConv_eq_integral_brownian

/-- info: 'HeatSemigroup.potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.potential

/-- info: 'HeatSemigroup.perturbedHeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.perturbedHeat

/-- info: 'HeatSemigroup.perturbedHeat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.perturbedHeat_eq

/-- info: 'HeatSemigroup.tendsto_trotter_perturbedHeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.tendsto_trotter_perturbedHeat

-- BACKLOG #36(c) FC-3 (2026-09-20), Probability/TimeSlicedWiener.lean: the time-sliced Wiener
-- functional E[g(x+B_h) ... g(x+B_{nh}) f(x+B_{nh})] equals the n-fold operator product
-- ((P_h M_g)^n f)(x) a.e. -- Feynman's finite-slice formula in the Euclidean continuum. The
-- freezing lemma for independent variables, the Markov step through the shifted process
-- (indepFun_shift), and the induction through the pointwise formula of the heat semigroup.
/-- info: 'TimeSlicedWiener.integral_prod_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.integral_prod_of_indepFun

/-- info: 'TimeSlicedWiener.slicedWiener' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.slicedWiener

/-- info: 'TimeSlicedWiener.slicedWiener_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.slicedWiener_zero

/-- info: 'TimeSlicedWiener.measurable_slicedWiener' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.measurable_slicedWiener

/-- info: 'TimeSlicedWiener.slicedWiener_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.slicedWiener_succ

/-- info: 'TimeSlicedWiener.stepOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.stepOp

/-- info: 'TimeSlicedWiener.ae_gaussian_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.ae_gaussian_of_ae

/-- info: 'TimeSlicedWiener.pow_stepOp_apply_ae_eq_slicedWiener' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TimeSlicedWiener.pow_stepOp_apply_ae_eq_slicedWiener

-- BACKLOG #36(c) FC-4 (2026-09-20), Probability/FeynmanKac.lean: the Feynman-Kac formula. For a
-- Brownian motion with a.s. continuous paths, a bounded continuous potential V and a bounded
-- f in L^2, (e^{-t(H_0+V)} f)(x) = E[exp(-int_0^t V(x+B_s) ds) f(x+B_t)] a.e., the perturbed heat
-- semigroup being the Dyson series around P_t. The exponential of a multiplication operator is
-- multiplication by the exponential; Riemann sums along the continuous path; the Trotter limit
-- and the Wiener limit agree on every finite-measure set. Conditional on hB : IsBrownianReal.
/-- info: 'FeynmanKac.exp_smul_neg_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.exp_smul_neg_potential

/-- info: 'FeynmanKac.tendsto_riemannSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.tendsto_riemannSum

/-- info: 'FeynmanKac.prod_exp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.prod_exp_eq

/-- info: 'FeynmanKac.norm_slicedWiener_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.norm_slicedWiener_le

/-- info: 'FeynmanKac.tendsto_slicedWiener' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.tendsto_slicedWiener

/-- info: 'FeynmanKac.feynmanKac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.feynmanKac

-- BACKLOG #36(c) FC-5 (2026-09-20), Analysis/Semigroup/SchrodingerGroup.lean: Nelson's product
-- formula and the unitary Schrodinger propagator on L^2(R). The phase group M_{e^{-it kappa}} of a
-- real measurable symbol is strongly continuous (weak continuity + polarisation); the unitary group
-- F^{-1} M F of a dispersion relation is a contraction semigroup for t >= 0; the complex multiplier
-- exponential; Nelson: (U(t/n) e^{-i(t/n)V})^n psi -> e^{-it(kappa(D)+V)} psi; the propagator is an
-- isometry and, with the reversed dynamics as two-sided inverse, unitary.
/-- info: 'SchrodingerGroup.exp_eq_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.exp_eq_potential

/-- info: 'SchrodingerGroup.tendsto_phaseGroup_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.tendsto_phaseGroup_apply_zero

/-- info: 'SchrodingerGroup.continuous_phaseGroup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.continuous_phaseGroup_apply

/-- info: 'SchrodingerGroup.fourierGroup_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.fourierGroup_add

/-- info: 'SchrodingerGroup.norm_fourierGroup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.norm_fourierGroup_apply

/-- info: 'SchrodingerGroup.isContractionSemigroup_fourierGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.isContractionSemigroup_fourierGroup

/-- info: 'SchrodingerGroup.trotterStep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.trotterStep_eq

/-- info: 'SchrodingerGroup.nelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.nelson

/-- info: 'SchrodingerGroup.nelson_freeSchrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.nelson_freeSchrodinger

/-- info: 'SchrodingerGroup.norm_schrodinger_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.norm_schrodinger_apply

/-- info: 'SchrodingerGroup.schrodinger_mul_schrodinger_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.schrodinger_mul_schrodinger_of_neg

/-- info: 'SchrodingerGroup.exists_linearIsometryEquiv_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.exists_linearIsometryEquiv_schrodinger

-- BACKLOG #40 FC-1' (2026-09-20), Analysis/Semigroup/MatrixInstance.lean: the rule-of-two test of the
-- bounded-perturbation engine. On C^m with S(t) = exp(tA), A skew-Hermitian, and any B, the engine's
-- Dyson terms are the matrix Dyson terms applied to psi, its perturbed semigroup is exp(t(A+B))
-- (matrix Duhamel identity + engine uniqueness), and the matrix Dyson series and Trotter formula
-- come back as corollaries with the skewness of B dropped; strong convergence is norm convergence
-- in finite dimension.
/-- info: 'Matrix.toEuclideanCLM_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.toEuclideanCLM_exp

/-- info: 'Matrix.tendsto_of_forall_tendsto_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.tendsto_of_forall_tendsto_apply

/-- info: 'Matrix.isContractionSemigroup_freeSemigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.isContractionSemigroup_freeSemigroup

/-- info: 'Matrix.engine_dysonTerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.engine_dysonTerm_eq

/-- info: 'Matrix.perturbed_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.perturbed_eq_exp

/-- info: 'Matrix.hasSum_dysonTerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.hasSum_dysonTerm_apply

/-- info: 'Matrix.hasSum_dysonTerm_of_engine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.hasSum_dysonTerm_of_engine

/-- info: 'Matrix.tendsto_trotter_of_engine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.tendsto_trotter_of_engine

/-- info: 'Matrix.trotter_skew_of_engine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.trotter_skew_of_engine

-- BACKLOG #42 FC-4' (2026-09-20), Probability/FeynmanKacL2.lean: Feynman-Kac for every g in L^2.
-- Both sides are continuous in g on finite-measure sets and agree on the dense simple functions;
-- the Wiener side is bounded through E|g(x+B_t)| = (P_t |g|)(x) a.e. (the pointwise formula of
-- HeatSemigroup.lean and the law of B_t). tendsto_riemann_path is the Riemann-sum lemma extracted
-- from FeynmanKac.lean when tendsto_slicedWiener was generalised to f integrable along the endpoint.
/-- info: 'FeynmanKac.tendsto_riemann_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.tendsto_riemann_path

/-- info: 'FeynmanKac.fkFunctional_congr_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.fkFunctional_congr_ae

/-- info: 'FeynmanKac.ae_integrable_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.ae_integrable_shift

/-- info: 'FeynmanKac.absConv_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.absConv_ae_eq

/-- info: 'FeynmanKac.norm_setIntegral_fkFunctional_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.norm_setIntegral_fkFunctional_le

/-- info: 'FeynmanKac.aestronglyMeasurable_fkFunctional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.aestronglyMeasurable_fkFunctional

/-- info: 'FeynmanKac.feynmanKac_Lp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeynmanKac.feynmanKac_Lp

-- BACKLOG #43 FC-5'' (2026-09-20), Analysis/Semigroup/SchrodingerSchwartz.lean: the free Schrodinger
-- group on Schwartz functions and the Schrodinger equation. The phase e^{-it kappa} of a symbol of
-- temperate growth has temperate growth, so U_kappa(t) preserves Schwartz space (Mathlib's
-- fourierMultiplierCLM); the kinetic operator is -1/2 Laplacian; d/dt U(t) f = -i H_0 U(t) f in L^2
-- at every t (dominated convergence for the difference quotient of the phase, lifted through the
-- Fourier isometry, moved by the group law).
/-- info: 'SchrodingerGroup.hasTemperateGrowth_exp_mul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.hasTemperateGrowth_exp_mul_I

/-- info: 'SchrodingerGroup.hasTemperateGrowth_phaseFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.hasTemperateGrowth_phaseFun

/-- info: 'SchrodingerGroup.fourierGroup_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.fourierGroup_toLp

/-- info: 'SchrodingerGroup.freeSchrodinger_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.freeSchrodinger_toLp

/-- info: 'SchrodingerGroup.kineticOp_eq_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.kineticOp_eq_laplacian

/-- info: 'SchrodingerGroup.hasDerivAt_phaseGroup_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.hasDerivAt_phaseGroup_toLp

/-- info: 'SchrodingerGroup.hasDerivAt_fourierGroup_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.hasDerivAt_fourierGroup_toLp

/-- info: 'SchrodingerGroup.hasDerivAt_freeSchrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.hasDerivAt_freeSchrodinger

-- BACKLOG #48 FC-5''' (2026-09-20), Analysis/Semigroup/GaussianPacket.lean: the free Gaussian packet.
-- The Gaussian e^{-pi a x^2} (Re a > 0) as a Schwartz function on R (its n-th derivative is a
-- polynomial times the Gaussian; |x|^m e^{-c x^2} <= 1 + m!/c^m), its Fourier transform as a Schwartz
-- identity from Mathlib's fourier_gaussian_pi, and the spreading packet: U_0(t) g_a is the Gaussian of
-- parameter a/(1 + 2 pi i a t) with amplitude (1 + 2 pi i a t)^{-1/2} (the principal square root is
-- multiplicative on the right half-plane); for real a the density widens as sqrt(1 + (2 pi a t)^2).
/-- info: 'SchrodingerGroup.iteratedDeriv_gaussFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.iteratedDeriv_gaussFun

/-- info: 'SchrodingerGroup.pow_mul_exp_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.pow_mul_exp_neg_le

/-- info: 'SchrodingerGroup.decay_gaussFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.decay_gaussFun

/-- info: 'SchrodingerGroup.fourier_gaussianS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.fourier_gaussianS

/-- info: 'SchrodingerGroup.fourierInv_gaussianS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.fourierInv_gaussianS

/-- info: 'SchrodingerGroup.smulLeft_phase_fourier_gaussianS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.smulLeft_phase_fourier_gaussianS

/-- info: 'SchrodingerGroup.mul_cpow_of_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.mul_cpow_of_re_pos

/-- info: 'SchrodingerGroup.packetAmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.packetAmp_eq

/-- info: 'SchrodingerGroup.freeSchrodingerS_gaussianS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.freeSchrodingerS_gaussianS

/-- info: 'SchrodingerGroup.freeSchrodinger_gaussianS_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.freeSchrodinger_gaussianS_toLp

/-- info: 'SchrodingerGroup.re_packetParam_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SchrodingerGroup.re_packetParam_ofReal

-- BACKLOG #41(b) FC-2' (2026-09-20), Probability/BrownianVec.lean: Brownian motion in R^d as d jointly
-- independent real coordinates; independent vectors of independent pairs; the product Gaussian, its
-- characteristic function and its absolute continuity (a product of absolutely continuous measures
-- is absolutely continuous); the weak Markov property in R^d. With it the Euclidean chain
-- (HeatSemigroup, TimeSlicedWiener, FeynmanKac, FeynmanKacL2) lives on L^2(R^d), same names.
/-- info: 'ProbabilityTheory.indepFun_pi_of_iIndepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.indepFun_pi_of_iIndepFun

/-- info: 'MeasureTheory.Measure.pi_absolutelyContinuous_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.Measure.pi_absolutelyContinuous_pi

/-- info: 'ProbabilityTheory.charFun_gaussianVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.charFun_gaussianVec

/-- info: 'ProbabilityTheory.gaussianVec_absolutelyContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.gaussianVec_absolutelyContinuous

/-- info: 'ProbabilityTheory.IsPreBrownianVec.hasLaw_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsPreBrownianVec.hasLaw_eval

/-- info: 'ProbabilityTheory.IsPreBrownianVec.indepFun_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsPreBrownianVec.indepFun_shift

/-- info: 'ProbabilityTheory.IsBrownianVec.of_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.IsBrownianVec.of_coord

/-- info: 'HeatSemigroup.charFun_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.charFun_gaussian

/-- info: 'HeatSemigroup.gaussian_absolutelyContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeatSemigroup.gaussian_absolutelyContinuous

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
-- INFRASTRUCTURE the measurement-gadget wall named; the n-fold hybrid amplitude equality was
-- separate work, done 2026-09-23 (Reversible/HybridLift.lean, pinned at the end of this file:
-- the gadget is monomial, so no tensor factor was needed after all).
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
-- Mathlib has no mixing definition and no pointwise Birkhoff (MATHLIB-ABSENT(MeasureTheory.birkhoff_pointwise)), so the abstract route stops at
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

-- ...and the form the route actually consumes: measures on R concentrated on the interval,
-- transferred through Subtype.val by map_comap_subtype_coe.  The subtype statement is the natural
-- one to PROVE; this is the natural one to APPLY, since the laws one meets are laws of
-- [a,b]-valued random variables and so live on R.
/-- info: 'MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl

-- Q12-c2 step 3' (2026-08-24): eq_of_forall_integral_mul_pow_eq -- two CONTINUOUS functions on a
-- compact interval with the same moments against all powers are equal.
-- This DISSOLVED the route's step-3' fork.  The memo had identified two ways past that step --
-- decreasing-rearrangement uniqueness (no Mathlib quantile machinery) or two-dimensional
-- determinacy on [0,1]^2 (general Stone-Weierstrass) -- and neither is needed.  The k-clock family
-- delivers more than the marginal moments: with j clocks at rate c and k at rate 1 it gives
-- E[H_c(U)^j U^k] = 1/(1 + jc + k), and j = 1 leaves a FIXED CONTINUOUS WEIGHT integrated against
-- all powers, which is exactly this lemma's hypothesis.
-- Lesson recorded in the memo: when a step looks like it needs a STRONGER determinacy theorem,
-- check first whether it needs only the SAME theorem against a different object.
-- IsOpenPosMeasure is what upgrades "a.e. equal" to "equal".
/-- info: 'MeasureTheory.eq_of_forall_integral_mul_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.eq_of_forall_integral_mul_pow_eq

-- The CARRIER (2026-08-24): Mathlib has no MeasureSpace instance on the subtype Set.Icc a b (MATHLIB-ABSENT(Set.Icc.instMeasureSpace)), so
-- the measure these results are stated against had to be built -- intervalMeasure, the comap of
-- volume -- together with its two needed properties.  Finiteness is immediate; full support
-- (isOpenPosMeasure_intervalMeasure) needs a < b and is what upgrades "equal almost everywhere"
-- to "equal".  Proof: a nonempty relatively-open subset of a nondegenerate interval contains
-- Ioo (max a (x - eps/2)) (min b (x + eps/2)), which has positive Lebesgue measure.
/-- info: 'MeasureTheory.isOpenPosMeasure_intervalMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.isOpenPosMeasure_intervalMeasure

-- Q12-c2 STEP 1 (2026-08-24, Mathlib/Probability/IidClockRace.lean): the k-CLOCK RACE FOR
-- GENERAL IID CLOCKS -- the route memo's "fiddliest part", and the piece that ties the analytic
-- half (steps 3/3') to record-layer-plan.md §3c.
-- THE CHANGE OF FRAMING is what makes it work.  CompetingExponentials gave each clock j its own
-- law Exp b_j and raced them unscaled; that is unusable here, because the law is the UNKNOWN.
-- scaledRaceCell puts one iid law mu on every clock and carries the rate as a SCALING of the
-- reading: clock j fires at (xi j)/(b j).  scaledRaceCell_one records that the two framings agree
-- at unit rates, and hasRaceProperty_expMeasure that they agree for the exponential at all rates
-- (the rate r cancels out of r/(r + r*S/b_i)) -- the non-vacuity check on the hypothesis.
-- measure_scaledRaceCell is the KERNEL IDENTITY: clock i wins with probability
-- int prod_j G(b_j/b_i * t) dmu(t), G t = mu (Ioi t) the survival function.  Same proof route as
-- measure_raceCell (measurePreserving_piFinSuccAbove split, Measure.pi_pi on a box) but STRICTLY
-- CLEANER: because the rate scales the reading rather than the law, the slice is a box at EVERY
-- t, so the a.e.-nonnegativity step of the exponential case disappears.
-- Then the k-clock family (rates (1, c, ..., c)) turns an integral equation into a MOMENT
-- SEQUENCE: lintegral_measure_Ioi_pow is E[G(c xi)^k] = 1/(1+kc), the memo's (1), and
-- lintegral_measure_Ioi_pow_mul_pow is the mixed form E[G(c xi)^p G(xi)^k] = 1/(1+pc+k) at rates
-- (1, c^p, 1^k) -- the form eq_of_forall_integral_mul_pow_eq consumes, since at p = 1 it is a
-- fixed continuous weight integrated against every power.
-- Steps 2, 3 and 4 landed the same day and close §3c -- see the block below for the finish and for
-- the SECOND CONJUNCT that must travel with the headline.
/-- info: 'ProbabilityTheory.measure_scaledRaceCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.measure_scaledRaceCell

/-- info: 'ProbabilityTheory.HasRaceProperty.lintegral_measure_Ioi_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.HasRaceProperty.lintegral_measure_Ioi_pow

/-- info: 'ProbabilityTheory.HasRaceProperty.lintegral_measure_Ioi_pow_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.HasRaceProperty.lintegral_measure_Ioi_pow_mul_pow

/-- info: 'ProbabilityTheory.hasRaceProperty_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.hasRaceProperty_expMeasure

-- Q12-c2 STEP 2 (2026-08-24, same file): the PROBABILITY INTEGRAL TRANSFORM -- and the route
-- memo's regularity hypothesis turns out to be UNNECESSARY.
-- map_survival: G(xi) is uniform on [0,1], where G t = mu (Ioi t) is the survival function
-- (survival, with its Icc-valued/antitone/measurable API).
-- The memo expected to need a PIT theorem and assumed G continuous and strictly decreasing to get
-- one.  Neither is required.  The c = 1 case of step 1's moment family already says
-- E[G(xi)^k] = 1/(1+k) for every k, and those are EXACTLY the moments of the uniform law, so
-- ext_of_forall_integral_pow_eq_of_null_compl (step 3) closes it with NO hypothesis on mu at all.
-- ★ The regularity is therefore DERIVED, not assumed: mu is atomless because the (k+1)-clock race
-- at equal rates says the smallest of k+1 iid readings is STRICTLY smallest with probability
-- 1/(k+1), and ties would cost.  This is the second time the k-clock family has paid for a step
-- the two-clock framing made look expensive.
/-- info: 'ProbabilityTheory.HasRaceProperty.map_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.HasRaceProperty.map_survival

-- Q12-c2 STEPS 3 + 4 (2026-08-24, same file): §3c CLOSED.  hasRaceProperty_iff_exists_expMeasure --
-- for iid linear clocks, first-to-fire is proportional to the rate IFF the waiting-time law is
-- exponential.  The ⇐ half is hasRaceProperty_expMeasure; exists_eq_expMeasure is the ⇒ half.
-- ★ THE ROUTE MEMO'S THREE MAPPED ASSEMBLIES WERE ALL UNNECESSARY, and so was its §5a successor.
-- Steps 3/3' were built to compare H_c(u) = G(c * G-inverse(u)) against u^c, which needs the
-- quantile G-inverse as a continuous function on a CLOSED interval -- machinery Mathlib lacks (MATHLIB-ABSENT(Set.Icc.instMeasureSpace)).
-- survival_natMul_ae sidesteps all of it: restrict the ratio to a NATURAL NUMBER m, and G(t)^m is
-- itself a product of m survival factors at rate 1, so ALL THREE terms of the expansion of
-- int (G(mt) - G(t)^m)^2 dmu are instances of the SAME race family --
--   int G(mt)^2       = 1/(1+2m)   at rates (1, m, m)
--   int G(mt) G(t)^m  = 1/(1+2m)   at rates (1, m, 1^m)
--   int G(t)^(2m)     = 1/(1+2m)   at rates (1, 1^(2m))
-- -- and they cancel.  A nonnegative function with zero integral vanishes a.e.  No quantile, no
-- two-dimensional determinacy, no injectivity of G, no Stone-Weierstrass.
-- ★ The integers are enough because ANTITONICITY supplies the missing real ratios (raceRate_le):
-- the functional equation ties G together only along the lattice {mt}, but m*t <= n*t' forces
-- G(t)^m >= G(t')^n, so m*lambda(t)*t <= n*lambda(t')*t', and letting the integer ratio m/n climb
-- to t'/t gives lambda(t) <= lambda(t').  Symmetry gives equality, so one lambda serves everywhere.
-- ★ pos_ae is DERIVED too: the memo sets the problem up with xi supported on (0,infinity); for
-- t <= 0 one has 2t <= t, so G(t) <= G(2t) = G(t)^2, false for G(t) in (0,1).  The m = 2 case alone.
-- The finish reads the law off through map_survival: on the good set t > s iff G t < exp(-lambda s),
-- so mu (Ioi s) = (mu.map G) (Iio exp(-lambda s)) = Lebesgue's, and Measure.ext_of_Iic closes it.
-- ⚠️ THE SECOND CONJUNCT IS NOT OPTIONAL.  HasRaceProperty quantifies over the NUMBER OF CLOCKS.
-- At a fixed number of outcomes n the family gives only n-1 moments and finitely many moments
-- determine nothing, so what is forced is the exponential law GIVEN THAT ONE CLOCK LAW SERVES
-- EVERY n -- the measurement-independence specs/sigma-fibre-contextuality.md commits to.  Do not
-- state the first conjunct without the second.
-- ⚠️ AND THIS IS A POSIT REMOVED, NOT A MECHANISM SUPPLIED.  §3c's exponential fibre measure is no
-- longer a choice, but NO DYNAMICS carves the race cells -- Q12's frontier half (Q12-d) stays
-- blocked by W1, and neither DeIsolationInteraction witness is dynamical.
/-- info: 'ProbabilityTheory.HasRaceProperty.survival_natMul_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.HasRaceProperty.survival_natMul_ae

/-- info: 'ProbabilityTheory.raceRate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.raceRate_le

/-- info: 'ProbabilityTheory.HasRaceProperty.exists_eq_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.HasRaceProperty.exists_eq_expMeasure

/-- info: 'ProbabilityTheory.hasRaceProperty_iff_exists_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.hasRaceProperty_iff_exists_expMeasure

-- InvariantTwist (2026-09-02, Mathlib/MeasureTheory/InvariantTwist.lean; 1-Mathlib staging).
-- A group with a left-invariant probability measure acts measurably on X preserving μ; φ : X → G
-- is measurable and constant on orbits. Then y ↦ act (φ y) y preserves μ — four lines of Tonelli,
-- no disintegration. Not found in Mathlib (2026-09-01); MeasurePreserving.skew_product is the
-- product-space special case. Consumer: RecordLayer/JointLift.lean (jointLift_measurePreserving).
/-- info: 'MeasureTheory.MeasurePreserving.twist_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.MeasurePreserving.twist_of_invariant

/-- info: 'MeasureTheory.MeasurePreserving.vadd_twist_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.MeasurePreserving.vadd_twist_of_invariant

-- R-016′ Category-1 pieces (2026-09-14): the arena ℂℙⁿ × T² as a symplectic manifold needs a
-- product of manifolds charted on the product NORMED SPACE (the corpus's form layer is stated for
-- self models only; Mathlib charts products on ModelProd), a translation atlas on AddCircle T
-- (every chart transition is a translation, so a constant alternating map is a global smooth
-- form), constant forms on such an atlas, and the sum π₁^*α + π₂^*β on a product with its
-- exterior derivative. ⚠️ Two charted-space structures on AddCircle T (stereographic over
-- EuclideanSpace ℝ (Fin 1), Q33; translation over ℝ, here) and two on M × N (ModelProd E F; E × F),
-- keyed on distinct model types, never compared.
/-- info: 'AddCircle.instIsManifoldReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.instIsManifoldReal

/-- info: 'AddCircle.fderiv_chart_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.fderiv_chart_transition

/-- info: 'Prod.instIsManifoldSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prod.instIsManifoldSelf

/-- info: 'Prod.fderiv_chart_transition_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prod.fderiv_chart_transition_prod

/-- info: 'DifferentialForm.localRep_constFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.localRep_constFamily

/-- info: 'DifferentialForm.constForm_mextDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.constForm_mextDeriv

-- ★★ The torus AddCircle T × AddCircle T', charted by translation over ℝ × ℝ, is a symplectic
-- manifold: the constant area form dθ₁ ∧ dθ₂ is closed (constant in every chart) and non-degenerate.
/-- info: 'AddCircle.torusAreaForm_isSymplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.torusAreaForm_isSymplectic

/-- info: 'DifferentialForm.localRep_prodFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.localRep_prodFamily

-- ★★ d(π₁^*α + π₂^*β) = π₁^* dα + π₂^* dβ on a product, from Mathlib's flat extDeriv_pullback
-- along the two projections.
/-- info: 'DifferentialForm.prodForm_mextDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.prodForm_mextDeriv

-- ★★ The product of two symplectic manifolds is symplectic.
/-- info: 'DifferentialForm.IsSymplectic.prodForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.IsSymplectic.prodForm

-- The Hamiltonian flow at any time is continuous (added for the fsVolumeNormalized invariance
-- theorems' map_smul' route, 2026-09-14).
/-- info: 'DifferentialForm.IsSymplectic.continuous_hamiltonianFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.IsSymplectic.continuous_hamiltonianFlow

-- The quotient map R -> AddCircle T is a local diffeomorphism for the translation atlas
-- (2026-09-14, R-016''): manifold derivative the identity, and a real curve pushed to the circle
-- has the curve's derivative. Consumer: LF4/ArenaStrokeFlux.lean (the transverse torus curve).
/-- info: 'AddCircle.hasMFDerivAt_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.hasMFDerivAt_coe

/-- info: 'AddCircle.hasMFDerivAt_coe_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.hasMFDerivAt_coe_comp

-- Maps that preserve a form in charts (2026-09-14, #29, Geometry/Manifold/FormInvariance.lean):
-- the chart form of g^* s = s that topFormMeasure_map_eq reads, named, with its closure under
-- iterated powers and under products of manifolds charted over E × F; chart translations preserve
-- constant forms on a translation atlas, and translation of AddCircle T is a chart translation.
/-- info: 'DifferentialForm.preservesLocalRep_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.preservesLocalRep_id

/-- info: 'DifferentialForm.PreservesLocalRep.wedgePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.PreservesLocalRep.wedgePow

-- ★ A homeomorphism preserving a top form in charts preserves its top-form measure.
/-- info: 'DifferentialForm.PreservesLocalRep.map_topFormMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.PreservesLocalRep.map_topFormMeasure

-- ★ A product of chart-preserving maps preserves the product family π₁^*α + π₂^*β.
/-- info: 'DifferentialForm.PreservesLocalRep.prodMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.PreservesLocalRep.prodMap

/-- info: 'DifferentialForm.preservesLocalRep_constFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.preservesLocalRep_constFamily

/-- info: 'DifferentialForm.IsChartTranslation.prodMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.IsChartTranslation.prodMap

-- ★ Translation of the circle is a chart translation of the translation atlas.
/-- info: 'AddCircle.isChartTranslation_addLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AddCircle.isChartTranslation_addLeft

-- ★ The unitary action preserves the Fubini–Study 2-form in charts (2026-09-14, #29,
-- Instances/ProjectiveSpaceFubiniStudyInvariance.lean): fsVolume_map_smul's chart hypothesis,
-- restated for the form itself so that products with ℂℙⁿ inherit it.
/-- info: 'Projectivization.preservesLocalRep_fsForm_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.preservesLocalRep_fsForm_smul

-- Holomorphic vector fields and maps for an atlas complex structure (2026-09-15, #30 KG-3',
-- Geometry/Manifold/HolomorphicVectorField.lean): IsHolomorphicVectorField J₀ X (the chart field
-- is differentiable with J₀-linear derivative in every chart), IsHolomorphicMap J g (mfderiv
-- commutes with J), and the Kähler triangle's "symplectic + holomorphic = Killing" half.
/-- info: 'DifferentialForm.IsAlmostKahler.metric_mfderiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DifferentialForm.IsAlmostKahler.metric_mfderiv_eq

-- The Schrödinger field on ℂℙⁿ is holomorphic and its flow is holomorphic and Killing (#30,
-- Instances/ProjectiveSpaceSchrodingerHolomorphic.lean): the unitary action is a holomorphic map
-- (its mfderiv is the real restriction of the ℂ-derivative of uTrans U), symplectic at bundle
-- level (fsModelForm_uTrans through the tangent spaces), hence an isometry of the Fubini–Study
-- metric; the Hamiltonian flow of −2⟨H⟩ inherits all three at every time; the Schrödinger field
-- read in ANY affine chart is schrodingerChartField in that chart (uniqueness of the local
-- Hamiltonian vector), a quadratic polynomial with complex coefficients, so ℂ-differentiable.
/-- info: 'Projectivization.hasMFDerivAt_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.hasMFDerivAt_smul

-- ★ The unitary action is a holomorphic map of ℂℙⁿ.
/-- info: 'Projectivization.isHolomorphicMap_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.isHolomorphicMap_smul

-- ★ U^* ω_FS = ω_FS at bundle level.
/-- info: 'Projectivization.fsForm_smul_mfderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.fsForm_smul_mfderiv

-- ★ The unitary action is an isometry of the Fubini–Study metric.
/-- info: 'Projectivization.fsMetric_smul_mfderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.fsMetric_smul_mfderiv

-- ★★ The Hamiltonian flow of −2⟨H⟩ is holomorphic and Killing at every time.
/-- info: 'Projectivization.isHolomorphicMap_hamiltonianFlow_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.isHolomorphicMap_hamiltonianFlow_schrodinger

/-- info: 'Projectivization.fsMetric_hamiltonianFlow_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.fsMetric_hamiltonianFlow_schrodinger

/-- info: 'Projectivization.chartField_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.chartField_schrodingerField

/-- info: 'Projectivization.differentiableAt_schrodingerChartField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.differentiableAt_schrodingerChartField

-- ★★ The Schrödinger field is a holomorphic vector field of the Kähler manifold ℂℙⁿ.
/-- info: 'Projectivization.isHolomorphicVectorField_schrodingerField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Projectivization.isHolomorphicVectorField_schrodingerField

-- ====================================================================================
-- Gleason's theorem, finite-dimensional (2026-09-21, specs/gleason-feasibility.md): the
-- Mathlib-only tree Analysis/InnerProductSpace/Gleason/. Layers A (reductions) and C (descent)
-- were proved first, the core lemma on S^2 (Layer B) entering only as the explicit hypothesis
-- `Gleason.CoreLemma` of `gleason_representation_of_core`; the core lemma was then proved in
-- five stages 57(a)-(e), 2026-09-21/22 (the blocks below), and Core.lean joins the two:
-- `Gleason.ProjectionPackage.gleason_representation`, Gleason's theorem for C^N, N >= 3, on
-- the foundational triple (the last block of this file).
-- ====================================================================================

-- Polarization.lean: the Jordan-von Neumann engine, extracted from LF2/EffectGleason.lean
-- (which now consumes it): a quadratic-like q (degree-2 homogeneous, parallelogram,
-- 0 <= q <= |.|^2) is the quadratic form of a Hermitian matrix, with the bounded-additive
-- Cauchy equation replacing continuity.
/-- info: 'Gleason.additive_bounded_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.additive_bounded_linear

/-- info: 'Gleason.IsQuadraticLike.polar_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.polar_add_left

/-- info: 'Gleason.IsQuadraticLike.polar_smul_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.polar_smul_real

/-- info: 'Gleason.IsQuadraticLike.sesq_conj_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.sesq_conj_symm

/-- info: 'Gleason.IsQuadraticLike.sesq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.sesq_self

/-- info: 'Gleason.IsQuadraticLike.polarMatrix_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.polarMatrix_isHermitian

-- ★ q v = <v, R v> for R = polarMatrix q.
/-- info: 'Gleason.IsQuadraticLike.eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLike.eq_dotProduct

/-- info: 'Gleason.matrix_eq_zero_of_quadForm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.matrix_eq_zero_of_quadForm_zero

/-- info: 'Gleason.trace_mul_isHermitian_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.trace_mul_isHermitian_real

/-- info: 'Gleason.trace_mul_vecMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.trace_mul_vecMulVec

-- ProjectionPackage.lean: the statement side. Projections are IsStarProjection matrices; a
-- package is nonnegative, normalised and additive on orthogonal projections. rankOne v = |v><v|,
-- the resolution of the identity over an orthonormal basis, additivity over any finite
-- pairwise-orthogonal family (p_sum), the frame function frame v = p |v><v| (A1: nonneg,
-- phase invariant, sums to 1 over every ONB), and A2: its restriction to a completely real
-- subspace is a real frame function with weight p(sum |e_i><e_i|).
/-- info: 'Gleason.ProjectionPackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage

/-- info: 'Gleason.IsFrameFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction

/-- info: 'Gleason.rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.rankOne

/-- info: 'Gleason.isStarProjection_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.isStarProjection_rankOne

/-- info: 'Gleason.sum_rankOne_orthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.sum_rankOne_orthonormalBasis

/-- info: 'Gleason.ProjectionPackage.p_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.p_sum

/-- info: 'Gleason.ProjectionPackage.frame_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.frame_smul

-- A1.
/-- info: 'Gleason.ProjectionPackage.sum_frame_orthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.sum_frame_orthonormalBasis

/-- info: 'Gleason.ProjectionPackage.isFrameFunction_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.isFrameFunction_frame

-- A2.
/-- info: 'Gleason.ProjectionPackage.isFrameFunction_realRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.isFrameFunction_realRestrict

-- Descent.lean (Layer C): a Hermitian matrix with nonnegative quadratic form on the sphere is
-- PSD, its trace is the sum over the standard basis, two Hermitian matrices agreeing on the
-- sphere are equal; packaged as quadraticForm_on_sphere_to_density (shared with Busch). The
-- projection descent: spectral resolution P = sum lambda_i |b_i><b_i| with lambda_i in {0,1},
-- so p P = Re Tr(A P) for every projection once the frame function is the form of A.
/-- info: 'Gleason.posSemidef_of_sphere_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.posSemidef_of_sphere_nonneg

/-- info: 'Gleason.eq_of_sphere_quadForm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eq_of_sphere_quadForm_eq

-- ★ the shared sphere-to-density lemma.
/-- info: 'Gleason.quadraticForm_on_sphere_to_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadraticForm_on_sphere_to_density

/-- info: 'Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.IsHermitian.eq_sum_eigenvalues_smul_rankOne

/-- info: 'Gleason.eigenvalues_eq_zero_or_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eigenvalues_eq_zero_or_one

/-- info: 'Gleason.ProjectionPackage.p_eq_re_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.p_eq_re_trace

-- ★★ Gleason's conclusion from the quadratic-form hypothesis.
/-- info: 'Gleason.ProjectionPackage.existsUnique_density_of_frame_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.existsUnique_density_of_frame_quadratic

-- FrameFunction.lean (Layer A3, the complex reduction): regularity on completely real planes
-- (IsRealPlaneRegular) makes the frame function a Hermitian form on every complex plane -- the
-- cross term's phase dependence is first-degree trigonometric (crossTerm_phase, via the
-- equator pair (x+y)/sqrt2, i(x-y)/sqrt2) -- so the degree-2 extension satisfies the
-- parallelogram law on C^N and the Jordan-von Neumann engine yields the Hermitian matrix.
-- isRealPlaneRegular_of_triples bridges from what the core lemma gives on 3-spaces (N >= 3).
/-- info: 'Gleason.IsRealPlaneRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsRealPlaneRegular

/-- info: 'Gleason.ProjectionPackage.frame_add_frame_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.frame_add_frame_eq

/-- info: 'Gleason.ProjectionPackage.crossTerm_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.crossTerm_phase

/-- info: 'Gleason.ProjectionPackage.frame_plane_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.frame_plane_unit

/-- info: 'Gleason.ProjectionPackage.ext_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.ext_plane

/-- info: 'Gleason.ProjectionPackage.ext_parallelogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.ext_parallelogram

/-- info: 'Gleason.ProjectionPackage.isQuadraticLike_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.isQuadraticLike_ext

-- ★ A3.
/-- info: 'Gleason.ProjectionPackage.exists_isHermitian_of_isRealPlaneRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.exists_isHermitian_of_isRealPlaneRegular

/-- info: 'Gleason.ProjectionPackage.isRealPlaneRegular_of_triples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.isRealPlaneRegular_of_triples

-- Reduction.lean: the core lemma as a proposition, and Gleason's theorem for C^N (N >= 3)
-- from it. The ONLY hypothesis beyond N >= 3 is CoreLemma; no sorry anywhere on main.
/-- info: 'Gleason.CoreLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.CoreLemma

-- ★★ Gleason from the core lemma (Layers A + C).
/-- info: 'Gleason.ProjectionPackage.gleason_representation_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.gleason_representation_of_core

-- 2026-09-21, stage 57(a) of the core lemma (specs/gleason-feasibility.md): Cooke-Keane-Moran
-- section 2 on S^2 (Sphere.lean) and section 3 (Warmup.lean). At this stage nothing claimed
-- Gleason's theorem; the core lemma itself (57(b)-(e)) was open (closed 2026-09-22, below).
-- Sphere.lean: the cross product as a vector of EuclideanSpace R (Fin 3) (an orthonormal pair
-- extends to a frame), a unit vector orthogonal to any two vectors (the orthogonal complement of
-- a plane is nontrivial), an orthonormal triple IS an orthonormal basis (so the frame identity
-- holds for every orthonormal triple, sum_triple); P1 (vector space), P2 f(-s) = f(s), P3 the
-- four-point identity on a great circle, P4 (f s > M - xi gives t orthogonal to s with
-- f t < m + xi), boundedness 0 <= f <= W for nonnegative frame functions, sphereSup/sphereInf,
-- and the regular examples: <p0, s>^2 (weight 1, Parseval) and every quadratic form (weight tr A).
/-- info: 'Gleason.cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.cross

/-- info: 'Gleason.norm_cross_of_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.norm_cross_of_orthonormal

/-- info: 'Gleason.orthonormal_triple_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.orthonormal_triple_iff

/-- info: 'Gleason.orthonormal_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.orthonormal_cross

/-- info: 'Gleason.exists_unit_orthogonal_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_unit_orthogonal_pair

/-- info: 'Gleason.orthonormalBasisOfTriple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.orthonormalBasisOfTriple

-- the frame identity for any orthonormal triple.
/-- info: 'Gleason.IsFrameFunction.sum_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.sum_triple

/-- info: 'Gleason.IsFrameFunction.const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.const

/-- info: 'Gleason.IsFrameFunction.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.add

-- P2.
/-- info: 'Gleason.IsFrameFunction.neg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.neg_apply

-- P3.
/-- info: 'Gleason.IsFrameFunction.four_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.four_point

-- P4.
/-- info: 'Gleason.IsFrameFunction.exists_orthogonal_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_orthogonal_lt

/-- info: 'Gleason.IsFrameFunction.le_weight_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.le_weight_of_nonneg

/-- info: 'Gleason.sphereSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.sphereSup

/-- info: 'Gleason.sphereInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.sphereInf

/-- info: 'Gleason.exists_sphereSup_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_sphereSup_sub_lt

/-- info: 'Gleason.IsFrameFunction.exists_orthogonal_lt_sphereInf_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_orthogonal_lt_sphereInf_add

/-- info: 'Gleason.isFrameFunction_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.isFrameFunction_inner_sq

-- every quadratic form is a frame function of weight tr A.
/-- info: 'Gleason.isFrameFunction_quadForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.isFrameFunction_quadForm

-- Warmup.lean: Warmup Theorem I (a bounded f on [0,1] with f a + f b + f c constant on
-- a + b + c = 1 is affine; the additivity on [0,1] is extended to R by x |-> g(fract x) + floor(x) g 1
-- and Gleason.additive_bounded_linear finishes) and Warmup Theorem II (C countable in (0,1),
-- f 0 = 0, f monotone off C, f a + f b + f c = 1 on a + b + c = 1 off C, then f a = a off C:
-- pick a_0 outside the rational quotients of C and 1 - C, rational homogeneity on multiples of
-- a_0, monotone squeeze, slope pinned by one triple).
/-- info: 'Gleason.linear_of_add_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.linear_of_add_on_Icc

-- Warmup Theorem I.
/-- info: 'Gleason.affine_of_sum_eq_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.affine_of_sum_eq_const

-- Warmup Theorem II.
/-- info: 'Gleason.eq_self_of_monotone_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eq_self_of_monotone_sum_eq_one

-- 2026-09-21, stage 57(b) of the core lemma (specs/gleason-feasibility.md): Piron.lean --
-- CKM section 4's vocabulary (latitude, northern hemisphere, equator, the coldest vector
-- orthogonal to s, the descent D_s) and the GEOMETRIC LEMMA of section 5 (Piron): any point
-- strictly lower than s is reached from s by a finite chain of descents. The gnomonic lift
-- (p + v)/|p + v| makes a descent the tangent line to a latitude circle
-- (lift_mem_descent_iff: lift w in D_{lift v} iff <w, v> = |v|^2); the tangent plane is read as
-- C through an orthonormal pair (tangent e1 e2 z); the explicit spiral z_k = z_0 (cos t)^{-k}
-- e^{ikt} descends step by step (spiral_step), turns by the angle of the target, and grows by
-- (cos t)^{-n} >= 1 - pi^2/(2n) (one_sub_le_cos_arg_div_pow: cos x >= 1 - x^2/2 + Bernoulli),
-- so it stops short of the target on its ray; two more steps along the ray finish
-- (descent_step_ray); an equator target is reached from any point orthogonal to it
-- (mem_descent_of_equator). Still nothing claims Gleason's theorem.
/-- info: 'Gleason.latitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.latitude

/-- info: 'Gleason.coldest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.coldest

/-- info: 'Gleason.descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.descent

/-- info: 'Gleason.mem_descent_of_equator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.mem_descent_of_equator

/-- info: 'Gleason.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.lift

/-- info: 'Gleason.latitude_lift_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.latitude_lift_lt_iff

/-- info: 'Gleason.eq_lift_of_northern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eq_lift_of_northern

-- the gnomonic dictionary.
/-- info: 'Gleason.lift_mem_descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.lift_mem_descent_iff

/-- info: 'Gleason.tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.tangent

/-- info: 'Gleason.inner_tangent_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_tangent_tangent

/-- info: 'Gleason.exists_tangent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_tangent_eq

/-- info: 'Gleason.lift_tangent_mem_descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.lift_tangent_mem_descent_iff

/-- info: 'Gleason.descent_step_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.descent_step_ray

/-- info: 'Gleason.spiral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.spiral

-- each spiral point is on the descent through the previous one.
/-- info: 'Gleason.spiral_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.spiral_step

/-- info: 'Gleason.spiral_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.spiral_end

-- the growth factor tends to one.
/-- info: 'Gleason.one_sub_le_cos_arg_div_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.one_sub_le_cos_arg_div_pow

/-- info: 'Gleason.IsDescentChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsDescentChain

-- ★ Piron's geometric lemma (CKM section 5).
/-- info: 'Gleason.exists_descent_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_descent_chain

-- 2026-09-22, stage 57(c) of the core lemma (specs/gleason-feasibility.md): SimpleFrame.lean --
-- CKM section 4's basic lemma and the theorem of section 5 (the simple frame functions: those
-- attaining sup at p and constant on the equator of p -- Bell's and Piron's extreme case).
-- equator_le: the equator value is the minimum (P4 at the pole); descent_le: f s' <= f s on the
-- descent through s (four-point identity on D_s, whose point orthogonal to s is on the
-- equator, inner_pole_cross_coldest); the approximate versions equator_lt_add/descent_lt_add
-- for section 6; le_of_latitude_lt: monotone in latitude via exists_descent_chain + descent_le
-- along the chain; exists_frame_of_latitudes: a frame in the northern hemisphere with latitudes
-- a, b, c for a + b + c = 1 (transport (sqrt a, sqrt b, sqrt c), completed to an ONB, through an
-- ONB (p, e1, e2)); parallelSup/parallelInf over the parallels, interlaced by monotonicity
-- (parallelSup_le_parallelInf), so the exceptional latitudes are disjoint open gaps, countable
-- (Set.PairwiseDisjoint.countable_of_isOpen); Warmup II on the common value; the squeeze
-- through nearby unexceptional latitudes empties the exceptional set. STAR eq_add_mul_latitude:
-- f s = m + (f p - m) <p,s>^2. Still nothing claims Gleason's theorem.
/-- info: 'Gleason.latitude_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.latitude_le_one

/-- info: 'Gleason.eq_pole_of_latitude_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eq_pole_of_latitude_eq_one

/-- info: 'Gleason.norm_coldest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.norm_coldest

/-- info: 'Gleason.inner_pole_cross_coldest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_pole_cross_coldest

-- the equator value is the minimum.
/-- info: 'Gleason.IsFrameFunction.equator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.equator_le

/-- info: 'Gleason.IsFrameFunction.equator_lt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.equator_lt_add

-- the basic lemma (CKM section 4).
/-- info: 'Gleason.IsFrameFunction.descent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.descent_le

-- its approximate version.
/-- info: 'Gleason.IsFrameFunction.descent_lt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.descent_lt_add

-- monotone in latitude.
/-- info: 'Gleason.IsFrameFunction.le_of_latitude_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.le_of_latitude_lt

-- a frame with prescribed latitudes.
/-- info: 'Gleason.exists_frame_of_latitudes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_frame_of_latitudes

/-- info: 'Gleason.parallelValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelValues

/-- info: 'Gleason.parallelSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelSup

/-- info: 'Gleason.parallelInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelInf

/-- info: 'Gleason.parallelValues_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelValues_nonempty

-- the parallels are interlaced.
/-- info: 'Gleason.parallelSup_le_parallelInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelSup_le_parallelInf

/-- info: 'Gleason.parallelValues_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.parallelValues_one

/-- info: 'Gleason.IsFrameFunction.eq_latitude_of_normalised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.eq_latitude_of_normalised

-- STAR the simple-frame-function theorem (CKM section 5).
/-- info: 'Gleason.IsFrameFunction.eq_add_mul_latitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.eq_add_mul_latitude

-- 2026-09-22, stage 57(d) of the core lemma (specs/gleason-feasibility.md): Extremal.lean --
-- CKM section 6, bounded frame functions attain their extremal values; the second risk point.
-- The 90-degree rotation rot p s = <p,s> p + p x s preserves inner products (Lagrange);
-- a frame function composed with an inner-preserving map is a frame function (comp_inner);
-- symmetrise p g s = g s + g (rot p s) is a frame function of weight 2W, bounded, with
-- symmetrise p g p = 2 g p and CONSTANT ON THE EQUATOR (four-point identity for the pairs
-- (e, p x e)). exists_motion: for a unit q != p in the open northern hemisphere, an
-- inner-preserving T with T p = q and T c_q = p, c_q on the meridian of e0 at parameter
-- meridianParam p q = sqrt(1 - <p,q>^2)/<p,q> (OrthonormalBasis.equiv on (c, d, e1) -> (p, d', p x d')).
-- exists_forall_le: a maximising sequence, a convergent subsequence (IsCompact.tendsto_subseq
-- on the sphere), the moved symmetrised functions in the box [2m, 2M]^{S^2}, a cluster point
-- (Tychonoff: isCompact_univ_pi + IsCompact.exists_clusterPt) which is a frame function,
-- constant on the equator, with value 2 sup f at p (closed conditions, mem_of_clusterPt;
-- eq_of_clusterPt_of_tendsto), hence m' + (2 sup f - m') <p,.>^2 by eq_add_mul_latitude; a
-- fixed meridian point c near p has h c > 2 sup f - eps, frequently the moved function is
-- close to h at c (clusterPt_iff_frequently), and the two-step ray descent
-- (descent_step_ray) with the approximate basic lemma twice gives f p > sup f - 8 eps.
-- Still nothing claims Gleason's theorem.
/-- info: 'Gleason.rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.rot

/-- info: 'Gleason.inner_rot_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_rot_rot

/-- info: 'Gleason.IsFrameFunction.comp_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.comp_inner

/-- info: 'Gleason.symmetrise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.symmetrise

/-- info: 'Gleason.IsFrameFunction.symmetrise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.symmetrise

-- the symmetrisation is constant on the equator.
/-- info: 'Gleason.symmetrise_equator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.symmetrise_equator

/-- info: 'Gleason.meridianParam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.meridianParam

/-- info: 'Gleason.inner_lt_one_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_lt_one_of_ne

-- the rigid motion (CKM section 6, Step 1).
/-- info: 'Gleason.exists_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_motion

/-- info: 'Gleason.motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.motion

/-- info: 'Gleason.motion_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.motion_inner

/-- info: 'Gleason.motion_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.motion_pole

/-- info: 'Gleason.motion_meridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.motion_meridian

/-- info: 'Gleason.mem_of_clusterPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.mem_of_clusterPt

/-- info: 'Gleason.eq_of_clusterPt_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.eq_of_clusterPt_of_tendsto

-- STAR bounded frame functions attain their supremum.
/-- info: 'Gleason.IsFrameFunction.exists_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_forall_le

/-- info: 'Gleason.IsFrameFunction.exists_forall_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_forall_ge

/-- info: 'Gleason.IsFrameFunction.exists_eq_sphereSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_eq_sphereSup

-- 2026-09-22, stage 57(e) of the core lemma (specs/gleason-feasibility.md): General.lean --
-- CKM section 7, the general case, and the core lemma itself. The frame (p, q, r) with
-- q = r x p and its multiplication table; the two rotations rot p, rot r as signed
-- permutations of the frame coordinates; the pole identities at a maximum and a minimum
-- (add_rot_of_forall_le / _ge, from the simple-frame-function theorem applied to the
-- symmetrisation); the target quadratic form quadFrame M alpha m p q r and its own pole
-- identities, so h = g - f is negated by both rotations; the reflections in the coordinate
-- planes preserve h and h vanishes on the four great circles x = +-y, y = +-z. The endgame
-- differs from the paper's zero count: a great circle of zeros of h sits at latitude 1/2 from
-- the pole of h's own identity (inner_sq_eq_half_of_vanish), so p' = +-q where h = 0,
-- contradicting sup h > 0 unless h = 0. Then Core.lean: coreLemma and the theorem.
/-- info: 'Gleason.inner_cross_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_cross_perm

/-- info: 'Gleason.cross_cross_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.cross_cross_left

/-- info: 'Gleason.Frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.Frame

/-- info: 'Gleason.Frame.expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.Frame.expand

/-- info: 'Gleason.Frame.sum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.Frame.sum_sq

/-- info: 'Gleason.Frame.inner_q_rot_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.Frame.inner_q_rot_p

/-- info: 'Gleason.rotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.rotInv

/-- info: 'Gleason.inner_rot_eq_inner_rotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_rot_eq_inner_rotInv

-- the pole identity at a maximum.
/-- info: 'Gleason.IsFrameFunction.add_rot_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.add_rot_of_forall_le

/-- info: 'Gleason.IsFrameFunction.add_rot_of_forall_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.add_rot_of_forall_ge

/-- info: 'Gleason.quadFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadFrame

/-- info: 'Gleason.isFrameFunction_quadFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.isFrameFunction_quadFrame

/-- info: 'Gleason.quadFrame_add_rot_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadFrame_add_rot_p

/-- info: 'Gleason.quadFrame_add_rot_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadFrame_add_rot_r

/-- info: 'Gleason.quadFrame_eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadFrame_eq_dotProduct

-- the circle lemma: a great circle of zeros is at latitude 1/2.
/-- info: 'Gleason.inner_sq_eq_half_of_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.inner_sq_eq_half_of_vanish

/-- info: 'Gleason.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.reflect

/-- info: 'Gleason.flip_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.flip_q

/-- info: 'Gleason.vanish_p_eq_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.vanish_p_eq_q

/-- info: 'Gleason.vanish_q_eq_neg_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.vanish_q_eq_neg_r

-- STAR STAR Gleason's core lemma: nonnegative frame functions on S^2 are quadratic forms.
/-- info: 'Gleason.frameFunction_regular_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.frameFunction_regular_sphere

-- Core.lean: the core lemma in the form Reduction.lean consumes, and the theorem.
/-- info: 'Gleason.coreLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.coreLemma

-- STAR STAR Gleason's theorem for C^N, N >= 3: every projection package is P |-> Re Tr(rho P) for a unique density matrix rho. Foundational triple; no hypothesis beyond N >= 3.
/-- info: 'Gleason.ProjectionPackage.gleason_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.ProjectionPackage.gleason_representation

-- Real.lean (2026-09-27, BACKLOG #58): A4, Gleason for real Hilbert spaces.
-- A1 over R: the frame function of a real package sums to 1 over every real orthonormal basis.
/-- info: 'Gleason.RealProjectionPackage.sum_frame_orthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.sum_frame_orthonormalBasis
-- A2 over R: the restriction to the span of an orthonormal family is a real frame function, of weight p of the family's projection (basis independent by the Gram identity).
/-- info: 'Gleason.RealProjectionPackage.isFrameFunction_restrictR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.isFrameFunction_restrictR
-- The core lemma of #57 applied to a triple.
/-- info: 'Gleason.RealProjectionPackage.exists_isSymm_restrictR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.exists_isSymm_restrictR
-- An orthonormal pair in R^N, N >= 3, extends to an orthonormal triple.
/-- info: 'Gleason.exists_orthonormal_tripleR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_orthonormal_tripleR
-- STAR The parallelogram law on R^N, by Gram-Schmidt on any two vectors.
/-- info: 'Gleason.extOf_parallelogramR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.extOf_parallelogramR
-- The real Jordan-von Neumann engine: a quadratic-like function is the quadratic form of its polarisation matrix.
/-- info: 'Gleason.IsQuadraticLikeR.eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsQuadraticLikeR.eq_dotProduct
-- STAR A4: the frame function of a real package is the quadratic form of a symmetric matrix on the unit sphere.
/-- info: 'Gleason.RealProjectionPackage.exists_isSymm_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.exists_isSymm_sphere
-- From a quadratic form on the real sphere to a density matrix.
/-- info: 'Gleason.quadraticForm_on_sphere_to_densityR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.quadraticForm_on_sphere_to_densityR
-- The real projection descent: p P = Tr(A P) for every orthogonal projection.
/-- info: 'Gleason.RealProjectionPackage.p_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.p_eq_trace
-- STAR Gleason's conclusion over R from the quadratic-form hypothesis.
/-- info: 'Gleason.RealProjectionPackage.existsUnique_density_of_frame_quadraticR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.existsUnique_density_of_frame_quadraticR
-- STAR STAR STAR Gleason's theorem for REAL Hilbert spaces, N >= 3: every real projection package is P |-> Tr(rho P) for a unique real density matrix. Foundational triple.
/-- info: 'Gleason.RealProjectionPackage.real_gleason_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.RealProjectionPackage.real_gleason_representation

-- RealFrame.lean (2026-09-28, BACKLOG #87): Gleason for bare real frame functions.
-- STAR A4 for any function quadratic on triples: the layer both real consumers share.
/-- info: 'Gleason.exists_isSymm_sphere_of_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_isSymm_sphere_of_quad
-- Two mutually orthogonal orthonormal families glue along a sum type.
/-- info: 'Gleason.orthonormal_sum_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.orthonormal_sum_elim
-- The frame sum is the weight over an orthonormal basis indexed by any finite type.
/-- info: 'Gleason.IsFrameFunction.sum_eq_of_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.sum_eq_of_basis
-- The frame sum splits along a completion.
/-- info: 'Gleason.IsFrameFunction.sum_elim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.sum_elim_eq
-- The orthogonal complement carries an orthonormal family of the complementary size.
/-- info: 'Gleason.exists_orthonormal_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_orthonormal_complement
-- A nonnegative frame function is bounded by its weight in any dimension.
/-- info: 'Gleason.IsFrameFunction.le_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.le_weight
-- A frame function is even on the sphere.
/-- info: 'Gleason.IsFrameFunction.neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.neg_eq
-- STAR STAR The weight of a 3-space is basis independent, so the restriction to its span is a frame function on R^3 -- the step the projection package gave for free.
/-- info: 'Gleason.IsFrameFunction.exists_weight_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.IsFrameFunction.exists_weight_restrict
-- STAR STAR A nonnegative frame function of weight 1 is a symmetric quadratic form on the sphere.
/-- info: 'Gleason.exists_isSymm_sphere_of_frameFunction_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.exists_isSymm_sphere_of_frameFunction_one
-- STAR STAR STAR Gleason's theorem for real FRAME FUNCTIONS, N >= 3 (the statement Gleason wrote): a nonnegative frame function of weight W is the quadratic form of a unique PSD matrix of trace W. Foundational triple.
/-- info: 'Gleason.existsUnique_density_of_frameFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Gleason.existsUnique_density_of_frameFunction

-- 2026-09-23, R-013 DISCHARGED (BACKLOG #16): Reversible/HybridLift.lean, the generic half.
-- gateMat g is the permutation matrix of a reversible gate's Boolean action (gateMat_CCX checks
-- it against Lift.lean's hand-built ccxAtMat). measureCorrectMat pairs g mo is the
-- measure-and-correct gadget on ancilla g at outcome mo: Hadamard, projection onto mo, a CZ per
-- pair when mo = 1. It is MONOMIAL (measureCorrectMat_basisState): a basis state goes to
-- (phase * <mo|H|w g>) |update w g mo>; when the ancilla holds the parity of ANDs the
-- corrections cancel, w g = andParity pairs w, the scalar is (sqrt 2)^-1 for both outcomes
-- (measureCorrect_scalar, the phase cancellation); when it does not, the mo = 1 branch carries
-- -(sqrt 2)^-1 (measureCorrect_scalar_of_ne). HybridGate / hybridLin / shadow / WellFormed /
-- gadgetCount: a hybrid gate list, its register semantics (a linear map), its Boolean shadow
-- (a gadget writes its outcome into the ancilla) and well-formedness. hybridLin_basisState:
-- on a well-formed basis input the hybrid circuit gives (sqrt 2)^-#gadgets * |shadow>;
-- hybridLin_sum extends it by linearity. The tensor factor the wall anticipated was not
-- needed: the induction carries a scalar. Foundational triple (andParity: propext,
-- Quot.sound; HybridGate: none).
/-- info: 'Reversible.gateMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gateMat

/-- info: 'Reversible.gateMat_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gateMat_basisState

/-- info: 'Reversible.gateMat_CCX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gateMat_CCX

/-- info: 'Reversible.andParity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andParity

/-- info: 'Reversible.correctionPhase_one_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.correctionPhase_one_eq_prod

/-- info: 'Reversible.measureCorrectMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.measureCorrectMat

/-- info: 'Reversible.measureCorrectMat_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.measureCorrectMat_basisState

/-- info: 'Reversible.measureCorrect_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.measureCorrect_scalar

/-- info: 'Reversible.measureCorrect_scalar_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.measureCorrect_scalar_of_ne

/-- info: 'Reversible.HybridGate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.HybridGate

/-- info: 'Reversible.hybridLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hybridLin

/-- info: 'Reversible.shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.shadow

/-- info: 'Reversible.WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.WellFormed

/-- info: 'Reversible.hybridLin_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hybridLin_basisState

/-- info: 'Reversible.hybridLin_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hybridLin_sum

/-- info: 'Reversible.shadow_gate_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.shadow_gate_list

-- 2026-09-23 (with BACKLOG #59): the Boolean-reading helpers of HybridLift.lean the Gidney
-- instance consumes -- a reversible gate's shadow reads as its denoteGate, and preserves every
-- wire it does not target.
/-- info: 'Reversible.stateOfReg_shadow_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.stateOfReg_shadow_gate

/-- info: 'Reversible.shadow_gate_apply_of_not_mem_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.shadow_gate_apply_of_not_mem_target

-- BACKLOG #50 (2026-09-23), LinearAlgebra/BilinearForm/SymplecticBasis.lean: symplectic bases of
-- alternating forms, over any field. IsSymplecticBasis: a basis indexed by iota + iota with
-- B p_i p_j = 0, B q_i q_j = 0, B p_i q_j = delta_ij. IsAlt.exists_isSymplecticBasis (STAR STAR):
-- every non-degenerate alternating form on a finite-dimensional space has one, by induction on
-- the dimension (Gram-Schmidt for alternating forms): a plane span {p, q} with B p q = 1 is split
-- off against its B-orthogonal complement (isCompl_orthogonal_of_restrict_nondegenerate), on
-- which the form stays non-degenerate. IsAlt.even_finrank: the dimension is even.
-- IsSymplecticBasis.apply_eq_sum: the standard form in symplectic coordinates. Mathlib at the pin
-- has orthogonal bases for symmetric forms only (iIsOrtho) and the symplectic group of matrices.
/-- info: 'LinearMap.BilinForm.IsAlt.exists_isSymplecticBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.BilinForm.IsAlt.exists_isSymplecticBasis

/-- info: 'LinearMap.BilinForm.IsAlt.even_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.BilinForm.IsAlt.even_finrank

/-- info: 'LinearMap.BilinForm.IsSymplecticBasis.apply_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.BilinForm.IsSymplecticBasis.apply_eq_sum

/-- info: 'LinearMap.BilinForm.IsSymplecticBasis.reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.BilinForm.IsSymplecticBasis.reindex

/-- info: 'LinearMap.BilinForm.IsSymplecticBasis.inr_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.BilinForm.IsSymplecticBasis.inr_inl

-- BACKLOG #50 (2026-09-23), Geometry/Manifold/DarbouxStandardForm.lean: Darboux's theorem in the
-- standard form. ContinuousAlternatingMap.toBilinForm: the bilinear form of a 2-form, alternating
-- and non-degenerate when the form is; standardSymplecticForm: sum dp_i wedge dq_i on
-- iota + iota -> R as a continuous alternating 2-form;
-- exists_continuousLinearEquiv_eq_standardSymplecticForm_comp (linear Darboux): a non-degenerate
-- 2-form is the pullback of the standard form by a linear isomorphism with R^{2n}, finrank = 2n;
-- exists_openPartialHomeomorph_pullback_standard (STAR STAR): the Moser chart composed with the
-- symplectic coordinates is a C^1 chart into R^{2n} with C^1 inverse in which omega is the
-- pullback of the standard form; IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_standard
-- (STAR STAR): the same on a symplectic manifold through localRep, the Darboux chart being
-- Psi o chartAt; IsSymplectic.even_finrank: a symplectic manifold has even dimension.
/-- info: 'ContinuousAlternatingMap.toBilinForm_isAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.toBilinForm_isAlt

/-- info: 'ContinuousAlternatingMap.toBilinForm_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.toBilinForm_nondegenerate

/-- info: 'standardSymplecticForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms standardSymplecticForm_apply

/-- info: 'exists_continuousLinearEquiv_eq_standardSymplecticForm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_continuousLinearEquiv_eq_standardSymplecticForm_comp

/-- info: 'exists_openPartialHomeomorph_pullback_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_openPartialHomeomorph_pullback_standard

/-- info: 'DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_standard

/-- info: 'DifferentialForm.IsSymplectic.even_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DifferentialForm.IsSymplectic.even_finrank

-- BACKLOG #60 (2026-09-23), Analysis/ODE/FlowDerivative.lean: linear ODEs on the whole interval.
-- norm_le_mul_exp_of_linearODE (Gronwall bound |Y t| <= |Y 0| exp(M t)),
-- hasDerivWithinAt_Icc_glue (two solutions on adjacent intervals agreeing at the junction glue
-- to one), exists_linearODE_solution_Icc (STAR): Y' = A(t) Y has a solution on all of [0, T] for
-- a continuous coefficient bounded by M, with no smallness condition, by concatenating the
-- short-time Picard-Lindelof solutions with a step length fixed by the Gronwall bound.
/-- info: 'norm_le_mul_exp_of_linearODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_le_mul_exp_of_linearODE

/-- info: 'hasDerivWithinAt_Icc_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivWithinAt_Icc_glue

/-- info: 'exists_linearODE_solution_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_linearODE_solution_Icc

-- BACKLOG #60 (2026-09-23), Analysis/ODE/FlowSmooth.lean: C^n dependence of a flow on its
-- initial point. hasFDerivAt_of_contDiffOn_uncurry (the partial derivative of a jointly C^1
-- field), exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry (the tube on which
-- hasFDerivAt_flow_of_variational_timeDependent applies), exists_variational_of_lipschitz (STAR:
-- C^1 dependence in Lipschitz form - the variational solution exists on [0, T], is the derivative
-- in the initial point, and is continuous in it), contDiffOn_flow_of_contDiffOn (STAR STAR): for
-- a jointly C^n field, 1 <= n <= infty, a flow confined to a compact convex set and Lipschitz in
-- the initial point is C^n in the initial point, by induction on n through the pair flow
-- (x, Z) -> (alpha x t, Y x t o Z) of the field (z, Z) -> (f t z, D(f t)(z) o Z) on E x (E ->L E),
-- which is one order less smooth. Mathlib at the pin has Picard-Lindelof and Lipschitz
-- dependence only.
/-- info: 'hasFDerivAt_of_contDiffOn_uncurry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_of_contDiffOn_uncurry

/-- info: 'exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isOpen_hasFDerivAt_of_contDiffOn_uncurry

/-- info: 'exists_variational_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_variational_of_lipschitz

/-- info: 'contDiffOn_flow_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_flow_of_contDiffOn

-- BACKLOG #60 (2026-09-23), Analysis/Calculus/ContDiffParametricIntervalIntegral.lean: a
-- parametric interval integral of a jointly C^n scalar integrand is C^n in the parameter
-- (finite-dimensional parameter space, n <= infty), by induction: the derivative of the integral
-- is the integral of the partial derivative (dominated), and applied to a fixed vector it is
-- again a parametric integral of a jointly C^(n-1) integrand (contDiffOn_clm_apply). With it the
-- Poincare primitive (Poincare.lean: contDiffOn_radialPrimitiveVal', contDiffOn_radialPrimitive',
-- contDiffOn_radialPrimitiveForm'), Moser's field (Darboux.lean: contDiffOn_moserPrimitive',
-- contDiffOn_moserForm_uncurry', contDiffOn_moserFieldJoint') and hence the Darboux chart are
-- C^n for a C^n form; exists_openPartialHomeomorph_pullback_eq now takes the order n and its
-- manifold form concludes C^infty and membership in the C^infty maximal atlas.
/-- info: 'exists_closedBall_prod_Icc_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_closedBall_prod_Icc_subset

/-- info: 'contDiffOn_intervalIntegral_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_intervalIntegral_of_contDiffOn

/-- info: 'contDiffOn_evalPair'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_evalPair'

/-- info: 'contDiffOn_radialPrimitiveVal'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitiveVal'

/-- info: 'contDiffOn_radialPrimitive'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitive'

/-- info: 'contDiffOn_radialPrimitiveForm'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_radialPrimitiveForm'

/-- info: 'contDiffOn_moserPrimitive'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_moserPrimitive'

/-- info: 'contDiffOn_moserForm_uncurry'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_moserForm_uncurry'

/-- info: 'contDiffOn_moserFieldJoint'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_moserFieldJoint'

-- BACKLOG #51 (2026-09-23), Probability/CodeCapacityThreshold.lean: the probabilistic core of
-- the code-capacity threshold. measure_pi_two_or_more_le (STAR): under the product of n copies of
-- a probability measure, the patterns with two or more coordinates in a set of measure <= q
-- have measure <= C(n,2) q^2 (union bound over pairs, each pair cylinder through
-- Measure.pi_pi). codeCapacityBound: the recursion p -> c p^2, closed form (c p)^(2^k)/c
-- (codeCapacityBound_eq), below p when c p <= 1 (codeCapacityBound_le), tending to 0 when
-- c p < 1 (tendsto_codeCapacityBound, STAR - the threshold). ConcatPat/concatMeasure/concatBad:
-- the error patterns of a k-fold concatenated n-block code under independent noise with the
-- bad patterns (an error at level 0, two or more bad sub-blocks at level k+1);
-- concatMeasure_concatBad_le (STAR STAR): they obey the recursion.
/-- info: 'measure_pi_two_or_more_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms measure_pi_two_or_more_le

/-- info: 'codeCapacityBound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codeCapacityBound_eq

/-- info: 'codeCapacityBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codeCapacityBound_le

/-- info: 'tendsto_codeCapacityBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_codeCapacityBound

/-- info: 'concatMeasure_concatBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concatMeasure_concatBad_le

-- BACKLOG #62 (a) (2026-09-28), Probability/CircuitThreshold.lean: the circuit-level
-- accounting. card_concatPat (STAR): a level-k gadget has n^k fault locations, so its
-- pattern space has 2^(n^k) elements - the overhead of the recursive simulation.
-- circuitMeasure/circuitBad: independent faults at every location of every gadget of a
-- circuit of N locations, the circuit failing when some gadget is bad;
-- circuitMeasure_circuitBad_le (STAR STAR): the union bound over the locations on top of
-- the code-capacity recursion, N (c p)^(2^k)/c. mul_codeCapacityBound_lt_of_log_div_lt
-- (STAR): any k with 2^k > log(c eps/N)/log(c p) suffices - the level grows like log log.
-- exists_level_mul_lt, exists_level_circuitMeasure_lt (STAR STAR STAR): below the
-- threshold every accuracy is reached at some level, whatever the circuit's size.
-- blockKron_replace_eq_gateOf_mul (STAR STAR, BlockKron.lean): error propagation - a
-- fault at one block of a tensor-over-blocks operator is a single-block error after the
-- ideal operator.
/-- info: 'card_concatPat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_concatPat

/-- info: 'circuitMeasure_circuitBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms circuitMeasure_circuitBad_le

/-- info: 'mul_codeCapacityBound_lt_of_log_div_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_codeCapacityBound_lt_of_log_div_lt

/-- info: 'exists_level_mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_level_mul_lt

/-- info: 'exists_level_circuitMeasure_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_level_circuitMeasure_lt

/-- info: 'QuantumInfo.blockKron_replace_eq_gateOf_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.blockKron_replace_eq_gateOf_mul

-- BACKLOG #62 (b) and (e) (2026-09-28). QuantumInfo/TransversalClifford.lean:
-- pauliMat_eq_blockKron (STAR STAR): a Pauli string IS the tensor product of its
-- single-qubit Paulis, onePauli (a i) (b i). hGateM_conj_onePauli (STAR): the four cases of
-- H X H = Z, H Z H = X, with the sign (-1)^{uv}. hadTransversal_conj_pauliMat (STAR STAR):
-- the transversal Hadamard exchanges the X- and Z-labels of every Pauli string - the
-- single-qubit rule raised to the tensor power, and the mechanism of transversality.
-- Probability/CircuitThreshold.lean, the overhead: pow_eq_rpow_logb (the identity
-- L^k = (2^k)^(log2 L)), exists_level_two_pow_le (STAR STAR: the level meeting an accuracy
-- has 2^k <= 4X, X the logarithm ratio - doubly logarithmic) and
-- exists_level_overhead_le (STAR STAR STAR: the gadget's L^k fault locations are at most
-- (4X)^(log2 L), a fixed power of a logarithm - polylogarithmic overhead).
/-- info: 'QuantumInfo.pauliMat_eq_blockKron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pauliMat_eq_blockKron

/-- info: 'QuantumInfo.hGateM_conj_onePauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.hGateM_conj_onePauli

/-- info: 'QuantumInfo.hadTransversal_conj_pauliMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.hadTransversal_conj_pauliMat

-- BACKLOG #62 (f) (2026-09-28), the permutation-matrix layer of TransversalClifford.lean:
-- permMat sigma is the gate sending |w> to |sigma w>, with the row/column reindexing
-- lemmas (permMat_mul_apply, mul_permMat_apply) and, for an involution, Hermitian,
-- self-inverse and unitary. A transversal CNOT is one of these, which is why its logical
-- action needs no amplitudes.
/-- info: 'QuantumInfo.permMat_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.permMat_mul_apply

/-- info: 'QuantumInfo.mul_permMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.mul_permMat_apply

/-- info: 'QuantumInfo.permMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.permMat_mul_self

/-- info: 'QuantumInfo.permMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.permMat_mem_unitaryGroup

/-- info: 'pow_eq_rpow_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pow_eq_rpow_logb

/-- info: 'exists_level_two_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_level_two_pow_le

/-- info: 'exists_level_overhead_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_level_overhead_le

/-- info: 'WignerFunction.fourier_comp_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.fourier_comp_affine

/-- info: 'WignerFunction.conj_wigner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.conj_wigner

/-- info: 'WignerFunction.integral_wigner_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_wigner_right

/-- info: 'WignerFunction.wigner_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_fourier

/-- info: 'WignerFunction.integral_wigner_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_wigner_left

/-- info: 'WignerFunction.wigner_gaussianS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_gaussianS

/-- info: 'WignerFunction.wigner_gaussianS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_gaussianS_pos

/-- info: 'WignerFunction.re_wigner_zero_zero_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.re_wigner_zero_zero_neg

/-- info: 'WignerFunction.wigner_freeSchrodingerS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_freeSchrodingerS

/-- info: 'GeometricPhase.hasFDerivAt_connectionFormT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometricPhase.hasFDerivAt_connectionFormT

/-- info: 'GeometricPhase.curvature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometricPhase.curvature_eq

/-- info: 'GeometricPhase.geometricPhase_eq_neg_integral_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometricPhase.geometricPhase_eq_neg_integral_curvature

/-! ### T-gate injection (MagicInjection.lean, 2026-09-23, BACKLOG #66-#67, closes R-006) -/

/-- info: 'QuantumInfo.injectSlice_magicState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.injectSlice_magicState

/-- info: 'QuantumInfo.norm_sq_injectSlice_magicState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.norm_sq_injectSlice_magicState

/-- info: 'QuantumInfo.injectSlice_zMagicState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.injectSlice_zMagicState

/-- info: 'QuantumInfo.injectionKraus_magicState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.injectionKraus_magicState

/-- info: 'QuantumInfo.injectionChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.injectionChannel_apply

/-- info: 'QuantumInfo.noisyInjectionChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.noisyInjectionChannel_apply

/-! ### The [[15, 1, 3]] code's combinatorics (ReedMuller15.lean, 2026-09-23, BACKLOG #75, R-004 (a)) -/

/-- info: 'ReedMuller15.syndrome_ne_zero_of_weight_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller15.syndrome_ne_zero_of_weight_two

/-- info: 'ReedMuller15.card_undetected_weight_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller15.card_undetected_weight_three

/-- info: 'ReedMuller15.dotp_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller15.dotp_add_one

/-- info: 'ReedMuller15.card_undetected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller15.card_undetected

/-! ### The [[15, 1, 3]] code space and its transversal T (ReedMuller15Code.lean, 2026-09-23, BACKLOG #76, R-004 (b)) -/

/-- info: 'QuantumInfo.ReedMuller15.pauliOp_row_logical0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.pauliOp_row_logical0

/-- info: 'QuantumInfo.ReedMuller15.tTrans_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.tTrans_eq_comp

/-- info: 'QuantumInfo.ReedMuller15.tTrans_logical0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.tTrans_logical0

/-- info: 'QuantumInfo.ReedMuller15.tTrans_logical1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.tTrans_logical1

/-- info: 'QuantumInfo.ReedMuller15.tTrans_logicalPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.tTrans_logicalPlus

/-! ### Z-error patterns on the encoded magic state (ReedMuller15Errors.lean, 2026-09-23, BACKLOG #77, R-004 (c)) -/

/-- info: 'QuantumInfo.ReedMuller15.measProj_row_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.measProj_row_z

/-- info: 'QuantumInfo.ReedMuller15.exists_reject_of_syndrome_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.exists_reject_of_syndrome_ne_zero

/-- info: 'QuantumInfo.ReedMuller15.pauliOp_z_logical1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.pauliOp_z_logical1

/-- info: 'QuantumInfo.ReedMuller15.pauliOp_z_encodedMagic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.pauliOp_z_encodedMagic

/-- info: 'QuantumInfo.ReedMuller15.outQubit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.outQubit_eq

/-- info: 'QuantumInfo.ReedMuller15.sGate_magicConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.sGate_magicConj

/-- info: 'QuantumInfo.ReedMuller15.parity_eq_one_iff_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.parity_eq_one_iff_odd

/-! ### The 15-to-1 distillation bound (ReedMuller15Distill.lean, 2026-09-24, BACKLOG #78, closes R-004) -/

/-- info: 'QuantumInfo.ReedMuller15.patternMeasure_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.patternMeasure_singleton

/-- info: 'QuantumInfo.ReedMuller15.measure_acceptSet_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.measure_acceptSet_ge

/-- info: 'QuantumInfo.ReedMuller15.measure_wrongSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.measure_wrongSet_le

/-- info: 'QuantumInfo.ReedMuller15.distillation_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.distillation_error_le

/-- info: 'QuantumInfo.ReedMuller15.distillation_error_le_ninety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.distillation_error_le_ninety

/-- info: 'QuantumInfo.ReedMuller15.distillIter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.distillIter_le

/-- info: 'QuantumInfo.ReedMuller15.tendsto_distillIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.tendsto_distillIter

/-! ### The irrational angle of T.HTH (CliffordTAngle.lean, 2026-09-25, BACKLOG #68, R-005 (a)) -/

/-- info: 'isIntegral_two_mul_cos_of_eq_two_pi_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isIntegral_two_mul_cos_of_eq_two_pi_mul

/-- info: 'not_isIntegral_of_sq_add_self_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_isIntegral_of_sq_add_self_eq

/-- info: 'QuantumInfo.CliffordT.cos_htAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.cos_htAngle

/-- info: 'QuantumInfo.CliffordT.irrational_htAngle_div_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.irrational_htAngle_div_two_pi

/-- info: 'QuantumInfo.CliffordT.denseRange_zsmul_htAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.denseRange_zsmul_htAngle

/-- info: 'QuantumInfo.CliffordT.exists_zsmul_htAngle_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.exists_zsmul_htAngle_approx

/-- info: 'QuantumInfo.CliffordT.trace_htht' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.trace_htht

/-- info: 'QuantumInfo.CliffordT.det_htht' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.det_htht

/-- info: 'QuantumInfo.CliffordT.trace_htht_eq_cos_htAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.CliffordT.trace_htht_eq_cos_htAngle

/-! ### The axis-angle layer and the word's dense circle (SU2Rotation.lean, 2026-09-25, BACKLOG #80) -/

/-- info: 'QuantumInfo.SU2.su2_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_mul

/-- info: 'QuantumInfo.SU2.su2_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_det

/-- info: 'QuantumInfo.SU2.axisRot_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_add

/-- info: 'QuantumInfo.SU2.axisRot_nat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_nat_mul

/-- info: 'QuantumInfo.SU2.htAxis_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.htAxis_unit

/-- info: 'QuantumInfo.SU2.htht_eq_su2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.htht_eq_su2

/-- info: 'QuantumInfo.SU2.htht_eq_axisRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.htht_eq_axisRot

/-- info: 'QuantumInfo.SU2.htht_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.htht_pow

/-- info: 'QuantumInfo.SU2.irrational_htAngle_div_four_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.irrational_htAngle_div_four_pi

/-- info: 'QuantumInfo.SU2.mem_closure_range_axisRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.mem_closure_range_axisRot

/-! ### Two-level unitaries (Matrix/TwoLevel.lean, 2026-09-25, BACKLOG #70, R-005 (c);
the `d(d − 1)/2` count 2026-09-28, BACKLOG #82) -/

/-- info: 'QuantumInfo.TwoLevel.IdOutside.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.IdOutside.mul

/-- info: 'QuantumInfo.TwoLevel.twoLevelMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.twoLevelMat_mul

/-- info: 'QuantumInfo.TwoLevel.twoLevelMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.twoLevelMat_mem_unitaryGroup

/-- info: 'QuantumInfo.TwoLevel.givensMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.givensMat_mem_unitaryGroup

/-- info: 'QuantumInfo.TwoLevel.givensMat_mulVec_apply_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.givensMat_mulVec_apply_snd

/-- info: 'QuantumInfo.TwoLevel.givensMat_mulVec_apply_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.givensMat_mulVec_apply_fst

/-- info: 'QuantumInfo.TwoLevel.exists_clear_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.exists_clear_column

/-- info: 'QuantumInfo.TwoLevel.row_eq_of_col_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.row_eq_of_col_eq

/-- info: 'QuantumInfo.TwoLevel.exists_twoLevel_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.exists_twoLevel_prod

/-- info: 'QuantumInfo.TwoLevel.sum_normSq_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.sum_normSq_col

/-- info: 'QuantumInfo.TwoLevel.isTwoLevel_of_idOutside_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.isTwoLevel_of_idOutside_card_le_two

/-- info: 'QuantumInfo.TwoLevel.exists_twoLevel_prod_of_idOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.exists_twoLevel_prod_of_idOutside

/-- info: 'QuantumInfo.TwoLevel.exists_twoLevel_prod_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.TwoLevel.exists_twoLevel_prod_length

/-! ### Multiply-controlled gates and the Gray-code sandwich (MultiControlled.lean, 2026-09-26, BACKLOG #71) -/

/-- info: 'QuantumInfo.MultiControlled.swapMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.swapMat_apply

/-- info: 'QuantumInfo.MultiControlled.swapMat_conj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.swapMat_conj_apply

/-- info: 'QuantumInfo.MultiControlled.idOutside_swapMat_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.idOutside_swapMat_conj

/-- info: 'QuantumInfo.MultiControlled.ctrlGate_eq_twoLevelMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.ctrlGate_eq_twoLevelMat

/-- info: 'QuantumInfo.MultiControlled.exists_ctrlGate_of_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.exists_ctrlGate_of_adjacent

/-- info: 'QuantumInfo.MultiControlled.isMultiCtrlX_swapMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.isMultiCtrlX_swapMat

/-- info: 'QuantumInfo.MultiControlled.exists_multiCtrl_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.exists_multiCtrl_sandwich

/-- info: 'QuantumInfo.MultiControlled.exists_multiCtrl_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.MultiControlled.exists_multiCtrl_list

/-! ### Controlled gates on a set of controls (ControlledGate.lean, 2026-09-26, BACKLOG #83) -/

/-- info: 'QuantumInfo.Controlled.ctrlSet_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSet_one

/-- info: 'QuantumInfo.Controlled.ctrlSet_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSet_mul

/-- info: 'QuantumInfo.Controlled.ctrlSet_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSet_conjTranspose

/-- info: 'QuantumInfo.Controlled.ctrlSet_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSet_mem_unitaryGroup

/-- info: 'QuantumInfo.Controlled.singleGate_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.singleGate_mem_unitaryGroup

/-- info: 'QuantumInfo.Controlled.cnotGate'_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.cnotGate'_mem_unitaryGroup

/-- info: 'QuantumInfo.Controlled.ctrlSet_erase_eq_ctrlGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSet_erase_eq_ctrlGate

/-! ### The z-y-z Euler decomposition and the ABC identity (EulerDecomposition.lean,
2026-09-26, BACKLOG #84) -/

/-- info: 'QuantumInfo.SU2.su2_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_mem_unitaryGroup

/-- info: 'QuantumInfo.SU2.axisRot_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_mem_unitaryGroup

/-- info: 'QuantumInfo.Euler.rz_ry_rz_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.rz_ry_rz_eq

/-- info: 'QuantumInfo.Euler.adjugate_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.adjugate_entries

/-- info: 'QuantumInfo.Euler.exists_euler_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_euler_of_det_one

/-- info: 'QuantumInfo.Euler.exists_euler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_euler

/-- info: 'QuantumInfo.Euler.abc_prod_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.abc_prod_eq_one

/-- info: 'QuantumInfo.Euler.abc_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.abc_identity

/-- info: 'QuantumInfo.Euler.exists_abc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_abc

/-! ### One control: C¹(U) from two CNOTs and single-qubit gates (ControlledSingle.lean,
2026-09-26, BACKLOG #84) -/

/-- info: 'QuantumInfo.Controlled.ctrlChoice_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlChoice_one

/-- info: 'QuantumInfo.Controlled.ctrlChoice_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlChoice_mul

/-- info: 'QuantumInfo.Controlled.gateOf_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.gateOf_mem_unitaryGroup

/-- info: 'QuantumInfo.Controlled.ctrlOf_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlOf_mem_unitaryGroup

/-- info: 'QuantumInfo.Controlled.diagGate_eq_ctrlChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.diagGate_eq_ctrlChoice

/-- info: 'QuantumInfo.Controlled.ctrlOf_eq_ctrlChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlOf_eq_ctrlChoice

/-- info: 'QuantumInfo.Controlled.ctrlOf_eq_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlOf_eq_circuit

/-! ### Axis-angle form and square roots (EulerDecomposition.lean, 2026-09-26,
BACKLOG #85) -/

/-- info: 'QuantumInfo.SU2.axisRot_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_det

/-- info: 'QuantumInfo.Euler.expI_smul_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.expI_smul_mem_unitaryGroup

/-- info: 'QuantumInfo.Euler.exists_su2_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_su2_of_det_one

/-- info: 'QuantumInfo.Euler.exists_axisRot_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_axisRot_of_det_one

/-- info: 'QuantumInfo.Euler.exists_sqrt_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_sqrt_of_det_one

/-- info: 'QuantumInfo.Euler.exists_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Euler.exists_sqrt

/-! ### The control-count recursion (ControlRecursion.lean, 2026-09-26, BACKLOG #85) -/

/-- info: 'QuantumInfo.Controlled.xGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.xGate_apply

/-- info: 'QuantumInfo.Controlled.xGate_conj_ctrlSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.xGate_conj_ctrlSet

/-- info: 'QuantumInfo.Controlled.diagBlock_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.diagBlock_mul

/-- info: 'QuantumInfo.Controlled.flipBlock_conj_diagBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.flipBlock_conj_diagBlock

/-- info: 'QuantumInfo.Controlled.diagBlock_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.diagBlock_five

/-- info: 'QuantumInfo.Controlled.pairSet_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.pairSet_mul

/-- info: 'QuantumInfo.Controlled.ctrlSetOf_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSetOf_insert

/-- info: 'QuantumInfo.Controlled.ctrlOf_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlOf_mem_closure

/-- info: 'QuantumInfo.Controlled.ctrlSetOf_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlSetOf_mem_closure

/-- info: 'QuantumInfo.Controlled.ctrlGateOf_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.ctrlGateOf_mem_closure

/-! ### Clifford+T fills the determinant-one unitaries (CliffordTDensity.lean, 2026-09-26,
BACKLOG #81) -/

/-- info: 'not_isIntegral_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_isIntegral_of_quadratic

/-- info: 'QuantumInfo.SU2.htA_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.htA_sq

/-- info: 'QuantumInfo.SU2.two_mul_cos_wAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.two_mul_cos_wAngle

/-- info: 'QuantumInfo.SU2.not_isIntegral_two_mul_cos_wAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.not_isIntegral_two_mul_cos_wAngle

/-- info: 'QuantumInfo.SU2.irrational_wAngle_div_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.irrational_wAngle_div_two_pi

/-- info: 'QuantumInfo.SU2.exists_euler_zxz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_euler_zxz

/-- info: 'QuantumInfo.SU2.exists_euler_two_axes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_euler_two_axes

/-- info: 'QuantumInfo.SU2.axisRot_mem_of_irrational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_mem_of_irrational

/-- info: 'QuantumInfo.SU2.axisRot_htAxis_pi_mul_hGateM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_htAxis_pi_mul_hGateM

/-- info: 'QuantumInfo.SU2.axisRot_htAxis_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_htAxis_mem

/-- info: 'QuantumInfo.SU2.axisRot_wAxis_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_wAxis_mem

/-- info: 'QuantumInfo.SU2.axisRot_uAxis_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_uAxis_mem

/-- info: 'QuantumInfo.SU2.det_one_mem_cliffordTLim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.det_one_mem_cliffordTLim

/-- info: 'QuantumInfo.SU2.exists_phase_mem_cliffordTLim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_phase_mem_cliffordTLim

/-! ### Clifford+T is universal, closing R-005 (CliffordTUniversal.lean, 2026-09-26,
BACKLOG #73) -/

/-- info: 'QuantumInfo.Controlled.block_mem_unitaryGroup_of_ctrlSetOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.block_mem_unitaryGroup_of_ctrlSetOf

/-- info: 'QuantumInfo.Controlled.block_mem_unitaryGroup_of_ctrlGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.block_mem_unitaryGroup_of_ctrlGate

/-- info: 'QuantumInfo.Controlled.twoLevel_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.twoLevel_mem_closure

/-- info: 'QuantumInfo.Controlled.mem_closure_elementary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.mem_closure_elementary

/-- info: 'QuantumInfo.Controlled.gateOf_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.gateOf_smul

/-- info: 'QuantumInfo.Controlled.gateOf_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.gateOf_mul

/-- info: 'QuantumInfo.Controlled.continuous_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.continuous_gateOf

/-- info: 'QuantumInfo.Controlled.gateOf_mem_cliffordTmLim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.gateOf_mem_cliffordTmLim

/-- info: 'QuantumInfo.Controlled.elementary_le_phaseLim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.elementary_le_phaseLim

/-- info: 'QuantumInfo.Controlled.exists_phase_mem_cliffordTmLim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.exists_phase_mem_cliffordTmLim

/-! ### Discretization: the recovery corrects the span (KnillLaflamme.lean, 2026-09-26,
BACKLOG #61) -/

/-- info: 'QuantumInfo.recovery_apply_lin_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.recovery_apply_lin_comb

/-- info: 'QuantumInfo.exists_smul_recovery_apply_of_eq_lin_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_smul_recovery_apply_of_eq_lin_comb

/-! ### The decoder of the 15-to-1 protocol as a CNOT circuit (ReedMuller15Decoder.lean,
2026-09-27, BACKLOG #79) -/

/-- info: 'QuantumInfo.Controlled.cnotGate'_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.cnotGate'_apply

/-- info: 'QuantumInfo.Controlled.cnotGate'_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.cnotGate'_mulVec_apply

/-- info: 'QuantumInfo.Controlled.cnotListMat_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.cnotListMat_mulVec_apply

/-- info: 'QuantumInfo.Controlled.cnotListMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Controlled.cnotListMat_mem_unitaryGroup

/-- info: 'QuantumInfo.ReedMuller15.cnotListPull_decoderList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.cnotListPull_decoderList

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_mulVec_apply

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_mem_unitaryGroup

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_mulVec_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_mulVec_basisState

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_logical_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_logical_update

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_logical_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_logical_apply_zero

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_encodedMagic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_encodedMagic

/-- info: 'QuantumInfo.ReedMuller15.decoderCircuit_encodedMagic_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ReedMuller15.decoderCircuit_encodedMagic_apply

/-! ### The tensor over blocks, and Knill-Laflamme in encoder form (BlockKron.lean,
KnillLaflamme.lean, 2026-09-27, BACKLOG #86) -/

/-- info: 'QuantumInfo.blockKron_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.blockKron_mul

/-- info: 'QuantumInfo.blockKron_sum_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.blockKron_sum_smul

/-- info: 'QuantumInfo.blockKron_single_eq_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.blockKron_single_eq_gateOf

/-- info: 'QuantumInfo.knillLaflamme_of_encoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.knillLaflamme_of_encoder

/-- info: 'QuantumInfo.encoder_of_knillLaflamme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.encoder_of_knillLaflamme

/-- info: 'QuantumInfo.exists_recovery_of_encoderKL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_recovery_of_encoderKL

/-- info: 'QuantumInfo.smul_eq_one_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.smul_eq_one_of_unitary

/-! BACKLOG #56 (BP-5): the rotating frame and the spin-½ axis-angle calculus. -/

/-- info: 'QuantumInfo.RotatingFrame.hasDerivAt_mul_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.hasDerivAt_mul_of_gen

/-- info: 'QuantumInfo.RotatingFrame.schrodingerUnitary_hasDerivAt_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.schrodingerUnitary_hasDerivAt_left

/-- info: 'QuantumInfo.RotatingFrame.rotHam_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.rotHam_isHermitian

/-- info: 'QuantumInfo.RotatingFrame.rotProp_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.rotProp_mem_unitaryGroup

/-- info: 'QuantumInfo.RotatingFrame.hasDerivAt_rotProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.hasDerivAt_rotProp

/-- info: 'QuantumInfo.RotatingFrame.hasDerivAt_rotState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.hasDerivAt_rotState

/-- info: 'QuantumInfo.RotatingFrame.inner_toEuclideanCLM_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.inner_toEuclideanCLM_left

/-- info: 'QuantumInfo.RotatingFrame.inner_toEuclideanCLM_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.RotatingFrame.inner_toEuclideanCLM_unitary

/-- info: 'QuantumInfo.SU2.pauliAxis_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.pauliAxis_mul_self

/-- info: 'QuantumInfo.SU2.axisRot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_eq

/-- info: 'QuantumInfo.SU2.axisRot_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_two_pi

/-- info: 'QuantumInfo.SU2.smul_pauliAxis_mul_axisRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.smul_pauliAxis_mul_axisRot

/-- info: 'QuantumInfo.SU2.hasDerivAt_axisRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.hasDerivAt_axisRot

/-- info: 'QuantumInfo.SU2.hasDerivAt_axisRot_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.hasDerivAt_axisRot_right

/-- info: 'QuantumInfo.SU2.axisRot_z_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_z_conj

/-! BACKLOG #65: the curvature of the geometric phase is the Fubini–Study form. -/

/-- info: 'Projectivization.studyForm_add_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_add_smul_left

/-- info: 'Projectivization.studyForm_add_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_add_smul_right

/-- info: 'Projectivization.studyForm_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_smul

/-- info: 'Projectivization.studyForm_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_lift

/-- info: 'Projectivization.studyForm_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_of_unit

/-- info: 'Projectivization.re_inner_deriv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.re_inner_deriv_eq_zero

/-- info: 'Projectivization.fsModelForm_eq_studyForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_eq_studyForm

/-- info: 'Projectivization.chartVelCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.chartVelCLM_apply

/-- info: 'Projectivization.hasDerivAt_coordRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasDerivAt_coordRatio

/-- info: 'Projectivization.insertOne_coordRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertOne_coordRatio

/-- info: 'Projectivization.insertZero_chartVelCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.insertZero_chartVelCLM

/-- info: 'Projectivization.studyForm_chartVelCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.studyForm_chartVelCLM

/-- info: 'Projectivization.fsModelForm_eq_neg_two_mul_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsModelForm_eq_neg_two_mul_curvature

/-- info: 'Projectivization.hasMFDerivAt_projCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasMFDerivAt_projCurve

/-- info: 'Projectivization.fsForm_eq_neg_two_mul_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsForm_eq_neg_two_mul_curvature

/-- info: 'Projectivization.curvature_eq_neg_half_fsPullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.curvature_eq_neg_half_fsPullback

/-- info: 'Projectivization.geometricPhase_eq_half_integral_fsPullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.geometricPhase_eq_half_integral_fsPullback

/-! BACKLOG #89: the two-parameter pushforward, and `[Ψ]^* ω_FS` as a bundled `2`-form. -/

/-- info: 'HasFDerivAt.div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasFDerivAt.div

-- BACKLOG #46 (2026-09-28), Analysis/Calculus/SchrodingerCurrent.lean: the probability
-- current and the continuity equation, with the two single-trajectory readings.
-- hasDerivAt_probCurrent (STAR): d_x J = Im(conj psi d^2_x psi), the Im(conj dpsi dpsi) = 0
-- cancellation. hasDerivAt_probDensity_time (STAR): d_t rho = 2 Re(conj psi d_t psi).
-- continuity_equation (STAR STAR): d_t rho + d_x J = 0 from the pointwise Schrodinger
-- equation with a real potential. probCurrent_polar (STAR): J = R^2 d_x S in polar form,
-- so continuity_polar (STAR STAR) is BOHM'S EQUIVARIANCE, d_t rho + d_x(rho v) = 0, and
-- hasDerivAt_density_along_trajectory (STAR STAR) is its Lagrangian form d rho/dt =
-- -rho d_x v. nelsonFlux with nelson_fokkerPlanck (STAR STAR): the same flux split with
-- the osmotic drift solves the Fokker-Planck equation of Nelson's diffusion.
/-- info: 'Schrodinger.hasDerivAt_probCurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.hasDerivAt_probCurrent

/-- info: 'Schrodinger.hasDerivAt_probDensity_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.hasDerivAt_probDensity_time

/-- info: 'Schrodinger.continuity_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.continuity_equation

/-- info: 'Schrodinger.probCurrent_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.probCurrent_polar

/-- info: 'Schrodinger.continuity_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.continuity_polar

/-- info: 'Schrodinger.hasDerivAt_density_along_trajectory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.hasDerivAt_density_along_trajectory

/-- info: 'Schrodinger.nelsonFlux_eq_mul_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.nelsonFlux_eq_mul_drift

/-- info: 'Schrodinger.nelson_fokkerPlanck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Schrodinger.nelson_fokkerPlanck

-- BACKLOG #47 (2026-09-28), Dynamics/Koopman.lean: classical mechanics in Hilbert space.
-- koopmanL2 (STAR): the Koopman operator of a measure-preserving map as a LINEAR isometry of
-- L^2 (Mathlib has the AddMonoidHom and its isometry, not the linear packaging).
-- koopmanUnitary (STAR STAR): for an invertible measure-preserving map it is unitary - a
-- LinearIsometryEquiv whose inverse is the Koopman operator of the inverse map.
-- koopmanL2_flow (STAR STAR): the group law U_{s+t} = U_t U_s, so t -> U_t is a
-- one-parameter unitary group. koopmanFun_mul: on observables the map is an algebra
-- homomorphism for the pointwise product - the classical side of the contrast.
-- hasDerivAt_koopmanFun (STAR): the generator on differentiable observables, the derivative
-- of f along the flow's velocity field; in a Darboux chart that is the Poisson bracket
-- (SigmaLayer/ChartBracket.lean's hasDerivAt_koopmanFun_poissonBracket, the Liouvillian).
/-- info: 'Koopman.koopmanL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Koopman.koopmanL2

/-- info: 'Koopman.koopmanUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Koopman.koopmanUnitary

/-- info: 'Koopman.koopmanL2_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Koopman.koopmanL2_flow

/-- info: 'Koopman.koopmanFun_mul' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Koopman.koopmanFun_mul

/-- info: 'Koopman.hasDerivAt_koopmanFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Koopman.hasDerivAt_koopmanFun

/-- info: 'ContinuousAlternatingMap.compContinuousLinearMap_apply_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousAlternatingMap.compContinuousLinearMap_apply_pair

/-- info: 'instHasTranslationAtlasSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instHasTranslationAtlasSelf

/-- info: 'Projectivization.hasFDerivAt_coordRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasFDerivAt_coordRatio

/-- info: 'Projectivization.hasMFDerivAt_projFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.hasMFDerivAt_projFamily

/-- info: 'Projectivization.mfderiv_projFamily_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mfderiv_projFamily_apply

/-- info: 'Projectivization.fsPullbackForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPullbackForm_apply

/-- info: 'Projectivization.fsPullbackForm_eq_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPullbackForm_eq_chart

/-- info: 'Projectivization.contDiffAt_fsPullbackForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contDiffAt_fsPullbackForm

/-- info: 'Projectivization.contMDiff_fsPullbackFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.contMDiff_fsPullbackFamily

/-- info: 'Projectivization.fsPullbackForm_apply_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.fsPullbackForm_apply_coord

/-- info: 'Projectivization.curvature_eq_neg_half_fsPullbackForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.curvature_eq_neg_half_fsPullbackForm

/-- info: 'Projectivization.geometricPhase_eq_half_integral_fsPullbackForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.geometricPhase_eq_half_integral_fsPullbackForm

/-! BACKLOG #55 (BP-4): the Aharonov–Bohm ring, its spectrum and its gauges. -/

/-- info: 'QuantumInfo.AharonovBohm.flux_ringHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.flux_ringHam

/-- info: 'QuantumInfo.AharonovBohm.ringHamOf_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringHamOf_isHermitian

/-- info: 'QuantumInfo.AharonovBohm.ringMode_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringMode_sub_one

/-- info: 'QuantumInfo.AharonovBohm.stdAddChar_neg_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.stdAddChar_neg_eq_conj

/-- info: 'QuantumInfo.AharonovBohm.bondPhase_mul_stdAddChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.bondPhase_mul_stdAddChar

/-- info: 'QuantumInfo.AharonovBohm.ringHam_mulVec_ringMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringHam_mulVec_ringMode

/-- info: 'QuantumInfo.AharonovBohm.ringEigval_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringEigval_add_two_pi

/-- info: 'QuantumInfo.AharonovBohm.ringEigval_add_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringEigval_add_card

/-- info: 'QuantumInfo.AharonovBohm.range_ringEigval_add_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.range_ringEigval_add_two_pi

/-- info: 'QuantumInfo.AharonovBohm.hasEigenvalue_ringHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.hasEigenvalue_ringHam

/-- info: 'QuantumInfo.AharonovBohm.gaugeDiag_conjTranspose_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.gaugeDiag_conjTranspose_mul

/-- info: 'QuantumInfo.AharonovBohm.gaugeDiag_conj_ringHamOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.gaugeDiag_conj_ringHamOf

/-- info: 'QuantumInfo.AharonovBohm.flux_gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.flux_gauge

/-- info: 'QuantumInfo.AharonovBohm.flux_oneBondPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.flux_oneBondPhase

/-- info: 'QuantumInfo.AharonovBohm.uniform_add_oneBondGauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.uniform_add_oneBondGauge

/-- info: 'QuantumInfo.AharonovBohm.gaugeDiag_conj_ringHam_oneBond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.gaugeDiag_conj_ringHam_oneBond

/-- info: 'QuantumInfo.AharonovBohm.sum_stdAddChar_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.sum_stdAddChar_mul

/-- info: 'QuantumInfo.AharonovBohm.dftMatrix_conjTranspose_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.dftMatrix_conjTranspose_mul

/-- info: 'QuantumInfo.AharonovBohm.dftMatrix_conj_ringHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.dftMatrix_conj_ringHam

/-- info: 'QuantumInfo.AharonovBohm.eq_ringEigval_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.eq_ringEigval_of_mulVec

/-- info: 'QuantumInfo.AharonovBohm.ringEigval_three_pi_ne_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringEigval_three_pi_ne_two

/-- info: 'QuantumInfo.AharonovBohm.not_exists_unitary_conj_ringHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.not_exists_unitary_conj_ringHam

/-- info: 'ProbabilityTheory.ChainedBell.abs_marginalA_sub_marginalB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.abs_marginalA_sub_marginalB_le

/-- info: 'ProbabilityTheory.ChainedBell.abs_marginalA_add_marginalB_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.abs_marginalA_add_marginalB_sub_one_le

/-- info: 'ProbabilityTheory.ChainedBell.abs_marginalA_sub_marginalB_chain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.abs_marginalA_sub_marginalB_chain_le

/-- info: 'ProbabilityTheory.ChainedBell.abs_marginalA_sub_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.abs_marginalA_sub_half_le

/-- info: 'ProbabilityTheory.ChainedBell.integral_abs_marginalA_sub_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.integral_abs_marginalA_sub_half_le

/-- info: 'ProbabilityTheory.ChainedBell.exists_signalling_of_sharp_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.ChainedBell.exists_signalling_of_sharp_integral

/-- info: 'WignerFunction.integral_wigner_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_wigner_mul_conj

/-- info: 'WignerFunction.integral_mulConj_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_mulConj_shift

/-- info: 'WignerFunction.integral_integral_wigner_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_integral_wigner_mul_conj

/-- info: 'WignerFunction.integral_integral_wigner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_integral_wigner_sq

/-- info: 'WignerFunction.integrable_weylPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_weylPair

/-- info: 'WignerFunction.integral_weylPair_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_weylPair_x

/-- info: 'WignerFunction.integral_conj_mul_weylOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_conj_mul_weylOp

/-- info: 'QuantumInfo.AharonovBohm.fluxDist_le_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.fluxDist_le_abs

/-- info: 'QuantumInfo.AharonovBohm.fluxDist_le_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.fluxDist_le_pi

/-- info: 'QuantumInfo.AharonovBohm.ringEigval_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringEigval_le

/-- info: 'QuantumInfo.AharonovBohm.ringEigval_neg_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.ringEigval_neg_round

/-- info: 'QuantumInfo.AharonovBohm.isGreatest_range_ringEigval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.isGreatest_range_ringEigval

/-- info: 'QuantumInfo.AharonovBohm.fluxDist_eq_of_range_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.fluxDist_eq_of_range_eq

/-- info: 'QuantumInfo.AharonovBohm.range_ringEigval_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.range_ringEigval_neg

/-- info: 'QuantumInfo.AharonovBohm.exists_eq_of_range_ringEigval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohm.exists_eq_of_range_ringEigval_eq

-- Aharonov–Bohm on the circle (BACKLOG #90): the continuum twin of the ring above. The
-- Fourier modes are Mathlib's own (`circleMode_eq_fourier`), the twisted eigenvalue equation
-- is pointwise on them, and the determination theorem is about `Set.range (circleEigval Φ)`.

/-- info: 'QuantumInfo.AharonovBohmCircle.circleMode_eq_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.circleMode_eq_fourier

/-- info: 'QuantumInfo.AharonovBohmCircle.circleMode_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.circleMode_periodic

/-- info: 'QuantumInfo.AharonovBohmCircle.hasDerivAt_circleMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.hasDerivAt_circleMode

/-- info: 'QuantumInfo.AharonovBohmCircle.twisted_deriv_circleMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.twisted_deriv_circleMode

/-- info: 'QuantumInfo.AharonovBohmCircle.hasDerivAt_twisted_circleMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.hasDerivAt_twisted_circleMode

/-- info: 'QuantumInfo.AharonovBohmCircle.twisted_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.twisted_eigen

/-- info: 'QuantumInfo.AharonovBohmCircle.sq_sub_round_le_circleEigval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.sq_sub_round_le_circleEigval

/-- info: 'QuantumInfo.AharonovBohmCircle.isLeast_range_circleEigval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.isLeast_range_circleEigval

/-- info: 'QuantumInfo.AharonovBohmCircle.range_circleEigval_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.range_circleEigval_add_one

/-- info: 'QuantumInfo.AharonovBohmCircle.range_circleEigval_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.range_circleEigval_neg

/-- info: 'QuantumInfo.AharonovBohmCircle.exists_eq_of_range_circleEigval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.exists_eq_of_range_circleEigval_eq

/-- info: 'QuantumInfo.AharonovBohmCircle.gauge_periodic_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.gauge_periodic_iff

-- Diagonal operators on a Hilbert basis (BACKLOG #93(a)): the unbounded self-adjoint
-- operator with a prescribed spectrum. The `LinearPMap` adjoint machinery is Mathlib's;
-- the resolvent set and the spectrum of an operator with a domain are defined here.

/-- info: 'Memℓp.mul_of_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Memℓp.mul_of_bddAbove

/-- info: 'lp.norm_mul_le_of_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp.norm_mul_le_of_bddAbove

/-- info: 'HilbertBasis.basis_mem_diagDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.basis_mem_diagDomain

/-- info: 'HilbertBasis.dense_diagDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.dense_diagDomain

/-- info: 'HilbertBasis.repr_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.repr_diagOp

/-- info: 'HilbertBasis.diagOp_apply_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.diagOp_apply_basis

/-- info: 'HilbertBasis.diagOp_isFormalAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.diagOp_isFormalAdjoint

/-- info: 'HilbertBasis.repr_adjoint_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.repr_adjoint_diagOp

/-- info: 'HilbertBasis.isSelfAdjoint_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.isSelfAdjoint_diagOp

/-- info: 'LinearPMap.bijective_of_isResolventAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.bijective_of_isResolventAt

/-- info: 'LinearPMap.mem_spectrum_of_apply_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.mem_spectrum_of_apply_eq_smul

/-- info: 'HilbertBasis.norm_diagCLM_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.norm_diagCLM_apply_le

/-- info: 'HilbertBasis.mem_resolventSet_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.mem_resolventSet_diagOp

/-- info: 'HilbertBasis.closure_range_subset_spectrum_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.closure_range_subset_spectrum_diagOp

/-- info: 'HilbertBasis.spectrum_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.spectrum_diagOp

/-- info: 'HilbertBasis.mem_spectrum_diagOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HilbertBasis.mem_spectrum_diagOp

-- The Weyl calculus (BACKLOG #92(b)(c)): phase space as a measure space (joint
-- measurability, square-integrability, the product-measure overlap identity) and the three
-- temperate symbols x, ξ, xξ as moment identities in operator form.

/-- info: 'WignerFunction.integral_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_fourier

/-- info: 'WignerFunction.integral_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_deriv

/-- info: 'WignerFunction.integral_mul_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_mul_fourier

/-- info: 'WignerFunction.integral_mul_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_mul_deriv

/-- info: 'WignerFunction.integral_mul_wigner_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_mul_wigner_right

/-- info: 'WignerFunction.integral_deriv_mul_conj_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_deriv_mul_conj_add

/-- info: 'WignerFunction.integral_mul_deriv_mul_conj_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_mul_deriv_mul_conj_add

/-- info: 'WignerFunction.integral_integral_wigner_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_integral_wigner_pos

/-- info: 'WignerFunction.integral_integral_wigner_mom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_integral_wigner_mom

/-- info: 'WignerFunction.integral_integral_wigner_posMom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_integral_wigner_posMom

/-- info: 'WignerFunction.stronglyMeasurable_wigner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.stronglyMeasurable_wigner

/-- info: 'WignerFunction.integrable_wignerEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_wignerEnergy

/-- info: 'WignerFunction.integrable_normSq_wigner_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_normSq_wigner_prod

/-- info: 'WignerFunction.integrable_wigner_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_wigner_mul_conj

/-- info: 'WignerFunction.integral_prod_wigner_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_prod_wigner_mul_conj

/-- info: 'WignerFunction.integral_prod_wigner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_prod_wigner_sq

-- The twisted Laplacian on L²(S¹) (BACKLOG #93(b)(c)): the Fourier-coefficient bridge for
-- derivatives, the diagonalisation of −(∂ − iΦ)², and the flux determined by the spectrum of a
-- self-adjoint operator rather than by a chosen level set.

/-- info: 'QuantumInfo.AharonovBohmCircle.exists_eq_of_sq_sub_round_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.AharonovBohmCircle.exists_eq_of_sq_sub_round_eq

/-- info: 'CircleFourier.fourierCoeffOn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.fourierCoeffOn_add

/-- info: 'CircleFourier.fourierCoeffOn_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.fourierCoeffOn_deriv

/-- info: 'CircleFourier.fourierCoeffOn_deriv_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.fourierCoeffOn_deriv_two_pi

/-- info: 'CircleFourier.fourierCoeffOn_twistedLap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.fourierCoeffOn_twistedLap

/-- info: 'CircleFourier.isSelfAdjoint_twistedOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.isSelfAdjoint_twistedOp

/-- info: 'CircleFourier.spectrum_twistedOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.spectrum_twistedOp

/-- info: 'CircleFourier.twistedOp_apply_fourierBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.twistedOp_apply_fourierBasis

/-- info: 'CircleFourier.twistedOp_apply_of_fourierCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.twistedOp_apply_of_fourierCoeff

/-- info: 'CircleFourier.periodic_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.periodic_deriv

/-- info: 'CircleFourier.fourierCoeff_toL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.fourierCoeff_toL2

/-- info: 'CircleFourier.twistedOp_toL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.twistedOp_toL2

/-- info: 'CircleFourier.isLeast_norm_image_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.isLeast_norm_image_spectrum

/-- info: 'CircleFourier.exists_eq_of_spectrum_twistedOp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircleFourier.exists_eq_of_spectrum_twistedOp_eq

-- The Moyal bracket of a potential (BACKLOG #64): the potential term of the Wigner
-- evolution as the Wigner transform of a commutator, and its classical limit with the
-- third-derivative remainder — exact when the third derivative vanishes.

/-- info: 'WignerFunction.norm_symmDiff_V''_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_symmDiff_V''_le

/-- info: 'WignerFunction.norm_symmDiff_V'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_symmDiff_V'_le

/-- info: 'WignerFunction.norm_symmDiff_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_symmDiff_sub_le

/-- info: 'WignerFunction.norm_symmDiff_sub_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_symmDiff_sub_le'

/-- info: 'WignerFunction.wignerKernel₂_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wignerKernel₂_self

/-- info: 'WignerFunction.wigner₂_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner₂_eq_integral

/-- info: 'WignerFunction.moyalPot_eq_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.moyalPot_eq_comm

/-- info: 'WignerFunction.deriv_wigner_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.deriv_wigner_right

/-- info: 'WignerFunction.integrable_moyalPot_integrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_moyalPot_integrand

/-- info: 'WignerFunction.poisson_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.poisson_eq_integral

/-- info: 'WignerFunction.norm_moyalPot_sub_poisson_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_moyalPot_sub_poisson_le

/-- info: 'WignerFunction.moyalPot_eq_poisson_of_third_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.moyalPot_eq_poisson_of_third_deriv_zero

-- BACKLOG #44 FC-5' (2026-10-01), Analysis/Semigroup/FresnelKernel.lean: Feynman's kernel for the
-- free propagator. The heat kernel (4 pi w)^{-1/2} e^{-x^2/(4w)} at COMPLEX time w is a Schwartz
-- function for Re w > 0 whose Fourier transform is the multiplier e^{-4 pi^2 w xi^2}; convolution
-- with it is a semigroup in w, so every time-slicing is exact. Its eps -> 0 limit on the imaginary
-- axis is the free propagator (dominated convergence on the Fourier side), and at w = it/2 the
-- kernel IS Feynman's (2 pi i t)^{-1/2} e^{i x^2/(2t)}, of constant modulus -- bounded, so the
-- integral against Schwartz (hence L^1) data converges absolutely and the kernel formula holds
-- EXACTLY, with no regularisation left in it. The n-slice product of kernels is amp^n e^{i S_n}
-- with S_n the discrete action sum (q_{k+1} - q_k)^2/(2 dt).
/-- info: 'SchrodingerGroup.coe_fresnelS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.coe_fresnelS

/-- info: 'SchrodingerGroup.fourier_fresnelS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fourier_fresnelS

/-- info: 'SchrodingerGroup.fresnelOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fresnelOp_apply

/-- info: 'SchrodingerGroup.fourier_fresnelOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fourier_fresnelOp

/-- info: 'SchrodingerGroup.fresnelOp_fresnelOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fresnelOp_fresnelOp

/-- info: 'SchrodingerGroup.fresnelOp_iterate_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fresnelOp_iterate_div

/-- info: 'SchrodingerGroup.fresnelOp_iterate_succ_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fresnelOp_iterate_succ_apply

/-- info: 'SchrodingerGroup.fourier_freeSchrodingerS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fourier_freeSchrodingerS

/-- info: 'SchrodingerGroup.tendsto_fresnelOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.tendsto_fresnelOp

/-- info: 'SchrodingerGroup.tendsto_integral_fresnelKernel_freeSchrodingerS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.tendsto_integral_fresnelKernel_freeSchrodingerS

/-- info: 'SchrodingerGroup.tendsto_fresnelOp_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.tendsto_fresnelOp_iterate

/-- info: 'SchrodingerGroup.fresnelKernel_I_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.fresnelKernel_I_mul

/-- info: 'SchrodingerGroup.norm_fresnelKernel_I_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.norm_fresnelKernel_I_mul

/-- info: 'SchrodingerGroup.integrable_fresnelKernel_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.integrable_fresnelKernel_mul

/-- info: 'SchrodingerGroup.tendsto_integral_fresnelKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.tendsto_integral_fresnelKernel

/-- info: 'SchrodingerGroup.freeSchrodingerS_eq_integral_fresnel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.freeSchrodingerS_eq_integral_fresnel

/-- info: 'SchrodingerGroup.freeSchrodingerS_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.freeSchrodingerS_iterate

/-- info: 'SchrodingerGroup.prod_fresnelKernel_eq_exp_discreteAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.prod_fresnelKernel_eq_exp_discreteAction

-- BACKLOG #64 time-dependent half, free part (2026-10-01), Analysis/Fourier/WignerEvolution.lean:
-- THE FREE WIGNER EQUATION. The Wigner integrand decays like 1/(1+y^2) UNIFORMLY IN THE POSITION
-- (the two arguments x +- y/2 differ by y, so 1 + y^2 <= 2(1+(x+y/2)^2)(1+(x-y/2)^2) and the two
-- Schwartz bounds multiply), which lets the x-derivative pass under the Fourier integral by
-- Mathlib's first-order parametric-differentiation lemma: d/dx W = W(psi', psi) + W(psi, psi'),
-- a sum of cross Wigner functions. Differentiating the exact free transport in t then gives
-- d/dt W_t = -2 pi xi d/dx W_t, i.e. d/dt W + p d/dx W = 0 in the momentum p = 2 pi xi: the
-- classical Liouville equation as a PDE satisfied by the quantum phase-space density, exact.
-- The interacting equation stays open on the propagator, not on the derivative (row 64).
/-- info: 'WignerFunction.exists_bound_one_add_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_one_add_sq

/-- info: 'WignerFunction.norm_mul_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_mul_norm_le

/-- info: 'WignerFunction.integrable_phase_mul_kernel₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_phase_mul_kernel₂

/-- info: 'WignerFunction.hasDerivAt_wignerKernel_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.hasDerivAt_wignerKernel_left

/-- info: 'WignerFunction.hasDerivAt_wigner_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.hasDerivAt_wigner_left

/-- info: 'WignerFunction.deriv_wigner_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.deriv_wigner_left

/-- info: 'WignerFunction.hasDerivAt_wigner_freeSchrodingerS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.hasDerivAt_wigner_freeSchrodingerS_pos

/-- info: 'WignerFunction.hasDerivAt_wigner_freeSchrodingerS_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.hasDerivAt_wigner_freeSchrodingerS_time

/-- info: 'WignerFunction.wigner_liouville' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_liouville

/-- info: 'WignerFunction.wigner_liouville_add_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.wigner_liouville_add_eq_zero

-- BACKLOG #64/#93 continuum operator layer (2026-10-02), Analysis/InnerProductSpace/MultiplicationOperator.lean:
-- MULTIPLICATION BY A REAL MEASURABLE FUNCTION AS AN UNBOUNDED SELF-ADJOINT OPERATOR on L^2(mu),
-- the continuum companion of #93(a)'s diagonal operator (which needs a basis, so it reaches only
-- discrete spectra). The cut-offs {|m| <= n} exhaust alpha because m is real-valued, and that one
-- lemma replaces every limiting argument: density (a vector orthogonal to the domain is killed by
-- every cut-off), maximality (the adjoint's value is m.y on every cut-off set, so its domain
-- cannot be larger), and the two-sided spectrum bound - a bounded inverse off the closure of the
-- values, and approximate eigenvectors at every essential value. No dominated convergence, no
-- spectral theorem, no Stone.
/-- info: 'MeasureTheory.L2.mulCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.mulCLM

/-- info: 'MeasureTheory.L2.coeFn_mulCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.coeFn_mulCLM

/-- info: 'MeasureTheory.L2.ae_eq_zero_of_ae_eq_zero_on_cutSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.ae_eq_zero_of_ae_eq_zero_on_cutSet

/-- info: 'MeasureTheory.L2.cutCLM_mem_mulDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.cutCLM_mem_mulDomain

/-- info: 'MeasureTheory.L2.inner_cutCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.inner_cutCLM

/-- info: 'MeasureTheory.L2.dense_mulDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.dense_mulDomain

/-- info: 'MeasureTheory.L2.mulOp_isFormalAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.mulOp_isFormalAdjoint

/-- info: 'MeasureTheory.L2.coeFn_adjoint_mulOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.coeFn_adjoint_mulOp

/-- info: 'MeasureTheory.L2.isSelfAdjoint_mulOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.isSelfAdjoint_mulOp

/-- info: 'MeasureTheory.L2.mem_resolventSet_mulOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.mem_resolventSet_mulOp

/-- info: 'MeasureTheory.L2.mem_spectrum_mulOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.mem_spectrum_mulOp

-- BACKLOG #64/#93 continuum operator layer (2026-10-02), Analysis/Semigroup/FreeHamiltonian.lean:
-- THE FREE HAMILTONIAN IN THE MOMENTUM REPRESENTATION is multiplication by the corpus's own
-- freeSymbol 2 pi^2 xi^2: self-adjoint on its natural domain, and its SPECTRUM IS THE NONNEGATIVE
-- REAL AXIS, both inclusions (the symbol's range is [0, infinity) and is closed, so the resolvent
-- exists off it; every ball around a nonnegative real has preimage of positive measure because it
-- is a nonempty open set, and of finite measure because it is bounded). The group and the
-- generator are built from one function; Stone's theorem, the position-space conjugate and H_0 + V
-- are not here (row 64).
/-- info: 'SchrodingerGroup.range_freeSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.range_freeSymbol

/-- info: 'SchrodingerGroup.isClosed_nonnegAxis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.isClosed_nonnegAxis

/-- info: 'SchrodingerGroup.range_ofReal_freeSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.range_ofReal_freeSymbol

/-- info: 'SchrodingerGroup.dense_domain_freeSymbolOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.dense_domain_freeSymbolOp

/-- info: 'SchrodingerGroup.isSelfAdjoint_freeSymbolOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.isSelfAdjoint_freeSymbolOp

/-- info: 'SchrodingerGroup.spectrum_freeSymbolOp_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.spectrum_freeSymbolOp_subset

/-- info: 'SchrodingerGroup.mem_spectrum_freeSymbolOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.mem_spectrum_freeSymbolOp

/-- info: 'SchrodingerGroup.spectrum_freeSymbolOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.spectrum_freeSymbolOp

-- BACKLOG #64(i): CONJUGATING AN UNBOUNDED OPERATOR BY A UNITARY
-- (Mathlib/Analysis/InnerProductSpace/LinearPMapConj.lean + the position representation in
-- Analysis/Semigroup/FreeHamiltonian.lean, 2026-10-09).
-- Row 64 recorded three pieces it waits on, and this is the first: conjugating a LinearPMap by a
-- unitary, so the momentum-space operator moves to position space.
-- LinearPMap.conjIsometry is U T U-inverse, with domain U(dom T). Mathlib has LinearMap.compPMap (a
-- bounded map after a partial one, same domain) and LinearPMap.comp (two partial ones with a domain
-- condition), and nothing that moves an operator ACROSS a unitary - which is what a change of
-- representation is.
-- WHAT MAKES IT SHORT IS THE ORDER ON LinearPMap, not a computation of the adjoint's domain.
-- conjIsometry U T-adjoint is shown to be a FORMAL adjoint of conjIsometry U T (four inner products,
-- a unitary moving across each time: IsFormalAdjoint.conjIsometry), so Mathlib's
-- IsFormalAdjoint.le_adjoint gives one inclusion; the other is the same statement for U-inverse,
-- through conjIsometry_symm_conjIsometry and conjIsometry_conjIsometry_symm (conjugation is an
-- involution) and conjIsometry_mono (it is monotone), with le_antisymm closing it. Hence
-- adjoint_conjIsometry - THE ADJOINT CONJUGATES - and IsSelfAdjoint.conjIsometry, a unitary
-- conjugate of a self-adjoint operator is self-adjoint.
-- conjIsometry_apply_of_eq is the technical workhorse: the conjugate's value at any element whose
-- coordinate is an image point. Stating it that way is what avoids rewriting under a membership
-- proof, which is where every earlier attempt in this file died (motive is not type correct).
-- resolventSet_conjIsometry and spectrum_conjIsometry: THE SPECTRUM IS UNCHANGED, with conjCLM the
-- conjugated bounded inverse. A change of representation does not move the spectrum, and this is
-- that sentence as a theorem; note it needs no completeness, so it sits above that hypothesis.
-- THE APPLICATION, which is why the row wanted it: freePositionOp is the free Hamiltonian in the
-- POSITION representation, the momentum-space multiplication operator conjugated by the Fourier
-- transform - which IS a unitary of L2 at this pin (MeasureTheory.Lp.fourierTransformₗᵢ, which the
-- row did not know was there). isSelfAdjoint_freePositionOp and spectrum_freePositionOp transfer
-- self-adjointness and the nonnegative real axis with no second computation, and
-- freePositionOp_apply is the unitary equivalence that makes the name honest.
-- NOT claimed. UNITARY, NOT MERELY ISOMETRIC: the inverse has to exist for the conjugate to be
-- defined on all of U(dom T), and a non-surjective isometry gives a compression, not a conjugate.
-- SAME FIELD: U is 𝕜-linear, so this is not the antiunitary (conjugate-linear) case, which is a
-- genuinely different statement. NO FUNCTIONAL CALCULUS: that the conjugate has the same functional
-- calculus, or that unitary equivalence preserves a spectral measure, is not claimed - only the
-- resolvent set, which is what the spectrum is defined from here.
-- AND freePositionOp IS NOT YET IDENTIFIED WITH -(1/2)d²/dx². It is the conjugate, with its domain
-- the Fourier image of the momentum domain; proving it IS the second derivative there needs the
-- Fourier-derivative identity at the L2 level and the identification of that image as a Sobolev
-- space, which is a separate brick. #64's remaining two pieces (bounded symmetric perturbation,
-- Stone's theorem) are untouched by this.
-- Foundational-triple.
/-- info: 'LinearPMap.conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.conjIsometry

/-- info: 'LinearPMap.conjIsometry_apply_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.conjIsometry_apply_of_eq

/-- info: 'LinearPMap.conjIsometry_symm_conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.conjIsometry_symm_conjIsometry

/-- info: 'LinearPMap.conjIsometry_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.conjIsometry_mono

/-- info: 'LinearPMap.dense_conjIsometry_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.dense_conjIsometry_domain

/-- info: 'LinearPMap.spectrum_conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.spectrum_conjIsometry

/-- info: 'LinearPMap.IsFormalAdjoint.conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.IsFormalAdjoint.conjIsometry

/-- info: 'LinearPMap.adjoint_conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.adjoint_conjIsometry

/-- info: 'IsSelfAdjoint.conjIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSelfAdjoint.conjIsometry

/-- info: 'SchrodingerGroup.freePositionOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.freePositionOp

/-- info: 'SchrodingerGroup.freePositionOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.freePositionOp_apply

/-- info: 'SchrodingerGroup.isSelfAdjoint_freePositionOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.isSelfAdjoint_freePositionOp

/-- info: 'SchrodingerGroup.spectrum_freePositionOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.spectrum_freePositionOp

-- BACKLOG #64(ii): A BOUNDED SYMMETRIC PERTURBATION KEEPS SELF-ADJOINTNESS AND THE DOMAIN
-- (Mathlib/Analysis/InnerProductSpace/LinearPMapPerturb.lean + isSymmetric_mulCLM in
-- MultiplicationOperator.lean + the Schrodinger operator in Analysis/Semigroup/FreeHamiltonian.lean,
-- 2026-10-09). The second of row 64's three recorded pieces.
-- LinearPMap.addCLM is T + V for a bounded V, with domain EXACTLY dom T. Mathlib's + on LinearPMap
-- intersects domains, so T + V.toPMap-top has domain dom T meet top, which is equal to dom T but not
-- syntactically it, and a perturbation statement wants the domain unchanged on the nose.
-- WHY THE DOMAIN IS THE WHOLE CONTENT. Symmetry of T + V is three lines and says nothing: with an
-- unbounded operator the issue is always MAXIMALITY, that the adjoint has no larger domain.
-- addCLM_adjointDomain is where that is settled, and it needs only BOUNDEDNESS of V, not symmetry -
-- the functional x -> inner y (V x) is continuous outright, so it cannot affect whether
-- x -> inner y (T x) is. That is exactly why the bounded case is elementary and Kato-Rellich proper
-- (a merely relatively bounded perturbation with relative bound < 1) is not: there the domain
-- argument needs the resolvent and a Neumann series.
-- adjoint_addCLM is the general statement, (T + V)-adjoint = T-adjoint + V, which does NOT need T
-- self-adjoint; IsSelfAdjoint.addCLM is the corollary that a bounded symmetric perturbation
-- preserves self-adjointness on the same domain.
-- isSymmetric_mulCLM DISCHARGES the hypothesis for the only perturbation the corpus needs:
-- multiplication by a bounded REAL function is symmetric as a bounded operator, reality being the
-- whole of it, exactly as for the unbounded mulOp.
-- AND THE PAYOFF IS WHY (i) AND (ii) BELONG TOGETHER. The free Hamiltonian lives in the MOMENTUM
-- representation and a potential multiplies in the POSITION representation, so H0 + V is only a
-- statement once both are in the same place: (i) moved H0 across the Fourier transform and (ii) adds
-- the potential there. schrodingerOp is H0 + V in the position representation and
-- isSelfAdjoint_schrodingerOp is SELF-ADJOINTNESS FOR EVERY BOUNDED REAL POTENTIAL, on the free
-- Hamiltonian's own domain.
-- NOT claimed. BOUNDED, NOT RELATIVELY BOUNDED: V is a ContinuousLinearMap, and the Kato-Rellich
-- theorem for T-bounded perturbations with relative bound < 1 - the version that covers Coulomb
-- potentials - is a different theorem that is not proved here. NO SEMIBOUNDEDNESS, NO FORM SUMS
-- (nothing about KLMN or quadratic forms, which is how potentials that are not operator-bounded are
-- handled). SYMMETRIC IS TAKEN AS THE HYPOTHESIS in the form LinearMap.IsSymmetric rather than
-- IsSelfAdjoint for a ContinuousLinearMap: they agree for a bounded operator on a complete space and
-- the symmetric form is what a consumer discharges. AND row 64's THIRD piece, STONE'S THEOREM, is
-- untouched: the generator of the interacting dynamics now exists as a self-adjoint operator, and
-- turning it into the unitary group the equation differentiates is still absent from the pin.
-- Foundational-triple.
/-- info: 'LinearPMap.addCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.addCLM

/-- info: 'LinearPMap.addCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.addCLM_apply

/-- info: 'LinearPMap.continuous_inner_apply_clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.continuous_inner_apply_clm

/-- info: 'LinearPMap.addCLM_adjointDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.addCLM_adjointDomain

/-- info: 'LinearPMap.adjoint_addCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearPMap.adjoint_addCLM

/-- info: 'IsSelfAdjoint.addCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSelfAdjoint.addCLM

/-- info: 'MeasureTheory.L2.isSymmetric_mulCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.L2.isSymmetric_mulCLM

/-- info: 'SchrodingerGroup.schrodingerOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.schrodingerOp

/-- info: 'SchrodingerGroup.isSelfAdjoint_schrodingerOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.isSelfAdjoint_schrodingerOp

/-- info: 'SchrodingerGroup.dense_domain_schrodingerOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.dense_domain_schrodingerOp

-- BACKLOG #64(iii): THE PHASE GROUP'S GENERATOR IS ITS MULTIPLICATION OPERATOR
-- (Mathlib/Analysis/Semigroup/PhaseGenerator.lean, 2026-10-09) - AND A CORRECTION TO THAT ROW.
-- Row 64 said it waits on STONE'S THEOREM. IT DOES NOT, and that is the finding. Stone's theorem is
-- an EXISTENCE statement (every self-adjoint operator generates a unitary group). Here the group was
-- already explicit - phaseGroup, with its group law, unitarity and strong continuity all proved in
-- SchrodingerGroup.lean - and #64(i)+(ii) made the generator self-adjoint. What was missing is only
-- that the two are RELATED, which is a derivative computation, not an existence theorem.
-- (The corpus does have Stone's theorem in FINITE DIMENSIONS, Analysis/Matrix/StoneC1.lean, in both
-- the C1 and the continuity-only forms; the infinite-dimensional existence theorem is still absent
-- from the pin and is NOT needed by #64.)
-- hasDerivAt_phaseGroup_apply is the theorem: on the natural domain, d/dt of e^{-it kappa} f is
-- -i kappa e^{-it kappa} f in L2. THE PROOF IS A SCALAR DOMINATED CONVERGENCE, and the domain
-- hypothesis is not a technical convenience - IT IS THE DOMINATING FUNCTION. The difference between
-- the slope and the claimed derivative is multiplication by phaseDefect, so its squared L2 norm is
-- the scalar integral of (norm f)^2 (norm phaseDefect)^2 (norm_sq_eq_integral); that integrand tends
-- to 0 pointwise by the scalar exponential's derivative (tendsto_phaseDefect) and is dominated by
-- 4 (norm (kappa f))^2, integrable exactly because f is in the domain. norm_phaseDefect_le is the
-- uniform bound, which rides the global estimate norm_phaseFun_sub_one_le (Mathlib's
-- Real.norm_exp_I_mul_ofReal_sub_one_le, valid for all t, not just small t).
-- hasDerivAt_phaseGroup_freeSymbolOp and hasDerivAt_fourierGroup_freePositionOp are THE FREE
-- SCHRODINGER EQUATION IN BOTH REPRESENTATIONS, with the generator being the SELF-ADJOINT OPERATOR
-- of #64(i) rather than a fresh object - which is what makes "H0 generates the free dynamics" a
-- statement rather than a name. The position form APPLIES THE FOURIER ISOMETRY to the momentum form
-- through #64(i)'s conjugation lemmas and recomputes nothing.
-- phaseGroup_mem_mulDomain: the group PRESERVES THE DOMAIN, free here because a phase commutes with
-- a multiplication, and the first thing an interacting version needs.
-- NOT claimed. THE INTERACTING GENERATOR IS NOT HERE. SchrodingerGroup.schrodinger already exists as
-- a unitary propagator for a bounded potential (Dyson series, Duhamel, Trotter, in
-- Semigroup/BoundedPerturbation.lean) and #64(ii) made H0 + V self-adjoint, but differentiating the
-- Duhamel integral - showing the MILD solution is a CLASSICAL one - needs more than the domain
-- invariance proved here, and that is #129. AND ONE DERIVATIVE IS NOT A FLOW STATEMENT: nothing here
-- says the orbit is the unique solution of the Cauchy problem.
-- Foundational-triple.
/-- info: 'SchrodingerGroup.norm_sq_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.norm_sq_eq_integral

/-- info: 'SchrodingerGroup.norm_phaseFun_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.norm_phaseFun_sub_one_le

/-- info: 'SchrodingerGroup.hasDerivAt_phaseFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.hasDerivAt_phaseFun

/-- info: 'SchrodingerGroup.norm_phaseDefect_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.norm_phaseDefect_le

/-- info: 'SchrodingerGroup.tendsto_phaseDefect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.tendsto_phaseDefect

/-- info: 'SchrodingerGroup.coeFn_slope_phaseGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.coeFn_slope_phaseGroup

/-- info: 'SchrodingerGroup.hasDerivAt_phaseGroup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.hasDerivAt_phaseGroup_apply

/-- info: 'SchrodingerGroup.phaseGroup_mem_mulDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.phaseGroup_mem_mulDomain

/-- info: 'SchrodingerGroup.hasDerivAt_phaseGroup_freeSymbolOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.hasDerivAt_phaseGroup_freeSymbolOp

/-- info: 'SchrodingerGroup.hasDerivAt_fourierGroup_freePositionOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.hasDerivAt_fourierGroup_freePositionOp

/-- info: 'SchrodingerGroup.coeFn_phaseGroup_freeSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchrodingerGroup.coeFn_phaseGroup_freeSymbol

-- BACKLOG #62(d1) (2026-10-02), QuantumInfo/FaultTolerantComposition.lean: COMPOSING CORRECTED
-- GADGETS ALONG A CIRCUIT. A corrected step returns the IDEAL gadget's output on code states and
-- the ideal gadget keeps code states in the code; those two conditions compose, so a circuit whose
-- every gadget is faulty and whose every fault is corrected computes exactly what the ideal circuit
-- computes. The step is an arbitrary map on density operators, so a faulty recovery (#62(c)) plugs
-- into the same theorem. Deterministic half only: no fault counting, no level reduction.
/-- info: 'QuantumInfo.isCodeState_idealRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCodeState_idealRun

/-- info: 'QuantumInfo.correctedRun_eq_idealRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.correctedRun_eq_idealRun

/-- info: 'QuantumInfo.isCorrectedCircuit_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedCircuit_replicate


-- EFFECTIVE STOCHASTICITY: WHEN A COARSE-GRAINED DETERMINISTIC ORBIT IS APPROXIMATELY MARKOV
-- (BACKLOG #100, Mathlib/Dynamics/CoarseMarkov.lean, 2026-10-04). A deterministic map observed only
-- through a finite coarse-graining produces a stochastic-LOOKING process; this says when it is
-- approximately Markov and with what error. The point of the design is that the hypothesis and the
-- conclusion are about DIFFERENT OBJECTS: MicroDecoupled is about the MICROSTATE (conditioning on
-- the whole coarse history moves the law of the microstate at step n by at most eps, uniformly over
-- measurable sets, compared with conditioning on the present coarse value), while the conclusions
-- are about the COARSE PROCESS. Assuming instead that the coarse process forgets its history would
-- be assuming the conclusion - that is the circularity this file is built to avoid.
-- abs_condProb_coarseEvent_sub_le is the one-step Markov error, via the bridge coarseEvent_succ_eq
-- (a coarse future event IS a microstate event pulled back along the flow).
-- measure_historyEvent_toReal_eq_prod is the EXACT chain rule, with no hypothesis beyond
-- non-degeneracy, and abs_measure_historyEvent_sub_markov_le is the headline: the path probability
-- factorises up to n*eps, i.e. "approximately Markovian with an explicit error", proved on the
-- elementary product comparison abs_prod_sub_prod_le_sum.
-- TWO BOUNDARY RESULTS. condProb_coarseEvent_succ_of_autonomous: when the coarse variable is
-- autonomous the transitions are 0/1 indicators and the error is 0 with NO hypothesis, so the
-- bounds are attainable. cex_not_microDecoupled: the four-point rotation coarse-grained into two
-- cells has P(C2=1 | C1=0, C0=0) = 1 but P(C2=1 | C1=0) = 1/2, so its coarse process is NOT Markov
-- and no eps < 1/2 exists for it - WITHOUT THIS THE THEOREMS COULD HAVE BEEN VACUOUS.
-- NOT claimed: that any dynamics satisfies MicroDecoupled (nothing supplies it, and for finite
-- unitary dynamics mixing is unavailable in principle, so the statement can only be conditional);
-- any connection to the corpus's HasCorrelationDecay, which bounds a two-point correlation of one
-- scalar observable and is a different kind of condition; uniformity in n (the error is additive,
-- useless once n ~ 1/eps, and no infinite-horizon or invariant-measure statement is implied); any
-- choice of coarse-graining (C is a parameter, identified with nothing); and above all NO
-- derivation of randomness or of the Born rule - the orbit is deterministic throughout and what is
-- bounded is only how far its coarse marginals sit from a Markov chain's.
/-- info: 'MeasureTheory.condProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condProb_le_one

/-- info: 'MeasureTheory.condProb_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condProb_mul_eq

/-- info: 'MeasureTheory.coarseEvent_succ_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.coarseEvent_succ_eq

/-- info: 'MeasureTheory.measurableSet_coarseEvent' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measurableSet_coarseEvent

/-- info: 'MeasureTheory.historyEvent_subset_coarseEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.historyEvent_subset_coarseEvent

/-- info: 'MeasureTheory.abs_condProb_coarseEvent_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.abs_condProb_coarseEvent_sub_le

/-- info: 'MeasureTheory.measure_historyEvent_toReal_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measure_historyEvent_toReal_eq_prod

/-- info: 'MeasureTheory.abs_prod_sub_prod_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.abs_prod_sub_prod_le_sum

/-- info: 'MeasureTheory.abs_measure_historyEvent_sub_markov_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.abs_measure_historyEvent_sub_markov_le

/-- info: 'MeasureTheory.condProb_coarseEvent_succ_of_autonomous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.condProb_coarseEvent_succ_of_autonomous

/-- info: 'MeasureTheory.cex_condProb_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.cex_condProb_history

/-- info: 'MeasureTheory.cex_condProb_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.cex_condProb_present

/-- info: 'MeasureTheory.cex_not_microDecoupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.cex_not_microDecoupled


-- SYNDROME EXTRACTION AS A CIRCUIT (BACKLOG #94, split out of #62 (c1),
-- Mathlib/QuantumInfo/SyndromeExtraction.lean, 2026-10-04). The corpus measured a syndrome as a
-- PROJECTIVE MEASUREMENT on the data (Empirical/QM/QEC/SyndromeRecovery.lean); a circuit-level
-- fault-tolerance argument needs it as a CIRCUIT - ancilla block prepared in 0, a ladder of
-- transversal CNOTs, a measurement of the ancilla. The whole construction is one observation: a
-- CNOT ladder from data to ancilla is a PERMUTATION OF BASIS LABELS, (z,a) -> (z, a + H z), so it
-- is permMat of TransversalClifford.lean and the only arithmetic needed is H z + H z = 0.
-- extractMat_mul_ancInit_apply is the content: the circuit takes basis state z with a fresh ancilla
-- to (z, H z). ancProj_mul_extractMat_mul_ancInit then says READING THE ANCILLA IS PROJECTING THE
-- DATA onto the syndrome subspace - the circuit implements the projective measurement the corpus had
-- been assuming - and ancProj_mul_extractMat_mul_ancInit_of_ne says a syndrome the data does not
-- carry gets zero amplitude, so the measurement is exhaustive and not merely consistent.
-- extractMat_mul_ancInit_mul_synProj_zero and extractMat_conj_codeState: ON THE CODE EXTRACTION DOES
-- NOTHING, ancilla included, as an operator identity rather than a statement about one state; and
-- the all-zero outcome is then certain.
-- NOT claimed: any fault (this is the FAULT-FREE gadget; a fault in the ladder or the ancilla is
-- rows 95 and 96, and nothing here says the gadget is fault-TOLERANT); a verified ancilla (one
-- unverified block, so no bound on an ancilla fault spreading into the data); more than one check
-- map applied once (no rounds, no interleaving with gates); Z-type checks (the construction works
-- because the ladder permutes computational-basis labels, and the conjugate-basis half is not
-- derived); and no decoder - the syndrome is produced, never interpreted.
-- Foundational-triple except extractPerm_involutive, which needs propext alone.
/-- info: 'QuantumInfo.extractPerm_involutive' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractPerm_involutive

/-- info: 'QuantumInfo.extractMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractMat_mul_self

/-- info: 'QuantumInfo.extractMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractMat_mem_unitaryGroup

/-- info: 'QuantumInfo.ancInit_conjTranspose_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ancInit_conjTranspose_mul

/-- info: 'QuantumInfo.sum_ancProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sum_ancProj

/-- info: 'QuantumInfo.sum_synProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sum_synProj

/-- info: 'QuantumInfo.extractMat_mul_ancInit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractMat_mul_ancInit_apply

/-- info: 'QuantumInfo.ancProj_mul_extractMat_mul_ancInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ancProj_mul_extractMat_mul_ancInit

/-- info: 'QuantumInfo.ancProj_mul_extractMat_mul_ancInit_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ancProj_mul_extractMat_mul_ancInit_of_ne

/-- info: 'QuantumInfo.extractMat_mul_ancInit_mul_synProj_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractMat_mul_ancInit_mul_synProj_zero

/-- info: 'QuantumInfo.extractMat_conj_codeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.extractMat_conj_codeState

/-- info: 'QuantumInfo.ancProj_zero_mul_extractMat_conj_codeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.ancProj_zero_mul_extractMat_conj_codeState


-- THE ANCILLA LADDER: HOW ONE FAULT PROPAGATES, AND WHY THE CAT STATE IS NEEDED (BACKLOG #95, split
-- out of #62 (c2), Mathlib/QuantumInfo/AncillaLadder.lean, 2026-10-04). #94 built syndrome extraction
-- as a circuit and left one thing open in its header: the ancilla is ONE UNVERIFIED BLOCK, so nothing
-- bounded how far a single ancilla fault spreads into the data. This file prices that, in the
-- Heisenberg picture Clifford.lean already supports. cnotGate_conj_pauliOp propagates X from control
-- to target and Z from TARGET TO CONTROL, so for a data->ancilla ladder the dangerous fault is a Z on
-- the ancilla, and the two wirings differ exactly there. laddGate_conj_pauliOp telescopes the one-gate
-- theorem along the ladder (the CNOTs commute - same target, controls off it - so the ladder is an
-- involution and the induction closes), giving explicit X and Z label maps with NO PHASE.
-- THE SHARED-TARGET COST: zLadd_bitAt_target_apply, with dataSupport_zLadd_bitAt_target and
-- card_dataSupport_zLadd_bitAt_target - one Z fault on the shared ancilla comes out as a Z on the
-- ancilla AND ON EVERY CONTROL, so the data-side support is exactly the control list and ONE FAULT
-- BECOMES w DATA ERRORS. THE CAT-STATE COST: card_dataSupport_zLadd_singleton - with one control per
-- ancilla qubit the same fault reaches exactly ONE data qubit. That contrast is the whole
-- justification for the cat state. And the verification half: catVerify_eq_zero_iff (verification
-- passes exactly on the constant strings) with not_isCat_add_bitAt and
-- catVerify_ne_zero_of_single_flip - A SINGLE PREPARATION BIT-FLIP IS FLAGGED on any register of at
-- least two qubits.
-- NOT claimed: any fault MODEL - "one fault" means one Pauli at one place and the conclusions are
-- SUPPORT statements, with no fault counting, no probabilities and no threshold (rows 96, 97); any
-- cat-state PREPARATION circuit, superposition, or the X-basis measurement whose parity gives the
-- check value - this is the propagation and flagging content, not a gadget; anything about X faults
-- on the ancilla (they propagate away from the data) or faults elsewhere; that weight 4 is
-- UNCORRECTABLE by a distance-3 code (only that the distance-3 guarantee does not apply); more than
-- one ladder and one register; and no Steane instance - the theorems hold for an arbitrary control
-- list, but the embedding of seven data qubits plus an ancilla block into one register is not written
-- down. Foundational-triple except zLadd_apply_target (no axioms) and the five label-level results
-- that need only propext + Quot.sound.
/-- info: 'QuantumInfo.cnotFlip_comm_of_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cnotFlip_comm_of_target

/-- info: 'QuantumInfo.cnotGate_laddGate_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cnotGate_laddGate_comm

/-- info: 'QuantumInfo.laddGate_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.laddGate_involutive

/-- info: 'QuantumInfo.laddGate_conj_pauliOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.laddGate_conj_pauliOp

/-- info: 'QuantumInfo.zLadd_apply_target' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.zLadd_apply_target

/-- info: 'QuantumInfo.zLadd_bitAt_target_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.zLadd_bitAt_target_apply

/-- info: 'QuantumInfo.dataSupport_zLadd_bitAt_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.dataSupport_zLadd_bitAt_target

/-- info: 'QuantumInfo.card_dataSupport_zLadd_bitAt_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.card_dataSupport_zLadd_bitAt_target

/-- info: 'QuantumInfo.zLadd_singleton_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.zLadd_singleton_apply

/-- info: 'QuantumInfo.card_dataSupport_zLadd_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.card_dataSupport_zLadd_singleton

/-- info: 'QuantumInfo.catVerify_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.catVerify_eq_zero_iff

/-- info: 'QuantumInfo.not_isCat_add_bitAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.not_isCat_add_bitAt

/-- info: 'QuantumInfo.catVerify_ne_zero_of_single_flip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.catVerify_ne_zero_of_single_flip


-- THE EXTENDED RECTANGLE (BACKLOG #96, split out of #62 (c3),
-- Mathlib/QuantumInfo/ExtendedRectangle.lean, 2026-10-04). #62 (d1)'s correctedRun_eq_idealRun was
-- deliberately abstract in the step, and said so, precisely so that this row could hand it a step
-- built from a FAULTY RECOVERY. This file builds those steps - the Aharonov-Ben-Or /
-- Aliferis-Gottesman-Preskill rectangle argument stripped to its algebra, with a correctable set D as
-- a parameter and three properties each about a DIFFERENT PIECE: IsRecovery (the recovery removes
-- every D-deviation from a code state), DeviatesBy (the one-fault bound on one piece), PropagatesD
-- (transversality - the gadget carries a D-deviation to a D-deviation, which is what stops a leading
-- fault being amplified). Hypotheses about the pieces, conclusions about the composite: nothing
-- assumes the rectangle is correct in order to prove it.
-- isCorrectedStep_exRec_leading is THE ROW'S INSTANCE FOR A FAULTY RECOVERY: the leading recovery is
-- the faulty piece, and the rectangle is still a corrected step because transversality carries its
-- error through the gadget and the trailing recovery removes it. isCorrectedStep_exRec_gadget is the
-- same when the gadget is faulty, isCorrectedStep_exRec_of_good packages the two as "the single fault
-- is anywhere but the trailing recovery", and deviatesBy_exRec_trailing is the honest statement for
-- the remaining case: a trailing-recovery fault is NOT corrected here but handed on as a
-- D-deviation, in exactly the form the next rectangle's IsRecovery consumes - the overlapping-
-- rectangle convention stated rather than assumed away. correctedRun_eq_idealRun_of_good_exRec is the
-- payoff WITH NO RESTATEMENT: #62 (d1)'s theorem applied verbatim to a circuit of these rectangles.
-- NOT claimed: any fault COUNT or probability ("at most one fault" is a hypothesis, and the counting
-- and probabilistic join are row 97); any value for D (no code is fixed, and in particular the link
-- to row 95's weight-w propagation bound is NOT made - that needs a concrete D and recovery);
-- correction of a trailing-recovery fault, or that the chain of overlapping rectangles closes (row
-- 97); transversality (PropagatesD is assumed, not instantiated - the corpus has it concretely for the
-- Steane transversal CNOT but it is not plugged in); any instance at a concrete code; and no
-- positivity or trace condition on the maps. Foundational-triple throughout.
/-- info: 'QuantumInfo.IsRecovery.apply_of_isCodeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.IsRecovery.apply_of_isCodeState

/-- info: 'QuantumInfo.isCorrectedStep_rect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_rect

/-- info: 'QuantumInfo.isCorrectedStep_exRec_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_exRec_leading

/-- info: 'QuantumInfo.isCorrectedStep_exRec_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_exRec_gadget

/-- info: 'QuantumInfo.isCorrectedStep_exRec_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_exRec_of_good

/-- info: 'QuantumInfo.deviatesBy_exRec_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.deviatesBy_exRec_trailing

/-- info: 'QuantumInfo.correctedRun_eq_idealRun_of_good_exRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.correctedRun_eq_idealRun_of_good_exRec

/-- info: 'QuantumInfo.correctedRun_replicate_exRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.correctedRun_replicate_exRec


-- LEVEL REDUCTION AND THE PROBABILISTIC JOIN (BACKLOG #97, split out of #62 (d2) - the LAST of that
-- row's remainder; Mathlib/QuantumInfo/LevelReduction.lean, 2026-10-04). Three things were
-- deliberately left out of #94, #95 and #96 and this supplies them: the RECURSION (a level-k gadget
-- IS a level-(k-1) circuit), the FAULT COUNT, and the JOIN of the deterministic and probabilistic
-- halves into one statement. The deterministic half is #62 (d1)'s correctedRun_eq_idealRun and the
-- arithmetic half is #51's codeCapacityBound with concatMeasure_concatBad_le; neither is re-proved.
-- LEVEL REDUCTION: isCorrectedStep_correctedRun - a corrected circuit IS a corrected step one level
-- up, with the preserves half free from isCodeState_idealRun - and then
-- isCorrectedStep_of_isCorrectedAtLevel: CORRECTNESS AT EVERY LEVEL FOLLOWS FROM CORRECTNESS AT
-- LEVEL 0, by induction on the tower, with correctedRun_eq_idealRun_of_level as its circuit form.
-- THE JOIN: one_sub_le_measure_output_eq needs NO MEASURABILITY HYPOTHESES AT ALL - subadditivity
-- gives 1 <= mu s + mu s-complement for arbitrary sets - and
-- one_sub_le_measure_output_eq_concat is the row's statement: for N gadgets, each a level-k
-- concatenated block under independent noise of rate at most p, the output is EXACTLY the ideal one
-- with probability at least 1 - N (C(n,2) p)^(2^k) / C(n,2), i.e. the row's 1 - N (cp)^(2^k)/c.
-- tendsto_one_sub_codeCapacityBound sends the bound to 1 below threshold.
-- NOT claimed: the deterministic premise is a NAMED HYPOTHESIS and is not discharged here, so nothing
-- is a threshold theorem for the Steane code or for any concrete gadget set; "bad" is a pattern
-- predicate and the correspondence between a gadget's faults and a ConcatPat is not constructed;
-- noise is INDEPENDENT across gadgets and blocks, which is a modelling choice visible in
-- circuitMeasure, and correlated or adversarial noise is outside everything; N is given and NO GATE
-- COUNT OR OVERHEAD is bounded, so no polylogarithmic-overhead claim is made or implied; the constant
-- C(n,2) is not claimed sharp; and maps, not channels - no positivity or trace preservation anywhere.
-- Foundational-triple throughout.
/-- info: 'QuantumInfo.isCorrectedStep_correctedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_correctedRun

/-- info: 'QuantumInfo.isCorrectedStep_of_isCorrectedAtLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.isCorrectedStep_of_isCorrectedAtLevel

/-- info: 'QuantumInfo.correctedRun_eq_idealRun_of_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.correctedRun_eq_idealRun_of_level

/-- info: 'QuantumInfo.one_sub_le_measure_output_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.one_sub_le_measure_output_eq

/-- info: 'QuantumInfo.measurableSet_of_concatPat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.measurableSet_of_concatPat

/-- info: 'QuantumInfo.circuitMeasure_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.circuitMeasure_coord

/-- info: 'QuantumInfo.one_sub_le_measure_output_eq_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.one_sub_le_measure_output_eq_concat

/-- info: 'QuantumInfo.tendsto_one_sub_codeCapacityBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.tendsto_one_sub_codeCapacityBound

-- BACKLOG #109 (Cat-1 half): RELATIVE ENTROPY IS A LYAPUNOV FUNCTION FOR A MARKOV DYNAMICS
-- (Mathlib/InformationTheory/KlDivArrow.lean, 2026-10-04). Mathlib has the three data-processing
-- inequalities for klDiv; two consequences the arrow of time is usually stated as are absent, and
-- this adds them. klDiv_map_measurableEquiv: A REVERSIBLE RELABELLING CHANGES NO DIVERGENCE -- the
-- DPI applied along e and along e.symm gives equality, so an invertible step produces NOTHING and
-- whatever a coarse-grained second law produces comes from the coarse-graining or the kernel.
-- klDiv_comp_le_of_stationary: THE H-THEOREM -- if a Markov kernel fixes pi, the divergence of any
-- law from pi is non-increasing under one step; no symmetry, double stochasticity or detailed
-- balance is assumed, only stationarity of the reference. Measure.compIterate with
-- antitone_klDiv_compIterate and klDiv_compIterate_le: the divergence is monotone along the WHOLE
-- trajectory, which is what makes it an arrow rather than a one-step inequality.
-- NOT claimed: any constructed kernel, and stationarity is a HYPOTHESIS (the H-theorem is vacuous
-- for a kernel with no invariant measure); Shannon entropy -- klDiv q pi decreasing is equivalent to
-- entropy increasing only for a UNIFORM pi on a finite space, through
-- klDiv q uniform = log card - H q, an identity NOT proved here (it needs the Radon-Nikodym
-- derivative of one finite-type measure against another); and anything off absolute continuity,
-- where klDiv is infinite and both inequalities are true and empty. Foundational-triple.
/-- info: 'InformationTheory.klDiv_map_measurableEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.klDiv_map_measurableEquiv

/-- info: 'InformationTheory.klDiv_comp_le_of_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.klDiv_comp_le_of_stationary

/-- info: 'InformationTheory.antitone_klDiv_compIterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.antitone_klDiv_compIterate

/-- info: 'InformationTheory.klDiv_compIterate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.klDiv_compIterate_le

-- BACKLOG #110: SHANNON ENTROPY ON A FINITE TYPE, AND THE H-THEOREM IN ENTROPY FORM
-- (Mathlib/InformationTheory/FiniteEntropy.lean, 2026-10-05, the residue #109 named). Mathlib has
-- the Kullback-Leibler divergence but NO Shannon entropy of a measure - not for a finite type, not
-- anywhere - so #109's arrow could only be stated in divergence form. measureEntropy mu =
-- sum over x of negMulLog (mu.real {x}) supplies it. The work is the Radon-Nikodym computation:
-- withDensity_uniformOn_univ, the density of a measure against the uniform law is card * mu{x},
-- which holds for ANY measure on a finite type and not only a probability measure (and so do
-- absolutelyContinuous_uniformOn_univ and llr_uniformOn_univ_ae, hence the log-likelihood ratio is
-- log (card * mu{x}) almost everywhere). Then integral_llr_uniformOn_univ and klDiv_uniformOn_univ:
-- THE IDENTITY klDiv mu uniform = ofReal (log card - measureEntropy mu), clean because both
-- correction terms in klDiv's definition vanish for probability measures.
-- measureEntropy_le_log_card: THE MAXIMUM-ENTROPY THEOREM, Gibbs' inequality read through the
-- identity, and measureEntropy_uniformOn_univ shows the uniform law attains it so the bound is
-- tight. monotone_measureEntropy_compIterate: THE H-THEOREM IN ENTROPY FORM - under a Markov kernel
-- that FIXES THE UNIFORM LAW, Shannon entropy is non-decreasing along the whole trajectory; it is
-- #109's divergence form composed with the identity, with the maximum-entropy bound licensing the
-- removal of ENNReal.ofReal.
-- NOT claimed: anything for a non-uniform reference - entropy increases along a kernel fixing the
-- UNIFORM law, and for any other stationary law what is monotone is the divergence from that law
-- (#109) and not the entropy, the two statements coinciding only here; anything beyond a finite type
-- - differential entropy, countable types with infinite entropy, and the conditional and joint
-- entropies are untouched; and any convergence or rate - monotone is not strictly increasing and a
-- kernel can be the identity. Foundational-triple.
/-- info: 'InformationTheory.measureEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.measureEntropy

/-- info: 'InformationTheory.withDensity_uniformOn_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.withDensity_uniformOn_univ

/-- info: 'InformationTheory.llr_uniformOn_univ_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.llr_uniformOn_univ_ae

/-- info: 'InformationTheory.integral_llr_uniformOn_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.integral_llr_uniformOn_univ

/-- info: 'InformationTheory.klDiv_uniformOn_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.klDiv_uniformOn_univ

/-- info: 'InformationTheory.measureEntropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.measureEntropy_le_log_card

/-- info: 'InformationTheory.measureEntropy_uniformOn_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.measureEntropy_uniformOn_univ

/-- info: 'InformationTheory.monotone_measureEntropy_compIterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.monotone_measureEntropy_compIterate

-- BACKLOG #112: THE GROUP-COMMUTATOR CONTRACTION, SOLOVAY-KITAEV'S SHRINKING LEMMA
-- (Mathlib/Analysis/CStarAlgebra/GroupCommutator.lean, 2026-10-06, the first brick of #74's split).
-- Two gates near the identity have a group commutator QUADRATICALLY nearer it, and that quadratic
-- gain is the entire engine of the Solovay-Kitaev recursion. norm_mul_sub_mul_comm_le holds in ANY
-- normed ring: ||VW - WV|| <= 2||V-1||*||W-1||, the whole content being the identity
-- VW - WV = (V-1)(W-1) - (W-1)(V-1), so the commutator sees only how far the factors are from 1.
-- CStarRing.norm_groupCommutator_sub_one_le is the unitary form,
-- ||V W V* W* - 1|| <= 2||V-1||*||W-1||, where unitarity enters exactly twice: to write
-- V W V* W* - 1 = (VW - WV)(V* W*) (groupCommutator_sub_one_eq) and to drop the trailing unitary
-- from the norm. CStarRing.norm_groupCommutator_sub_one_le_two_mul_sq is the form the recursion
-- uses (both factors within delta gives 2 delta^2) and
-- CStarRing.norm_groupCommutator_sub_one_lt is THE CONTRACTION: for 0 < delta < 1/2 the commutator
-- is STRICTLY closer to 1 than its factors were. The error budget comes with it:
-- CStarRing.norm_mul_sub_mul_le (a product of unitaries is stable) and
-- CStarRing.norm_groupCommutator_sub_groupCommutator_le (the commutator of two eps-approximations
-- is a 4 eps-approximation of the commutator, the adjoints moving by norm_star).
-- NOT claimed: any gate count or algorithm - this is the shrinking lemma alone, with the recursion
-- (#115), the eps-net (#113), the commutator decomposition (#114) and the O(log^c(1/eps)) bound
-- (#116) all separate rows; optimality of the constants 2 and 4, which are what the telescoping
-- gives and which the Solovay-Kitaev exponent does not depend on; and anything at delta >= 1/2,
-- where the bound is weaker than its input and says nothing - which is why the algorithm needs a
-- base accuracy from the net before it can recurse. Foundational-triple.
/-- info: 'norm_mul_sub_mul_comm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mul_sub_mul_comm_le

/-- info: 'CStarRing.groupCommutator_sub_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.groupCommutator_sub_one_eq

/-- info: 'CStarRing.norm_groupCommutator_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.norm_groupCommutator_sub_one_le

/-- info: 'CStarRing.norm_groupCommutator_sub_one_le_two_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.norm_groupCommutator_sub_one_le_two_mul_sq

/-- info: 'CStarRing.norm_groupCommutator_sub_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.norm_groupCommutator_sub_one_lt

/-- info: 'CStarRing.norm_mul_sub_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.norm_mul_sub_mul_le

/-- info: 'CStarRing.norm_groupCommutator_sub_groupCommutator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CStarRing.norm_groupCommutator_sub_groupCommutator_le

-- BACKLOG #113: THE DETERMINANT-ONE UNITARIES ARE COMPACT, SO THE CLIFFORD+T WORDS CONTAIN A
-- FINITE EPS-NET
-- (Mathlib/QuantumInfo/CliffordTNet.lean, 2026-10-06, the second brick of #74's split).
-- Solovay-Kitaev's base case needs a FINITE set of words within eps_0 of every target. #81 gives
-- DENSITY, and density alone gives one word per target - a set with no finiteness and no bound.
-- COMPACTNESS is what upgrades it. IsCompact.exists_finite_net is the general statement in any
-- metric space: a compact set inside the closure of D is covered by finitely many eps-balls centred
-- in D (elim_finite_subcover over the cover by balls around points of D). isClosed_unitaryGroup:
-- the unitary group of any finite index type is closed, as the preimage of {1} under U |-> U U*;
-- Mathlib has IsCompact.matrix for entrywise-compact sets but nothing about the unitary group.
-- isCompact_su2Set: THE DETERMINANT-ONE 2x2 UNITARIES ARE COMPACT - closed (the unitary condition
-- and det = 1 are both closed) and inside the closed unit ball, because a unitary has operator norm
-- 1 in the C*-norm (CStarRing.norm_of_mem_unitary), with compactness of the ball from the space
-- being finite-dimensional hence proper. su2Set_subset_closure_cliffordT is #81's density as an
-- inclusion of sets, and exists_finite_cliffordT_net is THE BASE CASE: for every eps > 0 there are
-- FINITELY MANY genuine Clifford+T words such that every determinant-one unitary is within eps of
-- one of them.
-- NOT claimed: ANY CONSTRUCTION - the net comes from elim_finite_subcover, so nothing bounds its
-- cardinality or its words' lengths, and that is not a gap to be filled by the same argument but
-- exactly WHY Solovay-Kitaev needs a recursion on top of the net (#115), the net being the O(1)
-- base rather than the algorithm; any calibration of eps_0 against #112's contraction threshold
-- delta < 1/2, which is #115's business; the route the row recorded (the det-one unitaries as the
-- continuous image
-- of the unit sphere in R^4), which would need the SURJECTIVITY of the su2 parametrisation onto the
-- determinant-one unitaries and the corpus has no such statement - closed and bounded is shorter and
-- needs nothing new, so the sphere picture appears nowhere; and anything modulo phase, the net being
-- for det = 1 as in #81. Foundational-triple.
/-- info: 'IsCompact.exists_finite_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsCompact.exists_finite_net

/-- info: 'QuantumInfo.SU2.isClosed_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.isClosed_unitaryGroup

/-- info: 'QuantumInfo.SU2.isClosed_su2Set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.isClosed_su2Set

/-- info: 'QuantumInfo.SU2.su2Set_subset_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2Set_subset_closedBall

/-- info: 'QuantumInfo.SU2.isCompact_su2Set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.isCompact_su2Set

/-- info: 'QuantumInfo.SU2.su2Set_subset_closure_cliffordT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2Set_subset_closure_cliffordT

/-- info: 'QuantumInfo.SU2.exists_finite_cliffordT_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_finite_cliffordT_net

-- BACKLOG #114: EVERY DETERMINANT-ONE UNITARY IS A GROUP COMMUTATOR OF TWO SQUARE-ROOT-CLOSE
-- UNITARIES (Mathlib/QuantumInfo/CommutatorDecomposition.lean, 2026-10-06, the third brick of #74's
-- split). #112 proved a commutator of near-identity unitaries is QUADRATICALLY nearer the identity;
-- this is the converse the recursion needs, and exists_commutator_of_det_one is the target:
-- ||V-1||, ||W-1|| <= sqrt 2 * sqrt ||U-1|| with the commutator EXACT.
-- The pieces. norm_su2_sub_one: the distance to the identity is sqrt(2 - 2w), w the scalar part,
-- with NO eigenvalue computation - star M * M is a SCALAR multiple of 1 for M = su2 w x y z - 1
-- (star_su2_sub_one_mul_self), so the C*-identity ||M||^2 = ||M* M|| settles it. skComm_eq: THE
-- EXACT COMMUTATOR IDENTITY - with c = cos(phi/2), s = sin(phi/2), the commutator of the x-axis and
-- y-axis rotations by phi is the unit quaternion (1 - 2s^4, 2cs^3, -2cs^3, 2c^2s^2), by su2_mul
-- alone, so the matrix work is quaternion algebra; the scalar part is the angle relation, QUARTIC in
-- s hence quadratic in the angle. norm_skComm_sub_one = 2 sin^2(phi/2), norm_skV_sub_one_le is the
-- SQUARE-ROOT BOUND and exists_skComm_norm_eq realises every distance in [0,2] EXACTLY, at factor
-- angle 2 arcsin sqrt(eps/2). exists_su2_of_det_one: THE su2 PARAMETRISATION IS ONTO the
-- determinant-one unitaries - the surjectivity #113 found missing - because for det U = 1 the
-- inverse is the adjugate and for a unitary it is the adjoint, forcing U 1 1 = conj (U 0 0) and
-- U 1 0 = -conj (U 0 1), exactly the shape su2 has. su2_conj_pure: conjugating by a pi-rotation
-- REFLECTS the axis, v |-> 2(m.v)m - v; bisector_reflect: the bisector reflection swaps two vectors
-- of EQUAL LENGTH (no normalisation needed), so the axis moves anywhere except to its exact
-- opposite; and star_groupCommutator disposes of that case - the opposite axis belongs to the
-- ADJOINT of the commutator, which is the same pair in the other order, so NO PERPENDICULAR-VECTOR
-- CONSTRUCTION IS NEEDED ANYWHERE. norm_conj_sub_one and conj_groupCommutator are the transport.
-- NOT claimed: V and W are UNITARIES, NOT GATE WORDS - the commutator is exact and the factors are
-- rotations, nothing expresses them in a generating set, which is the division of labour the
-- algorithm needs (the net #113 supplies words, the recursion #115 approximates these factors by
-- them) and means this row alone implies NO GATE COUNT; determinant one and 2x2 only, a general
-- unitary needing a phase exactly as in #81, with nothing in higher dimension; optimality of the
-- constant sqrt 2, which comes from sin(phi/4) <= sin(phi/2) and is lossy by design; and anything
-- outside 0 <= phi <= pi for the standard pair, where the sign analysis (2c+1)(c-1) <= 0 holds -
-- exists_skComm_norm_eq only ever produces angles in that range.
-- Two of these need no choice, and are pinned as they ARE rather than padded to the triple:
-- conj_groupCommutator and star_groupCommutator are pure monoid-with-star algebra, so the first
-- needs [propext, Quot.sound] and the second needs [propext] alone.
/-- info: 'QuantumInfo.SU2.su2_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_star

/-- info: 'QuantumInfo.SU2.su2_star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_star_mul_self

/-- info: 'QuantumInfo.SU2.su2_add_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_add_star

/-- info: 'QuantumInfo.SU2.star_su2_sub_one_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.star_su2_sub_one_mul_self

/-- info: 'QuantumInfo.SU2.norm_su2_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_su2_sub_one

/-- info: 'QuantumInfo.SU2.norm_axisRot_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_axisRot_sub_one

/-- info: 'QuantumInfo.SU2.skComm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.skComm_eq

/-- info: 'QuantumInfo.SU2.skComm_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.skComm_unit

/-- info: 'QuantumInfo.SU2.norm_skComm_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_skComm_sub_one

/-- info: 'QuantumInfo.SU2.norm_skV_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_skV_sub_one

/-- info: 'QuantumInfo.SU2.norm_skW_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_skW_sub_one

/-- info: 'QuantumInfo.SU2.norm_skV_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_skV_sub_one_le

/-- info: 'QuantumInfo.SU2.norm_skW_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_skW_sub_one_le

/-- info: 'QuantumInfo.SU2.exists_skComm_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_skComm_norm_eq

/-- info: 'QuantumInfo.SU2.exists_su2_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_su2_of_det_one

/-- info: 'QuantumInfo.SU2.su2_conj_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_conj_pure

/-- info: 'QuantumInfo.SU2.su2_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.su2_mem_unitary

/-- info: 'QuantumInfo.SU2.axisRot_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.axisRot_mem_unitary

/-- info: 'QuantumInfo.SU2.bisector_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.bisector_reflect

/-- info: 'QuantumInfo.SU2.norm_conj_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.norm_conj_sub_one

/-- info: 'QuantumInfo.SU2.exists_commutator_of_det_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_commutator_of_det_one

/-- info: 'QuantumInfo.SU2.conj_groupCommutator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.conj_groupCommutator

/-- info: 'QuantumInfo.SU2.star_groupCommutator' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.star_groupCommutator

-- BACKLOG #115 (the ERROR half; the length half is NEW ROW 117): WHY THE SOLOVAY-KITAEV ERROR
-- CONTRACTS AT EXPONENT 3/2 (Mathlib/QuantumInfo/SolovayKitaevStep.lean, 2026-10-06, the fourth
-- brick of #74's split). #112 contracts a commutator, #114 produces one, #113 supplies the base
-- case; this is the step that makes them a recursion, and the whole content is WHY THE EXPONENT IS
-- 3/2 AND NOT 1. Replacing each factor of a commutator by a delta-approximation gives the naive
-- bound 4 delta (#112's norm_groupCommutator_sub_groupCommutator_le), which CONTRACTS NOTHING since
-- the input error was already delta. The gain is that the commutator is BILINEAR IN THE DEVIATIONS
-- FROM THE IDENTITY: norm_mul_sub_mul_le' exposes the pairing (AB - A'B' = (A-A')B + A'(B-B')), and
-- norm_groupCommutator_sub_le is THE SHARP ESTIMATE, ||[V,W] - [V',W']|| <= 4 a delta (1 + a) with a
-- bounding all four distances to the identity - smaller than #112's by a FACTOR a, and that factor
-- is the whole algorithm. norm_groupCommutator_sub_le_sqrt is the same at #114's factor size
-- a = sqrt 2 * sqrt eps, the sqrt(eps)*delta shape, which at delta = eps is eps^{3/2}.
-- skError_le_rpow is the error bookkeeping in CLOSED FORM: a sequence with
-- eps_{n+1} <= C eps_n^{3/2} satisfies C^2 eps_n <= (C^2 eps_0)^{(3/2)^n}, by induction through
-- Real.rpow - DOUBLY exponentially small in the number of levels, which is what makes the gate count
-- polylogarithmic, and the inequality #116 takes logarithms of.
-- NOT claimed: THE LENGTH HALF, which the row also asked for and which is NOT a formality - it needs
-- a notion of WORD LENGTH in the generating set, and the corpus has none (cliffordT is
-- Submonoid.closure {H, T}, matrices with no length function, and #113's net is a Finset of matrices
-- rather than of words); that is NEW ROW 117. A FINDING recorded with it: the quoted exponent
-- log 5 / log(3/2) ~ 3.97 is a COST-MODEL CHOICE, not a mathematical fact about this gate set. The
-- recursion uses the inverses of its two factors, and over the letters {H, T} a shortest word for
-- T inverse has length 7 (T inverse = T^7), so the per-level factor is 1+1+7+7+1 = 17 and the
-- exponent is log 17 / log(3/2) ~ 6.99; counting T inverse as one letter restores 5 and 3.97, and
-- BOTH GENERATE THE SAME SUBMONOID (T^7 is already in closure {H, T}), so the choice costs no
-- density and changes only the length function. #116 must say which cost model it means.
-- Also not claimed: any constructed approximant - skError_le_rpow is a statement about real
-- sequences, saying what the recursion's error does GIVEN the recurrence. Foundational-triple.
/-- info: 'CSD.SolovayKitaev.norm_mul_sub_mul_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.norm_mul_sub_mul_le'

/-- info: 'CSD.SolovayKitaev.norm_mul_sub_mul_comm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.norm_mul_sub_mul_comm_sub_le

/-- info: 'CSD.SolovayKitaev.norm_groupCommutator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.norm_groupCommutator_sub_le

/-- info: 'CSD.SolovayKitaev.norm_groupCommutator_sub_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.norm_groupCommutator_sub_le_sqrt

/-- info: 'CSD.SolovayKitaev.skError_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SolovayKitaev.skError_le_rpow

-- BACKLOG #117: CLIFFORD+T AS WORDS - THE COST MODEL AND THE 5^n HALF OF SOLOVAY-KITAEV
-- (Mathlib/QuantumInfo/CliffordTWords.lean, 2026-10-06, out of #115's split). #115 proved the error
-- half and found the length half was blocked on missing infrastructure: cliffordT is
-- Submonoid.closure {H, T}, a set of MATRICES with no notion of how many gates an element costs, and
-- #113's net is a Finset of matrices rather than of words. This file supplies the cost structure and
-- proves the length recursion.
-- THE COST MODEL IS STATED RATHER THAN INHERITED. The letters are H, T and T inverse - THREE, not
-- two - because #115 found the quoted exponent log 5 / log(3/2) ~ 3.97 to be a COST-MODEL CHOICE:
-- the recursion inverts its two factors, and over {H, T} alone a shortest word for T inverse is T^7,
-- so a level costs 1+1+7+7+1 = 17 and the exponent is log 17 / log(3/2) ~ 6.99.
-- mem_cliffordT_iff_exists_word shows the price of the three-letter model is NOTHING: the values of
-- words are EXACTLY cliffordT, because T^7 was already in closure {H, T}. So the inverse-closed model
-- costs no density and changes only the length function, and it is the one used here.
-- length_ctInvWord is the fact the 5 rests on: reversing a word and flipping each letter inverts it
-- (ctEval_ctInvWord) AT THE SAME LENGTH. exists_word_net restates #113's net as a Finset of WORDS
-- with a common length bound ell_0 - the base case the recursion starts from.
-- length_le_of_mem_skWords is the recursion: a word of the Solovay-Kitaev shape
-- v w v^-1 w^-1 a with all five parts at level n has length at most 5^n * ell_0. Five parts, each
-- inverse free, so the factor is exactly 5. With #115's C^2 eps_n <= (C^2 eps_0)^{(3/2)^n} this is
-- the pair #116 turns into a polylogarithmic gate count.
-- NOT claimed: skWords is the SHAPE of the recursion, not the algorithm - it is the set of words of
-- that form, and the theorem bounds their length; it does NOT say which element of skWords n
-- approximates a given U, which is #116's job. The length bound is an INEQUALITY, not a count:
-- nothing says 5^n * ell_0 is attained or that these are shortest words for their values. And
-- nothing about ell_0's SIZE - exists_word_net inherits #113's existence-only net, with no bound on
-- ell_0 in terms of eps_0. Foundational-triple throughout (length_ctInvWord needs propext alone).
/-- info: 'QuantumInfo.SU2.ctEval_mem_cliffordT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.ctEval_mem_cliffordT

/-- info: 'QuantumInfo.SU2.mem_cliffordT_iff_exists_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.mem_cliffordT_iff_exists_word

/-- info: 'QuantumInfo.SU2.ctGen_invLetter_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.ctGen_invLetter_mul

/-- info: 'QuantumInfo.SU2.length_ctInvWord' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.length_ctInvWord

/-- info: 'QuantumInfo.SU2.ctEval_ctInvWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.ctEval_ctInvWord

/-- info: 'QuantumInfo.SU2.exists_word_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_word_net

/-- info: 'QuantumInfo.SU2.length_le_of_mem_skWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.length_le_of_mem_skWords

/-- info: 'QuantumInfo.SU2.ctEval_mem_cliffordT_of_mem_skWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.ctEval_mem_cliffordT_of_mem_skWords

-- BACKLOG #116: THE SOLOVAY-KITAEV THEOREM WITH ITS GATE COUNT - LINK 12'S LAST ROW
-- (Mathlib/QuantumInfo/SolovayKitaevCount.lean, 2026-10-06, the last brick of #74's split; two
-- strengthening lemmas also landed in CommutatorDecomposition.lean).
-- #115 proved the error side and #117 the length side. Two things were left, and this row does both.
-- (1) ELIMINATING n. skLevel b eps = ceil(log R / log(3/2)) with R = log eps / log b;
-- skLevel_rpow_le says that many levels reach eps, five_pow_skLevel_le says five to that power is at
-- most 5 * R^c, and skExponent = log 5 / log(3/2) with three_lt_skExponent and skExponent_lt_four
-- placing c in the open interval (3, 4) - the literature's 3.97 - each by ONE application of
-- Real.log_lt_log to (3/2)^3 = 27/8 < 5 < 81/16 = (3/2)^4. No decimal expansion is claimed.
-- (2) THE PAIRING, which #117 explicitly declined: WHICH word approximates a given U.
-- exists_mem_skWords_norm_sub_le is the recursion - from a net at base accuracy e, the level-n words
-- of #117's shape reach skErr e n on EVERY determinant-one unitary. One level approximates U, takes
-- the residual Delta = U * star (ctEval u), writes it as a group commutator of two near-identity
-- determinant-one factors (#114), approximates those one level down, and reassembles. The
-- reassembled approximant is a WORD because star_ctEval identifies #117's ctInvWord with the
-- ADJOINT, so a group commutator of word values is the value of
-- v ++ w ++ ctInvWord v ++ ctInvWord w - exactly skWords' shape, so #117's length bound transfers
-- untouched.
-- TWO THINGS HAD TO BE BUILT FOR THAT STEP, NEITHER OF THEM BOOKKEEPING.
-- ctEval_mem_unitary: words are unitary (hGateM_mem_unitary and tGateM_mem_unitary, which the corpus
-- did not have), so right multiplication by one is an isometry and the residual is as close to 1 as
-- the approximation is good. And THE DETERMINANT: #114 needs its input to have determinant one, and
-- a Clifford+T word does not. It is FORCED. det_ctEval_pow_eight - the determinant of a word is an
-- eighth root of unity, because H^2 = 1 and T^8 = 1 and nothing else enters - together with
-- eq_one_of_pow_eight_eq_one: an eighth root of unity within 1/8 of 1 IS 1. That last needs no
-- root-of-unity theory, only (z-1) * sum_{k<8} z^k = z^8 - 1 = 0 and ||1 - z^k|| <= k ||1 - z|| on
-- the unit circle, which bounds the sum by 28/8 < 8.
-- #114 WAS STRENGTHENED IN PLACE to record that its commutator factors are determinant one, which
-- its construction already produced but its statement did not say: axisRot_det (a rotation has
-- determinant one) and the new det_conj_of_mem_unitary (conjugation by a unitary leaves the
-- determinant alone) discharge both branches, the generic one through the conjugating su2 and the
-- antipodal one directly. exists_commutator_of_det_one now carries V.det = 1 and W.det = 1; its
-- axiom pin is unchanged and sits with #114 above.
-- axisRot_det was NOT new - it already existed in EulerDecomposition.lean, and writing a second copy
-- surfaced the duplication. Both copies are gone and the lemma now lives once in SU2Rotation.lean
-- beside axisRot and su2_det, which both files already import; its pin is the pre-existing one.
-- THE THEOREM: exists_word_approx_polylog - for every determinant-one U and every small enough eps,
-- a Clifford+T WORD within eps of U of length at most K * log(1/eps)^c.
-- NOT claimed: K and eps_0 are EXISTENTIAL, by inheritance - #113's net comes from compactness with
-- no bound on its size, and the radius forcing the residual's determinant comes from continuity of
-- det; neither is quantitative, so no constant here is. The EXPONENT is. The exponent is also #117's
-- COST MODEL and not a fact about {H, T}: the letters are H, T and T inverse, so inverting a word is
-- free and a level costs five; over two letters a shortest T inverse is T^7, a level costs 17, and
-- the exponent is log 17 / log(3/2) ~ 6.99. #117's mem_cliffordT_iff_exists_word is what makes the
-- choice free. The literature's 3 + delta needs a different net argument and stays unclaimed. And
-- NOTHING IS COMPUTED: the word comes from a recursion over an existence statement, not an
-- algorithm, and skErr's constant 33 is a sufficient one rather than the best.
-- Foundational-triple throughout.
/-- info: 'QuantumInfo.SU2.three_lt_skExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.three_lt_skExponent

/-- info: 'QuantumInfo.SU2.skExponent_lt_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.skExponent_lt_four

/-- info: 'QuantumInfo.SU2.skLevel_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.skLevel_rpow_le

/-- info: 'QuantumInfo.SU2.five_pow_skLevel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.five_pow_skLevel_le

/-- info: 'QuantumInfo.SU2.ctEval_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.ctEval_mem_unitary

/-- info: 'QuantumInfo.SU2.star_ctEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.star_ctEval

/-- info: 'QuantumInfo.SU2.det_ctEval_pow_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.det_ctEval_pow_eight

/-- info: 'QuantumInfo.SU2.eq_one_of_pow_eight_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.eq_one_of_pow_eight_eq_one

/-- info: 'QuantumInfo.SU2.skErr_le_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.skErr_le_base

/-- info: 'QuantumInfo.SU2.det_conj_of_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.det_conj_of_mem_unitary

/-- info: 'QuantumInfo.SU2.exists_mem_skWords_norm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_mem_skWords_norm_sub_le

/-- info: 'QuantumInfo.SU2.exists_word_approx_polylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.SU2.exists_word_approx_polylog

-- BACKLOG #18 / R-019 BRICK (a): THE COARSE-GRAINED ARROW FOR AN ARBITRARY FINITE COARSE-GRAINING
-- (Mathlib/InformationTheory/CoarseGrainArrow.lean, 2026-10-06).
-- #109 proved an H-theorem for ONE coarse-graining - the record string on Sigma - and its proof used
-- nothing about records beyond measurability into a finite type. This is that proof with the
-- vocabulary abstracted: a probability measure pi on alpha, a finite beta, a measurable q from alpha
-- to beta, and a pi-preserving F on alpha. coarseLaw pi q = pi.map q; coarseStep and coarseKernel are
-- the INDUCED MACRO DYNAMICS (from a cell, condition pi on it, evolve by F, read the cell; null cells
-- get dirac, which keeps the kernel Markov on the nose). comp_coarseLaw: one macro step is the
-- pushforward along q composed with F. comp_coarseLaw_of_measurePreserving: INVARIANCE OF THE FINE
-- MEASURE MAKES THE COARSE LAW STATIONARY - the reference law the divergence is measured from is not
-- chosen, it is the coarse-grained law itself. antitone_klDiv_coarseLaw is the H-theorem, and
-- monotone_measureEntropy_coarseLaw the entropy form through #110 when the cells carry equal weight.
-- NOT claimed, and both caveats are in the header. THE ARROW IS FOR THE INDUCED MACRO CHAIN, not for
-- coarse-graining the fine orbit: the statement that
-- klDiv (coarseLaw (pi.map F^[n]) q) (coarseLaw pi q) decreases is FALSE as a theorem - for a
-- measure-preserving F that quantity is CONSTANT, by data processing in both directions - which is
-- why coarseStep is a definition here and not a hypothesis. And MONOTONE IS NOT CONVERGENT: nothing
-- says the divergence tends to 0, and nothing depends on the geometry of the cells. A rate is where
-- the cell size enters, and that is R-019's remaining half, now BACKLOG #118.
-- Foundational-triple.
/-- info: 'InformationTheory.isMarkovKernel_coarseKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.isMarkovKernel_coarseKernel

/-- info: 'InformationTheory.coarseStep_apply_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.coarseStep_apply_mul

/-- info: 'InformationTheory.comp_coarseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.comp_coarseLaw

/-- info: 'InformationTheory.comp_coarseLaw_of_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.comp_coarseLaw_of_measurePreserving

/-- info: 'InformationTheory.antitone_klDiv_coarseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.antitone_klDiv_coarseLaw

/-- info: 'InformationTheory.monotone_measureEntropy_coarseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InformationTheory.monotone_measureEntropy_coarseLaw

-- BACKLOG #92(a) BRICK (a1): THE WEYL OPERATOR'S SYMBOL CLASS
-- (Mathlib/Analysis/Fourier/WeylSymbolClass.lean, 2026-10-07).
-- #92's own measurement of its part (a) was that Op(a) as a continuous operator on Schwartz space is
-- NOT a gap in the proofs but A STATEMENT NEEDING A DIFFERENT SYMBOL CLASS: with weylOp's datum, a
-- family b from R to Schwartz(R) with no regularity in its first slot, weylOp b psi need not even be
-- continuous. WignerWeyl.lean works around that by ASSUMING what it needs - integrable_weylPair takes
-- joint continuity (hbc) and a bound integrable in the first slot (hM, hbM) as hypotheses. This file
-- fixes the class and discharges those hypotheses as theorems.
-- exists_bound_fst and exists_bound_snd: a Schwartz function on the plane decays like (1 + t^2)^-1 in
-- EACH SLOT SEPARATELY, uniformly in the other - two orders of SchwartzMap.decay (k = 2 and k = 0)
-- together with ||p||^2 >= p_i^2. weylOpK is the Weyl operator of a JOINTLY SCHWARTZ KERNEL, and
-- weylOpK_eq_weylOp is the bridge: it agrees with weylOp of any slice family, so everything already
-- proved about weylOp transfers whenever a slice family is available. continuous_weylKernel and
-- exists_integrable_bound are WignerWeyl.lean's three assumed hypotheses, now theorems on this class.
-- integrable_weylOpK_integrand and continuous_weylOpK are THE DEFECT #92 RECORDED, FIXED: on the
-- Schwartz kernel class the Weyl operator's output IS continuous, by dominated continuity
-- (continuousAt_of_dominated) against 4C(1 + (y - x_0)^2)^-1, the majorant the second-slot decay
-- supplies uniformly for parameters within 1 of the point (norm_weylKernel_le, whose arithmetic is
-- the identity (d - a)^2 <= 2d^2 + 2a^2 at d = x - x_0 and a = x - y).
-- NOT claimed, and both caveats are in the header. THIS IS THE SYMBOL CLASS, NOT THE CALCULUS:
-- Op(a) as a continuous map of Schwartz space into itself is NOT proved - continuity of the output
-- function is the FIRST of the Schwartz seminorm estimates, not the last - and the remaining
-- obstruction is the one #92 measured and is unchanged, namely differentiation under the integral sign
-- TO ALL ORDERS WITH BOUNDS, which the pin has in no form for integrals over R (the corpus's
-- ContDiffParametricIntervalIntegral.lean, from #60, is INTERVAL integrals on a compact interval,
-- where the bounds come free from continuity); that is BACKLOG #120. And NO SLICING:
-- weylOpK_eq_weylOp takes the slice family as a HYPOTHESIS, because that a Schwartz function on the
-- plane slices into a Schwartz-valued family is exactly the two-variable Schwartz API #92 names as
-- absent, which is BACKLOG #121 - and the reason the properties above are proved for weylOpK directly
-- rather than inherited through weylOp.
-- Foundational-triple.
/-- info: 'WignerFunction.exists_bound_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_fst

/-- info: 'WignerFunction.exists_bound_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_snd

/-- info: 'WignerFunction.weylOpK_eq_weylOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_eq_weylOp

/-- info: 'WignerFunction.continuous_weylKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.continuous_weylKernel

/-- info: 'WignerFunction.exists_integrable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_integrable_bound

/-- info: 'WignerFunction.norm_weylKernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_weylKernel_le

/-- info: 'WignerFunction.integrable_weylOpK_integrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_weylOpK_integrand

/-- info: 'WignerFunction.continuous_weylOpK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.continuous_weylOpK

-- BACKLOG #120: DIFFERENTIATION UNDER THE INTEGRAL SIGN, TO ALL ORDERS
-- (Mathlib/Analysis/Calculus/ContDiffParametricIntegral.lean, 2026-10-07, out of #92's split).
-- Mathlib differentiates a parametric integral ONCE
-- (hasDerivAt_integral_of_dominated_loc_of_deriv_le and its fderiv siblings). The corpus
-- differentiates one to ALL orders but only for an INTERVAL integral on a compact interval
-- (ContDiffParametricIntervalIntegral.lean, #60), where the bounds come free from continuity on a
-- compact set. For an integral over a general measure space there is no such shortcut and the bounds
-- have to be hypotheses; this supplies that.
-- partialDeriv F k is the k-th derivative of F in its PARAMETER, defined by recursion rather than
-- through iteratedDeriv so the induction shifts the order with no API friction;
-- partialDeriv_eq_iteratedDeriv is the bridge so a user can discharge bounds with either vocabulary,
-- and partialDeriv_succ_left is the shift the induction runs on. contDiff_partialDeriv_one is the
-- step that passes parameter-smoothness to the parameter derivative, through contDiff_succ_iff_deriv.
-- contDiffOn_integral_of_bound is THE THEOREM: if each x |-> F x a is C^n in the parameter, each
-- partialDeriv F k x is measurable in a, and the k-th one is bounded on an open U by an integrable
-- bound k UNIFORMLY IN THE PARAMETER, then the integral is C^n on U. contDiff_integral_of_bound is
-- the global corollary (U = univ) and contDiffOn_integral_of_bound_all is smoothness at every order.
-- THE HYPOTHESES ARE THE STATEMENT, and the row that opened this warned that a version nobody can
-- discharge would be worse than none - so they are one integrable function per order, valid for every
-- parameter in U, rather than a Lipschitz modulus or something per-point. The U is there because that
-- is how such bounds actually arise: for a kernel like K ((x + y)/2, x - y) the majorant depends on
-- where the parameter sits, so a bound uniform on a ball is available and a globally uniform one is
-- not. ContDiffOn on an open set is exactly what that buys.
-- AND THE INTERFACE IS SHOWN DISCHARGEABLE rather than asserted to be:
-- contDiff_integral_schwartz_sub_mul proves CONVOLUTION WITH A SCHWARTZ FUNCTION IS SMOOTH TO EVERY
-- ORDER for any integrable weight, meeting all four hypotheses - partialDeriv_sub_mul computes the
-- parameter derivatives as iteratedDeriv k f (x - t) * g t through deriv_comp_sub_const, and
-- exists_bound_iteratedDeriv supplies the uniform bound from decay 0 k, which is exactly the
-- "uniformly in the parameter" the bound family asks for.
-- NOT claimed: NO FORMULA FOR THE DERIVATIVES - the proof produces
-- deriv (integral) = integral of partialDeriv F 1 on U as a by-product of each step, but the
-- statement records only the smoothness; exposing the identity at every order would want a statement
-- about iteratedDeriv OF the integral, which nothing needs. And the PARAMETER IS ONE-DIMENSIONAL: the
-- integration variable ranges over an arbitrary measure space, but the parameter is in R, which is
-- what lets the proof use deriv throughout and keeps the bounds scalar; the fderiv version over a
-- finite-dimensional parameter is the same induction with ContinuousLinearMap plumbing and is not
-- done here. #92(a3) is the consumer this was built for and remains open.
-- Foundational-triple.
/-- info: 'partialDeriv_eq_iteratedDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partialDeriv_eq_iteratedDeriv

/-- info: 'partialDeriv_succ_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partialDeriv_succ_left

/-- info: 'contDiff_partialDeriv_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_partialDeriv_one

/-- info: 'contDiffOn_integral_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_integral_of_bound

/-- info: 'contDiff_integral_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_integral_of_bound

/-- info: 'contDiffOn_integral_of_bound_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_integral_of_bound_all

/-- info: 'partialDeriv_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partialDeriv_sub_mul

/-- info: 'exists_bound_iteratedDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_bound_iteratedDeriv

/-- info: 'contDiff_integral_schwartz_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_integral_schwartz_sub_mul

-- BACKLOG #121(i): SLICING A SCHWARTZ FUNCTION ON A PRODUCT, AND THE PAYOFF
-- (Mathlib/Analysis/Fourier/SchwartzSlice.lean, 2026-10-07, out of #92's split).
-- A Schwartz function on a product restricts to a Schwartz function on each slice. Mathlib has the
-- machinery - SchwartzMap.compCLM composes on the right with any map of temperate growth that does not
-- shrink the norm too much - but not the instance, because the slice map w |-> (e, w) is AFFINE rather
-- than linear and fun_prop has no Prod.mk rule for HasTemperateGrowth.
-- Function.hasTemperateGrowth_prodMk_left supplies it through HasTemperateGrowth.of_fderiv: the slice
-- map's derivative is the CONSTANT inr (hasFDerivAt_prodMk_right) and its value grows linearly, since
-- the product norm is a max. exists_norm_le_prodMk_left is compCLM's other hypothesis, that the slice
-- map does not shrink the norm. SchwartzMap.sliceCLM is then the slice AS A CONTINUOUS LINEAR MAP IN
-- THE KERNEL and SchwartzMap.slice_apply its defining equation, slice K e w = K (e, w).
-- THE PAYOFF IS integral_conj_mul_weylOpK: THE WEYL EXPECTATION FORMULA ON THE SCHWARTZ KERNEL CLASS
-- WITH NO HYPOTHESES AT ALL - the expectation of the Weyl operator in a state is the phase-space
-- average of the symbol against the state's Wigner function. WignerWeyl.lean proves that for a slice
-- family under three assumptions its datum could not supply (joint continuity, and a bound integrable
-- in the first slot); #92(a1) discharged the latter two for a jointly Schwartz kernel
-- (continuous_weylKernel, exists_integrable_bound) and the slice supplies the family itself, so on
-- this class nothing is left to assume. weylOpK_eq_weylOp_slice is the bridge made unconditional.
-- NOT claimed: CONTINUITY IN THE SLICE PARAMETER, which is the other half of #121(i) and is now
-- BACKLOG #123. What is continuous here is slicing IN THE KERNEL (sliceCLM is a continuous linear map
-- for each fixed e), which is what transfers theorems; that e |-> slice K e is continuous into
-- Schwartz space for the SCHWARTZ TOPOLOGY is a different statement, needs one more order of decay and
-- a mean-value estimate in the sliced variable, and Mathlib has no curry to get it from. Nothing in
-- the corpus needs it. Also NOT claimed: the partial Fourier transform, which is #121(ii) and the half
-- a pseudodifferential calculus would need.
-- Foundational-triple.
/-- info: 'Function.hasTemperateGrowth_prodMk_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Function.hasTemperateGrowth_prodMk_left

/-- info: 'exists_norm_le_prodMk_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_le_prodMk_left

/-- info: 'SchwartzMap.slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.slice_apply

/-- info: 'WignerFunction.weylOpK_eq_weylOp_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_eq_weylOp_slice

/-- info: 'WignerFunction.integral_conj_mul_weylOpK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integral_conj_mul_weylOpK

-- BACKLOG #121(ii), PARTIALLY: THE SYMBOL OF A SCHWARTZ KERNEL AT EACH MIDPOINT
-- (Mathlib/Analysis/Fourier/PartialFourier.lean, 2026-10-07).
-- #121(ii) asked for the PARTIAL FOURIER TRANSFORM on Schwartz functions of the plane: the transform
-- in the second slot alone, landing in Schwartz functions ON THE PLANE. What is delivered is the
-- SLICE-WISE transform, which is the object weylSymbol actually is.
-- SchwartzMap.sliceFourierCLM composes #121(i)'s sliceCLM with Mathlib's fourierTransformCLM, so the
-- symbol at a fixed midpoint IS a Schwartz function of the frequency, continuously and linearly in the
-- kernel; weylSymbol_slice_apply identifies it with the corpus's weylSymbol of the slice family, and
-- integrable_weylSymbol_slice with exists_bound_weylSymbol_slice are the two consequences a consumer
-- wants, both free once the symbol slice is Schwartz.
-- NOT claimed, and this is the point of the file: THIS DOES NOT CLOSE #121(ii), AND THE JOINT
-- STATEMENT IS NOT A COROLLARY OF IT. That (u, xi) |-> weylSymbol (slice K) u xi is Schwartz ON THE
-- PLANE needs decay and smoothness JOINTLY, and slice-wise Schwartzness gives neither, since every
-- constant here may depend on the midpoint u.
-- AND THE REASON IS STRUCTURAL, WHICH IS NEW INFORMATION THE ROW DID NOT HAVE. The natural proof of
-- the joint statement factors through the CURRY of Schwartz spaces on a product, after which a partial
-- transform is just fourierTransformCLM applied in the inner factor - and Mathlib has no such curry,
-- whose first half is #123. The alternative is bespoke: differentiate under the integral in BOTH
-- variables to all orders, which needs the finite-dimensional-parameter version of #120 (that row's
-- own scope note records its one-dimensional restriction), plus the seminorm estimates assembled
-- against K's decay. Either way it is not a one-sitting build, which the row's L did not reflect; the
-- joint form is re-priced and kept open as #121(ii).
-- Foundational-triple.
/-- info: 'SchwartzMap.sliceFourierCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.sliceFourierCLM_apply

/-- info: 'WignerFunction.weylSymbol_slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylSymbol_slice_apply

/-- info: 'WignerFunction.integrable_weylSymbol_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_weylSymbol_slice

/-- info: 'WignerFunction.exists_bound_weylSymbol_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_weylSymbol_slice

-- BACKLOG #124: DIFFERENTIATION UNDER THE INTEGRAL SIGN OVER A FINITE-DIMENSIONAL PARAMETER
-- (Mathlib/Analysis/Calculus/ContDiffParametricIntegralFDeriv.lean, 2026-10-07, out of #121(ii)).
-- #120 did the one-dimensional-parameter case deliberately, its scope note recording that the fderiv
-- version "is the same induction with ContinuousLinearMap plumbing and is not done here". #121(ii) is
-- what wants the general case, since the joint Schwartz claim needs differentiating in two variables
-- at once, so here it is for a parameter in any finite-dimensional normed space.
-- THE INTERFACE IS DIRECTIONAL, AND THAT IS THE WHOLE DESIGN - AND IT REFUTES THE ROW'S OWN FORECAST.
-- #124's row warned that the hypothesis-design question #120 flagged "returns in harder form: a
-- per-order, locally-uniform bound on a MULTILINEAR norm". It does not have to. Bounding
-- iteratedFDeriv means bounding a multilinear map, which drags currying equivalences through every
-- step; bounding ITERATED DIRECTIONAL derivatives keeps every hypothesis valued in E, and the
-- recursion is then literally list-append - dirDeriv F hs differentiates along the list hs with
-- dirDeriv_append_singleton the shift, and dirWeight carries the product of the directions' norms so
-- that appending one direction multiplies the weight by its norm and raises the order by one
-- (dirWeight_append_singleton), leaving the inner call with fun k a => ||h|| * bound (k+1) a, still
-- integrable. No multilinear norm appears anywhere in the statement.
-- contDiffOn_integral_of_dirBound is the theorem; contDiff_integral_of_dirBound is the global case
-- (U = univ) and contDiffOn_integral_of_dirBound_all smoothness at every order.
-- TWO HYPOTHESES THE ROW DID NOT ANTICIPATE, both honest and both in the header. (1) ONE HYPOTHESIS IS
-- UNAVOIDABLY OPERATOR-VALUED: Mathlib's hasFDerivAt_integral_of_dominated_of_fderiv_le takes the
-- derivative as a map into H -> L E, so strong measurability of a |-> fderiv (F . a) x is required and
-- cannot be reduced to directional data; it appears as hmeasD and is closed under the recursion for
-- the same list-append reason. (2) THE BOUND FAMILY MUST BE NONNEGATIVE (hb0), which #120 needed not,
-- because its one-dimensional engine takes a bound on ||F' x a|| directly while here the directional
-- bounds must be turned into an OPERATOR-norm bound through opNorm_le_bound - false for a negative
-- constant when H is trivial. One line to discharge for any bound family anyone builds.
-- FiniteDimensional H is used exactly once, in contDiffOn_clm_apply, to assemble the directional
-- components back into the operator-valued derivative; that is the same place #60 needed it.
-- NOT claimed: no formula for the derivatives, as in #120 - each step produces
-- fderiv (integral) = integral of fderiv on U as a by-product and only the smoothness is recorded.
-- #121(ii) is the consumer this was built for and remains open; #123 is its alternative route.
-- Foundational-triple.
/-- info: 'dirDeriv_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirDeriv_append_singleton

/-- info: 'dirWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirWeight_nonneg

/-- info: 'dirWeight_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirWeight_append_singleton

/-- info: 'contDiffOn_integral_of_dirBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_integral_of_dirBound

/-- info: 'contDiff_integral_of_dirBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_integral_of_dirBound

/-- info: 'contDiffOn_integral_of_dirBound_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_integral_of_dirBound_all

-- BACKLOG #124, ADDENDUM 2026-10-07: THE MULTILINEAR INTERFACE AS A COROLLARY OF THE DIRECTIONAL ONE
-- (same module). Added after #121(ii) tried to consume #124 and COULD NOT: SchwartzMap.decay gives
-- bounds on iteratedFDeriv, so without a bridge the directional hypotheses were not dischargeable
-- from Schwartz data and the file was unusable by the row it was built for. #124 was under-delivered
-- as landed, and trying to consume it is what showed that.
-- norm_dirDeriv_le: an iterated DIRECTIONAL derivative is bounded by the iterated TOTAL derivative
-- times the product of the directions' norms. The induction peels the INNERMOST direction through
-- dirDeriv_append_singleton - peeling the head does not work, because the head is the outermost
-- derivative and the result is then not of the form dirDeriv G hs for any G - turns the evaluation
-- into a left composition with ContinuousLinearMap.apply
-- (ContinuousLinearMap.iteratedFDeriv_comp_left, with norm_applyCLM_le bounding its operator norm by
-- the direction's) and puts the extra order back with norm_iteratedFDeriv_fderiv. Smoothness is
-- assumed outright rather than tracked order by order, which is what removes all the bookkeeping and
-- is what a Schwartz integrand supplies anyway.
-- contDiffOn_integral_of_iteratedFDeriv_bound is then the form a user with SchwartzMap.decay data
-- actually has, and it makes the module header's claim honest: the directional form is easier to meet
-- AND strictly more general, since the multilinear form follows from it rather than competing with it.
-- NOT claimed: #121(ii) is still open. This supplies what it needs from #124 and nothing more - the
-- joint Schwartz conclusion also wants the Fourier seminorm identities and a Leibniz expansion across
-- the exponential, which is where that row now sits.
-- Foundational-triple.
/-- info: 'norm_applyCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_applyCLM_le

/-- info: 'norm_dirDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_dirDeriv_le

/-- info: 'contDiffOn_integral_of_iteratedFDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_integral_of_iteratedFDeriv_bound

-- BACKLOG #126, FIRST SLICE: THE DERIVATIVE FORMULA OVER A FINITE-DIMENSIONAL PARAMETER
-- (Mathlib/Analysis/Calculus/ContDiffParametricIntegralFDeriv.lean, 2026-10-08, out of #124 + #125).
-- #125 exported the identity #120 proves and discards, for a ONE-DIMENSIONAL parameter, and its own
-- scope note recorded what stayed missing: the same identity over a finite-dimensional parameter.
-- #126 is the consumer - a composite Weyl kernel is a parametric integral over a TWO-dimensional
-- parameter, and with no formula for its derivatives there is nothing to move a polynomial weight
-- onto, which is exactly the wall #122's decay half hit before #125.
-- hasFDerivAt_integral_of_bound is the first-order identity, exported from inside #124's induction
-- with the WEAKEST hypotheses that give it (differentiability of each slice, not smoothness), and
-- fderiv_integral_apply_of_bound is its directional form, in which no operator-valued integral
-- survives in the statement. integrable_of_bound and integrable_fderiv_of_bound are the
-- integrability the two statements are false without.
-- norm_iteratedFDeriv_integral_le is WHAT A CONSUMER ACTUALLY NEEDS, and it is a BOUND rather than
-- an identity: with #124's own hypotheses, the n-th iterated derivative of the integral obeys the
-- bound family, ‖iteratedFDeriv n (integral of F) x‖ <= integral of bound n. STATING the identity at
-- order n would need the iterated derivative of the integral AS A MULTILINEAR MAP, which is the
-- plumbing this file exists to avoid; the bound is scalar and is the shape every Schwartz seminorm
-- estimate asks for.
-- The induction peels the LAST direction (iteratedFDeriv_apply_succ_last, which puts Mathlib's
-- iteratedFDeriv_succ_apply_right back into E by composing with evaluation), replaces the derivative
-- of the integral by the integral of the directional derivative - legitimate under the remaining
-- derivatives because the identity holds on all of the OPEN U, which is what
-- Filter.EventuallyEq.iteratedFDeriv_eq is for (Mathlib has the iteratedFDerivWithin version only) -
-- and calls itself on dirDeriv F [h] with the bound family shifted exactly as #124 shifts it.
-- AND THE CHANGE THAT MATTERS MOST GOES THE OTHER WAY: #124's induction now CALLS the exported
-- first-order identity instead of rebuilding it inline, so that proof exists once.
-- NOT claimed. NO IDENTITY AT ORDER n, only the bound, for the reason above - a consumer wanting the
-- multilinear identity would have to state it, and nothing needs it. The bound family must still be
-- LOCALLY UNIFORM in the parameter (that is what U is for), and #124's two scope notes about the
-- operator-valued measurability hypothesis and the nonnegativity of the bound family stand unchanged.
-- Foundational-triple.
/-- info: 'integrable_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_of_bound

/-- info: 'hasFDerivAt_integral_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasFDerivAt_integral_of_bound

/-- info: 'integrable_fderiv_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_fderiv_of_bound

/-- info: 'fderiv_integral_apply_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fderiv_integral_apply_of_bound

/-- info: 'Filter.EventuallyEq.iteratedFDeriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Filter.EventuallyEq.iteratedFDeriv_eq

/-- info: 'iteratedFDeriv_apply_succ_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedFDeriv_apply_succ_last

/-- info: 'norm_iteratedFDeriv_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_iteratedFDeriv_integral_le

-- BACKLOG #126(ii): INTEGRATING OUT ONE VARIABLE PRESERVES SCHWARTZ SPACE
-- (Mathlib/Analysis/Fourier/SchwartzPartialIntegral.lean, 2026-10-08).
-- SchwartzMap.integralLastCLM is 𝓢(E × ℝ, F) →L[ℂ] 𝓢(E, F), G ↦ fun p => integral over t of G (p, t).
-- Mathlib has SchwartzMap.integralCLM, which integrates over the WHOLE domain into a scalar, and
-- nothing that integrates out ONE variable: this is the two-variable gap #121 names, in its integral
-- form, and it is what #126 needs - a composite integral kernel is exactly one variable integrated
-- out of a product of two kernels.
-- SMOOTHNESS is #124 and DECAY is #126's gate (norm_iteratedFDeriv_integral_le). What this file
-- supplies is the BRIDGE FROM SCHWARTZ DATA TO #124's DIRECTIONAL HYPOTHESES, in three pieces.
-- (1) iteratedFDeriv_comp_inl is the iterated chain rule through the inclusion y -> (y, t), with
-- norm_iteratedFDeriv_comp_inl_le: a derivative in the first factor is no bigger than the full
-- derivative, because the inclusion has norm one.
-- (2) THE MEASURABILITY HYPOTHESES, WHICH NOTHING HAD DISCHARGED BEFORE. #124's scope note flags one
-- of its hypotheses as unavoidably operator-valued (Mathlib's first-derivative theorem forces it).
-- contDiff_prodDirDeriv + dirDeriv_eq_prodDirDeriv are how both get discharged: folding the
-- inclusion into the recursion makes each directional derivative a SLICE OF SOMETHING JOINTLY
-- SMOOTH, hence continuous in the integration variable, hence measurable - and
-- aestronglyMeasurable_fderiv_dirDeriv_prodMk is the operator-valued one, which is continuity of a
-- CLM-valued map on ℝ (the domain is second countable, so only metrizability of the target is
-- needed, and a normed space has it).
-- (3) one_add_norm_pow_mul_norm_iteratedFDeriv_le is THE WEIGHT TRANSFER: two orders of G's decay
-- give (1 + ‖p‖)^N * ‖d^k G (p,t)‖ <= 2^(N+2) * S * (1 + t^2)^-1 with S a SINGLE Finset.sup of G's
-- seminorms - the same two-order combination #122's decay half runs on, with the slots swapped, and
-- in the shape SchwartzMap.mkCLM consumes. norm_dirDeriv_slice_le packages it as #124's bound family,
-- contDiff_integral_slice is the smoothness (uniform in the parameter, so no ball is needed), and
-- norm_pow_mul_norm_iteratedFDeriv_integral_le is the seminorm estimate, where the weight rides a
-- bound family CONSTANT ON A UNIT BALL of parameters (which is the shape the gate consumes) and
-- the integral of (1 + t^2)^-1 = pi finishes it.
-- NOT claimed. ONE VARIABLE, AND IT IS THE LAST ONE: 𝓢(E × F, ℂ) → 𝓢(E, ℂ) for a general second
-- factor is the same proof with (1 + t^2)^-1 replaced by an integrable profile on F, and only F = ℝ
-- is proved, because that is what a kernel composition integrates over. THE CONSTANTS ARE NOT SHARP.
-- AND NOTHING HERE IS A FUBINI STATEMENT: that an iterated integral equals a double integral is a
-- separate step, which the consumer does with Mathlib's integral_integral_swap.
-- Foundational-triple.
/-- info: 'iteratedFDeriv_comp_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedFDeriv_comp_inl

/-- info: 'norm_iteratedFDeriv_comp_inl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_iteratedFDeriv_comp_inl_le

/-- info: 'contDiff_prodDirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_prodDirDeriv

/-- info: 'dirDeriv_eq_prodDirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirDeriv_eq_prodDirDeriv

/-- info: 'aestronglyMeasurable_fderiv_dirDeriv_prodMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aestronglyMeasurable_fderiv_dirDeriv_prodMk

/-- info: 'one_add_norm_pow_mul_norm_iteratedFDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_add_norm_pow_mul_norm_iteratedFDeriv_le

/-- info: 'norm_dirDeriv_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_dirDeriv_slice_le

/-- info: 'contDiff_integral_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_integral_slice

/-- info: 'norm_pow_mul_norm_iteratedFDeriv_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_pow_mul_norm_iteratedFDeriv_integral_le

/-- info: 'SchwartzMap.integralLastCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.integralLastCLM

-- BACKLOG #123: SLICING IS LIPSCHITZ IN THE SLICE PARAMETER
-- (Mathlib/Analysis/Fourier/SchwartzSliceContinuous.lean, 2026-10-09, out of #121(i)).
-- continuous_slice: the slice family e -> slice K e is continuous into the Schwartz space of the
-- second factor, for the SCHWARTZ TOPOLOGY. #121(i) proved slicing continuous IN THE KERNEL
-- (sliceCLM is a continuous linear map for each fixed e), which is what transfers theorems; this is
-- the other direction, and the row was right that it is a genuinely different statement.
-- THE ROW'S OWN ROUTE WORKED, AND BOTH PIECES IT NAMED WERE NEEDED.
-- (1) iteratedFDeriv_comp_inr: the derivatives of a slice are the kernel's derivatives precomposed
-- with the inclusion w -> (e, w). This is the MIRROR of #126(ii)'s iteratedFDeriv_comp_inl, which is
-- why it was cheap - the proof is the same affine-translation-plus-linear-map factorisation.
-- (2) norm_fderiv_iteratedFDeriv_comp_inl_le: the kernel's n-th derivative is differentiable in the
-- parameter with derivative bounded by its (n+1)-st - K's decay AT ONE ORDER HIGHER, exactly as the
-- row predicted, through Mathlib's norm_fderiv_iteratedFDeriv.
-- lipschitz_seminorm_slice is the estimate: each Schwartz seminorm of the slice difference is at most
-- the norm of (e - e0) times ONE seminorm of K, the same one at one order higher.
-- THE ROW SAID "LOCALLY LIPSCHITZ"; IT IS GLOBALLY LIPSCHITZ. The derivative bound is a seminorm of
-- K, which does not depend on the base point, so no localisation is needed.
-- A NOTE ON THE PROOF: the weight is handled by a CASE SPLIT on whether it vanishes, not by weighting
-- the function before the mean value step. Weighting first is the mathematically natural move (the
-- derivative bound is then uniform in both variables) but it puts a scalar smul on a space of
-- continuous multilinear maps, where the NormSMulClass instance needed for the norm computation is
-- absent at this pin; the case split costs two lines and needs no instances.
-- NOT claimed. NOTHING IS GATED ON THIS - the row records it because #121(i) names it and because a
-- symbol-valued calculus would want it, and #121(ii) goes by #124 alone; it is here because it was
-- UNBLOCKED, not because anything waits on it. NOT A CURRY: as #123 was corrected on 2026-10-07, the
-- type 𝓢(E, 𝓢(F, G)) does not typecheck (SchwartzMap needs a normed target, Schwartz space is
-- Frechet), so this is a continuity statement about one map with no larger object behind it, and the
-- slice family is NOT claimed to be a Schwartz function of e - that would need every derivative in e
-- and a weight. AND LIPSCHITZ IN EACH SEMINORM, NOT FOR A NORM: the target has no norm, so the
-- conclusion is the seminorm-wise estimate and the continuity it gives, not LipschitzWith.
-- Foundational-triple.
/-- info: 'SchwartzMap.iteratedFDeriv_comp_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.iteratedFDeriv_comp_inr

/-- info: 'SchwartzMap.norm_inr_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.norm_inr_le_one

/-- info: 'SchwartzMap.norm_fderiv_iteratedFDeriv_comp_inl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.norm_fderiv_iteratedFDeriv_comp_inl_le

/-- info: 'SchwartzMap.norm_pow_mul_norm_iteratedFDeriv_slice_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.norm_pow_mul_norm_iteratedFDeriv_slice_sub_le

/-- info: 'SchwartzMap.lipschitz_seminorm_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.lipschitz_seminorm_slice

/-- info: 'SchwartzMap.continuous_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.continuous_slice

-- BACKLOG #126(i): THE TENSOR PRODUCT OF SCHWARTZ FUNCTIONS
-- (Mathlib/Analysis/Fourier/SchwartzTensor.lean, 2026-10-08).
-- SchwartzMap.tensorProd: (p, q) -> f p * g q is Schwartz on D1 x D2 when f and g are Schwartz on the
-- factors. Mathlib has no such lemma, and #126 needs it - a composite integral kernel is built from a
-- PRODUCT of two kernels with one variable then integrated out.
-- Two ingredients. The Leibniz bound norm_iteratedFDeriv_mul_le expands the derivatives of the
-- product, and norm_iteratedFDeriv_comp_clm_le returns each factor's derivative to its own variable:
-- a derivative along a continuous linear map of norm at most one is no bigger than the derivative of
-- the function it is composed with, which is what the two projections of a product are.
-- norm_le_one_add_mul_one_add is the other: the weight SPLITS MULTIPLICATIVELY, ‖(p,q)‖ <=
-- (1+‖p‖)(1+‖q‖), because the product norm is a max - so one weight on the pair becomes one weight on
-- each factor and one_add_le_sup_seminorm_apply bounds each side. The SAME bound then serves EVERY
-- term of the Leibniz sum, which is what keeps the constant short.
-- NOT claimed. NOT BILINEAR-CONTINUOUS: this is a function of two Schwartz functions, not a
-- continuous bilinear map of Schwartz spaces. The estimate IS linear in one Finset.sup of each
-- factor's seminorms, so the stronger statement is packaging, but nothing needs it and
-- SchwartzMap.decay' asks only that a bound exist. AND SCALAR-VALUED: both factors are ℂ-valued and
-- the product is multiplication; a general bounded bilinear map is the same proof.
-- Foundational-triple.
/-- info: 'norm_iteratedFDeriv_comp_clm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_iteratedFDeriv_comp_clm_le

/-- info: 'norm_le_one_add_mul_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_le_one_add_mul_one_add

/-- info: 'SchwartzMap.tensorProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.tensorProd

-- BACKLOG #126(iii)(iv), WHICH CLOSES #126: THE COMPOSITION OF TWO WEYL OPERATORS IS A WEYL OPERATOR
-- (Mathlib/Analysis/Fourier/WeylComposition.lean, 2026-10-08).
-- weylCLM_comp: Op(K1) composed with Op(K2) = Op of a single jointly Schwartz kernel, as continuous
-- linear maps of Schwartz space. #122 made Op(K) an operator on 𝓢(ℝ, ℂ); this is the first thing a
-- CALCULUS needs, and the first statement in which the OPERATORS compose rather than the integrals.
-- THE REFRAMING IS WHAT MAKES IT SHORT. A Weyl operator IS an integral operator with a Schwartz
-- kernel: x and y enter K through the linear isomorphism (x,y) -> ((x+y)/2, x-y), so weylKernelCLM
-- (composition with it, which Mathlib's compCLMOfContinuousLinearEquiv makes a continuous linear map)
-- turns the symbol-kernel into the integral kernel AND BACK, and weylOpK_eq_integral_kernel says the
-- operator is the integral operator of that kernel. In those coordinates composition is the classical
-- kernel product, and the whole content is that the product is again SCHWARTZ.
-- compAffineCLM is composition with an INJECTIVE AFFINE map on the right, as a CLM on Schwartz space:
-- Mathlib's compCLMOfAntilipschitz wants an antilipschitz constant, and
-- antilipschitzWith_affine_of_leftInverse supplies it from an explicit linear LEFT INVERSE, which is
-- what a concrete coordinate map always has. (Wigner.lean's antilipschitzWith_affine is the
-- one-dimensional x + s*y case of the same thing; it is left as it stands because it sits below this
-- file in the import order.)
-- weylCompKernel is then the composite kernel: #126(i)'s tensor product of the two integral kernels,
-- composed with the injective ((x,z),w) -> ((x,w),(w,z)), is Schwartz on (ℝ x ℝ) x ℝ, #126(ii)
-- integrates w out, and the change of variables carries the result back to a symbol-kernel.
-- weylCompKernel_apply is the formula - the classical kernel product - and weylOpK_comp the operator
-- identity, by integral_integral_swap with integrable_weylCompIntegrand supplying Fubini's
-- hypothesis through the same tensor construction at a fixed output point.
-- NOT claimed. THE SYMBOL-LEVEL STATEMENT IS NOT HERE: that the composite's SYMBOL is the Moyal star
-- product needs the joint partial Fourier transform of #121(ii), and the h-bar squared expansion of
-- the bracket is #64; this is the operator identity with the kernel named, which is what is reachable
-- without them. ONE KERNEL CLASS, as in #122. AND NO ALGEBRA STRUCTURE IS CLAIMED: associativity, or
-- that these operators form an algebra, follows from the identity and the injectivity of
-- weylKernelCLM, but neither is stated and nothing needs them.
-- Foundational-triple.
/-- info: 'WignerFunction.antilipschitzWith_affine_of_leftInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.antilipschitzWith_affine_of_leftInverse

/-- info: 'WignerFunction.compAffineCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.compAffineCLM

/-- info: 'WignerFunction.weylKernelCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylKernelCLM

/-- info: 'WignerFunction.weylOpK_eq_integral_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_eq_integral_kernel

/-- info: 'WignerFunction.weylCompKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel

/-- info: 'WignerFunction.weylCompKernel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_apply

/-- info: 'WignerFunction.integrable_weylCompIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.integrable_weylCompIntegrand

/-- info: 'WignerFunction.weylOpK_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_comp

/-- info: 'WignerFunction.weylCLM_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCLM_comp

-- BACKLOG #127: THE WEYL OPERATORS OF SCHWARTZ KERNELS FORM A NON-UNITAL ALGEBRA
-- (Mathlib/Analysis/Fourier/WeylAlgebra.lean, 2026-10-09, out of #126).
-- #126 proved Op(K1) composed with Op(K2) = Op(K1 star K2) and claimed nothing about the structure.
-- THE ROW'S OWN ROUTE WAS WRONG, AND THAT IS THE FINDING. It said associativity follows from
-- associativity of operator composition AND the injectivity of weylKernelCLM. That does not close:
-- weylKernelCLM is the CHANGE OF COORDINATES (x,y) -> ((x+y)/2, x-y), and its injectivity says
-- nothing about whether two different kernels can give the same operator - which is exactly what
-- turning an operator identity into a kernel identity needs. The ingredient is FAITHFULNESS of Op,
-- and that is a theorem rather than bookkeeping.
-- eq_zero_of_weylOpK_eq_zero and weylOpK_injective: THE KERNEL IS DETERMINED BY THE OPERATOR. The
-- proof feeds the operator the CONJUGATE OF ITS OWN KERNEL SLICE (SchwartzMap.conjCLM of #121(i)'s
-- slice, conjugation being R-linear and not C-linear, which is why conjCLM is a map over R), so the
-- pairing becomes the integral of the squared modulus of the slice; that vanishes only if the slice
-- vanishes almost everywhere, and a continuous function vanishing almost everywhere for Lebesgue
-- measure vanishes (Measure.eq_of_ae_eq). weylCLM_injective is the same for #122's packaged
-- operators, and weylKernelCLM_injective the coordinate change (which IS bookkeeping - composition
-- with a surjection).
-- Then the algebra laws are corollaries: weylCompKernel_assoc (associativity, from
-- ContinuousLinearMap.comp_assoc), weylCompKernel_add_left/_right and
-- weylCompKernel_smul_left/_right (bilinearity). The LEFT slot rides linearity of the integral in
-- the kernel (weylOpK_add_kernel, weylOpK_smul_kernel); the RIGHT slot is the INNER operator, so it
-- goes through the operators' action on the state instead - the asymmetry is real, not cosmetic.
-- not_weylOpK_eq_id and weylCLM_ne_one: THERE IS NO UNIT, which makes the non-unitality a theorem
-- rather than a caveat. The witness is shrinkBump, a bump at the origin of outer radius 2/(n+1) as a
-- complex Schwartz function: it keeps the value 1 at the origin for every n while its pairing with
-- the kernel's slice tends to 0 by dominated convergence, dominated by the slice's own norm because
-- the bump is bounded by 1. A unit would have to reproduce a state's value at a point from an
-- integral against a BOUNDED kernel, and that is what fails.
-- NOT claimed. NO Mul INSTANCE, DELIBERATELY: declaring star as the Mul of the Schwartz space on the
-- plane would commit the type globally to the Weyl product when the pointwise product is at least as
-- natural, and a NonUnitalAlgebra instance would then fix which one every downstream file means; the
-- facts are theorems and a bundled NonUnitalAlgHom is one letI away for a consumer who wants it.
-- NOTHING ABOUT THE SYMBOL PRODUCT: faithfulness here is of K -> Op(K) on KERNELS, and that the
-- SYMBOL composes by the Moyal star product still needs #121(ii), with the h-bar squared expansion
-- at #64. AND THE NON-UNITALITY IS FOR THIS CLASS ONLY: a wider class (distributional kernels, where
-- the identity's kernel is a delta) is a different setting and is not formalised.
-- Foundational-triple.
/-- info: 'SchwartzMap.conjCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SchwartzMap.conjCLM

/-- info: 'WignerFunction.weylOpK_add_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_add_kernel

/-- info: 'WignerFunction.weylOpK_smul_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_smul_kernel

/-- info: 'WignerFunction.weylKernelCLM_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylKernelCLM_injective

/-- info: 'WignerFunction.eq_zero_of_weylOpK_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.eq_zero_of_weylOpK_eq_zero

/-- info: 'WignerFunction.weylOpK_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylOpK_injective

/-- info: 'WignerFunction.weylCLM_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCLM_injective

/-- info: 'WignerFunction.weylCompKernel_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_assoc

/-- info: 'WignerFunction.weylCompKernel_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_add_left

/-- info: 'WignerFunction.weylCompKernel_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_add_right

/-- info: 'WignerFunction.weylCompKernel_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_smul_left

/-- info: 'WignerFunction.weylCompKernel_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCompKernel_smul_right

/-- info: 'WignerFunction.shrinkBump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.shrinkBump

/-- info: 'WignerFunction.not_weylOpK_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.not_weylOpK_eq_id

/-- info: 'WignerFunction.weylCLM_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCLM_ne_one

-- BACKLOG #122: THE WEYL OPERATOR MAPS SCHWARTZ SPACE TO SCHWARTZ SPACE
-- (Mathlib/Analysis/Fourier/WeylSmooth.lean, smoothness 2026-10-07, decay 2026-10-08).
-- #92(a1) proved the output CONTINUOUS and said continuity is the first of the Schwartz seminorm
-- estimates, not the last. This is the next one.
-- iteratedFDeriv_comp_affine is THE ITERATED CHAIN RULE ALONG AN AFFINE LINE, as an identity: the
-- linear part contributes its velocity in every slot. The Weyl kernel needs exactly this, because x
-- enters K through ((x+y)/2, x-y) = (y/2, -y) + x*(1/2, 1) - an affine path with constant velocity.
-- Mathlib has the two halves (ContinuousLinearMap.iteratedFDeriv_comp_right for the linear part,
-- iteratedFDeriv_comp_add_left for the translation) and not the composite;
-- norm_iteratedFDeriv_comp_affine_le is the bound it gives, the velocity's norm to the order.
-- exists_bound_snd_iteratedFDeriv is #92(a1)'s second-slot decay at EVERY order, and
-- inv_one_add_sq_le_of_abs_sub_le is the majorant uniform on a unit ball of parameters.
-- contDiff_weylOpK assembles them through #120: smoothness at every order on each ball, hence
-- ContDiffAt everywhere, hence ContDiff. The product rule is not needed anywhere, because psi does not
-- depend on x - only the chain rule does the work, which is why this was reachable at all.
-- Foundational-triple.
/-- info: 'WignerFunction.iteratedFDeriv_comp_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.iteratedFDeriv_comp_affine

/-- info: 'WignerFunction.norm_iteratedFDeriv_comp_affine_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_iteratedFDeriv_comp_affine_le

/-- info: 'WignerFunction.exists_bound_snd_iteratedFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_snd_iteratedFDeriv

/-- info: 'WignerFunction.inv_one_add_sq_le_of_abs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.inv_one_add_sq_le_of_abs_sub_le

/-- info: 'WignerFunction.contDiff_weylOpK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.contDiff_weylOpK

-- THE DECAY HALF (2026-10-08), WHICH MAKES Op(K) A MAP OF SCHWARTZ SPACE INTO ITSELF.
-- The obstruction this row recorded was the derivative FORMULA, and #125 supplied it.
-- iteratedDeriv_weylOpK is that formula on this integrand: the k-th derivative of the output IS the
-- integral of the k-th parameter derivative, so a weight has something to move onto. The hoisted
-- partialDeriv_weylIntegrand and norm_partialDeriv_weylIntegrand_le are the identity and the
-- primitive bound BOTH halves run on - the state's value times the kernel's k-th derivative at the
-- path point, with no power of the velocity because it is a unit vector.
-- abs_le_norm_weylPath is the one inequality the half turns on: |x| <= (3/2)*norm of the path point,
-- so a polynomial weight in the PARAMETER becomes a polynomial weight on the KERNEL, where the
-- kernel's own decay can eat it.
-- exists_bound_snd_iteratedFDeriv_weighted does the eating: the kernel's decay at orders N and N+2
-- combine into a bound carrying the weight AND still decaying in the second slot, which is what
-- keeps the majorant integrable (the unweighted lemma above is its N = 0 case).
-- exists_bound_weylOpK integrates that against the state and comes out with a constant depending
-- only on K and a bound LINEAR IN ONE SEMINORM of the state - the shape SchwartzMap.mkCLM consumes -
-- and weylCLM is the operator itself, continuous and linear on Schwartz space.
-- NOT claimed. ONE KERNEL CLASS: this is the operator of a jointly Schwartz kernel, and Weyl
-- quantisation of a wider symbol class (polynomially bounded symbols, Hormander classes) is a
-- different theorem that is not proved here; #92's slicing caveat stands as written. THE CONSTANT IS
-- NOT SHARP: (3/2)^N*C*pi falls out of this route, not out of an optimisation. AND NOTHING ABOUT
-- COMPOSITION: that Op(a) composed with Op(b) is again a Weyl operator - the Moyal product - is a
-- separate brick.
-- Foundational-triple.
/-- info: 'WignerFunction.abs_le_norm_weylPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.abs_le_norm_weylPath

/-- info: 'WignerFunction.partialDeriv_weylIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.partialDeriv_weylIntegrand

/-- info: 'WignerFunction.norm_partialDeriv_weylIntegrand_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.norm_partialDeriv_weylIntegrand_le

/-- info: 'WignerFunction.iteratedDeriv_weylOpK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.iteratedDeriv_weylOpK

/-- info: 'WignerFunction.exists_bound_snd_iteratedFDeriv_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_snd_iteratedFDeriv_weighted

/-- info: 'WignerFunction.exists_bound_weylOpK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.exists_bound_weylOpK

/-- info: 'WignerFunction.weylCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCLM

/-- info: 'WignerFunction.weylCLM_apply_eq_weylOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WignerFunction.weylCLM_apply_eq_weylOp

-- BACKLOG #125: DIFFERENTIATION UNDER THE INTEGRAL SIGN, WITH THE DERIVATIVE FORMULA KEPT
-- (Mathlib/Analysis/Calculus/ContDiffParametricIntegral.lean, 2026-10-08, out of #122).
-- #120 and #124 both recorded, deliberately, that they produce the identity
-- fderiv (integral of F) = integral of fderiv F on U as a BY-PRODUCT of each induction step and keep
-- only the smoothness; #120's scope note said "nothing here needs" the formula. #122's decay half and
-- #121(ii) both need it: without a formula for the k-th derivative of the integral there is nothing
-- to move a polynomial weight x^N onto, so no Schwartz seminorm estimate is possible.
-- hasDerivAt_integral_of_bound states the first-order identity under #120's own hypotheses;
-- iteratedDeriv_integral_of_bound iterates it - on an open U, the n-th derivative of the integral IS
-- the integral of the n-th parameter derivative - by the same shift (partialDeriv_succ_left) the
-- smoothness proof runs on, with the identity kept instead of discarded. The step that makes the
-- iteration legitimate is LOCALITY: Filter.EventuallyEq.iteratedDeriv_eq lets the first-order identity,
-- which holds only on U, be substituted under the remaining derivatives at a point of the open U.
-- iteratedDeriv_integral_of_bound_le is the every-order-up-to-n form a consumer wants, and
-- integrable_partialDeriv is the integrability the formula is false without.
-- THE ROW CALLED THIS A RESTATEMENT RATHER THAN NEW MATHEMATICS, AND IT WAS. The one-line change that
-- matters is in the other direction: contDiffOn_integral_of_bound now CALLS
-- hasDerivAt_integral_of_bound instead of re-proving it inline, so the proof exists once rather than
-- twice, and the dead hFdiff it used is gone.
-- NOT claimed: still no formula over a finite-dimensional parameter - #124 keeps its own scope note,
-- and #121(ii) would want the fderiv analogue of this. #122's decay half is now unblocked but not
-- done: the estimates still have to be written.
-- Foundational-triple.
/-- info: 'integrable_partialDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_partialDeriv

/-- info: 'hasDerivAt_integral_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_integral_of_bound

/-- info: 'iteratedDeriv_integral_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_integral_of_bound

/-- info: 'iteratedDeriv_integral_of_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_integral_of_bound_le

end CSD.Tests.AxiomAudit
