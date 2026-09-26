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

/-! ### Two-level unitaries (Matrix/TwoLevel.lean, 2026-09-25, BACKLOG #70, R-005 (c)) -/

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

end CSD.Tests.AxiomAudit
