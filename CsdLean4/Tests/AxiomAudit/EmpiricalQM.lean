/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: EmpiricalQM

**Category:** Special (axiom-posture regression pins; G9 split part).

Empirical/QM pins (QM-validity twins: Bell family, no-cloning, algorithms, QEC, crypto, measurement adders).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.EmpiricalQM`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- Leggett–Garg inequality (temporal CHSH / macrorealism test, 2026-07-26): the macrorealist bound
-- K₃ ≤ 1 (genuine measure-theoretic model) + Born two-time correlation cos(2Δ) (from zenoU) +
-- quantum violation K₃(π/6) = 3/2 (Lüders bound) > 1. The record-layer/de-isolation denial of
-- non-invasive measurability is exactly why CSD is realist yet LG-violating.
/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound

/-- info: 'CSD.Empirical.QM.LeggettGarg.lgCorr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lgCorr_eq

/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_violation

/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound_violated

-- Quantum eraser (complementarity + which-path erasure, 2026-07-27): entangled path–marker Bell
-- state; joint P(a,c)=(1+ac cosφ)/4 fringe (erasure, marker-conditioned) vs flat system marginal
-- ∑_c P=1/2 (which-path info present) + bright/dark (visibility 1). Born-grounded (jointAmplitude).
/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_joint

/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_no_interference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_no_interference

/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_fringe_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_fringe_dark

-- Elitzur–Vaidman bomb tester (interaction-free measurement, 2026-07-27): balanced MZ (H·H=I) →
-- dark port 0 with no bomb (full interference); live bomb (which-path collapse) → dark port 1/4;
-- interaction_free (0 < 1/4): a dark click certifies the bomb without the photon hitting it.
/-- info: 'CSD.Empirical.QM.ElitzurVaidman.bomb_absent_dark_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.bomb_absent_dark_zero

/-- info: 'CSD.Empirical.QM.ElitzurVaidman.bomb_present_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.bomb_present_dark

/-- info: 'CSD.Empirical.QM.ElitzurVaidman.interaction_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.interaction_free

-- KCBS pentagon (state-dependent contextuality, noncontextual bound, 2026-07-27): K₅=∑⟨Πᵢ⟩≤2 over a
-- genuine measure-theoretic C₅ model (5 {0,1} observables, cyclic exclusivity) via the pentagon
-- independence-number pointwise bound + integral_mono. (QM √5 violation = separate pentagon-trig build.)
/-- info: 'CSD.Empirical.QM.KCBS.kcbs_noncontextual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_noncontextual_bound

-- KCBS QM √5 violation (pentagon on ℝ³, 2026-07-27): 5 unit vectors (kv_orth: consecutive
-- orthogonal, exclusivity) + apex; kcbs_qm_value (∑⟨ψ|Πᵢ|ψ⟩ = 5·(1/√5) = √5), kcbs_quantum_violation
-- (2 < √5). QM exceeds the noncontextual bound 2 → violates KCBS noncontextuality.
/-- info: 'CSD.Empirical.QM.KCBS.kcbs_qm_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_qm_value

/-- info: 'CSD.Empirical.QM.KCBS.kcbs_quantum_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_quantum_violation

/-- info: 'CSD.Empirical.QM.KCBS.kv_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kv_orth

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

/-- info: 'CSD.Empirical.QM.NoCommunication.no_communication_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.no_communication_reduced

/-- info: 'CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq

-- E3 CPTP form (channels phase C4): an arbitrary local channel Φ ⊗ id on Alice's
-- subsystem leaves Bob's reduced state traceLeft invariant (channel_no_communication),
-- via the Kraus-summed partial-trace lemma (traceLeft_sum_conjTranspose_kronecker_one)
-- and the local channel Φ ⊗ id (tensorRight). Retires the E3 CPTP gap. Foundational triple.
/-- info: 'CSD.Empirical.QM.NoCommunication.channel_no_communication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.channel_no_communication

-- Deutsch-Jozsa (R4): the circuit H^⊗n ∘ U_f ∘ H^⊗n on |0ⁿ⟩ discriminates constant from
-- balanced f in one query — prob(measure 0ⁿ) = 1 if constant, 0 if balanced. Foundational
-- triple. First algorithm in the quantum-algorithm branch.
/-- info: 'CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_constant

/-- info: 'CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_balanced

-- Simon's algorithm (single-register reduced analysis): H^⊗n on the coset state
-- (1/√2)(|x₀⟩+|x₀⊕s⟩). The general Hadamard entry collects per-qubit signs into one parity
-- sign (Hn_apply_inner), giving amplitude (1/√2)^{n+1}·(-1)^⟨x₀,y⟩·(1+(-1)^⟨s,y⟩)
-- (simon_amplitude). Hence prob = 0 when ⟨s,y⟩ odd (simon_orthogonal, the orthogonality property:
-- every outcome ⊥ s) and prob = 2/2ⁿ when ⟨s,y⟩ even (simon_uniform, uniform on s^⊥); the
-- coset state is normalised for s ≠ 0 (cosetState_normalized). Foundational triple.
/-- info: 'CSD.Empirical.QM.Simon.Hn_apply_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.Hn_apply_inner

/-- info: 'CSD.Empirical.QM.Simon.simon_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_amplitude

/-- info: 'CSD.Empirical.QM.Simon.simon_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_orthogonal

/-- info: 'CSD.Empirical.QM.Simon.simon_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_uniform

/-- info: 'CSD.Empirical.QM.Simon.cosetState_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.cosetState_normalized

-- Swap test (ancilla-interferometry overlap/fidelity estimator): the circuit
-- H_anc ∘ cSWAP ∘ H_anc on |0⟩⊗ψ⊗φ collapses (two-Hadamard ancilla orthogonality) to the
-- ancilla-0 amplitude (1/2)(ψ i φ j + φ i ψ j) (swapTest_apply); the ancilla-0 marginal is
-- P(0) = (1 + |⟨ψ,φ⟩|²)/2 (swap_test_prob) via the tensor identity ⟨ψ⊗φ,φ⊗ψ⟩ = |⟨ψ,φ⟩|².
-- Hence P(0) = 1 for equal states (swap_test_equal) and 1/2 for orthogonal (swap_test_orthogonal).
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_prob

/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_equal

/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_orthogonal

-- Hadamard test (parent of the swap test; expectation-value estimator): the circuit
-- H_anc ∘ cU ∘ H_anc on |0⟩⊗ψ collapses (two-Hadamard ancilla orthogonality) to the
-- ancilla-0 amplitude (1/2)(ψ i + (Uψ) i) (hadTest_apply); the ancilla-0 marginal is
-- P(0) = (1 + Re⟨ψ,Uψ⟩)/2 (hadamard_test_prob), ancilla-1 P(1) = (1 - Re⟨ψ,Uψ⟩)/2
-- (hadamard_test_prob1), so P(0) - P(1) = Re⟨ψ,Uψ⟩ (hadamard_test_prob_diff); P(0) = 1 at
-- Uψ = ψ (hadamard_test_eq_one). The swap test is this at U = swapMap on the doubled
-- register: swapTestProb0 = hadTestProb0 swapMap (ψ⊗φ) (swap_test_via_hadamard), value
-- (1 + ‖⟨ψ,φ⟩‖²)/2 (hadamard_test_swap_closed) — derived NATIVELY through hadamard_test_prob
-- via the inner identity Re⟨ψ⊗φ,swap(ψ⊗φ)⟩ = ‖⟨ψ,φ⟩‖² (re_inner_tensorEuc_swap) and the
-- tensor unit norms, NOT through SwapTest.swap_test_prob. Foundational triple.
/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob1

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob_diff

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_eq_one

/-- info: 'CSD.Empirical.QM.HadamardTest.swap_test_via_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.swap_test_via_hadamard

/-- info: 'CSD.Empirical.QM.HadamardTest.re_inner_tensorEuc_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.re_inner_tensorEuc_swap

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_swap_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_swap_closed

-- Bernstein-Vazirani: the FULL phase-oracle circuit H^⊗n ∘ U_f ∘ H^⊗n on |0ⁿ⟩ for the hidden
-- linear function f_a(x) = ⟨a,x⟩. The 𝔽₂ character sum ∑ₓ (-1)^⟨z,x⟩ = 2ⁿ·[z=0]
-- (bitInner_char_sum) collapses the output amplitude to the Kronecker delta δ_{y,a}
-- (bv_amplitude), so the hidden a is measured with certainty (bv_certain) and every other
-- outcome has probability 0 (bv_zero). One query. Foundational triple.
/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bitInner_char_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bitInner_char_sum

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_amplitude

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_certain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_certain

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_zero

-- Grover (R5+): amplitude amplification of a marked item w. The genuine reflection operators
-- oracle = I - 2|w⟩⟨w| and diffusion = 2|s⟩⟨s| - I keep the evolution in the 2D (|w⟩, rest)
-- plane, where one step is a rotation by 2θ (sin θ = 1/√N). The closed form for the success
-- probability after k steps is sin²((2k+1)θ) (grover_success). Foundational triple.
-- RE-DERIVED 2026-08-29 from the general BHMT theorem (Mathlib/QuantumInfo/
-- AmplitudeAmplification.lean, pinned in the MathlibStaging part): groverStep w =
-- ampStep uniformState {w} (groverStep_eq_ampStep), uniformState is the rotation-plane state at
-- the Grover angle (uniformState_eq_ampState), and ampStep_iterate carries the closed form. The
-- file's previous self-contained symState rotation development was retired (the priced
-- atlas-extraction pilot, plan AA-3); statements of both pinned theorems unchanged. NEW at the
-- same stroke: the k-marked-items instance (grover_multi_success, |G| marked of 2^n on the
-- uniform start, success sin²((2j+1)·arcsin √(|G|/N)) exactly).
/-- info: 'CSD.Empirical.QM.Grover.grover_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Grover.grover_success

/-- info: 'CSD.Empirical.QM.Grover.grover_multi_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Grover.grover_multi_success

-- Grover optimal iteration: when the accumulated angle hits π/2 ((2k+1)θ = π/2) the marked
-- item is measured with certainty (grover_certain, prob = 1). Foundational triple.
/-- info: 'CSD.Empirical.QM.Grover.grover_certain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Grover.grover_certain

-- Shor's algorithm, quantum core (M1 = S1+S2+S3-core; specs/shor-plan.md). The genuine
-- multiply-by-a oracle |y⟩↦|a·y⟩ on EuclideanSpace ℂ (ZMod N) has eigenvectors u_s with
-- eigenvalues ω_r^s (mulOracle_eigU, r = orderOf a); the QFT inverse inverts the QFT exactly so
-- phase estimation reads a QFT column with certainty (phase_estimation_exact — RELOCATED
-- 2026-08-29 to Cat-1 Mathlib/QuantumInfo/PhaseEstimation.lean, pinned in the MathlibStaging
-- part); and in the ideal case r ∣ T the eigenphase ω_r^s is read off as the basis state
-- s·(T/r) with prob 1 (shor_order_readout, the M1 headline). Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.mulOracle_eigU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.mulOracle_eigU

/-- info: 'CSD.Empirical.QM.Shor.shor_order_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_order_readout

-- Shor's algorithm, M1.5 (full ideal-case output distribution; specs/shor-plan.md). The genuine
-- two-register modexp state postModexpState = (1/√T) ∑_x |x⟩|a^x⟩ (jointModexp_initial), expanded
-- in the eigenbasis (basisState_apow_eq + postModexp_eq_eigenbasis), is read by the
-- counting-register inverse QFT (qftInvCount_postModexp) so that measuring the counting register
-- gives prob = 1/r on each multiple s·(T/r) (shor_order_distribution, the uniform-1/r marginal M1
-- deferred). Foundational triple. General r ∤ T (S4) remains the open quantum piece.
/-- info: 'CSD.Empirical.QM.Shor.shor_order_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_order_distribution

-- Shor's algorithm, S4 (phase estimation lower bound, general r ∤ T; specs/shor-plan.md §S4). The
-- single-eigenvector / generic-phase Dirichlet-kernel 4/π² estimate is generic in T and was
-- RELOCATED 2026-08-29 to Cat-1 Mathlib/QuantumInfo/PhaseEstimation.lean (phaseStateR,
-- applyQFTinv_phaseStateR_apply, prob_phaseStateR_eq, phase_estimation_lower_bound — pinned in
-- the MathlibStaging part). What stays Shor's is the corollary instantiating φ = s/r.
-- Foundational triple. The two-register r ∤ T marginal (cross-term control across the r
-- eigen-branches) is beyond S4 and deferred.
/-- info: 'CSD.Empirical.QM.Shor.shor_phase_estimation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_phase_estimation_lower_bound

-- Shor S5 (period recovery, uniqueness route): the measured count determines the order r.
-- Distinct lowest-terms fractions are ≥ 1/(b·d) apart (abs_sub_rat_ge), so a fraction within
-- 1/(2T) of c/T with denominator product < T is unique (approx_unique ⟹ shor_period_determined).
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.abs_sub_rat_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.abs_sub_rat_ge

/-- info: 'CSD.Empirical.QM.Shor.approx_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.approx_unique

/-- info: 'CSD.Empirical.QM.Shor.shor_period_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_period_determined

-- Shor S6 (factoring from order): a nontrivial square root of unity mod N yields a proper
-- nontrivial divisor gcd(x-1, N) of N. The classical reduction order-finding ⟹ factoring.
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.nontrivial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.nontrivial_factor

/-- info: 'CSD.Empirical.QM.Shor.N_has_nontrivial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.N_has_nontrivial_factor

--- S6 bridge: an even-order unit `a` with `a^(r/2) ≢ ±1` gives the nontrivial-square-root
--- hypotheses for the integer lift `x`. Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.even_order_sqrt_unity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.even_order_sqrt_unity

--- S6 composed: even order ⟹ proper nontrivial divisor gcd(x-1, N). The full classical
--- reduction order-finding ⟹ factoring. Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_factor_of_even_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_factor_of_even_order

--- S7b: the per-cyclic-factor 2-adic-valuation distribution bound. In a finite cyclic group of
--- even order, no v₂(order) class exceeds half the group. Pure finite group theory; foundational
--- triple. The meaty, reusable core of the random-`a` ≥ 1/2 argument (specs/shor-plan.md §S7).
/-- info: 'CSD.Empirical.QM.Shor.card_v2_orderOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.card_v2_orderOf_le

-- S7c: the `−1` characterisation (abstract cyclic core). In a finite cyclic group the unique
-- order-2 element `z` is hit by `a^(R/2)` iff v₂(orderOf a) = v₂(R). Per-cyclic-factor core of the
-- Shor `a^(r/2) = -1` success condition. Pure finite group theory; foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.pow_half_eq_orderTwo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.pow_half_eq_orderTwo_iff

-- S7a: two-factor CRT framing for units. The CRT iso `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`
-- transports `orderOf` to an `lcm` (`unitsCRT_orderOf`), splits the success witness `-1` to
-- `(-1, -1)` (`unitsCRT_neg_one`), and factors the cardinality (`card_units_mul`). Cyclicity-
-- agnostic assembly of standard Mathlib pieces; foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.unitsCRT_orderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsCRT_orderOf

/-- info: 'CSD.Empirical.QM.Shor.unitsCRT_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsCRT_neg_one

/-- info: 'CSD.Empirical.QM.Shor.card_units_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.card_units_mul

-- S7d-1: the diagonal count (abstract). Sums the per-factor v₂ bound `card_v2_orderOf_le` (S7b)
-- over the first coordinate of a product group to bound the matched-v₂ diagonal by half. Only the
-- second factor is cyclic / even; Finset sum-decomposition of standard Mathlib pieces; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_diag_le

-- S7d-2a: the BAD characterisation (abstract). For a pair of finite cyclic groups with order-2
-- elements z₁, z₂, the Shor "BAD" event ¬(Even r ∧ p^(r/2) ≠ (z₁,z₂)) holds iff the two component
-- orders share the same 2-adic valuation. Prod.orderOf (→ lcm) + Nat.factorization_lcm (→ max) +
-- pow_half_eq_orderTwo_iff (S7c) per factor + omega case split; triple.
/-- info: 'CSD.Empirical.QM.Shor.bad_iff_v2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.bad_iff_v2_eq

-- S7d-2b-i (two_mul_card_good_ge): for a pair of finite cyclic groups G₁, G₂ with distinguished
-- order-2 elements z₁, z₂, the Shor "GOOD" event Even (orderOf p) ∧ p^(orderOf p/2) ≠ (z₁,z₂) covers
-- at least half: |G₁|·|G₂| ≤ 2·#GOOD. Complement of bad_iff_v2_eq (S7d-2a) against the diagonal count
-- two_mul_card_diag_le (S7d-1) via Finset.filter_congr + card_filter_add_card_filter_not + omega; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_good_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_good_ge

-- S7d-2b-ii (shor_good_transport): the abstract GOOD lower bound transported onto the actual units
-- group of a coprime composite. For coprime m, n with cyclic unit groups each having orderOf(-1)=2,
-- |(ZMod (m·n))ˣ| ≤ 2·#GOOD. Transport two_mul_card_good_ge (S7d-2b-i) across unitsCRT (S7a) via a
-- Finset.card_bij filter bijection (predicate corresponds: MulEquiv.orderOf_eq + unitsCRT_neg_one)
-- + card_units_mul; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_good_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_good_transport

-- S7★ (shor_random_a_success): the prime-power headline. For distinct odd primes p ≠ q and
-- exponents α, β ≥ 1, the Shor GOOD event covers ≥ half of (ZMod (p^α·q^β))ˣ — random-a success ≥ 1/2.
-- Instantiates shor_good_transport (S7d-2b-ii) at m=p^α, n=q^β: coprimality (Nat.Coprime.pow),
-- cyclicity (ZMod.isCyclic_units_of_prime_pow), orderOf(-1)=2 (orderOf_neg_one, ringChar=p^α≠2); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success

-- S7★ (shor_success_prob_ge): the probability reading of the headline. Restates the counting bound
-- as #GOOD/#units ≥ 1/2 under uniform sampling. Pure ℚ-arithmetic corollary of shor_random_a_success
-- (le_div_iff₀ + Fintype.card_pos + linarith on the cast bound); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_success_prob_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_success_prob_ge

-- gen-C (two_mul_card_pi_diag_le): the m-fold diagonal count (abstract). General-m analogue of
-- two_mul_card_diag_le: for a finite family of finite cyclic groups with the distinguished factor
-- i₀ of even order (and a free factor i₁ ≠ i₀), the fully-matched-v₂ diagonal is at most half the
-- product group. Route: fiberwise partition by the common valuation (card_eq_sum_card_fiberwise),
-- each fiber a piFinset product (Fintype.card_piFinset), factor out i₀ (mul_prod_erase) bounded by
-- card_v2_orderOf_le (S7b), erased sum bounded by a disjoint-biUnion count over {i // i ≠ i₀}; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_pi_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_pi_diag_le

-- gen-A (orderOf_pi): the order of a tuple in a finite indexed product is the lcm of component
-- orders (m-fold Prod.orderOf, re-exported from Mathlib's Pi.orderOf); triple.
/-- info: 'CSD.Empirical.QM.Shor.orderOf_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.orderOf_pi

-- gen-A (unitsPiCRT_neg_one): the indexed units-CRT iso (ZMod (∏ N i))ˣ ≃* Π i, (ZMod (N i))ˣ sends
-- the success witness -1 to the constant tuple fun _ => -1 (m-fold unitsCRT_neg_one); triple.
/-- info: 'CSD.Empirical.QM.Shor.unitsPiCRT_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsPiCRT_neg_one

-- gen-B (bad_iff_v2_eq_pi): the m-fold BAD characterisation (Pi form). For a finite indexed family
-- of finite cyclic groups with distinguished order-2 elements, the Shor BAD event holds iff every
-- component order shares the 2-adic valuation of the distinguished index (m-fold bad_iff_v2_eq);
-- triple.
/-- info: 'CSD.Empirical.QM.Shor.bad_iff_v2_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.bad_iff_v2_eq_pi

-- gen-B (two_mul_card_good_pi_ge): the abstract m-fold GOOD lower bound (Pi form). For a finite
-- indexed family of finite cyclic groups each with a distinguished order-2 element and a free index
-- i₁ ≠ i₀, the Shor GOOD event covers at least half the product group (m-fold two_mul_card_good_ge);
-- triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_good_pi_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_good_pi_ge

-- gen-D (shor_random_a_success_pi): the m-fold coprime transport (indexed S7d-2b-ii). For a
-- pairwise-coprime family N : ι → ℕ of nonzero moduli with cyclic unit groups each having
-- orderOf (-1) = 2 and a free index i₁ ≠ i₀, the Shor GOOD event covers at least half of
-- (ZMod (∏ i, N i))ˣ (m-fold shor_good_transport, transported across unitsPiCRT); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success_pi

-- gen-E (shor_random_a_success_general): the general odd-composite headline (S7★-gen). For odd N
-- with ≥ 2 distinct prime factors, the Shor GOOD event covers at least half of (ZMod N)ˣ.
-- Instantiates gen-D at the prime-power factorisation ι := ↥N.primeFactors,
-- N' p := p^(N.factorization p) (∏ N' = N, pairwise coprime; per-factor odd-prime-power cyclicity +
-- orderOf(-1)=2; free index pair from one_lt_card), transported ∏N' → N via the units MulEquiv; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success_general

-- gen-E (shor_success_prob_ge_general): the probability reading of the general headline. Restates
-- the counting bound as #GOOD/#units ≥ 1/2 under uniform sampling mod an odd composite N. Pure
-- ℚ-arithmetic corollary of shor_random_a_success_general; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_success_prob_ge_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_success_prob_ge_general

-- Shor factoring capstone (shor_random_a_yields_factor): pointwise, a GOOD unit a (Even (orderOf a)
-- ∧ a^(orderOf a/2) ≠ -1 in the units group) yields a proper nontrivial factor gcd(x-1, N) of N,
-- where x lifts a^(orderOf a/2). Bridges the units ≠ ±1 conditions to the ZMod-coercion hypotheses
-- of shor_factor_of_even_order (S6); foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_yields_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_yields_factor

-- Shor factoring capstone (shor_factor_prob_ge): the probability reading. For odd N with ≥ 2
-- distinct prime factors, a uniformly random unit yields a proper nontrivial factor of N with
-- probability ≥ 1/2 — the GOOD filter ⊆ the factor-yielding filter (shor_random_a_yields_factor),
-- so the ≥ 1/2 GOOD frequency (shor_success_prob_ge_general) transports by card + ℚ monotonicity.
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_factor_prob_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_factor_prob_ge

-- E2: No-broadcasting, pure-marginal confinement core. A bipartite PSD operator
-- with a pure first-factor marginal |ψ⟩⟨ψ| is confined to that pure sector
-- ((P⊗I)·ρ·(P⊗I) = ρ) — the obstruction to broadcasting a pure state. Built on the
-- partial-trace module laws + PSD block-vanishing. Foundational triple. The full
-- BCFJS commuting-states theorem is fidelity-gated (deferred QI-infra tranche).
/-- info: 'CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement

-- Wiesner single-slot mint/verify protocol on top of quantum_money_unforgeable:
-- honest money verifies with certainty (completeness), no isometry forges both
-- non-orthogonal notes (no perfect forgery, instantiating quantum_money_unforgeable),
-- and the per-slot acceptance advantage is bounded by the shared Protocols
-- SecurityBound (ε = 1, the trivial probability bound; quantitative cloning ε out
-- of scope). Foundational triple only.
/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_verify_honest

/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_forge_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_forge_impossible

/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_forge_advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_forge_advantage_le

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

-- E91 device-independent asymptotic secret-key rate (Crypto/E91KeyRate.lean):
-- a certified CHSH violation 2 < S ≤ 2√2 (above the LHV ceiling) gives a positive
-- DI secret-key rate (e91_key_rate_pos_of_chsh, UNCONDITIONAL), with boundary
-- values r(2) = 0 and r(2√2) = 1, instantiating the minimal reusable Protocols
-- interface (SecurityBound / RealProtocol.secure / IdealQKD via secure_emulates).
-- Reuses Real.binEntropy and lhvCHSH_abs_le_two. Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_pos_of_chsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_pos_of_chsh

/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_zero_at_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_zero_at_classical

/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_one_at_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_one_at_tsirelson

/-- info: 'CSD.Empirical.QM.E91.e91_eavesdropper_chsh_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_eavesdropper_chsh_le_two

/-- info: 'CSD.Empirical.QM.E91.e91_eavesdropper_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_eavesdropper_advantage

/-- info: 'CSD.Empirical.QM.E91.e91_protocol_secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_protocol_secure

/-- info: 'CSD.Empirical.QM.E91.e91_chsh_certifies_secure_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_chsh_certifies_secure_key

-- E91 finite-sample / finite-key concentration (Crypto/E91FiniteKey.lean):
-- the empirical CHSH estimator Sn = (sum of n bounded, unbiased, independent
-- per-round CHSH statistics)/n concentrates around the true S via Mathlib's
-- sub-Gaussian Hoeffding pipeline (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
-- per round + measure_sum_range_ge_le_of_iIndepFun Chernoff tail), giving the
-- finite-round confidence bridge to e91_key_rate_pos_of_chsh. Finite-SAMPLE
-- confidence, NOT composable finite-key security. Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.e91_chsh_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_chsh_concentration

/-- info: 'CSD.Empirical.QM.E91.e91_finite_key_confidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_finite_key_confidence

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

-- QEC: the three-qubit bit-flip code (first QEC theorem; foundational-triple only).
/--
info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_single_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_single_bitflip

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X1

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X2

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X3

-- Identifiability (the load-bearing QEC ingredient, now inside the bit-flip capstone): the
-- four error syndromes {I,X₁,X₂,X₃} → {(+,+),(−,+),(−,−),(+,−)} are pairwise distinct, so
-- measuring (Z₁Z₂, Z₂Z₃) pins down the error. Injectivity of errorSyndrome.
/-- info: 'CSD.Empirical.QM.QEC.three_qubit_syndromes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_syndromes_distinct

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_syndrome_eigenstates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_syndrome_eigenstates

/--
info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_single_phaseflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_single_phaseflip

-- Shor-9 by concatenation (ShorNine.lean, Q5/E1, 2026-08-13): the combinator
-- (block Kronecker action factorises through the block tensor), all eight
-- stabilisers fix the code space, the X/Z syndrome tables (Z degenerate in
-- the inner position), and the correction set {X, Z, XZ} at every one of the
-- nine positions -- with the Z recovery needing only the block syndrome.
/-- info: 'CSD.Empirical.QM.QEC.tel9_bkron_vkron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.tel9_bkron_vkron

/-- info: 'CSD.Empirical.QM.QEC.innerStab_fixes_shorLogical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.innerStab_fixes_shorLogical

/-- info: 'CSD.Empirical.QM.QEC.outerStab_fixes_shorLogical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.outerStab_fixes_shorLogical

/-- info: 'CSD.Empirical.QM.QEC.innerStab_syndrome_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.innerStab_syndrome_X

/-- info: 'CSD.Empirical.QM.QEC.outerStab_syndrome_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.outerStab_syndrome_Z

/-- info: 'CSD.Empirical.QM.QEC.xSyndromeSign_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.xSyndromeSign_injective

/-- info: 'CSD.Empirical.QM.QEC.shor_corrects_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.shor_corrects_X

/-- info: 'CSD.Empirical.QM.QEC.shor_corrects_Z_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.shor_corrects_Z_degenerate

/-- info: 'CSD.Empirical.QM.QEC.shor_corrects_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.shor_corrects_XZ

-- Error discretization (2026-07-27): WHY correcting four Paulis corrects a CONTINUUM of errors.
-- pauli_decomposition -- every 2x2 complex matrix is c0.I + c1.X + c2.Z + c3.XZ with the
-- coefficients read off its entries ((M00 +/- M11)/2, (M01 +/- M10)/2); no analysis, no choice.
-- pauli_span_top says the same as span C {I,X,Z,XZ} = TOP: the Pauli set does not merely happen to
-- cover the errors a given code faces, it EXHAUSTS the single-qubit operator space.
-- error_discretization_qubit_1/2/3 lift it to the three-qubit code (kron3 is C-linear in each
-- slot), and errored_codeword_eq lands it on states: an arbitrary single-qubit error produces
-- exactly the corresponding combination of the four discrete corrupted states, so no continuum of
-- OUTCOMES accompanies the continuum of ERRORS. This is the conceptual content that makes
-- ThreeQubit (bit flips) + PhaseFlip (phase flips) a general error-correction claim rather than
-- two special cases. HONEST SCOPE (see the module's "Scope" section): this is the DISCRETIZATION
-- half only. It is NOT a proof that the three-qubit code corrects arbitrary errors -- that code's
-- correctable set is {I,X1,X2,X3} and Z errors lie outside it. Completing the argument to "any
-- single-qubit error" needs the CONCATENATED Shor 9-qubit code (open, specs/BACKLOG.md, blocked on
-- 512-dimensional infrastructure); the syndrome-collapse half (error subspaces orthogonal, so
-- measurement projects onto one correctable branch) is not claimed by THESE pins -- it is
-- delivered and pinned below (errored_pairwise_orthogonal, three_qubit_corrects_span_error).
/-- info: 'CSD.Empirical.QM.QEC.pauli_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.pauli_decomposition

/-- info: 'CSD.Empirical.QM.QEC.pauli_span_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.pauli_span_top

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₁

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₂

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₃

/-- info: 'CSD.Empirical.QM.QEC.errored_codeword_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.errored_codeword_eq

-- Syndrome collapse (2026-07-27): the half that JOINS error discretization to the four
-- point-checks. Before this, the corpus had "an arbitrary error is a combination of four"
-- (ErrorDiscretization) and "each of the four is corrected" (ThreeQubit) with NOTHING connecting
-- them -- a superposition of error branches is not obviously reducible to one branch, so
-- discretization was true but load-BEARING on nothing. errored_pairwise_orthogonal supplies the
-- missing fact: the four errored codewords are mutually orthogonal (their supports are disjoint --
-- {000,111}, {100,011}, {010,101}, {001,110} -- which is the concrete form of the distinct
-- (Z1Z2,Z2Z3) syndrome pairs; available directly, so no spectral theorem needed).
-- branch_overlap_X1/X2/X3 is the collapse step proper: the overlap of the corrupted codeword with
-- branch k is EXACTLY c_k times that branch's norm, so the syndrome measurement reads off one
-- coefficient and is blind to the other three. three_qubit_corrects_span_error bundles all four
-- ingredients (decomposition, orthogonality, extraction, branch-wise recovery): THE CODE CORRECTS
-- AN ARBITRARY ERROR IN span C {I,X1,X2,X3} -- a continuum, not four points.
-- SCOPE: still the BIT-FLIP span, the 3-qubit code's actual correctable set. Reaching all four
-- Paulis per qubit (so pauli_span_top applies and EVERY single-qubit error is corrected) needs the
-- concatenated Shor-9 code, open on 512-dimensional infrastructure (specs/BACKLOG.md). What closed
-- here is the gap WITHIN the 3-qubit story.
/-- info: 'CSD.Empirical.QM.QEC.errored_pairwise_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.errored_pairwise_orthogonal

/-- info: 'CSD.Empirical.QM.QEC.spanError_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.spanError_logical

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X1

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X2

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X3

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_span_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_span_error

-- Phase-flip identifiability (Hadamard dual; now inside the phase-flip capstone).
/-- info: 'CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndromes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndromes_distinct

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndrome_eigenstates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndrome_eigenstates

-- The bit-flip error channel (channels phase C4): the single-qubit error as a CPTP
-- mixedUnitaryChannel {I, X}, Φ(ρ) = (1-p)ρ + p XρX — the honest "error = decoherence"
-- model behind the bit-flip code. Foundational triple.
/-- info: 'CSD.Empirical.QM.QEC.bitFlipChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.bitFlipChannel_apply

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

-- Two-qubit gate UNITARITY (Gᴴ * G = 1) via Hermiticity (Gᴴ = G) + involutivity.
/-- info: 'CSD.Empirical.QM.Gates.qmCNOT_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCNOT_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmSWAP_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmSWAP_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmCZ_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCZ_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_factorisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_factorisation

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus

/-- info: 'CSD.Empirical.QM.Gates.qmToffoli_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmToffoli_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmFredkin_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmFredkin_mul_self

-- Multi-qubit gate UNITARITY (Gᴴ * G = 1) via Hermiticity + involutivity.
/-- info: 'CSD.Empirical.QM.Gates.qmToffoli_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmToffoli_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmFredkin_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmFredkin_unitary

/-! ### L5-a measurement-based AND-uncomputation (Gidney measure-and-correct gadget) -/

/-- info: 'CSD.Empirical.QM.measureUncompute_uncomputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_uncomputes

/-- info: 'CSD.Empirical.QM.measureUncompute_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_basisState

/-- info: 'CSD.Empirical.QM.andInput_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andInput_nontrivial

/-- info: 'CSD.Empirical.QM.gadgetGateList_zero_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetGateList_zero_toffoli

/-! ### L5-b operator↔list link and cost as an operator property -/

/-- info: 'CSD.Empirical.QM.gadgetGateList_denotes_measureUncompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetGateList_denotes_measureUncompute

/-- info: 'CSD.Empirical.QM.measureUncompute_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_cost

/-- info: 'CSD.Empirical.QM.measureUncompute_toffoli_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_toffoli_eq_zero

/-! ### #31 localized amplitude lift of the AND-uncompute block (L5-c bridge, cell granularity) -/

-- The gate-lift layer (andUncompMat_lifts_denote and its cluster) was EXTRACTED 2026-08-21 to
-- Mathlib/QuantumInfo/Reversible/Lift.lean (Cat-1, namespace Reversible); its pins moved to the
-- MathlibStaging part. The gadget-equivalence pins below stay — that content is 3-Local.

/-- info: 'CSD.Empirical.QM.andUncompMat_uncomputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompMat_uncomputes

/-- info: 'CSD.Empirical.QM.andUncompute_measureUncompute_agree_on_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measureUncompute_agree_on_block

/-- info: 'CSD.Empirical.QM.andUncompute_measureUncompute_same_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measureUncompute_same_data

/-- info: 'CSD.Empirical.QM.andUncompute_measurement_saving' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measurement_saving

-- EC-6 / L5-d (2026-07-09): the circuit-level measurement-discipline saving threaded through the whole
-- AND-adder. Each of the n fresh-AND uncomputes is replaced by the proven-equivalent measurement gadget
-- (same data, 0 Toffoli), so the measurement-discipline AND-adder costs 3n — exactly HALF the unitary 6n
-- (andAdd_measurement_halves). The per-cell data-effect equivalence is proved; the full channel-level
-- composition over all cells is the standing residual.
/-- info: 'CSD.Empirical.QM.andAdd_measurement_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_measurement_toffoli

/-- info: 'CSD.Empirical.QM.andAdd_measurement_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_measurement_halves

/-! ### L5-d measurement-based AND-adder re-cost (Build #21) -/

/-- info: 'CSD.Empirical.QM.gadgetBlockToffoli_eq_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetBlockToffoli_eq_zero

/-- info: 'CSD.Empirical.QM.numUncomputeBlocks_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.numUncomputeBlocks_eq

/-- info: 'CSD.Empirical.QM.measUncomputeGadgets_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measUncomputeGadgets_toffoli

/-- info: 'CSD.Empirical.QM.measAddToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAddToffoli_eq

/-- info: 'CSD.Empirical.QM.andAdd_toffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_toffoli_eq

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_saving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_saving

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_savings_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_savings_eq

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_256

/-- info: 'CSD.Empirical.QM.perBlock_saving' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.perBlock_saving

/-- info: 'CSD.Empirical.QM.measAdd_saving_aggregates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_saving_aggregates

/-! ### Gidney adder measurement re-cost (Empirical/QM/MeasurementGidneyAdder.lean, Build #35) -/

/-- info: 'CSD.Empirical.QM.gidneyMeasAddToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeasAddToffoli_eq

/-- info: 'CSD.Empirical.QM.gidneyMeasAdd_saving_aggregates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeasAdd_saving_aggregates

/-- info: 'CSD.Empirical.QM.gidney_beats_cuccaro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidney_beats_cuccaro

/-- info: 'CSD.Empirical.QM.gidney_toffoli_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidney_toffoli_256

-- EC-3 capstone (2026-07-09): the measurement-discipline ADDER HIERARCHY, unifying EC-3 (Gidney
-- measurement adder, n) and EC-6/L5-d (AND-adder measurement, 3n). Each of the four costs is a proven
-- circuit figure: meas-Gidney n < unitary-Gidney 2n < meas-AND 3n < unitary-AND 6n. The measurement
-- Gidney adder is the cheapest reversible adder in the corpus (gidneyMeas_cheapest). Channel-level
-- composition over all cells is the standing residual shared by EC-3/EC-6.
/-- info: 'CSD.Empirical.QM.measurement_adder_hierarchy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measurement_adder_hierarchy

/-- info: 'CSD.Empirical.QM.gidneyMeas_cheapest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeas_cheapest

-- The Steane [[7,1,3]] code (Empirical/QM/QEC/Steane.lean, 2026-08-29; plan
-- specs/steane-plan.md; candidate 4 of the 2026-08-28 five). The first genuine CSS
-- instance of the GK-3 stabiliser layer: the Hamming [7,4] parity rows give 3 X-type + 3
-- Z-type generators, the CSS condition H H^T = 0 (kernel-checked) makes the trivial sign
-- coherent, and the general layer instantiates -- trace 2^7/2^6 = 2 (one logical qubit,
-- steane_code_dimension). The logical states (uniform superpositions over the row space
-- and its all-ones coset) are proved stabilised by ALL 64 group elements and orthonormal;
-- Xbar = X^{1} swaps them, Zbar = Z^{1} fixes |0bar> and negates |1bar> -- a genuine
-- encoded qubit. Distance mechanism: single-qubit errors have nonzero pairwise-distinct
-- syndromes (the Hamming distance-3 property; via pauliOp_comm = anticommutation with a
-- syndrome-identified generator; CSS self-duality covers both error types). HONEST SCOPE:
-- no recovery map, no Knill-Laflamme, no fault tolerance -- same posture as the
-- three-qubit modules. Foundational triple.
/-- info: 'CSD.Empirical.QM.QEC.Steane.steane_code_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.Steane.steane_code_dimension

/-- info: 'CSD.Empirical.QM.QEC.Steane.steaneZero_stabilised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.Steane.steaneZero_stabilised

/-- info: 'CSD.Empirical.QM.QEC.Steane.logicalZ_steaneOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.Steane.logicalZ_steaneOne

/-- info: 'CSD.Empirical.QM.QEC.Steane.steane_syndrome_single_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.Steane.steane_syndrome_single_injective

-- ccxAtMat_lifts_denote (the arbitrary-wire lift): EXTRACTED 2026-08-21 to
-- Mathlib/QuantumInfo/Reversible/Lift.lean; pinned in the MathlibStaging part as
-- Reversible.ccxAtMat_lifts_denote.

end CSD.Tests.AxiomAudit
