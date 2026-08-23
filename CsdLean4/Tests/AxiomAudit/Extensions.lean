/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: Extensions

**Category:** Special (axiom-posture regression pins; G9 split part).

CV + Thermo pins (finite-mode field content; thermodynamics track).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.Extensions`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- W4 (CV/ApproxCCR): the finite-dimensional obstruction to exact canonical
-- commutation. trace(QP - PQ) = 0 but trace(c•1) = c*card, so no finite matrices
-- satisfy [Q,P] = c•1 when c*card ≠ 0. The physics corollary is c = iℏ.
-- Foundational triple; CSD-free general matrix facts (the CSD reading is docstring
-- only). Motivates the finite-sector reading of position/momentum; does NOT derive CV-QM.
/-- info: 'CSD.CV.trace_commutator_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.trace_commutator_eq_zero

/-- info: 'CSD.CV.trace_scalar_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.trace_scalar_identity

/-- info: 'CSD.CV.no_exact_finite_ccr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.no_exact_finite_ccr

/-- info: 'CSD.CV.no_exact_finite_ccr_ihbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.no_exact_finite_ccr_ihbar

-- CV-1 (CV/Position): the positive counterpart to W4 — a genuine finite position observable
-- Q_N = diag(x_j) on an N-point symmetric lattice. Hermitian, eigenvalues = the lattice points
-- (standard basis is the position eigenbasis), distinct for a≠0, bounded spectrum, centered (trace 0).
-- Foundational triple; Cat-1 general matrix facts (CSD reading is docstring only).
/-- info: 'CSD.CV.positionOp_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_isHermitian

/-- info: 'CSD.CV.positionOp_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_mulVec_single

/-- info: 'CSD.CV.latticePoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.latticePoint_injective

/-- info: 'CSD.CV.abs_latticePoint_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.abs_latticePoint_le

/-- info: 'CSD.CV.positionOp_trace_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_trace_eq_zero

-- CV-2/CV-3 (CV/Oscillator): the conjugate (Q,P) pair and the sharp approximate CCR. The N-level
-- truncated oscillator gives a†a = diag(n), aa† = diag(1..N-1,0), hence the truncated CCR
-- [a,a†] = 1 - N·|N-1⟩⟨N-1| (both sides trace 0, per W4). Q=(a+a†)/√2, P=(a-a†)/(i√2) are Hermitian,
-- [Q,P] = i·[a,a†], and [Q,P]·eₙ = i·eₙ exactly for every n ≠ N-1 (exact CCR on the low-energy
-- sector; the W4-forced defect is confined to the top level). Foundational triple; Cat-1.
/-- info: 'CSD.CV.truncated_ccr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.truncated_ccr

/-- info: 'CSD.CV.Q_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.Q_isHermitian

/-- info: 'CSD.CV.P_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.P_isHermitian

/-- info: 'CSD.CV.QP_commutator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.QP_commutator

/-- info: 'CSD.CV.ccr_exact_on_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.ccr_exact_on_bulk

-- CV-4 (CV/OscillatorSpectrum): the energy spectrum. H = a†a + ½ = diag(n+½), Hermitian, with the
-- Fock states as energy eigenstates (H·eₙ = (n+½)·eₙ). The energy Eₙ = n+½ is CUTOFF-INDEPENDENT
-- (oscEnergy has no N), so every finite-energy prediction below the ceiling — zero-point ½, uniform
-- gap 1, each level — is recovered exactly by the truncation. Foundational triple; Cat-1.
/-- info: 'CSD.CV.hamiltonian_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_isHermitian

/-- info: 'CSD.CV.hamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_mulVec_single

/-- info: 'CSD.CV.oscEnergy_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.oscEnergy_gap

/-- info: 'CSD.CV.hamiltonian_groundEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_groundEnergy

-- TH1 (thermodynamics track): canonical typicality -- thermal equilibrium from
-- Fubini-Study volume. The FS first moment E[|psi><psi|] = (1/N) I (a genuine
-- twirl/Schur integral via FS U(N)-invariance, sign-flip + permutation
-- unitaries), and the average reduced state E[Tr_E |psi><psi|] = (1/d_S) I_S
-- (canonical typicality IN EXPECTATION, generalising maxEntangled_marginal_uniform).
-- Exponential concentration/Levy (the typical-state upgrade) is the NAMED
-- residual, not proved; the POLYNOMIAL (Chebyshev) tier is proved (Q24, below).
-- Foundational-triple; Gleason-free.
/-- info: 'CSD.Thermo.fs_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_first_moment

/-- info: 'CSD.Thermo.canonical_typicality_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.canonical_typicality_expectation

-- Q24 (2026-08-21, specs/th1-concentration-scoping.md): the Chebyshev tier.
-- Fubini-Study second moments by pure twirl algebra -- a two-coordinate
-- Hadamard rotation plus the sign-flip and quarter-phase kills give
-- E[x_i^2] = 2*E[x_i x_j] per pair; with the integrated normalisation this
-- pins E[x_i^2] = 2/(N(N+1)), E[x_i x_j] = 1/(N(N+1)) (the Dirichlet values,
-- no simplex integrals). Downstream: exact second moment of any diagonal
-- statistic and polynomial-rate canonical typicality via Chebyshev
-- (meas_ge_le_variance_div_sq). The exponential (Levy/isoperimetry) tier
-- stays the recorded residual (MATHLIB-GAPS.md).
/-- info: 'CSD.Thermo.fs_x_sq_eq_two_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_x_sq_eq_two_cross

/-- info: 'CSD.Thermo.fs_x_sq_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_x_sq_moment

/-- info: 'CSD.Thermo.fs_x_cross_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_x_cross_moment

/-- info: 'CSD.Thermo.fs_linear_sq_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_linear_sq_moment

/-- info: 'CSD.Thermo.fs_chebyshev_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_chebyshev_concentration

-- E3, THE EQUILIBRATION-ARC SPIKE (2026-08-22, Thermo/SectorRestriction.lean,
-- specs/equilibration-arc-plan.md). Run first because it was the item most likely to sink the
-- arc. VERDICT: the naive statement is FALSE, and these theorems record why.
-- projectiveLaw_restrict_saturated -- the POSITIVE half: a fibre-saturated constraint surface
-- (S = pi^-1 B, constraining only the base) pushes forward to the restricted Fubini-Study
-- measure. The honest generalisation of the unrestricted c = 1; it needs saturation because
-- the proof is a product computation.
-- ★★ projectiveLaw_restrict_sector_eq_zero -- the NO-GO: for a proper spectral sector the
-- restriction is the ZERO measure. Not a normalisation failure -- the constraint set is
-- Fubini-Study-NULL, so there is nothing to condition on. A microcanonical statement must
-- therefore either use positive-measure energy windows (whose conditioned law is NOT mu_FS on
-- any P(H_R)) or treat the sector as its own arena (making the mu_L relation a POSIT).
/-- info: 'CSD.Thermo.projectiveLaw_restrict_saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.projectiveLaw_restrict_saturated

/-- info: 'CSD.Thermo.projectiveLaw_restrict_sector_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.projectiveLaw_restrict_sector_eq_zero

/-- info: 'CSD.Thermo.kMuL_sector_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.kMuL_sector_eq_zero

-- E1, COMPLETE (2026-08-22/23, Thermo/ReducedSecondMoment.lean): the reduced state's moments.
-- H-TENSOR discipline: the bipartition is an EXPLICIT argument e : Fin N = Fin dA x Fin dB in
-- every signature, never inferred from a tensor API -- a silently chosen factorisation would
-- be a structural posit doing load-bearing work (a second D1).
-- blockPop = the subsystem populations, a LINEAR statistic in the moment map
-- (blockPop_eq_linear), so Q24's linear moments apply verbatim:
--   fs_blockPop_mean : E[(rho_A)_aa] = d_B/N  (= 1/d_A)
--   fs_blockPop_sq   : E[(rho_A)_aa^2] = (d_B^2 + d_B)/(N(N+1))
-- ★ fs_redOff_cross_vanish -- the novel ingredient: the genuinely four-index expectations
-- vanish, because a coordinate occurring an odd number of times is killed by the sign flip
-- (signFlip_smul_rayDensity_ne is its companion: a flip touching neither index does nothing).
-- Still NOT proved here (and not asserted): the trace-norm form, which needs the matrix-norm
-- API rather than moments, and the identification of these entries with Matrix.traceRight of
-- the projector, which is index bookkeeping in a different vocabulary.
/-- info: 'CSD.Thermo.fs_blockPop_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_blockPop_mean

/-- info: 'CSD.Thermo.fs_blockPop_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_blockPop_sq

/-- info: 'CSD.Thermo.signFlip_smul_rayDensity_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.signFlip_smul_rayDensity_ne

/-- info: 'CSD.Thermo.fs_redOff_cross_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_redOff_cross_vanish

-- ★★ fs_redOff_normSq (2026-08-23): E|(rho_A)_{a a'}|^2 = d_B/(N(N+1)) for a /= a'. Expanding
-- the modulus of the sum into real and imaginary parts, the b = b' terms are the landed cross
-- moment E[x_i x_j] and the b /= b' terms vanish by fs_redOff_cross_vanish.
/-- info: 'CSD.Thermo.fs_redOff_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_redOff_normSq

-- ★★ THE HILBERT-SCHMIDT ASSEMBLY (2026-08-23) -- E1's target, previously the named remainder.
-- fs_hsDeviationNormSq : E||rho_A - I_A/d_A||_2^2 = (d_A + d_B)/(N+1) - 1/d_A, the Lubkin-Page
-- purity average. The d_A diagonal entries contribute fs_hsDeviation_diag_sq (where the mean
-- population is EXACTLY 1/d_A, so the cross term collapses against the constant) and the
-- d_A(d_A - 1) off-diagonal entries contribute fs_hsDeviation_off_sq. The cardinality identity
-- N = d_A d_B is read off the bipartition e itself (card_eq_mul_of_tensorEquiv), not assumed --
-- H-TENSOR again: what the equivalence carries, its arithmetic carries too.
-- fs_hsDeviation_typicality is the usable form: MARKOV on that second moment (not Chebyshev --
-- the functional is quadratic; Chebyshev applies to the linear populations individually).
/-- info: 'CSD.Thermo.fs_hsDeviation_diag_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_hsDeviation_diag_sq

/-- info: 'CSD.Thermo.fs_hsDeviation_off_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_hsDeviation_off_sq

/-- info: 'CSD.Thermo.fs_hsDeviationNormSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_hsDeviationNormSq

/-- info: 'CSD.Thermo.fs_hsDeviation_typicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_hsDeviation_typicality

-- E4 (2026-08-23, Thermo/Equilibration.lean): equilibration as a CONDITIONAL theorem, the arc
-- instantiation of Mathlib/Dynamics/CorrelationDecay.lean on E1's observables.
-- BOTH theorems are conditionals and the antecedent is the content: IF the flow preserves mu_FS
-- AND its correlations for that observable decay with a summable envelope, THEN the time averages
-- converge in L^2 to the Fubini-Study average. NEITHER hypothesis is proved or exhibited for any
-- Sigma -- that is E5's job, and until a witness exists these are conditionals with an
-- unpopulated antecedent. The correlation hypothesis is taken at ONE LAG, the form a physical
-- estimate produces.
-- blockPop_timeAverage_tendsto  : time-averaged populations -> d_B/N = 1/d_A (fs_blockPop_mean).
-- hsDeviationNormSq_timeAverage_tendsto : E4 composed with E1 -- the time-averaged Hilbert-
-- Schmidt deviation -> the Lubkin-Page value (d_A+d_B)/(N+1) - 1/d_A (fs_hsDeviationNormSq).
-- Discrete time (a continuous flow enters by sampling); no Sigma-dynamics is built, so the D1
-- residue is untouched.
/-- info: 'CSD.Thermo.blockPop_timeAverage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.blockPop_timeAverage_tendsto

/-- info: 'CSD.Thermo.hsDeviationNormSq_timeAverage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.hsDeviationNormSq_timeAverage_tendsto

-- E5's sharpness check (2026-08-23, Thermo/Equilibration.lean): E4's antecedent is EMPTY for
-- periodic Sigma-flows whenever the subsystem is nontrivial (dA >= 2).  Q24 arithmetic against
-- the periodic no-go: a periodic map forces <x^2> = <x>^2, but fs_blockPop_sq and
-- fs_blockPop_mean give (d_B^2+d_B)/(N(N+1)) and d_B/N, which agree exactly when N = d_B, i.e.
-- d_A = 1 -- no subsystem at all.  A unitary on CP^{N-1} generates a relatively compact group, so
-- its correlations are almost periodic and cannot decay either; the finite-order case proved here
-- is the part of that available without a recurrence argument (the general version is argued in
-- the module docstring and in equilibration-arc-plan.md E5, and is NOT proved).
/-- info: 'CSD.Thermo.not_hasCorrelationDecay_blockPop_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.not_hasCorrelationDecay_blockPop_of_periodic

-- E2 (2026-08-23, Thermo/EnergyWindow.lean), RE-SCOPED BY E3's VERDICT. The original "E1 on
-- the unit sphere of a spectral sector" is refuted (an exact sector is Fubini-Study-NULL,
-- SectorRestriction.lean), so the surviving route is a POSITIVE-MEASURE ENERGY WINDOW.
-- For a diagonal Hamiltonian the energy expectation is the LINEAR statistic sum lam_k x_k, so
-- Q24's moments and Chebyshev bound control the window directly.
-- ★★ energyWindow_ne_zero -- the window provably carries weight once it is wider than the
-- fluctuation scale (Var/eps^2 < 1). This is exactly the hypothesis E3 made load-bearing, and
-- it is QUANTITATIVE rather than assumed.
-- ★★ micro_redOff_cross_vanish + map_signFlip_microMeasure -- THE STRUCTURAL FINDING:
-- conditioning breaks U(N) invariance, but NOT uniformly. A sign flip fixes every moment
-- coordinate, hence fixes the energy, hence preserves the window -- so the sign-flip half of
-- the twirl toolkit survives conditioning and the four-index vanishing still holds. The
-- permutations and the Hadamard rotation move coordinates and change the energy, so the moment
-- VALUES do not transfer; conditional moments are a microcanonical density-of-states problem
-- and are NOT attempted.
/-- info: 'CSD.Thermo.energyWindow_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.energyWindow_ne_zero

/-- info: 'CSD.Thermo.map_signFlip_microMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.map_signFlip_microMeasure

/-- info: 'CSD.Thermo.micro_redOff_cross_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.micro_redOff_cross_vanish

-- TH2: the second law as coarse-grained entropy monotonicity. Pinching
-- (dephasing to the pointer-basis diagonal) never decreases the von Neumann
-- entropy -- S(rho) <= S(pinch rho) -- via Klein's inequality against the
-- diagonal and the cross-term identity Tr(rho log(pinch rho)) = -S(pinch rho).
-- The fine-grained unitary step conserves entropy (vonNeumannEntropy_conj_unitary);
-- the coarse-graining step produces it: the H-theorem form of the second law.
-- Honest scope: strict-positivity (Klein support) hypothesis; a specific
-- coarse-graining, not a universal second law; the pure-state instance is
-- LF6-B.3. Foundational-triple.
/-- info: 'CSD.Thermo.vonNeumannEntropy_le_pinching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.vonNeumannEntropy_le_pinching

/-- info: 'CSD.Thermo.entropy_reversible_then_coarsegrain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.entropy_reversible_then_coarsegrain

/-- info: 'CSD.Thermo.entropy_production_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.entropy_production_nonneg

-- TH3: temperature, free energy, and the Gibbs variational principle. The Gibbs
-- state ρ_β = exp(-βH)/Z (built via the Hermitian functional calculus) minimises
-- the free energy F(ρ) = Re Tr(ρH) - T·S(ρ) among all density operators, with
-- minimum F(ρ_β) = -T log Z. Proof: β(F(ρ) - F(ρ_β)) = D(ρ ‖ ρ_β) ≥ 0 by Klein,
-- using the crux log(ρ_β) = -βH - (log Z)·1 (cfc_eq_conj_diagonal on the
-- H-eigenbasis). Foundational-triple; the variational characterisation of
-- thermal equilibrium. Requires [Nonempty n].
/-- info: 'CSD.Thermo.cfc_log_gibbsState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.cfc_log_gibbsState

/-- info: 'CSD.Thermo.gibbsState_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbsState_posDef

/-- info: 'CSD.Thermo.gibbsState_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbsState_trace

/-- info: 'CSD.Thermo.gibbs_free_energy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbs_free_energy_eq

/-- info: 'CSD.Thermo.gibbs_free_energy_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbs_free_energy_min

-- TH4: Landauer's principle (Reeb-Wolf bound). A system coupled by a global
-- unitary to a bath in the Gibbs state obeys β·ΔQ ≥ S(ρ_S) − S(ρ_S') -- the
-- entropy removed from the system is at most β times the heat dumped into the
-- bath. Chain: entropy conservation (conj_unitary + kronecker) + subadditivity
-- ⇒ S(ρ_S)−S(ρ_S') ≤ S(ρ_B')−S(τ_B); the bath Clausius inequality
-- (relEntropy_nonneg + the TH3 Gibbs log identity) bounds that by β·ΔQ. One-bit
-- corollary: erasing a maximally-mixed bit to a definite state costs
-- ΔQ ≥ T log 2 = kT ln 2. Foundational-triple.
/-- info: 'CSD.Thermo.bath_clausius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.bath_clausius

/-- info: 'CSD.Thermo.landauer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.landauer_bound

/-- info: 'CSD.Thermo.landauer_one_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.landauer_one_bit

-- OscillatorBorn (EFT Stage 0: the truncated CV mode as a record-layer measurement, 2026-07-25). The
-- oscillator Hamiltonian is diagonal → number basis = standard basis → the mode's number/energy
-- measurement IS the record-layer measurement. numberMeasurement_prob (= ‖⟨n|ψ⟩‖²),
-- numberMeasurement_frequency (Born = LLN over the unknown microstate, inherited), numberBornProb_embed
-- (cutoff-independence: raising the truncation N→M≥N leaves each level's Born prob unchanged). The
-- gate step toward the EFT direction (QM→CV→EFT); single mode at finite cutoff, continuum not taken.
/-- info: 'CSD.CV.numberMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberMeasurement_prob

/-- info: 'CSD.CV.numberMeasurement_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberMeasurement_frequency

/-- info: 'CSD.CV.numberBornProb_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberBornProb_embed

-- FieldModes (EFT Stage 1: a free scalar field at a cutoff as a product of modes, 2026-07-25). Field
-- Hilbert space = tensor product of K truncated modes, indexed by occupation configs Fin K → Fin N.
-- fieldHamiltonian_mulVec_single (free field = sum of oscillators, diagonal, eigenvalue ∑ oscEnergy),
-- fieldEnergy_cutoff_independent, sum_fieldBornProb_unit (config Born distribution), norm_sq_tprodState
-- (product state ‖⊗ψₖ‖²=∏‖ψₖ‖² — composite/tensor structure), and modeMarginal_tprod_unit (MODE-WISE
-- BORN: the marginal of a product state = the single-mode Born weight ‖ψ_{k₀} n‖²). Free field, cutoff.
/-- info: 'CSD.CV.fieldHamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.fieldHamiltonian_mulVec_single

/-- info: 'CSD.CV.norm_sq_tprodState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_sq_tprodState

/-- info: 'CSD.CV.modeMarginal_tprod_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.modeMarginal_tprod_unit

-- Dispersion (EFT Stage 2a: relativistic dispersion ω(m,p) = √(p²+m²), 2026-07-27). The mode
-- frequencies that make the mode sum a RELATIVISTIC field: omega_sq_sub_sq is the MASS SHELL
-- ω²−p²=m² (the Lorentz-invariant content, and why m is called the mass); abs_le_omega (|p| ≤ ω —
-- excitations do not outrun the light cone); abs_mass_le_omega + omega_zero (the MASS GAP |m| ≤ ω,
-- attained at rest); omega_massless (ω = |p| exactly, the light cone); omega_le_newtonian (ω ≤ m +
-- p²/2m, the non-relativistic limit as a clean INEQUALITY, no asymptotics); omega_mono. The field:
-- relFieldHamiltonian_mulVec_single + _isHermitian (still DIAGONAL in the configuration basis, so
-- the OscillatorBorn record-layer account carries over verbatim — only the eigenvalues change),
-- relFieldEnergy_quantum (THE HEADLINE: one quantum in mode k₀ costs exactly ω(m, p k₀), so the
-- excitations ARE relativistic particles of mass m — the dispersion is about the particle content,
-- not a parameter choice), relFieldEnergy_vacuum (zero-point ½∑ω), relFieldEnergy_cutoff_independent.
/-- info: 'CSD.CV.omega_sq_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_sq_sub_sq

/-- info: 'CSD.CV.abs_le_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.abs_le_omega

/-- info: 'CSD.CV.abs_mass_le_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.abs_mass_le_omega

/-- info: 'CSD.CV.omega_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_zero

/-- info: 'CSD.CV.omega_massless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_massless

/-- info: 'CSD.CV.omega_le_newtonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_le_newtonian

/-- info: 'CSD.CV.omega_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_mono

/-- info: 'CSD.CV.relFieldHamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldHamiltonian_mulVec_single

/-- info: 'CSD.CV.relFieldHamiltonian_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldHamiltonian_isHermitian

/-- info: 'CSD.CV.relFieldEnergy_quantum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_quantum

/-- info: 'CSD.CV.relFieldEnergy_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_vacuum

/-- info: 'CSD.CV.relFieldEnergy_cutoff_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_cutoff_independent

-- ModeLocality (EFT Stage 2b: commuting algebras of disjoint mode sets, 2026-07-27). The HAAG-
-- KASTLER kinematic locality axiom at the finite cutoff: commute_of_disjointSupport -- operators
-- supported on DISJOINT mode sets commute (A*B = B*A), so observables of disjoint regions are
-- jointly measurable and the record layer can assign them outcomes simultaneously. Proof = the
-- uniqueness of the intermediate configuration (one surviving term per product, equal in pairs by
-- the support conditions). NOT VACUOUS: modeOp_supportedOn exhibits SupportedOn {k₀} for every
-- single-mode matrix, and commute_modeOp is the concrete instance at distinct modes.
-- HONEST SCOPE (see the file's "does NOT claim" section): this is SUBSYSTEM locality, spatial only
-- under the position-space reading of the modes (CV/Position.lean). Continuum microcausality
-- [φ(x),φ(y)]=0 at spacelike separation is NOT proved and does NOT hold exactly at a finite cutoff;
-- it needs the continuum limit, deliberately deferred (CV/ApproxCCR.no_exact_finite_ccr).
/-- info: 'CSD.CV.commute_of_disjointSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_of_disjointSupport

/-- info: 'CSD.CV.modeOp_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.modeOp_supportedOn

/-- info: 'CSD.CV.commute_modeOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_modeOp

-- CV-5 free-field Floquet + CV-6 dynamical locality (2026-08-07). CV-5: the free field's
-- stroboscopic step is an explicit diagonal-phase unitary, and freeFieldU_eq_exp proves it
-- IS the matrix exponential exp(-(i tau) . H_field) -- "generated by the field Hamiltonian"
-- is a theorem, not a reading. CV-6: Heisenberg conjugation by the (mode-additive) free
-- evolution preserves SupportedOn, so the Haag-Kastler kinematic axiom is DYNAMICALLY
-- stable: disjointly supported observables still commute after ANY number of periods.
-- HONEST SCOPE: free (mode-diagonal) drive only; interacting-drive spreading is
-- BOUNDED by CV-8 (SupportSpreading: coupling-graph light cone + K=N=2 witness) and
-- PRICED by CV-9 (InteractionPrice: linear in the coupling).
/-- info: 'CSD.CV.freeFieldU_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.freeFieldU_eq_exp

/-- info: 'CSD.CV.heisenberg_freeFieldU_pow_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.heisenberg_freeFieldU_pow_supportedOn

/-- info: 'CSD.CV.commute_heisenberg_freeFieldU_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_heisenberg_freeFieldU_pow

-- CV-7 interacting drive + CV-8 local algebras & the light cone (2026-08-07). CV-7: a
-- DIAGONAL (density-density) interaction commutes with H_free, so the interacting step is
-- EXACT (one phaseDiagU, no Trotter) and interactingU_eq_exp proves it IS
-- exp(-(i tau).(H_field + lam.V)). CV-8: SupportedOn S is a unital *-subalgebra
-- (SupportedOn.mul = the closure keystone); conjugation by a T-supported unitary spreads
-- at most onto S UNION T, disjoint couplings act TRIVIALLY, and the light cone: after n
-- interacting periods support sits in the coupling graph's n-ball (one edge per period);
-- observables outside each other's light cones still commute. NON-VACUOUS:
-- spreadKick_not_supportedOn -- at K=N=2 the pair kick moves modeOp 0 off the single-mode
-- algebra (evolved entries 1 vs -1), so the cone bounds a real phenomenon.
/-- info: 'CSD.CV.interactingU_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.interactingU_eq_exp

/-- info: 'CSD.CV.SupportedOn.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.SupportedOn.mul

/-- info: 'CSD.CV.heisenberg_graphInteractingU_pow_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.heisenberg_graphInteractingU_pow_supportedOn

/-- info: 'CSD.CV.commute_heisenberg_graphInteractingU_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_heisenberg_graphInteractingU_pow

/-- info: 'CSD.CV.spreadKick_not_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.spreadKick_not_supportedOn

-- CV-9 small-coupling pricing (2026-08-07). The Duhamel engine (generalized to any finite
-- index) prices ANY Hermitian perturbation -- diagonal or hopping, no closed-form step
-- needed: ||exp(-(i tau).(H+lam V)) - freeFieldU|| <= |tau||lam| ||V||; the diagonal drive
-- specializes to |tau|(|lam| C) via l2_opNorm_diagonal_le; Heisenberg stability (C*-identity
-- ||U||=1 + submultiplicativity) then puts the interacting Heisenberg observable of an
-- S-supported A within 2|tau||lam|C||A|| of an S-SUPPORTED operator (the free-evolved one,
-- CV-6): LOCALITY VIOLATION IS PRICED LINEARLY IN THE COUPLING -- the CV rhyme of the
-- record half-life bound mu <= n.eps. Bounds are inequalities; attainment not claimed.
/-- info: 'CSD.CV.freeField_perturbed_exp_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.freeField_perturbed_exp_dist_le

/-- info: 'CSD.CV.interactingU_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.interactingU_dist_le

/-- info: 'CSD.CV.heisenberg_interactingU_near_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.heisenberg_interactingU_near_supported

-- CV-10 finite-cutoff power counting (2026-08-07). The honest EFT kernel: grade an
-- interaction by operator content and track the cutoff scaling of the CV-9 price.
-- Norm-growth bricks WITHOUT spectral asymptotics: ||a||^2 = ||a^dag a|| = ||N-hat|| <= N
-- (C*-identity + the diagonal bound), so ||Q|| <= sqrt(2N); embedding into the field is
-- norm-nonincreasing (l2_opNorm_modeOp_le: modeOp is block-diagonal over spectators).
-- The grade-m interaction Q_k^m then has price <= |tau||lam| sqrt(2N)^m (exponent = the
-- grade), and with the coupling renormalized as lam0/sqrt(2N)^m the price is <= |tau||lam0|
-- UNIFORM IN THE CUTOFF: relevant/irrelevant as a theorem about price-bound scaling.
-- HONEST SCOPE: upper bounds on the certified price only -- no lower bounds, no divergence
-- claim, no RG, nothing continuum (ApproxCCR.no_exact_finite_ccr stands).
/-- info: 'CSD.CV.Q_l2_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.Q_l2_opNorm_le

/-- info: 'CSD.CV.l2_opNorm_modeOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.l2_opNorm_modeOp_le

/-- info: 'CSD.CV.gradedInteraction_price_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.gradedInteraction_price_le

/-- info: 'CSD.CV.gradedInteraction_renormalized_price_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.gradedInteraction_renormalized_price_le

-- SH diagnostics meet Stage 3 (2026-08-08, CV/ChaosBounds.lean). The OTOC LIGHT-CONE GATE:
-- for A supported on R and a static probe B on T, the out-of-time-order commutator is
-- EXACTLY zero at every period where the coupling graph's n-ball of R is still disjoint
-- from T -- scrambling provably cannot begin before A's cone reaches the probe (CV-8
-- re-expressed as the standard diagnostic; exact but one-directional, no growth claim).
-- The ECHO PRICE: Loschmidt decay between free and interacting drives <= 2n|tau||lam|C --
-- the third linear-pricing rhyme (records mu <= n.eps; locality 2|tau||lam|C||A||; echo).
-- Free-field SFF = explicit exponential sum (the integrable baseline).
/-- info: 'CSD.CV.otoc_graphInteractingU_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.otoc_graphInteractingU_eq_zero

/-- info: 'CSD.CV.one_sub_loschmidtEcho_interacting_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.one_sub_loschmidtEcho_interacting_le

/-- info: 'CSD.CV.sff_freeFieldU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.sff_freeFieldU

-- CV-11 non-diagonal light cone (2026-08-09, CV/LocalAlgebraClosed.lean). The local algebra
-- is packaged (Submodule/Subalgebra) and TOPOLOGICALLY CLOSED (finite-dim subspace), so
-- exp of a T-supported matrix is T-supported (partial sums in the algebra + closedness):
-- SupportedOn.exp. KickData.ofGenerator then admits ANY skew-Hermitian edge-supported
-- generator -- hopping terms included -- as a local kick, and the kicked drive's n-period
-- Heisenberg support is confined to the kickFold ball (in-period chaining recorded
-- honestly by the fold); observables with disjoint fold-balls still commute. HONEST
-- SCOPE: kicked drives; the full-exponential cone is Lieb-Robinson, the PROMOTED Stage-5
-- headline (eft-stage4-plan.md horizon note), gated on CV-11 + CV-12.
/-- info: 'CSD.CV.SupportedOn.exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.SupportedOn.exp

/-- info: 'CSD.CV.heisenberg_kickedStep_pow_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.heisenberg_kickedStep_pow_supportedOn

/-- info: 'CSD.CV.commute_heisenberg_kickedStep_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_heisenberg_kickedStep_pow

-- CV-13 the finite free propagator (2026-08-09, CV/Propagator.lean). THE CHAIN'S FIRST
-- COMPUTED CORRELATION FUNCTION: <vac| Q_k(n) Q_l |vac> = (1/2) e^{-i n tau} delta_{kl}
-- -- diagonal in the mode index (free modes do not mix) and oscillating at the excitation
-- energy, so the dispersion appears as an OBSERVABLE TIME DEPENDENCE, not a spectrum
-- label. Route: one-quantum intermediate state (the only survivor from the vacuum),
-- phaseDiagU_pow for the n-period drive, the CV-6 Heisenberg entry formula for the phase
-- difference, and fieldEnergy_excCfg_sub = 1 for the spacing. norm_freeTwoPoint: modulus
-- period-independent (the free propagator does not decay). The interacting correction is
-- PRICED (twoPoint_interacting_dist_le, via CV-9's Duhamel bound + CV-12's unitary
-- telescoping + the entrywise bound). HONEST SCOPE: quadrature two-point function at a
-- finite cutoff, not a general Wightman function; the relativistic reading is the same
-- computation with relFieldHamiltonian (spacing 1 -> omega(m,p_l)), recorded residue.
/-- info: 'CSD.CV.freeTwoPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.freeTwoPoint_eq

/-- info: 'CSD.CV.norm_freeTwoPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_freeTwoPoint

/-- info: 'CSD.CV.twoPoint_interacting_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.twoPoint_interacting_dist_le

-- CV-14 boost covariance of the mass shell (2026-08-09, CV/Boost.lean). The 1+1D boost
-- at rapidity chi is a genuine one-parameter GROUP (boostE_add/boostP_add: rapidities add,
-- via the cosh/sinh addition formulas), it preserves E^2 - p^2 (cosh^2 - sinh^2 = 1), and
-- therefore the boosted dispersion pair satisfies the SAME mass shell with the SAME mass:
-- boost_mass_shell. Sharp form boost_omega: the boosted energy IS omega at the boosted
-- momentum -- the dispersion relation is boost-covariant on the nose. boost_forward
-- (|p| <= omega + |sinh| <= cosh) keeps the forward shell: no physical mode is boosted to
-- negative energy. HONEST SCOPE: ONE-PARTICLE KINEMATIC covariance at the dispersion
-- level; NO boost action on the mode lattice is claimed (a finite mode lattice is not
-- boost-invariant -- standard cutoff honesty, stated in the module).
/-- info: 'CSD.CV.boost_mass_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.boost_mass_shell

/-- info: 'CSD.CV.boost_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.boost_omega

/-- info: 'CSD.CV.boostE_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.boostE_add

-- CV-15 the renormalization-trivial class (2026-08-09, CV/CutoffStability.lean). The
-- COMPLEMENT of CV-10: interactions defined by OCCUPATION NUMBERS through a cutoff-uniform
-- kernel g need no renormalization at all. embedCfg carries a cutoff-N configuration into
-- cutoff M >= N; both the free energy and the interaction are cutoff-independent there, so
-- interactingU_cutoff_independent: the two drives have EQUAL matrix elements between
-- corresponding configurations at the SAME coupling (diagonal equal, off-diagonal zero on
-- both sides) -- raising the cutoff does not move predictions on configurations that
-- already existed. And natDensityCoupling_price_uniform: the CV-9 price is |tau||lam|C
-- with C independent of N and K, versus CV-10's sqrt(2N)^m growth for quadrature-graded
-- interactions. RELEVANT/IRRELEVANT IS NOW A THEOREM ON BOTH SIDES. HONEST SCOPE: cutoff
-- STABILITY of this class on the shared low-energy sector, not a renormalization group;
-- matching for interactions that need it is CV-16 (gated); no continuum.
/-- info: 'CSD.CV.interactingU_cutoff_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.interactingU_cutoff_independent

/-- info: 'CSD.CV.natDensityCoupling_price_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.natDensityCoupling_price_uniform

-- CV-16 decimation between cutoffs (2026-08-09, CV/Decimation.lean). The GATED RG row,
-- resolved by running its feasibility pass first (the CV-10 discipline) -- and the pass
-- found the row's PLANNED statement unattainable. Positive half: compressCfg_interactingU
-- -- decimating the cutoff-M drive of an occupation-defined coupling gives EXACTLY the
-- cutoff-N drive of the same coupling, so for that class the RG map is the identity on
-- couplings (CV-15 in decimation language, matching as a matrix identity). NO-GO half:
-- compress_hopU_not_unitary / exists_unitary_compress_not_unitary -- a unitary at cutoff 3
-- decimates to diag(1,0) at cutoff 2, NOT unitary. The failure is LOSS OF NORM, not a
-- wrong parameter value, so no coupling redefinition repairs it: the effective low-cutoff
-- dynamics of a support-spreading drive is NECESSARILY NON-UNITARY. Consequence recorded
-- in the module: an honest RG statement must be about CHANNELS AND OBSERVABLES WITH AN
-- ERROR BUDGET (CP map + correlator agreement up to a bound), needing a leakage estimate
-- the corpus does not have -- research-grade, deferred, not attempted. NO flow, NO fixed
-- points, NO beta function claimed.
/-- info: 'CSD.CV.compressCfg_interactingU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.compressCfg_interactingU

/-- info: 'CSD.CV.exists_unitary_compress_not_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.exists_unitary_compress_not_unitary

-- CV-17/CV-18 the linear Lieb-Robinson bound (2026-08-09, CV/LiebRobinson.lean). Stage 5's
-- first two bricks, for a skew-Hermitian generator S = -iH so the propagators are unitary.
-- CV-17: hasDerivAt_heisenbergFlow -- the Heisenberg flow solves d/dt A(t) = [A(t), S].
-- The split (commutator_deriv_eq): writing S = S_X + T with S_X commuting with the probe B,
-- f(t) = [A(t), B] obeys f' = [f, S_X] + [[A(t), T], B]; the S_X term is a pure conjugation
-- carrying no growth, and the Jacobi cancellation A[S_X,B] - [S_X,B]A = 0 is what puts it
-- there. CV-18: conjugating that term away and applying the mean-value inequality (the
-- DuhamelBound pattern) gives ||[A(t),B]|| <= 4|t| ||T|| ||A|| ||B|| -- INFORMATION CANNOT
-- LEAVE A REGION INSTANTANEOUSLY, at a rate set by the coupling ACROSS THE CUT alone, not
-- by the total energy. On the field, CV-8's commute_of_disjointSupport supplies [A,B] = 0.
-- HONEST SCOPE: this is the LINEAR bound. The exponential form e^{-mu(d - v|t|)}, with a
-- velocity and a distance, needs the iteration over chains and the path count = CV-19,
-- gated research (eft-stage5-plan.md). Nothing here claims a velocity.
/-- info: 'CSD.CV.hasDerivAt_heisenbergFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.hasDerivAt_heisenbergFlow

/-- info: 'CSD.CV.commutator_deriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commutator_deriv_eq

/-- info: 'CSD.CV.norm_commutator_heisenbergFlow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_heisenbergFlow_le

/-- info: 'CSD.CV.norm_commutator_field_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_field_le

-- CV-19 PARTIAL: the Gronwall (exponential-in-time) Lieb-Robinson bound (2026-08-09,
-- CV/LiebRobinson.lean). The gated row's feasibility pass found a concrete route to a
-- strictly stronger result than CV-18, so that much was taken: the Jacobi re-split
-- (leak_jacobi) turns the leakage term into (current commutator).T plus a source
-- proportional to [T,B], which is exactly Gronwall shape, and Mathlib's
-- norm_le_gronwallBound_of_norm_deriv_right_le closes it:
-- ||[A(t),B]|| <= gronwallBound 0 (2||T||) (2||A|| ||[T,B]||) t, i.e.
-- (||A|| ||[T,B]||/||T||)(e^{2||T||t} - 1). The prefactor ||[T,B]|| is the part of the
-- coupling that REACHES the probe, so a coupling commuting with B contributes exactly
-- nothing at any time (commutator_eq_zero_of_coupling_commutes) -- the seed of a light
-- cone. NOT PROVED, and the module says so: the spatial form e^{-mu(d - v|t|)}. No
-- velocity is defined, no lattice distance appears, and the chain iteration with its
-- path count is not attempted. That is the remaining CV-19 frontier.
/-- info: 'CSD.CV.norm_commutator_gronwall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_gronwall_le

/-- info: 'CSD.CV.commutator_eq_zero_of_coupling_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commutator_eq_zero_of_coupling_commutes

/-- info: 'CSD.CV.norm_conj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_conj_eq

-- CV-19 second pass: the combinatorial half of the SPATIAL cone (2026-08-09,
-- CV/LiebRobinson.lean). The Heisenberg flow is the exponential generating series of the
-- nested commutators ad_S^k(A). For a generator that is a sum of edge-supported terms,
-- adIter_supportedOn_graphBall shows those iterates stay inside the coupling graph's
-- k-ball: a term whose edge MISSES the current region commutes with the observable and
-- drops out (commute_of_disjointSupport), so k steps reach at most k edges. Hence
-- commutator_adIter_eq_zero: ad_S^k(A) commutes with B EXACTLY while the k-ball has not
-- reached B's region -- which is what makes a Lieb-Robinson series start at the graph
-- distance rather than at zero. STILL NOT PROVED, and the module says so: the spatial
-- form itself. It needs the analytic half (flow = sum_k (-t)^k/k! ad^k(A) plus a tail
-- estimate); no velocity is defined and no such series is claimed here.
/-- info: 'CSD.CV.adIter_supportedOn_graphBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.adIter_supportedOn_graphBall

/-- info: 'CSD.CV.commutator_adIter_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commutator_adIter_eq_zero

-- CV-19 COMPLETED: the SPATIAL Lieb-Robinson bound (2026-08-09, CV/LiebRobinson.lean).
-- The two halves assembled. Analytic half: flowRemainder is the flow minus the first d
-- terms of its adjoint series, hasDerivAt_flowRemainder shows d/dt R_{k+1} = -ad_S(R_k)
-- (the Taylor terms differentiate into one another and cancel), and norm_flowRemainder_le
-- bounds ||R_k(t)|| <= (2||S|| |t|)^k ||A|| by induction with the mean-value inequality.
-- Combinatorial half: every discarded term commutes with B exactly, since k nested
-- commutators reach at most k graph edges. Hence norm_commutator_spatial_le:
-- ||[A(t),B]|| <= 2||A|| ||B|| (2||S|| |t|)^d for every d whose ball has not reached B.
-- For 2||S|| |t| < 1 this DECAYS GEOMETRICALLY IN THE GRAPH DISTANCE: propagation speed is
-- bounded by the coupling strength. HONEST SCOPE: the geometric form, not the textbook
-- factorial form (2||S|| |t|)^d/d! -- recovering that means replacing the mean-value step
-- by an integral estimate, recorded as the remaining strengthening. No velocity constant
-- is extracted or claimed optimal.
/-- info: 'CSD.CV.norm_flowRemainder_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_flowRemainder_le

/-- info: 'CSD.CV.hasDerivAt_flowRemainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.hasDerivAt_flowRemainder

/-- info: 'CSD.CV.norm_commutator_spatial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_spatial_le

-- The factorial strengthening (2026-08-09, CV/LiebRobinson.lean): the recorded remaining
-- delta on CV-19, taken. norm_flowRemainder_le_factorial replaces the mean-value step by an
-- integral estimate (FTC on the remainder + norm_integral_le_integral_norm +
-- integral_mono_on + integral_pow), sharpening ||R_k(t)|| to (2||S||t)^k/k! ||A||. Hence
-- norm_commutator_spatial_factorial_le: ||[A(t),B]|| <= 2||A|| ||B|| (2||S||t)^d/d! for
-- every d whose ball has not reached B. The factorial is what makes the bound decay in the
-- graph distance at EVERY time rather than only below 2||S||t = 1 -- the textbook
-- Lieb-Robinson shape. No velocity constant is extracted or claimed optimal.
/-- info: 'CSD.CV.norm_flowRemainder_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_flowRemainder_le_factorial

-- CV-20 (Stage 6 opener, 2026-08-13): the velocity, made explicit. The Stage-5
-- non-claim discharged: pow_pow_le_exp_mul_factorial (d^d <= e^d d!, one term of
-- the exponential series) + pow_div_factorial_le_exp_neg give
-- norm_commutator_velocity_le -- outside the cone v*t <= d with v = 2e^2 ||S||,
-- ||[A(t),B]|| <= 2||A|| ||B|| e^{-d}: exponential decay in the graph distance
-- with the velocity constant explicit. Optimality of the constant NOT claimed.
/-- info: 'CSD.CV.pow_div_factorial_le_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.pow_div_factorial_le_exp_neg

/-- info: 'CSD.CV.norm_commutator_velocity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_velocity_le

-- CV-21 (Stage 6, 2026-08-13): vacuum clustering -- the statics companion to
-- the cone. diag_entry_mul_of_disjointSupport: (A*B)(v,v) = A(v,v)*B(v,v) for
-- disjointly supported A, B at ANY configuration (unique-intermediate argument,
-- the commute_of_disjointSupport engine); vacuum_clustering instantiates at
-- vacCfg: <vac|AB|vac> = <vac|A|vac><vac|B|vac> -- no vacuum correlations
-- across disjoint mode sets at the cutoff.
/-- info: 'CSD.CV.diag_entry_mul_of_disjointSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.diag_entry_mul_of_disjointSupport

/-- info: 'CSD.CV.vacuum_clustering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.vacuum_clustering

-- CV-22 (Stage 6 close, 2026-08-13): the four-point Wick table, pattern-
-- resolved (the gated feasibility pass PASSED at the sanctioned scope).
-- eqFourPoint_same: <vac|Q_k^4|vac> = 3/4 (three pairings; needs 2 < N --
-- the two-quantum level enters); the three two-pair arrangements = 1/4
-- (one surviving pairing, via clustering + disjoint-mode commutation);
-- a mode appearing once kills the expectation (all four positions).
-- Exactly Wick's values Sum_pairings Prod G with G = (1/2)delta.
/-- info: 'CSD.CV.modeOpQ_sq_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.modeOpQ_sq_vac

/-- info: 'CSD.CV.eqFourPoint_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_same

/-- info: 'CSD.CV.eqFourPoint_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_pair

/-- info: 'CSD.CV.eqFourPoint_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_alt

/-- info: 'CSD.CV.eqFourPoint_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_outer

/-- info: 'CSD.CV.eqFourPoint_single₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_single₁

/-- info: 'CSD.CV.eqFourPoint_single₄' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.eqFourPoint_single₄

/-- info: 'CSD.CV.norm_commutator_spatial_factorial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_commutator_spatial_factorial_le

-- H7 level 1 (CV/CarrierPersistence.lean, 2026-08-12): carrier persistence
-- priced by locality — exact in the cone-complement (an equality, not a
-- bound), einselection of the configuration basis under the whole diagonal
-- family, the telescoped Duhamel bound, and the window headline (zero until
-- the cone arrives, the derived rate after).
/-- info: 'CSD.CV.heisenberg_perturbed_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.heisenberg_perturbed_pow_eq

/-- info: 'CSD.CV.heisenberg_diagonal_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.heisenberg_diagonal_pow_eq

/-- info: 'CSD.CV.heisenberg_perturbed_pow_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.heisenberg_perturbed_pow_dist_le

/-- info: 'CSD.CV.carrier_persistence_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.carrier_persistence_window

-- Q3 (2026-08-12): the diagnostics beyond the light-cone gate — the linear
-- OTOC growth cap (slow scrambling) and the free field's exact SFF revival
-- at τ = 2π (the integrable baseline).
/-- info: 'CSD.CV.otoc_interactingU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.otoc_interactingU_le

/-- info: 'CSD.CV.freeField_phase_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.freeField_phase_two_pi

/-- info: 'CSD.CV.sff_freeFieldU_revival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.sff_freeFieldU_revival

-- CV-24 (2026-08-17, CV/ThermalPropagator.lean, Stage 7): the thermal tier at the cutoff --
-- the first join of the Thermo and CV verticals, and the corpus's FIRST KMS statement.
-- thermalFieldState is THE TH3 gibbsState instantiated on fieldHamiltonian (not a separately
-- posited Boltzmann matrix); the diagonal Hamiltonian gives the closed form via
-- cfc_eq_conj_diagonal at U = 1, with the configuration-basis partition function reconciled
-- to TH3's eigenvalue form through the trace normalisation. The partition function
-- factorises over modes (Z = z^K), the thermal mode marginal reduces field expectations to
-- single-mode Gibbs averages, and thermal_kms is EXACT: at finite dimension with diagonal H,
-- complex-time evolution is entrywise and the KMS identity is the Boltzmann weight
-- transport w_c = w_d e^{-beta(Ec-Ed)} plus an index shuffle -- no analytic continuation,
-- no approximation. The thermal propagator: modes do not mix (offdiag = 0), the diagonal is
-- a single-mode Boltzmann average of one up-step and one down-step with the TRUNCATION EDGE
-- EXPLICIT (the top level has no up-step -- the eqFourPoint_same honesty at every level),
-- and the beta -> infinity limit recovers freeTwoPoint exactly (zero-point energies cancel,
-- geometric weights, ground level dominates; finite sums, no dominated convergence).
-- Scope: free (mode-diagonal) drive, matching freeTwoPoint; no continuum limit
-- (no_exact_finite_ccr stands); no thermodynamic limit in K. Proof-engineering notes: the
-- Pi.div module-system defeq wall (Complex.mulAux unexposed) bridged via Pi.div_apply; the
-- unannotated-binder nat-default trap on oscEnergy sums; Fin-literal if_pos conditions
-- stated via show-ascriptions (the B5-geom idiom family).
/-- info: 'CSD.CV.thermalFieldState_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermalFieldState_eq

/-- info: 'CSD.CV.fieldPartition_eq_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.fieldPartition_eq_pow

/-- info: 'CSD.CV.thermalExpect_modeOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermalExpect_modeOp

/-- info: 'CSD.CV.thermal_kms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermal_kms

/-- info: 'CSD.CV.thermalTwoPoint_offdiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermalTwoPoint_offdiag

/-- info: 'CSD.CV.thermalTwoPoint_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermalTwoPoint_diag

/-- info: 'CSD.CV.thermalTwoPoint_tendsto_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.thermalTwoPoint_tendsto_vacuum

-- CV-23a (2026-08-17, CV/Propagator.lean, Stage 7): Wick's four-point theorem PACKAGED --
-- the eqFourPoint coincidence table assembled into the single pairing-sum formula
-- 1/4(d_kl d_mp + d_km d_lp + d_kp d_lm), one statement over every mode pattern, per the
-- CONVENTIONS 8.3b discipline (the existing table strengthened in place, no new capstone
-- file). The 2 < N hypothesis is load-bearing exactly where the table says: at N = 2 the
-- all-equal pattern is 1/4 not the Gaussian 3/4. CV-23b (time-separated four-point) and
-- CV-23c (2n-point, gated on the six-point pass) remain queued.
/-- info: 'CSD.CV.eqFourPoint_wick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.eqFourPoint_wick

-- CV-23b (2026-08-17, CV\Wick.lean, Stage 7): Wick's four-point theorem at DISTINCT times --
-- the eqFourPoint_wick pairing sum with the phases on. twoPointKernel n m = (1/2)e^{-i n tau}
-- e^{+i m tau} is the stroboscopic kernel, kept in two-factor form so Nat-subtraction never
-- appears; timeTwoPoint_eq is the two-time propagator delta_kl * K(n,m). The four-point
-- coincidence table transfers verbatim (singleton modes die; the two-pair patterns give the
-- kernel product of the paired TIMES -- the arrangement now carries content the equal-time
-- table could not see: pair/alt/outer pick different time pairings), and the all-equal
-- pattern is the three-pairing sum. The load-bearing identity: the level-2 walk 0->1->2->1->0
-- carries (1/2)e^{-i(t1+t2-t3-t4)} and the two cross-pairings are EACH a quarter of that one
-- exponent -- their sum IS the walk term, which is why Wick survives truncation exactly
-- above threshold (2 < N load-bearing exactly where eqFourPoint_same says; at N = 2 the walk
-- dies). Equal periods recover eqFourPoint_wick through twoPointKernel_self = 1/2; all
-- periods 0 recover eqFourPoint at the definition level. Scope: free drive only; no
-- continuum limit; the 2n-point theorem NOT claimed (CV-23c, gated on the six-point pass).
/-- info: 'CSD.CV.timeTwoPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.timeTwoPoint_eq

/-- info: 'CSD.CV.timeFourPoint_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.timeFourPoint_same

/-- info: 'CSD.CV.timeFourPoint_wick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.timeFourPoint_wick

/-- info: 'CSD.CV.timeFourPoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.timeFourPoint_zero

-- CV-23c GATE (2026-08-17, CV\Wick.lean, Stage 7): the six-point pass -- RESULT: PASSED.
-- The all-equal sixth moment <Q^6> = 15/8 = 5!!(1/2)^3 for 3 < N via the Q^3 column at the
-- vacuum (the plan's ||Q^3 e0||^2 anchor in walk-collapse form: mass (3/2)/sqrt2 on the
-- one-quantum configuration, sqrt3/2 on the three-quantum configuration), plus the mixed
-- pattern <Q_k^4 Q_l^2> = 3/8 by clustering into eqFourPoint_same. fin_cases-free; the
-- idiom scaled by exactly ONE RUNG (one new configuration exc3Cfg, one entry-ladder level
-- Q_two_three/Q_three_two, one reachability lemma modeOp_Q_apply_exc2) -- linear growth,
-- no combinatorial blowup, exactly as the feasibility check predicted. Threshold honesty
-- one rung up: at N = 3 the level-3 walk dies and the all-equal value is 9/8, not 15/8
-- (documented, guarded by 3 < N). The general 2n-point theorem is NOT claimed -- the gate
-- un-gates that work (L residue, queue decision). Proof-engineering snag for the ledger:
-- rw of a naked Nat-literal equation (show (6:N) = 3+3) in a goal containing complex
-- numerals corrupts the OfNat/AtLeastTwo instance terms (the raw 6 lives inside 8's
-- instance) -- do pow-expansions in a standalone have with no other numerals, then rw the
-- matrix-level equation.
/-- info: 'CSD.CV.modeOpQ_six_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.modeOpQ_six_vac

/-- info: 'CSD.CV.modeOpQ_four_two_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.modeOpQ_four_two_vac

-- CV-23c CLOSURE (2026-08-17, CV\Wick.lean, Stage 7): the 2n-point theorem, pattern-resolved.
-- The moment ladder: <0|Q^{2n}|0> = (2n-1)!! (1/2)^n EXACTLY for n < N -- the vacuum moments
-- of the truncated quadrature are Gaussian below threshold, with (2n-1)!! counting Wick's
-- pairings. The threshold is n < N shaped exactly as the row scoped: a 2n-step return walk
-- reaches at most level n, so the cutoff is invisible iff n < N. Proof = the commutator
-- recursion <Q^{2n+2}> = (2n+1)/2 <Q^{2n}> against truncated_ccr ([a,a+] = 1 - N topProj):
-- the rank-one defect is sandwiched as <0|Q^j topProj Q^i|0> with i+j = 2n < 2(N-1), so at
-- most one factor reaches the top level and the walk band (Q_pow_apply_vac_of_lt) kills it.
-- Odd moments vanish by walk parity. modeOp is multiplicative (modeOp_mul/modeOp_pow, new
-- API), so the ladder transports verbatim to the field; grouped patterns factorise by
-- clustering (modeOpQ_pow_mul_pow_vac), longer grouped words iterate it, and interleavings
-- reduce via commute_modeOp. NOT claimed: the one-shot sum-over-perfect-matchings formula
-- for an arbitrary 2n-letter word (the four-point case has it: eqFourPoint_wick). The
-- generic ring identity commutator_pow_expand ([A,B^m] telescoped) landed as a helper.
/-- info: 'CSD.CV.Q_pow_two_mul_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.Q_pow_two_mul_vac

/-- info: 'CSD.CV.modeOpQ_pow_two_mul_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.modeOpQ_pow_two_mul_vac

/-- info: 'CSD.CV.modeOpQ_pow_two_mul_add_one_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.modeOpQ_pow_two_mul_add_one_vac

/-- info: 'CSD.CV.modeOpQ_pow_mul_pow_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.modeOpQ_pow_mul_pow_vac

-- CV-26 (2026-08-18, CV\ChannelRG.lean): channel-level RG at the cutoff -- the statement the
-- Stage-4 no-go said had to replace unitary RG matching. The coarse-graining is MODE TRACING
-- (keep the spectators, discard mode k), built as the Stinespring channel of the mode-split
-- permutation isometry, so CPTP is free and the DPI applies. CR-2
-- (coarseChannel_free_intertwine) is EXACT: the traced mode's phase meets its own conjugate in
-- every surviving entry and cancels, so at zero coupling the RG step incurs no error at all --
-- the whole CR-3 budget is the price of the interaction. CR-3 (channelRG_dist_le) is the
-- capstone: D(C(U^n rho U^n+), U_eff^n C(rho) U_eff^n+) <= 2n |tau| |lam| C for every density
-- operator, with 2 from the CR-1 bridge, n from the CV-12 telescoping, and |tau||lam|C from
-- the CV-9 Duhamel price; the DPI is what lets the channel be applied AFTER the estimate.
-- Scope: ONE coarse-graining step, not a flow -- no iteration, no fixed point, no beta
-- function; no level decimation (compressCfg is trace-decreasing, needs a leakage arm the
-- corpus lacks); uniform in distance (the cone-refined budget is deferred). Executes
-- specs\channel-rg-scoping.md exactly as scoped, both missing links discharged.
/-- info: 'CSD.CV.coarseChannel_apply_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.coarseChannel_apply_entry

/-- info: 'CSD.CV.coarseChannel_free_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.coarseChannel_free_intertwine

/-- info: 'CSD.CV.spectatorU_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.spectatorU_pow

/-- info: 'CSD.CV.channelRG_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.channelRG_dist_le

-- P1 first arc (2026-08-19, CV\ArenaBridge.lean): THE ARENA BRIDGE -- operator locality
-- carried onto the projective record arena, the twice-observed category bottleneck of
-- eft-pillars-plan P1. arenaObs A p = re tr(rho_p A) reads a matrix observable as a
-- FUNCTION on the arena; arenaObs_kick is the bridge identity (Schrodinger on the arena
-- IS Heisenberg on the operator); arenaObs_sub_le is CR-1's Hoelder-lite doing the
-- category translation (arena observables are 1-Lipschitz in the operator norm).
-- Statics: arenaObs_kick_of_disjointSupport -- an arena observable of mode set S is
-- EXACTLY invariant under any kick supported on disjoint T (Haag-Kastler on the arena).
-- Dynamics: arena_lightcone -- the previously UNSTATABLE theorem: a kick outside the
-- graph d-ball of R changes any region-R arena observable after time t by at most the
-- CV-20 factorial tail 2(2||S||t)^d/d! ||A||. Far interventions cannot reach the
-- epistemic regions faster than the cone. Scope: base arena only (fibred T^2 extension
-- and the field-structured-flow definitional layer are the recorded P1 remainder).
/-- info: 'CSD.CV.arenaObs_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaObs_kick

/-- info: 'CSD.CV.arenaObs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaObs_sub_le

/-- info: 'CSD.CV.arenaObs_kick_of_disjointSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaObs_kick_of_disjointSupport

/-- info: 'CSD.CV.arena_lightcone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arena_lightcone

-- P1 definitional layer (2026-08-19, CV\FieldStructuredFlow.lean): what it MEANS for a
-- flow to have field structure -- a skew generator presented as a sum of edge-supported
-- pieces (on-site terms as self-edges), with the induced one-parameter families on the
-- operators (flow_add) and on the record arena (arenaFlow_add, via the kick group law
-- arenaKick_mul). The characterisation P1 asked for: FieldStructuredFlow.lightcone --
-- EVERY field-structured flow's arena action has the Lieb-Robinson cone, as a property
-- of the structure, not of a chosen drive. Non-vacuity tied to the corpus's own drives:
-- freeFieldStructured_flow_eq identifies the structured free flow with freeFieldU at
-- accumulated phase, and graphStructured_flow_eq identifies the structured graph flow
-- with interactingU at the graph potential (same coupling; no-self-loops needed only for
-- the identification, not the structure). So the EFT chain's drives are instances and
-- the arena cone applies to them with no further hypotheses.
/-- info: 'CSD.CV.FieldStructuredFlow.lightcone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.FieldStructuredFlow.lightcone

/-- info: 'CSD.CV.FieldStructuredFlow.arenaFlow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.FieldStructuredFlow.arenaFlow_add

/-- info: 'CSD.CV.freeFieldStructured_flow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.freeFieldStructured_flow_eq

/-- info: 'CSD.CV.graphStructured_flow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.graphStructured_flow_eq

-- P1 close (2026-08-20, CV\FibredArenaBridge.lean): THE FIBRE-ACTIVE EXTENSION -- the
-- record arena fibred by the flat torus (FibredFieldArena = FieldArena x RecordFibre,
-- RecordFibre defeq LF4.KTorus), with the record write as the ShearWitness skew stroke
-- (recordStroke: fibre translated by g(arenaObs A .), a base-dependent shift factoring
-- through a region-supported arena observable). Statics: fibredObs_kick_of_disjoint-
-- Support (fibre-carrying observables exactly invariant under disjoint kicks) and
-- recordStroke_comm_kick (kicks outside the read region commute with record writing,
-- exactly). Dynamics: record_lightcone -- kick outside the graph d-ball of the read
-- region, evolve under ANY field-structured flow, write the record, read any Lipschitz
-- fibre observable: the readout moves by at most Lh*Lg * 2(2||S||t)^d/d! * ||A|| (the
-- rigid fibre rotation cancels between the two histories). The record cell -- a fibre
-- fact, where record content necessarily lives for N >= 3 -- cannot be steered from
-- outside the cone. Scope: stroke-shaped fibre activity (base-coupled fibre VELOCITY
-- is declared out of scope in the module and in check-claims' wait ledger).
/-- info: 'CSD.CV.fibredObs_kick_of_disjointSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.fibredObs_kick_of_disjointSupport

/-- info: 'CSD.CV.recordStroke_comm_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.recordStroke_comm_kick

/-- info: 'CSD.CV.record_lightcone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.record_lightcone

-- P4 (2026-08-20, CV\DispersionEarned.lean): THE DISPERSION EARNED -- the converse the
-- necessity audit recorded as proved nowhere. cone_preserving_is_boost: a linear map of
-- the (E,p) plane preserving both light rays forward with unit determinant IS a boost
-- (cosh/sinh derived, chi = -arsinh b). boost_covariance_selects_omega: rest energy
-- m > 0 + boost-covariant graph forces omega = sqrt(p^2+m^2) -- one orbit through the
-- rest point covers every momentum; no continuity/evenness/measurability assumed.
-- cone_symmetry_characterises_omega: the iff (backward = the corpus's own boost_omega
-- via omega_cone_covariant, so the hypothesis is non-vacuous by theorem, not by toy).
-- massless_covariance_not_selecting: at m = 0 selection fails (omega = id is covariant
-- with rest energy 0 but is not |p|), so the mass gap is sharp. Kinematic level;
-- no lattice boost action, no LR-cone identification (module scope block).
/-- info: 'CSD.CV.boost_covariance_selects_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.boost_covariance_selects_omega

/-- info: 'CSD.CV.cone_preserving_is_boost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.cone_preserving_is_boost

/-- info: 'CSD.CV.cone_symmetry_characterises_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.cone_symmetry_characterises_omega

/-- info: 'CSD.CV.massless_covariance_not_selecting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.massless_covariance_not_selecting

-- P2 (2026-08-20, CV\CompositeArena.lean): THE COMPOSITE ARENA -- two sectors compose by
-- mode concatenation (FieldArena (K1+K2) N; configSplit), the join is the Segre/Kronecker
-- map (arenaJoin, norm multiplicative), and the algebra forcing transports. Statics:
-- leftOp/rightOp are SupportedOn their mode blocks (P1 machinery applies for free), so
-- composite_no_signalling -- a right-sector kick leaves every left-sector observable
-- invariant EXACTLY, for ALL states including entangled ones (instance of the P1 statics,
-- not a consequence of the join). Transport: arenaDM_join (rho tensor factorises),
-- arenaObs_join_left/right (exact marginals), arenaObs_join_mul (local tomography on the
-- arena), arenaKick_join (product dynamics restrict). Entanglement: bell_not_join -- the
-- Bell ray is NOT a join (composite strictly larger than the pair; the arena-side
-- signature of tensor vs Cartesian). Forcing: composite_generate (the mode-local
-- subalgebras generate, arena-natively) + compositeArenaForced (the landed
-- compositeAlgReconstruction CONSUMED at the arena's own algebras, pinned on tmuls by
-- compositeArenaForced_tmul). Scope: homogeneous field sectors (module scope block).
/-- info: 'CSD.CV.composite_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.composite_no_signalling

/-- info: 'CSD.CV.bell_not_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.bell_not_join

/-- info: 'CSD.CV.arenaObs_join_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaObs_join_mul

/-- info: 'CSD.CV.arenaKick_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaKick_join

/-- info: 'CSD.CV.composite_generate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.composite_generate

/-- info: 'CSD.CV.compositeArenaForced_tmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.compositeArenaForced_tmul

-- P5-attainment (2026-08-20, CV\PriceAttainment.lean): THE LINEAR PRICE IS ATTAINED --
-- CV-9's declared boundary closed. The commutator functional (any S-supported B
-- commutes with a disjoint probe, so a single computable commutator lower-bounds the
-- distance to the WHOLE supported subalgebra) evaluated on the K=N=2 witness: the
-- interacting drive is a diagonal phase, the free phases cancel between the two
-- commutator paths (energy is mode-additive), the coupling phase survives (it reads
-- both modes), and the commutator entry has modulus 2|sin(tau*lam/2)| EXACTLY
-- (comm_entry_norm). price_lower_bound: every {0}-supported operator is at least
-- |sin(tau*lam/2)| from the interacting Heisenberg observable. price_linear_attained:
-- the sandwich tau*lam/pi <= dist <= 2*tau*lam (Jordan below, CV-9 above) -- the price
-- is linear on BOTH sides; "costs at most" is now "costs exactly" up to [1/pi, 2].
-- Scope: one witness (attainment is an existence claim; module scope block).
/-- info: 'CSD.CV.comm_entry_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.comm_entry_norm

/-- info: 'CSD.CV.price_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.price_lower_bound

/-- info: 'CSD.CV.price_linear_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.price_linear_attained

-- Q27 first brick (2026-08-20, CV\EntangledWeights.lean): WHAT ENTANGLEMENT DOES TO THE
-- WEIGHTS -- local observations are reduced-state expectations. reducedDM (right partial
-- trace of arenaDM read on the pair index) is a genuine density operator for EVERY
-- composite point (reducedDM_posSemidef / reducedDM_trace). The bridge:
-- arenaObs_leftOp_eq_reduced -- arenaObs (leftOp A) x = re tr(reducedDM x * A) for every
-- composite point x, entangled included; local arena observations ARE mixed-Born pairings
-- against the reduced state. Contrast: reducedDM_join -- on a product point the reduced
-- state is the pure local state arenaDM p, so departure from rank-one is exactly
-- entanglement's contribution. The Bell answer: reducedDM_bell -- the Bell ray's reduced
-- state is the equal mixture (1/2)(|x0><x0| + |x1><x1|); corollaries bell_local_weight0/1:
-- each correlated pattern's local weight is exactly 1/2 (maximal mixing; no remote labels
-- survive -- composite_no_signalling read as a consequence). Scope: weights delivered in
-- the re tr(reducedDM * A) mixed-Born form on the field-configuration index; the
-- Fin-indexed LF2 mixed-tier transport is declared index plumbing, not claimed;
-- sequential/record-conditioned versions are Q25 (module scope block).
/-- info: 'CSD.CV.reducedDM_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.reducedDM_posSemidef

/-- info: 'CSD.CV.reducedDM_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.reducedDM_trace

/-- info: 'CSD.CV.arenaObs_leftOp_eq_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.arenaObs_leftOp_eq_reduced

/-- info: 'CSD.CV.reducedDM_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.reducedDM_join

/-- info: 'CSD.CV.reducedDM_bell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.reducedDM_bell

/-- info: 'CSD.CV.bell_local_weight₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.bell_local_weight₀

/-- info: 'CSD.CV.bell_local_weight₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.CV.bell_local_weight₁

end CSD.Tests.AxiomAudit
