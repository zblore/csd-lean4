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
-- Concentration/Levy (the typical-state upgrade) is the NAMED residual, not
-- proved. Foundational-triple; Gleason-free.
/-- info: 'CSD.Thermo.fs_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_first_moment

/-- info: 'CSD.Thermo.canonical_typicality_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.canonical_typicality_expectation

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

end CSD.Tests.AxiomAudit
