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
-- HONEST SCOPE: free (mode-diagonal) drive only; interacting-drive spreading is now
-- BOUNDED by CV-8 (SupportSpreading: coupling-graph light cone + K=N=2 witness); the
-- norm pricing (CV-9, Duhamel route) is what is still not claimed here.
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

end CSD.Tests.AxiomAudit
