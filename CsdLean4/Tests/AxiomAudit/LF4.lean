/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: LF4

**Category:** Special (axiom-posture regression pins; G9 split part).

LF4 pins (moment map, Born-from-volume, Kaehler instances, W-series dynamics spine).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.LF4`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- MOMENT-MAP REGULARITY (2026-07-30, LF4/MomentMap.lean) -- the prerequisite for the basin.
-- momentMap is DEFINED through p.rep, a Classical.choice representative, so it cannot be attacked
-- directly: Projectivization.rep is not continuous out of P, and no unfolding makes it so. The route
-- is the QUOTIENT -- the coordinate ratio is continuous on the nonzero subtype and scale-invariant
-- (momentRatio_smul), and mk' is a quotient map (Projectivization.isQuotientMap_mk'), so the
-- descended function is continuous. Measurability is then IMMEDIATE, because P K V carries the BOREL
-- sigma-algebra of that same topology (Projectivization.instBorelSpace).
-- ⚠️ ESTIMATE CORRECTION: this was logged as effort M on the assumption the infrastructure was
-- missing. It is S -- Projectivization/Topology.lean and Projectivization/MeasureSpace.lean already
-- staged continuous_iff_continuous_comp_mk' and the Borel instance. The row was wrong, not the work.
/-- info: 'CSD.LF4.continuous_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.continuous_momentMap

/-- info: 'CSD.LF4.measurable_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.measurable_momentMap

/-- info: 'CSD.LF4.schrodinger_flow_kahler_symplectomorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.schrodinger_flow_kahler_symplectomorphism

/-- info: 'CSD.LF4.cpSectorActionBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorActionBundle

-- §13.2 CONCRETE gate discharge (2026-07-19): the three single-qubit gate realisability Props
-- (hadamard/phaseS/phaseT_realisable_for) DISCHARGED on cpSectorData. Each gate's action is a genuine
-- CSDUnitaryBundle whose U_isometry is derived from the gate ∈ U(2) (inner_toEuclideanLin_unitary),
-- modulo the posited CSD sector (SO-1). Type carries U + U_isometry + Context, not a Σ-flow (PLACEHOLDERS §7), so the Σ-flow-lift
-- reading is the open D1 gap. Converts 3 of the 9 claim-shaped gate placeholders (PLACEHOLDERS §1) to proved.
/-- info: 'CSD.LF4.hadamard_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hadamard_realisable_cpSector

/-- info: 'CSD.LF4.phaseS_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phaseS_realisable_cpSector

/-- info: 'CSD.LF4.phaseT_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phaseT_realisable_cpSector

-- §13.2 gate discharge COMPLETE (2026-07-19): the remaining six gate realisability Props discharged on
-- cpSectorData (2-qubit CNOT/SWAP/CZ, multi-qubit Toffoli/Fredkin, composite Bell-prep). All nine gate
-- placeholders (PLACEHOLDERS §1) now proved; same honest scope (modulo the posited CSD sector (SO-1); type carries U + U_isometry +
-- Context, not a Σ-flow — D1 gap). U_isometry derived from the gate ∈ U(N) (inner_toEuclideanLin_unitary).
/-- info: 'CSD.LF4.cnot_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cnot_realisable_cpSector

/-- info: 'CSD.LF4.swap_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.swap_realisable_cpSector

/-- info: 'CSD.LF4.cz_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cz_realisable_cpSector

/-- info: 'CSD.LF4.toffoli_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.toffoli_realisable_cpSector

/-- info: 'CSD.LF4.fredkin_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fredkin_realisable_cpSector

/-- info: 'CSD.LF4.bell_prep_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bell_prep_realisable_cpSector

-- SL-3 (2026-07-10): the §13.2 ontic lift on the NON-TRIVIAL-FIBRE instance kSectorData
-- (π = pr₁ many-to-one, Σ = ℂℙ^{N-1}×T²), the cpSectorActionBundle analogue on the Kähler instance.
-- Part 1 (thread Φ): the sector flow Φ=kFlow descends along π to f_Φ=id on rays
-- (kSectorDataFlow_projectable), which is TransProbPreserving (kProjectedFlow_transProbPreserving)
-- and fed through Wigner realises the unitary branch (kProjectedFlow_unitary_or_antiunitary) —
-- honest but degenerate (ray flow trivial; dynamics live in the T² fibre). Part 2 (genuine, caveat
-- C-1): the sector U(N)-action carries the FS-isometry — kSectorActionBundle's U_isometry is a Wigner
-- OUTPUT (kSectorActionBundle_U_isometry), not a posit. Does NOT derive TPP from measure-preservation
-- (that is the §13.2 trap / open D1 gap); SO-1 untouched.
/-- info: 'CSD.LF4.kSectorDataFlow_projectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_projectable

/-- info: 'CSD.LF4.kProjectedFlow_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kProjectedFlow_transProbPreserving

/-- info: 'CSD.LF4.kProjectedFlow_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kProjectedFlow_unitary_or_antiunitary

/-- info: 'CSD.LF4.kSectorActionBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorActionBundle

/-- info: 'CSD.LF4.kSectorActionBundle_U_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorActionBundle_U_isometry

/-! ### LF4 §8 ontic-shell instantiation

The first concrete `SectorData` instance and its axiom-free measure bridge.
Both cite only the foundational triple; `cp_measure_bridge` realises the measure
bridge `π∗μL = c • μFS` axiom-free (`c = 1`). This is now the *only* form of the
bridge in the corpus — the abstract `measure_bridge` and the
`invariant_measure_uniqueness` axiom it carried were removed 2026-06-04. -/

/-- info: 'CSD.LF4.cpSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorData

/-- info: 'CSD.LF4.cp_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cp_measure_bridge

-- The non-trivial-fibre compact-Kähler instance Σ = ℂℙ^{N-1} × T² and its
-- axiom-free marginal bridge π∗μL = μFS (c = 1). No invariant_measure_uniqueness.
/-- info: 'CSD.LF4.kSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorData

/-- info: 'CSD.LF4.k_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.k_measure_bridge

-- Tranche A: a non-trivial measure-preserving flow on the Kähler fibre (Φ ≠ id),
-- making the LF1 deterministic-typicality theorem non-vacuous on the instance.
/-- info: 'CSD.LF4.kFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_measurePreserving

/-- info: 'CSD.LF4.kFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_ne_id

/-- info: 'CSD.LF4.kFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_frequency_convergence

-- W2: the Kähler ontic-sector INTERFACE (sector hypotheses as structure fields,
-- no global axioms) + its inhabitation witness (non-vacuity). The projective
-- target matches Wigner's ℙ ℂ (EuclideanSpace ℂ (Fin N)).
/-- info: 'CSD.LF4.trivialKahlerOnticSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup

-- Connectivity fix C1 (manifest link L4): a GENUINE Φ≠id KahlerOnticSetup
-- inhabitant. unitaryFlowSetup builds one from any unitary family
-- (measure-preserving via fubiniStudyMeasure_smul_invariant); the concrete
-- rotationSetup at N=2 (the ℂℙ¹ rotation flow) has projectedFlow ≠ id
-- (rotationSetup_projectedFlow_ne_id, [e₀]↦[e₁] at t=π/2). This flips the
-- Schrödinger pillar off the trivial Φ=id, H=0 witness. See
-- specs/connectivity-manifest.md.
/-- info: 'CSD.LF4.rotationSetup_projectedFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_projectedFlow_ne_id

/-- info: 'CSD.LF4.unitaryFlowSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup

-- Connectivity fix C5 (manifest link L1): the Liouville-volume field is
-- load-bearing. It carries the formalizable core of "Liouville = Kähler
-- volume" -- that μ_FS is a normalized volume (probability measure). Since the
-- 2026-08-06 F-04 tightening the field IS the concrete liouville_isProbability
-- (an instance); this theorem stays as the thin projection exposing it.
/-- info: 'CSD.LF4.unitaryFlowSetup_liouville_isProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_liouville_isProbability

-- Kähler pointwise core (de-vacuumed 2026-07-19; field made CONCRETE 2026-08-06, F-04: the structure
-- field is now kahler_pointwise : IsFubiniStudyKahler N) -- the pointwise Fubini-Study Kähler-compatibility
-- triple (J²=-1, ω=g∘J, g=ω∘J, ω a (1,1)-form, ω u (Ju)=‖u‖²), PROVED axiom-free
-- (fubiniStudy_pointwise_kahler_compatibility). Only the manifold residual (dω=0, top-power volume
-- identity) stays unformalizable. isFubiniStudyKahler is the discharge.
/-- info: 'CSD.LF4.isFubiniStudyKahler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.isFubiniStudyKahler

-- Move up the chain (2026-07-10): UPGRADE the Liouville-volume content from "μ is a
-- probability measure" (C5 core) to "μ is THE volume forced by the space + U(N)-symmetry"
-- (IsForcedKahlerVolume: prob + invariant + UNIQUE, via fubiniStudyMeasure_unique). So the Kähler
-- volume is an OUTCOME of Σ = ℂℙ^{N-1} and its symmetry, not posited: fubiniStudyMeasure IS the forced
-- volume, the unitaryFlowSetup sector volume IS it, and the many-to-one instance's ray-space volume
-- π_*(kMuL) IS it (kMuL = forced-FS ⊗ Haar). The 2-form manifold residual stays Mathlib-blocked (KG-1);
-- FORWARD (takes G=U(N) as given, does not derive it — SO-1 untouched).
/-- info: 'CSD.LF4.fubiniStudyMeasure_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fubiniStudyMeasure_isForcedKahlerVolume

/-- info: 'CSD.LF4.unitaryFlowSetup_liouville_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_liouville_isForcedKahlerVolume

/-- info: 'CSD.LF4.manyToOneSetup_baseVolume_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_baseVolume_isForcedKahlerVolume

/-- info: 'CSD.LF4.manyToOneSetup_liouville_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_liouville_eq_product

-- Connectivity fix C2 (manifest link L3, off the trivial witness): the W-series
-- Schrödinger capstone sigmaFlow_schrodinger_form FIRED on the genuine Φ≠id
-- rotation flow. The rotation R(t) is a one-parameter unitary group (trivial
-- cocycle) with generator J=[[0,-1],[1,0]]; the capstone recovers H=iJ=σ_y
-- (Pauli-Y, Hermitian, ≠0), landing rotationSetup.pi(flow t x) = exp(-it σ_y) •
-- pi x. First fully-instantiated H≠0 Schrödinger statement of the corpus.
/-- info: 'CSD.LF4.rotationSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_schrodinger_form

/-- info: 'CSD.LF4.rotationSetup_generator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_generator_ne_zero

-- Connectivity fix C4 (manifest links L5/L6): BOTH pillars on ONE object. The
-- Born capstone now references the SECTOR'S OWN liouvilleMeasure (defeq
-- fubiniStudyMeasure), so a single rotationSetup instance supports both
-- Schrödinger dynamics (A) and Born frequencies (B).
-- rotationSetup_both_pillars is the structural "one posited object underlies
-- both pillars" theorem. Honest gap: the Born trials still SAMPLE the measure
-- rather than being evolved by the flow (= C6/L7, the SO-1/D1 frontier).
/-- info: 'CSD.LF4.unitaryFlowSetup_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_born_frequency

/-- info: 'CSD.LF4.rotationSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_both_pillars

-- Connectivity fix C7 (Paper-C A3 caveat): BOTH pillars on ONE object with a
-- GENUINE many-to-one π. rotationSetup uses π = id (degenerate); manyToOneSetup
-- has Σ = ℂℙ^{N-1} × T², π = Prod.fst (fibres = T², not points —
-- manyToOneSetup_pi_not_injective) AND a non-trivial projected ray flow. The
-- Born pillar scores the FIBRED region π⁻¹'(bornRegion), whose kMuL-volume = the
-- base Born weight because the fibre volume is normalized (Prod.fst_* kMuL = μFS).
-- Same honest gap as C4: trials sample kMuL, not evolved by the flow (L7/SO-1).
/-- info: 'CSD.LF4.manyToOneSetup_pi_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_pi_not_injective

/-- info: 'CSD.LF4.manyToOneSetup_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_born_frequency

/-- info: 'CSD.LF4.manyToOneRotationSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneRotationSetup_both_pillars

-- General-N unified capstone (2026-07-10): both pillars from the Kähler space Σ = ℂℙ^{N-1}×T² mapped
-- by π = pr₁ onto the ray space, at general N with ARBITRARY Hermitian H. manyToOneSetup driven by
-- U t = exp(-itH) (schrodingerUnitary): (A) Schrödinger π(Φ_t x)=exp(-itH)•π x holds by rfl at general N
-- (no N=2 σ_y, no Wigner selection — the flow is unitary by construction), (B) Born via the already
-- general-N manyToOneSetup_born_frequency. FORWARD delivery (consumes the sector); SO-1 untouched.
/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_both_pillars

-- Schrödinger pillar DERIVED (2026-07-19): the (A)-by-rfl form above is now backed by an exercised
-- C¹-Stone derivation on the REAL nonzero generator at general N. schrodingerUnitary_hasDerivAt
-- DISCHARGES the smoothness datum U' t = U t·(-iH); manyToOneSchrodingerSetup_schrodinger_derived
-- exhibits the skew generator A = -iH, that discharged datum, the Stone conclusion U t = exp(t•A)
-- (Matrix.StoneC1.eq_exp_of_hasDeriv), and the pillar — no longer only the A = 0 witness.
/-- info: 'CSD.LF4.schrodingerUnitary_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.schrodingerUnitary_hasDerivAt

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_pi_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_pi_not_injective

-- W3: the Wigner selection on the Kähler ontic setup. The per-t disjunction
-- (unitary ∨ antiunitary) consumes W1 wigner_rigidity_unitaryGroup through the W2
-- interface; hTPP (transition-probability preservation) is a HYPOTHESIS, NOT
-- derived from Liouville-preservation (measure ≠ metric). The continuous-from-
-- identity refinement selects the unitary branch, STAGED on the clopen datum
-- (named topological residual: continuity of t ↦ flow + disconnectedness of the
-- antiunitary component), discharged via connectedness of ℝ.
/-- info: 'CSD.LF4.projectedFlow_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_or_antiunitary

/-- info: 'CSD.LF4.projectedFlow_unitary_of_clopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_of_clopen

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_unitary_or_antiunitary

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_unitary_of_clopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_unitary_of_clopen

-- W5: projected CSD dynamics = projective action of a one-parameter unitary
-- family. projectedFlow_eq_unitary_family is the MILESTONE (given the W3
-- selection hU: ∀t, ProjUnitary d t, the projected flow is the projective action
-- of a single one-parameter family {U_t}; choice over the per-t existentials,
-- NOT from Liouville-preservation, measure ≠ metric). The ray-level one-parameter
-- projective representation (U(s+t)•p = (U s * U t)•p, U 0•p = p) is proved under
-- EXPLICIT one-parameter-group hypotheses on projectedFlow. exp(-itH) is STAGED:
-- the CONVERSE realizability witness (expNegITH_unitary_group: t ↦ exp(-itH) is a
-- genuine vector-level one-parameter unitary group for Hermitian H) is proved,
-- while the Stone direction (recover H from an abstract projected flow) is the
-- named residual (phase lift S1 + finite-dim Stone S2, absent from Mathlib).
/-- info: 'CSD.LF4.projectedFlow_eq_unitary_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_eq_unitary_family

/-- info: 'CSD.LF4.unitaryFamily_projective_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFamily_projective_representation

/-- info: 'CSD.LF4.projectedFlow_projective_one_parameter_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_projective_one_parameter_representation

/-- info: 'CSD.LF4.schrodingerGen_exp_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.schrodingerGen_exp_mem_unitaryGroup

/-- info: 'CSD.LF4.expNegITH_unitary_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expNegITH_unitary_group

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_eq_unitary_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_eq_unitary_family

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_projective_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_projective_representation

/-- info: 'CSD.LF4.expNegITH_unitary_group_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expNegITH_unitary_group_zero

/-- info: 'CSD.LF4.projectedFlow_phase_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_phase_cocycle

/-- info: 'CSD.LF4.phase_cocycle_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phase_cocycle_identity

/-- info: 'CSD.LF4.projectedFlow_phase_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_phase_lift

/-- info: 'CSD.LF4.projectedFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_schrodinger_form

-- Continuity variant (2026-09-01): same conclusion with the C^1 datum replaced by plain
-- continuity of the lifted family, via Matrix.StoneC1.stone_continuous (which derives
-- smoothness by integral averaging). Discharges the W5 S2 smoothness posit; before this
-- the continuity-only Stone theorem was proved and had NO consumer.
/-- info: 'CSD.LF4.projectedFlow_schrodinger_form_of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_schrodinger_form_of_continuous

-- ★★ S1 AND S2 both discharged (2026-09-01): continuity of the projective flow alone gives
-- the Schrodinger form. The coboundary datum dies by the one-parameter lift (Lambda^2(R)=0,
-- no Bargmann theorem needed) which returns a CONTINUOUS b -- exactly what stone_continuous
-- was missing. Only hfam (transition-probability preservation) still conditions the chain.
/-- info: 'CSD.LF4.projectedFlow_schrodinger_form_of_continuous_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_schrodinger_form_of_continuous_flow

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_phase_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_phase_lift

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_schrodinger_form

-- The Σ-level capstone: the SUBSTRATE-CONSUMING form. Unlike the ray-level
-- schrodinger_form (which touches only d.projectedFlow), sigmaFlow_schrodinger_form
-- consumes d.projectable + d.flow + d.pi to conclude the deterministic ontic
-- Σ-flow, projected through π, IS exp(-itH)-conjugation: d.pi (d.flow t x) =
-- exp(-itH) • d.pi x. This is the theorem that makes the KahlerOnticSetup
-- substrate load-bearing (guarded by scripts/check-sector-linkage.sh); without
-- it the sector object is carried-but-unused scaffolding.
/-- info: 'CSD.LF4.sigmaFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaFlow_schrodinger_form

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_sigmaFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_sigmaFlow_schrodinger_form

/-- info: 'CSD.LF4.not_projUnitary_and_projAntiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.not_projUnitary_and_projAntiunitary

/-- info: 'CSD.LF4.projUnitary_isClopen_of_bargmann_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projUnitary_isClopen_of_bargmann_continuous

/-- info: 'CSD.LF4.projectedFlow_unitary_of_bargmann_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_of_bargmann_continuous

/-- info: 'CSD.LF4.projUnitary_of_dim_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projUnitary_of_dim_le_one

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_bargmann_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_bargmann_selection

-- D1c-1: the concrete compact-Kähler SectorData that carries the genuine
-- measure-preserving Φ = kFlow ≠ id (structural discharge of the "Φ = id in the
-- concrete Kähler instance" debt; cpSectorData still carries Φ = id).
/-- info: 'CSD.LF4.kSectorDataFlow_phi_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_phi_ne_id

/-- info: 'CSD.LF4.kSectorDataFlow_phi_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_phi_measurePreserving

/-- info: 'CSD.LF4.kSectorDataFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_frequency_convergence

-- Tranche 1: the Born weights as the torus moment map on ℂℙ^{N-1} (a forced
-- symplectic invariant of the Kähler structure, not a carving). Headline:
-- momentMap_mk_eq_inner_sq — Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖² at a unit preparation.
/-- info: 'CSD.LF4.momentMap_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_sum_eq_one

/-- info: 'CSD.LF4.momentMap_mk_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_mk_eq_inner_sq

/-- info: 'CSD.LF4.momentMap_mk_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_mk_of_norm_eq

-- The measured observable's Hamiltonian flow (the first physically-meaningful Φ≠id):
-- measure-preserving (obsFlow_measurePreserving), and the Born weights are its conserved
-- quantities (momentMap_obsFlow: momentMap (obsFlow p) = momentMap p). Ties the observable's
-- dynamics to the Born volumes; the measurement event (collapse) is still LF5.
/-- info: 'CSD.LF4.obsFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_measurePreserving

/-- info: 'CSD.LF4.momentMap_obsFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_obsFlow

-- The observable flow is genuinely non-trivial (Φ ≠ id), witnessed on a SUPERPOSITION ray
-- (every computational-basis ray is a diagonal-phase eigenvector and is FIXED): the |0⟩+|1⟩
-- ray is moved because its two coordinates pick up the distinct phases 1 and -1. Mirrors
-- kFlow_ne_id as the named non-triviality witness.
/-- info: 'CSD.LF4.obsFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_ne_id

-- SO-1 onramp (TypicalityForcing.lean): WHERE the Fubini–Study typicality measure comes from.
-- (A) fubiniStudy_forced_by_symmetry — any U(N)-invariant probability measure on the sector
-- ℂℙ^{N-1} IS the Fubini–Study measure (restates the axiom-free fubiniStudyMeasure_unique as
-- the typicality-derivation: Born = FS-volume is DERIVED from the sector symmetry G = U(N),
-- not posited). (B) obsFlow_not_uniquely_ergodic — a single ontic flow does NOT force FS: it
-- has ≥2 distinct invariant probability measures (μFS and δ_{[e₀]} at a fixed basis ray).
-- so1_onramp conjoins them. HONEST: typicality is forced by the SYMMETRY, not any flow; residual
-- SO-1 primitive = G = U(N) itself, which reduces to D1 (G-from-CSD-dynamics, NOT done). SO-1 not
-- closed. (SO-1 = the CSD sector origin, distinct from Paper C A5 = projectability.)
-- Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.fubiniStudy_forced_by_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fubiniStudy_forced_by_symmetry

/-- info: 'CSD.LF4.obsFlow_not_uniquely_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_uniquely_ergodic

/-- info: 'CSD.LF4.so1_onramp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.so1_onramp

-- (B′) STRENGTHENING (TypicalityForcing.lean): the obstruction to unique ergodicity is GENERIC,
-- via a CONSERVED QUANTITY. map_withDensity_of_conserved — reweighting an invariant measure by a
-- conserved density (d ∘ T = d) keeps it invariant (the genuine conserved-quantity mechanism).
-- withDensity_momentMap_obsFlow_invariant — instantiated at the conserved Born coordinate
-- momentMap·i (momentMap_obsFlow): μFS.withDensity (g ∘ momentMap·i) is obsFlow-invariant.
-- obsFlow_continuum_invariant — a CONTINUUM (Set.InjOn on [0,1]) of pairwise-distinct
-- obsFlow-invariant PROBABILITY measures (convex-combo witness s·μFS+(1-s)·δ_{[e₀]}; the
-- conserved Born coordinates are the structural WHY). HONEST: strengthens the obstruction;
-- still does NOT force FS / NOT close SO-1. Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.map_withDensity_of_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.map_withDensity_of_conserved

/-- info: 'CSD.LF4.withDensity_momentMap_obsFlow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.withDensity_momentMap_obsFlow_invariant

/-- info: 'CSD.LF4.obsFlow_continuum_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_continuum_invariant

-- (B′′) SHARPER, μFS-SPECIFIC obstruction (TypicalityForcing.lean): obsFlow is not even
-- μFS-ERGODIC (distinct from not-uniquely-ergodic, which does NOT imply not-μFS-ergodic).
-- momentMap_obsFlow_nonconstant_conserved — the Born coordinate momentMap·0 is a NON-CONSTANT
-- CONSTANT OF MOTION (conserved via momentMap_obsFlow, measurable, values 1 at [e₀] vs 0 at
-- [e₁]). obsFlow_not_ergodic — therefore ¬ Ergodic obsFlow μFS: the conserved coordinate gives
-- a non-trivial μFS-invariant set {m₀ ≥ m₁} of measure ∈ (0,1) (full support of μFS via the
-- Haar pushforward bounds it away from 0 and 1), contradicting the zero-one law.
-- so1_obstruction_capstone — packages (1)⇒(2): single flow ⇒ non-constant conserved observable
-- ⇒ not μFS-ergodic ⇒ cannot force μFS. HONEST: CLOSES the single-flow obstruction story; an
-- ergodic flow (only-constant conserved observables) is what D1 must supply; residue = G-from-D1.
-- SO-1 NOT closed. Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.momentMap_obsFlow_nonconstant_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_obsFlow_nonconstant_conserved

/-- info: 'CSD.LF4.obsFlow_not_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_ergodic

/-- info: 'CSD.LF4.so1_obstruction_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.so1_obstruction_capstone

-- D1c-2: the concrete BASE SectorData carrying a PHYSICALLY-MEANINGFUL Φ = obsFlow ≠ id
-- (the observable's Hamiltonian flow exp(i t Â) on the Fubini–Study Kähler base ℂℙ^{N-1}).
-- Strictly stronger than D1c-1's free T²-fibre translation (kSectorDataFlow): dynamics on
-- the actual projective state space, not a trivial fibre shift. obsFlow is a single
-- observable's periodic phase flow (not de-isolation Φ_vN, not ergodic); SO-1 ergodicity gap
-- remains.
/-- info: 'CSD.LF4.cpSectorDataFlow_phi_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_phi_ne_id

/-- info: 'CSD.LF4.cpSectorDataFlow_phi_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_phi_measurePreserving

/-- info: 'CSD.LF4.cpSectorDataFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_frequency_convergence

-- Tranche M slice 3: the Born weight as a barycentric volume ratio. The i-th
-- subdivision region of the moment polytope at Φ([ψ]) has Lebesgue-volume
-- fraction ‖⟨eᵢ,ψ⟩‖² (vertex-replacement map det = barycentric coord, via Cramer
-- + addHaar_image_linearMap). Geometric region, not carved; no operational axiom.
/-- info: 'CSD.LF4.replaceMap_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_det

/-- info: 'CSD.LF4.replaceMap_image_volume_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_image_volume_sum

/-- info: 'CSD.LF4.born_eq_volume_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_eq_volume_ratio

-- Tranche M slice 2 (reduction): the moment map along the U(N) orbit reduces the
-- Fubini-Study pushforward to the Haar law of the squared-moduli of U·rep (the
-- Dirichlet keystone; N=2 = "|U₀₀|² uniform"). Bridge lemma toward Φ∗μ_FS=uniform.
/-- info: 'CSD.LF4.momentMap_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_orbit

-- Tranche M slice 2 (option C): Born = Fubini-Study volume ratio on the ontic
-- Kähler Σ = ℂℙ¹, modulo the explicit N=2 Duistermaat-Heckman hypothesis
-- (the 0-coordinate marginal of the genuine FS measure is uniform[0,1]).
-- Axiom-clean (hypothesis-gated); momentMap measurable via the §12 lift API.
/-- info: 'CSD.LF4.momentMap_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_measurable

/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit

-- Busch-free empirical capstone: i.i.d. sampling from fubiniStudyMeasure on ℂℙ¹,
-- frequencies of the moment-sublevel outcome → the Born weight ‖⟨e₀,ψ⟩‖² via the
-- volume route (foundational triple + h_uniform hypothesis; NO busch_effect_gleason).
/-- info: 'CSD.LF4.qubit_born_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence

-- General-N joint Busch-free Born frequency convergence over a finite outcome
-- family (Born = ontic volume as hypothesis hborn). Closes LF4-todo §9.
/-- info: 'CSD.LF4.born_frequency_convergence_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_partition

-- Plan B step 1: the moment marginal of μ_FS = the Haar law of the
-- squared-modulus ratio of U·rep. Reduces h_uniform to the (deferred) Dirichlet
-- marginal "|U₀₀|² ~ Uniform[0,1] for Haar U(2)".
/-- info: 'CSD.LF4.momentMap_pushforward_eq_haar_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_pushforward_eq_haar_marginal

-- (The qubit Duistermaat–Heckman fact `fs_moment_pushforward_uniform` is now a
-- THEOREM, discharged in MomentUniform.lean; its foundational-triple pin lives in
-- the Slice 4 block below, together with the two unconditional Born consumers.)

-- Plan B Part 1 step: a unitary matrix's toEuclideanLin preserves the Euclidean
-- norm (the matrix-analytic core for the Gaussian unitary-invariance step).
/-- info: 'CSD.LF4.unitary_norm_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitary_norm_preserving

-- Plan B Part 1 (Option 2) C1: the hand-built real coordinate isometry ℝ⁴ ≃ₗᵢ[ℝ] ℂ²
-- (keeps stdGaussian on the clean real space, avoiding the ℝ/ℂ instance diamond).
/-- info: 'CSD.LF4.coords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.coords

-- Plan B Part 1 (Option 2) C4-C5: gaussianCP = fubiniStudyMeasure on ℂℙ¹, via the
-- by-hand real conjugate isometry conjR (restrictScalars ℝ diamonds in the full LF4
-- import context), unitary-invariance of the Gaussian-induced measure, and the
-- axiom-free Fubini-Study uniqueness theorem. All foundational-triple-only.
/-- info: 'CSD.LF4.conjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.conjR

/-- info: 'CSD.LF4.gaussianH_map_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianH_map_unitary

/-- info: 'CSD.LF4.gaussianCP_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_smul_invariant

/-- info: 'CSD.LF4.gaussianCP_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_eq_fubiniStudy

-- General-N Part 1 (Slice B): the projectivised standard Gaussian on ℂ^N is the
-- Fubini-Study measure on ℂℙ^{N-1}, via the real coordinate isometry
-- coordsN : ℝ^{N×2} ≃ₗᵢ ℂ^N + stdGaussian U(N)-invariance + fubiniStudyMeasure_unique.
-- The N-general analogue of gaussianCP_eq_fubiniStudy. Foundational triple.
/-- info: 'CSD.LF4.gaussianCPN_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCPN_eq_fubiniStudy

-- Plan B Part 2, Slice 1 (L5.1): the single-block squared-norm law is Exp(1/2).
-- `‖·‖²∗ N(0,I₂) = Exp(1/2)` on plain ℝ × ℝ, via polarCoord + the 1-D s=r²
-- Jacobian change of variables. Foundational triple; entry slice of the route
-- discharging `fs_moment_pushforward_uniform`.
/-- info: 'CSD.LF4.gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2

/-- info: 'CSD.LF4.expHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expHalf

/-- info: 'CSD.LF4.sqNorm_map_gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sqNorm_map_gaussian2

-- Plan B Part 2, Slice 2 (L5.2): block product = independence.
-- `gaussian2` is the product of two 1-D standard Gaussians, and the joint law of
-- the two block squared-norms factors as `expHalf × expHalf` (the independence
-- statement; the product measure carries it). Foundational triple.
/-- info: 'CSD.LF4.gaussian2_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2_eq_prod

/-- info: 'CSD.LF4.blockSqNorm_map_gaussian2_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussian2_prod

-- General-N DH Slice C (Part 2a): the N-fold block law. The joint law of the N
-- block squared-norms factors as Exp(1/2)^{⊗N} (Measure.pi_map_pi + Slice 1 per
-- block) — the independence statement at general N. Foundational triple.
/-- info: 'CSD.LF4.blockSqNorm_map_gaussianN_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussianN_pi

-- Plan B Part 2, Slice 3 (L5.3, the crux): the ratio map sends expHalf × expHalf
-- to uniform on (0,1). 2-D change of variables through the diffeo Ψ(T,S) =
-- (T·S,(1−T)·S) (Jacobian det = S), with the radial S-integral collapsing to 1.
-- Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_const

-- General-N DH Slice D.1: the radial moment ∫⁻_{S>0} Sⁿ e^{−S/2} = 2^{n+1}·n!
-- (Γ(n+1)=n!), the normalisation the post-substitution S-integral collapses to in
-- the Gamma→Dirichlet change of variables. Generalises lintegral_radial_const
-- (n=1). Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_moment

-- General-N DH Slice D.3 (the crux/gate): the Jacobian determinant of the
-- stick-breaking substitution Ψ_{M+1} is S^M. The bordered matrix (S·I block +
-- border) via the row operation "add all castSucc rows into the last" (det
-- invariant, psiMat_col_sum) → two-block-triangular. The genuine general-N content
-- (no direct Mathlib lemma). Foundational triple.
/-- info: 'CSD.LF4.psiMat_col_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_col_sum

/-- info: 'CSD.LF4.psiMat_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_det

-- General-N DH Slice D.2: the stick-breaking diffeo Ψ_N + its Fréchet derivative.
-- hasFDerivAt_PsiN (componentwise via hasFDerivAt_pi; derivative = toLin' psiMat)
-- and psiFDerivN_det = (y last)^M (LinearMap.det_toLin' + psiMat_det). Foundational
-- triple.
/-- info: 'CSD.LF4.hasFDerivAt_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hasFDerivAt_PsiN

/-- info: 'CSD.LF4.psiFDerivN_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDerivN_det

-- General-N DH Slice D.5c (capstone): the ratio map sends Exp(1/2)^{⊗N} to the
-- Dirichlet(1,…,1) law — M! times uniform on the open simplex (free coords). The
-- general-N analogue of ratioSqNorm_map_expHalf_prod; the genuine general-N DH
-- content, composing D.1-D.5b. Foundational triple. Closes Slice D.
/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_pi

-- General-N DH Slice D.4: Ψ_N is a bijection domainN (open simplex × Ioi 0) →
-- posQuadrant. PsiN_sum (∑ᵢ Ψ_N(y)ᵢ = S, the inverse-map crux), injOn_PsiN,
-- image_PsiN. Foundational triple.
/-- info: 'CSD.LF4.PsiN_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.PsiN_sum

/-- info: 'CSD.LF4.injOn_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.injOn_PsiN

/-- info: 'CSD.LF4.image_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.image_PsiN

/-- info: 'CSD.LF4.psiFDeriv_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDeriv_det

/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_prod

-- Plan B Part 2, Slice 4 (assembly + discharge): `fs_moment_pushforward_uniform`
-- (the qubit Duistermaat–Heckman fact) is now a THEOREM, not an axiom. The bridge
-- `regroup4∗ (pi gaussianReal) = gaussian2 × gaussian2` (finSumFinEquiv reindex),
-- the moment marginal `Tpi∗ (pi gaussianReal) = uniform`, and the discharge all
-- depend only on the foundational triple.
/-- info: 'CSD.LF4.regroupPi_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.regroupPi_map

/-- info: 'CSD.LF4.moment_marginal_uniform_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.moment_marginal_uniform_pi

/-- info: 'CSD.LF4.fs_moment_pushforward_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform

-- Now foundational-triple-only (the DH input is discharged); previously these
-- carried `fs_moment_pushforward_uniform` as an axiom.
/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit_uncond

/-- info: 'CSD.LF4.qubit_born_frequency_convergence_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence_uncond

-- General-N DH Slice E (bridge): the per-block squared-norm map sends the ℝ^{N×2}
-- standard Gaussian to Exp(1/2)^{⊗N}, via the product-index curry + Measure.pi_map_pi
-- + the single-block fact gBlock_map_pi. Bypasses Slice C. Foundational triple.
/-- info: 'CSD.LF4.blockSqNormCurry_map_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNormCurry_map_pi

-- General-N DH Slice E (headline): the free-coordinate moment map ratioN ∘ momentMap
-- pushes the genuine Fubini–Study measure on ℂℙ^M to M! · uniform on the open simplex
-- (the joint Dirichlet(1,…,1) law). The general-N analogue of fs_moment_pushforward_uniform
-- (the qubit could give only the scalar Beta marginal). Foundational triple; no Busch.
/-- info: 'CSD.LF4.fs_moment_joint_dirichlet_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_joint_dirichlet_N

-- General-N DH Slice E (Born lift). E4a: the Duistermaat–Heckman volume law on Σ
-- (μ_FS of a moment region = M!·its Lebesgue volume). E4b: the standard simplex has
-- volume (M!)⁻¹ (forced by μ_FS being a probability measure). E4c: Born weight =
-- FS volume ratio of the i-th barycentric region, for the N-1 free coordinates,
-- now UNCONDITIONAL (the qubit h_uniform is the proved headline). Foundational triple;
-- no busch_effect_gleason.
/-- info: 'CSD.LF4.fs_volume_eq_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_volume_eq_dirichlet

/-- info: 'CSD.LF4.volume_openSimplexFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.volume_openSimplexFree

/-- info: 'CSD.LF4.fs_born_volume_ratio_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N

-- Apex coordinate (the dropped vertex, index M): the affine apex map (det = 1 - ∑b
-- = b_last via det_one_sub_mul_comm) closes the last Born coordinate. With
-- fs_born_volume_ratio_N this covers all N coordinates. Foundational triple.
/-- info: 'CSD.LF4.fs_born_volume_ratio_N_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_apex

-- General-N Busch-free capstone: i.i.d. trials from μ_FS on ℂℙ^M, empirical frequencies
-- of the N barycentric Born regions → the Born weights ‖⟨eᵢ,ψ⟩‖² jointly a.s. The Born
-- values come from fs_born_volume_ratio_N(_apex) (the volume route), so the chain is
-- foundational-triple-only — NO busch_effect_gleason. The general-N analogue of
-- qubit_born_frequency_convergence_uncond; the headline empirical payoff.
/-- info: 'CSD.LF4.born_frequency_convergence_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N

-- HY-5 (BornFlowLinkage): the Born-side sigmaFlow fix. The general-N Born capstone, now on trials
-- EVOLVED by the sector's own deterministic flow Φ_t = (unitaryFlowSetup …).flow t, converging to
-- the Born weights. The flow's Liouville-preservation (flow_preserves_volume = U(N)-invariance of
-- μ_FS) pins the evolved law back to μ_FS — the substrate flow is now consumed on the Born side.
-- Still foundational-triple; weights-from-flow (SO-1) untouched.
/-- info: 'CSD.LF4.unitaryFlowSetup_born_frequency_evolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_born_frequency_evolved

/-- info: 'CSD.LF4.povm_born_frequency_volume_evolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_evolved

-- N=2 consistency cross-check: the qubit fs_moment_pushforward_uniform is kernel-derived
-- from the general-N fs_moment_joint_dirichlet_N (M:=1). Machine-confirms the general-N
-- statement faithfully generalises the independently-proved qubit result. Foundational triple.
/-- info: 'CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet

-- The ofKählerPreparation constructor: a concrete LF3.PureSingletPreparation
-- on the non-trivial-fibre compact-Kähler instance. bridge_op_p is proved
-- Busch-free via born_rank_one_direct + the carving identity kMuPsi_kRegion,
-- so the constructor stays foundational-triple only.
/-- info: 'CSD.LF4.ofKählerPreparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation

-- Applying the LF3 chain capstone to the concrete prep gives a non-vacuous
-- empirical statement. Now foundational-triple-only (2026-06-02): the chain bridge
-- was re-routed off Busch onto the volume-ratio Born step, so this end-to-end
-- ontic capstone no longer cites busch_effect_gleason.
/-- info: 'CSD.LF4.ofKählerPreparation_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation_singlet_frequency_convergence

-- SL-2 (2026-07-09): the singlet preparation rebuilt over the Φ≠id sector kSectorDataFlow (Φ=kFlow),
-- the ENTANGLED analogue of D1c-1. The LF1 preEvent = Φ⁻¹'Ω, so with Φ=kFlow the capstone scores the
-- flow-EVOLVED trials (kFlow∘X)⁻¹'kRegion, and kFlow's μψ-preservation (kFlow_measurePreserving_muPsi)
-- is load-bearing (bridge_op_p: kMuPsi (kFlow⁻¹'kRegion) = kMuPsi kRegion = P_st). Still foundational-triple.
/-- info: 'CSD.LF4.kFlow_measurePreserving_muPsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_measurePreserving_muPsi

/-- info: 'CSD.LF4.ofKählerPreparationFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparationFlow

/-- info: 'CSD.LF4.ofKählerPreparationFlow_flow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparationFlow_flow_frequency_convergence

-- LF4 §14 discharge (projector observables, single-qubit Stern-Gerlach):
-- the Hilbert ↔ ontic-measure identity, foundational triple only.
/-- info: 'CSD.LF4.sg_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_observable_correspondence

-- LF4 §14 general-N discharge for DIAGONAL observables (2026-07-22): the Hilbert expectation of
-- diagonal(lam·) equals the eigenvalue-weighted sum of the ontic Born-region volumes, at all N and
-- all real eigenvalues. Foundational triple only; carving-free, Gleason-free.
/-- info: 'CSD.LF4.observable_correspondence_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.observable_correspondence_diagonal

-- LF4 §14 general-N diagonal observable, canonical INTEGRAL form (2026-07-22): ⟨ψ,Aψ⟩ = ∫ A_ontic dμ
-- with A_ontic = ∑ₖ lam k · 𝟙_{Rₖ} an explicit measurable Σ-function. Foundational triple only.
/-- info: 'CSD.LF4.observable_correspondence_diagonal_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.observable_correspondence_diagonal_integral

-- LF4 §14 GENERAL (non-diagonal) self-adjoint observable (2026-07-22): via spectral unitary transport
-- of the state (φ = Uᴴψ), ⟨ψ,Aψ⟩ = ∑ₖ λₖ·vol(bornRegionN φ k) = ∫ aOntic φ λ dμ. Foundational triple.
/-- info: 'CSD.LF4.hermitian_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_observable_correspondence

/-- info: 'CSD.LF4.hermitian_observable_correspondence_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_observable_correspondence_integral

-- LF4 §14 STATES obligation (pure states / rank-one projectors, 2026-07-23): ‖⟨Φ,ψ⟩‖² = an ontic
-- Fubini–Study volume, via a unitary sending e₀ ↦ Φ. Foundational triple only.
/-- info: 'CSD.LF4.pure_state_born_prob_eq_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pure_state_born_prob_eq_volume

-- LF4 §14 STATES obligation, MIXED-STATE / density-operator case (2026-07-23): Tr(ρ·|φ⟩⟨φ|) =
-- ρ-eigenvalue-weighted sum of ontic Fubini–Study volumes of ρ's pure eigenstates. Foundational triple.
/-- info: 'CSD.LF4.mixed_state_born_eq_ensemble_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.mixed_state_born_eq_ensemble_volume

-- The non-vacuous LF3-chain Stern-Gerlach capstone (N = 2 analog of
-- ofKählerPreparation_singlet_frequency_convergence). Foundational triple only.
/-- info: 'CSD.LF4.sg_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_frequency_convergence

-- LF4 §14.2 first step beyond projectors: Pauli observable σ·a via the
-- spectral-decomposition signed-indicator construction. Foundational triple only.
/-- info: 'CSD.LF4.pauliDot_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_observable_correspondence

-- LF4 §14.2 at N = 4: two-qubit Pauli observables on the singlet (covering
-- all 9 Mermin-Peres observables and the 4 Hardy single-qubit Paulis).
/-- info: 'CSD.LF4.sigmaDotLeft_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotLeft_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotRight_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotRight_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotJoint_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotJoint_observable_correspondence

-- Hardy LF3-chain capstones: the four Hardy probability constraints lifted to
-- ontic frequency-convergence theorems on the Hardy-state Kähler preparation.
-- Headline pin (positive coincidence) + load-bearing zero (A'=+1, B'=+1).
/-- info: 'CSD.LF4.hardy_freq_convergence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_AB

/-- info: 'CSD.LF4.hardy_freq_convergence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_A'_B'

-- Hardy §14 observable correspondence (Hilbert ↔ ontic): closes the QM ↔ LF4
-- amplitude loop. Headline pin (the positive-coincidence Hilbert ↔ ontic match)
-- + the load-bearing zero observable correspondence.
/-- info: 'CSD.LF4.hardy_observable_correspondence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_AB

/-- info: 'CSD.LF4.hardy_observable_correspondence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_A'_B'

-- LF4 §14.2 general N×N spectral expansion of the Hilbert expectation.
-- The Hilbert-side spectral identity ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²
-- for any Hermitian A and any state ψ — unlocks variance / uncertainty
-- ontic correspondences beyond the projector / ±1-eigenvalue case.
/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion

/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion_re

-- LF4 §14.2 ontic-side multi-region spectral carving (Phase A foundation
-- + Phase C carving identity + Phase D integration headline).
/-- info: 'CSD.LF4.fibreShiftedArc_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fibreShiftedArc_volume

/-- info: 'CSD.LF4.diracProd_spectralRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.diracProd_spectralRegion

/-- info: 'CSD.LF4.integral_spectralOntic_eq_inner_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOntic_eq_inner_re

-- LF4 §14.2 variance: Hilbert-side norm-squared, spectral variance,
-- Hilbert ↔ spectral identity, and ontic ↔ Hilbert variance correspondence.
/-- info: 'CSD.LF4.hilbert_norm_sq_apply_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hilbert_norm_sq_apply_hermitian

/-- info: 'CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_variance

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff

-- LF4 §14.2 Robertson uncertainty on the Kähler instance: ontic-variance
-- bridge to QM variance, and the headline ontic-variance Robertson bound.
/-- info: 'CSD.LF4.QM_variance_eq_spectralVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.QM_variance_eq_spectralVariance

/-- info: 'CSD.LF4.kahler_robertson_ontic_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kahler_robertson_ontic_variance

-- LF4 §14.2 concrete instance: σ_x, σ_y Robertson saturation on |0⟩.
/-- info: 'CSD.LF4.pauli_xy_robertson_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauli_xy_robertson_saturation

-- LF4 §14.2 parametric: Robertson for σ·â, σ·b̂ on |0⟩, geometric form.
/-- info: 'CSD.LF4.pauliDot_robertson_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_robertson_zPlus

-- The pure-state ontic Born capstone composes LF1 frequency convergence with the
-- LF2 operational Born derivation. Since `busch_effect_gleason` was discharged
-- (2026-07-21), it now stands on the foundational triple alone.
/-- info: 'CSD.LF4.ontic_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ontic_born_frequency

/-- info: 'CSD.LF4.NaimarkDilation.born_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.NaimarkDilation.born_transfer

-- POVM tranche P.3a (block decomposition): the POVM Born weight is the sum, over
-- the i-th ancilla block, of the dilated computational-basis (rank-1) Born
-- weights — each of which the general-N result reads as a Fubini-Study volume.
-- Foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_block_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_block_sum

-- POVM tranche P.3b (FS-volume identification): the POVM Born weight is the sum,
-- over the i-th ancilla block, of the genuine Fubini-Study typicality volumes of
-- the dilated barycentric cells on Σ' = ℂℙ^{N·|ι|−1}. Composes P.3a with the
-- general-N Born = FS-volume result through the reindex isometry. Carving-free,
-- Gleason-free (no busch_effect_gleason); foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_dilated_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_dilated_volume

-- POVM tranche P.4 (empirical capstone): i.i.d. Fubini-Study trials on the dilated
-- Σ' have the i-th POVM outcome's empirical frequency (the block sum of dilated
-- cell frequencies) converge a.s. to the POVM Born weight pᵢ(ψ). The empirical →
-- Born chain for a general POVM, carving-free and Gleason-free. Foundational triple.
/-- info: 'CSD.LF4.povm_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume

-- POVM tranche P.5 (existence): the canonical Naimark dilation built from the CFC
-- square roots √Eᵢ inhabits NaimarkDilation P for every POVM, making the Phase-1
-- POVM Born = Kähler-volume results unconditional (no longer needing a supplied
-- dilation). Foundational triple only — the CFC sqrt and isometry/pullback proofs
-- add no axioms.
/-- info: 'CSD.LF4.naimarkV_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_isom

/-- info: 'CSD.LF4.naimarkV_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_pullback

/-- info: 'CSD.LF4.canonicalNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.canonicalNaimark

-- LF5-D part 1 (the unconditional Born-region engine): the general-N Born =
-- FS-volume results and the POVM tranche wrappers with the hpos genericity
-- hypothesis retired — valid for every unit ψ, vanishing amplitudes included.
-- Per-cell dichotomy: positive cells by the closed-simplex subset argument,
-- zero cells by the det-0 null image + the joint Dirichlet law (the cells
-- genuinely collapse to FS-null sets; no carving). Additive over the audited
-- originals in MomentBornN / BornFrequencyN / POVMVolume. Carving-free,
-- Gleason-free; foundational triple only.
/-- info: 'CSD.LF4.fs_born_volume_ratio_N_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_uncond

/-- info: 'CSD.LF4.fs_born_volume_ratio_N_apex_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_apex_uncond

/-- info: 'CSD.LF4.bornRegion_fs_measure_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornRegion_fs_measure_uncond

/-- info: 'CSD.LF4.born_frequency_convergence_N_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N_uncond

/-- info: 'CSD.LF4.povm_born_eq_dilated_volume_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_dilated_volume_uncond

/-- info: 'CSD.LF4.povm_born_frequency_volume_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_uncond

/-- info: 'CSD.LF4.fsTrial_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fsTrial_law

/-- info: 'CSD.LF4.fsTrial_pairwise_indepFun_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fsTrial_pairwise_indepFun_indicator

/-- info: 'CSD.LF4.born_frequency_convergence_N_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N_canonical

-- LF5-F: bornRegion pairwise disjointness, the per-microstate outcome map, and
-- the outcome-frequency capstone (single union event per pointer, not a sum of
-- cell frequencies). Closes the owed-since-aeece86 outcome function. The cells
-- are the same ψ-indexed moment-subdivision cells (no carving); Φ = id (D1).
-- Foundational triple throughout; Gleason-free.
/-- info: 'CSD.LF4.bornRegion_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornRegion_pairwiseDisjoint

/-- info: 'CSD.LF4.bornOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornOutcome_preimage_some

/-- info: 'CSD.LF4.bornOutcome_ae_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornOutcome_ae_isSome

-- Volume-series canonical coverage (2026-06-15): the trial-witness discharge,
-- previously wired into only three headlines (born_frequency_convergence_N,
-- measurement_flow_born_frequency, measurement_flow_outcome_frequency), is now
-- applied to EVERY remaining volume-frequency headline. Each _canonical form is
-- a bare term-mode application of its parent with the abstract trial bundle
-- discharged at the in-tree FS coordinate process (fsTrialMeasure / fsTrial):
-- conclusions verbatim, hypothesis sets now Lean-inhabited rather than merely
-- classically satisfiable. The LF4 POVM headline lives in TrialWitness.lean
-- (import-direction constraint POVMVolume → BornRegionUncond → TrialWitness);
-- the Empirical/CSD headlines are centralised in
-- Empirical/CSD/VolumeCanonical.lean. Coverage/completeness, not new
-- mathematics: measure-theoretic existence of the i.i.d. sampling law only; the
-- physical FS-typical preparation reading remains the LF1 typicality / sector posit (SO-1).
-- Foundational triple throughout; Gleason-free.

/-- info: 'CSD.LF4.povm_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_canonical

-- HatBox (context-fixed qubit measurement infra / A7, 2026-07-26): the Archimedes hat-box, the
-- single-axis crux integral. hatBox_moment: the Fubini-Study average over ℂℙ¹ of the Bloch height
-- |λ·n| = |2·momentMap - 1| is 1/2. NOT raw S² integration — reduces to the proved moment coordinate
-- being Uniform[0,1] (fs_moment_pushforward_uniform) + the 1D integral ∫_{[0,1]}|2t-1|=1/2
-- (integral_abs_two_mul_sub_one). The foundation for the qubit context-fixed hemisphere+spread proof.
/-- info: 'CSD.LF4.hatBox_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.hatBox_moment

/-- info: 'CSD.LF4.integral_abs_two_mul_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.integral_abs_two_mul_sub_one

-- spread-density normalisation (context-fixed qubit, 2026-07-26): ρ = 4·max(2·momentMap−1,0) (Bloch
-- 4(m·λ)₊) integrates to 1 against μ_FS (spreadDensity_normalized) via the moment coordinate Uniform[0,1]
-- + integral_max_two_mul_sub_one_zero (∫_{[0,1]}max(2t−1,0)=1/4). The "½"-term ingredient of §2.
/-- info: 'CSD.LF4.spreadDensity_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.spreadDensity_normalized

-- QubitReflection (context-fixed qubit, brick 1, 2026-07-26): the reflection identity — the C-term crux
-- of §2. reflect_sq_add: ‖⟨ψ,φ⟩‖² + ‖⟨ψ,R_nφ⟩‖² = 2cu + 2(1−c)(1−u), R_n φ = 2⟨n,φ⟩·n − φ. Pure ℂ²
-- linear algebra: completeness of {n,n^⊥} (`completeness`), Parseval (`parseval_vec`), parallelogram.
/-- info: 'CSD.LF4.reflect_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflect_sq_add

/-- info: 'CSD.LF4.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.completeness

/-- info: 'CSD.LF4.parseval_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.parseval_vec

-- BlochProjection (context-fixed qubit foundation, 2026-07-26): general-axis Born weight
-- blochProj a p = |⟨a,rep p⟩|²/‖rep p‖² — shared foundation for the hemisphere cut (blochProj n) and
-- the spread density (blochProj ψ). blochProj_smul: U(N)-equivariance; blochProj_measurable: Borel.
/-- info: 'CSD.LF4.blochProj_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_smul

/-- info: 'CSD.LF4.blochProj_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_measurable

/-- info: 'CSD.LF4.blochProj_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_mk

-- AxisBridge (context-fixed qubit, 2026-07-26): general axis ↦ reference axis for μ_FS integrals.
-- blochProj_integral_bridge: ∫ f(blochProj n p) dμ_FS = ∫ f(momentMap p 0) dμ_FS (unit n), via
-- fubiniStudyMeasure_smul_invariant. Lifts hatBox_moment/spreadDensity_normalized to any axis:
-- hatBox_axis (∫|2·blochProj n−1|=½), spreadDensity_normalized_axis (∫4(2·blochProj n−1)₊=1).
/-- info: 'CSD.LF4.blochProj_integral_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_integral_bridge

/-- info: 'CSD.LF4.hatBox_axis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.hatBox_axis

/-- info: 'CSD.LF4.spreadDensity_normalized_axis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.spreadDensity_normalized_axis

-- QubitDipole (context-fixed qubit, brick 3 infra, 2026-07-26): R_n = 2|n⟩⟨n|−I as a Hermitian
-- unitary (reflMat_mem_unitaryGroup, reflU), its action reflMat_toEuclideanLin (R_n w = 2⟨n,w⟩•n−w),
-- and blochProj_refl_fixes (R_n fixes the n-coordinate). The dipole change-of-variables engine.
/-- info: 'CSD.LF4.reflMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflMat_mem_unitaryGroup

/-- info: 'CSD.LF4.reflMat_toEuclideanLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflMat_toEuclideanLin

/-- info: 'CSD.LF4.blochProj_refl_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_refl_fixes

-- Dipole (context-fixed qubit, brick 3, 2026-07-26): D = ∫ rsign(2·blochProj n−1)(2·blochProj ψ−1)
-- dμ_FS = (2c−1)/2, c=|⟨n,ψ⟩|². Via R_n reflection (μ_FS-preserving, fixes n) + reflect_sq_add
-- (reflSum) linearising the paired density + hatBox_axis. The dipole term of the qubit Born rule.
/-- info: 'CSD.LF4.dipole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.dipole

/-- info: 'CSD.LF4.reflSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflSum

-- CrossTerm (context-fixed qubit, brick 2, 2026-07-26): T = ∫ rsign(2·blochProj n−1)|2·blochProj ψ−1|
-- dμ_FS = 0 — the antipode symmetry (Haar right-mult by the e₀↔e₁ swap flips both Born coords via the
-- ONB-complement Parseval flip inner_unitary_flip), so T = −T. The monopole cross-term vanishing.
/-- info: 'CSD.LF4.crossTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.crossTerm

/-- info: 'CSD.LF4.inner_unitary_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.inner_unitary_flip

-- ★ QubitBorn (context-fixed qubit, brick 5 = THE PAYOFF, 2026-07-26): the qubit Born rule derived
-- from the CSD spread density + context-fixed hemisphere against the Fubini–Study typicality measure:
-- ∫ ½(1+rsign(2·blochProj n−1))·4(2·blochProj ψ−1)₊ dμ_FS = |⟨n,ψ⟩|². Assembles the four component
-- integrals (∫(2s−1)=0, ∫|2s−1|=½ hat-box, dipole=(2c−1)/2, crossTerm=0) = c. Foundational-triple.
/-- info: 'CSD.LF4.qubitBorn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.qubitBorn

/-- info: 'CSD.LF4.blochProj_integral_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_integral_half

-- A1 ONTIC-SECTOR ROW, item (b) (2026-08-25, LF4/LiouvilleUnique.lean): THE SECTOR MEASURE IS
-- FORCED, NOT CHOSEN.
-- ⚠️ The gap was NARROWER than the BACKLOG row implied.  KahlerOnticSetup.liouvilleMeasure is NAMED
-- Liouville but only TYPED as Measure Sigma + liouville_isProbability -- nothing in the structure
-- forced the sector's measure to be canonical, so kMuL = mu_FS (x) Haar read as a CHOICE.
-- ★★ kMuL_unique: kMuL p0 is the ONLY probability measure on CP^{N-1} x T^2 invariant under U(N) on
-- the base and T^2 on the fibre.  Forced by the symmetry, not selected.
-- ★ WHY THIS IS THE RIGHT READING OF "LIOUVILLE".  The textbook definition is the top exterior power
-- of the Kahler form, and it is NOT available and will not be: connectivity-manifest L1 records that
-- manifold residual (d-omega = 0, top-power volume identity) as blocked on Mathlib, Q8 rated XL.
-- Symmetry-uniqueness is the formalisable content of the SAME fact -- on a homogeneous space the
-- Liouville measure IS the invariant one -- and it is the reading the corpus already uses for the
-- base (invariant_measure_uniqueness_cpn).  This extends it to the whole fibred sector.
-- Two independent halves joined by Measure.prod_eq (rectangles suffice):
--   FIBRE -- fst_prod_volume_of_fibreShift_invariant.  For measurable A, the pushforward of
--     mu.restrict (A x univ) to the fibre is a finite translation-invariant measure on T^2.
--     ★ Because T^2 is COMPACT, isAddInvariant_eq_smul_of_compactSpace pins it to a multiple of Haar
--     with NO regularity side conditions.  Fibre compactness is LOAD-BEARING here, not decoration --
--     and it is exactly what TorusFibre/GlobalRecordClosure bought in July when the record layer
--     moved off the non-compact R fibre.  The scalar is read off at univ.
--   BASE -- the marginal is U(N)-invariant, so invariant_measure_uniqueness_cpn applies and total
--     mass one fixes the multiplier.
-- ⚠️ SCOPE: forced GIVEN the symmetry group.  This does NOT derive the group, and Sigma stays the
-- floor (deriving Sigma is a non-question, CSD-CHARTER).  It also does NOT touch the record layer's
-- other open item: no H_int(M) produces the basins.
/-- info: 'CSD.LF4.fst_prod_volume_of_fibreShift_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF4.fst_prod_volume_of_fibreShift_invariant

/-- info: 'CSD.LF4.kMuL_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF4.kMuL_unique

end CSD.Tests.AxiomAudit
