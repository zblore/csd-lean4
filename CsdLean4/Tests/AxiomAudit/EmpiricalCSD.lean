/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: EmpiricalCSD

**Category:** Special (axiom-posture regression pins; G9 split part).

Empirical/CSD pins (transported CSD readings, volume series, gates, contextuality).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.EmpiricalCSD`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


/-! ### Empirical predictions (Bell family, Phase A1-A5)

All Phase A1-A5 predictions cite only the foundational triple: the LF3
content they re-export does too (LF3 algebraic core in `Singlet/Kernel.lean`
is axiom-clean), and the new CHSH-at-Tsirelson computation is pure
arithmetic. -/

/-- info: 'CSD.Empirical.Bell.correlation_eq_neg_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.correlation_eq_neg_dot

/-- info: 'CSD.Empirical.Bell.no_signalling_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_alice

/-- info: 'CSD.Empirical.Bell.no_signalling_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_bob

/-- info: 'CSD.Empirical.Bell.singlet_marginal_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_alice

/-- info: 'CSD.Empirical.Bell.singlet_marginal_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_bob

/-- info: 'CSD.Empirical.Bell.chsh_classical_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_classical_bound_violated

/-- info: 'CSD.Empirical.Bell.chsh_singlet_at_optimal_angles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_at_optimal_angles

/-- info: 'CSD.Empirical.Bell.chsh_singlet_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_tsirelson_bound

/-- info: 'CSD.Empirical.Bell.chsh_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_inner_bound

/-- info: 'CSD.Empirical.Bell.chsh_qm_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_qm_tsirelson_bound

-- Hong-Ou-Mandel (two-photon interference, 2026-07-27). Two identical bosons entering opposite
-- ports of a 50:50 beamsplitter (the corpus's own qmH) are NEVER found in different output ports:
-- hom_coincidence_zero (the DIP, = 0) / hom_bunching_one (= 1, they always leave together). The
-- whole effect is one matrix identity -- bsTwo_bosonIn, that H·σx·H is DIAGONAL, so the two
-- exchange paths cancel. The point is that this is EXCHANGE SYMMETRY, not optics: with the SAME
-- beamsplitter and the SAME input ports, distinct_coincidence_half gives 1/2 for distinguishable
-- particles (the classical baseline the dip drops below) and fermion_coincidence_one gives 1 --
-- Pauli anti-bunching, the exact opposite. hom_exchange_trichotomy is the 0 < 1/2 < 1 capstone;
-- inputs_normalised confirms all three inputs are unit vectors, so the comparison is honest.
-- Two-particle sector of two modes only -- no Fock space, no creation operators (CV/ApproxCCR
-- shows a finite model cannot carry the CCR exactly); HOM's content lives in the two-photon
-- amplitude, so this is the full effect, not a truncation of it.
/-- info: 'CSD.Empirical.HOM.bsTwo_bosonIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.bsTwo_bosonIn

/-- info: 'CSD.Empirical.HOM.hom_coincidence_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_coincidence_zero

/-- info: 'CSD.Empirical.HOM.hom_bunching_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_bunching_one

/-- info: 'CSD.Empirical.HOM.distinct_coincidence_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.distinct_coincidence_half

/-- info: 'CSD.Empirical.HOM.fermion_coincidence_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.fermion_coincidence_one

/-- info: 'CSD.Empirical.HOM.hom_dip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_dip

/-- info: 'CSD.Empirical.HOM.hom_exchange_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_exchange_trichotomy

/-- info: 'CSD.Empirical.HOM.inputs_normalised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.inputs_normalised

-- THE FIRST DYNAMICAL EMPIRICAL ENTRY (2026-08-02, Empirical/CSD/SequentialMeasurement.lean).
-- Every other empirical entry exercises the KINEMATIC Born machinery; this one exercises the
-- MEASUREMENT DYNAMICS -- the calibrated-swap witness -- and two textbook empirical facts fall out
-- as consequences rather than separate posits:
-- ★★ csd_repeatability (+ _same/_other): measure in the computational basis, obtain i, measure
-- again in the SAME basis -- outcome i recurs with probability 1, every other outcome 0. Von
-- Neumann repeatability, DERIVED from swap_luders_born + momentMap_vertex (the follow-up context's
-- rate at the collapsed vertex is the vertex's indicator).
-- ★ csd_sequential_born: after outcome i, follow-up statistics for ANY context field c' are the
-- COLLAPSED state's Born weights c'.rate [e_i] -- the preparation has left the statistics. The
-- Luders update as an empirical prediction.
-- ⚠️ Rank-one computational-basis first measurement (the swap witness's scope); hpos carried as a
-- hypothesis (conditioning on a null outcome is undefined, as it should be); inherits the witness's
-- calibration-posit and Hamiltonian-origin scope notes.
/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_sequential_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_sequential_born

/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability

/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability_same

-- KCBS PENTAGON BORN WEIGHTS AS KAHLER VOLUMES (2026-08-02,
-- Empirical/CSD/Contextuality/KCBSVolume.lean) -- closing the audit's KCBS gap, the last flagship
-- test without a CSD twin.
-- The representative pentagon context {kv 0, kv 1} is completed to a projective frame by the CROSS
-- PRODUCT kv 0 x kv 1 (orthogonal to both by dot_self_cross/dot_cross_self, unit by the Lagrange
-- identity cross_dot_cross: 1*1 - 0^2 = 1), complexified via the transport c3_inner -- every
-- orthonormality fact PULLED from the QM side's real dot products (kv_orth, kv_unit), nothing
-- re-proved. kcbsContextBasis is the resulting OrthonormalBasis; the engine
-- context_born_frequency_volume instantiates at it: every ray's context-dependent Born weight is
-- the a.s. frequency limit of its barycentric Born region on the fixed ontic Sigma = CP^2 -- an FS
-- typicality volume. kcbs_pentagon_weight: at the apex preparation the ray-0 weight is the pentagon
-- number 1/sqrt(5) -- the quantity whose five-fold sum sqrt(5) violates the noncontextual bound 2
-- (kcbs_quantum_violation). The _canonical form discharges the trial bundle on fsTrialMeasure.
-- ⚠️ One representative context built (KS18Volume discipline): the other four are identical
-- instantiations, orthogonality already certified for all five adjacencies by kv_orth. Realisation
-- not derivation; Phi = id; the inequality itself stays at the QM layer.
/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_pentagon_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_pentagon_weight

/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume_canonical

-- THE QUANTUM ERASER TWIN, VIA THE RECORD ROUTE (2026-08-02, Empirical/CSD/QuantumEraserVolume.lean).
-- The eraser's signature is a VANISHING conditional probability (the dark fringe), which the
-- Duistermaat-Heckman route's ORIGINAL lemmas could not state (hpos) -- corrected 2026-08-02: the _uncond engine (2026-06-11) does state zeros; the record route stands by choice. Like
-- HongOuMandelVolume, this twin lives on the record layer, where a zero rate is a zero-width cell:
-- ★ eraser_fringe_typicality: the full-visibility conditioned fringe (1 + c·cos φ)/2 is a fibre
-- typicality volume at EVERY phase, boundary values included.
-- ★ eraser_dark_typicality_zero (+ _record_null, _measurement_zero): at φ = π the dark cell is
-- exactly null -- no microstate of Σ produces a dark-port detection; nothing cancels across runs.
-- ★ eraser_dark_basin_null: the same zero at the v1.0 context-fixed basin layer -- at the dark point
-- the conditioned state IS the vertex [e₁] (mk_eraserOut_pi), and the dark basin's fibre arc has
-- width 0 there (globalBasin_prob + momentMap_vertex, the repeatability lemmas).
-- eraserOut_rate_conditional ties the rates to the QM module: joint over marker marginal, both
-- sides QM-side quantities -- the conditioned state is derived, not asserted.
-- ⚠️ Realises the conditioned STATISTICS ontically; the conditioning PROCESS (marker measurement as
-- swap-witness dynamics on the composite) needs the unitary-covariance extension (BACKLOG).
/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_fringe_typicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_fringe_typicality

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_typicality_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_typicality_zero

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_record_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_record_null

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_basin_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_basin_null

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraserOut_rate_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraserOut_rate_conditional

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_eve_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_eve_selector_born

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_wrong_basis_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_wrong_basis_bob

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_no_disturbance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_no_disturbance

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_faithful

-- B92 AND WIESNER SEQUENTIAL TWINS (2026-08-02, Empirical/CSD/Crypto/{B92,Wiesner}Sequential.lean).
-- Instantiations of the BB84Sequential engine, recorded as such -- the dynamical fact is the same
-- calibrated-swap composition, re-read on each protocol's semantics:
-- B92: ★ b92_honest_false_click_null -- unambiguity as a NULL BASIN (a |+> carrier has a zero-width
-- conclusive-bit-0 arc; the eraser-dark-fringe shape); ★ b92_eve_false_click -- after Eve's
-- Z-intercept the false-click basin is exactly 1/2 whatever she recorded; ★ b92_eve_detectable --
-- the strict contrast (intercept raises false clicks strictly above the honest zero).
-- Wiesner: ★ wiesner_forge_x_pass_half / _caught_half -- the measure-resend counterfeit passes a
-- conjugate-basis position with probability exactly 1/2 (collapse = pushforward theorem);
-- ★ wiesner_forge_z_invisible -- matching basis = repeatability, the forger copies for free (the
-- mint's secret basis IS the security); wiesner_rate_eq_verifyProb ties the ontic pass rate to the
-- QM module's verifyProb; the 3/4 = (1/2)(1) + (1/2)(1/2) per-position average is the (3/4)^n
-- counterfeiting value -- ⚠️ ATTAINED by measure-resend here; optimality (Molina-Vidick-Watrous
-- 2012) out of scope. Both inherit the calibrated-swap scope notes.
/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_honest_false_click_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_honest_false_click_null

/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_eve_false_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_eve_false_click

/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_eve_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_eve_detectable

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_x_pass_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_x_pass_half

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_z_invisible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_z_invisible

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_rate_eq_verifyProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_rate_eq_verifyProb

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_primal_wrong_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_primal_wrong_basis

-- Hong-Ou-Mandel CSD twin (2026-07-27): the dip as an ONTIC IMPOSSIBILITY, not a statistical
-- cancellation. hom_coincidence_typicality_zero -- the coincidence cell's fibre typicality is
-- EXACTLY 0, so the set of microstates yielding a coincidence is NULL; there is nothing in Sigma
-- to cancel. Same at the record level (hom_coincidence_record_null: the P5 record event "recorded
-- a coincidence" is a null subset of Sigma) and as a Measurement (hom_coincidence_measurement_zero).
-- hom_bunch_typicality_half confirms the weight went to the two bunched outcomes (1/2 each), so
-- the vanishing is a genuine redistribution rather than a normalisation artefact. The occupation
-- state is DERIVED from the QM module (homOut_eq_bsTwo_bosonIn: |20>/|02> are the diagonal entries
-- of bsTwo bosonIn and the |11> amplitude is the symmetrised off-diagonal (S01+S10)/sqrt2), not
-- re-asserted. ARCHITECTURAL NOTE: this twin uses the RECORD LAYER, not the Duistermaat-Heckman
-- fs_born_volume_ratio_N / fsMeasure_bornRegionN route that every earlier ...Volume twin uses --
-- because those carry hpos (STRICTLY POSITIVE Born weights) and HOM's defining feature is a ZERO
-- amplitude. hpos is load-bearing there, not decorative: replaceMap_det b i = b i (Cramer), so a
-- zero weight makes the vertex-replacement map SINGULAR, puts b on the simplex boundary
-- (b in openSimplexFree fails) and breaks both the openness/measurability and volume-scaling steps.
-- volume_cdfCell has NO positivity hypothesis (a zero rate is just a zero-width cell), so the
-- record layer expresses the degenerate case the projective machinery cannot. Extending the DH
-- lemmas to the simplex boundary is an open item (specs/BACKLOG.md).
/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_typicality_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_typicality_zero

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_record_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_record_null

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_measurement_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_measurement_zero

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_bunch_typicality_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_bunch_typicality_half

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.homOut_eq_bsTwo_bosonIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.homOut_eq_bsTwo_bosonIn

-- CSD Volume twins (Born = Kähler typicality volume, 2026-07-27): LG survival cos²Δ and EV split 1/2
-- realised as Fubini–Study moment-sublevel volumes on ℂℙ¹ via fs_born_volume_ratio_qubit_uncond (DH).
/-- info: 'CSD.Empirical.CSDBridge.LeggettGargVolume.lg_survival_as_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.LeggettGargVolume.lg_survival_as_volume

/-- info: 'CSD.Empirical.CSDBridge.ElitzurVaidmanVolume.ev_split_as_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.ElitzurVaidmanVolume.ev_split_as_volume

/-! ### Empirical predictions (no-cloning, Phase B2) -/

/-- info: 'CSD.Empirical.NoCloning.no_cloning_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_cloning_two_state

/-- info: 'CSD.Empirical.NoCloning.no_universal_cloner_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_universal_cloner_of_witness

/-- info: 'CSD.Empirical.NoDeleting.no_deleting_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_deleting_two_state

/-- info: 'CSD.Empirical.NoDeleting.no_universal_deleter_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_universal_deleter_of_witness

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_inner

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_nonorthogonal

/-- info: 'CSD.Empirical.QuantumMoney.quantum_money_unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.quantum_money_unforgeable

-- BB84 QKD security (Crypto/BB84.lean): intercept-resend QBER (¼ sifted-key error),
-- eavesdropping detectability (¼ > 0 baseline), and the non-orthogonality
-- disturbance root (⟨0|+⟩ = (√2)⁻¹ ≠ 0). All Born-grounded via ‖⟨a|b⟩‖²; the
-- intercept-resend error is a classical marginal over Eve's outcome (no collapse
-- operator). Full composable finite-key security stays out of scope (LF5 gate).
-- Foundational triple only.
/-- info: 'CSD.Empirical.BB84.bb84_qber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_qber

/-- info: 'CSD.Empirical.BB84.bb84_intercept_resend_wrong_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_intercept_resend_wrong_basis

/-- info: 'CSD.Empirical.BB84.bb84_intercept_resend_right_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_intercept_resend_right_basis

/-- info: 'CSD.Empirical.BB84.bb84_eavesdropping_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_eavesdropping_detectable

/-- info: 'CSD.Empirical.BB84.bb84_states_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_states_nonorthogonal

/-- info: 'CSD.Empirical.BB84.bb84_no_eavesdrop_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_no_eavesdrop_error_zero

/-- info: 'CSD.Empirical.BB84.bornProb_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_comm

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ket0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ket0

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ket1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ket1

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ketPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ketPlus

-- B92 QKD security (Crypto/B92.lean): the two-state protocol. Unambiguous-
-- discrimination structure (error-free conclusive events ⟨1|0⟩=⟨−|+⟩=0 + ½
-- conclusive rates) and the no-cloning security root (no universal cloner copies
-- both encoding states |0⟩, |+⟩). All Born-grounded via ‖⟨a|b⟩‖², reusing BB84's
-- Born layer. Full composable finite-key security stays out of scope (LF5 gate).
-- Foundational triple only.
/-- info: 'CSD.Empirical.B92.b92_no_perfect_eavesdrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_no_perfect_eavesdrop

/-- info: 'CSD.Empirical.B92.b92_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_nonorthogonal

/-- info: 'CSD.Empirical.B92.b92_unambiguous_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_unambiguous_one

/-- info: 'CSD.Empirical.B92.b92_unambiguous_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_unambiguous_zero

/-- info: 'CSD.Empirical.B92.b92_conclusive_rate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_conclusive_rate_one

/-- info: 'CSD.Empirical.B92.b92_conclusive_rate_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_conclusive_rate_zero

/-- info: 'CSD.Empirical.B92.b92_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_encode

/-- info: 'CSD.Empirical.Protocols.secure_emulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Protocols.secure_emulates

/-- info: 'CSD.Empirical.Uncertainty.robertson_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_core

/-- info: 'CSD.Empirical.Uncertainty.robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_uncertainty

/-! ### Empirical predictions (GHZ paradox, Phase D6 / Mermin all-or-nothing) -/

/-- info: 'CSD.Empirical.GHZ.ghz_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_norm

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xxx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xxx

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xyy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xyy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yxy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yxy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yyx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yyx

/-- info: 'CSD.Empirical.GHZ.no_lhv_assignment_for_ghz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.no_lhv_assignment_for_ghz

/-! ### Empirical predictions (Kochen-Specker, Phase D9 / Cabello 1996 18-vector form)

The abstract combinatorial impossibility and the concrete Cabello-18
instance. The abstract form is genuinely Cat-2 (CSD-free, Hilbert-
space-free); the instance is Cat-3 only because it lives under
`Empirical/`. Both pinned to the foundational triple. -/

/-- info: 'CSD.Empirical.KochenSpecker.no_value_assignment_18_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.no_value_assignment_18_9

/-- info: 'CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice

/-- info: 'CSD.Empirical.MerminPeres.no_lhv_mermin_peres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.no_lhv_mermin_peres

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaZ_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaZ_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R2

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C2

/-- info: 'CSD.Empirical.Hardy.no_lhv_hardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.no_lhv_hardy

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_cube

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_value

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq

/-- info: 'CSD.Empirical.SternGerlach.born_zPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_zMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_z_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_z_basis_complete

/-- info: 'CSD.Empirical.SternGerlach.born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_x_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_law

/-- info: 'CSD.Empirical.Malus.malus_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_pi_div_two

/--
info: 'CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18

/--
info: 'CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis

/-! ### Empirical/CSD bridge readings

CSD-side companions to the Empirical/QM/ predictions. Each cites the
foundational triple and the LF4-discharge axioms threaded through the
shared `CSDBridge.Context` bundle.

The Bell-family CSD readings are re-exports of LF3 chain capstones;
their axiom citations match the corresponding LF3 capstones. -/

/-- info: 'CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence

/--
info: 'CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle

/--
info: 'CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle

/--
info: 'CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty

-- Phase-E CSD bridges (transport readings; foundational-triple only).
/--
info: 'CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting

/--
info: 'CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication

/--
info: 'CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input

/--
info: 'CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound

/--
info: 'CSD.Empirical.CSDBridge.QEC.csd_three_qubit_corrects_single_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QEC.csd_three_qubit_corrects_single_bitflip

-- Stern-Gerlach: representative pin (the iconic 1/2 split) + completeness.
-- All six transport theorems share the same foundational-triple axiom set.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus

/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete

-- Stern-Gerlach Born values as DERIVED Kähler-volume frequencies (carving-free,
-- Gleason-free CSD-ontic layer): the moment-sublevel frequency → Born number
-- via fs_moment_pushforward_uniform (DH theorem). Strictly above both the
-- transport tag (csd_sg_*) and the carved LF4 capstone (sg_frequency_convergence).
-- Foundational triple only; NO busch_effect_gleason, NO invariant_measure_uniqueness.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain

/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half

-- Malus's law (parametric generalisation of the two SG values) as a DERIVED
-- Kähler-volume frequency: freq → cos²(θ/2) via the same volume route.
-- Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law

-- Metrology A1: Ramsey interferometry. The fringe cos²(φ/2) as a DERIVED
-- Kähler-volume frequency (the Malus reading with θ = φ the accumulated phase),
-- plus the first parameter-driven metrology flow Φ_φ = diag(1,e^{iφ}) on Σ = ℂℙ¹
-- (FS-measure-preserving, genuinely ≠ id, via the audited LF4.obsFlow).
-- Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_volume

/--
info: 'CSD.Empirical.Metrology.ramseyPhaseFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyPhaseFlow_measurePreserving

/--
info: 'CSD.Empirical.Metrology.ramseyPhaseFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyPhaseFlow_ne_id

-- Mach-Zehnder interference (2026-07-19, roadmap B4, the last iconic missing phenomenon): single-photon
-- two-mode interferometer = qubit phase circuit H·D(φ)·H·|0⟩ (= ramseyVec, machine-checked
-- ramseyVec_eq_circuit). Fringe cos²(φ/2) reuses ramsey_fringe_volume (Born-as-volume). NEW content:
-- interferometric visibility = 1 for a pure single photon (bright P(0)=1, dark P(π)=0). Foundational triple.
/-- info: 'CSD.Empirical.CSDBridge.MachZehnder.mz_visibility_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MachZehnder.mz_visibility_one

-- Double-slit interference + Bohr complementarity (2026-07-19): coherent fringe reuses MZ (visibility 1),
-- NEW content = which-path complementarity — measuring the slit makes the interference coherence
-- (off-diagonal of the decohered reduced state) VANISH (decoherence_offdiagonal_vanish), collapsing the
-- fringe to the flat classical mixture (visibility 0). The physical heart of the double slit; the part MZ
-- does not carry. Built on the LF6-B decoherence stratum. Foundational triple.
/-- info: 'CSD.Empirical.CSDBridge.DoubleSlit.doubleslit_complementarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.DoubleSlit.doubleslit_complementarity

-- §14 CONNECTED (2026-07-19): the transport-only SternGerlach module now re-exports the genuine ontic
-- derivation (sg_frequency_convergence) so its CSD reading cites the ontic substrate, not only QM transport.
/-- info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_ontic_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_ontic_frequency_convergence

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_max' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_max

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_min

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_hasDerivAt

-- The Ramsey output state IS the genuine interferometer circuit H·diag(1,e^{iφ})·H·|0⟩
-- (corpus Hadamard QM.Gates.qmH), machine-checked (not a hand-check).
/--
info: 'CSD.Empirical.Metrology.ramseyVec_eq_circuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyVec_eq_circuit

-- Metrology A2: Quantum Fisher Information = Fubini-Study metric. The genuine
-- derivative of the Ramsey state (ramseyVec_hasDerivAt, proved via HasDerivAt, not
-- asserted), the FS line element g = 1/4 (ramsey_fs_metric), the QFI F_Q = 1
-- (ramsey_qfi), the classical Fisher info of the |0⟩ readout F_C = 1
-- (ramsey_classical_fisher, sin φ ≠ 0), and the QCRB saturation F_C = F_Q
-- (ramsey_qcrb_saturation): the computational-basis Ramsey measurement is
-- Fisher-optimal. Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.Metrology.ramseyVec_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyVec_hasDerivAt

/--
info: 'CSD.Empirical.Metrology.ramsey_fs_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fs_metric

/--
info: 'CSD.Empirical.Metrology.ramsey_qfi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_qfi

/--
info: 'CSD.Empirical.Metrology.ramsey_classical_fisher' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_classical_fisher

/--
info: 'CSD.Empirical.Metrology.ramsey_qcrb_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_qcrb_saturation

-- Metrology A3: the Heisenberg limit (1/N scaling) via the entangled GHZ probe.
-- The phase-accumulated GHZ state on the genuine N-qubit carrier Fin (2^N) is
-- normalized (ghzPhaseVec_norm) with a GENUINE derivative (ghzPhaseVec_hasDerivAt,
-- proved via HasDerivAt, not asserted), giving F_Q^GHZ = N² (ghz_qfi) — the
-- Heisenberg quadratic enhancement — versus F_Q^SQL = N for N separable probes, so
-- the entangled probe carries N× the information (heisenberg_advantage: N² = N·N).
-- Reuses A2's fsMetric/qfi/singleRL idiom; foundational triple only (no busch).

/--
info: 'CSD.Empirical.Metrology.ghzPhaseVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghzPhaseVec_norm

/--
info: 'CSD.Empirical.Metrology.ghzPhaseVec_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghzPhaseVec_hasDerivAt

/--
info: 'CSD.Empirical.Metrology.ghz_qfi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghz_qfi

/--
info: 'CSD.Empirical.Metrology.heisenberg_advantage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.heisenberg_advantage

/--
info: 'CSD.Empirical.Metrology.ghz_qfi_div_sql' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghz_qfi_div_sql

-- Bell singlet joint frequencies as DERIVED Kähler-volume convergence (N=4
-- surfacing of born_frequency_convergence_N): carving-free, Gleason-free, and
-- UNCONDITIONAL (no PureSingletPreparation bundle). Plus the recovered singlet
-- correlation -cos θ. Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation

-- GHZ three-qubit joint frequencies as DERIVED Kähler-volume convergence (N=8
-- surfacing of born_frequency_convergence_N, generic xy-plane basis): carving-free,
-- Gleason-free, unconditional. Plus the recovered three-point correlation cos Φ
-- (Mermin values are the excluded Φ=0,π boundary). Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation

-- Hardy's maximal probability (5√5−11)/2 ≈ 9.017% as a DERIVED Kähler-volume
-- frequency (N=4 surfacing of born_frequency_convergence_N at the golden-ratio
-- Hardy state, an interior simplex point — no boundary obstruction): carving-free,
-- Gleason-free, unconditional. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability

-- Arbitrary rank-1 projective measurement context: outcome Born weights as
-- Fubini–Study typicality volumes. Carving-free, Gleason-free, the reusable
-- contextuality grounding. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume

-- Degenerate-eigenspace context: the outcome-a Born weight as the block sum of
-- per-ray Born weights (rank-1-sum projector ⟨ψ, Pₐ ψ⟩). Closes the rank-1 scope
-- note. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_eq_blockSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_eq_blockSum

-- Degenerate-eigenspace context block frequency → block Born weight (sum of FS
-- typicality volumes). Covers Mermin–Peres rank-2 eigenspaces and any degenerate
-- projective context. Carving-free, Gleason-free, foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume

-- Degenerate-eigenspace block frequency as the frequency of a SINGLE union event
-- (⋃_{blk i = a} bornRegion). The aeece86-owed union restatement, available now
-- that the per-ray cells are pairwise disjoint (CSD.LF4.bornRegion_pairwiseDisjoint,
-- LF5-F). Sum form untouched. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event

-- Concrete degenerate (rank-2) witness: the two-qubit parity Z⊗Z. The +1 parity
-- outcome Born weight realised as a block sum of two FS typicality volumes
-- (computational eigenbasis, blk = ![0,1,1,0]). The Mermin–Peres rank-2 observable
-- case made explicit. Carving-free, Gleason-free, foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume

-- Qubit observable variance as a product of two Fubini–Study typicality volumes
-- (the CSD volume-ratio twin of robertson_uncertainty). Var = 4·vol₊·vol₋, the ±
-- Born weights derived as FS volumes via context_born_frequency_volume (M=1).
-- Carving-free, Gleason-free, foundational triple only. The Robertson INEQUALITY
-- itself stays at the QM-validity layer (Empirical/QM/Uncertainty.lean).
/--
info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.born_variance_eq_vol_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.born_variance_eq_vol_product

-- The variance-as-volume-product frequency capstone: 4·freq₊(m)·freq₋(m) → the
-- volume-product variance, grounding observable spread in ontic typicality
-- volumes on Σ = ℂℙ¹. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency

-- Trine POVM: the first non-projective (POVM) entry in the volume-frequency series.
-- A concrete qubit trine POVM (completeness ∑ Eₖ = I), its canonical Naimark
-- dilation, and the frequency-volume capstone — POVM outcome frequencies on the
-- dilated Σ' = ℂℙ⁵ → the trine Born weight as a sum of FS volumes. Foundational
-- triple only (carving-free, Gleason-free; POVM Born = Kähler volume).
/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_complete

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq

-- USD volume capstone: the second non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free).
/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume

-- SIC volume capstone: the third non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free); includes the equiangular
-- SIC property and the tetrahedral tight-frame completeness.
/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume

-- Weak / unsharp measurement (Build 15c): the one-parameter unsharp POVM
-- interpolating no-measurement (η=0) and the sharp σ_z carve (η=1), its Born weights,
-- and the partial-volume-nudge reading on the dilated Σ' = ℂℙ³. Foundational-triple
-- only (carving-free, Gleason-free), static / operational (continuous dynamics D1-gated).
/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_effects_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_effects_sum_one

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_effect_psd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_effect_psd

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus_unit

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_minus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_minus

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_unsharp_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_unsharp_interpolation

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_partial_information_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_partial_information_witness

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume

-- Quantum Zeno effect (Build 15d): frequent projective re-measurement freezes the state.
-- Part A (DERIVED, concrete σx/|0⟩ witness): variance (ΔH)²=1 from the matrices (varH_eq),
-- the quadratic short-time bound P(s) ≥ 1−(ΔH)²s² (zeno_survival_quadratic, from cos²=1−sin²
-- ≥ 1−s²), and the zero initial slope P'(0)=0 (zeno_survival_slope_zero). Part B: the Zeno
-- lower bound P_n ≥ 1−(ΔH)²t²/n (Bernoulli) and the freezing limit P_n → 1
-- (zeno_freezing, squeeze). Non-vacuity: (ΔH)²>0 with full free decay at π/2. The closed-form
-- exp(-isσx) is the standard qubit rotation (asserted closed form); everything else derived.
-- Foundational-triple only; static/operational, the dynamical Σ-flow realisation D1-gated.
/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.varH_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.varH_eq

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_quadratic

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_slope_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_slope_zero

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_lower_bound

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_freezing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_freezing

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_nonvacuous

-- Qutrit POVM volume capstone: the first non-qubit (N=3) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free); a genuine non-projective
-- qutrit POVM (the unsharp / white-noise measurement) via Naimark dilation to ℂℙ⁸.
/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_complete

/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume

-- d=3 SIC (Hesse) volume capstone: the first SYMMETRIC non-qubit (N=3) volume entry,
-- foundational-triple only (carving-free, Gleason-free); the genuine dimension-3 SIC
-- (9 Weyl-Heisenberg states, equiangular |⟨ψⱼ,ψₖ⟩|²=1/4) via Naimark dilation to ℂℙ²⁶.
/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_complete

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_inner_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_inner_normSq

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume

-- d=3 complete-MUB volume capstone: the 4 mutually unbiased bases in dimension 3
-- (|⟨v,w⟩|²=1/3 across distinct bases) as a 12-outcome POVM via Naimark dilation to ℂℙ³⁵;
-- foundational-triple only (carving-free, Gleason-free).
/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_complete

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_unbiased' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_unbiased

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume

-- Superdense coding: representative pins (one encoding + the orthonormality).
/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X

/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal

/--
info: 'CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger

/--
info: 'CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment

/--
info: 'CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment

/--
info: 'CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle

/-- info: 'CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle

/-- info: 'CSD.Empirical.CSDBridge.Gates.u_isometry_of_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Gates.u_isometry_of_transProbPreserving

/-- info: 'CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving

-- Build 15a (Einselection, 2026-06-29): the first einselection / pointer-basis-selection
-- result on the LF6-B decoherence machinery. decohereReduced ψ (LF6-B) is diagonal in the
-- measurement (pointer) basis {eⱼ} (decohere_diagonal_in_pointer_basis), but conjugating by
-- the Hadamard qmH rotates it into a basis where the (0,1) coherence = (p₀−p₁)/2 PERSISTS
-- (decohere_hadamard_offDiag), nonzero for any qubit with distinct Born weights p₀≠p₁
-- (decohere_not_diagonal_in_rotated_basis). einselection bundles diagonal-in-pointer + nonzero
-- in the Hadamard rotation for the concrete witness (2,1) (p₀=4≠1=p₂, off-diag 3/2). The
-- preferred basis comes from the de-isolation/partial-trace CONTEXT, contrasting #29's
-- basis-covariant FS typicality (fubiniStudy_forced_by_symmetry, unique U(N)-invariant, picks
-- no basis). QM-validity/open-system layer; basis-SELECTIVITY of decoherence (not derived from
-- an environment Hamiltonian). Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_diagonal_in_pointer_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_diagonal_in_pointer_basis

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_not_diagonal_in_rotated_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_not_diagonal_in_rotated_basis

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionWitness_offDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionWitness_offDiag

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselection

-- Build 15a follow-up (#34, 2026-06-30): the degeneracy boundary of einselection + general-N
-- einselection. Qubit boundary: the rotated off-diagonal (p₀−p₁)/2 is nonzero IFF p₀ ≠ p₁
-- (decohere_hadamard_offDiag_ne_zero_iff); at p₀ = p₁ the dephased state is the maximally mixed
-- (1/2)·I (decohere_degenerate_half / degenerateWitness_decohere_half) which is invariant under
-- ANY unitary conjugation (decohere_degenerate_basis_invariant), so NO basis is einselected (the
-- einselection-FAILS side). General-N: the dephasing channel decohereReducedN kills off-diagonals
-- and keeps the diagonal pointer populations (einselectionN), with degenerate locus = equal
-- populations ρ i i = 1/N ⟹ (1/N)·I, basis-invariant (einselectionN_degenerate). Non-vacuity:
-- decohereReducedN_acts_nontrivial (off-diagonal nonzero before, zero after) +
-- decohereReducedN_maximally_mixed. The pointer basis is the COMPUTATIONAL basis by construction;
-- the ontic einselection-from-Σ-dynamics origin is GATED to the entangled tier / D1.
-- Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag_ne_zero_iff

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_half

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_basis_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_basis_invariant

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselection_degenerate_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselection_degenerate_boundary

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_scalar

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionN

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_acts_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_acts_nontrivial

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_degenerate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_degenerate_scalar

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_maximally_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_maximally_mixed

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionN_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionN_degenerate

-- Build 15b (QECDecoherence, 2026-06-30): the QEC-corrects-decoherence companion to 15a. A
-- single-qubit error is the K2 bit-flip CHANNEL (CPTP, bitflip_error_cptp) whose Stinespring /
-- partial-trace origin is bitflip_error_is_decoherence (Φ ρ = traceRight(V ρ Vᴴ), Vᴴ V = 1):
-- the error is environmental entanglement traced away. The three-qubit code CORRECTS it:
-- recover ∘ error = id on a bare qubit (qubit_recover_compose_bitflip) and on the code density
-- (three_qubit_recover_density: Xⱼ(Xⱼ ρ Xⱼᴴ)Xⱼᴴ = ρ); qec_corrects_decoherence bundles the
-- Stinespring origin + syndrome-distinctness + exact vector recovery (bitflip_recovers).
-- Non-vacuity: the SAME channel corrupts a bare qubit (bitFlipChannel_corrupts_bare_qubit:
-- Φ(|0⟩⟨0|) ≠ |0⟩⟨0| for 0<p). csd_qec_decoherence_corrected transports it through a
-- CSDThreeQubitBundle. QM-OPERATIONAL (channel + correction) discharged here; the ontic
-- Σ-volume / partial-trace-volume-loss origin is GATED to the entangled tier (LF6 / D1).
-- Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_cptp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_cptp

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_is_decoherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_is_decoherence

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.qubit_recover_compose_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.qubit_recover_compose_bitflip

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.three_qubit_recover_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.three_qubit_recover_density

-- The in-code channel-correction bridge (one Hilbert space): recoverⱼ ∘ errorⱼ = id on the
-- ENCODED density encodeDensity a b, lifting the correctable X branch to qubit j as the K2
-- unitaryChannel (the conjunct that earns qec_corrects_decoherence's name). error_moves_codeword
-- is the non-vacuity witness (X₁ displaces |000⟩).
/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.recover_channel_compose_error_on_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.recover_channel_compose_error_on_code

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.error_moves_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.error_moves_codeword

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.error_moves_encoded_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.error_moves_encoded_density

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitFlipChannel_corrupts_bare_qubit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitFlipChannel_corrupts_bare_qubit

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.qec_corrects_decoherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.qec_corrects_decoherence

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.csd_qec_decoherence_corrected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.csd_qec_decoherence_corrected

/-- info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law_canonical

/-- info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain_canonical

/-- info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half_canonical

/-- info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency_canonical

-- Kochen-Specker (Cabello-18) contextual Born weights as Kähler volumes: the representative
-- context (basis 0) built as a genuine OrthonormalBasis from the complexified/normalised
-- Cabello rays (orthonormality reusing cabello_pairwise_orthogonal_in_basis via the
-- complexification transport), then instantiating the context engine. Carving-free,
-- Gleason-free, foundational triple only.
/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ksCtxVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ksCtxVec_orthonormal

/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume_canonical

-- Mermin–Peres rank-2 observable (X⊗X) ±1-outcome Born weights as Kähler volumes: the
-- non-diagonal grid observable's eigenbasis (H⊗H) built as a genuine OrthonormalBasis from
-- the explicit (±1/2)-component vectors (orthonormality a clean norm_num computation), then
-- instantiating the degenerate-eigenspace engine block_born_frequency_volume at the
-- sign-parity block. Carving-free, Gleason-free, foundational triple only.
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_orthonormal

-- Eigenbasis-identity faithfulness lemmas: mpXXBasis really is the σx⊗σx eigenbasis,
-- machine-checked against the genuine Pauli observable sigmaX ⊗ₖ sigmaX (not a literal).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXBlk_eq_zero_iff_eigval_one

-- Z⊗Z (diagonal) eigenbasis-identity lemmas: earn the σz⊗σz label for the engine-file
-- zz_parity_born_frequency_volume by composition (computational basis = σz⊗σz eigenbasis,
-- machine-checked against the genuine sigmaZ ⊗ₖ sigmaZ).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume_canonical

-- The remaining seven Mermin–Peres square observables, each with a machine-checked
-- eigenbasis tie to the genuine Pauli observable (sigma_a ⊗ₖ sigma_b reindexed onto Fin 4).
-- Eigenvector faithfulness lemmas (the label earned, not asserted) + volume headlines.
-- Foundational-triple-only (no busch), carving-free, Gleason-free.

-- X⊗I (H⊗I frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXIVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXIVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xi_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xi_born_frequency_volume

-- X⊗Z (H⊗I frame, shared eigenbasis with X⊗I)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xz_born_frequency_volume

-- I⊗X (I⊗H frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_ix_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_ix_born_frequency_volume

-- Z⊗X (I⊗H frame, shared eigenbasis with I⊗X)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zx_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zx_born_frequency_volume

-- Z⊗I (computational frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZIVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZIVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume

-- I⊗Z (computational frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume

-- Y⊗Y (complex U_Y⊗U_Y frame; the hard cell)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpYYVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpYYVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_yy_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_yy_born_frequency_volume

-- Block/+1-eigenspace certificates (the second half of the earned-label faithfulness
-- claim: the collapsed block {…} IS exactly the +1 eigenspace, machine-checked against
-- the eigenvalue vector). X⊗X and Z⊗Z block lemmas are pinned above; these are the
-- remaining seven cells.
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXIBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXIBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIXBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZXBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZIBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZIBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpYYBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpYYBlk_eq_zero_iff_eigval_one

-- Z⊗I / I⊗Z canonical FS-trial witnesses (the computational-frame cells; the other
-- non-computational cells already carry _canonical pins above).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_fixes_basis_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_fixes_basis_state

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.holevo_classical_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.holevo_classical_eq_log_two

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_plus_eq_half_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_plus_eq_half_one

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_destroys_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_destroys_coherence

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_classical_vs_quantum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_classical_vs_quantum

-- EraserDynamics (2026-08-03, Empirical/CSD/EraserDynamics.lean; dynamical no-signalling
-- brick 3b — the eraser PROCESS). The two eraser arms are the corpus's local Lüders maps on
-- the Bell path–marker state. MARK (computational marker): localProjB_bellE — the post-state
-- IS the which-path product |j⟩⊗|j⟩; marked_no_fringe — screen rate 1/2 at EVERY phase (the
-- fringe dies dynamically). ERASE (± marker, an instance of localProjOn at the genuine
-- OrthonormalBasis pmBasis): ★ erased_amp — the dynamical post-state's screen amplitudes are
-- EXACTLY √2·eraserOut, so every QuantumEraserVolume statistic is a statement about the state
-- the measurement dynamics produces: erased_rate (conditional fringes), erased_dark (the
-- exact dark-fringe zero, from the dynamics), erased_weight (marker weights 1/2 — the
-- dynamical eraser_marker_marginal). With reduceA_localLudersOn_mixture: mark kills the
-- fringe, erase restores it in the conditioned records, nothing reaches Alice's marginal.
/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.localProjB_bellE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.localProjB_bellE

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.marked_no_fringe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.marked_no_fringe

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_amp

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_dark

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_rate

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_weight

-- EraserSequential (2026-08-03, Empirical/CSD/EraserSequential.lean; the row's residue). The
-- two-stroke composition, in the decisive order: MARK FIRST (record exists), THEN ERASE.
-- seqProfile_eq: the erase stroke only RESCALES the recorded ray |j⟩; weights stay 1/2
-- (sequential_erase_weight); ★ sequential_no_revival — the screen rate stays 1/2 at every
-- phase, port, and marker outcome: once a record exists, no later marker measurement revives
-- the fringe. Records are statistically irreversible — the statistical face of
-- relocation-with-storage. (The other residue, the measure-level ensemble integral, is closed
-- as definitional: for finite outcomes the post ray-ensemble IS the discrete mixture and its
-- barycenter statement IS reduceA_localLudersOn_mixture.)
/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.seqProfile_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.seqProfile_eq

/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.sequential_erase_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.sequential_erase_weight

/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.sequential_no_revival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.sequential_no_revival

-- H3 quantum-chaos pilot, CSD side (Empirical/CSD/QuantumChaos/, 2026-08-07): the
-- ontic lift of unitary-generated Floquet evolutions (Liouville-preserving, projects
-- to the interface's ray dynamics period by period), sure record persistence under
-- uncoupled post-record driving, and the pilot capstone bundling the four universal
-- clauses for EVERY unitary U and base point (a witness/feature index; the
-- accessibility-change clause is the kicked-Ising witness in the Incubator part).
/-- info: 'CSD.Empirical.QuantumChaos.floquetOnticStep_iterate_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.floquetOnticStep_iterate_lifts

/-- info: 'CSD.Empirical.QuantumChaos.floquetOnticStep_iterate_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.floquetOnticStep_iterate_measurePreserving

/-- info: 'CSD.Empirical.QuantumChaos.floquetRecordStep_record_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.floquetRecordStep_record_invariant

/-- info: 'CSD.Empirical.QuantumChaos.floquetPilotClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.floquetPilotClosure

-- Record degradation under COUPLED post-record driving (RecordDegradation.lean,
-- 2026-08-07, the SH continuation): the record half-life bound - a formed record
-- survives n periods of measure-preserving coupled driving except on a set of measure
-- at most n * epsilon (epsilon = the per-step coupling set's measure); null coupling
-- gives a.s. persistence; the pilot's uncoupled case recovered as epsilon = 0.
/-- info: 'CSD.Empirical.QuantumChaos.recordIntact_compl_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordIntact_compl_measure_le

/-- info: 'CSD.Empirical.QuantumChaos.recordIntact_compl_null_of_flip_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordIntact_compl_null_of_flip_null

/-- info: 'CSD.Empirical.QuantumChaos.recordIntact_postRecordStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordIntact_postRecordStep

-- SH small-coupling witness + concrete-model closure (2026-08-07): the fibre-triggered
-- record kick has coupling strength EXACTLY 1/2 (the half-life bound bites: survival
-- except on measure <= n/2), and the kicked-Ising model reaches the ontic-lift clause
-- at Fin 4 through the reindex.
/-- info: 'CSD.Empirical.QuantumChaos.fibreTriggeredKick_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.fibreTriggeredKick_coupling

/-- info: 'CSD.Empirical.QuantumChaos.fibreTriggeredKick_record_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.fibreTriggeredKick_record_halfLife

/-- info: 'CSD.Empirical.QuantumChaos.kickedIsing_pilotClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.kickedIsing_pilotClosure

-- CV-5 CSD-side closure (2026-08-07): the free field at any cutoff, reindexed to
-- Fin (card (FieldConfig K N)) = Fin (N^K), satisfies the full SH3 pilot closure --
-- the quantum-chaos vertical and the CV vertical meet on the same closure instance.
/-- info: 'CSD.Empirical.QuantumChaos.freeField_pilotClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.freeField_pilotClosure

-- CV-7 CSD side (2026-08-07): the closure covers every diagonal interaction at every
-- coupling strength -- the clauses are about unitarity, not freeness.
/-- info: 'CSD.Empirical.QuantumChaos.interacting_pilotClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.interacting_pilotClosure

-- SH attainment (2026-08-08, HalfLifeAttainment.lean): the record half-life bound is
-- SHARP. The cyclic-shift kick (uniform cycle Fin m, trigger {0}) attains mu(intact n)^c
-- = n.eps with eps = 1/m EXACTLY on the window n <= m: within one cycle every trajectory
-- visits the trigger at most once, so the unstable set IS the reach-the-trigger cylinder
-- (set equality, not an estimate). Linear degradation at exactly the coupling rate is
-- realised; sharpness exhibited for this drive, with no claim every drive attains it.
/-- info: 'CSD.Empirical.QuantumChaos.cyclicKick_halfLife_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.cyclicKick_halfLife_attained

-- H7 level 2 (Empirical/CSD/QuantumChaos/CarrierPersistence.lean,
-- 2026-08-12): the event/carrier separation — events reindex and conserve
-- probability; carriers are antitone (perishable).
/-- info: 'CSD.Empirical.QuantumChaos.recordEvent_preimage_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordEvent_preimage_step

/-- info: 'CSD.Empirical.QuantumChaos.recordEvent_measure_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordEvent_measure_invariant

/-- info: 'CSD.Empirical.QuantumChaos.recordIntact_antitone' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.recordIntact_antitone

-- Q1: the derived coupling (DerivedCoupling.lean, 2026-08-12) — the
-- operator-norm -> flip-measure bridge: the overlap-deficit trigger's
-- typicality measure is Markov-bounded by |W - 1|, and the record
-- half-life bound inherits the derived rate; W = 1 gives a.s. persistence.
/-- info: 'CSD.Empirical.QuantumChaos.overlapDeficit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.overlapDeficit_le

/-- info: 'CSD.Empirical.QuantumChaos.measure_deficitTrigger_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.measure_deficitTrigger_le

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_record_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_record_halfLife

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_persists_of_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_persists_of_id

-- Q2: the derived coupling bites, exactly (DerivedCoupling.lean bite
-- section, 2026-08-12): the qubit phase flip's deficit = 2 * momentMap, the
-- trigger measure = 1 - delta/2 via the Duistermaat-Heckman law (exact,
-- where Markov could only bound), strictly-between-0-and-1 coupling, and
-- the half-life at the exact rate. Generic attainment was already settled
-- by cyclicKick_halfLife_attained.
/-- info: 'CSD.Empirical.QuantumChaos.overlapDeficit_phaseFlipW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.overlapDeficit_phaseFlipW

/-- info: 'CSD.Empirical.QuantumChaos.measure_deficitTrigger_phaseFlipW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.measure_deficitTrigger_phaseFlipW

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_bites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_bites

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_halfLife

-- Q4: the entropy ledger (EntropyLedger.lean, 2026-08-12): retrodiction
-- reliability, the one-way erosion fraction, and the two-cell coarse
-- entropy ledger, all priced by the same per-step coupling; the ledger
-- identified with the von Neumann entropy of the register's diagonal
-- state; the phase-flip instantiation with the DH-computed coupling.
/-- info: 'CSD.Empirical.QuantumChaos.measure_retrodictionSuccess_compl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.measure_retrodictionSuccess_compl_le

/-- info: 'CSD.Empirical.QuantumChaos.erosionFraction_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.erosionFraction_monotone

/-- info: 'CSD.Empirical.QuantumChaos.erosionFraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.erosionFraction_le

/-- info: 'CSD.Empirical.QuantumChaos.ledgerEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.ledgerEntropy_le

/-- info: 'CSD.Empirical.QuantumChaos.vonNeumannEntropy_ledgerState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.vonNeumannEntropy_ledgerState

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_reliability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_reliability

/-- info: 'CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumChaos.deficitKick_phaseFlip_ledger

-- Einselection commutation criterion (PointerCommutation, 2026-08-27): the
-- Hamiltonian-level pointer-basis criterion [P, H_int] = 0, discharging in part Build 15a's
-- honest-scope note ("the basis is the de-isolation's by construction"). intFlow Hint t =
-- exp (t • (−i • Hint)) is unitary (via StoneC1's exp_smul_unitary); commutation transfers
-- to the flow (Commute.exp_right), so a commuting P is a CONSTANT OF THE INTERACTION MOTION
-- (pointer_invariant_of_commute, Heisenberg U†PU = P), its populations exactly conserved in
-- every state (pointer_population_conserved), sector states confined
-- (sector_state_invariant); pointer_basis_of_commuting packages all three for a family —
-- commutation ALONE is load-bearing, no projection hypothesis. Class-level:
-- every computational projection |eᵢ⟩⟨eᵢ| commutes with EVERY pointer-diagonal interaction
-- (pointer_basis_of_diagonal), whose flow is diagonal phases (intFlow_diagonal) preserving
-- every coherence modulus (coherence_modulus_preserved) — flow preserves, the LF6-B trace
-- selects. Contrast: the Hadamard-rotated projection |+⟩⟨+| = qmH|e₀⟩⟨e₀|qmH fails the
-- criterion against diag(0,π) (rotatedProj_not_commute) and its own-eigenstate population is
-- driven 1 → 0 in one stroke (noncommuting_population_disturbed);
-- einselection_commutation_contrast bundles the separation. RESIDUE: H_int is the
-- measurement context, an input — the criterion einselects GIVEN the interaction.
-- Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.Einselection.pointer_invariant_of_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.pointer_invariant_of_commute

/-- info: 'CSD.Empirical.CSDBridge.Einselection.pointer_basis_of_commuting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.pointer_basis_of_commuting

/-- info: 'CSD.Empirical.CSDBridge.Einselection.coherence_modulus_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.coherence_modulus_preserved

/-- info: 'CSD.Empirical.CSDBridge.Einselection.pointer_basis_of_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.pointer_basis_of_diagonal

/-- info: 'CSD.Empirical.CSDBridge.Einselection.noncommuting_population_disturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.noncommuting_population_disturbed

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselection_commutation_contrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselection_commutation_contrast

end CSD.Tests.AxiomAudit
