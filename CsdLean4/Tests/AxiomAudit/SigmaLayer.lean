/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4

/-!
# AxiomAudit part: SigmaLayer

**Category:** Special (axiom-posture regression pins; G9 split part).

SigmaLayer + RecordLayer pins (the record layer: swap/join/pointer witnesses, Lueders, POVM dynamics, capstones).

Split from the monolithic `Tests/AxiomAudit.lean` 2026-08-06 (BACKLOG G9):
blocks retain their original relative order; a pin lives here because its
constant's namespace classifies to this part. All parts share the umbrella's
resolution context (root import + the LF1-LF3 opens), so placement never
affects whether a pin compiles. Layer-local gate: `lake build
CsdLean4.Tests.AxiomAudit.SigmaLayer`. Update discipline unchanged — see the
umbrella `Tests/AxiomAudit.lean` docstring and `AXIOMS.md §5`.
-/

@[expose] public section

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3


-- Context-fixed A7 at general N: the SUPPORT REDUCTION (2026-07-28, SigmaLayer/ContextFixedA7).
-- Step one of the general-N A7 no-go, and honest about being step one. Paper C A7 wants regions
-- Omega_i(M) fixed by the APPARATUS ALONE plus a preparation law; U(N)-covariance collapses the
-- density to g(|<psi|phi>|^2) for a SINGLE nonneg g. N=2 works (LF4/QubitBorn qubitBorn, g(s) =
-- 4(2s-1)+); N>=3 is OPEN IN BOTH DIRECTIONS (the earlier "provably dead" verdict rested on
-- numerics + an informal argument and was retracted 2026-07-28, specs/BACKLOG.md).
-- The reduction: evaluate A7 at the n BASIS-VECTOR preparations psi = e_j, where the Born weights
-- are delta_ij. For i != j the requirement makes a NONNEGATIVE integrand integrate to ZERO over
-- Omega_i, forcing it to vanish a.e. there (ae_eq_zero_of_setIntegral_eq_zero -- nonnegativity is
-- doing all the work, which is exactly what a SIGNED density would escape). Hence each support
-- sits in its own region (overlapSupport_ae_subset), the n supports are pairwise a.e. disjoint
-- (overlapSupports_ae_disjoint), and their measures sum to <= 1
-- (sum_measure_overlapSupport_le_one) -- so by symmetry each is <= 1/n while still carrying total
-- integral 1: a base-only density MUST SPIKE. That is what the N=2 solution, supported exactly on
-- (1/2, 1], is doing.
-- Stated over an ABSTRACT probability space on purpose: no projective geometry is needed, so the
-- reduction also survives a move to a fibred Sigma. Intended instantiation X := CPN n,
-- mu := fubiniStudyMeasure, s j := momentMap . j (momentMap_mk_eq_inner_sq).
-- NOT THE NO-GO. It constrains g; it does not refute it. Untouched: the generic-psi requirement
-- (everything here comes from the n basis-vector preps), and the harmonic argument (g(|<psi|phi>|^2)
-- integrated over a fixed region has components of every degree (k,k) while the target is pure
-- (1,1)) -- which needs harmonic analysis on CP^{n-1} that Mathlib does not have.
/-- info: 'CSD.SigmaLayer.ae_eq_zero_of_setIntegral_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.ae_eq_zero_of_setIntegral_eq_zero

/-- info: 'CSD.SigmaLayer.overlapSupport_ae_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.overlapSupport_ae_subset

/-- info: 'CSD.SigmaLayer.overlapSupports_ae_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.overlapSupports_ae_disjoint

-- STEP TWO (2026-07-28): THE CAP. The supports are A_i = {phi | s_i(phi) in S_g}, and step one
-- made them pairwise a.e. disjoint. If S_g contained a positive-measure set T of overlap values
-- BELOW 1/2, two coordinates could both land in T -- they would sum to < 1, so nothing forbids it
-- -- and at N >= 3 a third coordinate absorbs the remainder, so such states occur with POSITIVE
-- measure. Any of them lies in A_j AND A_k, contradicting disjointness. Hence
-- cap_of_joint_nondegenerate: g vanishes a.e. below 1/2. SHARP AND ATTAINED -- the N=2 solution
-- 4(2s-1)+ is supported exactly on (1/2, 1].
-- ★ WHY THE QUBIT ESCAPES, made precise: joint_degenerate_of_sum_eq_one. At N=2 the two Born
-- weights exhaust the state, s_j + s_k = 1, so they can NEVER both be below 1/2 -- the set is
-- literally EMPTY and the abundance hypothesis fails identically. That degeneracy IS the qubit's
-- escape route, and it closes at N >= 3 where the coordinates stop being functionally dependent.
-- base_only_density_confined assembles both halves: the density lives on measure <= 1/n AND only
-- where the overlap exceeds 1/2, while still integrating to 1.
-- The state-abundance input (hjoint) is an explicit HYPOTHESIS, not derived: deriving it is the
-- Dirichlet pushforward of mu_FS, real work and orthogonal to the argument. Stating it that way is
-- what makes the N=2 contrast visible.
/-- info: 'CSD.SigmaLayer.cap_of_joint_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.cap_of_joint_nondegenerate

/-- info: 'CSD.SigmaLayer.joint_degenerate_of_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.joint_degenerate_of_sum_eq_one

/-- info: 'CSD.SigmaLayer.base_only_density_confined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.base_only_density_confined

/-- info: 'CSD.SigmaLayer.sum_measure_overlapSupport_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.sum_measure_overlapSupport_le_one

-- BALANCED-STATE ABUNDANCE, DISCHARGED FOR mu_FS (2026-07-29, ContextFixedA7FS.lean).
-- fs_balanced_abundance: for every c above the forced minimum 1/(M+1), the projective points whose
-- moment coordinates are ALL <= c form a non-null set. This is the `hbalanced` hypothesis of
-- vanishes_below_of_balanced, so step five now has one of its two inputs supplied for mu_FS.
-- Proof: fs_volume_eq_dirichlet_inter reduces it to Lebesgue positivity, and a box about the
-- simplex barycentre witnesses it -- centre b = 1/(M+1), half-width d = min(b, c-b)/(M+1), the two
-- constraints being M*d < b (box stays inside sum t < 1) and M*d < c - b (the dropped coordinate
-- 1 - sum t stays below c).
-- ⚠️ LESSON: an earlier attempt on the same lemma FAILED across four iterations because b and d
-- were introduced with `set`, which makes them opaque local definitions that linarith/nlinarith
-- cannot see through. The fix was to SPLIT GEOMETRY FROM ARITHMETIC: box_in_simplex takes b and d
-- as ABSTRACT reals constrained by linear relations plus the single identity M*b = 1 - b, so every
-- step inside it is linear; the concrete choice is then made once, outside.
-- ⚠️ SCOPE: this does NOT make the (n-1)/n bound unconditional. Step four's OTHER input -- hdense,
-- the tilt fact that unit psi in the sphere of e_i-perp sweep overlaps across [0, 1 - s_i(phi)] --
-- is still a hypothesis and has not been attempted. And even with both discharged, the result is a
-- NECESSARY CONDITION on g, not a proof that A7 fails at N >= 3.
/-- info: 'CSD.SigmaLayer.volume_balanced_inter_openSimplexFree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.volume_balanced_inter_openSimplexFree_pos

/-- info: 'CSD.SigmaLayer.fs_balanced_abundance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_balanced_abundance

-- THE RE-PLUMBING (2026-07-29, SigmaLayer/CircleRecord.lean): the RECORD LAYER on the compact fibre.
-- CircleFibre.lean moved the Born PARTITION to AddCircle 1; this moves the rest with it -- the P5
-- record semantics, isolation-as-conditioning, measurement-as-(context + unknown microstate), the
-- Born probabilities, and a.e. totality of the readout.
-- ★ The RecordSignature is reused VERBATIM (fibreSignature: contexts are nonneg rate vectors,
-- outcomes are Fin n) because it never mentioned the fibre at all -- so swapping R for the circle
-- touches only the SEMANTICS, the assignment of ontic events. That is why nothing physical changes.
-- circleRecordSemantics (P5 on CompactSpace CircleFibre: events measurable + mutually exclusive);
-- compatibleSet_circle_single (P6 -- isolation = conditioning on the arc); circleOutcome_eq_record
-- (the ontic selection IS the record); circleBornMeasurement_prob (= ||psi i||^2, the SAME weight
-- the R fibre gave); circleBornMeasurement_ae_total.
-- ★ NOTE THE IMPROVEMENT in ae_total: on R the statement had to be RESTRICTED to [0,1) by hand,
-- because Lebesgue measure on the line is infinite. On the circle it is a statement about the WHOLE
-- space, because the whole space has measure one. That is the compactness paying for itself.
-- ⚠️ SCOPE unchanged: compactness + Haar probability measure YES; A1 in full NO (no Kahler structure
-- on the fibre; dw=0 needs manifold exterior calculus Mathlib lacks -- permanently scoped, see
-- reconstruction-status.md 2a). Measure exhibited as Haar, not SHOWN Liouville. And the general-N A7
-- question is PARKED, not settled (specs/sigma-fibre-contextuality.md).
/-- info: 'CSD.RecordLayer.circleRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleRecordSemantics

/-- info: 'CSD.RecordLayer.compatibleSet_circle_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compatibleSet_circle_single

/-- info: 'CSD.RecordLayer.circleOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleOutcome_eq_record

/-- info: 'CSD.RecordLayer.circleBornMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleBornMeasurement_prob

/-- info: 'CSD.RecordLayer.circleBornMeasurement_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleBornMeasurement_ae_total

-- THE FIBRE SWAP (2026-07-29, SigmaLayer/CircleFibre.lean) -- the Born partition on a COMPACT fibre.
-- ⚠️ THE DIAGNOSIS THIS FIXES: the corpus had TWO record-layer constructions and COMPACTNESS AND
-- FIBRE-ACTIVITY SAT IN DIFFERENT ONES. KSigmaRecord puts a P5 RecordSemantics on the COMPACT
-- KSigma = CPN x T^2, but its events are pi^-1(bornRegion psi i) -- pulled back from the BASE, so
-- the torus fibre is INERT and it inherits the preparation-indexed base regions. FibredSigma has an
-- ACTIVE fibre (it carries the CDF Born cells) but that fibre is R -- NOT COMPACT, so it cannot be a
-- Paper C A1 ontic surface. Neither had both, and since the A7 work concluded contextuality must
-- live in the FIBRE, active-fibre-on-compact-Sigma is exactly what was needed.
-- circleFibre_volume_univ + the CompactSpace instance: the fibre is AddCircle 1 -- the same factor
-- KTorus is built from -- compact, with Haar a genuine PROBABILITY measure (what restricted Lebesgue
-- on R only had by fiat). circleCell is defined as a PREIMAGE under the canonical representative
-- map, not as an image of cdfCell, so measurability is immediate (measurableSet_circleCell).
-- volume_circleCell: the cell carries EXACTLY the Born weight r_i, via Mathlib's
-- AddCircle.measurePreserving_equivIoc -- so moving to a compact fibre changes NOTHING about the
-- outcome probabilities. volume_circleBornCell: fed the Born rates, the measure is ||psi i||^2.
-- circleCell_pairwiseDisjoint: distinct outcomes stay mutually exclusive.
-- ⚠️ SCOPE: this supplies the FIBRE half. It does NOT by itself make the fibred Sigma an A1 ontic
-- surface, and the measure is exhibited as Haar, not SHOWN to be Liouville.
-- FibreRecord/Measurement/RecordLayerClosure still run on the R fibre and would need re-plumbing
-- onto this one -- NOT done (CircleRecord.lean is a PARALLEL counterpart, not a migration).
-- ⚠️ CORRECTED 2026-07-30: this block previously said the missing Kahler structure needed "the
-- manifold exterior calculus Mathlib lacks; see reconstruction-status.md 2a scoping decision".
-- That was a MISCLASSIFICATION. CP^{n-1} x AddCircle 1 has real dimension 2n-1 -- ODD -- and no
-- odd-dimensional manifold admits a symplectic, hence Kahler, structure. It is a PARITY fact, not
-- a tooling gap, and no Mathlib API repairs it. See TorusFibre.lean, which moves the partition to
-- the even-dimensional KTorus.
/-- info: 'CSD.RecordLayer.circleFibre_volume_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleFibre_volume_univ

/-- info: 'CSD.RecordLayer.measurableSet_circleCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_circleCell

/-- info: 'CSD.RecordLayer.circleCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_circleCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_circleCell

/-- info: 'CSD.RecordLayer.volume_circleBornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_circleBornCell

-- THE PARITY FIX (2026-07-30, SigmaLayer/TorusFibre.lean) -- the Born partition on KTorus.
-- ⚠️ WHAT THIS FIXES, and it is NOT what the fibre-swap block above first said. CircleFibre closed
-- the COMPACTNESS objection but left a second one that is NOT a tooling gap: CP^{n-1} has real
-- dimension 2n-2, so CP^{n-1} x AddCircle 1 has real dimension 2n-1 -- ODD. A symplectic form needs
-- w^k as a volume form, so no odd-dimensional manifold carries one, hence none carries a Kahler
-- structure. A SINGLE CIRCLE CAN THEREFORE NEVER BE THE FIBRE OF A PAPER C A1 SURFACE, however much
-- differential-geometry API Mathlib grows. The same applies retroactively to FibredSigma's
-- CP^{n-1} x R, also 2n-1.
-- THE FIX WAS ALREADY IN THE CORPUS: LF4/KahlerInstance.lean's KTorus = AddCircle 1 x AddCircle 1,
-- with KSigma N = CPN N x KTorus of real dimension 2n -- EVEN, compact, a product of Kahler
-- manifolds. This file puts the cells on the FIRST torus coordinate, leaving the second free as its
-- symplectic partner (mem_torusCell_iff states that freedom as a theorem, rather than leaving it to
-- the prose).
-- volume_torusCell: the cell carries EXACTLY the Born weight r_i -- the free coordinate contributes
-- a factor of 1 because T^2's Haar measure is a probability measure -- so moving to the
-- even-dimensional arena changes NOTHING about the outcome probabilities, just as compactifying did
-- not. volume_torusBornCell: fed the Born rates, the measure is ||psi i||^2.
-- torusCell_pairwiseDisjoint: exclusivity, inherited coordinatewise. torusCell_ae_total /
-- torusBornCell_ae_total: the cells cover T^2 up to a null set.
-- ⚠️ SCOPE: this REMOVES AN OBSTRUCTION to A1; it does not ESTABLISH A1. KSigma is not proved Kahler
-- here, and the fibre measure is exhibited as Haar, not shown to be Liouville. The partition is also
-- still KINEMATIC and still PREPARATION-INDEXED (the consumer feeds it bornRate psi). The successor
-- is the global context-fixed basin B_i(M) with the moment map evaluated at the ONTIC POINT, which
-- is NOT in this file and needs measurability of momentMap -- a lemma the corpus does not have.
/-- info: 'CSD.RecordLayer.mem_torusCell_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.mem_torusCell_iff

/-- info: 'CSD.RecordLayer.measurableSet_torusCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_torusCell

/-- info: 'CSD.RecordLayer.volume_torusCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_torusCell

/-- info: 'CSD.RecordLayer.torusCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_torusBornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_torusBornCell

/-- info: 'CSD.RecordLayer.torusBornCell_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusBornCell_ae_total

-- ★★ THE CONTEXT-FIXED GLOBAL BASIN (2026-07-30, SigmaLayer/GlobalBasin.lean) -- Paper C A7, fibred.
-- THE DEFECT THIS CLOSES: the corpus's record-layer partition is cdfCell (bornRate psi) -- built from
-- the PREPARATION -- so it was never the Omega_i(M) Paper C A7 asks for. QubitBorn does it at N = 2;
-- the general-N BASE-ONLY question is PARKED (ContextFixedA7*, sigma-fibre-contextuality.md).
-- THE CONSTRUCTION (due to an external review of 29c6afd): B_i = {(p, t1, t2) : t1 in circleCell
-- (rate p) i}, with the rate vector read off AT THE ONTIC POINT p. NO psi APPEARS IN THE DEFINITION,
-- so the basin is a function of the apparatus context alone. ContextField bundles what a context
-- actually contributes: a measurable simplex-valued rate FIELD on the base.
-- measurableSet_globalBasin: cut out by two inequalities between measurable real functions
-- (measurable_rep, the rate field, its partial sums) -- this is the step measurable_momentMap unblocks.
-- globalBasin_prob: conditioning the epistemic state on p returns rate p i, via Measure.prod_apply +
-- lintegral_dirac and the TorusFibre slice (preimage_globalBasin). globalBasin_born: at preparation
-- psi the probability is EXACTLY ||<e_i, psi>||^2 -- the Born rule from a partition that never
-- mentions psi. globalBasin_pairwiseDisjoint, globalBasin_ae_total.
-- ★ NOT CIRCULAR: bornRate_eq_momentMap already has the rates FORCED by the Kahler structure and the
-- T^n action, not carved to a target. ★ DOES NOT COLLIDE with the parked N>=3 chain, which constrains
-- BASE-ONLY densities; this partition is genuinely FIBRED, exactly where the fibre-contextuality
-- finding said it must live.
-- ⚠️ SCOPE. (1) dirac p (x) Haar is the EPISTEMIC measure, NOT the Liouville measure. Conditioning on
-- a preparation conditions on a mu_FS-NULL set, so the Dirac product is taken as a DEFINITION rather
-- than obtained by disintegration -- a modelling choice, not a theorem. kMuL = mu_FS (x) vol remains
-- the Liouville measure. (2) KINEMATIC: no H_int(M) generating these basins is constructed; the Paper
-- D obligation is untouched. (3) This does NOT close general-N A7 outright -- it closes the
-- PREPARATION-INDEXING defect. Whether Paper C intends the regions to be BASE-ONLY (in which case the
-- parked chain still governs) is a question about the axiom, not about this file. (4) KSigma is still
-- not proved Kahler and the fibre measure is still Haar, not shown Liouville.
/-- info: 'CSD.RecordLayer.measurableSet_globalBasin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_globalBasin

/-- info: 'CSD.RecordLayer.globalBasin_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.globalBasin_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_prob

/-- info: 'CSD.RecordLayer.globalBasin_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_ae_total

/-- info: 'CSD.RecordLayer.globalBasin_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_born

-- ★★ THE RECORD-LAYER CAPSTONE, MIGRATED (2026-07-31, SigmaLayer/GlobalRecordClosure.lean).
-- RecordLayerClosure certifies the record layer on the fibre Sigma = R with fibreTypicality, for the
-- context bornContext psi -- BUILT FROM THE PREPARATION. This bundle certifies THE SAME FIVE FACTS on
-- the corpus's actual compact sector KSigma = CPN x T^2, for a ContextField -- built from the
-- APPARATUS ALONE. What moved: the arena (R, odd-dimensional, -> KSigma, even), the context type
-- (bornContext psi -> ContextField), the measure (fibreTypicality -> epistemicMeasure p).
-- ★ THE RECORD EVENT IS NOW A FUNCTION OF (context, outcome, time) AND NOTHING ELSE. That is visible
-- in the TYPE of globalRecordSemantics and needs no theorem: the SAME set globalBasin c i serves
-- every preparation, and only the epistemic measure moves. Under fibreRecordSemantics the event was
-- cdfCell (bornRate psi), so it moved with psi. That is the defect A7 objected to.
-- ★ globalOutcome is LITERALLY circleOutcome read at the point's own base, so the ontic selection
-- needs no new machinery -- globalOutcome_eq_some_iff is circleOutcome_eq_some_iff plus unfolding.
-- ★ ae_total STRENGTHENS: on R it had to be stated relative to Ico 0 1 because Lebesgue on the line
-- is infinite; here it is about the WHOLE SPACE, which has measure one.
-- THAT THE FIVE FIELDS ARE OTHERWISE IDENTICAL is the evidence that neither defect was ever
-- load-bearing for the record layer's CONTENT.
-- ⚠️ SCOPE, unchanged from GlobalBasin and repeated because this is the capstone. (1) epistemicMeasure
-- is the EPISTEMIC measure, a definition not a disintegration, and NOT the Liouville measure.
-- (2) KINEMATIC -- no H_int(M); the Paper D obligation is untouched and a certified readout is not a
-- dynamical account of measurement. (3) Closes the PREPARATION-INDEXING defect, not general-N A7
-- outright. (4) RecordLayerClosure is SUPERSEDED, NOT DELETED -- still true, still consumed -- and
-- FiniteQMClosure still carries the older vnPointerOutcome readout; swapping THAT is a separate
-- migration on the productDynamics engine and is NOT done here.
/-- info: 'CSD.RecordLayer.globalOutcome_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalOutcome_eq_some_iff

/-- info: 'CSD.RecordLayer.compatibleSet_global_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compatibleSet_global_single

/-- info: 'CSD.RecordLayer.globalRecordClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalRecordClosure

/-- info: 'CSD.RecordLayer.globalRecordClosure_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalRecordClosure_born

-- CONSTRAINTS ON THE UNBUILT DYNAMICAL LAYER (2026-08-01, SigmaLayer/MeasurementConstraints.lean).
-- ⚠️ THE DIAGNOSIS THAT FORCED THIS (external review, and it is SHARPER than the "still kinematic"
-- caveat the GlobalBasin block carries): globalBasin_ae_total shows the basins cover Sigma up to a
-- null set, so A.E. EVERY POINT ALREADY CARRIES A RECORD and there is no apparatus-ready state of
-- positive measure. A flow cannot CREATE a record in such a space. So "add dynamics to
-- GlobalRecordClosure" is not merely incomplete, it is STRUCTURALLY IMPOSSIBLE -- the repair has to
-- split the hidden SELECTOR from a pointer REGISTER with its own ready region.
-- This file builds none of that. It derives NECESSARY CONDITIONS on any such witness from measure
-- preservation and continuity alone, BEFORE a Hamiltonian exists -- the same cheap-failure check the
-- CP^{n-1} x S^1 parity argument would have been.
-- pointer_region_measure_ge: mu_sel(S) * mu_R(R_0) <= mu_R(B). ⚠️ THE MEASURE CHECK COMES BACK
-- NEGATIVE -- it does NOT obstruct. Granting the (unformalised) evaluation mu_sel(S_i) = 1/n, it
-- reads mu_R(B_i) >= mu_R(R_0)/n, satisfiable with room. That is a GREEN LIGHT for attempting the
-- concrete H_int, NOT evidence that a witness exists. ready_region_measure_le: the summed form,
-- recorded explicitly AS WEAK rather than dressed up.
-- ★ no_everywhere_correlation IS THE ONE WITH TEETH. A continuous Phi maps the preconnected
-- S x R_0 to a preconnected image, which cannot meet two DISJOINT OPEN pointer regions. So an
-- EVERYWHERE correlation is impossible for n >= 2. THEREFORE THE "a.e." IN THE CORRELATION THEOREM
-- IS MATHEMATICALLY NECESSARY, NOT A CONVENIENCE: the exceptional set must be NON-EMPTY, it contains
-- the seams between selector sectors, and its image threads the gaps between pointer regions.
-- Consequences for the implementer: any candidate H_int advertised as giving an exact/everywhere
-- correlation is wrong on these grounds alone; and a witness that leaves the seam unspecified has
-- not addressed the hardest part of its own statement.
/-- info: 'CSD.RecordLayer.pointer_region_measure_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointer_region_measure_ge

/-- info: 'CSD.RecordLayer.ready_region_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.ready_region_measure_le

/-- info: 'CSD.RecordLayer.no_everywhere_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.no_everywhere_correlation

-- THE DYNAMICAL MEASUREMENT INTERFACE (2026-08-01, SigmaLayer/MeasurementProtocol.lean) -- items 1-2.
-- Supplies what GlobalBasin structurally could not: a POINTER REGISTER whose ready region is
-- disjoint from every outcome region, plus a TWO-TIME propagator Phi_{s->t} (not a one-parameter
-- group -- a measurement interaction is switched on and off, and a time-dependent H_int(M,t) does
-- not generate a group).
-- ★ THE DESIGN RULE. The plan warns that a structure with fields like basin_has_born_measure or
-- record_persists "would merely rename the assumptions". Taken literally here: MeasurementProtocol
-- carries ONLY KINEMATICS -- propagator laws, regions, measurability, disjointness, every one a
-- CHECKABLE property of the data. THE CORRELATION IS NOT A FIELD. It is CorrelatesOn, a HYPOTHESIS
-- of the theorems that need it (CONVENTIONS 8.3 _of_ pattern), so discharging it is the visible act
-- of REMOVING a hypothesis. The corpus already has one field-shaped assumption of the forbidden kind
-- (DeIsolationInteraction.basin_rate) and this file deliberately does not add a second.
-- readout_ready_eq_none: BEFORE THE INTERACTION THERE IS NO RECORD -- the non-triviality condition
-- GlobalBasin could not state, and what stops a pre-existing label being sold as a created record.
-- outcomeSector i = Phi_{0->T}^{-1}(B_i): the INITIAL states DESTINED for record i, as against the
-- pointer region where a record is DISPLAYED. That is the TN6 two-level distinction, and conflating
-- the two is what makes a kinematic partition look dynamical.
-- readout_evolve_outcomeSector bridges the levels; outcomeSector_pairwiseDisjoint inherits
-- exclusivity through the preimage.
-- ★ measure_outcomeSector_eq_of_correlates: THE BORN WEIGHT, DERIVED. Given the correlation, the
-- outcome sector's measure EQUALS the selector sector's -- so the dynamic probability is not a new
-- postulate, it is the existing context-fixed selector weight transported by the interaction.
-- Composed with globalBasin_born it yields ||<e_i,psi>||^2.
-- ⚠️ NO INTERACTION HAMILTONIAN. Nothing here constructs a Phi satisfying CorrelatesOn; that is the
-- open Paper D obligation. Every theorem is pure kinematics or explicitly conditional. This file is
-- SCAFFOLDING FOR THE STATEMENT of the problem, NOT progress on its solution.
-- ⚠️ And by no_everywhere_correlation above, the EVERYWHERE form of CorrelatesOn is UNSATISFIABLE at
-- K >= 2 on a connected ready set. A real witness establishes it only off a null set and must say
-- what happens on the seam.
/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_ready_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_ready_eq_none

/-- info: 'CSD.RecordLayer.MeasurementProtocol.outcomeSector_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.outcomeSector_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_evolve_outcomeSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_evolve_outcomeSector

/-- info: 'CSD.RecordLayer.MeasurementProtocol.measure_outcomeSector_eq_of_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.measure_outcomeSector_eq_of_correlates

-- PERSISTENCE AND THE POST-MEASUREMENT ENSEMBLE (2026-08-01, SigmaLayer/RecordPersistence.lean) --
-- items 5-6.
-- ★ BOTH USE THE EVOLUTION, WHICH IS THE POINT. The plan is explicit that reusing the same set at
-- every time does not count as persistence. record_persists_on_interval is stated about
-- evolve startTime t for a RANGE of t and its proof runs through evolve_comp
-- (Phi_{0->t} = Phi_{T->t} . Phi_{0->T}), so it is a statement about the PROPAGATOR, not the
-- observation that a time-independent set is time-independent. Likewise postMeasure is a genuine
-- pushforward along the propagator, not a relabelling of the conditioned measure.
-- PointerInvariantOn: the post-readout invariance HYPOTHESIS -- again NOT a field, for the same
-- reason CorrelatesOn is not. It is an assumption ABOUT THE DYNAMICS; a witness must establish it,
-- by forward invariance of B_i or by a conserved pointer observable.
-- record_persists_on_interval: a state destined for i is in B_i at EVERY time of [T_M, T_M + tau_R].
-- readout_persists_on_interval: the readout-level form -- and therefore the POINTER-LEVEL
-- REPEATABILITY statement, a second look during the lifetime returns the recorded outcome.
-- ★ SELECTION vs DISTURBANCE, which the corpus previously could not distinguish:
-- measure_outcomeSector_eq_of_correlates says WHICH initial sector produced outcome i (selection);
-- postMeasure says WHERE THE SELECTED ENSEMBLE ENDS UP (disturbance).
-- postMeasure_supported_pointerRegion: the whole selected ensemble lands in B_i, probability one.
-- Almost definitional -- Phi^{-1}(B_i) IS Omega_i by construction -- and that is the RIGHT shape,
-- not a weakness: the content is the definitions lining up. Holds for ANY propagator, needing
-- neither CorrelatesOn nor PointerInvariantOn.
-- ⚠️ SCOPE. No interaction Hamiltonian: PointerInvariantOn is ASSUMED, not constructed, so nothing
-- here advances the open Paper D obligation. AND THE LUDERS BRIDGE IS NOT HERE -- item 6 also asks
-- that after the system-reduction map r_S this reproduce rho -> Pi_i rho Pi_i / Tr(rho Pi_i), which
-- needs a reduction map from Sigma_meas to the system density operator that the corpus does NOT have
-- for this arena. The measure-theoretic half is done; the bridge to LF5's Luders result is not, and
-- is not claimed. The finite window [T_M, T_M + tau_R] is deliberate -- on a compact phase space with
-- an invariant probability measure, indefinite stability raises recurrence questions finite-QM
-- closure does not need.
/-- info: 'CSD.RecordLayer.MeasurementProtocol.record_persists_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.record_persists_on_interval

/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_persists_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_persists_on_interval

/-- info: 'CSD.RecordLayer.MeasurementProtocol.postMeasure_supported_pointerRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.postMeasure_supported_pointerRegion

-- ★★ THE CONCRETE MEASUREMENT WITNESS (2026-08-01, SigmaLayer/ShearWitness.lean) -- item 3, PARTLY.
-- An explicit propagator on Sigma_sel x T^2_R that takes a ready pointer into one displaying the
-- outcome the hidden selector had already fixed. It DISCHARGES BOTH standing hypotheses of the
-- interface -- CorrelatesOn AND PointerInvariantOn -- so neither is assumed.
-- THE PHYSICS: the von Neumann shear H_int(t) = g(t)(iota(x_sel)+1) delta p_R. Hamilton gives
-- qdot_R = g(t)(iota+1)delta, pdot_R = 0, and -- the point -- xdot_sel ~ grad(iota) = 0 A.E.,
-- because iota is LOCALLY CONSTANT off the seams between selector sectors. So the coupling moves the
-- pointer at an outcome-dependent rate and does NOT disturb the selector, except on the measure-zero
-- seam. ★ THAT IS EXACTLY WHERE no_everywhere_correlation SAID THE EXCEPTIONAL SET HAD TO LIVE --
-- the constraint predicted the singularity's location before the construction existed. Two
-- independent routes agreeing is the reason to think this is the right shape.
-- DESIGN, each choice forced: shifts of (i+1)delta not i*delta (else the outcome-0 region IS the
-- ready region and "no record" masquerades as a record); g SWITCHED OFF after T_M (which is why the
-- interface is a TWO-TIME propagator -- a group cannot express the switch-off, and it is what makes
-- shear_pointerInvariant PROVABLE); epsilon = delta/2 with delta = 1/(K+1) (arcs pairwise disjoint
-- in one turn, AND every shifted ready state stays below 1 so no wraparound occurs and rep is
-- additive -- rep_pshift_of_mem).
-- shear_correlates: CorrelatesOn DISCHARGED. shear_pointerInvariant: PointerInvariantOn DISCHARGED.
-- shear_readout_ready / shear_readout_after: the non-triviality pair -- NO record before, a unique
-- record after -- which rules out an identity flow or a pre-existing label sold as record creation.
-- ⚠️ SCOPE, and item 3 IS NOT CLOSED. (1) THE HAMILTONIAN GENERATION IS STATED, NOT FORMALISED: the
-- propagator is constructed explicitly and every required property proved OF it, but that it is the
-- time-T_M flow of that H_int is symplectic geometry and Mathlib has no manifold Hamiltonian-flow
-- API (the section 2a permanently-scoped row). The plan's "propagator PROVED TO ARISE FROM that
-- Hamiltonian" is therefore HALF done. Do not cite this as a formalised H_int. (2) MEASURE
-- PRESERVATION IS NOT PROVED -- and it matters, because it is what makes this a DYNAMICS rather than
-- an arbitrary relabelling, and every necessary condition in MeasurementConstraints assumes it.
-- First thing to close. (3) NOT connected to the Born weights: that needs the selector sectors to be
-- globalBasin's, which depends on (2). (4) A WITNESS, NOT A DERIVATION -- the coupling is ENGINEERED
-- to work. (5) iota is the outcome index, so "the apparatus is coupled to the answer" -- an
-- objection that applies verbatim to the textbook von Neumann coupling this is the ontic analogue of.
/-- info: 'CSD.RecordLayer.rep_pshift_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rep_pshift_of_mem

/-- info: 'CSD.RecordLayer.shear_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_correlates

/-- info: 'CSD.RecordLayer.shear_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_pointerInvariant

/-- info: 'CSD.RecordLayer.shear_readout_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_readout_after

-- MEASURE PRESERVATION FOR THE SHEAR (2026-08-01) -- closing scope item (2) of the block above.
-- ⚠️ That block recorded measure preservation as NOT PROVED, and warned it MATTERED: it is what makes
-- the witness a DYNAMICS rather than an arbitrary relabelling of states, and EVERY necessary
-- condition in MeasurementConstraints assumes it. It is now proved, so that warning is discharged.
-- shear_measurePreserving: a SKEW PRODUCT -- the selector is held fixed and each fibre is translated
-- by a Haar-preserving shift (measurePreserving_pshift, from translation invariance of Haar on the
-- compact group T^2). The instance IsAddLeftInvariant for volume on KTorus had to be supplied by
-- hand: volume on a product IS the product measure, but the invariance instance does not fire
-- through the MeasureSpace instance.
-- CONSEQUENCE: the Born connection (scope item 6) is now UNBLOCKED -- what remains there is the
-- instantiation of the selector sectors as globalBasin's, not a missing ingredient.
-- ⚠️ STILL OPEN and unchanged: the Hamiltonian generation is stated, not formalised (no manifold
-- Hamiltonian-flow API in Mathlib), so item 3 remains only PARTLY closed.
/-- info: 'CSD.RecordLayer.measurePreserving_pshift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurePreserving_pshift

/-- info: 'CSD.RecordLayer.shear_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_measurePreserving

-- THE SHEAR DRIVEN BY THE CONTEXT-FIXED BASINS (2026-08-01, SigmaLayer/DynamicBorn.lean) -- item 4.
-- ShearWitness proves the correlation for an ABSTRACT measurable index. This supplies the index the
-- architecture intends -- the one read off globalBasin -- so the dynamical sectors carry BORN
-- WEIGHTS rather than arbitrary ones.
-- basinIndex: the outcome index of a point of Sigma_sel. Its fibre over i is globalBasin c i, except
-- over the DEFAULT index which also picks up the points in NO basin -- a null set by
-- globalBasin_ae_total. measure_basinIndex_fibre: that null set costs nothing, so every fibre has
-- exactly its basin's measure. (This is the one place the a.e.-totality that caused the original
-- problem is actually USEFUL: it is what makes the default index harmless.)
-- ★ shear_selector_born: at preparation psi the sector "hidden selector reads i AND apparatus ready"
-- has measure ||<e_i,psi>||^2. Composed with shear_correlates and
-- measure_outcomeSector_eq_of_correlates, the DYNAMICAL outcome weight IS the Born weight -- the
-- probability is TRANSPORTED BY THE INTERACTION, not posited for it.
-- ⚠️ SCOPE unchanged from ShearWitness: the propagator is explicit and every property proved OF it,
-- but the HAMILTONIAN GENERATION IS STATED, NOT FORMALISED. This closes the BORN half of item 4, not
-- item 3.
/-- info: 'CSD.RecordLayer.measurable_basinIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_basinIndex

/-- info: 'CSD.RecordLayer.measure_basinIndex_fibre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measure_basinIndex_fibre

/-- info: 'CSD.RecordLayer.shear_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_selector_born

-- GENERALISATION AND THE DYNAMICAL CAPSTONE (2026-08-01, OutcomeField + DynamicMeasurementClosure)
-- items 7-8.
-- ITEM 7. ContextField N ties the OUTCOME COUNT to the DIMENSION (rate : CPN N -> Fin N), which is
-- right for a NONDEGENERATE measurement and wrong for everything else. OutcomeField N K decouples
-- them. ★ TWO PLAN CONSTRAINTS FOLLOWED LITERALLY: (a) introduced ALONGSIDE ContextField, NOT
-- replacing its uses -- globalBasin and everything downstream are untouched, and
-- ContextField.toOutcomeField shows the generalisation is CONSERVATIVE; (b) an arbitrary
-- simplex-valued field is NOT treated as automatically physical -- OutcomeField is a
-- measurability-and-simplex condition and inhabiting it proves nothing about an apparatus.
-- The physical content is blockField: given a DEGENERACY MAP b : Fin N -> Fin K, the rate of outcome
-- i is the total moment-map weight of its block, the ontic form of <psi, Pi_i psi>. Every field
-- condition comes FREE from the moment map's, because it is a FINITE SUM OF MOMENT COORDINATES --
-- the same object, coarse-grained. blockField_id recovers momentContext, so the nondegenerate case
-- is recovered rather than replaced. ⚠️ globalBasin still consumes a ContextField, so an
-- OutcomeField cannot yet DRIVE the dynamical layer -- that bridge is deliberately not built.
-- ITEM 8. ADDITIVE, NOT DESTABILISING, exactly as the plan required: FiniteQMClosure is UNTOUCHED.
-- DynamicMeasurementClosure bundles the five dynamical facts: ready => no record; a record is
-- CREATED and is the outcome the selector fixed; outcomes exclusive; the record PERSISTS across the
-- operational window; the selector weights ARE the Born weights.
-- ★ NOTE WHAT IS ABSENT FROM ITS HYPOTHESES: CorrelatesOn and PointerInvariantOn DO NOT APPEAR,
-- because ShearWitness discharged them from an explicitly constructed propagator. This bundle rests
-- on a CONSTRUCTION, not on assumed dynamics -- the difference between it and every earlier
-- record-layer bundle in the corpus.
-- ⚠️ The post-measurement/Luders field is DELIBERATELY NOT bundled: postMeasure_supported_pointerRegion
-- exists but the Luders bridge needs a system-reduction map the corpus lacks for this arena, so
-- including it would overstate.
-- CsdFiniteQMClosure combines operational + dynamic. ⚠️ IT ASSERTS BOTH BUNDLES HOLD; IT DOES NOT
-- ASSERT THEY ARE ABOUT THE SAME ARENA. The operational closure lives on productDynamics over
-- CP^M x T^2 for a composite indexed by Fin Nsub x Fin Nsub ~ Fin (M+1); the dynamical one on
-- Sigma_sel x T^2_R in dimension Nsys. The parameter lists are DISJOINT, and that is the honest
-- state of the corpus, not an encoding artefact. Unifying the arenas is the ENGINE MIGRATION and is
-- NOT done. Read it as "both hold", not "one theory covers both".
-- ⚠️ And item 3's residue is unchanged: the Hamiltonian generation is STATED, NOT FORMALISED. A
-- capstone cannot launder that.
/-- info: 'CSD.RecordLayer.blockField_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.blockField_id

/-- info: 'CSD.RecordLayer.dynamicMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.dynamicMeasurementClosure

/-- info: 'CSD.RecordLayer.csdFiniteQMClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.csdFiniteQMClosure

-- THE TWO REMAINING BRIDGES (2026-08-01).
-- BRIDGE A -- OutcomeField -> basins (SigmaLayer/OutcomeBasin.lean). OutcomeField decoupled the
-- outcome count from the dimension but globalBasin still consumed a ContextField, so a K-outcome
-- field could not drive the record layer. outcomeBasin closes that: same construction, Fin K in
-- place of Fin N, with measurability, exclusivity, outcomeBasin_prob and a.e. totality re-proved.
-- ★ outcomeBasin_toOutcomeField: for a ContextField the generalised basin IS globalBasin,
-- DEFINITIONALLY -- the generalisation adds cases without changing any existing one. So DEGENERATE
-- PROJECTIVE MEASUREMENTS now reach the basins.
-- BRIDGE B -- THE LUDERS CONNECTION, AND IT IS A NEGATIVE RESULT.
-- ⚠️ shear_base_marginal_unchanged: Prod.fst . evolve = Prod.fst, so the base marginal of the
-- POST-measurement ensemble is the base marginal of the SELECTED ensemble. NOTHING ABOUT THE SYSTEM
-- HAS MOVED. The shear therefore gives REPEATABILITY (re-reading the same observable returns the
-- same outcome) but does NOT implement the LUDERS UPDATE: after outcome i the system is still at
-- [psi], not at [e_i], so a subsequent INCOMPATIBLE measurement would see the original preparation
-- -- which is not what QM predicts.
-- ★ THE TENSION IS STRUCTURAL, NOT AN OVERSIGHT. The property that makes this witness work --
-- xdot_sel ~ grad(iota) = 0, NO BACK-REACTION on the selector -- is EXACTLY the property that
-- prevents collapse. A witness reproducing Luders must DISTURB the selector, and then the clean
-- correlation argument has to be redone. So item 6's Luders half is not merely unbuilt here: THIS
-- WITNESS CANNOT SUPPLY IT, and a different coupling is required. Recorded as a theorem rather than
-- left as an absence, so the limitation is machine-checked rather than asserted.
/-- info: 'CSD.RecordLayer.outcomeBasin_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.outcomeBasin_prob

/-- info: 'CSD.RecordLayer.outcomeBasin_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.outcomeBasin_ae_total

/-- info: 'CSD.RecordLayer.shear_base_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_base_marginal_unchanged

-- ★★ THE CALIBRATED-SWAP WITNESS AND THE LUDERS THEOREM (2026-08-01/02, SigmaLayer/SwapWitness.lean
-- + SwapLuders.lean + MeasurementConstraints additions + Mathlib/MeasureTheory/PiecewisePreserving).
-- shear_base_marginal_unchanged proved the shear CANNOT collapse: no back-reaction on the selector
-- is exactly what prevents it. The design (Fable review, 2026-08-01) starts from TWO NO-GOS proved
-- FIRST, in MeasurementConstraints:
--   no_exact_collapse        a measure-preserving map cannot send a positive-measure set of states
--                            into a NULL target (the basis vertices). So pointwise collapse across
--                            preparations is IMPOSSIBLE, and collapse must be RELOCATION of a null
--                            epistemic slice, never contraction.
--   collapse_accuracy_bound  approximate collapse to eps-balls forces mu_R(R_0) <= N mu_FS(ball) --
--                            COLLAPSE ACCURACY IS PAID IN READY-STATE IMPROBABILITY (Landauer as a
--                            measure inequality). Retroactively FORCES the Dirac-calibration
--                            convention rather than excusing it.
-- THE CONSTRUCTION: enlarge the arena with an ANCILLA BANK, SwapArena = (Xsel x T^2_R) x (Fin K ->
-- Xsel) -- K reference cells, one per outcome, each a full copy of the selector space. Propagator =
-- record-triggered swap AFTER the shear: when the pointer sits in arc j, exchange the system's
-- selector coordinate with bank slot j (swapG, an INVOLUTION).
-- ★ THE RECORD-TRIGGER IS FORCED: the pieces {register in arc j} are invariant under the slot-j swap
-- BECAUSE the swap never touches the register -- which is what makes swapG measure-preserving via
-- measurePreserving_of_partition. Triggering on the SELECTOR index would move the coordinate the
-- pieces are defined by, and the bookkeeping fails. The right causal story and the only working
-- measure theory COINCIDE.
-- ★ THE CROSSING PROPAGATOR IS SYMMETRIC -- a CORRECTION to the reviewed design, which fired the
-- swap on forward readout-crossings only. evolve_comp is quantified over ALL time triples, and a
-- forward-only flag FAILS on go-past-and-come-back paths. G being an involution, the repair fires it
-- on crossings in EITHER direction; all eight side-of-readout cases close on G^2 = id + the shear
-- frozen right of readout (swapEvolve_comp).
-- swapEvolve_measurePreserving: the FULL propagator preserves the Liouville measure at every time
-- pair. swap_correlates / swap_pointerInvariant: both hypotheses discharged again, now on the
-- enlarged arena. Supporting Mathlib-dir lemmas (upstream candidates, CSD-free):
-- measurable_of_partition, measurePreserving_of_partition, Measure.map_eval_pi',
-- measurePreserving_swapSlot (via piFinSuccAbove -- a subtype-free split avoiding a Fintype
-- instance diamond).
-- ★★ swap_luders_marginal (SwapLuders.lean): CONDITIONED ON OUTCOME i, THE POST-MEASUREMENT SYSTEM
-- MARGINAL IS THE SLOT-i CALIBRATION -- map projSys (postMeasure mu_in i) = nu i. Collapse as
-- measure-preserving RELOCATION: nothing shrinks, the involution exchanges Liouville volume 1:1, and
-- what moves is WHICH NULL SLICE the epistemic measure occupies. Slot i afterwards holds the
-- PRE-measurement state and the depleted fibre -- a perfect ontic memory; irreversibility enters
-- only at slot RESET (erasure, priced by collapse_accuracy_bound).
-- ★★ swap_luders_born: with slots calibrated to the vertex preparations epistemicMeasure [e_j], the
-- post-outcome-i system marginal IS epistemicMeasure [e_i], so for ANY context field c' the
-- follow-up outcome-j probability is c'.rate [e_i] j -- THE BORN WEIGHTS OF THE COLLAPSED STATE.
-- Sequential statistics are Luders at rank one.
-- ⚠️ SCOPE. (1) NONDEGENERATE ONLY: at rank one the Luders channel IS measure-and-reprepare (a
-- standard QI fact -- the objection "that is reprepare, not collapse" applies identically to the
-- textbook channel); for DEGENERATE projectors it is NOT, and this witness does not cover them.
-- (2) The calibration nu_j = epistemicMeasure [e_j] is a CONTEXT-FIXED EPISTEMIC POSIT, parallel to
-- pointer-readiness, basis-dependent only, never psi-dependent -- A7-compatible -- and its
-- Liouville-nullity is FORCED by no_exact_collapse. (3) ONE MEASUREMENT CONSUMES ONE BANK; reset =
-- erasure, outside the protocol. (4) The Hamiltonian generation of the swap stage is STATED, NOT
-- FORMALISED, as for the shear. (5) The Luders CHANNEL-level bridge to LF5's operational result
-- (rho -> Pi rho Pi / Tr) is the rank-one reading recorded in the docstring, not a corpus theorem.
/-- info: 'CSD.RecordLayer.no_exact_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.no_exact_collapse

/-- info: 'CSD.RecordLayer.collapse_accuracy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.collapse_accuracy_bound

/-- info: 'CSD.RecordLayer.measurePreserving_swapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurePreserving_swapG

/-- info: 'CSD.RecordLayer.swapEvolve_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapEvolve_comp

/-- info: 'CSD.RecordLayer.swapEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.swap_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_correlates

/-- info: 'CSD.RecordLayer.swap_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_pointerInvariant

/-- info: 'CSD.RecordLayer.swap_luders_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_luders_marginal

-- ★ swap_luders_iff_calibrated (F-05 discharge, G4, 2026-08-06): the MINIMAL CALIBRATION THEOREM —
-- post-outcome-i system marginal = tau IFF nu i = tau. Both directions: calibration ⇒ Luders AND
-- Luders ⇒ that exact calibration. "The update is calibration-encoded" is now a theorem, not a
-- scope note.
/-- info: 'CSD.RecordLayer.swap_luders_iff_calibrated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_luders_iff_calibrated

/-- info: 'CSD.RecordLayer.swap_luders_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_luders_born

-- Q25 (2026-08-21, specs/two-time-luders-scoping.md): TWO-TIME LUDERS ON ONE ARENA
-- (RecordLayer/TwoTimeLuders.lean + swap_sector_born_ctx in SwapClosure.lean).
-- The swap arena extended with a SECOND apparatus (fresh register + fresh bank); stage 2 acts
-- through the regroup shuffle and provably never touches the first record (structural
-- persistence). The engine: the stage-2 record event reads only the SYSTEM marginal of the
-- conditioned post-measurement state (= swap_luders_marginal), so the joint law factors.
-- ★ swap_sector_born_ctx — the dynamical sector Born for an ARBITRARY context field.
-- ★★ two_stage_joint — the generic composition: joint record probability = (stage-1 sector
-- measure) × (stage-2 sector measure at the relocated state).
-- ★★ two_time_born — P(record i at t₁ ∧ record j at t₂) = momentMap p i · c₂.rate [e_i] j:
-- Born-then-Luders-Born as ONE number on ONE arena, any second context.
-- ★ two_time_repeat — von Neumann repeatability in composed form: same context twice gives
-- momentMap p i · δ_ij at the two-record sector.
-- ★ two_time_other_fate — the post-outcome fate of the OTHER Ω_j: conditioned on record i at
-- t₁, the next partition carries the collapsed weights c₂.rate [e_i] (repeat context: the other
-- regions are NULL, Ω_i certain).
/-- info: 'CSD.RecordLayer.swap_sector_born_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_sector_born_ctx

/-- info: 'CSD.RecordLayer.two_stage_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.two_stage_joint

/-- info: 'CSD.RecordLayer.two_time_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.two_time_born

/-- info: 'CSD.RecordLayer.two_time_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.two_time_repeat

/-- info: 'CSD.RecordLayer.two_time_other_fate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.two_time_other_fate

-- DEGENERATE LUDERS: THE PROBLEM MADE PRECISE, THE BOUNDARY PROVED (2026-08-02,
-- SigmaLayer/DegenerateLuders.lean).
-- At rank one the Luders channel IS measure-and-reprepare and swap_luders_born delivers it. At
-- higher rank the post-state is the NORMALISED PROJECTION [Pi_i psi] -- psi-DEPENDENT, coherence
-- inside the block intact -- and that dependence is the whole difficulty. This module does three
-- things and claims no fourth:
-- (1) BlockLudersObligation -- the degenerate demand as a _statement Prop (CONVENTIONS 8.3):
-- post-outcome-i marginal = epistemicMeasure [Pi_i psi]. NOTHING in the corpus inhabits it for a
-- block of dimension >= 2.
-- (2) ★★ swap_not_blockLuders -- THE BOUNDARY, AS A THEOREM: the calibrated-swap witness fails the
-- obligation for ANY fixed calibration nu, whenever a block has dimension >= 2. The proof turns
-- swap_luders_marginal's virtue against it: the swap's post-marginal is the FIXED slot state nu i,
-- preparation-independent, while the obligation at two vertex preparations inside the block demands
-- the two DISTINCT states epistemicMeasure [e_j1] != epistemicMeasure [e_j2]
-- (vertexPoint_injective + epistemicMeasure_injective). So the fixed-calibration architecture is
-- REFUTED for degenerate measurements -- a machine-checked scope boundary, not a scope note.
-- (3) ★ degenerate_selector_born -- THE POSITIVE HALF THAT SURVIVES: the block-selector
-- (blockIndex b = b . basinIndex) has outcome sectors carrying EXACTLY the coarse-grained Born
-- weights, the dynamical realisation of OutcomeField's kinematic blockField. STATISTICS generalise
-- to degenerate measurements; the UPDATE is what does not.
-- Supporting: momentMap_vertex (the moment map at a vertex is its indicator -- also what makes
-- vertex_outcome_pos work), vertexPoint_injective, epistemicMeasure_injective.
-- ⚠️ WHAT REMAINS OPEN: the degenerate witness itself. It must relocate [psi] -> [Pi_i psi] -- a
-- psi-dependent target -- while preserving measure; no_exact_collapse still governs, so the lost
-- base data must be STORED. Route: the projective-join decomposition of CP^{N-1}, wall = the FS
-- measure decomposition under the join, unformalised geometry, effort L. specs/BACKLOG.md.
/-- info: 'CSD.RecordLayer.momentMap_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.momentMap_vertex

/-- info: 'CSD.RecordLayer.degenerate_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.degenerate_selector_born

/-- info: 'CSD.RecordLayer.vertex_outcome_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.vertex_outcome_pos

/-- info: 'CSD.RecordLayer.swap_not_blockLuders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_not_blockLuders

-- A5 STEP TWO: THE (eps,T)-PROJECTABILITY PACKAGE (2026-08-02,
-- SigmaLayer/ApproxProjectability.lean) -- the BACKLOG ★ A5 row's stated shape, delivered.
-- EpsProjectable: the predicate on ontic Hamiltonians Sigma -> R in OSCILLATION form -- Hs varies by
-- at most eps along each fibre of pi. ⚠️ The DERIVATIVE form sup||d(deltaH)|_V|| <= eps is the
-- scoped manifold statement (section 2a; no exterior-calculus API); the oscillation form is its
-- formalisable core, and the substitution is stated wherever it appears, not made silently.
-- epsProjectable_zero_iff: THE EXACT CASE IS THE eps = 0 INSTANCE, AS AN IFF -- zero
-- fibre-oscillation is precisely factoring through pi, tying the new predicate to the corpus's
-- existing exact-case formalisation (kSectorDataFlow_projectable).
-- diagOnticEnergy_epsProjectable: NON-VACUITY -- the moment-map energy of a diagonal observable
-- (the ontic form of <psi, diag(lam) psi>) is an EpsProjectable _ 0 witness: the corpus's own
-- Born-weight energies are exactly projectable.
-- ★ quantum_effective_shadowing (+ _state): THE DYNAMICAL CONTENT. ||H - H_0|| <= eps and |t| <= T
-- give ||e^{t(-iH)} - e^{t(-iH_0)}|| <= eps*T (and eps*T*||psi|| on states). Since H_0's witness
-- flow is projectable (the exact case), THE SECTOR DYNAMICS TRACKS THE TRUE DYNAMICS TO WITHIN
-- eps*T -- for times up to T the sector cannot tell a quantum-effective Hamiltonian from its
-- projectable part. That is what "selects the sector" means operationally, and it is the content
-- the exact case alone could not express.
-- ⚠️ SCOPE: the shadowing lives on the HILBERT side, where the corpus's dynamics genuinely runs;
-- the ontic predicate lives on Sigma. The bridge -- an ontic Hamiltonian GENERATING a flow whose
-- projection is e^{-itH} -- is A2's open row, not A5's, and is not claimed.
/-- info: 'CSD.RecordLayer.epsProjectable_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epsProjectable_zero_iff

/-- info: 'CSD.RecordLayer.diagOnticEnergy_epsProjectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.diagOnticEnergy_epsProjectable

/-- info: 'CSD.RecordLayer.quantum_effective_shadowing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.quantum_effective_shadowing

/-- info: 'CSD.RecordLayer.quantum_effective_shadowing_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.quantum_effective_shadowing_state

-- A2'S FORMALISABLE HALF: THE HAMILTONIAN SIGNATURE (2026-08-02,
-- SigmaLayer/HamiltonianSignature.lean).
-- A2 as written -- the flow is generated by X_H = w^{-1} dH -- needs the symplectic form and
-- exterior derivative: the section-2a-scoped manifold gap (verified a tooling gap, not a falsity).
-- What a measure space CAN express is the SIGNATURE a Hamiltonian flow leaves, and the witness flow
-- is shown to have every piece:
-- (1) A CANONICAL CONSERVED ENERGY. onticEnergy H = the base-point expectation re<psi,H psi>/||psi||^2,
-- well-defined on rays (baseEnergy_mk, the same quotient-descent as momentMap), invariant under any
-- unitary commuting with H (baseEnergy_smul_invariant: <Uv,HUv> = <v,(U*HU)v> = <v,Hv> plus unitary
-- norm preservation), hence CONSERVED BY THE WITNESS FLOW (onticEnergy_flow_invariant -- the
-- Schrodinger unitary is exp((-it)H), which commutes with H). The flow conserves its own generator:
-- the first Hamiltonian signature.
-- (2) ★ THE A5 JUNCTION. onticEnergy H is fibre-independent by construction, so it is
-- EpsProjectable _ 0 (onticEnergy_epsProjectable): it IS the canonical h of the exact case
-- H = h.pi. A2's conserved quantity and A5's projectable Hamiltonian are the SAME OBJECT.
-- (3) THE COMMUTING PHASE TORUS. phaseDiag phi = diag(e^{i phi_k}) is unitary; the action is
-- additive hence commuting (phaseDiag_add / phaseDiag_comm) and PRESERVES EVERY MOMENT-MAP
-- COORDINATE (momentMap_phaseDiag_invariant) -- the flow-level shadow of "the moment map generates
-- the torus action" (the generating statement needs the symplectic form; scoped). The fibre half of
-- the torus signature is ShearWitness's pshift translations, measure-preserving, already in place.
-- Together with the Liouville property and group laws already proved of the witness flow, the
-- honest claim: EVERY property of "Hamiltonian flow" expressible without the manifold API is proved
-- of the witness flow; the vector-field equation itself is scoped. A2's unscoped content is
-- discharged; what remains of A2 is exactly its scoped half.
/-- info: 'CSD.RecordLayer.baseEnergy_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.baseEnergy_mk

/-- info: 'CSD.RecordLayer.baseEnergy_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.baseEnergy_smul_invariant

/-- info: 'CSD.RecordLayer.onticEnergy_flow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.onticEnergy_flow_invariant

/-- info: 'CSD.RecordLayer.onticEnergy_epsProjectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.onticEnergy_epsProjectable

/-- info: 'CSD.RecordLayer.momentMap_phaseDiag_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.momentMap_phaseDiag_invariant

/-- info: 'CSD.RecordLayer.phaseDiag_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.phaseDiag_comm

-- A6 STEP ONE: THE SEGRE EMBEDDING AND NON-FACTORISATION (2026-08-02,
-- SigmaLayer/OnticComposite.lean).
-- Paper C A6's "the composite ontic sector is NOT the product of the subsystem sectors" made sharp:
-- segre ([u],[v]) = [u (x) v] is INJECTIVE (segre_injective -- product rays remember their factors;
-- the scalar is recovered from a nonzero coordinate of the other factor) but NOT SURJECTIVE
-- (segre_not_surjective) whenever both factors have dimension >= 2: the Bell-type ray
-- [e0(x)e0 + e1(x)e1] is not a product ray -- the four corner coordinates give u0v0 = c, u1v1 = c,
-- u0v1 = 0, u1v0 = 0, and (u0v0)(u1v1) = c^2 != 0 = (u0v1)(u1v0). Hence
-- Sigma_AB STRICTLY EXCEEDS image(Sigma_A x Sigma_B): non-factorisation as a THEOREM, at every
-- dimension pair >= 2x2.
-- ⚠️ SCOPE: witness-level A6 content. The corpus CONSTRUCTS the composite sector from the composite
-- Hilbert space; A6-as-philosophy ("Sigma_AB is primitive") is not a formalisation target and is not
-- claimed. Steps 2-3 (ontic reduction maps via partialTrace; marginal stability under local flows =
-- ontic no-signalling) are NOT in the file. Measure statements (Segre image mu_FS-null) not
-- attempted; the strict inclusion carries the axiom's weight.
/-- info: 'CSD.RecordLayer.segre_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_mk

/-- info: 'CSD.RecordLayer.segre_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_injective

/-- info: 'CSD.RecordLayer.segre_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_not_surjective

-- Q28 ITEM 2 (2026-08-21, OnticComposite.lean + EntangledMeasure.lean): ENTANGLED RAYS
-- CARRY POSITIVE FUBINI-STUDY WEIGHT -- the C2-blocking item, in topological-neighbourhood
-- form (no metric on P exists; MATHLIB-GAPS). Topology: segre_range_isClosed (compact image
-- in a Hausdorff target -- the product rays are closed, so the entangled rays are OPEN);
-- not_mem_range_segre (the reusable minor criterion: one unbalanced 2x2 minor of the
-- coefficient matrix puts a ray outside the Segre image; segre_not_surjective's Bell
-- computation is the (0,0,1,1) case); exists_entangled_mem_nhds (the path
-- [a (x) b + t e_(j1,k1)] -- a SINGLE standard-basis perturbation, no orthogonal
-- complements -- is continuous, lands on the product ray at t = 0, and fails the minor
-- criterion for t /= 0). Measure: compositeFubiniStudy (THE FS measure carried across the
-- canonical index bijection Fin nA x Fin nB ~ Fin (nA*nB); probability; full support --
-- compositeFubiniStudy_pos_of_isOpen); compositeFubiniStudy_entangled_pos_global (the
-- entangled complement has positive measure -- open by 2a, nonempty by
-- segre_not_surjective); compositeFubiniStudy_entangled_pos (EVERY open neighbourhood of a
-- product ray meets the entangled complement in positive measure).
-- SCOPE CORRECTED 2026-08-25: this block previously ended "the set a PBR-style product-
-- supported law must give measure zero; the C2 contradiction". That reading is WITHDRAWN.
-- These are composite-GEOMETRY results. Global non-factorisation of the composite ontology
-- does NOT establish that PBR preparation independence fails, and nothing here is a PBR
-- contradiction. The corrected exact-state PBR classification is
-- RecordLayer/PBRPreparation.lean; see specs/c2-support-plan.md for the supersession.
/-- info: 'CSD.RecordLayer.segre_range_isClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_range_isClosed

/-- info: 'CSD.RecordLayer.not_mem_range_segre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.not_mem_range_segre

/-- info: 'CSD.RecordLayer.exists_entangled_mem_nhds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.exists_entangled_mem_nhds

/-- info: 'CSD.RecordLayer.compositeFubiniStudy_pos_of_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compositeFubiniStudy_pos_of_isOpen

/-- info: 'CSD.RecordLayer.compositeFubiniStudy_entangled_pos_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compositeFubiniStudy_entangled_pos_global

/-- info: 'CSD.RecordLayer.compositeFubiniStudy_entangled_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compositeFubiniStudy_entangled_pos

-- Q28 ITEM 5, DE-RESEARCH-GATED 2026-08-22 (MG-2, specs/mathlib-gaps-plan.md): the positive-
-- measure statements above upgrade to the SHARP form. The Segre (product) rays are NULL, so a
-- Fubini-Study-typical composite state is entangled. Route: Fubini-Study is the
-- projectivization of a Lebesgue-a.c. measure (FubiniStudyLebesgue.lean), so a ray set whose
-- vector cone is Lebesgue-null is null; the Segre cone sits inside the zero set of ONE
-- coordinate quadratic (segre_minor_eq's 2x2 minor at the corner, read through the index
-- bijection), and that is null by Fubini slicing. The general polynomial-zero-set lemma was
-- NOT needed and is recorded as pure optionality.
/-- info: 'CSD.RecordLayer.compositeFubiniStudy_range_segre_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compositeFubiniStudy_range_segre_null

/-- info: 'CSD.RecordLayer.ae_not_mem_range_segre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.ae_not_mem_range_segre

-- Q28 ITEMS 3 AND 4 (2026-08-21, IsolationPreparation.lean + PreparationDensity.lean):
-- RHO_EP AND FINITE-RESOLUTION PREPARATION OVERLAP. (Header corrected 2026-08-25: this
-- read "THE PSI-EPISTEMIC OVERLAP". Region-preparation overlap is NOT Harrigan-Spekkens
-- psi-epistemicity of exact pure states -- it is a fact about a different preparation
-- class. The exact interface is psi-ONTIC: RecordLayer/PBRPreparation.lean.)
-- Item 4a: conditional_not_mutuallySingular --
-- preparations with Liouville-positive region overlap have NON-mutually-singular
-- conditional laws (a DENSITY argument, not shared support: on the overlap both are
-- normalised restrictions of the same Liouville measure, so a singularity witness covers
-- the overlap by two null sets). Item 3: projectivePreparationLaw_absolutelyContinuous
-- (under a bridge pi_* muL = c * muFS -- no c /= 0 needed for this direction) and
-- projectivePreparationLaw_withDensity (rho_ep := rnDeriv; the law IS muFS.withDensity
-- rho_ep -- the object Papers C and TN2 use, in the corpus for the first time).
-- The Kahler seam at c = 1: kahlerFstSector_projectiveLaw (the base pushforward of kMuL
-- IS the FS measure), kahler_preparation_density (rho_ep concrete for every region
-- preparation on KSigma -- the first statement mentioning both SigmaLayer.Preparation and
-- the LF4 bridge, the seam where C2 v1.01 tore). Item 4b: kahler_preparations_overlap --
-- preparations localised on overlapping open neighbourhoods of their own rays are not
-- mutually singular (the FINITE-RESOLUTION preparation-overlap witness, topological
-- existence form; the epsilon-ball form needs the FS metric, MATHLIB-GAPS). This does not
-- classify exact pure-state preparations as psi-epistemic.
/-- info: 'CSD.SigmaLayer.Preparation.conditional_not_mutuallySingular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.Preparation.conditional_not_mutuallySingular

/-- info: 'CSD.SigmaLayer.ProjectiveSector.projectivePreparationLaw_absolutelyContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.ProjectiveSector.projectivePreparationLaw_absolutelyContinuous

/-- info: 'CSD.SigmaLayer.ProjectiveSector.projectivePreparationLaw_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.ProjectiveSector.projectivePreparationLaw_withDensity

/-- info: 'CSD.SigmaLayer.kahlerFstSector_projectiveLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.kahlerFstSector_projectiveLaw

/-- info: 'CSD.SigmaLayer.kahler_preparation_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.kahler_preparation_density

/-- info: 'CSD.SigmaLayer.kahler_preparations_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.kahler_preparations_overlap

/-- info: 'CSD.SigmaLayer.kMuL_fibre_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.kMuL_fibre_null

-- Q26 (2026-08-21, RecordLayer/EpistemicDisintegration.lean): THE EPISTEMIC MEASURE IS A
-- DISINTEGRATION, NOT A DEFINITION -- the external review's third point, and the gap
-- GlobalBasin's own design note named. kMuL_fst (the c = 1 bridge as a marginal);
-- kMuL_eq_compProd_const (kMuL = fst (x)_m const-Haar); kMuL_condKernel_ae -- THE
-- IDENTIFICATION: the disintegration kernel of kMuL is mu_FS-a.e. the constant Haar
-- kernel (Mathlib standard-Borel condKernel + a.e. uniqueness applied to the constant
-- kernel); epistemicMeasure_eq_disintegration -- THE HEADLINE: delta_p (x) Haar IS the
-- fibre of the arena's own disintegration, planted at its base point, mu_FS-a.e.;
-- kMuL_disintegration (the reassembly kMuL = mu_FS (x)_m condKernel). The a.e. form IS
-- the theorem (kernels are only determined up to base-null sets). GlobalBasin's
-- "modelling choice stated as a definition" note superseded at source.
/-- info: 'CSD.RecordLayer.kMuL_condKernel_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.kMuL_condKernel_ae

/-- info: 'CSD.RecordLayer.epistemicMeasure_eq_disintegration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epistemicMeasure_eq_disintegration

/-- info: 'CSD.RecordLayer.kMuL_disintegration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.kMuL_disintegration

-- A6 STEPS TWO AND THREE: ONTIC REDUCTION MAPS + MARGINAL STABILITY (2026-08-02,
-- SigmaLayer/OnticMarginals.lean).
-- STEP 2: rayDensity -- the density matrix of a composite ray, RAY-WELL-DEFINED (rayDensity_mk, the
-- quotient-descent pattern) and UNIT TRACE (rayDensity_trace): a genuine state. reduceA / reduceB:
-- the subsystem marginals as partial traces -- the ontic-level r_S, what a subsystem observer can
-- see of a single composite point.
-- STEP 3: actA U -- the local A-action (U (x) 1) in vector form, no Kronecker plumbing. The
-- workhorse is actA_column_sums: for U^H U = 1 the A-sums of transformed products equal the A-sums
-- of the originals, for EVERY pair of B-indices -- one computation carrying the norm preservation
-- (norm_actA) and both marginal laws:
-- ★★ reduceB_pointA_invariant  MARGINAL STABILITY = ONTIC NO-SIGNALLING: a local unitary on A
--                              leaves the B-marginal of the composite ray UNCHANGED. Acting on A
--                              changes nothing B can see, at the level of the single ontic point --
--                              the ontic form of the operational tensorSector_no_signalling.
-- reduceA_pointA_conj          the A-marginal evolves by CONJUGATION -- the Heisenberg law.
-- ★★ reduceB_local_flow_invariant  the Schrodinger flow of ANY A-Hamiltonian leaves the B-marginal
--                              fixed AT EVERY TIME -- A6's marginal-stability clause in flow form.
-- ⚠️ SCOPE: kinematic identities about the reduction maps under local unitaries -- exactly what
-- A6's clause asserts; no new dynamics claimed. Step 4 (DYNAMICAL no-signalling through the v0.7.0
-- measurement layer) is NOT here. Defined at the projective level; the torus fibre plays no role in
-- reduction.
-- WITH THIS, EVERY A6 CLAUSE THE CORPUS CAN EXPRESS IS A THEOREM: non-factorisation (step 1),
-- reduction maps (step 2), marginal stability (step 3). The A1-A7 map has NO unscoped open rows
-- left.
/-- info: 'CSD.RecordLayer.rayDensity_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rayDensity_trace

/-- info: 'CSD.RecordLayer.actA_column_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.actA_column_sums

/-- info: 'CSD.RecordLayer.reduceB_pointA_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceB_pointA_invariant

/-- info: 'CSD.RecordLayer.reduceA_pointA_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceA_pointA_conj

/-- info: 'CSD.RecordLayer.reduceB_local_flow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceB_local_flow_invariant

-- BB84 INTERCEPT-RESEND WITH A DYNAMICAL COLLAPSE STEP (2026-08-02,
-- Empirical/CSD/Crypto/BB84Sequential.lean + SigmaLayer/RotatedContext.lean).
-- The QM module (Crypto/BB84.lean) models Eve's measure-and-resend as a CLASSICAL MARGINAL, with a
-- scope note gating the collapse operator on "the LF5 gate". The dynamical measurement layer
-- dissolved that gate; this entry replaces the posited marginal with the calibrated-swap dynamics:
-- ★ basisContext_rate_mk (RotatedContext): the context field of an apparatus measuring in ANY
-- orthonormal basis, rates = rotated Born weights ‖⟨b i, ψ⟩‖² -- the unitary-covariance seed. With
-- it, csd_sequential_born extends to CROSS-BASIS follow-ups.
-- ★ prep_outcome_pos (SequentialMeasurement): for the canonical ready preparation, hpos is a
-- THEOREM whenever the Born weight is nonzero -- conditioning licensed by the preparation, the
-- carried-hypothesis caveat discharged at every concrete preparation.
-- ★ bb84_wrong_basis_bob (+ _error): Alice sends |+>, Eve Z-measures (the swap witness's native
-- basis), Bob reads the rotated X-context: every Bob basin has probability EXACTLY 1/2 whatever
-- Eve saw -- the 1/2 disturbance with the collapse a pushforward theorem. Both measurements are
-- context-field reads of the dynamical layer: the sequential composition is end-to-end.
-- ★ bb84_right_basis_no_disturbance / _faithful: Eve in the matching basis is exactly
-- repeatability -- error basin null, correct basin certain. Eve learns the bit and disturbs nothing.
-- bb84_eve_selector_born: Eve's outcome weights on |+> are a fair coin (the information side).
-- ⚠️ Dual round of the QM module's (Alice X / Eve Z, so Eve is computational-basis); one sifted
-- round; Eve's basis choice + the 1/4 average stay classical bookkeeping on the QM side
-- (bb84_dynamical_matches_marginal records the correspondence); composable finite-key remains the
-- recorded QKD tranche.
/-- info: 'CSD.RecordLayer.basisContext_rate_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.basisContext_rate_mk

/-- info: 'CSD.RecordLayer.prep_outcome_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
-- (moved 2026-08-02 from Empirical/CSD/SequentialMeasurement.lean to SigmaLayer/SwapClosure.lean)
#print axioms CSD.RecordLayer.prep_outcome_pos

-- THE MEASUREMENT PROPAGATOR IS PROVABLY NOT CONTINUOUS (2026-08-02,
-- SigmaLayer/ShearDiscontinuity.lean; machine-checks an external review's claim).
-- ★ shearEvolve_not_continuous: over the measurement interval the shear witness displaces the
-- register by shearAmt(basinIndex x); if continuous, its register marginal would be a continuous
-- map from the CONNECTED KSigma onto >= 2 distinct points, whose fibres give a clopen partition --
-- impossible. Consequence: the witness is a measurable, measure-preserving, PIECEWISE map, not a
-- time slice of any continuous flow -- so the earlier "Hamiltonian generation = permanently scoped
-- (Mathlib gap)" classification was misjustified and is REOPENED (specs/BACKLOG.md). Context that
-- keeps this honest in both directions: no_everywhere_correlation already proves SOME seam set is
-- forced for every exact-record dynamics -- the witness's jumps sit exactly where the no-go says
-- they must. Supporting: ℂℙ^{N-1} is CONNECTED (staged connectedSpace_of_isConnected_nonzero via
-- isConnected_compl_singleton_of_one_lt_rank at real rank 2N); vertex basin inhabitants; pairwise
-- distinct shear displacements.
/-- info: 'CSD.RecordLayer.shearEvolve_not_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shearEvolve_not_continuous

/-- info: 'CSD.RecordLayer.vertex_mem_globalBasin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.vertex_mem_globalBasin

-- THE PIECEWISE-HAMILTONIAN CLASSIFICATION (2026-08-02, SigmaLayer/PiecewiseHamiltonian.lean;
-- the decision resolving the reopened Hamiltonian-origin row -- route 2, user decision).
-- ★ shear_piecewise_hamiltonian: (1) on every basin cylinder the propagator IS an explicit rigid
-- register translation -- a Hamiltonian flow slice -- and is ContinuousOn there
-- (shearEvolve_eq_translation_on_basin, shearEvolve_continuousOn_basin); (2) the seam set outside
-- the cylinders is NULL (seam_null, via globalBasin_ae_total through the product). Together with
-- shearEvolve_not_continuous (the seams are real) and no_everywhere_correlation (they are forced
-- for every exact-record dynamics): piecewise rigid SYMPLECTIC translation, null seam set.
-- CORRECTED 2026-08-04 (audit): this read "piecewise Hamiltonian" long after
-- PiecewiseHamiltonian.lean's header WITHDREW that reading (on T^2, iota_X omega = a*dp is
-- closed but NOT exact, so no global generator exists). The pieces are symplectic, not
-- Hamiltonian; the theorem name is a known misnomer kept for pin stability.
-- ⚠️ The h_i = shearAmt(i)·p_R reading of each piece is prose (the symplectic spelling is the
-- genuine §2a Mathlib gap); corridor regularisation stays recorded as optional strengthening.
/-- info: 'CSD.RecordLayer.shear_piecewise_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_piecewise_hamiltonian

/-- info: 'CSD.RecordLayer.shearEvolve_eq_translation_on_basin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shearEvolve_eq_translation_on_basin

/-- info: 'CSD.RecordLayer.seam_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.seam_null

-- ALL SIX DYNAMICAL FACTS ON ONE ARENA (2026-08-02, SigmaLayer/SwapClosure.lean; the external
-- review's step 2, the precursor to the engine migration).
-- ★ swapMeasurementClosure: ready ⇒ no record, record created, outcomes exclusive, record persists,
-- DYNAMICAL Born (sector measure = Born weight, via measure_outcomeSector_eq_of_correlates -- the
-- correlation theorem genuinely consumed), and rank-one Lüders -- every field a swapProtocol
-- statement on SwapArena at the canonical preparation swapPrep [ψ]. CorrelatesOn/PointerInvariantOn
-- proved (swap_correlates/swap_pointerInvariant), never assumed. Lüders carries NO measure
-- hypothesis: Born-weight positivity licenses the conditioning (prep_outcome_pos, moved here from
-- the empirical layer). ⚠️ The OPERATIONAL closure still lives on its own arena -- CsdFiniteQMClosure
-- remains a two-arena conjunction; this removes the split within the DYNAMICAL bundle only. The
-- engine migration proper stays recorded (BACKLOG).
/-- info: 'CSD.RecordLayer.swapMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapMeasurementClosure

/-- info: 'CSD.RecordLayer.swap_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_sector_born

-- ★★ THE ENGINE MIGRATION (2026-08-02, SigmaLayer/UnifiedArena.lean; review step 3 -- arena
-- unification step 2 of 2). ONE ontic model now carries the finite-QM reconstruction:
-- UnifiedArena M = ((ℂℙ^M × T²) × T²_R) × bank, with Liouville measure arenaLiouville =
-- swapMeasure at μs = kMuL -- so the measure the MEASUREMENT dynamics preserves IS the Liouville
-- measure the ISOLATED flow preserves (that coincidence is the migration's content).
-- ★★ unifiedArenaClosure: isolated exp(-itH) lifted to the arena preserves arenaLiouville
-- (arenaIso_measurePreserving) and projects to Schrödinger on rays (arenaIso_schrodinger); the
-- FS bridge holds through the arena marginals (arenaRay_pushforward); swapEvolve preserves the
-- SAME measure; the six dynamical facts hold (SwapMeasurementClosure field); i.i.d. Born
-- frequencies and mixed-state Born weights transfer through the system-slot marginal
-- (rfl-level cylinder identities). All ELEVEN operational fields accounted for in the module's
-- mapping table: migrated / upgraded / superseded-by-stronger / one recorded (mixed LLN, S).
-- ⚠️ CsdFiniteQMClosure (the two-arena conjunction) stays untouched as the historical capstone;
-- the composed round-trip theorem (isolate → measure → isolate) is recorded, not claimed.
/-- info: 'CSD.RecordLayer.unifiedArenaClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.unifiedArenaClosure

/-- info: 'CSD.RecordLayer.arenaIso_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaIso_measurePreserving

/-- info: 'CSD.RecordLayer.arenaIso_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaIso_schrodinger

/-- info: 'CSD.RecordLayer.arenaRay_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaRay_pushforward

-- THE MIGRATION RESIDUES, DISCHARGED SAME DAY (2026-08-02, UnifiedArena.lean second pass):
-- ★ arena_round_trip -- isolate → measure → isolate: the record is created from the evolved
-- state's selector and SURVIVES subsequent isolated evolution (readout_arenaIso: the pointer
-- register is a conserved coordinate of the lifted flow -- definitional, rfl). The first theorem
-- composing the Schrödinger and measurement propagators; not stateable before the migration.
-- arena_mixed_born_frequency -- the mixed two-stage LLN on the arena (rfl-level transfer).
/-- info: 'CSD.RecordLayer.arena_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arena_round_trip

/-- info: 'CSD.RecordLayer.arena_mixed_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arena_mixed_born_frequency

-- DEGENERATE LÜDERS, THE JOIN ROUTE, BRICK 1 (2026-08-02, SigmaLayer/BlockCollapse.lean; review
-- step 4 opened). swap_not_blockLuders proved no FIXED calibration works; this brick builds the
-- object every witness must realise and the mechanism one level above the rays:
-- ★ blockCollapse -- the measurable ray-level collapse [ψ] ↦ [Πᵢψ] (quotient descent via
-- Projectivization.lift; measurability through measurable_iff_measurable_comp_mk').
-- ★ luders_target_eq_relocation + blockLudersObligation_iff_relocation -- COLLAPSE AS RELOCATION:
-- the §8.3 target epistemicMeasure [Πᵢψ] IS the pushforward of the preparation under the
-- deterministic relocation (base ray collapses, fibre untouched); the obligation is exactly the
-- demand that a witness realise this pushforward as its conditioned trace.
-- ★ componentSwap_collapse/_stores (+ _involutive, _norm_sum) -- the VECTOR-LEVEL witness core:
-- on ℂ^N ⊕ ℂ^N, keep block parts, swap complements: with a block-calibrated slot this performs
-- exactly the collapse WITH THE RESIDUAL STORED (no_exact_collapse respected by storage), and it
-- is involutive + summed-norm-preserving (the unitary content).
-- ⚠️ THE WALL, SHARPENED: the ray-pair version is ill-defined -- the stored residual depends on
-- the relative scale the product ℙ×ℙ quotient forgets (a surviving relative U(1) is needed).
-- Recorded routes: (i) FS disintegration under join coordinates; (ii) NEW -- a phase-carrying
-- slot (sphere-level bank), likely cheaper. swap_not_blockLuders remains the honest boundary;
-- NO ray-level witness is claimed.
/-- info: 'CSD.RecordLayer.luders_target_eq_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.luders_target_eq_relocation

/-- info: 'CSD.RecordLayer.blockLudersObligation_iff_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.blockLudersObligation_iff_relocation

/-- info: 'CSD.RecordLayer.componentSwap_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.componentSwap_collapse

/-- info: 'CSD.RecordLayer.measurable_blockCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_blockCollapse

-- ★★ THE PHASE-CARRYING SLOT: DEGENERATE LÜDERS REALISED (2026-08-02,
-- SigmaLayer/PhaseSlot.lean; route (ii) of the sharpened wall, brick 2).
-- ★★ phase_slot_block_luders: prepare the PHASE ORBIT of ψ (uniform over the ontic phase --
-- the enrichment adds ontic phase, not epistemic content: readout_phasePrep gives back the
-- Dirac at [ψ]); calibrate the slot with a FIXED block-supported α; fire the pair swap; read
-- out the system ray: the result is EXACTLY δ_{[Πᵢψ]} -- the blockLudersObligation target --
-- for every preparation with nonvanishing block component.
-- ★ pairSwap: TOTAL + INVOLUTIVE + MEASURABLE -- fire componentSwap exactly when both outputs
-- are nonzero; at a fired image the condition holds automatically (componentSwap involutive +
-- inputs nonzero), so the conditional map is a genuine involution: reversibility, hence
-- storage, hence no_exact_collapse respected.
-- WHY THE NO-GO IS EVADED, not contradicted: swap_not_blockLuders killed FULL swaps (post-
-- system = slot's prior content, preparation-independent); the PARTIAL swap keeps the system's
-- block part and stores its complement -- fixed calibration, preparation-dependent post-state.
-- The partial swap needed the phase-enriched arena, exactly as the sharpened wall said.
-- ⚠️ Brick 3 still owed (BACKLOG): register/sector protocol plumbing on the enriched arena +
-- Liouville preservation (unitarily-invariant reference measure, e.g. Gaussian; effort M).
/-- info: 'CSD.RecordLayer.phase_slot_block_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.phase_slot_block_luders

/-- info: 'CSD.RecordLayer.pairSwap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pairSwap_involutive

/-- info: 'CSD.RecordLayer.readout_phasePrep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.readout_phasePrep

/-- info: 'CSD.RecordLayer.measurable_pairSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_pairSwap

-- ★★ THE JOIN ARENA: LIOUVILLE-PRESERVING DEGENERATE LÜDERS (2026-08-02,
-- SigmaLayer/JoinArena.lean; brick 3's Liouville half). The identification that closes the arc:
-- THE PHASE-ENRICHED PAIR ARENA IS THE PROJECTIVE JOIN ℙ(ℂ^{N+N}) -- a system-slot pair
-- quotiented only by the GLOBAL phase, so the relative phase (the join coordinate the wall
-- demanded) lives in the point itself. There the component swap is a PERMUTATION UNITARY
-- (joinMat_mem_unitaryGroup), and:
-- ★★ joinSwap_measurePreserving -- Liouville preservation = Fubini-Study unitary invariance,
-- discharged by fubiniStudyMeasure_smul_invariant. The obligation recorded as the route's hard
-- half is a ONE-LINE consequence of the dynamics being unitary.
-- ★★ join_block_luders -- the Lüders update POINTWISE: every join microstate [ψ ⊕ α] with
-- nonvanishing block component and block-supported slot reads out post-swap to EXACTLY [Πᵢψ].
-- Deterministic at every microstate; PhaseSlot's measure form is the orbit-averaged shadow.
-- (The slot's nonvanishing is not even needed -- the hypothesis list is minimal.)
-- ⚠️ Remaining (BACKLOG, mechanical M): the register/sector MeasurementProtocol on
-- ℙ(ℂ^{N+N}) × T²_R firing joinSwap, mirroring SwapWitness. No new mathematics.
/-- info: 'CSD.RecordLayer.join_block_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_block_luders

/-- info: 'CSD.RecordLayer.joinSwap_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinSwap_measurePreserving

/-- info: 'CSD.RecordLayer.joinMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinMat_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.measurable_joinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_joinFst

-- THE DEGENERATE MEASUREMENT AS A MeasurementProtocol (2026-08-02, SigmaLayer/JoinProtocol.lean;
-- brick 4 -- the protocol plumbing). The join update now runs inside the standard architecture:
-- arena = (join point, system fibre, ANCILLA fibre) x register; selector = coarse block index
-- (joinIdx); propagator = register shear + record-triggered joinG at the readout crossing (join
-- unitary on the point + system-fibre/ancilla-fibre exchange -- the degenerate analogue of the
-- rank-one fresh slot: the original fibre is STORED, not destroyed). Region/readout/sector/
-- persistence machinery inherited from shearProtocol by structure update.
-- ★ joinEvolve_measurePreserving -- the FULL propagator preserves the join-arena Liouville
-- measure (FS x vol x vol) x vol at every time pair (generic shear theorem + FS unitary
-- invariance + the fibre-transposition shuffle, glued by the register-arc partition).
-- join_correlates / join_pointerInvariant discharged from the construction; joinG_joinG is the
-- involution (reversibility = storage). ⚠️ Brick 5 (last): the sector-conditioned post-marginal
-- = epistemicMeasure [Πᵢψ] -- the BlockLudersObligation instance (BACKLOG).
/-- info: 'CSD.RecordLayer.joinEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.join_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_correlates

/-- info: 'CSD.RecordLayer.join_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_pointerInvariant

/-- info: 'CSD.RecordLayer.joinG_joinG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinG_joinG

-- ★★ BlockLudersObligation, INHABITED (2026-08-02, SigmaLayer/JoinLuders.lean; brick 5 -- the
-- degenerate-Lüders arc CLOSED). The §8.3 demand that swap_not_blockLuders proved impossible for
-- every fixed ray-level calibration is DELIVERED by the join witness:
-- ★★ joinWitness_blockLuders -- with any block-supported calibration family, the sector-
-- conditioned post-measurement system readout equals epistemicMeasure [Πᵢψ] for EVERY preparation
-- with nonvanishing block component. ψ-dependent post-states from a FIXED calibration, through
-- Liouville-preserving dynamics inside the standard MeasurementProtocol architecture.
-- ★ join_luders_marginal -- the computation: conditioning commutes with the preparation
-- pushforward (cond_map); the sector pulls back to a SYSTEM-FIBRE cylinder (the phase orbit has
-- constant ray, so the selector never sees the phase); product conditioning factorises
-- (cond_prod_prod); on the conditioned support the readout is [Πᵢψ] at every phase with the
-- ANCILLA's fibre; the conditioned original fibre integrates out -- stored, not destroyed.
-- goodTheta_vol_pos: positivity from Πᵢψ ≠ 0 alone -- the obligation carries NO measure
-- hypothesis. The rank-one (SwapLuders) and degenerate (here) updates now stand on the same
-- architectural footing; swap_not_blockLuders stands as the theorem for WHY the ray-pair arena
-- was too small.
/-- info: 'CSD.RecordLayer.joinWitness_blockLuders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinWitness_blockLuders

/-- info: 'CSD.RecordLayer.join_luders_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_luders_marginal

/-- info: 'CSD.RecordLayer.goodTheta_vol_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.goodTheta_vol_pos

/-- info: 'CSD.RecordLayer.basisContext_basisFun_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.basisContext_basisFun_rate

-- ★★ THE UNITARY-COVARIANCE LAW (2026-08-02, SigmaLayer/RotatedSwap.lean; the last extension
-- item of the dynamical arc). The first measurement now runs in ANY orthonormal basis:
-- ★★ measurement_covariance -- for EVERY orthonormal basis bON and every state, the full
-- six-fact measurement closure holds (RotatedSwapClosure): selector = the rotated context's
-- basins, bank calibrated on the rotated vertices [bON i], dynamical Born = ‖⟨bON i, ψ⟩‖²,
-- Lüders to [bON i]. The apparatus basis is a PARAMETER of the context field, not a preferred
-- structure of Σ. Pure instantiation: swap_luders_marginal was always selector- and
-- calibration-generic; the new content is the context-generic swap-arena accounting
-- (sector_born_ctx, prep_outcome_pos_ctx -- generalising the momentContext instances).
-- ★ bb84_primal_wrong_basis (BB84Sequential): the QM module's OWN round (Alice Z / Eve X /
-- Bob Z), end-to-end dynamical -- the dual-round caveat retired.
/-- info: 'CSD.RecordLayer.measurement_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurement_covariance

/-- info: 'CSD.RecordLayer.rotated_swap_luders_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rotated_swap_luders_born

/-- info: 'CSD.RecordLayer.sector_born_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.sector_born_ctx

-- STEP FIVE (2026-07-29): THE (n-1)/n SUPPORT BOUND, as a theorem.
-- vanishes_below_of_balanced: given (a) step four's output -- for a.e. phi some outcome i has
-- g == 0 on [0, 1 - s_i(phi)] -- and (b) that states with ALL overlaps <= c are non-null for every
-- c above the forced minimum 1/n, the density VANISHES ON EVERY OVERLAP VALUE BELOW (n-1)/n.
-- The step is short for a structural reason worth noting: step four's conclusion is POINTWISE IN g
-- (g dies on a whole interval, for a.e. phi). g is a fixed function, so ONE suitable phi suffices
-- and no almost-everywhere bookkeeping survives into the conclusion -- hence the helper
-- exists_mem_of_measure_pos_of_ae (a positive-measure set meets any a.e. property) is all that is
-- needed to bridge measure to pointwise.
-- At n = 2 the bound reads "g vanishes below 1/2", exactly the support of the known solution
-- 4(2s-1)+ -- sharp at the one dimension where a solution exists.
-- STILL CONDITIONAL for mu_FS on hypothesis (b): the balanced-state abundance. Its proof shape is
-- settled (barycentre box, side min(b,c-b)/(M+1)) but was NOT landed 2026-07-29 -- see the note in
-- ContextFixedA7FS.lean and the BACKLOG row. Not stubbed, not claimed.
/-- info: 'CSD.SigmaLayer.exists_mem_of_measure_pos_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.exists_mem_of_measure_pos_of_ae

/-- info: 'CSD.SigmaLayer.vanishes_below_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.vanishes_below_of_balanced

-- STEP FOUR (2026-07-29): ORTHOGONAL PREPARATIONS -- the first GENERIC-psi input.
-- Steps one to three used only the n basis-vector preparations. This uses psi PERPENDICULAR to
-- e_i: the Born weight |<e_i|psi>|^2 is then zero, so the same nonnegativity argument applies --
-- but now for a whole FAMILY of psi rather than one. orthogonal_preparation_vanishes: on Omega_i
-- the density vanishes at every overlap value any such psi realises.
-- vanishes_on_interval_of_dense upgrades that from the realised values to an INTERVAL, given
-- continuity of g and density of the realised values. The geometric input: for unit psi in the
-- sphere of e_i-perp, |<psi|phi>|^2 is maximised at the normalised projection of phi into
-- e_i-perp with value 1 - s_i(phi), and tilting psi within e_i-perp sweeps continuously down to 0.
-- ★ THAT TILT NEEDS dim(e_i-perp) >= 2, i.e. N >= 3 -- at N=2 the orthocomplement is a LINE, psi
-- is unique up to phase, and only the single value 1 - s_i(phi) is realised. Same threshold as
-- steps two and three, for a THIRD independent reason.
-- Consequence (analysis, not yet formalized -- the covering + max-coordinate step remains):
-- g vanishes below (n-1)/n, sharpening the cap from 1/2. At n=2 that reads "below 1/2", which is
-- exactly where the known solution 4(2s-1)+ is supported -- sharp at the one dimension where a
-- solution exists.
/-- info: 'CSD.SigmaLayer.orthogonal_preparation_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.orthogonal_preparation_vanishes

/-- info: 'CSD.SigmaLayer.vanishes_on_interval_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.vanishes_on_interval_of_dense

-- STEP THREE (2026-07-28): THE CAP IS NOW UNCONDITIONAL AT N >= 3
-- (SigmaLayer/ContextFixedA7FS.lean). Step two left the cap conditional on an ABUNDANCE
-- hypothesis -- that two overlap coordinates can jointly take values in any positive-measure set
-- below 1/2. fs_joint_abundance DISCHARGES it for the actual Fubini-Study measure, via the
-- corpus's own pushforward fs_volume_eq_dirichlet_inter (mu_FS pushes to the UNIFORM/Dirichlet
-- measure on the open simplex). Abundance then reduces to Lebesgue positivity on Fin M -> R, with
-- an EXPLICIT witness: the two chosen coordinates in T, every other coordinate in a small (0, eps).
-- The one subtlety is that T subset (0,1/2) bounds t_j + t_k < 1 POINTWISE BUT NOT UNIFORMLY, so
-- exists_trunc_of_volume_pos first passes to a positive-measure part of T bounded away from 1/2 --
-- only then is there uniform room for the remaining coordinates.
-- ★ fs_cap_unconditional: a base-only, U(N)-covariant, NONNEGATIVE preparation density reproducing
-- Born on the Fubini-Study sector VANISHES A.E. ON OVERLAP VALUES BELOW 1/2, with no hypothesis
-- left over. Sharp and attained -- the N=2 density 4(2s-1)+ is supported exactly on (1/2, 1].
-- ★ WHY N >= 3 IS EXACTLY THE THRESHOLD: M = N-1 is the number of free simplex coordinates, and
-- two DISTINCT ones exist precisely when M >= 2. At N=2 there is one free coordinate and the second
-- Born weight is 1 - s_1 -- functionally dependent (ContextFixedA7.joint_degenerate_of_sum_eq_one).
-- So the dimension count that powers this file is the same one that exempts the qubit.
-- This replaces the NUMERICAL evidence the retracted "provably dead" row rested on with a DERIVED
-- constraint. Still not the no-go: generic-psi and the harmonic argument remain open.
/-- info: 'CSD.SigmaLayer.exists_trunc_of_volume_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.exists_trunc_of_volume_pos

/-- info: 'CSD.SigmaLayer.volume_inter_openSimplexFree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.volume_inter_openSimplexFree_pos

/-- info: 'CSD.SigmaLayer.fs_joint_abundance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_joint_abundance

/-- info: 'CSD.SigmaLayer.fs_cap_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_cap_unconditional

-- SigmaLayer Tranche 1 (2026-07-12): the projective-sector foundation. ConstraintDynamics (deterministic
-- measure-preserving one-parameter-group ontic flow), RecordedFact/RecordSemantics/compatibleSet
-- (records as measurable contextual events; isolation = conditioning muL on the record history),
-- IsolationPreparation (LF1 adapter reusing prepMeasure), ProjectiveSector (measurable pi to CP^{N-1}, not
-- injective), and the Kähler adapters. No Born/unitarity/Fubini-Study as fields; those are uninhabited
-- theorem-target predicates (TheoremTargets). Foundational triple only.
/-- info: 'CSD.SigmaLayer.ConstraintDynamics.flow_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ConstraintDynamics.flow_bijective

/-- info: 'CSD.SigmaLayer.compatibleSet_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_measurable

/-- info: 'CSD.SigmaLayer.compatibleSet_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_append_singleton

/-- info: 'CSD.SigmaLayer.Preparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.Preparation.conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.HistoryPreparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.ProjectiveSector.projectiveLaw_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ProjectiveSector.projectiveLaw_apply

/-- info: 'CSD.SigmaLayer.kahlerProjectiveSector_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.kahlerProjectiveSector_pi

-- SigmaLayer Tranche 2 (2026-07-13): the de-isolation measurement layer + the concrete product forward
-- capstone. productSector_hasFubiniStudyPushforward proves bridge B1 (pi_*(muFS ⊗ vol) = muFS) for the
-- CP^{N-1}×T² product model; productProjectedFlow_hasHamiltonianRealisation inhabits target T5
-- (exp(-itH) realisation); product_projectiveSector_forward_capstone bundles measure preservation + projectability
-- + T5 + B1, no open hypotheses. DeisolationModel + establishedFact are the measurement/record interface.
/-- info: 'CSD.SigmaLayer.productSector_hasFubiniStudyPushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productSector_hasFubiniStudyPushforward

/-- info: 'CSD.SigmaLayer.productProjectedFlow_hasHamiltonianRealisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productProjectedFlow_hasHamiltonianRealisation

/-- info: 'CSD.SigmaLayer.product_projectiveSector_forward_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.product_projectiveSector_forward_capstone

/-- info: 'CSD.SigmaLayer.compatibleSet_appendEstablishedFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_appendEstablishedFact

-- SigmaLayer Tranche 2b (2026-07-13): the concrete de-isolation model from the LF5 pointer machinery.
-- vnDeisolationModel is a fully theorem-backed DeisolationModel on CP^{M} (M+1 = N*N): interaction =
-- measurementFlow (measure-preserving unitary), readout = vnPointerOutcome, outcome regions = pointer
-- fibres. vnDeisolationModel_records proves the readout records the established outcome (B5);
-- vnDeisolationModel_ae_total proves the outcome is established for a.e. initial ontic state (target T6),
-- by transferring bornOutcome_ae_isSome through the measure-preserving interaction.
/-- info: 'CSD.SigmaLayer.vnDeisolationModel_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_records

/-- info: 'CSD.SigmaLayer.vnDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_ae_total

/-- info: 'CSD.SigmaLayer.lifted_projectiveSector_measurement_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lifted_projectiveSector_measurement_capstone

-- SigmaLayer Tranche 2b Born statistics (2026-07-13): the concrete de-isolation model reproduces the Born
-- FREQUENCIES, not merely a defined outcome. vnDeisolationModel_born_frequency transfers the LF5
-- outcome-frequency capstone measurement_flow_outcome_frequency through the measure-preserving
-- interaction (composed trial process measurementFlow ∘ fsTrial), so the pointer-i readout frequency
-- converges a.s. to ‖⟨eᵢ,ψ⟩‖². lifted_projectiveSector_measurement_born_capstone bundles the full measurement:
-- measure preservation + unique outcome a.e. + record establishment + a.e. total + Born frequencies.
/-- info: 'CSD.SigmaLayer.vnDeisolationModel_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_born_frequency

/-- info: 'CSD.SigmaLayer.lifted_projectiveSector_measurement_born_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lifted_projectiveSector_measurement_born_capstone

-- SigmaLayer Tranche 3 (2026-07-13): the composition/measurement targets (ledger T9-T15) as bridge interfaces
-- and uninhabited predicates (SigmaLayer/CompositeInterface.lean), inhabited by adapters wiring the existing
-- LF6/Empirical capstones (SigmaLayer/CompositeAdapters.lean). T15 no-signalling from the singlet marginals;
-- T14 Bell from the d-intrinsic CGLMP no-LHV force and the CHSH Tsirelson saturation; T13 contextuality
-- from Kochen-Specker (Cabello-18), Mermin-Peres and GHZ; T10 POVM normalisation. T9 (mixed states) left
-- out honestly: the ensemble/mixed-Born content is the reported Mathlib density-matrix gap.
/-- info: 'CSD.SigmaLayer.singlet_hasNoSignalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.singlet_hasNoSignalling

/-- info: 'CSD.SigmaLayer.maxEntangled_noLocalHiddenVariable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.maxEntangled_noLocalHiddenVariable

/-- info: 'CSD.SigmaLayer.singlet_hasTsirelsonSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.singlet_hasTsirelsonSeparation

/-- info: 'CSD.SigmaLayer.cabello18_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.cabello18_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.merminPeres_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.merminPeres_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.ghz_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ghz_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.povm_weightsProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.povm_weightsProbability

-- SigmaLayer interference (T16) + tensor weave (2026-07-14). hadamardTest_hasBornInterference inhabits the
-- two-path Born-interference target from the Hadamard test ((1 + Re⟨ψ,Uψ⟩)/2); interference is a
-- consequence of the complex sector (P7) + Born rule (T1/T2), not a postulate. The tensor weave shows
-- the finite tensor product ℂ^{NA} ⊗ ℂ^{NB} = ℂ^{NA·NB} is DERIVED (tensorIndexEquiv on Fin NA × Fin NB,
-- the local algebra aliceOp_bobOp_commute, operator no-signalling tensorSector_no_signalling); only the
-- composite-is-tensor bridge (CompositeSector.tensor_dimension, B6) is posited (P3 parked).
/-- info: 'CSD.SigmaLayer.hadamardTest_hasBornInterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.hadamardTest_hasBornInterference

/-- info: 'CSD.SigmaLayer.aliceOp_bobOp_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.aliceOp_bobOp_commute

/-- info: 'CSD.SigmaLayer.tensorSector_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.tensorSector_no_signalling

-- SigmaLayer time-indexed records + persistence (2026-07-15, SL-T5 final follow-on): makes records physical.
-- flowedSemantics event ⟨c,i,t⟩ = Φ_t⁻¹'(region c i) genuinely uses the recorded time (the pointer
-- semantics ignored it). flowedSemantics_event_measure: μL(event ⟨c,i,t⟩) = μL(region c i) -- record
-- probability conserved under isolated evolution. flowedSemantics_event_flow: event ⟨c,i,t+s⟩ =
-- Φ_s⁻¹'(event ⟨c,i,t⟩) -- record covariant with the flow. flowedSemantics_persistence bundles both.
/-- info: 'CSD.SigmaLayer.flowedSemantics_event_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_event_measure

/-- info: 'CSD.SigmaLayer.flowedSemantics_event_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_event_flow

/-- info: 'CSD.SigmaLayer.flowedSemantics_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_persistence

-- SigmaLayer post-outcome preparation (2026-07-15, SL-T5 follow-on): closes the measurement/record loop.
-- HistoryPreparation.appendFact constructs the post-measurement preparation on the extended history
-- (history ++ [r]); its compatible region compatibleSet ∩ event r has PROVEN nonzero measure when the
-- outcome is possible. appendFactOfPos builds it from positive conditional probability
-- (conditionalMeasure(event r) ≠ 0). appendFact_conditionalMeasure_apply: the post-measurement law is
-- the Bayesian update μL(A ∩ (compatible ∩ event))/μL(compatible ∩ event).
/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFact

/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFact_conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFact_conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFactOfPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFactOfPos

-- SigmaLayer conditional->Luders correspondence (2026-07-15, SL-T5 follow-on): connects the two conditioning
-- rules the review flagged as unlinked. bayesianConditional w = w(fine)/w(coarse); BOTH the projective
-- Luders update (ludersUpdate_isBayesianConditional, over the Born weight) and the ontic record-history
-- conditioning (historyConditioning_isBayesianConditional, over the Liouville measure) are instances.
-- luders_record_conditioning_correspondence bundles both -- one conditioning rule, two weights. That the
-- two weights AGREE (asserted there, not proved) is now a THEOREM: ConditioningLuders.lean.
/-- info: 'CSD.SigmaLayer.luders_record_conditioning_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.luders_record_conditioning_correspondence

-- SigmaLayer conditioning->Luders WEIGHT AGREEMENT (2026-07-17, ConditioningLuders.lean): the missing link the
-- review flagged. onticRegion_measure_eq_born: μL(π⁻¹ bornRegion i) = ‖⟨eᵢ,ψ⟩‖² -- the ontic measure of the
-- i-th OUTCOME REGION equals the Born weight, via B1 (π_*μL=μFS) + Born-from-volume. So the ontic and Born
-- conditioning weights are the SAME number (previously only asserted). conditioning_born_ratio_correspondence:
-- the ontic Bayesian conditional of the outcome regions = the ratio of Born weights (probability-level
-- correspondence). Residual: all-effects operational STATE equivalence via projWeight.
/-- info: 'CSD.SigmaLayer.onticRegion_measure_eq_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticRegion_measure_eq_born

/-- info: 'CSD.SigmaLayer.conditioning_born_ratio_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_born_ratio_correspondence

-- SigmaLayer #4 OPERATIONAL EQUIVALENCE (2026-07-17, ConditioningLuders.lean): the review's #4 for pointer-basis
-- effects. projWeight_rankOne: projWeight(rank-1 proj eₖ)ψ = ‖⟨eₖ,ψ⟩‖² -- the formalism bridge between the
-- projWeight (E→ₗE) weight and the Born/region weight. onticWeight_eq_ludersWeight: μL(π⁻¹ bornRegion i) =
-- projWeight(rankOneProj i)ψ -- the ontic and Lüders conditioning weights are LITERALLY equal per outcome.
-- conditioning_luders_operational_equivalence: the two conditionings give the SAME conditional probability,
-- each in its native weight -- operational equivalence as PREDICTIONS, not measure=vector. Residual:
-- non-pointer-basis / general-projector effects (sums over ranges).
/-- info: 'CSD.SigmaLayer.projWeight_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.projWeight_rankOne

/-- info: 'CSD.SigmaLayer.onticWeight_eq_ludersWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticWeight_eq_ludersWeight

/-- info: 'CSD.SigmaLayer.conditioning_luders_operational_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_luders_operational_equivalence

-- SigmaLayer #4 GENERAL-EFFECT extension (2026-07-17, ConditioningLuders.lean): #4 completed for ALL pointer-basis
-- effects. onticRegion_biUnion_measure_eq_born_sum: μL(π⁻¹ ⋃_{k∈S} bornRegion k) = ∑_{k∈S} ‖⟨eₖ,ψ⟩‖² --
-- the weight agreement for an effect S (union of regions = sum of Born weights), via additivity over the
-- pairwise-disjoint Born regions. conditioning_luders_effect_equivalence: the ontic and Lüders conditionings
-- give the SAME conditional probability for every pointer-basis effect. So #4 (operational equivalence) is
-- proved for all diagonal effects on the product model.
/-- info: 'CSD.SigmaLayer.onticRegion_biUnion_measure_eq_born_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticRegion_biUnion_measure_eq_born_sum

/-- info: 'CSD.SigmaLayer.conditioning_luders_effect_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_luders_effect_equivalence

/-- info: 'CSD.SigmaLayer.ludersUpdate_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ludersUpdate_isBayesianConditional

/-- info: 'CSD.SigmaLayer.historyConditioning_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.historyConditioning_isBayesianConditional

-- SL-T5 unified many-to-one measurement capstone (2026-07-15): dynamics + measurement on ONE ontic
-- model. unified_projectiveSector_capstone puts BOTH the isolated Hamiltonian flow (productDynamics, exp(-itH)•)
-- AND the de-isolation measurement (measurementFlow on the base fibre) on the SAME (Σ=ℂℙ^{M}×T², μL=μFS⊗
-- vol, π=Prod.fst): flow measure-preserving + Schrödinger-projectable + FS pushforward + interaction
-- measure-preserving + a.e. readout (T6, lifted through π) + record establishment (B5). Removes the
-- forward-vs-measurement model split. unifiedDeisolationModel_ae_total lifts the base a.e. via Prod.fst.
/-- info: 'CSD.SigmaLayer.unified_projectiveSector_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_projectiveSector_capstone

-- SigmaLayer #5 TIME-INDEXED RECORDS ON THE UNIFIED MODEL (2026-07-17, UnifiedFlowedRecords.lean): the review's
-- #5. unifiedFlowedSemantics = flowedSemantics over the isolated flow productDynamics with the pointer-fibre
-- region; unified_records_persistence instantiates flowedSemantics_persistence ON the unified model (Born
-- weight conserved + flow-covariant under the exp(-itH) evolution); unifiedFlowedSemantics_zero: the static
-- vnRecordSemanticsProd is the t=0 slice (so the capstone is undisturbed). Records are now genuinely
-- time-physical ON the model -- the piece L9 needs to list records in "proved on the unified model".
/-- info: 'CSD.SigmaLayer.unified_records_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_records_persistence

/-- info: 'CSD.SigmaLayer.unifiedFlowedSemantics_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedFlowedSemantics_zero

-- SigmaLayer #2 BORN-FREQUENCY ON THE UNIFIED MODEL (2026-07-17, UnifiedFlowedRecords.lean): the review's #2.
-- unified_born_frequency: for i.i.d. trials with the unified model's OWN law (productDynamics.muL), the
-- frequency of trials in π⁻¹(bornRegion i) converges a.s. to ‖⟨eᵢ,ψ⟩‖² -- a direct transfer of
-- manyToOneSetup_born_frequency through productDynamics.muL = liouvilleMeasure (rfl). Born frequencies now
-- stated ON the unified model itself, alongside dynamics/measurement/records/conditioning=Lüders.
/-- info: 'CSD.SigmaLayer.unified_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_born_frequency

-- FiniteQMClosure (#6, 2026-07-17): the tiered capstone. unifiedFiniteQMClosure bundles the eleven
-- GENUINELY-PROVED-on-the-unified-model facts (isolated flow measure-preserving, Schrödinger projection,
-- Fubini-Study bridge/B1, measurement preserving, readout a.e. total/T6, records established/B5, records
-- time-physical/#5, Born frequency/#2, conditioning=Lüders/#3#4) into one record, each field discharged by
-- its source lemma. The Choice-A posit, QM adapters, and open residue are documented in the module header,
-- not encoded as fields -- so no field is sorry and the tiers are honest.
/-- info: 'CSD.SigmaLayer.unifiedFiniteQMClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedFiniteQMClosure

/-- info: 'CSD.SigmaLayer.unifiedDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedDeisolationModel_ae_total

-- SigmaLayer P3 SOLVED via local tomography (2026-07-15): composite_is_tensor_product. The composite observable
-- algebra IS the tensor product of the local ones -- compositeTensorEquiv (= kroneckerLinearEquiv) is a
-- SUFFICIENCY (2026-07-17 downgrade): BIJECTIVE linear iso M_{NA} ⊗ M_{NB} ≃ M_{NA·NB} sending
-- U ⊗ₜ Q ↦ aliceOp U · bobOp Q -- the standard tensor model REALIZES locality (commuting) + local tomography
-- (joint_mem_span_local). This is SUFFICIENCY, not uniqueness; the NECESSITY half (any composite with
-- commuting, generating local algebras IS the tensor product) is TensorReconstruction.lean below.
/-- info: 'CSD.SigmaLayer.composite_is_tensor_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.composite_is_tensor_product

-- SigmaLayer P3 RECONSTRUCTION (2026-07-17, TensorReconstruction.lean): the NECESSITY/uniqueness half.
-- compositeAlgReconstruction: commuting local embeddings M_m, M_n whose images GENERATE 𝒜 give an ALGEBRA
-- EQUIVALENCE M_m ⊗ M_n ≃ₐ 𝒜 (injective since M_m⊗M_n is SIMPLE -- matrixTensor_isSimpleRing; surjective
-- from generation). composite_dim_eq: for 𝒜 = M_k, forces k = m·n -- discharging bridge B6
-- (CompositeSector.tensor_dimension) as a THEOREM. So locality + generation FORCE ⊗, not just admit it.
/-- info: 'CSD.SigmaLayer.compositeAlgReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compositeAlgReconstruction

/-- info: 'CSD.SigmaLayer.composite_dim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.composite_dim_eq

-- SigmaLayer P3 BRIDGE B6 DISCHARGED (2026-07-17): CompositeSector.ofReconstruction builds a CompositeSector
-- whose tensor_dimension (NA*NB=Njoint) FIELD is filled by composite_dim_eq -- derived from commuting,
-- generating local embeddings, not posited. So B6 is no longer a bare assumption.
/-- info: 'CSD.SigmaLayer.CompositeSector.ofReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.CompositeSector.ofReconstruction

/-- info: 'CSD.SigmaLayer.compositeTensorEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compositeTensorEquiv_apply

-- SigmaLayer P3 resolution + localized sector posit (SO-1) (2026-07-15): reducing the two deep posits.
-- P3 (why tensor): single_prod (the joint basis matrix = product of local ones) + joint_mem_span_local
-- (the commuting local subalgebras GENERATE the whole joint algebra) -- the tensor product carries no
-- observables beyond local ones and their products, so B6 reduces from "posit ⊗" to "posit two full
-- local algebras that act and commute". SO-1 (sector origin) LOCALIZED: forcedVolume_unique /
-- region_measure_symmetry_forced (any two U(N)-invariant measures give the same region weights, so the
-- Born weights are symmetry-forced, not measure-chosen); localised_sectorPostulate_capstone (the concrete sector's
-- typicality is forced by the U(N) symmetry the flow is part of -- "the sector posit in the appropriate places (SO-1)").
-- Neither closes the universal posit (P3 "why ⊗" / sector-origin-from-bare-flow (SO-1)); both reduce where it bites.
/-- info: 'CSD.SigmaLayer.single_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.single_prod

/-- info: 'CSD.SigmaLayer.joint_mem_span_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.joint_mem_span_local

/-- info: 'CSD.SigmaLayer.region_measure_symmetry_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.region_measure_symmetry_forced

/-- info: 'CSD.SigmaLayer.localised_sectorPostulate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.localised_sectorPostulate_capstone

-- SigmaLayer SO-1 NO-GO (2026-07-15): the single-flow limit made a PROVED boundary. A projective unitary flow with
-- two distinct fixed rays admits an invariant probability measure /= mu_FS (the two fixed-ray Diracs), so a
-- single deterministic flow does NOT pin the sector's typicality measure -- "the CSD sector is posited (SO-1)" is a theorem
-- about the limit, not a formalisation gap. phaseFlip_admits_invariant_ne_fubiniStudy exhibits it on the
-- concrete nontrivial flow diag(1,-1) on CP^1. Positive companion: region_measure_symmetry_forced (full U(N)
-- symmetry DOES pin mu_FS). Matches Paper C (S1.4): Sigma, pi, the A5 sector are assumed, not derived.
/-- info: 'CSD.SigmaLayer.flow_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flow_admits_invariant_ne_fubiniStudy

/-- info: 'CSD.SigmaLayer.phaseFlip_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.phaseFlip_admits_invariant_ne_fubiniStudy

-- UniqueErgodicity (2026-07-19, SO-1/L7 ergodic face sharpened): UniquelyErgodic defined (absent from
-- Mathlib) + UniquelyErgodic ⇒ Ergodic (via Ergodic.of_mem_extremePoints: singleton invariant-measure
-- set) + the scaffold link Ergodic(Φ_1) ⇒ IsErgodicForOutcomeRegions. Does NOT prove BornFromFlow
-- (needs the Mathlib-absent pointwise Birkhoff theorem); the unitary no-gos above provably exclude the
-- hypothesis for the current flows (candidate must be non-unitary). Boundary-marking, not SO-1 closure.
/-- info: 'CSD.SigmaLayer.UniquelyErgodic.ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.UniquelyErgodic.ergodic

/-- info: 'CSD.SigmaLayer.isErgodicForOutcomeRegions_of_uniquelyErgodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isErgodicForOutcomeRegions_of_uniquelyErgodic

-- SigmaLayer Bell/contextuality generality (2026-07-14): the UNIVERSAL bounds behind the per-instance T13/T14
-- witnesses. lhv_chsh_le_two (every LHV: |S| ≤ 2), qm_chsh_le_tsirelson (every state: |S| ≤ 2√2),
-- cglmp_lhv_le_two (every LHV table, every d: cglmp ≤ 2), bell_general_separation (2 < 2√2, gap attained
-- by the singlet), general_ks_noNonContextualValuation (any parity-(18,9) config, not just Cabello-18).
/-- info: 'CSD.SigmaLayer.lhv_chsh_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lhv_chsh_le_two

/-- info: 'CSD.SigmaLayer.qm_chsh_le_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.qm_chsh_le_tsirelson

/-- info: 'CSD.SigmaLayer.bell_general_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.bell_general_separation

/-- info: 'CSD.SigmaLayer.general_ks_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.general_ks_noNonContextualValuation

-- SigmaLayer T8: the projective (Lüders) update (2026-07-14). luders_capstone bundles the three defining
-- properties of the projective post-measurement update ludersUpdate p x = (‖p x‖)⁻¹ • p x: normalised,
-- repeatable (p fixes it, so re-measurement is certain), and Lüders = conditional probability
-- (ludersUpdate_conditional: the updated Born weight of a finer projection q is projWeight q x /
-- projWeight p x). projWeight_eq_re_inner ties the weight ‖p x‖² to the effect form Re⟨x, p x⟩;
-- isProjection_toEuclideanLin connects matrix projectors. Closes the T8 gap left by MeasurementRecord.
/-- info: 'CSD.SigmaLayer.luders_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.luders_capstone

/-- info: 'CSD.SigmaLayer.ludersUpdate_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ludersUpdate_conditional

/-- info: 'CSD.SigmaLayer.projWeight_eq_re_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.projWeight_eq_re_inner

-- SigmaLayer T7: the general (non-projective) conditional state update (2026-07-14). conditionalUpdate_capstone
-- bundles the general Kraus/effect update stateUpdate M x = (‖M x‖)⁻¹ • M x for a measurement operator M
-- (effect E = M† M): normalised, outcome weight = Re⟨x, M† M x⟩ (updateWeight_eq_re_inner), and the
-- sequential (Wigner) rule stateUpdate_sequential (updateWeight N (stateUpdate M x) = updateWeight N
-- (M x) / updateWeight M x). Lüders (T8) is the sharp special case (stateUpdate_eq_ludersUpdate); T7
-- needs neither self-adjointness nor idempotence.
/-- info: 'CSD.SigmaLayer.conditionalUpdate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditionalUpdate_capstone

/-- info: 'CSD.SigmaLayer.stateUpdate_sequential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.stateUpdate_sequential

/-- info: 'CSD.SigmaLayer.stateUpdate_eq_ludersUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.stateUpdate_eq_ludersUpdate

-- SigmaLayer T9: the mixed-state representation (2026-07-14). Closes the density-matrix gap on the statistical
-- side. mixedState_capstone / traceForm_mix: the convex mixture mix p ρ₁ ρ₂ is a density operator and
-- the Born rule traceForm is affine in the state (Tr((p ρ₁ + (1-p) ρ₂) E) = p Tr(ρ₁ E) + (1-p) Tr(ρ₂ E)).
-- rankOneDensity_isPure: pure states are the rank-one projectors; maximallyMixed_not_isPure: I/N is a
-- genuinely mixed state for N ≥ 2 (non-vacuity). Built on LF2.DensityOperator/Effect/traceForm; the
-- purity converse Tr(ρ²)=1 → ρ²=ρ (spectral theorem) is left as a residue.
/-- info: 'CSD.SigmaLayer.mixedState_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixedState_capstone

/-- info: 'CSD.SigmaLayer.traceForm_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.traceForm_mix

/-- info: 'CSD.SigmaLayer.maximallyMixed_not_isPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.maximallyMixed_not_isPure

-- T9 purity converse (2026-07-14): the spectral-theorem direction, closing the residue. IsPure ρ ↔
-- Tr(ρ²)=1 (isPure_iff_trace_sq_one); the converse isPure_of_trace_sq_one uses Matrix spectral theory
-- (∑λᵢ = ∑λᵢ² = 1, λᵢ ≥ 0 ⇒ λᵢ ∈ {0,1} ⇒ ρ² = ρ). Foundational triple.
/-- info: 'CSD.SigmaLayer.isPure_of_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isPure_of_trace_sq_one

/-- info: 'CSD.SigmaLayer.isPure_iff_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isPure_iff_trace_sq_one

-- MixedEnsemble (#8 A+B, 2026-07-17): the mixed-state / ensemble representation. A -- finite ensembles:
-- ensemble w ρ = ∑ᵢ wᵢρᵢ (∑wᵢ=1, wᵢ≥0) is a density operator via posSemidef_sum; traceForm_ensemble is
-- the affine Born rule over the whole ensemble, Tr((∑wᵢρᵢ)E) = ∑wᵢTr(ρᵢE) (the many-component
-- traceForm_mix). B -- spectral ensemble decomposition: density_eq_eigen_ensemble (ρ = ∑λᵢ|eᵢ⟩⟨eᵢ| via
-- the Hermitian spectral theorem), eigenvalues_isProbability (λ a probability distribution),
-- density_isPureEnsemble (every density operator IS a convex ensemble of pure states), and
-- traceForm_eq_pureEnsemble / mixedEnsemble_capstone (the Born rule of a mixed state is the
-- eigenvalue-weighted average of the pure Born rules).
/-- info: 'CSD.SigmaLayer.ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ensemble

/-- info: 'CSD.SigmaLayer.traceForm_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.traceForm_ensemble

/-- info: 'CSD.SigmaLayer.density_eq_eigen_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.density_eq_eigen_ensemble

/-- info: 'CSD.SigmaLayer.density_isPureEnsemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.density_isPureEnsemble

/-- info: 'CSD.SigmaLayer.mixedEnsemble_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixedEnsemble_capstone

-- MixedOntic (#8 C, 2026-07-17): the ontic-side mixed-state representation on the unified model.
-- mixed_ontic_born_weight: for any density operator ρ and pointer outcome i, the classical mixture over
-- ρ's spectral ensemble (λⱼ,eⱼ) of the ontic Born-region measures ∑ⱼ λⱼ·μL(π⁻¹ bornRegion(eⱼ) i) equals
-- Tr(ρ Eᵢ) = traceForm ρ (rankOneEffect eᵢ) -- composing onticRegion_measure_eq_born with
-- traceForm_eq_pureEnsemble + born_quadratic. So productDynamics represents mixed states, not only pure ψ;
-- wired as the FiniteQMClosure.mixed_born field. Weight-level (the mixed frequency LLN is the refinement).
/-- info: 'CSD.SigmaLayer.mixed_ontic_born_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixed_ontic_born_weight

-- MixedFrequency (#8 C, a.s. limit, 2026-07-19, roadmap A1): the mixed Born WEIGHT upgraded to a
-- FREQUENCY LLN. unified_mixed_born_frequency: for i.i.d. two-stage trials Y whose law is mixtureMeasure
-- (eigenvalue distribution ⊗ μL), the frequency in mixtureRegion i (component j's eigenvector lands in the
-- i-th ontic Born region) converges a.s. to Tr(ρ Eᵢ). Proof: mixtureMeasure_region_toReal shows the
-- two-stage region measure = Tr(ρ Eᵢ) (via Measure.prod_prod + eigenvalueMeasure_singleton +
-- mixed_ontic_born_weight), then born_frequency_convergence_partition. Wired as FiniteQMClosure's 11th
-- field mixed_born_frequency, closing the closure's last open QM item (Tier-4 mixed frequency LLN).
/-- info: 'CSD.SigmaLayer.unified_mixed_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_mixed_born_frequency

/-- info: 'CSD.SigmaLayer.mixtureMeasure_region_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixtureMeasure_region_toReal

-- Symmetrization (identical particles / exchange statistics, n=2, 2026-07-18): the swap operator on
-- H⊗H = EuclideanSpace ℂ (Fin N × Fin N) is a self-adjoint involution (swap_isSymmetric); symProj/
-- antisymProj = ½(1±swap) are complementary orthogonal projections (symProj_idem, symProj_antisymProj,
-- symProj_add_antisymProj); the exchange dichotomy Sym=(+1)/Anti=(-1) eigenspaces (swap_eq_self_iff,
-- swap_eq_neg_iff, eq_zero_of_swap_self_and_neg → H⊗H = Sym⊕Anti); and Pauli exclusion
-- antisymProj_tprod_self (antisymProj (v⊗v) = 0: no two fermions in the same state).
/-- info: 'CSD.SigmaLayer.swap_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_isSymmetric

/-- info: 'CSD.SigmaLayer.symProj_add_antisymProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.symProj_add_antisymProj

/-- info: 'CSD.SigmaLayer.swap_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_eq_self_iff

/-- info: 'CSD.SigmaLayer.swap_eq_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_eq_neg_iff

/-- info: 'CSD.SigmaLayer.antisymProj_tprod_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.antisymProj_tprod_self

-- OnticBornFrequency (connectivity G1, 2026-07-25): Born grounded in the ONTIC typicality. The only
-- hypothesis is ontic (trials sample μ_L = D.muL, the floor); the epistemic μ_FS and Born are DERIVED.
-- onticBornVolume_eq: Born = the ontic typicality volume — μ_L(π⁻¹ bornRegion) = ‖⟨eᵢ,ψ⟩‖² via the
-- pushforward bridge (HasFubiniStudyPushforward) + bornRegion_fs_measure_uncond, for ANY sector.
-- born_frequency_from_ontic_sampling: iid ontic-μ_L trials → Born frequency (freq_tendsto_of_iid).
-- productModel_onticBornVolume: non-vacuity — hpush discharged by the proved productSector pushforward.
/-- info: 'CSD.SigmaLayer.onticBornVolume_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticBornVolume_eq

/-- info: 'CSD.SigmaLayer.born_frequency_from_ontic_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.born_frequency_from_ontic_sampling

/-- info: 'CSD.SigmaLayer.productModel_onticBornVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productModel_onticBornVolume

-- BornFibrePartition (record layer / MD-1, 2026-07-25): the fibre-partition factor of measurement.
-- The fibre F=ℝ is carved into cumulative (CDF) cells cdfCell whose Lebesgue measure equals a given
-- rate rᵢ (volume_cdfCell); the cells are pairwise disjoint (cdfCell_pairwiseDisjoint) so the fibre
-- is genuinely partitioned. Fed the Born rates rᵢ=‖ψ i‖²=|⟨eᵢ,ψ⟩|² (bornRate) the fibre measure of
-- outcome i is the Born weight (volume_bornCell), and for a unit state the cells cover a set of
-- measure exactly 1 (volume_iUnion_bornCell_unit) — the record-layer measure content. The open piece
-- is the dynamical realisation (a de-isolation flow with moment-map target-measures), not this.
/-- info: 'CSD.RecordLayer.volume_cdfCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_cdfCell

/-- info: 'CSD.RecordLayer.cdfCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cdfCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_bornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_bornCell

/-- info: 'CSD.RecordLayer.volume_iUnion_bornCell_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_iUnion_bornCell_unit

-- DeIsolationFlow (record layer / MD-1 step 2b′, 2026-07-25): the de-isolation outcome DISTRIBUTION.
-- On the canonical fibre typicality measure fibreTypicality = vol|[0,1) (a probability measure), the
-- Born cell i has fibre typicality exactly ‖ψ i‖² (fibreTypicality_bornCell = the outcome
-- probability), the cells cover the fibre up to a null set (fibreTypicality_uncovered = pointer a.e.
-- defined), and the abstract bridge map_pointer_apply shows ANY measurable pointer whose basins carry
-- the Born cell measures pushes fibreTypicality forward to the Born distribution. The open piece is
-- exhibiting such a pointer from a physical de-isolation Hamiltonian H_int(M) — the bridge's hbasin
-- hypothesis IS that obligation, not this theorem.
/-- info: 'CSD.RecordLayer.fibreTypicality_bornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_bornCell

/-- info: 'CSD.RecordLayer.fibreTypicality_uncovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_uncovered

/-- info: 'CSD.RecordLayer.map_pointer_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.map_pointer_apply

-- Added 2026-08-11 by the prose audit. Five record-layer modules explained the Ico 0 1 in
-- fibreTypicality_uncovered by saying "Lebesgue measure on the line is infinite". That reason was
-- wrong twice over: fibreTypicality is vol|[0,1), a PROBABILITY measure (instIsProbabilityMeasure),
-- and the restriction was never forced. These two theorems settle it rather than asserting it.
-- fibreTypicality_uncovered_univ gives the univ form on R outright; fibreTypicality_Ici_one states
-- what compactness actually buys, by making the fiat explicit -- the fibre's complement carries
-- infinite Lebesgue measure and zero typicality, so a point there is excused by the measure rather
-- than covered by a cell. On CircleFibre/TorusFibre the mass one is Haar mass instead.

/-- info: 'CSD.RecordLayer.fibreTypicality_uncovered_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_uncovered_univ

/-- info: 'CSD.RecordLayer.fibreTypicality_Ici_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_Ici_one

-- FibreRecord (record layer / MD-1 step 3, 2026-07-25): the record-layer readout as a first-class
-- postulate-P5 RecordSemantics on Σ=ℝ. fibreRecordSemantics: record event of "context c recorded
-- outcome i" = cdfCell c.rate i, measurable + exclusive (distinct outcomes disjoint, from
-- cdfCell_pairwiseDisjoint). fibreOutcome_eq_record: the ontic selection fibreOutcome IS the record
-- (some i ↔ ξ in event). compatibleSet_fibre_single: isolation on one record = conditioning on the
-- cell. fibreTypicality_bornRecord: the ontic typicality of recording outcome i is exactly ‖ψ i‖²
-- (Born meets the record). The intended replacement for the prep-indexed LF5 vnPointerOutcome readout.
/-- info: 'CSD.RecordLayer.fibreRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreRecordSemantics

/-- info: 'CSD.RecordLayer.fibreOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreOutcome_eq_record

/-- info: 'CSD.RecordLayer.fibreTypicality_bornRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_bornRecord

-- RecordLayerClosure (record layer / MD-1 step 5, 2026-07-25): the record-layer capstone bundle, the
-- analog of FiniteQMClosure. recordLayerClosure discharges, for every unit ψ: exclusive (P5), the
-- ontic selection IS the record, isolation = conditioning on the cell (P6), born_typicality (fibre
-- typicality of the record event = ‖ψ i‖²), and ae_total (events cover the fibre up to null). The
-- certified successor to the prep-indexed vnPointerOutcome readout — outcome probabilities are
-- measurement-noncontextual. Migrating FiniteQMClosure's proved fields onto it stays open (MD-1).
/-- info: 'CSD.RecordLayer.recordLayerClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordLayerClosure

-- MomentMapRace (record layer / MD-1 step 2b′, 2026-07-25): grounds the fibre-partition rates in the
-- Kähler geometry (feature 2 of §3c). bornRate_eq_momentMap: for a unit ψ the rate ‖ψ i‖² IS the
-- i-th Fubini-Study torus moment-map coordinate at [ψ] (corpus LF4/MomentMap.momentMap) — forced by
-- the Kähler structure, not injected. bornRate_eq_inner_sq: hence = the corpus Born weight ‖⟨eᵢ,ψ⟩‖²
-- (FiniteQMClosure.born_frequency target). DeIsolationInteraction: the kinematic interface (pointer
-- with moment-map basins) ⟹ Born (.born). Open: realising the interface from a Hamiltonian H_int(M).
/-- info: 'CSD.RecordLayer.bornRate_eq_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRate_eq_momentMap

/-- info: 'CSD.RecordLayer.bornRate_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRate_eq_inner_sq

/-- info: 'CSD.RecordLayer.DeIsolationInteraction.born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.DeIsolationInteraction.born

-- Q12-a (2026-08-23): a WITNESS for that interface.  Until this was built DeIsolationInteraction had
-- NO instance anywhere in the corpus -- an interface whose satisfiability was never exhibited, the
-- same defect E5 closed for E4.  cdfDeIsolationInteraction assembles the already-landed pieces:
-- the CDF pointer (fibreOutcome, made total by sending the leftover to a default outcome), its
-- basins are the Born cells (fibreTypicality_bornCell), and the leftover is null
-- (fibreTypicality_compl_iUnion_bornCell, from fibreTypicality_iUnion_bornCell = 1).
-- ⚠️ WITNESSES SATISFIABILITY ONLY.  CDF stacking imposes an arbitrary outcome ORDER, whereas the
-- mechanism record-layer-plan.md §3b asks for is order-free; and NO DYNAMICS carves these cells --
-- they are defined, not flowed to.  Deriving them from a de-isolation flow is Q12-d, which
-- specs/q12-fibre-mechanism-scoping.md records as BLOCKED: the mixing hypothesis it needs is
-- unsatisfiable by any flow the corpus defines (E6).  Reading this pin as "the dynamical problem is
-- solved" is exactly the inference MomentMapRace's 2026-07-30 correction note exists to block.
/-- info: 'CSD.RecordLayer.cdfDeIsolationInteraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cdfDeIsolationInteraction

-- Q12-b' (2026-08-23): the interface was GENERALISED to an arbitrary fibre (F, nu) -- it had been
-- hard-wired to pointer : R -> Fin n.  That mismatch was the finding of Q12-b: the order-free race
-- lives on Fin (n+1) -> R, and record-layer-plan.md §3b says the minimal fibre dimension is n-1, so
-- the old interface was committed to the ORDERED construction.  With the generalisation the race
-- instantiates it, giving a SECOND and symmetric witness.
-- The shared machinery is Mathlib/MeasureTheory/CellPointer.lean (extracted at the second consumer,
-- CONVENTIONS §9 rule of two): cellPointer makes a disjoint measurable cell family into a TOTAL
-- readout by sending the leftover to a default index, and measure_cellPointer_preimage shows the
-- leftover is null whenever the cell weights already exhaust the probability.
-- ⚠️ NEITHER witness is the dynamical result: the CDF cells are stacked in index order, the race
-- cells are symmetric but their clock law is POSITED, and NO FLOW carves either family (Q12-d,
-- blocked -- see specs/q12-fibre-mechanism-scoping.md).
/-- info: 'MeasureTheory.measure_cellPointer_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MeasureTheory.measure_cellPointer_preimage

/-- info: 'CSD.RecordLayer.raceDeIsolationInteraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.raceDeIsolationInteraction

-- Q12 successor question, executed in its honest form (ShearDeIsolation, 2026-08-27): the THIRD
-- DeIsolationInteraction witness, and the first whose pointer is the readout of the CONSTRUCTED
-- de-isolation propagator rather than a defined cell family.  The pointer is cellPointer over the
-- flow-carved outcome sectors Omega_i = Phi_{0->1}^{-1}(B_i) of the shear protocol driven by the
-- context-fixed momentContext basins; cellPointer_outcomeSector_eq_readout certifies it equals
-- (readout . flow).getD i0 POINTWISE -- the p = readout . flow(H_int(M)) shape of step 2b' as a
-- theorem, not a reading.  basin_rate is DISCHARGED from shear_sector_born (the bankless mirror of
-- swap_sector_born: readyPrep [psi] (Omega_i) = the moment-map weight, via
-- measure_outcomeSector_eq_of_correlates, so the discharged correlation theorem is consumed).
-- The psi-dependence lives ONLY in the ontic preparation measure readyPrep [psi]; readout arcs,
-- basins and propagator are context-fixed.  ⚠️ CARRIED, NOT LAUNDERED: the propagator's Hamiltonian
-- generation is stated, not formalised (ShearWitness item 1 -- no manifold symplectic API, the
-- permanently-scoped row), and the coupling is engineered (witness, not derivation).  Read these
-- pins as "basin_rate discharged from the constructed de-isolation propagator", never as a
-- formalised H_int.
/-- info: 'CSD.RecordLayer.readyPrep_selReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readyPrep_selReady

/-- info: 'CSD.RecordLayer.shear_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shear_sector_born

/-- info: 'CSD.RecordLayer.cellPointer_outcomeSector_eq_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cellPointer_outcomeSector_eq_readout

/-- info: 'CSD.RecordLayer.shearDeIsolationInteraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shearDeIsolationInteraction

/-- info: 'CSD.RecordLayer.shearDeIsolationInteraction_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shearDeIsolationInteraction_pointer

/-- info: 'CSD.RecordLayer.shearDeIsolation_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shearDeIsolation_born

-- Externality, the before/after pair (ShearWitness, 2026-08-27; the record-network programme's
-- necessary condition, first brick).  outcome_system_dependent_before (A1, the CONTENTFUL half):
-- before the stroke a system-only transformation moving the selector across basins changes which
-- outcome gets recorded -- the outcome information is still in the system, and the stroke is what
-- exports it to the register.  readout_system_invariant (A2): the displayed record is invariant
-- under EVERY system-side map -- ⚠️ VACUOUS BY ARCHITECTURE (the readout reads the register
-- factor only; the proof is rfl), pinned so it is documented rather than re-landed as content.
-- Both joined DynamicMeasurementClosure as fields the same day (A3).
/-- info: 'CSD.RecordLayer.outcome_system_dependent_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.outcome_system_dependent_before

/-- info: 'CSD.RecordLayer.readout_system_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readout_system_invariant

-- Measurement (record layer / MD-1, 2026-07-25): the architecture in one object — context (measurement
-- type, fixes the basins/probabilities) + unknown microstate ξ → outcome (the basin it occupies) →
-- record. outcome_eq_some_iff (microstate selects its basin), record_of_mem_basin (combined result IS
-- the record ⟨context,outcome,time⟩), bornMeasurement_prob (basins set the probabilities = ‖ψ i‖²),
-- bornMeasurement_prob_momentMap (= the Kähler moment map, forced not injected), bornMeasurement_ae_total
-- (a.e. microstate yields a record). Assembles the proven pieces; the physical flow H_int(M) stays open.
/-- info: 'CSD.RecordLayer.Measurement.record_of_mem_basin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.record_of_mem_basin

/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_prob

/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_prob_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_prob_momentMap

-- The Born rule as LLN over the unknown microstate (2026-07-25): the whole probabilistic content is
-- the strong law — i.i.d. typical microstates (law fibreTypicality) give outcome-i frequency → the
-- basin measure ‖ψ i‖² = the moment map. Randomness = ignorance of the initial condition; no extra
-- dynamical postulate (the "de-isolation flow" is just the deterministic microstate→basin map).
/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_frequency

-- ProjectiveRecord (record layer migration onto the actual Σ, 2026-07-25): the record layer instantiated
-- on the corpus's REAL model — Σ = CPN(M+1), events = the corpus's own bornRegion, outcome map =
-- bornOutcome, measure = fubiniStudyMeasure. projRecordSemantics (P5 RecordSemantics on CPN, measurable
-- + exclusive from bornRegion_measurable_uncond/bornRegion_pairwiseDisjoint); bornOutcome_eq_record (the
-- corpus outcome map IS the record); fubiniStudy_projRecord (FS typicality of the record event = ‖⟨eᵢ,ψ⟩‖²);
-- projRecord_frequency (Born = LLN over the unknown microstate on the real Σ = FiniteQMClosure.born_frequency
-- conclusion, carried by the record-layer RecordSemantics). Not a parallel toy — the real Born machinery.
/-- info: 'CSD.RecordLayer.projRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projRecordSemantics

/-- info: 'CSD.RecordLayer.bornOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornOutcome_eq_record

/-- info: 'CSD.RecordLayer.fubiniStudy_projRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fubiniStudy_projRecord

/-- info: 'CSD.RecordLayer.projRecord_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projRecord_frequency

-- FibredSigma (record layer / MD-1, 2026-07-25): the ontic space assembled as Σ = base × fibre =
-- CPN n × ℝ — the base the EPISTEMIC projective point (pinned to [ψ] for a sharp prep,
-- baseProj_sharpTypicality), the fibre the ONTIC record coordinate (carves the Born partition). The
-- sharp typicality δ_[ψ] ⊗ fibreTypicality gives Born as the fibre event's typicality
-- (sharpTypicality_fibredEvent = ‖ψ i‖² = the moment map). The epistemic(base)/ontic(fibre) split of
-- Papers C/D made literal — ties FibreRecord to the projective base.
/-- info: 'CSD.RecordLayer.baseProj_sharpTypicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.baseProj_sharpTypicality

/-- info: 'CSD.RecordLayer.sharpTypicality_fibredEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sharpTypicality_fibredEvent

/-- info: 'CSD.RecordLayer.sharpTypicality_fibredEvent_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sharpTypicality_fibredEvent_momentMap

-- BasisMeasurement (record layer, arbitrary observable, 2026-07-25): the record layer for a general
-- orthonormal basis b (any observable). bornRateBasis_eq_inner_sq (outcome prob = ‖⟨bᵢ,ψ⟩‖²),
-- sum_bornRateBasis_unit (probability vector), bornMeasurementBasis_prob (the general measurement's
-- outcome-i probability = ‖⟨bᵢ,ψ⟩‖²). Change of basis via the isometry b.repr.
/-- info: 'CSD.RecordLayer.bornMeasurementBasis_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornMeasurementBasis_prob

/-- info: 'CSD.RecordLayer.bornRateBasis_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRateBasis_eq_inner_sq

-- KSigmaRecord (record layer on the closure's actual product Σ, 2026-07-25): the record layer on
-- Σ = KSigma(M+1) = CPN × T² (the FiniteQMClosure space). kSigmaRecordSemantics (P5 RecordSemantics,
-- events = bornRegion lifted through π = Prod.fst); born_frequency_region_eq_record (the region
-- FiniteQMClosure.born_frequency lands in, π⁻¹'bornRegion, is DEFINITIONALLY the record event — the
-- record layer is wired to the closure's actual field, field rewrite unnecessary); bornOutcome_base_eq_record.
/-- info: 'CSD.RecordLayer.kSigmaRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.kSigmaRecordSemantics

/-- info: 'CSD.RecordLayer.born_frequency_region_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.born_frequency_region_eq_record

-- PointerArena (2026-08-03, SigmaLayer/PointerArena.lean; pointer-witness-plan.md brick 0 — the
-- smooth-Hamiltonian route's kinematic floor, architecture confirmed 2026-08-03). The compact
-- Kähler pointer ℂℙ^K replacing the torus register (the flux correction's repair): open,
-- disjoint, positive-FS-measure ready/record regions via the pointer moment map, and the arena
-- KSigma N × ℂℙ^K with pointerLiouville = kMuL ⊗ μ_FS^ptr. Key structural fact: arenaReady_pos —
-- a positive-measure apparatus-ready state EXISTS on this arena (contrast globalBasin_ae_total,
-- where a.e. every point already carries a record). Kinematics only; the propagator is bricks 1–4.
/-- info: 'CSD.RecordLayer.recordRegion_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.readyRegion_disjoint_recordRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readyRegion_disjoint_recordRegion

/-- info: 'CSD.RecordLayer.recordRegion_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pos

/-- info: 'CSD.RecordLayer.readyRegion_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readyRegion_pos

/-- info: 'CSD.RecordLayer.arenaReady_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.arenaReady_pos

-- PointerRotation (2026-08-03, SigmaLayer/PointerRotation.lean; pointer-witness-plan.md brick 1).
-- The fixed-outcome pointer rotation: Hermitian generator h_j = |f0><f_{j+1}| + |f_{j+1}><f0|
-- (pointerH_isHermitian), whose rotation family pointerRot θ j = 1 + (cosθ−1)•P_j − (i sinθ)•h_j
-- is a CONTINUOUS ONE-PARAMETER UNITARY GROUP: group law (pointerRotU_add), unitarity via
-- rotᴴ = rot(−θ), continuity (continuous_pointerRotU) — the properties shearEvolve provably
-- lacks (shearEvolve_not_continuous). Quarter turn transports ready → record projectively
-- (pointerRotU_pi_div_two_ready); FS measure preservation is unitary invariance
-- (pointerRotU_measurePreserving). Honest scope: the exp(−iθh_j) identification is brick 5.
/-- info: 'CSD.RecordLayer.pointerH_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerH_isHermitian

/-- info: 'CSD.RecordLayer.pointerRot_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRot_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.pointerRotU_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_add

/-- info: 'CSD.RecordLayer.continuous_pointerRotU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerRotU

/-- info: 'CSD.RecordLayer.pointerRotU_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_measurePreserving

/-- info: 'CSD.RecordLayer.pointerRotU_pi_div_two_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_pi_div_two_ready

-- PointerCoupling (2026-08-03, SigmaLayer/PointerCoupling.lean; pointer-witness-plan.md brick 2a,
-- generator half). The selector-modulated coupling: couplingH w = Σⱼ wⱼ•hⱼ Hermitian for every
-- real weight vector; couplingU w = exp((π/2)•(−i•couplingH w)) UNITARY (skew-Hermitian
-- exponential; the hⱼ do NOT commute — genuine exp, no closed form). ★ pointerRot_eq_exp: the
-- HAMILTONIAN-GENERATION IDENTIFICATION — brick 1's closed form IS exp(θ•(−i•hⱼ)), by ODE
-- uniqueness (eq_exp_of_hasDeriv); brick 5's single-plane half, pulled forward because the
-- landing theorem reads pure cells through couplingU_single = pointerRot (π/2) j. Entrywise
-- Lipschitz continuity in the weights (continuous_couplingU_entry) via the Duhamel bound + the
-- NEW staged entry bound Matrix.norm_entry_le_l2_opNorm (L2OpNormEntry.lean) — stated in the
-- plain Pi topology, no scoped norm instances in the statement.
/-- info: 'CSD.RecordLayer.couplingH_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingH_isHermitian

/-- info: 'CSD.RecordLayer.couplingU_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingU_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.pointerRot_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRot_eq_exp

/-- info: 'CSD.RecordLayer.couplingU_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingU_single

/-- info: 'CSD.RecordLayer.continuous_couplingU_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_couplingU_entry

-- PointerWeights (2026-08-03, SigmaLayer/PointerWeights.lean; pointer-witness-plan.md brick 2b).
-- The selector-modulated weight field and the arena propagator. Weights are CIRCLE-INTRINSIC
-- trapezoids clamp((r_j/2 − dist(θ₁, cellMid_j))/ε) with rates read at the base point
-- (ContextField, no preparation) — so joint continuity is a composition, no lift, no seam.
-- ★ continuous_pointerEvolve: THE FULL ARENA PROPAGATOR IS CONTINUOUS — the theorem
-- shearEvolve_not_continuous proves no torus-register witness can have; proof descends through
-- the open quotient id × mk' (IsOpenQuotientMap.prodMap) to entrywise-continuous matrix data.
-- pointerEvolve_measurePreserving: Liouville preservation as a skew product (sector conserved,
-- FS-preserving unitary on each pointer slice). pointerEvolve_pure: on shrunk cells the
-- propagator IS the brick-1 quarter rotation (weights collapse to Pi.single) — the landing seed;
-- the cell-geometry distance facts are brick 3's obligation.
/-- info: 'CSD.RecordLayer.continuous_pointerWeights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerWeights

/-- info: 'CSD.RecordLayer.pointerWeights_eq_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerWeights_eq_single

/-- info: 'CSD.RecordLayer.continuous_pointerEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerEvolve

/-- info: 'CSD.RecordLayer.pointerEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.pointerEvolve_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_pure

-- PointerLanding (2026-08-03, SigmaLayer/PointerLanding.lean; pointer-witness-plan.md brick 3).
-- The landing geometry. cellMid_dist_ge: distinct CDF-cell midpoints are ≥ (r_j+r_k)/2 apart on
-- the circle (UnitAddCircle.norm_eq + round case analysis + the loSum interval ordering);
-- shrunk_dist_other: triangle inequality discharges pointerEvolve_pure's second hypothesis — no
-- per-cell inclusion geometry needed. momentMap_pointerRot_smul: m_{j+1}(U_j(π/2)•q) = m_0(q)
-- EXACTLY, so the open ready region maps into the open record region with margin (δ ≤ 1/2).
-- ★ pointer_landing: sector in the shrunk cell of j + pointer ready ⇒ the CONTINUOUS
-- Liouville-preserving propagator lands in arenaRecord j — record creation with the ontic sector
-- selecting the outcome. volume_shrunkCell_slice: the shrunk slice carries selector volume
-- exactly r_j − 2ε (AddCircle.volume_closedBall) — the ε-Born seed; the 2ε deficit is the
-- no_everywhere_correlation corridor, priced, never hidden.
/-- info: 'CSD.RecordLayer.cellMid_dist_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cellMid_dist_ge

/-- info: 'CSD.RecordLayer.shrunk_dist_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shrunk_dist_other

/-- info: 'CSD.RecordLayer.momentMap_pointerRot_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.momentMap_pointerRot_smul

/-- info: 'CSD.RecordLayer.pointer_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_landing

/-- info: 'CSD.RecordLayer.measurableSet_shrunkCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.measurableSet_shrunkCell

/-- info: 'CSD.RecordLayer.volume_shrunkCell_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_shrunkCell_slice

-- PointerProtocol (2026-08-03, SigmaLayer/PointerProtocol.lean; pointer-witness-plan.md brick 4a).
-- The smooth witness in the standard record architecture: MeasurementProtocol on the pointer
-- arena with evolve = ramped exponential of the selector-modulated coupling. The two-time law is
-- THE GROUP PROPERTY of the exponential (couplingUAt_mul, exp_add_of_commute) — vs the swap's
-- eight-case crossing proof; persistence is FREEZING (ramp constant after readout ⇒ identity ⇒
-- PointerInvariantOn discharged outright); the correlation obligation is the landing theorem
-- (pointerProtocol_correlatesOn, sectors = shrunk cell × ready). ★ Joint time–state continuity
-- (continuous_pointerRampedEvolve, definitionally the protocol propagator): the two-sided
-- Duhamel estimates (weights + angle: norm_couplingUAt_sub_time swaps the roles of time and
-- generator) squeeze each entry (continuous_couplingUAt_entry_joint); the projective action by
-- the generic open-quotient descent continuous_unitaryFamily_smul.
/-- info: 'CSD.RecordLayer.couplingUAt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingUAt_mul

/-- info: 'CSD.RecordLayer.norm_couplingUAt_sub_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.norm_couplingUAt_sub_time

/-- info: 'CSD.RecordLayer.continuous_couplingUAt_entry_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_couplingUAt_entry_joint

/-- info: 'CSD.RecordLayer.continuous_unitaryFamily_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_unitaryFamily_smul

/-- info: 'CSD.RecordLayer.continuous_pointerRampedEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerRampedEvolve

/-- info: 'CSD.RecordLayer.pointerProtocol_correlatesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerProtocol_correlatesOn

/-- info: 'CSD.RecordLayer.pointerProtocol_pointerInvariantOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerProtocol_pointerInvariantOn

-- PointerBorn (2026-08-03, SigmaLayer/PointerBorn.lean; pointer-witness-plan.md brick 4b —
-- closes brick 4). The ε-Born sandwich for the ready-CONDITIONED preparation
-- pointerPrep = epistemicMeasure ⊗ FS[|ready] (legitimate: readyRegion_pos — NO Dirac
-- calibration posit, unlike the swap): pointerPrep_sector_measure = r_j − 2ε EXACTLY (the
-- brick-3 slice volume through the globalBasin_prob dirac-slice pattern);
-- ★ pointer_born_lower (containment) and ★ pointer_born_upper — the upper bound needs NO cell
-- geometry: disjoint sectors + the other N−1 lower bounds crowd out everything above
-- r_j + 2(N−1)ε in a probability space. ★★ smoothWitnessClosure: ONE witness carrying protocol
-- + joint time–state continuity + Liouville preservation + positive-measure ready state +
-- record creation (sector-selected) + structural persistence + ε-Born; instantiated on the
-- canonical moment-map context (smoothWitnessClosureCanonical). The smooth horn of the
-- no_everywhere_correlation trade-off — complementing, never displacing, the exact-record
-- piecewise closures.
/-- info: 'CSD.RecordLayer.pointerPrep_sector_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerPrep_sector_measure

/-- info: 'CSD.RecordLayer.pointer_born_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_lower

/-- info: 'CSD.RecordLayer.pointer_born_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_upper

/-- info: 'CSD.RecordLayer.smoothWitnessClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothWitnessClosure

/-- info: 'CSD.RecordLayer.smoothWitnessClosureCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothWitnessClosureCanonical

-- PointerGeneration (2026-08-03, SigmaLayer/PointerGeneration.lean; pointer-witness-plan.md
-- brick 5 -- COMPLETES THE LADDER). * rampedU_schrodinger: on the interaction window the ramped
-- propagator satisfies the SCHRODINGER EQUATION U' = U*(-i*H_eff) with the explicit HERMITIAN
-- generator H_eff = (pi/2) * couplingH w (pointerHeff_isHermitian) -- the Hamiltonian-generation
-- statement at the formalisable level, with no flux obstruction (projective pointer, H^1 = 0);
-- the symplectic/moment-map reading stays the A1/A3-scoped prose boundary (MATHLIB-GAPS).
-- pointerEvolve_base_marginal_unchanged: the stroke leaves every sector marginal untouched --
-- records WITHOUT back-reaction, the smooth counterpart of shear_base_marginal_unchanged;
-- collapse stays on the swap/join witnesses, composition = the recorded M-L extension.
/-- info: 'CSD.RecordLayer.pointerHeff_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerHeff_isHermitian

/-- info: 'CSD.RecordLayer.rampedU_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.rampedU_schrodinger

/-- info: 'CSD.RecordLayer.pointerEvolve_base_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_base_marginal_unchanged

-- LocalLuders (2026-08-03, SigmaLayer/LocalLuders.lean; dynamical no-signalling brick 1).
-- A local B-measurement on the composite acts by the coordinate-form local projectors
-- P_j = 1_A (x) |f_j><f_j| (localProjB): idempotent, identity-resolving (sum_localProjB),
-- norm-resolving Born weights (sum_normSq_localProjB). ★★ reduceA_localLuders_mixture — THE
-- STATICS CORE OF DYNAMICAL NO-SIGNALLING: the Born-weighted mixture of post-measurement
-- A-marginals equals the pre-measurement A-marginal (zero-weight branches carry weight 0, no
-- positivity smuggled). Unnormalised core traceRight_sum_vecOuter_localProjB: tracing out B
-- collapses the Lüders sum entrywise. Brick 2 = wire to BlockLudersObligation through the
-- Fin (nA·nB) index bridge; brick 3 = the eraser process (mark then erase, sequential).
/-- info: 'CSD.RecordLayer.sum_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_localProjB

/-- info: 'CSD.RecordLayer.sum_normSq_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_normSq_localProjB

/-- info: 'CSD.RecordLayer.traceRight_sum_vecOuter_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.traceRight_sum_vecOuter_localProjB

/-- info: 'CSD.RecordLayer.reduceA_localLuders_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_localLuders_mixture

-- LocalBlockBridge (2026-08-03, SigmaLayer/LocalBlockBridge.lean; dynamical no-signalling
-- brick 2). Under finProdFinEquiv, the block structure of a local B-measurement is the second
-- projection (localBlock) and ★ the degenerate-Lüders block projector IS the local projector
-- (toComposite_blockProj — a definitional identity, not an analogy), with isometric transport
-- so block Born weights = local Born weights. ★★ reduceA_blockLuders_mixture — DYNAMICAL
-- NO-SIGNALLING in the dynamics' own vocabulary: the Born-weighted mixture of A-marginals of
-- the post-states the JOIN WITNESS delivers (BlockLudersObligation localBlock, inhabited by
-- joinWitness_blockLuders; weights per degenerate_selector_born) equals the A-marginal of the
-- preparation. Brick 3 (remaining): the measure-level ensemble integral + the eraser process.
/-- info: 'CSD.RecordLayer.toComposite_blockProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.toComposite_blockProj

/-- info: 'CSD.RecordLayer.norm_blockProj_localBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.norm_blockProj_localBlock

/-- info: 'CSD.RecordLayer.reduceA_blockLuders_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_blockLuders_mixture

-- LocalLudersBasis (2026-08-03, SigmaLayer/LocalLudersBasis.lean; dynamical no-signalling
-- brick 3a). The local Lüders map for an ARBITRARY orthonormal basis on the measured factor:
-- localProjOn g j = 1_A (x) |g_j><g_j| in coordinate form; the computational case recovers
-- localProjB exactly (localProjOn_basisFun). Identity resolution by basis expansion
-- (sum_localProjOn), Born weights resolve the norm by Parseval per slice
-- (sum_normSq_localProjOn), and ★★ reduceA_localLudersOn_mixture — MARGINAL INVARIANCE IN
-- EVERY BASIS: Alice cannot detect Bob's outcome OR his basis choice; Parseval
-- (sum_inner_mul_inner) does the work the ite-collapse did in brick 1. Brick 3b: the 2⊗2
-- eraser instantiation (computational mark = which-path/no fringe; ± erase = eraserOut
-- fringes + the exact dark zero).
/-- info: 'CSD.RecordLayer.localProjOn_basisFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.localProjOn_basisFun

/-- info: 'CSD.RecordLayer.sum_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_localProjOn

/-- info: 'CSD.RecordLayer.sum_normSq_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_normSq_localProjOn

/-- info: 'CSD.RecordLayer.traceRight_sum_vecOuter_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.traceRight_sum_vecOuter_localProjOn

/-- info: 'CSD.RecordLayer.reduceA_localLudersOn_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_localLudersOn_mixture

-- MeasurementCapstone (2026-08-03, SigmaLayer/MeasurementCapstone.lean; the second review's
-- step 4). ★★★ projectiveMeasurementCapstone — the corpus's four measurement closures as ONE
-- Prop, for every Hermitian generator, base point, and unit preparation: rank_one
-- (unifiedArenaClosure — one arena, one Liouville family), every_basis
-- (measurement_covariance — the apparatus basis is a parameter, not preferred structure),
-- degenerate (joinWitness_blockLuders — every block structure, ψ-dependent Lüders through
-- Liouville-preserving dynamics), smooth (smoothWitnessClosureCanonical — the ε-horn at every
-- ε, as Nonempty since the closure carries its protocol), generation (rampedU_schrodinger as
-- a field — added 2026-08-03, fourth review). The fields quantify over different witnesses BY
-- DESIGN: the two-horn framing (author decision 2026-08-03). New prose cites this one
-- theorem; the constituent closures remain as the construction record.
/-- info: 'CSD.RecordLayer.projectiveMeasurementCapstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projectiveMeasurementCapstone

-- MixedSwap (2026-08-03, SigmaLayer/MixedSwap.lean; the mixed-preparations row). A mixed
-- preparation is two-stage sampling made a measure: mixedSwapPrep ρ = Σ_j λ_j • swapPrep [ψ_j]
-- over the spectral ensemble (a probability measure by eigenvalues_isProbability).
-- ★ mixed_swap_sector_born — THE MIXED DYNAMICAL BORN RULE: the mixture's mass on the
-- measurement protocol's outcome sector is exactly Tr(ρ|e_i⟩⟨e_i|); same propagator, same
-- sectors, classical ignorance responding as traceForm demands (spectral bridge
-- spectral_born_eq_traceForm via swap_sector_born per eigenray + traceForm_eq_pureEnsemble +
-- born_quadratic). Record creation/exclusivity/persistence are per-protocol facts, inherited
-- verbatim; the Bayes-conditioned mixture posts WERE a recorded extension and are now
-- delivered (MixedLuders, pinned below: mixed_post_bayes, mixed_luders_followup).
/-- info: 'CSD.RecordLayer.spectral_born_eq_traceForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.spectral_born_eq_traceForm

/-- info: 'CSD.RecordLayer.mixed_swap_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_swap_sector_born

-- PovmDynamics (2026-08-03, SigmaLayer/PovmDynamics.lean; the POVM/instrument-dynamics row).
-- A POVM is a projective measurement on a dilated space watched through an isometry — made
-- DYNAMICAL: prepare the dilated ray [Vψ] on the flat index and run the EXISTING degenerate
-- record protocol with the ancilla block structure localBlock N K (no new dynamics/sectors).
-- ★ povm_selector_born — THE DYNAMICAL POVM BORN RULE: the block selector's outcome-i sector
-- at [Vψ] carries exactly ⟨ψ, E_i ψ⟩ (degenerate_selector_born + born_transfer through the
-- spectral bridge sum_block_normSq_dilate).
-- ★ toComposite_blockProj_dilate — the record-layer block posts ARE the Naimark–Lüders posts
-- Π_i(Vψ) under the index transport.
-- ★★ povm_instrument — the join witness's post-marginals satisfy degenerate Lüders at the
-- dilated preparation: outcome i relocates the dilated system to [Π_i(Vψ)], the instrument of
-- the dilation (Liouville-preserving dynamics, not fiat).
-- ★★ naimarkInstrumentClosure / …Canonical — the bundle for every dilation, and via
-- canonicalNaimark for EVERY POVM. Honest scope: the instrument is dilation-relative (a POVM
-- does not determine its instrument); realising V as a unitary-plus-ancilla stroke = recorded
-- extension.
/-- info: 'CSD.RecordLayer.povm_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_selector_born

/-- info: 'CSD.RecordLayer.toComposite_blockProj_dilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.toComposite_blockProj_dilate

/-- info: 'CSD.RecordLayer.povm_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_instrument

/-- info: 'CSD.RecordLayer.naimarkInstrumentClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.naimarkInstrumentClosure

/-- info: 'CSD.RecordLayer.naimarkInstrumentClosureCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.naimarkInstrumentClosureCanonical

-- JoinClosure (2026-08-03, SigmaLayer/JoinClosure.lean; the degenerate one-protocol package,
-- fourth external review). The degenerate pieces existed as theorems on the join protocol but
-- were never packaged as ONE closure on ONE protocol.
-- ★ join_sector_born — the coarse dynamical Born mass: the canonical join preparation gives
-- the outcome-i sector exactly the block Born weight Σ_{j: b j = i}‖⟨e_j,ψ⟩‖², independently
-- of the ancilla calibration (quantified). Spine: preimage_sector_ae (sector = good-fibre
-- cylinder a.e.) + volume_goodTheta (the Dirac slice of degenerate_selector_born).
-- ★★ degenerateMeasurementClosure — ready/record/exclusivity/persistence + Liouville + the
-- Born mass + ψ-dependent degenerate Lüders (joinWitness_blockLuders), one structure, one
-- protocol, for every block structure and preparation. The capstone's degenerate field is
-- upgraded to this closure (was bare BlockLudersObligation).
/-- info: 'CSD.RecordLayer.join_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.join_sector_born

/-- info: 'CSD.RecordLayer.degenerateMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.degenerateMeasurementClosure

/-- info: 'CSD.RecordLayer.mixed_post_bayes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_post_bayes

/-- info: 'CSD.RecordLayer.mixed_luders_followup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_luders_followup

-- PointerSmoothProfile (2026-08-03, SigmaLayer/PointerSmoothProfile.lean; the C^∞-ingredients
-- row, fourth external review's "continuous, not smooth"). Real.smoothTransition profiles with
-- the plateau interface VERBATIM IDENTICAL to the trapezoids' (same statements, same
-- hypotheses: =1 on the shrunk arc, =0 off the open arc, 0/π-halves around the stroke) — only
-- the corridor's shape changed.
-- contDiff_smoothClampDiv — the smooth clamp is C^∞ (what clampDiv could not be at its joins).
-- ★ contDiff_smoothArcWeight_lift — the arc weight's 1-periodic lift is C^∞ on the universal
-- cover: both circle-distance kinks fall inside plateaus (centre: 2ε < r; cut locus: r < 1),
-- and the transition zone sees a locally affine distance (round locally constant strictly
-- inside the half-integer window). The strongest formulation without a manifold structure on
-- the arena (that stays §2a-scoped with A1/A3).
-- SUBSTITUTED 2026-08-04 (BACKLOG B1): the profile primitives moved DOWN the import graph to
-- SigmaLayer/SmoothProfile.lean and pointerWeights is now built on smoothArcWeight, so the
-- witness USES the C^infinity profile rather than citing it. The plateau interface is
-- identical by construction, so every downstream landing/Born/protocol proof transferred with
-- no change. contDiff_pointerWeights_lift is the new smoothness statement, and it is what
-- makes {w_i, w_j} well-formed -- the prerequisite the joint-arena Poisson route turns on.
-- The TIME RAMP is deliberately still the trapezoid (not a phase-space function; swapping it
-- would put a rate factor in the capstone's generation field -- BACKLOG B1b).
/-- info: 'CSD.RecordLayer.contDiff_pointerWeights_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_pointerWeights_lift

-- ★ smoothRampedU_schrodinger — SCHRÖDINGER AT EVERY TIME: the smooth ramp removes the open-
-- window restriction of rampedU_schrodinger (the corners are gone, as PointerGeneration's
-- honest scope predicted); outside [0,1] the ODE reads U̇ = 0 — persistence as an ODE.
-- Protocol re-instantiation = mechanical (identical interface), recorded.
/-- info: 'CSD.RecordLayer.contDiff_smoothClampDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_smoothClampDiv

/-- info: 'CSD.RecordLayer.contDiff_smoothArcWeight_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_smoothArcWeight_lift

/-- info: 'CSD.RecordLayer.smoothRampedU_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothRampedU_schrodinger

-- NullSeamWitness (2026-08-03, SigmaLayer/NullSeamWitness.lean; the "Cantor-horn" row, fourth
-- external review — delivered, and SIMPLER than the devil's-staircase sketch: the transition
-- between record regions dodges the record gap by crossing WHERE THE RECORD REGIONS KISS
-- (m₁ = m₂ = ½), touching the complement at one projective point; the crossing angle sweeps
-- continuously in the register, hitting π/4 exactly at the two cell boundaries.
-- ★ nullSeam_seam_null — the seam is TWO POINTS (nullSeamSign = infDist-to-arc difference:
-- negative exactly on the open first cell, positive exactly on the second, zero exactly at
-- the boundaries). ★ nullSeam_born_left/right — EXACT Born (r and 1−r, no ε; closedBall
-- sandwich + the two-point seam). ★★ continuous_nullSeamEvolve + Liouville preservation
-- (skew product, FS unitary invariance; the measure is NOT called Liouville — S¹ × ℂℙ² is
-- odd-dimensional hence not symplectic, naming corrected 2026-08-03 by the fifth review).
-- ★★ nullSeamClosure — THE THIRD HORN EXISTS.
-- THE TRILEMMA: each horn pays exactly one of — seams (piecewise), ε-Born (smooth witness),
-- Dirac calibration (this witness: exactness is at the calibrated ready point [f₀]; with a
-- positive-width ready region the seam fattens to O(δ) — the price collapse_accuracy_bound
-- already prices). Whether a fourth combination is impossible = recorded candidate no-go.
/-- info: 'CSD.RecordLayer.nullSeam_seam_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeam_seam_null

/-- info: 'CSD.RecordLayer.nullSeam_born_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeam_born_left

/-- info: 'CSD.RecordLayer.continuous_nullSeamEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_nullSeamEvolve

/-- info: 'CSD.RecordLayer.nullSeamClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamClosure

-- JointFlowTransfer (2026-08-04, SigmaLayer/JointFlowTransfer.lean; BACKLOG A1 -- the
-- formalisable half of the joint-arena Hamiltonian route). Paper C A2 / TN6 want measurement
-- generated by a scalar on the WHOLE arena; the corpus's witness is fibrewise
-- (pointerEvolve_fst freezes the base by rfl). A genuine joint flow BACK-REACTS, and the
-- worry was that this destroys the landing/Born analysis. It does not:
-- ★★ IsJointLift.outcomeSector_eq — the record preimages are the SAME SET, not merely the
-- same measure: arenaRecord is a cylinder over the pointer, so horizontal motion is invisible
-- to it. Landing and both Born bounds then transport with NO measure-theoretic work.
-- ★ IsJointLift.weights_conserved — the weight field is a constant of motion; this is exactly
-- what the Poisson argument {w_i,w_j} = 0 delivers, and it is well-formed only since B1 made
-- the weights C^infinity.
-- ★ IsJointLift.moment_marginal_unchanged — THE HONEST REPLACEMENT for the no-collapse
-- theorem: under a genuine lift the base point moves inside its moment fibre, so
-- pointerEvolve_base_marginal_unchanged FAILS; what survives is that the moment-and-register
-- data is unchanged. Prose about the joint flow must claim this, not the stronger statement.
-- isJointLift_pointerEvolve — non-vacuity (the fibrewise witness is a lift with zero
-- back-reaction). CONDITIONAL by design (CONVENTIONS 8.3 _of_): discharging the hypotheses
-- for the actual X_H is the paper's job, and the Hamiltonian identification stays 2a-scoped.
/-- info: 'CSD.RecordLayer.IsJointLift.outcomeSector_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.outcomeSector_eq

/-- info: 'CSD.RecordLayer.IsJointLift.weights_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.weights_conserved

/-- info: 'CSD.RecordLayer.IsJointLift.moment_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.moment_marginal_unchanged

/-- info: 'CSD.RecordLayer.jointFlowTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.jointFlowTransfer

/-- info: 'CSD.RecordLayer.isJointLift_pointerEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.isJointLift_pointerEvolve

-- ChartBracket (2026-08-04, SigmaLayer/ChartBracket.lean; BACKLOG A3 -- the formalisable
-- fragment of the joint-arena Poisson argument). Stating {w_i,w_j}=0 on the ARENA needs
-- omega^-1 dH, the one arrow Mathlib lacks. In a DARBOUX CHART it is a computation: the
-- bracket is an explicit fderiv expression and the Hamiltonian field is the explicit
-- swap-and-negate (no omega^-1 needed in canonical coordinates).
-- ★ poissonBracket_eq_zero_of_disjoint — the FAITHFUL statement, and NOT the naive one:
-- H = sum_j w_j(x) h_j(q) is NOT momentum-free (it depends on the pointer's momenta), so
-- "both momentum-independent" would be false of H. What holds is DISJOINT SUPPORT: w is
-- momentum-free and its position indices are disjoint from H's momentum indices -- which is
-- exactly the product structure of the arena (base vs pointer).
-- poissonBracket_comm_of_momentumIndep — the easy case {w_i,w_j}=0, no support hypothesis.
-- ★ conserved_of_bracket_eq_zero / weight_conserved_of_disjoint — vanishing bracket implies
-- constant along any integral curve of X_H: the conservation A2 needs, feeding A1's
-- IsJointLift.weights_conserved.
-- SCOPE: a chart MODEL. KSigma x CP^K is not globally R^{2n} and nothing here transports to
-- the arena -- that transport IS the missing arrow (A4). d-omega = 0 is not stated because in
-- a canonical chart it is automatic, which is precisely why this is weaker than the manifold
-- statement.
/-- info: 'CSD.SigmaLayer.poissonBracket_eq_zero_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.poissonBracket_eq_zero_of_disjoint

/-- info: 'CSD.SigmaLayer.poissonBracket_comm_of_momentumIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.poissonBracket_comm_of_momentumIndep

/-- info: 'CSD.SigmaLayer.conserved_of_bracket_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conserved_of_bracket_eq_zero

/-- info: 'CSD.SigmaLayer.weight_conserved_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.weight_conserved_of_disjoint

-- NullSeamLift (2026-08-04, SigmaLayer/NullSeamLift.lean; BACKLOG B2). The third horn was
-- built on S^1 x CP^2 -- real dimension 5, ODD, hence no symplectic structure, which is why
-- its measure had to be renamed nullSeamMeasure. Giving the register its CONJUGATE coordinate
-- makes the arena T^2 x CP^2, dimension 6. The construction is unchanged (the crossing still
-- reads theta_1; theta_2 rides along untouched, as a conjugate variable does when the
-- generator does not depend on it), so every transfer is a cylinder argument.
-- ★★ nullSeamLiftClosure — the third horn on an even-dimensional arena; ★ born_left/right
-- exact r and 1-r via Measure.prod_prod; seam still null (two points x T^1).
-- EARNED: the parity obstruction is gone. NOT EARNED and not claimed: the symplectic FORM
-- itself -- Mathlib has no symplectic API, so "this measure IS the Liouville volume of
-- omega^3/3!" stays section-2a scoped (A4). Even dimension is necessary, not sufficient.
/-- info: 'CSD.RecordLayer.nullSeamLiftClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamLiftClosure

/-- info: 'CSD.RecordLayer.nullSeamLift_born_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamLift_born_left

/-- info: 'CSD.RecordLayer.nullSeamEvolveLift_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamEvolveLift_measurePreserving

-- PointerFrequency (2026-08-04, SigmaLayer/PointerFrequency.lean; BACKLOG B3a). The smooth
-- horn proved a SINGLE-SHOT sandwich but never said what an experimenter sees. The exact
-- horns have had the frequency layer since LF1; the smooth horn did not.
-- ★ pointer_born_frequency — i.i.d. trials of the smooth witness's preparation: the relative
-- frequency of outcome j converges a.s., and the limit sits in the eps-window
-- [r_j - 2eps, r_j + 2(N-1)eps] (pointerSectorProb_mem_window carries the ENNReal sandwich
-- across toReal, safe because pointerPrep is a probability measure).
-- Nothing new was needed: LF1's freq_tendsto_of_iid is already generic over (measurable
-- space, probability measure, measurable event) and the smooth witness supplies all three.
-- SCOPE: the limit is BRACKETED, not pinned -- the eps-horn's price; and eps -> 0 sharpens
-- the window only ACROSS witnesses, since each eps is a different propagator.
/-- info: 'CSD.RecordLayer.pointer_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_frequency

/-- info: 'CSD.RecordLayer.pointerSectorProb_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerSectorProb_mem_window

-- PovmSectorBorn (2026-08-04, SigmaLayer/PovmSectorBorn.lean; BACKLOG B4). Discharges the
-- scope note the 2026-08-04 audit added to PovmDynamics: povm_selector_born was DESCRIBED as
-- "the dynamical POVM Born rule" but measures a SELECTOR FIBRE, not a protocol outcome
-- sector -- the distinction SwapClosure states explicitly.
-- ★★ povm_sector_born — the JOIN PROTOCOL's outcome sector (initial states destined for
-- record i) at the dilated preparation carries exactly <psi, E_i psi>. This is the dynamical
-- statement the prose had claimed. povm_sector_born_canonical: every POVM, via canonicalNaimark.
-- It is a two-line composition of join_sector_born (the protocol-sector spine,
-- preimage_sector_ae + volume_goodTheta) with sum_block_normSq_dilate -- which is itself the
-- evidence that the original defect was one of DESCRIPTION, not missing mathematics.
-- Unchanged scope: the instrument stays dilation-relative, and V-as-unitary-stroke is still
-- a recorded extension; both statements take the dilated ray [V psi] as entry point.
/-- info: 'CSD.RecordLayer.povm_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_sector_born

/-- info: 'CSD.RecordLayer.povm_sector_born_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_sector_born_canonical

-- SharpenedNoGo (2026-08-04, SigmaLayer/SharpenedNoGo.lean; BACKLOG B5, the trilemma's
-- third leg -- SHARPENED, NOT CLOSED).
-- ★ posMeasure_noRecord_of_isOpenMap — an OPEN-MAP propagator on an OPEN ready set cannot
-- hide the no-record set in a null set: the image is an open neighbourhood, and any
-- neighbourhood of a boundary point of the no-record set meets its INTERIOR, which has
-- positive measure. posMeasure_noRecord_unitary specialises to a unitary stroke on CP^K
-- (a homeomorphism; FS is positive on nonempty opens). This is exactly why a DIRAC
-- calibration escapes: a point has no neighbourhood to spare, which is how the null-seam
-- witness threads the kissing state and keeps its seam null.
-- ⚠️ WHAT IT DOES NOT PROVE, and a correction to my own earlier claim: NullSeamWitness said
-- a positive-width ready region fattens the seam "of order the calibration width". The ORDER
-- is quantitative, does NOT follow from this topological argument, and is proved nowhere --
-- corrected at source. Also: the forcing step (that some ready state MUST land in the
-- closure of the no-record interior) is a HYPOTHESIS here, not a conclusion; deriving it
-- needs no_everywhere_correlation's connectedness plus a regularity condition on the
-- no-record set. Hence: the leg is sharpened, not closed.
/-- info: 'CSD.RecordLayer.posMeasure_noRecord_of_isOpenMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_of_isOpenMap

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_unitary

-- FORCING STEP CLOSED (same session): exists_noRecord_of_meets_two inverts
-- no_everywhere_correlation -- instead of assuming the image is covered by two record
-- regions and deriving False, conclude it is NOT covered, so a correlating propagator on a
-- preconnected ready set MUST carry some state outside every record region.
-- ★★ posMeasure_noRecord_of_correlates chains that to the measure bound. The hypotheses now
-- split by KIND: everything about the DYNAMICS is discharged (continuity, open map,
-- correlation), and the single remaining assumption is about the RECORD GEOMETRY -- that the
-- no-record set is contained in the closure of its interior. True of the corpus's moment
-- regions (perturb toward the ready vertex) but NOT constructed, so the leg is closed modulo
-- a geometric fact rather than closed outright.
-- [2026-08-05: that geometric fact IS now constructed -- NoRecordGeometry block below;
-- the "closed modulo" qualifier above is superseded and B5 is closed outright.]
/-- info: 'CSD.RecordLayer.exists_noRecord_of_meets_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.exists_noRecord_of_meets_two

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_of_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_of_correlates

-- PointerLuders (2026-08-05, SigmaLayer/PointerLuders.lean; BACKLOG B3b, BRICK 1 ONLY).
-- The smooth witness PROVABLY does not collapse (pointerEvolve_base_marginal_unchanged) --
-- a feature, but it means the smooth horn gives records and Born and no state update.
-- Composing with relocation needs an arena carrying pointer AND bank, and a relocation
-- triggered by the POINTER's record region rather than a torus arc. That is this brick.
-- pointerIndex — the readout off the record regions, well defined by their disjointness.
-- pointerRelocate — swap system with bank slot j when the pointer displays j; ★ it never
-- moves the pointer, so the record survives its own relocation.
-- ★ pointerBankSwap_measurePreserving — the slot swap preserves the composed arena measure
-- (same conjugation as the torus version; FS vs Haar plays no part).
-- pointerLudersStroke — the two-stroke composite, DEFINED.
-- ⚠️ NOT PROVED HERE, and the docstring says so: measure preservation of pointerRelocate
-- ITSELF (a piecewise map -- needs the partition argument swapG uses, with record cylinders
-- in place of register arcs), and the conditioned post-measurement marginal. Those are
-- brick 2, and until they land this module is the ARENA AND DYNAMICS, not a Lüders theorem.
-- Nothing here weakens pointerEvolve_base_marginal_unchanged: relocation is a SECOND stroke.
-- [2026-08-05: both owed items are now proved -- PointerLudersMarginal block below; the
-- "arena and dynamics, not a Lüders theorem" qualifier is superseded and B3b is closed.]
/-- info: 'CSD.RecordLayer.pointerBankSwap_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerBankSwap_measurePreserving

/-- info: 'CSD.RecordLayer.pointerRelocate_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRelocate_pointer

/-- info: 'CSD.RecordLayer.pointerIndex_eq_some_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerIndex_eq_some_of_mem

-- NoRecordGeometry (2026-08-05, SigmaLayer/NoRecordGeometry.lean; BACKLOG B5-geom -- and
-- with it B5 CLOSED OUTRIGHT).
-- The single remaining hypothesis of the trilemma's third leg was GEOMETRIC: that the
-- no-record set is contained in the closure of its interior. The construction: feed weight
-- into the ready component (feedReady) -- every record numerator is fixed, the norm
-- strictly grows, so every record moment strictly drops below 1/2; the family is
-- phase-preserving on the nonzero branch, so convergence back to the ray is immediate and
-- needs no chart argument.
-- ★ noRecord_subset_closure_strict — the core, for an arbitrary index set of record
-- moments (one proof serves the all-j and pair consumers).
-- ★ noRecord_subset_closure_interior — B5-geom as stated in the BACKLOG row.
-- ★ recordRegion_pair_compl_regular — the pair form posMeasure_noRecord_of_correlates's
-- hreg consumes.
-- ★★ posMeasure_noRecord_pointer — B5: on the pointer manifold, a continuous open-map
-- propagator correlating two outcomes on an open preconnected ready set gives the
-- no-record set positive FS measure. NO geometric hypothesis remains -- exact-a.e. records
-- force Dirac calibration as a THEOREM. Honest scope unchanged: this is the LOCAL leg
-- (the pointer's moment regions); general exhaustiveness over all arenas stays research.
/-- info: 'CSD.RecordLayer.noRecord_subset_closure_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.noRecord_subset_closure_strict

/-- info: 'CSD.RecordLayer.noRecord_subset_closure_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.noRecord_subset_closure_interior

/-- info: 'CSD.RecordLayer.recordRegion_pair_compl_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pair_compl_regular

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_pointer

-- PointerLudersMarginal (2026-08-05, SigmaLayer/PointerLudersMarginal.lean; BACKLOG B3b
-- brick 2 -- and with it B3b CLOSED).
-- Brick 1 explicitly owed two things; both land here.
-- ★ pointerRelocate_measurePreserving — the piecewise invariance: the arena partitions
-- into record cylinders (where the relocation is brick 1's measure-preserving slot swap,
-- and fixes its own piece because it never moves the pointer) and the no-record piece
-- (identity); measurePreserving_of_partition assembles -- the swapG argument with record
-- cylinders in place of register arcs, exactly as the brick-1 gap note predicted.
-- ★ pointerLudersStroke_measurePreserving — the WHOLE two-stroke composite conserves
-- Liouville measure: collapse as relocation, not contraction, on the smooth horn.
-- pointerProtocol_outcomeSector — the sector identification: the protocol's sector IS the
-- brick-2b propagator's preimage of the record cylinder (the trigger the relocation reads).
-- ★★ pointer_luders_marginal — THE LUDERS THEOREM for the smooth horn: conditioned on the
-- outcome-i sector (a base cylinder -- the bank plays no part in which outcome occurs),
-- the post-stroke system marginal IS the slot-i calibration. Same three moves as
-- swap_luders_marginal; the trigger is the pointer's record region, not a torus arc.
-- ★ pointer_luders_born — CSD form: follow-up statistics are the COLLAPSED state's Born
-- weights, for any context field.
-- ★★ pointer_luders_born_prep — on the witness's OWN preparation: 2eps < rate i makes the
-- conditioning non-vacuous via the eps-Born lower bound, so the smooth horn now delivers
-- records (eps-Born) AND a Lueders update on one arena.
-- Honest scope unchanged: rank-one only (degenerate = join witness); one bank per
-- measurement; the two-stroke composite is NOT a MeasurementProtocol (the relocation is a
-- triggered map, not a flow -- its Hamiltonian generation stays the same recorded
-- extension as the swap witness's); the eps lives in WHICH outcome occurs, never in the
-- post-measurement state (the conditioned marginal is exact).
/-- info: 'CSD.RecordLayer.pointerRelocate_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRelocate_measurePreserving

/-- info: 'CSD.RecordLayer.pointerLudersStroke_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerLudersStroke_measurePreserving

/-- info: 'CSD.RecordLayer.pointerProtocol_outcomeSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerProtocol_outcomeSector

/-- info: 'CSD.RecordLayer.pointer_luders_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_luders_marginal

/-- info: 'CSD.RecordLayer.pointer_luders_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_luders_born

/-- info: 'CSD.RecordLayer.pointer_luders_born_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_luders_born_prep

/-- info: 'CSD.RecordLayer.coupling_hamiltonian_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.coupling_hamiltonian_duality

-- MixedJoinLuders (2026-08-06, SigmaLayer/MixedJoinLuders.lean; BACKLOG D3a --
-- degenerate outcomes on mixed preparations, riding JoinClosure exactly as
-- MixedLuders's scope note predicted).
-- ★ mixed_join_sector_born — the mixed BLOCK Born rule: sector mass = the block sum
-- of Tr(rho|e_k><e_k|), via the block spectral bridge (sum interchange + one rank-one
-- bridge per block member, spectral_block_born_eq_traceForm).
-- ★ mixed_join_post_bayes — Bayes on a degenerate outcome: posterior weight
-- lambda_j . p_{i|j} / sum_k Tr(...), likelihood = eigenvector j's block Born weight;
-- the same cond_finsetSum engine as the rank-one case.
-- ★★ mixed_join_luders — BLOCK LUDERS COMPOSED WITH BAYES: the conditioned system
-- marginal is the Bayes mixture of the per-component degenerate posts
-- epistemicMeasure [Pi_i psi_j]. At rank >= 2 the posteriors are GENUINELY DISTINCT:
-- the record does not erase classical ignorance -- the density-operator update
-- rho -> Pi rho Pi / Tr(rho Pi) realised as a mixture (contrast the rank-one vertex
-- collapse of mixed_luders_followup).
-- ⚠️ Scope: stated under hproj (every spectral component meets block i); a component
-- with zero block projection has zero Bayes weight but no Lueders post AS A RAY, so
-- the filtered refinement is recorded in-module rather than shipped as a weaker
-- theorem under the same name.
/-- info: 'CSD.RecordLayer.spectral_block_born_eq_traceForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.spectral_block_born_eq_traceForm

/-- info: 'CSD.RecordLayer.mixed_join_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_join_sector_born

/-- info: 'CSD.RecordLayer.mixed_join_post_bayes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_join_post_bayes

/-- info: 'CSD.RecordLayer.mixed_join_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_join_luders


-- A1 parity: the record layer on the EVEN-dimensional fibre (2026-08-09,
-- SigmaLayer/TorusRecord.lean). CircleFibre/CircleRecord fixed the fibre's non-compactness
-- but not its parity: a single circle is 1-dimensional, so CP^{N-1} x S^1 has ODD real
-- dimension and cannot carry a symplectic or Kaehler structure at all. TorusFibre put the
-- Born cells on T^2 (cells constrain the first angle, the second stays free); this file
-- ports the rest of the record layer there, so the ACTIVE fibre and the A1-admissible
-- arena are finally the same object: torusRecordSemantics (P5), compatibleSet_torus_single
-- (P6 isolation = conditioning), torusOutcome_eq_record (the ontic selection IS the
-- record), and the Born weight ||psi i||^2 unchanged from the R and S^1 fibres.
-- HONEST SCOPE, in the module: no Kaehler form is constructed on the arena and the fibre
-- measure is not shown to be a Liouville volume for one (Mathlib has no manifold forms
-- API; standing KG-1 block). Parity was a NECESSARY condition that was violated and now is
-- not. That is not sufficiency, and no A1 discharge is claimed.
/-- info: 'CSD.RecordLayer.torusOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusOutcome_eq_record

/-- info: 'CSD.RecordLayer.torusBornMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusBornMeasurement_prob

/-- info: 'CSD.RecordLayer.torusBornMeasurement_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusBornMeasurement_ae_total

-- The relocation-generation obstruction (2026-08-10, RelocationObstruction.lean).
-- PointerGeneration closed the record-CREATING half (rampedU_schrodinger: the stroke is the
-- flow of an explicit Hermitian generator). These four close the COLLAPSE half negatively.
-- Horn 1: the bank swap exchanges the system factor with slot j, so it collapses the circle
-- section embedded in the system's torus angle (after the exchange that coordinate reads
-- slot j, held constant) -- and the circle is not contractible. NOT the PiecewiseHamiltonian
-- flux obstruction: flux obstructs within the identity component, this never reaches it, and
-- the H^1(CP^K)=0 escape does not apply because the obstruction is in the bank's product
-- structure. Horn 2: the non-permutation alternative (imprint into a ready slot) is not
-- injective, hence not a homeomorphism, hence not a flow map either. Scope: the SWAP
-- architecture, not collapse-as-dynamics in general.
/-- info: 'CSD.RecordLayer.pointerBankSwap_not_homotopic_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointerBankSwap_not_homotopic_id

/-- info: 'CSD.RecordLayer.pointerBankSwap_not_flow_time_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointerBankSwap_not_flow_time_one

/-- info: 'CSD.RecordLayer.pointerImprint_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointerImprint_not_injective

/-- info: 'CSD.RecordLayer.pointerImprint_not_homeomorph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointerImprint_not_homeomorph

-- The join relocation IS generated (2026-08-10, JoinGeneration.lean) -- the POSITIVE
-- counterpart to RelocationObstruction. The bank arena is a PRODUCT and pointerBankSwap
-- exchanges two of its factors; the join arena is CP^{N+N-1}, a SINGLE projective space, and
-- joinSwap is one unitary acting on it. So neither horn applies: nothing to exchange, and a
-- projective unitary is bijective. Constructively: joinMat is a Hermitian involution (real
-- permutation matrix of an involutive permutation), so Q = (1-P)/2 is a Hermitian idempotent,
-- so U(t) = (1-Q) + e^{i*pi*t}Q is unitary with U 0 = 1 and U 1 = joinMat, and it solves the
-- Schrodinger ODE for the explicit Hermitian generator H = pi*Q. No matrix exponential is
-- needed: on an idempotent the series collapses to 1 + (e^z - 1)Q, written down in closed
-- form. Collapse CAN be dynamics; the obstruction really was about the swap architecture.
/-- info: 'CSD.RecordLayer.joinMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinMat_mul_self

/-- info: 'CSD.RecordLayer.joinProj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinProj_mul_self

/-- info: 'CSD.RecordLayer.joinFlowMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinFlowMat_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.joinGen_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinGen_isHermitian

/-- info: 'CSD.RecordLayer.joinFlowMat_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinFlowMat_hasDerivAt

/-- info: 'CSD.RecordLayer.joinSwap_eq_flowTimeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinSwap_eq_flowTimeOne

-- D3b: the general-N null-seam witness (NullSeamGeneralN.lean, 2026-08-12) —
-- the third horn at every N >= 2 and every weight vector: continuity, measure
-- invariance, exact records off an N-point null seam, exact Born mass r i per
-- cell; plateau tents + the amplitude-polynomial seam rotation (no
-- per-boundary gluing, no monodromy). Two-cell witness unchanged as the
-- minimal exhibit.
/-- info: 'CSD.RecordLayer.nullSeamGenClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.nullSeamGenClosure

/-- info: 'CSD.RecordLayer.nullSeamGenClosure_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.nullSeamGenClosure_uniform

/-- info: 'CSD.RecordLayer.nullSeamGen_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.nullSeamGen_outcome

/-- info: 'CSD.RecordLayer.nullSeamGen_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.nullSeamGen_born

/-- info: 'CSD.RecordLayer.seamRotationR_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.seamRotationR_orthogonal


-- Q18 / the Q11 first brick (2026-08-13, RecordLayer/StatisticsRigidity): transition
-- probabilities are RECORD OBSERVABLES, and both necessity-audit conditioners convert.
-- recordKernel p q is the Born rate a context containing q assigns to the unit preparation
-- representative of p, defined through bornRateBasis (never the inner product); every ray is
-- an outcome of some context (exists_context_extending_ray, Gram-Schmidt extension); the
-- HEADLINE recordKernel_eq_transProb identifies the operational statistic with the FS
-- transition probability, recordKernel_well_defined makes it apparatus-independent, and the
-- iff makes "preserves record statistics" THE SAME predicate as TransProbPreserving. The two
-- conversions: projectedFlow_unitary_of_record_statistics (W3+Bargmann with the record-level
-- premise in place of the hTPP FS-isometry posit -- a premise CONVERSION, honestly a thin
-- wrapper) and measure_eq_fubiniStudy_of_record_statistics_invariant (any probability measure
-- invariant under every statistics-preserving symmetry IS fubiniStudyMeasure -- U(N) in the
-- proof, never the statement). recordStatisticsPreserving_realisation pins the operational
-- symmetry group semi-unitary via Wigner. NOT claimed: elimination of the posits (the
-- operational premises survive, papers owe motivation); TPP from measure preservation (the
-- section-13.2 trap, untouched); the FS-invariance converse (needs conjProj pushforward
-- invariance, absent); D1 G-from-dynamics (still obstructed, sidestepped). See
-- specs/unitary-tpp-scoping.md sections 4-5 and BACKLOG row Q18.
/-- info: 'CSD.RecordLayer.exists_context_extending_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.exists_context_extending_ray

/-- info: 'CSD.RecordLayer.transProb_mk_eq_bornRateBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.transProb_mk_eq_bornRateBasis

/-- info: 'CSD.RecordLayer.recordKernel_eq_transProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.recordKernel_eq_transProb

/-- info: 'CSD.RecordLayer.recordKernel_well_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.recordKernel_well_defined

/-- info: 'CSD.RecordLayer.recordStatisticsPreserving_iff_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.recordStatisticsPreserving_iff_transProbPreserving

/-- info: 'CSD.RecordLayer.recordStatisticsPreserving_realisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.recordStatisticsPreserving_realisation

/-- info: 'CSD.RecordLayer.projectedFlow_unitary_of_record_statistics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.projectedFlow_unitary_of_record_statistics

/-- info: 'CSD.RecordLayer.measure_eq_fubiniStudy_of_record_statistics_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measure_eq_fubiniStudy_of_record_statistics_invariant

-- C2 PBR PREPARATION CAPSTONE (2026-08-25, RecordLayer/PBRPreparation.lean): THE EXACT
-- SHARP INTERFACE IS PSI-ONTIC. epistemicMeasure_projectiveLaw -- the concrete exact
-- witness delta_p (x) Haar pushes forward to delta_p on the base (shown, not assumed, so
-- the witness is demonstrably inside the classified class). sharp_preparations_
-- mutuallySingular -- ANY two ontic measures whose projective laws are Diracs at distinct
-- points are mutually singular; hypothesis is the Dirac pushforward alone, no Preparation,
-- no region, no finiteness. epistemicMeasure_mutuallySingular -- the concrete corollary,
-- routed THROUGH the general theorem so the proof graph C2 cites is the checked one.
-- no_region_preparation_exact_fibre -- an exact fibre is kMuL-null (kMuL_fibre_null) and so
-- is not the region of any positive-volume SigmaLayer.Preparation (SET-level).
-- STRENGTHENED 2026-08-25 to the MEASURE level: epistemicMeasure_fibre_one (the exact sharp
-- law puts mass 1 on its own fibre); epistemicMeasure_mutuallySingular_kMuL (the exact fibre
-- separates the sharp law from the Liouville measure outright); and
-- exact_sharp_ne_region_conditional -- no positive-volume region-conditioned LAW equals an
-- exact sharp LAW, however the region is chosen (region laws are kMuL-absolutely-continuous,
-- so they give the fibre 0; the sharp law gives it 1). That last is what C2 cites for class
-- separation; the set-level form is kept as the weaker companion. pbr_sharp_preparation_capstone -- the single citable
-- conjunction (both Dirac laws AND the singularity).
-- NOT PROVED, and not to be inferred: anything about PBR preparation independence, which
-- is a compositional assumption and remains neither established nor refuted.
/-- info: 'CSD.RecordLayer.epistemicMeasure_projectiveLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epistemicMeasure_projectiveLaw

/-- info: 'CSD.RecordLayer.sharp_preparations_mutuallySingular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.sharp_preparations_mutuallySingular

/-- info: 'CSD.RecordLayer.epistemicMeasure_mutuallySingular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epistemicMeasure_mutuallySingular

/-- info: 'CSD.RecordLayer.no_region_preparation_exact_fibre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.no_region_preparation_exact_fibre

/-- info: 'CSD.RecordLayer.pbr_sharp_preparation_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pbr_sharp_preparation_capstone

/-- info: 'CSD.RecordLayer.epistemicMeasure_fibre_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epistemicMeasure_fibre_one

/-- info: 'CSD.RecordLayer.epistemicMeasure_mutuallySingular_kMuL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epistemicMeasure_mutuallySingular_kMuL

/-- info: 'CSD.RecordLayer.exact_sharp_ne_region_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.exact_sharp_ne_region_conditional

end CSD.Tests.AxiomAudit
