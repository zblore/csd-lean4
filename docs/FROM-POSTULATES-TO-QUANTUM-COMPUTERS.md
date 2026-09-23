# From the postulates to a quantum computer: the chain, link by link

*(A reader's path, written 2026-09-19 from the ledgers: [`specs/reconstruction-status.md`](../specs/reconstruction-status.md),
[`specs/qit-chain-scoping.md`](../specs/qit-chain-scoping.md), [`specs/POSITS.md`](../specs/POSITS.md),
[`specs/residues.tsv`](../specs/residues.tsv) and [`EMPIRICAL.md`](../EMPIRICAL.md). It makes no claim of its own.
Every link names the theorems that carry it and the seam it rests on; where the ledgers say "witness,
not derivation", so does this page. The sector-by-sector reading lists are [`PATHS.md`](PATHS.md); the
reader-type paths and the measurement story are [`TOUR.md`](TOUR.md).)*

## The chain in one table

| # | Link | What the corpus establishes | Seam |
|---|---|---|---|
| 1 | The arena | `ℂℙⁿ × T²` is a symplectic Kähler arena whose measure is forced by its own symmetry | Posits 2, 3, 9: Fubini–Study as the typicality measure; Liouville preservation; the product form |
| 2 | Born | probability is a volume ratio, at every `N`, for every unit vector | Posit 4: that a volume ratio *is* a probability |
| 3 | Schrödinger | the projected flow is `exp(-itH)`-conjugation, derived at general `N` for arbitrary `H` | Posit 6: the unitary class |
| 4 | Observables and update | Gleason-type effects, Lüders and general conditioning, mixtures, POVMs, interference | none beyond 1–3; the closure is a consistency witness |
| 5 | Records | context-fixed basins at every `N`; a constructed de-isolation propagator produces Born | Posit 1 (open foundations); `R-015` (boundary); `R-016` (open mathematics) |
| 6 | Composites | non-factorisation, Bell, Tsirelson, no-signalling, contextuality, reduced-state records | Posit 7 local tomography (`R-017`, boundary); Posit 8 measurement independence |
| 7 | States and channels | a preparation is a density operator; a flow is a channel; de-isolation is the measurement channel; second law, Landauer, Holevo | none new; strong subadditivity comes through an external bridge |
| 8 | Gates | each standard gate is the isometry of a `Σ`-sector; a projective unitary action lifts to a `Σ`-flow | none new |
| 9 | Algorithms | Deutsch–Jozsa, Bernstein–Vazirani, Simon, Grover, the Fourier transform, Shor, teleportation; the sum over paths at finite dimension; Grover and Shor as `Σ`-flows | the other algorithms QM-side only; `R-002` |
| 10 | Error correction | QEC on `Σ` end to end for the three-qubit code; Shor-nine and Steane code mechanisms; stabiliser formalism | `R-003` to `R-006`: active Steane recovery, magic states, Clifford+T density, fault tolerance |
| 11 | Arithmetic and cost | verified reversible adders and modular arithmetic; measurement-gadget adders | `R-013` |

Four kinds of seam appear, and only one is a research problem. They are defined in
[`specs/POSITS.md`](../specs/POSITS.md) ("What frontier means here") and summarised at the end of this page.

## 1. The arena: geometry and symmetry fix `Σ`

**What is established.** The arena `Σ = ℂℙᴺ × T²` is an analytic manifold
(`CSD.LF4.ksigma_isManifold`, [`LF4/ProjectiveManifold.lean`](../CsdLean4/LF4/ProjectiveManifold.lean))
and a symplectic manifold (`arenaForm_isSymplectic`,
[`LF4/ArenaSymplectic.lean`](../CsdLean4/LF4/ArenaSymplectic.lean)). The projective factor carries the
Fubini–Study form, which is Kähler (`fsForm_isKahler`) and closed (`fsForm_mextDeriv`), and whose top power is
the Fubini–Study measure up to the constant `(4π)ⁿ` (`fsVolume_eq_smul_fsMeasure`). The sector's measure is
forced by its own symmetry rather than merely chosen (`kMuL_unique`,
[`LF4/LiouvilleUnique.lean`](../CsdLean4/LF4/LiouvilleUnique.lean)); its total mass is `(N+1)(4π)^N`
(`arenaVolume_univ`), and every smooth Hamiltonian flow on the arena preserves it
(`kMuL_map_hamiltonianFlow`, [`LF4/ArenaVolume.lean`](../CsdLean4/LF4/ArenaVolume.lean)). Every one of these
is Mathlib-only mathematics (Category 1) below the CSD layer, and the CSD layer instantiates it.

**The seam.** Three posits, all design choices stated as such in [`specs/POSITS.md`](../specs/POSITS.md).
Posit 2: the typicality measure on the projective base is Fubini–Study. What is proved is that it is the
unique measure compatible with the unitary symmetry; what is posited is that typicality is measured by it.
Posit 3: every time-`t` map of the constraint dynamics preserves the Liouville measure, a structure field of
every model. Posit 9: the measure is a product of the base measure and the uniform fibre measure; the base
half is a theorem, the fibre half is the posit.

**What is not claimed.** That `Σ` is derived from anything. The charter's position is that `Σ` is the floor,
and the corpus proves that a single flow cannot pin the Fubini–Study measure on its own
([`SigmaLayer/SectorPostulateNoGo.lean`](../CsdLean4/SigmaLayer/SectorPostulateNoGo.lean)). Constraining
`Σ` from above is the live work; deriving it is not a question the programme asks.

## 2. Born: probability as volume

**What is established.** The Born weight is the volume ratio of an outcome region, at every dimension and
for every unit vector: `fs_born_volume_ratio_N`
([`LF4/MomentBornN.lean`](../CsdLean4/LF4/MomentBornN.lean)), with the qubit case worked as a sphere
integral (`qubitBorn`, [`LF4/QubitBorn.lean`](../CsdLean4/LF4/QubitBorn.lean)). Frequencies converge to
those weights (`born_frequency_convergence_N`,
[`LF4/BornFrequencyN.lean`](../CsdLean4/LF4/BornFrequencyN.lean)). The weight is the torus moment map of
the Fubini–Study form, so the probability of an outcome is a coordinate of the arena's own geometry.

**The seam.** Posit 4, the typicality reading: that the volume ratio `μL(π⁻¹Ωᵢ(M) ∩ Ω₀) / μL(Ω₀)` *is* the
outcome probability, not merely equals it numerically. Its Lean entry point is the i.i.d. product structure
of the frequency layer, and the ledger says so. Posit 8 also enters here: one preparation measure serves
every measurement context, and nothing backs that short of assuming it. Both are shared with every
deterministic theory.

**What is not claimed.** That Born frequencies are derived from the flow. Link L7 of the connectivity
chain is open: a single trajectory provably cannot pin the measure, so the sector is posited and the
frequencies are a theorem given the posit.

## 3. Schrödinger: dynamics as the sector's Hamiltonian flow

**What is established.** On a genuine many-to-one sector with a nontrivial projection, the projected flow
is `exp(-itH)`-conjugation on rays, derived at general `N` for arbitrary Hermitian `H` through a
finite-dimensional C¹ Stone theorem the corpus supplies (`Matrix.StoneC1.stone_c1`,
[`Mathlib/Analysis/Matrix/StoneC1.lean`](../CsdLean4/Mathlib/Analysis/Matrix/StoneC1.lean)):
`CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived`
([`LF4/ManyToOneSchrodingerDerived.lean`](../CsdLean4/LF4/ManyToOneSchrodingerDerived.lean)). One object
carries both pillars, Born and Schrödinger (`manyToOneSchrodingerSetup_both_pillars`,
[`LF4/ManyToOnePillars.lean`](../CsdLean4/LF4/ManyToOnePillars.lean)). At the arena level the Schrödinger
unitary times the identity on the torus *is* the Hamiltonian flow of the sector energy
(`hamiltonianFlow_sectorEnergy_schrodinger`, [`LF4/ArenaSymplectic.lean`](../CsdLean4/LF4/ArenaSymplectic.lean)),
and on `ℂℙⁿ` alone the Schrödinger flow is the Hamiltonian flow of the expectation of `H`
(`hamiltonianFlow_schrodingerHamiltonian`).

**The seam.** Posit 6, the unitary class: the projected flow is projectively unitary. The corpus's Wigner
and Bargmann results select the unitary branch given transition-probability preservation, and that
preservation is a hypothesis of the interface, not a consequence of Liouville preservation. The ledger
records this in the W-series rows of [`specs/future-work.md`](../specs/future-work.md).

**What is not claimed.** That the witness derives unitary evolution from a fibre-primitive ontology. The
witness has `exp(-itH)` built in; the theorem is that the projected dynamics of that witness is Schrödinger
evolution, and that the Hamiltonian flow of the arena's own geometry reproduces it.

## 4. Observables, update, mixtures, POVMs

**What is established.** Effects have the Gleason-type representation, proved without axioms
(`effect_gleason_representation`, [`LF2/EffectGleason.lean`](../CsdLean4/LF2/EffectGleason.lean)). General
conditioning and its sharp special case are theorems on the model (`conditionalUpdate_capstone`,
[`SigmaLayer/ConditionalUpdate.lean`](../CsdLean4/SigmaLayer/ConditionalUpdate.lean); `luders_capstone`,
[`SigmaLayer/Luders.lean`](../CsdLean4/SigmaLayer/Luders.lean)), as are mixed states
(`mixedState_capstone`, [`SigmaLayer/MixedState.lean`](../CsdLean4/SigmaLayer/MixedState.lean)) and POVMs by
dilation (`povm_born_frequency_volume_canonical`,
[`LF4/TrialWitness.lean`](../CsdLean4/LF4/TrialWitness.lean)). Two-path interference is derived, not
postulated (`HasBornInterference`, [`SigmaLayer/Interference.lean`](../CsdLean4/SigmaLayer/Interference.lean)).
All eleven proved-on-the-model facts are assembled into one tiered record
(`unifiedFiniteQMClosure`, [`SigmaLayer/FiniteQMClosure.lean`](../CsdLean4/SigmaLayer/FiniteQMClosure.lean)),
each field discharged by its source lemma and none by a placeholder.

**The seam.** None beyond links 1 to 3. The honest qualifier is the closure's own: it is a consistency
witness of the Paper C architecture, not a derivation of it, because the witness model has the measure and
the unitary built in. [`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §1 says this in
its first paragraph and this page repeats it.

**What is not claimed.** That reproducing the quantum calculation engine is the goal. It is the floor.

## 5. Measurement as records

**What is established.** A measurement context fixes a partition of the arena into basins, and the
partition mentions no preparation: the basin is the apparatus's and the preparation only picks the point.
The probability of a basin is the Born weight at every `N` (`globalBasin_born`,
[`RecordLayer/GlobalBasin.lean`](../CsdLean4/RecordLayer/GlobalBasin.lean)), with the closure
`GlobalRecordClosure` on the full arena. A constructed de-isolation propagator, the shear, pushes the ready
preparation forward to the Born distribution by dynamics rather than by assumption
(`shearDeIsolation_born`, [`RecordLayer/ShearDeIsolation.lean`](../CsdLean4/RecordLayer/ShearDeIsolation.lean)).
Almost every microstate yields exactly one outcome (`vnDeisolationModel_ae_total`,
[`SigmaLayer/LiftedMeasurement.lean`](../CsdLean4/SigmaLayer/LiftedMeasurement.lean)). The structural lesson
of [`specs/sigma-fibre-contextuality.md`](../specs/sigma-fibre-contextuality.md) belongs here: Born is a
typicality volume at every `N`, but where contextuality lives in `Σ` is dimension-dependent, in the base
only for a qubit and necessarily in the fibre from three levels up.

**The seam.** Three different things, and the ledger keeps them apart. Posit 1, the cell law: that a
context's rates generate its pointer torus. Its discharge condition is known, to derive `IsTorusGenerated`
([`RecordLayer/CellLawForced.lean`](../CsdLean4/RecordLayer/CellLawForced.lean)) from the de-isolation
dynamics, and it is not a Lean-shaped task. This is *the* open foundations item of the whole chain.
`R-015`: which interaction Hamiltonian a given apparatus realises is a modelling input, a permanent
boundary that no interpretation removes. `R-016`: the arena-level statement that the shear propagator is
the flow of a stated interaction Hamiltonian is open mathematics with a concrete Lean shape. Posit 5, the
calibrated bank, is the apparatus preparation and is stated as such.

**What is not claimed.** That the shear is derived. It is constructed, every required property is proved
of it, and the ledger calls it a witness. The base-only question at `N ≥ 3` is parked by author decision,
not refuted in general.

## 6. Composite systems

**What is established.** Composites do not factorise: the Segre embedding of a pair of rays into the joint
projective space is injective and, from two levels a side, not surjective (`segre_injective`,
`segre_not_surjective`, [`RecordLayer/OnticComposite.lean`](../CsdLean4/RecordLayer/OnticComposite.lean)).
Bell correlations exceed every local-hidden-variable table and stay under Tsirelson's bound
(`NoLocalHiddenVariableTable`, `HasTsirelsonSeparation` in
[`SigmaLayer/CompositeInterface.lean`](../CsdLean4/SigmaLayer/CompositeInterface.lean);
`bell_general_separation`, `lhv_chsh_le_two`, `qm_chsh_le_tsirelson` in
[`SigmaLayer/BellGenerality.lean`](../CsdLean4/SigmaLayer/BellGenerality.lean)). No signalling holds on the
operator side (`tensorSector_no_signalling`,
[`SigmaLayer/TensorSector.lean`](../CsdLean4/SigmaLayer/TensorSector.lean)). No non-contextual valuation
exists, for the Mermin–Peres square and in the general Kochen–Specker form (`no_lhv_mermin_peres`,
`general_ks_noNonContextualValuation`). On the record side, a local context's record weights are the reduced
state's Born weights even for entangled preparations (`entangled_local_record_born`,
[`RecordLayer/EntangledRecord.lean`](../CsdLean4/RecordLayer/EntangledRecord.lean)), and the Bell ray's
reduced state is the equal mixture (`reducedDM_bell`,
[`CV/EntangledWeights.lean`](../CsdLean4/CV/EntangledWeights.lean)).

**The seam.** Posit 7, local tomography, which is how the tensor product enters. It is `R-017`, a permanent
boundary: a composite carrying commuting local algebras need not be locally tomographic, and the
ledger names the two failure faces. Posit 8, measurement independence, is shared with every deterministic
theory and backed by nothing short of assuming it. The corpus is contextual and non-local by construction,
so the no-go theorems constrain the ontology rather than threaten it.

**What is not claimed.** A locality mechanism. The programme's conjecture `C-1`
([`specs/POSITS.md`](../specs/POSITS.md)) is that the correlations are local in `Σ` and nonlocal only in an
emergent spacetime. In the corpus's own terms: bounded influence and non-signalling correlations across an
assumed tensor cut are theorems, and the conjecture is that the cut is itself emergent
([`specs/records-to-spacetime-scoping.md`](../specs/records-to-spacetime-scoping.md)). Nothing here
establishes it.

## 7. Density operators, channels, entropy

**What is established.** This is the W-series of [`specs/qit-chain-scoping.md`](../specs/qit-chain-scoping.md),
complete on its critical path. A preparation on `Σ` has a density operator
(`preparationDensity`, [`LF2/PreparationQdensity.lean`](../CsdLean4/LF2/PreparationQdensity.lean)), which
is the barycentre of its projective law (`preparationDensity_eq_barycenter`,
[`LF2/PreparationBarycenter.lean`](../CsdLean4/LF2/PreparationBarycenter.lean)). When the ontic flow lifts a
unitary, the flowed preparation's density operator is the conjugated one, and on a joint sector the reduced
flowed state is the Stinespring channel of that unitary (`barycenter_flow`, `traceRight_barycenter_flow`,
[`LF2/FlowChannel.lean`](../CsdLean4/LF2/FlowChannel.lean)). The de-isolation channel is the environment
marginal of the measurement flow, and it is the pinching that the second law coarse-grains by
(`deisolationChannel_apply_eq_pinch`), so the second law, data processing and Landauer's bound hold on `Σ`
(`vonNeumannEntropy_le_deisolation`, `landauer_flow`,
[`Thermo/SigmaSecondLaw.lean`](../CsdLean4/Thermo/SigmaSecondLaw.lean)). The single-letter Holevo capacity
of the de-isolation channel is one classical bit (`deisolationChannel_holevoCapacity`,
[`LF6/DeisolationCapacity.lean`](../CsdLean4/LF6/DeisolationCapacity.lean)).

**The seam.** None new. Strong subadditivity is not proved in this corpus; it is read in from Physlib by a
separate bridge package that depends on both libraries by pinned revision, and that package is outside this
repository by design. Everything else in this link is foundational-triple here.

**What is not claimed.** That the quantum-information layer is CSD-specific. Every theorem under
`Mathlib/QuantumInfo/` is stated on bare matrices; what this link adds is that CSD preparations and flows
instantiate them.

## 8. Gates

**What is established.** Each standard gate is realised as the isometry of a `Σ`-sector bundle at every
base point: Hadamard, the phase gates `S` and `T`, and CNOT (`hadamard_realisable_cpSector`,
`phaseS_realisable_cpSector`, `phaseT_realisable_cpSector`,
[`Empirical/CSD/Gates/SingleQubitDischarge.lean`](../CsdLean4/Empirical/CSD/Gates/SingleQubitDischarge.lean);
`cnot_realisable_cpSector`,
[`Empirical/CSD/Gates/TwoQubitDischarge.lean`](../CsdLean4/Empirical/CSD/Gates/TwoQubitDischarge.lean)).
More generally a projective unitary action lifts to a `Σ`-flow with no hypothesis
(`isUnitaryLift_of_smul`, [`LF2/FlowChannel.lean`](../CsdLean4/LF2/FlowChannel.lean)), through a measurable
unit section of the projective space. A gate is therefore a flow on the arena and a circuit is a composed
flow. The QM-side gate algebra is in [`Empirical/QM/Gates/`](../CsdLean4/Empirical/QM/Gates/).

**The seam.** None new. A gate is a unitary, so Posit 6 is the only posit involved.

**What is not claimed.** That a gate's Hamiltonian is derived from an apparatus. The flow is the time-one
map of the projective action, and `R-015` applies to gates as it applies to measurements.

## 9. Algorithms

**What is established.** On the QM side, in [`Empirical/QM/Algorithms/`](../CsdLean4/Empirical/QM/Algorithms/):
Deutsch–Jozsa decides balanced from constant in one query (`deutsch_jozsa_balanced`,
`deutsch_jozsa_constant`), Bernstein–Vazirani reads the hidden string with certainty (`bv_certain`), Simon's
measurement outcomes are orthogonal to the hidden period and uniform on that subspace (`simon_orthogonal`,
`simon_uniform`), Grover's iterate succeeds with the stated amplitude and with certainty at the right count
(`grover_success`, `grover_certain`, `grover_multi_success`), the quantum Fourier transform is unitary
(`qft_unitary`), Shor's order-finding distribution and phase-estimation bound hold and a random base yields
a factor with the stated probability (`shor_order_distribution`, `shor_phase_estimation_lower_bound`,
`shor_random_a_yields_factor`, `shor_factor_prob_ge`), and teleportation recovers the input on every branch
(`teleportation_branch_recovers_input`). The amplitude-amplification core is Category 1
(`qsearch_average`, [`Mathlib/QuantumInfo/AmplitudeAmplification.lean`](../CsdLean4/Mathlib/QuantumInfo/AmplitudeAmplification.lean)).

**The seam.** Grover and Shor now have `Σ`-flow twins: a circuit is the projective action of its unitary on
the register's sector, the flow lifts the unitary with no hypothesis, `k` runs are the flow iterated, and the
readout is the record basin of the outcome (`Circuit.epistemicMeasure_globalBasin_flow_iterate`,
[`Empirical/CSD/Algorithms/CircuitFlow.lean`](../CsdLean4/Empirical/CSD/Algorithms/CircuitFlow.lean)); Grover's
success probability and Shor's order distribution are read off the basins at the flowed ready point
(`grover_flow_born`, `shor_flow_born_count`). The twins add the ontic reading, not new analysis: the QM-side
theorems carry the mathematics, and the other algorithms are still QM-side only. One residue is open mathematics:
`R-002`, the exponential-doubling schedule for unknown amplitude; the straddling-kernel bound behind the literal
amplitude-estimation constant (`R-001`) is proved (`amplitude_estimation_bhmt`, BHMT Theorem 11 with its `8/π²`). The interference picture most readers bring, Feynman's
sum over paths, is a theorem at finite dimension: the matrix element of a propagator is the limit of sums
over discrete paths of products of one-step amplitudes (`exp_add_apply_tendsto_sum_pathWeight`,
[`Mathlib/Analysis/Matrix/SumOverPaths.lean`](../CsdLean4/Mathlib/Analysis/Matrix/SumOverPaths.lean)), read
off the Lie–Trotter formula through the path expansion of a matrix power. In the continuum the Euclidean path
integral is a Wiener integral, as a theorem: for a Brownian motion in `ℝᵈ` with continuous paths and a bounded
potential,
`(e^{−t(H₀+V)} f)(x) = E[exp(−∫₀ᵗ V(x+B_s) ds) f(x+B_t)]` almost everywhere (`feynmanKac`,
[`Mathlib/Probability/FeynmanKac.lean`](../CsdLean4/Mathlib/Probability/FeynmanKac.lean)), with the propagator
defined by the Dyson series around the heat semigroup and reached equally by the Trotter product formula. In real
time the same construction gives Nelson's limit, `(e^{−i(t/n)H₀} e^{−i(t/n)V})ⁿ ψ → e^{−it(H₀+V)} ψ` in `L²(ℝᵈ)`,
with `e^{−itH₀}` the Fourier multiplier `e^{−2π²it‖ξ‖²}` and the propagator unitary (`nelson_freeSchrodinger`,
`exists_linearIsometryEquiv_schrodinger`,
[`Mathlib/Analysis/Semigroup/SchrodingerGroup.lean`](../CsdLean4/Mathlib/Analysis/Semigroup/SchrodingerGroup.lean)):
the real-time path integral is the strong limit of time-sliced products, which is what `∫𝒟x e^{iS}` means; on
Schwartz data the orbit solves the free Schrödinger equation `i ∂_t ψ = −½ Δ ψ` in `L²`
(`hasDerivAt_freeSchrodinger`, `kineticOp_eq_laplacian`), and the free Gaussian packet spreads as the
textbook says, `U₀(t) g_a = (1 + 2πiat)^{−1/2} g_{a/(1 + 2πiat)}` (`freeSchrodingerS_gaussianS`,
[`Mathlib/Analysis/Semigroup/GaussianPacket.lean`](../CsdLean4/Mathlib/Analysis/Semigroup/GaussianPacket.lean)).

**What is not claimed.** Any complexity-theoretic statement. The theorems are about amplitudes and
probabilities of specific circuits.

## 10. Error correction

**What is established.** Error correction on `Σ`, end to end, for the three-qubit code: the bit-flip channel
is the environment marginal of a concrete `Σ`-flow (`bitFlipFlow_traceRight_barycenter`), the four error
regions of `Σ` are disjoint and the syndrome projection fixes each (`syndromeProj_fixes_errorRegion`,
[`Empirical/CSD/QEC/ThreeQubit.lean`](../CsdLean4/Empirical/CSD/QEC/ThreeQubit.lean)); on the whole register
the single-error channel is the environment marginal of the joint flow and the syndrome-conditioned recovery
returns the register's density operator (`registerFlow_traceRight_barycenter`, `registerFlow_recovery`,
[`Empirical/CSD/QEC/RegisterFlow.lean`](../CsdLean4/Empirical/CSD/QEC/RegisterFlow.lean)). On the QM side,
Shor's nine-qubit code corrects single `X`, `Z` and `XZ` errors (`shor_corrects_X`,
`shor_corrects_Z_degenerate`, `shor_corrects_XZ`,
[`Empirical/QM/QEC/ShorNine.lean`](../CsdLean4/Empirical/QM/QEC/ShorNine.lean)), the Steane code's syndrome
separates single errors (`steane_syndrome_single_injective`,
[`Empirical/QM/QEC/Steane.lean`](../CsdLean4/Empirical/QM/QEC/Steane.lean)), and the stabiliser formalism
gives the code-space dimension and uniqueness (`stabState_unique`,
[`Mathlib/QuantumInfo/Stabilizer.lean`](../CsdLean4/Mathlib/QuantumInfo/Stabilizer.lean)). The general
criterion for active correction is a theorem (2026-09-21): a family of errors on a code is correctable —
some channel undoes every error on every code state — if and only if it satisfies the Knill–Laflamme
condition `P Eᵢᴴ Eⱼ P = cᵢⱼ P`, with the recovery channel constructed from the condition
(`exists_recovery_of_knillLaflamme`, `knillLaflamme_of_recovery`, `knillLaflamme_iff`,
[`Mathlib/QuantumInfo/KnillLaflamme.lean`](../CsdLean4/Mathlib/QuantumInfo/KnillLaflamme.lean)). On a
stabiliser code a Pauli error family whose pairwise products are detected satisfies the condition with
`c = 1` (`stabMat_knillLaflamme`,
[`Mathlib/QuantumInfo/StabilizerRecovery.lean`](../CsdLean4/Mathlib/QuantumInfo/StabilizerRecovery.lean)),
and **the Steane code corrects every single-qubit Pauli error**: one recovery channel undoes each of the
twenty-two errors on every code state, and on the density operator of an encoded qubit
(`exists_steane_recovery`, `steane_recovery_logical`,
[`Empirical/QM/QEC/SteaneRecovery.lean`](../CsdLean4/Empirical/QM/QEC/SteaneRecovery.lean)).

**The seam.** Four residues, all open mathematics with a Lean shape. `R-003`: any fault-tolerance claim;
the code space, the distance mechanism, the Knill–Laflamme theorem and the Steane recovery are landed
(the code-capacity threshold is BACKLOG #51; the `Σ`-twin of the Steane recovery is #53). `R-004`, `R-005`, `R-006`: magic-state distillation, the density of
Clifford+T in the unitary group, and `T`-gate injection; what exists is the `T` gate itself and the fact
that it is not Clifford (`tGate_conj_X_not_pauli`,
[`Mathlib/QuantumInfo/Magic.lean`](../CsdLean4/Mathlib/QuantumInfo/Magic.lean)). The three-qubit `Σ` model
corrects the single-flip channel exactly and, under independent bit-flip noise, returns
`(1 − p_fail) σ + p_fail X̄ σ X̄` with `p_fail = 3p² − 2p³` (`indepFlow_recovery`,
[`Empirical/CSD/QEC/IndependentNoiseFlow.lean`](../CsdLean4/Empirical/CSD/QEC/IndependentNoiseFlow.lean)):
the double and triple flips are modelled, and mis-corrected into the logical flip — the residual a
threshold argument (#51) would have to drive down.

**What is not claimed.** A threshold theorem, or that a fault-tolerant machine follows from the chain.

## 11. Arithmetic and resource counts

**What is established.** The reversible arithmetic a Shor-style machine runs on is verified circuit by
circuit: the carry-clean modular adder (`cuccaroModAdd_clean`,
[`Mathlib/QuantumInfo/Reversible/CuccaroModAdd.lean`](../CsdLean4/Mathlib/QuantumInfo/Reversible/CuccaroModAdd.lean)),
the general Horner multiplication loop (`mulLoop_correct`,
[`Mathlib/QuantumInfo/Reversible/ModularMulLoop.lean`](../CsdLean4/Mathlib/QuantumInfo/Reversible/ModularMulLoop.lean)),
and the Boolean-to-amplitude lift of a gate (`andUncompMat_lifts_denote`,
[`Mathlib/QuantumInfo/Reversible/Lift.lean`](../CsdLean4/Mathlib/QuantumInfo/Reversible/Lift.lean)). The
measurement-gadget adders in [`Empirical/QM/`](../CsdLean4/Empirical/QM/) re-cost the arithmetic with
mid-circuit measurement. The elliptic-curve harness that turned these into machine sizes lives in a separate
repository by design, with a one-way dependency on this one.

**The seam.** `R-013`, open mathematics: the `n`-fold hybrid amplitude equality that threads the
non-permutation gadget through every block of the adder; the single-block embedding is proved and the tensor
interface exists. Backlog row 17 holds the general lift and the documentation de-application that came with
the harness split.

**What is not claimed.** Average-case costs. The corpus's counts are worst-case gate counts; the harness's
metric is executed Toffolis times peak qubits, and the two are not the same number.

## The four kinds of seam, and where each is tracked

* **Permanent boundaries** never close and are not gaps: `R-015`, which interaction an apparatus realises,
  and `R-017`, local tomography. The work is to state them, which the ledgers do.
* **Design posits** are choices the reconstruction makes and defends: Posits 2, 3, 4, 6, 8 and 9. The work
  is to keep them visible, which [`specs/POSITS.md`](../specs/POSITS.md) does, and to constrain them from
  above where a theorem can (Posit 2 and the base half of Posit 9 are now forced by symmetry).
* **Open mathematics** has a Lean shape and no proof yet: `R-016`, `R-002` to `R-006`, `R-013`, and the
  `Σ`-twins of the algorithms. Each is a numbered row of [`specs/BACKLOG.md`](../specs/BACKLOG.md).
* **Open foundations** is one item: Posit 1's discharge, the cell law from the de-isolation dynamics. It is
  the reconstruction frontier, and the ledgers say it is not a brick.

So the chain from the postulates to a working machine's parts is continuous, with a theorem behind every
link, and the only research seam in it is the cell law. What the chain does not yet contain is a
fault-tolerant machine.
