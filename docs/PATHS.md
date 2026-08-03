# Reading paths, by quantum sector

*(Each path is an ordered list of stops — file, then why it's next. Start anywhere; each sector
is self-contained. The reader-type paths (physicist / Lean reader / skeptic) are in
[`TOUR.md`](TOUR.md). Every stop's module header carries its own ⚠️ honest-scope block.)*

## 1 · Foundations & ontology — what is Σ, and what is assumed?

1. [`specs/CSD-CHARTER.md`](../specs/CSD-CHARTER.md) — Σ is the floor; QM arises from the
   epistemic Ω-partition + the ontic typicality volume. The anti-drift frame.
2. [`AXIOMS.md`](../AXIOMS.md) §3 — the posits, as posits: substrate, sector, typicality
   reading, apparatus calibration (§3.8).
3. `CsdLean4/LF4/KahlerInstance.lean`, `LF4/MomentMap.lean` — `Σ = ℂℙ^{N-1} × T²`, `μL`,
   the torus moment map (where the Born weight lives geometrically).
4. `CsdLean4/SigmaLayer/SectorPostulateNoGo.lean` — why "derive Σ from a single flow" is
   provably not available (the SO-1 no-go).
5. [`specs/sigma-fibre-contextuality.md`](../specs/sigma-fibre-contextuality.md) — the
   structural lesson: for `N ≥ 3`, contextuality necessarily lives in Σ's *fibre*. The open
   foundations frontier.
6. [`specs/reconstruction-status.md`](../specs/reconstruction-status.md) §2a — the A1–A7
   audit, row by row.

## 2 · Dynamics — the Schrödinger pillar

1. `CsdLean4/LF4/KahlerOnticSetup.lean` — the sector interface: compact Σ, Liouville measure,
   deterministic measure-preserving flow, descent to rays.
2. `CsdLean4/Mathlib/LinearAlgebra/Projectivization/{WignerRigidity, Bargmann,
   PhaseRigidity}.lean` — Wigner rigidity, the Bargmann discriminator (unitary branch
   selection), the `U(1)` phase lift.
3. `CsdLean4/Mathlib/Analysis/Matrix/StoneC1.lean` — the finite-dimensional C¹ Stone theorem
   (Mathlib has none).
4. `CsdLean4/LF4/PhaseLift.lean` — the capstone `projectedFlow_schrodinger_form`: the
   projected flow is `exp(-itH)`-conjugation on rays.
5. `CsdLean4/LF4/NonTrivialSetup.lean` — the genuine `Φ ≠ id` instantiation for arbitrary
   Hermitian `H`; `manyToOneSchrodingerSetup_both_pillars` puts Schrödinger and Born on one
   object.

## 3 · Born & measurement — the record layer and the dynamical arc

1. `CsdLean4/LF4/…` (Born-from-volume cluster) — `momentMap_mk_eq_inner_sq`,
   `fs_born_volume_ratio_N`, POVMs via `canonicalNaimark`.
2. `CsdLean4/SigmaLayer/GlobalBasin.lean` — context-fixed basins: the partition is the
   apparatus's, the preparation only picks the point (`globalBasin_born`).
3. `CsdLean4/SigmaLayer/MeasurementConstraints.lean` — the no-gos that shaped everything:
   forced seams, no exact collapse, the accuracy price.
4. `CsdLean4/SigmaLayer/{ShearWitness, SwapWitness, SwapLuders, SwapClosure}.lean` — records
   created → collapse as relocation → rank-one Lüders → the six-fact closure.
5. `CsdLean4/SigmaLayer/{DegenerateLuders, BlockCollapse, PhaseSlot, JoinArena, JoinProtocol,
   JoinLuders}.lean` — the degenerate arc: no-go → wall → the projective join →
   `BlockLudersObligation` inhabited.
6. `CsdLean4/SigmaLayer/{RotatedContext, RotatedSwap}.lean` — any-basis follow-ups and the
   unitary-covariance law (`measurement_covariance`).
7. `CsdLean4/SigmaLayer/UnifiedArena.lean` — one arena, one Liouville measure family; the
   round trip.
8. `CsdLean4/SigmaLayer/{ShearDiscontinuity, PiecewiseHamiltonian}.lean` — what kind of
   dynamics this provably is.
9. `CsdLean4/SigmaLayer/{PointerArena, PointerRotation, PointerCoupling, PointerWeights,
   PointerLanding, PointerProtocol, PointerBorn, PointerGeneration}.lean` — the smooth horn:
   a projective pointer, a Hermitian coupling, a Schrödinger-generated propagator continuous
   in time and state, and Born up to a stated `ε` (`smoothWitnessClosure`,
   `rampedU_schrodinger`).

## 4 · Entanglement & non-locality

1. `CsdLean4/LF3/…` — the singlet chain and the kernel `P_st`.
2. `CsdLean4/LF6/ForcedContextuality.lean` — `no_product_partition_realises_singlet`:
   non-factorisation is Bell-forced, not posited.
3. `CsdLean4/LF6/{SingletDeisolationFlow, GHZ…, CGLMPQudit}.lean` — genuine de-isolation
   flows; CGLMP violation for every `d`; GHZ/Mermin for every `n`; no-signalling.
4. `CsdLean4/SigmaLayer/{OnticComposite, OnticMarginals}.lean` — the Segre embedding (Bell
   witness), ontic reduction maps, local-flow marginal stability.
5. `CsdLean4/Empirical/QM/{Bell, Hardy, …}.lean` + the CSD volume twins — the empirical face.

## 5 · Quantum information & channels

1. `CsdLean4/Mathlib/QuantumInfo/{Entropy, Subadditivity, StrongSubadditivity}.lean` — von
   Neumann entropy, Klein, subadditivity, Araki–Lieb; SSA conditional on DPI (the recorded
   operator-convexity wall — see [`MATHLIB-GAPS.md`](../MATHLIB-GAPS.md)).
2. `CsdLean4/Mathlib/QuantumInfo/{Channel, TraceDistance, PartialTrace, Helstrom}.lean` —
   CPTP/Kraus/Stinespring, the trace-distance metric with data processing, partial trace,
   minimum-error discrimination.
3. `CsdLean4/Empirical/QM/{NoCloning, NoBroadcasting, NoDeleting, NoCommunication, USD}.lean`
   — the no-go suite and state discrimination.
4. `CsdLean4/Empirical/Resources/…` — teleportation, superdense coding.
5. `REFERENCES.json` — the Lean-QIT cross-reference (cited, not imported).

## 6 · Cryptography

1. `CsdLean4/Empirical/QM/Crypto/{E91, E91KeyRate, E91FiniteKey}.lean` — device-independent
   security from the CHSH bound; asymptotic key rate; finite-sample concentration.
2. `CsdLean4/Empirical/QM/Crypto/{BB84, B92, QuantumMoney, WiesnerProtocol}.lean` — the
   intercept-resend QBER, two-state QKD, unforgeability.
3. `CsdLean4/Empirical/CSD/Crypto/{BB84Sequential, B92Sequential, WiesnerSequential}.lean` —
   the **dynamical** twins: Eve's collapse as a pushforward theorem, false conclusive clicks,
   the ¾ counterfeit value — both BB84 rounds run natively (primal via the covariance law).

## 7 · Algorithms

1. `CsdLean4/Mathlib/QuantumInfo/Register.lean` — the n-qubit register.
2. `CsdLean4/Empirical/QM/Algorithms/…` — Deutsch–Jozsa, QFT, Grover.
3. `Shor{Core, Recovery, RandomA, Capstone}.lean` — the full Shor chain, machine-checked end
   to end (random-`a` success ≥ ½ for arbitrary odd composites).

## 8 · Thermodynamics

1. `CsdLean4/Thermo/CanonicalTypicality.lean` — TH1: thermal equilibrium as an FS-typicality
   expectation (`fs_first_moment`).
2. `CsdLean4/Thermo/SecondLaw.lean` — TH2: the H-theorem via Klein's inequality; entropy from
   coarse-graining, not from the reversible step.
3. `CsdLean4/Thermo/FreeEnergy.lean` — TH3: the Gibbs variational principle.
4. `CsdLean4/Thermo/Landauer.lean` — TH4: `kT ln 2`, the Reeb–Wolf bound.
