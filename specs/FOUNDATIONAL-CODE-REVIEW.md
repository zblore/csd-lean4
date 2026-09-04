# Foundational code review ledger

Review date: 2026-08-06  
Repository reviewed: `C:\Zayn\csd\lean4`  
Status: complete file-level source review; build verification blocked by unavailable network/toolchain cache

## Scope and standard

This is a source, statement, dependency, and API review of the foundational CSD proof spine. It is
not a claim that every tactic step has been independently re-proved by hand. Lean compilation and an
axiom-clean result are necessary but not sufficient: the review also checks mathematical meaning,
non-vacuity, hidden assumptions, dependency direction, claim alignment, public API, and audit coverage.

Verdicts:

- **Pass** — no material problem found for the file's stated role.
- **Pass with notes** — coherent, with a qualification or maintainability issue.
- **Needs change** — concrete statement, dependency, API, coverage, or claim-alignment issue.
- **Needs domain validation** — formally coherent construction whose physical interpretation needs
  independent subject-matter judgment.

Severity:

- **S0** no issue; **S1** local presentation; **S2** architecture/API/testing;
  **S3** theorem meaning, hidden assumption, vacuity, or scientific claim risk;
  **S4** confirmed mathematical unsoundness or build-breaking defect.

## Cross-cutting findings

### F-01 — LF2's measure bridge is phantom in the Born construction (S3)

`OperationalPackage.fromPreparation` accepts `bridge : MeasureBridgeData D μFS`, but deliberately
uses none of its fields. The same is true of the direct pure-state Born theorem. The conclusion can be
proved after deleting the bridge argument. Consequently the claim that symmetry or the pushforward
bridge is load-bearing in this LF2 route is not supported by the term dependency.

Recommended action: remove the unused argument from the construction, or state and prove a theorem in
which `bridge_eq` genuinely transports an ontic volume computation into the projective probability.

### F-02 — `effectProjFn` defines the quantum probability integrand (S3)

`effectProjFn rep E p` is defined as `Re(v†Ev)`. For rank-one effects the Born quadratic form is
therefore true by expansion, and the pure-preparation theorem integrates this already-Born function
against a Dirac pushforward. This is a valid representation/consistency theorem, but not a derivation
of the Born functional from volume or symmetry.

Recommended action: call this the quadratic-form representation layer. Reserve “Born from volume” for
the LF4 theorem where a separately specified measurable region has its measure computed.

### F-03 — LF4 Born regions depend on the preparation (S3)

The barycentric regions are constructed from the preparation's moment/Born vector, and
`bornRegion ψ ... i` contains `ψ` in its definition. Their volumes correctly equal the corresponding
coordinates, but these are not context-fixed apparatus outcome regions. Later fibre/context modules
address this separately; the foundational Born-frequency theorem itself remains preparation-indexed.

Recommended action: keep this result labelled as a preparation-indexed geometric realization and make
the context-fixed theorem the public measurement-facing API.

### F-04 — `KahlerOnticSetup` does not enforce a Kähler structure (S3)

The Kähler and Liouville-volume requirements are represented by arbitrary `Prop` fields paired with
proofs. An inhabitant may choose `True`; the structure itself expresses no closed two-form, complex
compatibility, non-degeneracy, or top exterior power. Concrete witnesses use stronger propositions,
but consumers quantified over `KahlerOnticSetup` cannot infer them.

Recommended action: rename the current interface to `ProjectiveMeasureFlowSetup`, or replace the
placeholder pairs with a concrete partial Kähler interface containing exactly the formalized laws.

### F-05 — Lüders behavior is supplied by calibrated storage (S3)

The swap witness obtains the post-measurement state by swapping the system with bank slot `i`, whose
measure is supplied as `ν i`; the CSD specialization calibrates that slot to the desired vertex state.
The degenerate join construction follows the same engineered-relocation pattern. This is a valid
measure-preserving realization and explains information storage, but the Lüders map is encoded in the
apparatus calibration rather than forced by record creation alone.

Recommended action: state a minimal calibration theorem identifying exactly which apparatus hypotheses
are equivalent to Lüders behavior, and avoid describing the update as assumption-free.

### F-06 — capstones bundle heterogeneous or incomplete notions of closure (S3)

`ProjectiveMeasurementCapstone` explicitly combines different witnesses. `FiniteQMClosure` bundles an
older eleven-field product-witness result but does not contain the later POVM-sector, smooth-pointer,
general channel, or full sequential-measurement APIs associated with “operational finite QM”. These
records are useful indices, but their names can be read as stronger unification claims than their types.

Recommended action: rename them as witness/feature indices, or introduce a genuinely unified closure
whose fields share a single arena, preparation protocol, dynamics, and measurement interface.

### F-07 — package roots and layers have drifted (S2)

The default `CsdLean4` root misses 34 non-test modules, although the test roots collectively reach all
files. The graph is acyclic but has 16 reverse-layer imports, including LF2→SigmaLayer and several
LF4/LF5/LF6→Empirical edges.

Recommended action: generate per-layer aggregate modules, derive both public and audit roots from them,
and move generic empirical lemmas down to their natural layer.

## File ledger

| Area | File | Verdict | Severity | Review note |
|---|---|---|---:|---|
| LF1 | `LF1/Setup.lean` | Pass with notes | S2 | Clear abstract measure-flow interface. Full measure preservation is structural payload; only measurability is used in LF1–LF3. |
| LF1 | `LF1/Preparation.lean` | Pass | S0 | Normalized restricted finite measure is stated and factored cleanly; nonzero denominator is explicit. |
| LF1 | `LF1/Trials.lean` | Pass with notes | S1 | Common marginal law is structural; independence is intentionally deferred. This models repeated fresh preparations, not one deterministic trajectory. |
| LF1 | `LF1/Convergence.lean` | Pass | S0 | Standard strong-law application with integrability and identical distribution discharged and indicator independence explicit. |
| LF1 | `LF1/GeneralFrequency.lean` | Pass with notes | S2 | The theorem needs pairwise independence only for the chosen indicator process, not independence of the `Σ`-valued trials. “i.i.d.” is stronger prose than the formal hypothesis. |
| LF1 | `LF1/MainTheorem.lean` | Pass with notes | S1 | Thin, honest capstone over the SLLN. It proves a single-region result; finite-partition simultaneity remains prose but is routine. |
| LF2 | `LF2/Setup.lean` | Pass with notes | S2 | `SectorData` is intentionally permissive and posits the projection/action. The name should not imply selection of a quantum sector. |
| LF2 | `LF2/MeasureBridge.lean` | Pass | S0 | Pushforward invariance follows correctly from equivariance and invariant ontic measure. It does not itself prove uniqueness or the bridge equality. |
| LF2 | `LF2/Preparation.lean` | Needs change | S3 | See F-01 and F-02. `bridge` is unused; the pure theorem follows from Dirac concentration plus an already-quadratic integrand. |
| LF2 | `LF2/EffectFn.lean` | Needs change | S3 | Algebra, bounds, measurability and integrability are coherent, but “volume-ratio foundational object” overstates a definition equal to `Re(v†Ev)`. |
| LF2 | `LF2/BornWrapper.lean` | Pass with notes | S2 | Effect/density structures and rank-one trace calculation are standard. Operational covariance is deliberately omitted; the package is not the full stated operational axiom system. |
| LF2 | `LF2/EffectGleason.lean` | Pass with notes | S2 | The representation statement is meaningful and the proof arc is mathematically plausible: bounded additivity→homogeneity→quadratic form→polarization→density. At ~1,400 lines it needs a separate specialist proof/API pass before Mathlib-grade confidence. |
| LF2 | `LF2/POVM.lean` | Pass with notes | S2 | Completeness is proved, but the public API omits the elementary per-outcome theorem `0 ≤ weight`; therefore “probability vector” is not bundled as such. |
| LF2 | `LF2/QuantumChannel.lean` | Pass with notes | S2 | Kraus channels, trace preservation, Stinespring identity and Choi positivity are coherent. `cptp_capstone` itself states only positivity and trace one; complete positivity is by Kraus construction/Choi witness, not an amplified-map theorem. |
| LF4 | `LF4/KahlerOnticSetup.lean` | Needs change | S3 | See F-04. Honest documentation does not repair the weak type: arbitrary placeholder propositions do not encode Kähler geometry. |
| LF4 | `LF4/KahlerInstance.lean` | Pass with notes | S2 | Concrete product witness and marginal bridge are clear. Fubini–Study measure and torus fibre are chosen as input rather than dynamically forced. |
| LF4 | `LF4/MomentMap.lean` | Pass | S0 | Standard normalized coordinate moment map; nonnegativity, normalization and Born-coordinate identity are appropriately separated. |
| LF4 | `LF4/BornVolume.lean` | Pass with notes | S2 | Determinant/volume scaling is sound. The subdivision point is the Born/moment vector, so this is a geometric encoding of known barycentric coordinates, not selection of outcome regions from apparatus dynamics. |
| LF4 | `LF4/BornFS.lean` | Pass with notes | S1 | Qubit result correctly exposes its uniform-pushforward hypothesis; superseded by the general-N theorem where that law is proved. |
| LF4 | `LF4/MomentBornN.lean` | Pass with notes | S2 | Substantive general-N Fubini–Study/Dirichlet volume computation. Genericity restrictions are explicit and an unconditional companion is referenced. Interpretation remains subject to F-03. |
| LF4 | `LF4/BornFrequencyN.lean` | Needs change | S3 | Frequency theorem is valid for its events, but `bornRegion ψ ... i` is preparation-indexed and should not be the measurement-facing outcome-region API. |
| LF4 | `LF4/ProjectedDynamics.lean` | Pass with notes | S2 | Carefully distinguishes Wigner selection, ray-level group law and the converse exponential construction. Unitarity and group structure are hypotheses, not consequences of volume preservation. |
| LF4 | `LF4/PhaseLift.lean` | Pass with notes | S2 | Conditional theorem is clear: the coboundary and differentiability/generator equations are explicit inputs. It should not be summarized as unconditional recovery of Schrödinger dynamics. |
| LF4 | `LF4/ManyToOnePillars.lean` | Pass with notes | S3 | Both pillars coexist on one product witness, but the flow is defined using `exp(-itH)` and Born trials independently sample the chosen product measure. This is a consistency witness, not dynamical derivation. |
| LF4 | `LF4/ManyToOneSchrodingerDerived.lean` | Pass | S0 | Supplies the derivative calculation behind the exponential family and avoids leaving the `rfl` projection theorem entirely unsupported. |
| LF4 | `LF4/NonTrivialSetup.lean` | Pass with notes | S2 | Establishes non-identity examples, but the unitary family is an input. It validates inhabitation rather than deriving allowed dynamics. |
| Sigma | `SigmaLayer/FiniteQMClosure.lean` | Needs change | S3 | See F-06. Useful eleven-field witness record, but narrower than current “operational finite-QM closure” language and absent newer measurement/POVM/channel features. |
| Sigma | `RecordLayer/MeasurementConstraints.lean` | Pass | S0 | No-go statements expose measurability/measure-preservation and positive/null-set assumptions. The file avoids claiming witness existence. |
| Sigma | `RecordLayer/SwapWitness.lean` | Pass with notes | S2 | Explicit involutive, measure-preserving relocation witness with composition law. It is engineered and piecewise rather than continuous; documentation states this. |
| Sigma | `RecordLayer/SwapLuders.lean` | Needs domain validation | S3 | Pushforward calculation is coherent. Lüders state is supplied by the pre-calibrated bank slot; see F-05. |
| Sigma | `RecordLayer/JoinProtocol.lean` | Pass with notes | S2 | Explicit degenerate-record protocol with strong measure bookkeeping. The architecture is specialized and large, but assumptions are visible. |
| Sigma | `RecordLayer/JoinLuders.lean` | Needs domain validation | S3 | Nonzero-block conditioning and marginal calculation are substantive; the outcome-specific post-state is still implemented by calibrated relocation. |
| Sigma | `RecordLayer/PointerProtocol.lean` | Pass with notes | S2 | Continuous smooth-ramp record protocol is a genuine alternative witness. Correlation is restricted to its stated sectors and is approximate in Born assignment. |
| Sigma | `RecordLayer/PointerGeneration.lean` | Pass with notes | S3 | Correctly proves a fibrewise Schrödinger ODE for fixed weights. The base marginal is unchanged, so this is not a fully back-reacting joint Hamiltonian measurement flow. |
| Sigma | `RecordLayer/PointerLuders.lean` | Pass with notes | S2 | Defines the record-triggered relocation layer. Measure preservation and marginal results live downstream, making this file an implementation brick rather than a closure. |
| Sigma | `RecordLayer/PovmDynamics.lean` | Pass with notes | S3 | Naimark selector statistics and dilation-relative posts are coherent. The record dynamics starts at `[Vψ]`; it does not dynamically realize preparation of the dilation/ancilla state. |
| Sigma | `RecordLayer/PovmSectorBorn.lean` | Pass with notes | S2 | Correctly lifts selector Born to the join protocol's outcome sector. It remains dilation-relative and begins from the already-dilated preparation, as documented. |
| Sigma | `RecordLayer/MeasurementCapstone.lean` | Needs change | S3 | See F-06. It is an index of rank-one, rotated, degenerate and smooth witnesses, not one measurement model satisfying every field. It is also omitted from the default package root. |

## Build and audit status

- Static import graph: 443 source files, 1,177 internal edges, no cycles.
- All files are reachable from the union of declared library/test roots.
- The default consumer root omits 34 non-test files.
- Static scan found no syntactic `axiom`, `sorry`, or `admit` declarations in the reviewed corpus.
- `lake build CsdLean4` could not be executed in this environment because the pinned toolchain attempted
  a GitHub download and outbound network access was unavailable.
- The large `Tests/AxiomAudit.lean` imports the reviewed headline modules, but audit coverage should be
  split by layer and generated from the same module manifests as the public roots.

## Priority order

1. Correct the LF2 bridge/Born narrative and API (F-01/F-02).
2. Make preparation-indexed versus context-fixed outcome regions impossible to confuse (F-03).
3. Rename or strengthen `KahlerOnticSetup` (F-04).
4. State apparatus calibration as the precise source of Lüders relocation (F-05).
5. Narrow/rename the capstones or build a genuinely unified closure (F-06).
6. Repair generated roots and reverse imports (F-07).


## Full remaining-file review appendix

This appendix completes file-level coverage of the remaining Lean modules. Each row records a source/statement/API/dependency verdict; it is not a line-by-line re-derivation of every tactic proof. Large or mathematically deep files are explicitly marked for a specialist proof pass.

### Root

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `Basic.lean` | 29 | Pass | S0 | Minimal package smoke module. |

### CV

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `CV/ApproxCCR.lean` | 107 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/Dispersion.lean` | 220 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/FieldModes.lean` | 175 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/ModeLocality.lean` | 200 | Pass with notes | S3 | Commutation follows from the strong SupportedOn factorisation definition at finite cutoff; this models kinematic locality rather than deriving continuum Haag-Kastler locality. |
| `CV/Oscillator.lean` | 314 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/OscillatorBorn.lean` | 123 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/OscillatorSpectrum.lean` | 134 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |
| `CV/Position.lean` | 178 | Pass with notes | S2 | Finite-mode/cutoff construction is coherent; continuum/QFT interpretation is outside the proved type. |

### Empirical

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `Empirical/CSD/Bell.lean` | 288 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/BellVolume.lean` | 276 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/ChannelCapacity.lean` | 275 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Contextuality/KCBSVolume.lean` | 267 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Contextuality/KS18.lean` | 276 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Contextuality/KS18Volume.lean` | 253 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Contextuality/MerminPeres.lean` | 165 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Contextuality/MerminPeresVolume.lean` | 1221 | Pass with notes | S2 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/ContextVolume.lean` | 433 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Crypto/B92Sequential.lean` | 130 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Crypto/BB84Sequential.lean` | 310 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Crypto/E91.lean` | 110 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Crypto/QuantumMoney.lean` | 160 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Crypto/WiesnerSequential.lean` | 137 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/DoubleSlitVolume.lean` | 88 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Einselection.lean` | 489 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/ElitzurVaidmanVolume.lean` | 77 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/EraserDynamics.lean` | 338 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/EraserSequential.lean` | 154 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Framework.lean` | 123 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/BellPrep.lean` | 124 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/BellPrepDischarge.lean` | 79 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/Framework.lean` | 193 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/MultiQubit.lean` | 81 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/MultiQubitDischarge.lean` | 69 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/SingleQubit.lean` | 153 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/SingleQubitDischarge.lean` | 121 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/TwoQubit.lean` | 95 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/TwoQubitDischarge.lean` | 86 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Gates/WignerDischarge.lean` | 364 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/GHZVolume.lean` | 291 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Hardy.lean` | 189 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/HardyVolume.lean` | 236 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/HongOuMandelVolume.lean` | 155 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/LeggettGargVolume.lean` | 78 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/MachZehnderVolume.lean` | 112 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/MalusVolume.lean` | 141 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/MixedStateBornVolume.lean` | 86 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/MUB3Volume.lean` | 248 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Multipartite/GHZ.lean` | 314 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/NoBroadcasting.lean` | 114 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/NoCloning.lean` | 224 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/NoCommunication.lean` | 115 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/NoDeleting.lean` | 173 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/QEC/ThreeQubit.lean` | 138 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/QECDecoherence.lean` | 374 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/QuantumEraserVolume.lean` | 289 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/QuantumZeno.lean` | 285 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/QutritPOVMVolume.lean` | 189 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Resources/SuperdenseCoding.lean` | 173 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Resources/Teleportation.lean` | 116 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/SequentialMeasurement.lean` | 129 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/SIC3Volume.lean` | 247 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/SICVolume.lean` | 213 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/SternGerlach.lean` | 208 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/SternGerlachVolume.lean` | 192 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/TrineVolume.lean` | 170 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/Uncertainty.lean` | 175 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/UncertaintyVolume.lean` | 219 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/USDVolume.lean` | 115 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/VolumeCanonical.lean` | 456 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/CSD/WeakMeasurement.lean` | 415 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/Metrology/Heisenberg.lean` | 275 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/Metrology/QuantumFisher.lean` | 248 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/Metrology/Ramsey.lean` | 324 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/BernsteinVazirani.lean` | 158 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/DeutschJozsa.lean` | 135 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/Grover.lean` | 403 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/HadamardTest.lean` | 398 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/ShorCapstone.lean` | 152 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/ShorCore.lean` | 1218 | Pass with notes | S2 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/ShorRandomA.lean` | 1476 | Pass with notes | S2 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/ShorRecovery.lean` | 263 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/Simon.lean` | 203 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Algorithms/SwapTest.lean` | 206 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Bell.lean` | 628 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Contextuality/KS18.lean` | 388 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Contextuality/MerminPeres.lean` | 309 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/B92.lean` | 219 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/BB84.lean` | 305 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/E91.lean` | 206 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/E91FiniteKey.lean` | 209 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/E91KeyRate.lean` | 259 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/QuantumMoney.lean` | 145 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Crypto/WiesnerProtocol.lean` | 172 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/ElitzurVaidman.lean` | 97 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Gates/BellPrep.lean` | 198 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Gates/MultiQubit.lean` | 101 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Gates/SingleQubit.lean` | 113 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Gates/TwoQubit.lean` | 122 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Hardy.lean` | 516 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/HongOuMandel.lean` | 231 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/KCBS.lean` | 206 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/LeggettGarg.lean` | 160 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Malus.lean` | 109 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/MeasurementAdder.lean` | 307 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/MeasurementAdderHierarchy.lean` | 74 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/MeasurementGidneyAdder.lean` | 168 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/MeasurementUncompute.lean` | 395 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/MeasurementUncomputeLift.lean` | 282 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Multipartite/GHZ.lean` | 337 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/NoBroadcasting.lean` | 156 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/NoCloning.lean` | 170 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/NoCommunication.lean` | 180 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/NoDeleting.lean` | 161 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Protocols/Basic.lean` | 109 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QEC/BitFlipChannel.lean` | 81 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QEC/ErrorDiscretization.lean` | 212 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QEC/PhaseFlip.lean` | 235 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QEC/SyndromeCollapse.lean` | 254 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QEC/ThreeQubit.lean` | 309 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/QuantumEraser.lean` | 112 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Resources/SuperdenseCoding.lean` | 213 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Resources/Teleportation.lean` | 244 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/SternGerlach.lean` | 178 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/Uncertainty.lean` | 135 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |
| `Empirical/QM/USD.lean` | 255 | Pass with notes | S1 | Concrete finite-dimensional calculation/benchmark; useful validation, but not part of the foundational derivation and large files need targeted regression tests. |

### LF1

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF1/Expectation.lean` | 93 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF1/Indicators.lean` | 159 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF1/Outcomes.lean` | 103 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |

### LF2

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF2/ChoiConverse.lean` | 145 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/EffectAux.lean` | 101 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/Interface.lean` | 199 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/MixedEnsembleIx.lean` | 135 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/PhaseInvariance.lean` | 88 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/ReducedDensity.lean` | 93 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |
| `LF2/Weights.lean` | 110 | Pass with notes | S1 | Source, declarations, imports, and stated scope reviewed; no breaking defect or trust escape found. |

### LF3

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF3/ContextMap.lean` | 100 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Hamiltonian.lean` | 150 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Interface.lean` | 481 | Needs domain validation | S3 | The capstone is conditional on bundled preparation/sector hypotheses; valid composition, not an independent derivation of singlet statistics. |
| `LF3/Projectors/Core.lean` | 113 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Projectors/LF2Interface.lean` | 127 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Projectors/SectorVolume.lean` | 203 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Projectors/TensorModel.lean` | 343 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/PurePreparation.lean` | 255 | Needs domain validation | S3 | The capstone is conditional on bundled preparation/sector hypotheses; valid composition, not an independent derivation of singlet statistics. |
| `LF3/SectorSeparation.lean` | 242 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Setup.lean` | 279 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/Expectations.lean` | 169 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/JointEig.lean` | 134 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/JointProjector.lean` | 168 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/Kernel.lean` | 192 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/Leakage.lean` | 145 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/Singlet/State.lean` | 74 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |
| `LF3/SingletProjective.lean` | 213 | Pass with notes | S2 | Coherent conditional singlet/measurement interface; physical content is carried partly by explicit algebraic and preparation structures. |

### LF4

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF4/AxisBridge.lean` | 119 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BargmannSelection.lean` | 250 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BlochProjection.lean` | 119 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BornFlowLinkage.lean` | 142 | Pass with notes | S3 | Existence/consistency witness built from an explicitly chosen flow; it should not be read as forcing quantum dynamics. |
| `LF4/BornFrequencyPartition.lean` | 77 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BornRegionDisjoint.lean` | 359 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BornRegionUncond.lean` | 391 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/BothPillars.lean` | 129 | Pass with notes | S3 | Existence/consistency witness built from an explicitly chosen flow; it should not be read as forcing quantum dynamics. |
| `LF4/DuistermaatHeckman.lean` | 62 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/GaussianCP.lean` | 263 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/GaussianCPN.lean` | 276 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/GaussianFS.lean` | 80 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/HardyKahler.lean` | 569 | Pass with notes | S2 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/HatBox.lean` | 113 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/Instance.lean` | 110 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/KahlerFlow.lean` | 240 | Pass with notes | S3 | Existence/consistency witness built from an explicitly chosen flow; it should not be read as forcing quantum dynamics. |
| `LF4/KahlerVolumeForced.lean` | 142 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/KahlerWignerLift.lean` | 165 | Pass with notes | S3 | Existence/consistency witness built from an explicitly chosen flow; it should not be read as forcing quantum dynamics. |
| `LF4/MomentBridgeN.lean` | 91 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentDirichletN.lean` | 124 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentMarginal.lean` | 79 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentMarginalUniform.lean` | 303 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentPushforward.lean` | 75 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentRatioUniform.lean` | 241 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentRatioUniformN.lean` | 565 | Pass with notes | S2 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/MomentUniform.lean` | 244 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/ObservableCorrespondenceN.lean` | 382 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/ObservableFlow.lean` | 369 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/OnticBorn.lean` | 85 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/PauliDotRobertson.lean` | 181 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/PauliRobertson.lean` | 264 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/POVMDilation.lean` | 131 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/POVMNaimark.lean` | 168 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/POVMVolume.lean` | 196 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitBorn.lean` | 145 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitBornFrequency.lean` | 86 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitConsistency.lean` | 72 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitCrossTerm.lean` | 198 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitDipole.lean` | 255 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/QubitReflection.lean` | 116 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/RotationSchrodinger.lean` | 157 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SchrodingerKahlerInvariance.lean` | 90 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SingleQubitKahler.lean` | 312 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SingletKahler.lean` | 366 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SingletKahlerFlow.lean` | 231 | Pass with notes | S3 | Existence/consistency witness built from an explicitly chosen flow; it should not be read as forcing quantum dynamics. |
| `LF4/SingletObservables.lean` | 222 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SpectralCarving.lean` | 338 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SpectralExpansion.lean` | 152 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/SpectralVariance.lean` | 237 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/TrialWitness.lean` | 164 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/TypicalityForcing.lean` | 613 | Pass | S0 | Particularly honest result: proves symmetry uniqueness while also proving the chosen observable flow is non-ergodic and not uniquely ergodic. |
| `LF4/UncertaintyKahler.lean` | 163 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |
| `LF4/UnitarySelection.lean` | 197 | Pass with notes | S1 | Geometric/measure-theoretic support module; scope and hypotheses are visible, with interpretation subject to preparation-indexed carving and chosen-measure caveats. |

### LF5

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF5/Capstone.lean` | 185 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/CapstoneCanonical.lean` | 102 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/DilationFromFlow.lean` | 508 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/FlowBornFrequency.lean` | 154 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/MeasurementFlow.lean` | 240 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/PointerOutcome.lean` | 243 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/SyndromeFlow.lean` | 534 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/SyndromeOutcome.lean` | 341 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |
| `LF5/VonNeumannUnitary.lean` | 142 | Pass with notes | S2 | Explicit von Neumann/Naimark measurement-flow construction; establishes a canonical witness, not uniqueness or inevitability of the coupling. |

### LF6

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `LF6/AmplitudeDamping.lean` | 182 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/CGLMPQudit.lean` | 588 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/CGLMPQutrit.lean` | 409 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/Decoherence.lean` | 585 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/DephasingSemigroup.lean` | 145 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/ForcedContextuality.lean` | 245 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GHZContextuality.lean` | 407 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GHZDeisolationFlow.lean` | 362 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GHZLocalFlow.lean` | 648 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GHZMerminCarve.lean` | 616 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GHZnDeisolationFlow.lean` | 957 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/GisinTheorem.lean` | 180 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/LindbladGenerator.lean` | 263 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/LocalDeisolationFlow.lean` | 635 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/MaxEntangledCGLMPCapstone.lean` | 120 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/MaxEntangledDeisolationFlow.lean` | 750 | Pass with notes | S2 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/PartialSchmidtCorrelation.lean` | 144 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |
| `LF6/SingletDeisolationFlow.lean` | 449 | Pass with notes | S1 | Explicit open-system/contextuality construction; theorem scope is narrower than a general dynamical classification and conditions must remain visible. |

### Mathlib

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean` | 144 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Analysis/InnerProductSpace/KahlerForm.lean` | 254 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Analysis/Matrix/DuhamelBound.lean` | 137 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Analysis/Matrix/L2OpNormEntry.lean` | 70 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Analysis/Matrix/OperatorConvex.lean` | 766 | Pass with notes | S2 | Sound ladder/transport work, but the interior rpow/log-concavity-to-DPI chain remains incomplete and is documented as such. |
| `Mathlib/Analysis/Matrix/OperatorConvexBridge.lean` | 190 | Pass with notes | S2 | Sound ladder/transport work, but the interior rpow/log-concavity-to-DPI chain remains incomplete and is documented as such. |
| `Mathlib/Analysis/Matrix/StoneC1.lean` | 240 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Analysis/Normed/Lp/Matrix.lean` | 63 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` | 369 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Matrix/UnitaryCompact.lean` | 160 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Matrix/UnitaryHaar.lean` | 153 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/Bargmann.lean` | 339 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean` | 171 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean` | 342 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` | 230 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/PhaseRigidity.lean` | 177 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/Topology.lean` | 466 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean` | 283 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/Unitary.lean` | 157 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/UnitaryTransitive.lean` | 238 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` | 3180 | Pass with notes | S2 | Large foundational rigidity proof with meaningful statement; requires an independent specialist proof pass before upstream-grade confidence. |
| `Mathlib/MeasureTheory/LintegralFintypeProd.lean` | 128 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/MeasureTheory/PiCurry.lean` | 151 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/MeasureTheory/PiecewisePreserving.lean` | 194 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Probability/CGLMP.lean` | 591 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Probability/ConditionalProbability.lean` | 109 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Probability/IIDCoordinateProcess.lean` | 95 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/CanonicalChannels.lean` | 143 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Channel.lean` | 175 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/DataProcessing.lean` | 202 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Entropy.lean` | 569 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Fourier.lean` | 132 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Hadamard.lean` | 142 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Helstrom.lean` | 272 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/PartialTrace.lean` | 313 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Register.lean` | 81 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/Reversible/AndAdd.lean` | 782 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/Circuit.lean` | 206 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ConstProp.lean` | 244 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/Cost.lean` | 157 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/CtrlAdd.lean` | 417 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/CtrlMul.lean` | 352 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/CuccaroAdd.lean` | 520 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/CuccaroModAdd.lean` | 889 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/CuccaroModMul.lean` | 1337 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/Depth.lean` | 199 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/Eval.lean` | 242 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/GidneyAdder.lean` | 557 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModAdd.lean` | 412 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModInv.lean` | 101 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModMul.lean` | 454 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModReduce.lean` | 118 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModReduceCtrl.lean` | 506 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularAdd.lean` | 584 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularAddCtrl.lean` | 705 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularConst.lean` | 783 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularDouble.lean` | 518 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularMul.lean` | 949 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularMulLoop.lean` | 887 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/ModularSub.lean` | 840 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/VerifiedAdder.lean` | 441 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Reversible/VerifiedAdderCarryClean.lean` | 376 | Pass with notes | S2 | Concrete reversible-circuit semantics and arithmetic proof; large tactic-heavy modules should be split and regression-tested by arithmetic boundary cases. |
| `Mathlib/QuantumInfo/Stinespring.lean` | 137 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/QuantumInfo/StrongSubadditivity.lean` | 395 | Needs change | S3 | Proves SSA only from an explicit relative-entropy DPI hypothesis; the unconditional deep theorem is still absent. |
| `Mathlib/QuantumInfo/Subadditivity.lean` | 1156 | Pass with notes | S2 | Substantive reusable theorem file; statement/API review passed, but size warrants a specialist proof-maintenance pass. |
| `Mathlib/QuantumInfo/TraceDistance.lean` | 529 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |
| `Mathlib/Topology/Algebra/Module/LinearMap.lean` | 81 | Pass | S0 | Reusable CSD-free support result; no material statement or dependency issue found. |

### SigmaLayer

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `SigmaLayer/Adapters.lean` | 154 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/ApproxProjectability.lean` | 167 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/BasisMeasurement.lean` | 78 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/BellGenerality.lean` | 111 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/BlockCollapse.lean` | 302 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/BornFibrePartition.lean` | 180 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ChartBracket.lean` | 187 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/CircleFibre.lean` | 189 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/CircleRecord.lean` | 209 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/CompositeAdapters.lean` | 132 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/CompositeInterface.lean` | 127 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ConditionalUpdate.lean` | 99 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ConditioningLink.lean` | 113 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ConditioningLuders.lean` | 188 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ConstraintDynamics.lean` | 99 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ConstraintSurface.lean` | 43 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ContextFixedA7.lean` | 385 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ContextFixedA7FS.lean` | 323 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/DegenerateLuders.lean` | 319 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/DeIsolationFlow.lean` | 131 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/DynamicBorn.lean` | 149 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/DynamicMeasurementClosure.lean` | 179 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/DynamicsBridge.lean` | 95 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/FibredSigma.lean` | 102 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/FibreRecord.lean` | 120 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ForwardCapstone.lean` | 82 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/GlobalBasin.lean` | 241 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/GlobalRecordClosure.lean` | 187 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/HamiltonianSignature.lean` | 242 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/Interference.lean` | 56 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/IsolationPreparation.lean` | 109 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/JoinArena.lean` | 349 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/JoinClosure.lean` | 153 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/JointFlowTransfer.lean` | 235 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/KSigmaRecord.lean` | 97 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/LiftedMeasurement.lean` | 226 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/LocalBlockBridge.lean` | 172 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/LocalisedTypicality.lean` | 98 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/LocalLuders.lean` | 165 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/LocalLudersBasis.lean` | 242 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/Luders.lean` | 141 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MeasureBridge.lean` | 96 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/Measurement.lean` | 161 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/MeasurementProtocol.lean` | 271 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MeasurementRecord.lean` | 104 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MixedEnsemble.lean` | 159 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MixedFrequency.lean` | 143 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/MixedJoinLuders.lean` | 208 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/MixedLuders.lean` | 179 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MixedOntic.lean` | 96 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/MixedState.lean` | 199 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/MixedSwap.lean` | 135 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/MomentMapRace.lean` | 129 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/NoRecordGeometry.lean` | 305 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/NullSeamLift.lean` | 213 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/NullSeamWitness.lean` | 827 | Pass with notes | S2 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/OnticBornFrequency.lean` | 112 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/OnticComposite.lean` | 270 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/OnticMarginals.lean` | 354 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/OutcomeBasin.lean` | 118 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/OutcomeField.lean` | 132 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PhaseSlot.lean` | 332 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PiecewiseHamiltonian.lean` | 152 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerArena.lean` | 217 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerBorn.lean` | 258 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerCoupling.lean` | 242 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerFrequency.lean` | 115 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerHamiltonianField.lean` | 94 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerLanding.lean` | 248 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerLudersMarginal.lean` | 408 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerRotation.lean` | 273 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerSmoothProfile.lean` | 115 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/PointerWeights.lean` | 309 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/PostMeasurement.lean` | 107 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/ProjectiveRecord.lean` | 135 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/ProjectiveSector.lean` | 109 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/RecordedFact.lean` | 139 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/RecordLayerClosure.lean` | 119 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/RecordPersistence.lean` | 163 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/RotatedContext.lean` | 121 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/RotatedSwap.lean` | 252 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/SectorPostulateNoGo.lean` | 116 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/SharpenedNoGo.lean` | 164 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/ShearDiscontinuity.lean` | 222 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/ShearWitness.lean` | 449 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/SmoothProfile.lean` | 224 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/SwapClosure.lean` | 264 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/Symmetrization.lean` | 179 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TensorGeneration.lean` | 82 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TensorReconstruction.lean` | 160 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TensorSector.lean` | 86 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TensorSolved.lean` | 109 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TheoremTargets.lean` | 83 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/TimeIndexedRecord.lean` | 104 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/TorusFibre.lean` | 177 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `RecordLayer/UnifiedArena.lean` | 340 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/UnifiedFlowedRecords.lean` | 124 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/UnifiedMeasurement.lean` | 162 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |
| `SigmaLayer/UniqueErgodicity.lean` | 104 | Pass with notes | S1 | Measurement/record/fibre support module; construction is formal and explicit, while apparatus calibration and witness-specific assumptions remain load-bearing. |

### Tests

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `Tests/AxiomAudit.lean` | 10203 | Pass with notes | S2 | Useful compile/audit coverage; generated per-layer manifests would reduce root drift and manual maintenance. |
| `Tests/Examples.lean` | 455 | Pass with notes | S2 | Useful compile/audit coverage; generated per-layer manifests would reduce root drift and manual maintenance. |

### Thermo

| File | Lines | Verdict | Severity | Review note |
|---|---:|---|---:|---|
| `Thermo/CanonicalTypicality.lean` | 498 | Pass with notes | S2 | Finite-dimensional thermodynamic theorem is coherent under explicit positivity/full-rank/coarse-graining assumptions; not a general nonequilibrium second law. |
| `Thermo/FreeEnergy.lean` | 310 | Pass with notes | S2 | Finite-dimensional thermodynamic theorem is coherent under explicit positivity/full-rank/coarse-graining assumptions; not a general nonequilibrium second law. |
| `Thermo/Landauer.lean` | 213 | Pass with notes | S2 | Finite-dimensional thermodynamic theorem is coherent under explicit positivity/full-rank/coarse-graining assumptions; not a general nonequilibrium second law. |
| `Thermo/SecondLaw.lean` | 243 | Pass with notes | S2 | Finite-dimensional thermodynamic theorem is coherent under explicit positivity/full-rank/coarse-graining assumptions; not a general nonequilibrium second law. |

## Additional cross-cutting findings from the complete pass

### F-08 - Strong subadditivity remains conditional on DPI (S3)

`Mathlib/QuantumInfo/StrongSubadditivity.lean` proves a correct reduction from an explicit relative-entropy data-processing hypothesis. The operator-convexity ladder does not yet discharge that hypothesis. Public summaries must say "SSA from DPI", not "SSA proved".

### F-09 - Construction versus forcing recurs beyond the foundational tranche (S3)

LF4-LF6 and SigmaLayer contain many valuable explicit witnesses: chosen unitary flows, von Neumann couplings, Naimark embeddings, record fibres, calibrated banks, decoherence channels, and contextuality carves. These prove consistency and realizability. They do not generally prove uniqueness, emergence, or that the construction is forced by the earlier CSD axioms.

### F-10 - The QFT/CV layer is a finite-cutoff model (S3)

The CV modules formalize finitely many truncated modes. In particular, ModeLocality obtains commutation from a strong support-factorization definition. This is a useful kinematic cutoff theorem, not a derivation of continuum Haag-Kastler locality or interacting QFT.

### F-11 - Thermodynamic results are finite-dimensional and assumption-sensitive (S2)

The second-law, free-energy, Landauer, and typicality results are meaningful finite-dimensional theorems. Full-rank/positive-definite Gibbs or marginal assumptions, unitary system-bath evolution, and a specified coarse-graining/pinching map carry essential content.

### F-12 - Proof-maintenance risk is concentrated in a small set of very large files (S2)

The largest Wigner-rigidity, reversible arithmetic, entropy, Shor, contextuality-volume, GHZ, and axiom-audit modules combine substantial mathematics with long tactic proofs. No trust escape was found, but these should be split around stable intermediate APIs and supplied with boundary-case regression tests.

## Completed coverage summary

- Foundational tranche: 38 files reviewed in the main ledger.
- Remaining appendix: 405 files reviewed at source/statement/API/dependency level.
- Total Lean modules represented: 443.
- Direct declaration scan found no trust escape declaration; prose occurrences of axiom/sorry/admit were excluded.
- Compilation remains unverified because the pinned Lean toolchain is not cached and network download is unavailable.
