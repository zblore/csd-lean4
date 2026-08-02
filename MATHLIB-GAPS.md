# Mathlib gaps this project has hit — and what closing them would unlock

*(Created 2026-08-02. Two lists: genuine absences in Mathlib that gate corpus work, and the
material this repo has already staged for upstream. Each gap names the corpus item it blocks,
so contributors can see the physics payoff of a library PR. The single open-work list remains
[`specs/BACKLOG.md`](specs/BACKLOG.md); this page is the Mathlib-facing cut of it.)*

## Genuine absences (no Mathlib API today)

| Gap | What it is | What it blocks here | Current workaround |
|---|---|---|---|
| **Kähler / symplectic manifold API** | Differential forms on manifolds with `dω = 0`, compatible complex structure, Liouville volume `ωⁿ/n!`, Hamiltonian vector fields `X_H = ω⁻¹dH` | The A1 exterior-calculus row and the symplectic *spelling* of the piecewise-Hamiltonian classification (`reconstruction-status.md` §2a — the pieces are exhibited as explicit continuous translations; only the `X_H` sentence is prose) | Measures (`fubiniStudyMeasure`, Haar products) carry all consumed content; the geometric reading is documented prose (`AXIOMS.md` §3.1) |
| **Pointwise Birkhoff ergodic theorem** | A.e. time-average = space-average for measure-preserving flows | `BornFromFlow` (manifest L7 / T3): frequencies along a *single flow trajectory* rather than i.i.d. sampling | The strong-law route (i.i.d. trials of `μL`); the no-gos (`flow_admits_invariant_ne_fubiniStudy`) show a single flow cannot pin `μ_FS` anyway |
| **Operator convexity interior rungs (Löwner)** | `log` operator-concavity, `x^p` (`p∈(0,1)`) concavity, Effros perspective, **Lieb concavity → joint convexity of relative entropy → DPI** | Unconditional **strong subadditivity** (`StrongSubadditivity.lean` carries the reduction with `hDPI` as an explicit hypothesis); the quantum data-processing inequality | The ladder is part-built (`OperatorConvex.lean`: predicate, `x⁻¹` rung, resolvent rungs, reframing lemma, cfc-integral commutation); the wall is instance resolution, next row |
| **`CStarAlgebra`-instances for `Matrix n n ℂ`** | The default instances on `Matrix` don't provide `CStarAlgebra`/`NonUnitalCStarAlgebra`; the `CStarMatrix` synonym's instances don't *resolve* for `rpow`/`NonnegSpectrumClass` (discrimination-key failures) | Everything C⋆-generic on matrices: `CFC.log` monotonicity transported by a hand-built bridge (`OperatorConvexBridge.lean`); `cfcₙ_setIntegral`; the `x^p` rungs above | The bridge file (B.1–B.3) + a from-scratch matrix Bochner-cfc (`cfc_integral_commute`); an upstream instance-hygiene fix would delete both |
| **Lévy concentration / spherical isoperimetry** | Measure concentration on high-dimensional spheres | Canonical-typicality **concentration** (TH1 is expectation-level only) | Named residual, recorded; expectation form proved (`fs_first_moment`) |
| **Stone's theorem (general)** | Strongly continuous one-parameter unitary groups ↔ self-adjoint generators | Full-continuity Schrödinger recovery (we require C¹) | Staged finite-dimensional C¹ version (`StoneC1.lean`) — itself an upstream candidate |
| **Bargmann's theorem** | Continuity ⇒ vanishing of the projective-representation cocycle | Would discharge the coboundary *datum* in the W-series phase lift from continuity alone | The coboundary is an explicit named hypothesis, non-vacuously inhabited |
| **Wigner normal form** | The last normal-form lemma behind full Wigner rigidity | Closing `LF4-todo.md` §13 without the staged pause | §13 is paused at that single lemma; the rigidity chain up to it is staged and audited |
| **Kronecker spectral theorem** | Eigenvalues of `A ⊗ B` = products, as a spectral statement | Was needed for entropy additivity | Worked around: `spectral_sum_kronecker` via charpoly (staged) |
| **Unitarily invariant Gaussian on `ℂⁿ`** | Multivariate complex Gaussian + invariance under `U(n)` | Was the recorded route to Liouville preservation for the phase-slot dynamics | Dissolved — the projective join made the dynamics a unitary on `ℙ(ℂ^{2N})`, so FS invariance sufficed |

## Staged in this repo, ready to edge upstream (`CsdLean4/Mathlib/`)

All CSD-free (Category 1), Mathlib naming/docstring discipline, foundational-triple only.

| Staged file(s) | Contents | Upstream target |
|---|---|---|
| `LinearAlgebra/Projectivization/Topology.lean` | Quotient topology instance, `continuous_mk'`, open-map/quotient-map, T2, compactness, `Projectivization.map` continuity, `mapEquiv`, **connectedness** (`connectedSpace_of_isConnected_nonzero`) | `Mathlib.LinearAlgebra.Projectivization.Topology` |
| `…/Projectivization/MeasureSpace.lean` | Borel instance, `measurable_mk'`, Borel = coinduced coincidence, `measurable_iff_measurable_comp_mk'`, lift measurability | ditto (measure file) |
| `…/Projectivization/FubiniStudy.lean` (+`Unique`) | `fubiniStudyMeasure` as Haar pushforward, unitary invariance, uniqueness | new file |
| `…/Projectivization/{TransitionProbability, WignerRigidity, Bargmann, PhaseRigidity, Unitary…}.lean` | Transition probabilities, Wigner rigidity chain, Bargmann invariant, `U(N)→PU(N)` kernel | staged pending the §13 pause decision |
| `Analysis/Matrix/StoneC1.lean` | Finite-dimensional C¹ Stone theorem | `Mathlib.Analysis.Matrix` |
| `Analysis/Matrix/DuhamelBound.lean` | `‖e^{tC}−e^{tA}‖ ≤ \|t\|‖C−A‖` for skew-Hermitian generators (integral-free) | ditto |
| `Analysis/Matrix/{OperatorConvex, OperatorConvexBridge}.lean` | Löwner operator-convexity predicate + rungs; the `CStarMatrix ↔ Matrix` CFC/order bridge | `Mathlib.Analysis.Matrix` (and an instance-hygiene issue upstream) |
| `MeasureTheory/PiecewisePreserving.lean` | Measurability/measure-preservation by partition; `swapSlot` on `Measure.pi` | `Mathlib.MeasureTheory` |
| `QuantumInfo/{Entropy, PartialTrace, Subadditivity, StrongSubadditivity, Channel, TraceDistance, Register, Helstrom}.lean` | von Neumann entropy (+ subadditivity, Araki–Lieb, conditional SSA), matrix partial trace, CPTP/Kraus/Stinespring, trace distance with DPI, n-qubit registers, Helstrom bound | a future `Mathlib.QuantumInfo` (none exists today) |

**Suggested first upstream batch** (self-contained, no pauses touching them):
Projectivization `Topology` + `MeasureSpace`, `StoneC1`, `DuhamelBound`, `PiecewisePreserving`,
`PartialTrace`, `TraceDistance`. See `specs/BACKLOG.md` for the tracked item.
