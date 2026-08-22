# Mathlib gaps this project has hit — and what closing them would unlock

*(Created 2026-08-02. Two lists: genuine absences in Mathlib that gate corpus work, and the
material this repo has already staged for upstream. Each gap names the corpus item it blocks,
so contributors can see the physics payoff of a library PR. The single open-work list remains
[`specs/BACKLOG.md`](specs/BACKLOG.md); this page is the Mathlib-facing cut of it.)*

**Triage 2026-08-22** ([`specs/mathlib-gaps-plan.md`](specs/mathlib-gaps-plan.md)): every row
below was re-probed at the pin. Birkhoff and Lévy verified standing; the `CStarAlgebra`
row is a SOFT wall (the instances exist at the pin — the failure is discrimination-tree
resolution, probe-first as MG-3); the FS-metric and polynomial-zero-sets rows are **attackable
in-corpus** (MG-1, MG-2 — the latter converts "almost every composite state is entangled" from
research-gated prose to a bounded three-brick chain).

## Genuine absences (no Mathlib API today)

| Gap | What it is | What it blocks here | Current workaround |
|---|---|---|---|
| **Kähler / symplectic manifold API** | Differential forms *on manifolds* with `dω = 0`, compatible complex structure, Liouville volume `ωⁿ/n!`, Hamiltonian vector fields `X_H = ω⁻¹dH`. ⚠️ *Narrowed 2026-08-06:* upstream now has the exterior derivative **on normed spaces** (`Mathlib/Analysis/Calculus/DifferentialForm/`, flat space, with `d² = 0`; manifold forms are that file's own TODO), so the FLAT half of the gap is gone | The *manifold* spelling only. The `X_H = ω⁻¹dH` sentence is no longer pure prose: the linear-level identification is proved (`Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean` — `ι_Xω = dH` with the Schrödinger field `-(i•Ax)` exhibited, instantiated on the pointer coupling in `SigmaLayer/PointerHamiltonianField.lean`); the chart-level Poisson fragment is A3 (`ChartBracket.lean`). What stays blocked: the quotient/manifold statement on `ℂℙ^{N-1}` and the arena (`reconstruction-status.md` §2a) | Measures (`fubiniStudyMeasure`, Haar products) carry all consumed content; the geometric reading above the linear/chart fragments is documented prose (`AXIOMS.md` §3.1). Flat `dω = 0` for the constant fundamental form is **PROVED** (2026-08-06, `Mathlib/Analysis/InnerProductSpace/KahlerClosed.lean`: `extDeriv_const` + `Kahler.extDeriv_fundamentalFormAlt`); only the manifold spelling on `ℂℙ^{N-1}` remains in this gap |
| **Pointwise Birkhoff ergodic theorem** | A.e. time-average = space-average for measure-preserving flows | `BornFromFlow` (manifest L7 / T3): frequencies along a *single flow trajectory* rather than i.i.d. sampling | The strong-law route (i.i.d. trials of `μL`); the no-gos (`flow_admits_invariant_ne_fubiniStudy`) show a single flow cannot pin `μ_FS` anyway |
| **Operator convexity interior rungs (Löwner)** | `log` operator-concavity, `x^p` (`p∈(0,1)`) concavity, Effros perspective, **Lieb concavity → joint convexity of relative entropy → DPI** | Unconditional **strong subadditivity** (`StrongSubadditivity.lean` carries the reduction with `hDPI` as an explicit hypothesis); the quantum data-processing inequality | The ladder is part-built (`OperatorConvex.lean`: predicate, `x⁻¹` rung, resolvent rungs, reframing lemma, cfc-integral commutation); the wall is instance resolution, next row |
| **`CStarAlgebra`-instances for `Matrix n n ℂ`** | The default instances on `Matrix` don't provide `CStarAlgebra`/`NonUnitalCStarAlgebra`; the `CStarMatrix` synonym's instances don't *resolve* for `rpow`/`NonnegSpectrumClass` (discrimination-key failures) | Everything C⋆-generic on matrices: `CFC.log` monotonicity transported by a hand-built bridge (`OperatorConvexBridge.lean`); `cfcₙ_setIntegral`; the `x^p` rungs above | The bridge file (B.1–B.3) + a from-scratch matrix Bochner-cfc (`cfc_integral_commute`); an upstream instance-hygiene fix would delete both |
| **Lévy concentration / spherical isoperimetry** | Measure concentration on high-dimensional spheres | Canonical-typicality **exponential** concentration (TH1 carries expectation + the Q24 Chebyshev tier) | Named residual, recorded; expectation form proved (`fs_first_moment`); polynomial-rate concentration proved (Q24, 2026-08-21: `fs_chebyshev_concentration`, twirl-algebra second moments — no isoperimetry); only the `exp(−c·d_E·ε²)` rate still waits on this gap |
| **Fubini–Study metric on `ℙ`** | A `MetricSpace` instance on `Projectivization` (Mathlib has topology only, staged here; no `dist` anywhere) | The quantified ε-ball forms of the C2 support arc (BACKLOG Q28): "every ε-ball around a product ray", "states closer than 2ε have overlapping ε-preparations". The topological forms land without it | The Q28 statements are formulated with open neighbourhoods instead of balls; the contradiction C2 runs on is unaffected |
| **Polynomial zero sets are null** | Zero set of a nonzero (multivariate/holomorphic) polynomial has measure zero, in a form transportable through `Measure.map (orbitMap p₀) unitaryHaarProb` (equivalently: analytic identity theorem on the connected group `U(N)`) | `segre_range_null` — "almost every composite state is entangled" (`specs/c2-support-plan.md` Item 5); prose-strength only, the C2 argument runs on the positive form | The positive-measure form (Q28 item 2) carries the argument; the null form is research-gated |
| **Hilbert tensor factorisation of registers** | `QReg m ≅ QReg 3 ⊗ QReg (m − 3)` as Hilbert spaces (inner product carried), from the `Fin m ≃ Fin 3 ⊕ (m−3)` reindex — `EuclideanSpace`/`PiLp` has no tensor-split API | The measurement-gadget hybrid at full-register level (`MeasurementAdder.lean`'s wall: the gadget is not a permutation, so it needs the local tensor factor); also cited by the general-lift optionality verdict (`Reversible/Lift.lean`) | The per-block equivalence + cost aggregation carry the result; the n-fold amplitude state-equality is recorded as WALLED. Attack gated on a consumer (`specs/mathlib-gaps-plan.md` MG-5) |
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
| `Analysis/Matrix/L2OpNormEntry.lean` | `‖M a b‖ ≤ ‖M‖` (entry ≤ L2 operator norm) + `EuclideanSpace.norm_coord_le_norm` — the bridge from operator-norm estimates to entrywise (Pi-topology) continuity | `Mathlib.Analysis.CStarAlgebra.Matrix` (beside `entry_norm_bound_of_unitary`) |
| `Analysis/Matrix/{OperatorConvex, OperatorConvexBridge}.lean` | Löwner operator-convexity predicate + rungs; the `CStarMatrix ↔ Matrix` CFC/order bridge | `Mathlib.Analysis.Matrix` (and an instance-hygiene issue upstream) |
| `MeasureTheory/PiecewisePreserving.lean` | Measurability/measure-preservation by partition; `swapSlot` on `Measure.pi` | `Mathlib.MeasureTheory` |
| `QuantumInfo/{Entropy, PartialTrace, Subadditivity, StrongSubadditivity, Channel, TraceDistance, Register, Helstrom}.lean` | von Neumann entropy (+ subadditivity, Araki–Lieb, conditional SSA), matrix partial trace, CPTP/Kraus/Stinespring, trace distance with DPI, n-qubit registers, Helstrom bound | a future `Mathlib.QuantumInfo` (none exists today) |

**Suggested first upstream batch** (self-contained, no pauses touching them):
Projectivization `Topology` + `MeasureSpace`, `StoneC1`, `DuhamelBound`, `PiecewisePreserving`,
`PartialTrace`, `TraceDistance`. See `specs/BACKLOG.md` for the tracked item.
