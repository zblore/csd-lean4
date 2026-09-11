# Content-carrying terms: what they mean here, and what backs them

**Status:** created 2026-09-04. Companion to `CONVENTIONS.md` §8.3a ("Names are claims"), which
rules that a word carrying mathematical content must be honest about the object it names. §8.3a
says *that* the rule holds; this file says *what each word means in this corpus and what
establishes it*, so the rule can be checked rather than remembered.

**Why it exists.** A word like "Kähler" or "Hamiltonian" has a standard meaning that is stronger
than what any given module establishes. Where the corpus uses the strong sense it disclaims the
gap — at the definition sites, carefully. The risk is not there: it is in the 150-odd modules that
use the word in passing, where a reader has no way to know which sense is meant. This file is the
one place that says, and `scripts/check-terms.sh` enforces that the **restricted** sense is
marked wherever it is used.

**How to read an entry.** *Means here* is the sense the corpus uses. *Backed by* names the
declaration that establishes it. *NOT established* is the part of the standard meaning that is
absent — and any module invoking **that** part must carry the marker `TERM-SCOPE(<Term>)`.

---

## Kähler

* **Means here (backed):** the **pointwise** compatibility triple on the tangent model of
  `ℂℙ^{N−1}` — `J² = −1`, `ω = g∘J`, `g = ω∘J`, `ω` a `(1,1)`-form, and the taming identity
  `ω u (J u) = ‖u‖²`.
* **Backed by:** `IsFubiniStudyKahler` (`LF4/KahlerOnticSetup.lean`), proved axiom-free by
  `Kahler.fubiniStudy_pointwise_kahler_compatibility`; the objects themselves are
  `Kahler.complexStructure`, `Kahler.metric`, `Kahler.fundamentalForm`
  (`Mathlib/Analysis/InnerProductSpace/KahlerForm.lean`).
* **Also backed (2026-09-07):** the manifold-level **closedness** `dω = 0` on `ℂℙⁿ` —
  `Projectivization.fsForm_mextDeriv` (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean`),
  for the Fubini–Study form `fsForm` as a `C^∞` global 2-form and the exterior derivative
  `mextDeriv` of `Mathlib/Geometry/Manifold/ExteriorDerivative.lean` (real boundaryless model,
  smoothness `∞`).
* **Also backed (2026-09-07/08):** non-degeneracy at every point and the symplectic predicate —
  `fsForm_nondegenerate`, ★★★ `fsForm_isSymplectic` (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`);
  and the top-power identity with its constant — ★★★ `fsVolume_eq_smul_fubiniStudyMeasure`,
  `ω_FS^{∧n} = (4π)ⁿ · μ_FS` (`Instances/ProjectiveSpaceFubiniStudyMass.lean`; see the Liouville
  entry for the convention behind `(4π)ⁿ`).
* **Also backed (2026-09-09, G7):** the manifold-level predicate — `DifferentialForm.IsAlmostKahler β J`
  (`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean`: a symplectic form with a compatible almost
  complex structure, `J² = -1`, `J`-invariance, taming `β (J v, v) > 0`, and the compatible metric
  `g = β (J ·, ·)` symmetric and positive definite) and its inhabitant ★★
  `Projectivization.fsForm_isAlmostKahler` (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`):
  **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is almost Kähler**; `fderiv_chart_transition_smul_I`
  shows the chart transitions are holomorphic, so `J = i·` is the complex structure of the atlas.
* **Also backed (2026-09-10, G12):** analyticity — `Kahler.contDiff_omega_fsPotential` (the potential
  `log(1 + ‖z‖²)` is real-analytic; `Analysis/InnerProductSpace/KahlerPotential.lean`) and ★★
  `Projectivization.contMDiff_omega_fsForm` / `fsFormAnalytic` (**the Fubini–Study form is an analytic
  section**, a term of the `ω` type; `Instances/ProjectiveSpaceFubiniStudyForm.lean`). Nothing downstream is
  restated at `ω`.
* **Also backed (2026-09-10, G14a):** the Kähler predicate itself — `DifferentialForm.IsKahler β J J₀`
  (`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean`: almost Kähler, and `J` is the model's
  complex structure `J₀` through the tangent trivialisation of every chart, so every chart transition
  is holomorphic, `IsKahler.fderiv_chart_transition_comm` — the textbook definition, a complex manifold
  with a Hermitian metric whose fundamental form is closed) and its inhabitant ★★★
  `Projectivization.fsForm_isKahler` (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`):
  **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is a Kähler manifold.**
* **Also backed (2026-09-11, Q33):** the arena `ℂℙⁿ × T²` is an analytic manifold
  (`CSD.LF4.ksigma_isManifold`; `AddCircle` made a manifold by transport along
  `AddCircle.homeomorphCircle`, `Mathlib/Geometry/Manifold/Instances/AddCircle.lean`) and the sector
  projection `π` is `C^ω` (`manyToOneSetup_pi_contMDiff`) — Paper C's A3.
* **Wired to the physics (2026-09-10, W1):** `LF4/SectorManifold.lean` — the `ℂℙⁿ` instances of
  `KahlerOnticSetup` have `liouvilleMeasure = fsVolumeNormalized n`, the normalised top power of the
  Kähler form (★★★ `unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized`), their flows preserve
  `fsVolume n` itself, the forced volume of `KahlerVolumeForced.lean` IS that top power
  (`fsVolumeNormalized_isForcedKahlerVolume`), and ★★★ `unitaryFlowSetup_isKahler_liouville` /
  `manyToOneSetup_isKahler_liouville` state each sector as the standard object. The structure's
  fields are unchanged; Posit 3 is untouched.
* **Also backed (2026-09-10, G15):** `J` as a smooth section of the endomorphism bundle — ★★
  `DifferentialForm.IsKahler.contMDiff_hom_section` (for a Kähler structure whose `J` is given as
  continuous linear maps, `x ↦ J x` is a `C^∞` section of `Hom(TM, TM)`: constant `J₀` in every
  chart) and its instance `Projectivization.contMDiff_fsJL` on `ℂℙⁿ`.
* **Also backed (2026-09-10, G14b):** the tensor formulation of integrability —
  `DifferentialForm.nijenhuis` (the Nijenhuis tensor, with Mathlib's manifold Lie bracket
  `VectorField.mlieBracket`) and ★★★ `DifferentialForm.IsKahler.nijenhuis_eq_zero` (**on a Kähler
  manifold it vanishes** on vector fields differentiable at the point), with
  `Projectivization.nijenhuis_fsJ_eq_zero` on `ℂℙⁿ`. The easy direction of Newlander–Nirenberg.
* **Also backed (2026-09-11, G17):** the Riemannian reading — `fsMetric = ω(J·,·)` is the compatible
  metric of `fsForm_isAlmostKahler` (`fsMetric_eq_metric`, rfl), and its Riemannian volume is
  `ω^{∧n}/n!` (`riemannianVolume_fsMetric`, `Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`).
* **NOT established:** the converse of Newlander–Nirenberg (a vanishing Nijenhuis tensor yields a
  holomorphic atlas — a PDE result nothing here needs). Marker: `TERM-SCOPE(Kahler)`.

## density operator of a preparation

* **Means here (backed, 2026-09-11, W2):** `CSD.LF2.preparationDensity` (`LF2/PreparationQdensity.lean`)
  — the unique `DensityOperator N` whose trace form is the effect probabilities of the operational
  package `fromPreparation` builds from a preparation measure on `Σ` (`preparation_traceForm`,
  `preparation_qdensity_unique`: `effect_gleason_representation` composed with `fromPreparation`). Its
  von Neumann entropy is `preparationEntropy`, non-negative and at most `log N`; two preparations'
  trace distance contracts under any channel (`channel_traceDist_preparation_le`).
* **Also backed (2026-09-11, W3):** it IS the barycentre `∫ |ψ⟩⟨ψ| d(π_* μprep)` of the rank-one projectors
  along the preparation's projective law — `preparationDensity_eq_barycenter`, entrywise
  `preparationDensity_apply` (`LF2/PreparationBarycenter.lean`); in the `ρ_ep dμ_FS` form when the
  projective law is absolutely continuous w.r.t. `μFS` (`preparationDensity_apply_rnDeriv`).
* **Also backed (2026-09-11, W6):** it evolves along `Σ`-flows as the QIT layer says it does — if the
  ontic flow lifts a unitary `U` (`IsUnitaryLift`, `LF2/FlowChannel.lean`), the density operator of the
  flowed preparation is `U ρ Uᴴ` (`barycenter_flow`), and on a joint sector the reduced flowed state is the
  Stinespring channel `ρ ↦ Tr_env (U (ρ ⊗ σ) Uᴴ)` applied to the system's density operator
  (`traceRight_barycenter_flow`, `traceRight_barycenter_flow_prod`); LF6's `decohereReduced` is such a
  channel output (`deisolationChannel_apply_outerProduct`).
* **Also backed (2026-09-11, W4, `LF2/PreparationPurity.lean`):** its entropy vanishes iff the preparation is
  pure, i.e. its projective law is a Dirac mass at a single ray (`preparationEntropy_eq_zero_iff`, with the
  canonical measurable unit section as representative; matrix level `vonNeumannEntropy_eq_zero_iff`).
* **Also backed (2026-09-11, W8, `LF2/PreparationCoarseGraining.lean`):** it is affine in the preparation
  measure, and its entropy is concave: the entropy of a mixture of preparations is at least the weighted
  average of the components' entropies (`preparationEntropy_mixture_ge`; Cat-1
  `vonNeumannEntropy_mixture_ge`, Klein's full-support condition on the mixture).
* **Also backed (2026-09-11, W7, `Thermo/SigmaSecondLaw.lean`):** its entropy is conserved along the ontic
  flow and does not decrease under pinching the flowed state or under de-isolation (the second law on
  `Σ`, `vonNeumannEntropy_le_pinching_flow` / `vonNeumannEntropy_le_deisolation`; TH2's `pinch` IS the
  de-isolation channel, `deisolationChannel_apply_eq_pinch`); de-isolation cannot increase two
  preparations' trace distance (`traceDist_traceRight_flow_le`); Landauer's bound holds for a product
  preparation whose bath preparation has the Gibbs barycentre (`landauer_flow`).
* **Also backed (2026-09-11, `SigmaLayer/PreparationDensityBridge.lean`):** the `LF2` and `SigmaLayer`
  preparation interfaces agree on it — for a region preparation of the `SigmaLayer` with a bridge, the
  `LF2` density operator of its conditional law is `∫ ρ_ep |ψ⟩⟨ψ| dμ_FS` with `ρ_ep` Q28's Radon–Nikodym
  density (`preparationDensity_apply_rhoEp`; absolute continuity is a theorem there, not a hypothesis),
  and on the Kähler arena with `kSectorData` / `kBridgeData` and the canonical unit section it holds
  with no hypotheses (`kahler_preparationDensity_apply_unitSection`).
  (The `LF2.QuantumChannel ↔ QuantumInfo.Channel` bridge is `LF2/ChannelBridge.lean`, W5, 2026-09-11.)
* **Also backed (2026-09-11, W6′/W6″):** LF5's `measurementFlow` produces the de-isolation channel
  (`measurementFlow_traceRight_barycenter_unitSection`, `LF6/MeasurementFlowChannel.lean`), with the
  canonical measurable unit section `Projectivization.unitSection` as representative, so no section
  hypothesis remains between the ontic flow and the channel.

## moment map

* **Means here (backed):** the coordinate function `Φ([z])ᵢ = |zᵢ|²/‖z‖²` on `ℂℙ^{N−1}`
  (`LF4.momentMap`), with its elementary properties — well-definedness on rays (`momentMap_mk`),
  `momentMap_nonneg`, `momentMap_sum_eq_one`, `continuous_momentMap`, `measurable_momentMap` — **and
  the moment-map defining equation `ι_{X_i}ω = dF` at the LINEAR level**: `IsPhaseHamiltonian` is
  exactly that equation on the ambient `EuclideanSpace`, and `generatedRateField_eq_momentMap`
  proves that a rate field satisfying it *is* `momentMap`.
* **Backed by:** `LF4/MomentMap.lean`; `RecordLayer/CellLawForced.lean` (`IsPhaseHamiltonian`,
  `generatedRateField_eq_momentMap`, `torusGenerated_eq_momentMap`, CR-15). The pushforward facts
  the corpus needs are **theorems, not citations**: `fs_moment_pushforward_uniform` (qubit —
  a *discharged axiom*, 2026-05-31) and `fs_moment_joint_dirichlet_N` (general `N`), both on the
  foundational triple.
* **Also backed (2026-09-08):** the defining equation on the symplectic *manifold* — ★★★
  `Projectivization.torusField_isHamiltonianVectorField`
  (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean`, brick G6 of
  `specs/generator-layer-scoping.md`): the velocity field of the torus action `p ↦ diag(e^{iθ}) • p`
  on `ℂℙⁿ` — proved to be that velocity (`hasDerivAt_chartFun_torusUnitary`) — satisfies
  `ι_X ω_FS = dH` with `H = 2 ∑ₖ θₖ · momentMap`, for the Fubini–Study form `fsForm` of the symplectic
  manifold `fsForm_isSymplectic`. The factor `2` is the `-4` convention of `fsChartForm`. **And it is
  unique (G8):** `eq_add_const_of_isHamiltonianVectorField` (any Hamiltonian of the same field differs
  by a constant) and `eq_torusHamiltonian_of_nonneg_of_sum` (non-negativity and the sum-two
  normalisation pin a family of phase-field Hamiltonians to `2 · momentMap`).
* **Also backed (2026-09-09, G9):** the image of `momentMap` is exactly the standard simplex — ★★
  `Projectivization.range_momentMap` (same module): `Set.range momentMap = stdSimplex ℝ (Fin (n + 1))`,
  `⊆` the normalisation and `⊇` the ray of `(√t₀, …, √tₙ)` (`sqrtVec`, `momentMap_mk_sqrtVec`). That is
  the moment polytope of *this* action, by direct computation.
* **Also backed (2026-09-09, G13):** the `U(n+1)` moment map — `Projectivization.expectation H`, the
  expectation value `⟪z, Hz⟫.re / ‖z‖²` on rays, is (up to the factor `-2`) the Hamiltonian of the
  Schrödinger flow `exp(-itH)` for the Fubini–Study form
  (`schrodingerField_isHamiltonianVectorField`, `Instances/ProjectiveSpaceSchrodingerFlow.lean`);
  the torus moment map is its diagonal case (`schrodingerHamiltonian_neg_diagonal`).
* **NOT established:** the Atiyah–Guillemin–Sternberg convexity theorem itself (the polytope of a
  general Hamiltonian torus action — here the simplex is exhibited, not deduced from convexity), and
  smoothness of the field as a section of the tangent bundle (G3). Marker: `TERM-SCOPE(MomentMap)`.
* ⚠️ **Why this entry is late (added 2026-09-06).** This file is indexed by *words*, and "moment
  map" matched none of the Kähler / Hamiltonian / Liouville patterns, so the ratchet could not see
  it — even though `momentMap` is the most load-bearing named object in the corpus. It **is** the
  cell law, and the fibred Born route (`RecordLayer.globalBasin_born`) rests on exactly twelve
  definitions, of which this is the **only** one carrying external mathematical content. Found by a
  declaration-indexed sweep of the Born route's proof term, not by a word list. The lesson is about
  the register, not the object: the object's defining equation *is* proved as far as the corpus can
  reach.
* ⚠️ **Duistermaat–Heckman is NOT in this category**, despite appearing in ~48 modules. Nothing is
  named for it — `LF4/DuistermaatHeckman.lean` is a tombstone — and the statements the corpus needs
  are proved by an independent (Gaussian / change-of-variables) route. It is a literature signpost,
  not an unformalised import. The same check cleared `Naimark` (the defining properties are
  *structure fields* of `NaimarkDilation`, and `canonicalNaimark` builds one for an **arbitrary**
  POVM) and `UniquelyErgodic` (the standard definition, absent from Mathlib, defined here).

## Hamiltonian

⚠️ **Two senses, and only one is restricted.** Conflating them is why an audit of this word looks
alarming and is not.

* **Sense 1 — operator / Schrödinger (backed, and the corpus's usual meaning).** A Hermitian
  matrix `H` generating `exp(−itH)`. Backed by `HasHamiltonianRealisation`
  (`SigmaLayer/TheoremTargets.lean`: `∃ H, H.IsHermitian ∧ ∀ t p, flow t p = schrodingerUnitary hH t • p`),
  `LF4.schrodingerUnitary`, and the `_isHermitian` theorem beside each concrete operator
  (`fieldHamiltonian`, `relFieldHamiltonian`, `interactionHamiltonian` in `CV/`). **No marker
  needed** — nothing symplectic is claimed.
* **Sense 2 — Hamiltonian vector field (RESTRICTED).** `X_H = ω⁻¹dH` on a manifold, and
  "the flow is generated by a Hamiltonian" in the symplectic sense. The linear fragment is
  formalised (`Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean`, BACKLOG A4).
  **Also backed (2026-09-08):** the defining equation *at manifold level* —
  `DifferentialForm.IsHamiltonianVectorField α X H` (`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean`,
  brick G1 of `specs/generator-layer-scoping.md`): `α x (X x, v) = mfderiv H x v` for a 2-form family
  and a vector-field family, with `dH (X) = 0` and uniqueness for a symplectic form proved from it.
  **Inhabited on `ℂℙⁿ` (2026-09-08, G6):** `torusField_isHamiltonianVectorField` — the torus action
  is Hamiltonian for `fsForm` with `2 ∑ θₖ momentMap` as its Hamiltonian (see the moment-map entry).
  **Hamiltonian implies locally Hamiltonian (2026-09-09, G11):** ★
  `DifferentialForm.IsHamiltonianVectorField.isLocallyHamiltonian` — `d(ι_X ω) = d(dH) = 0` for a
  `C^∞` energy, through the `0`-form API of `ExteriorDerivative.lean` (`zeroFormFamily`,
  `toFlat_mextDeriv_zeroFormFamily`: `d` of a `0`-form is its differential) and `d ∘ d = 0`. The
  converse is false and not stated: closed-not-exact is the flux obstruction below.
  **The Schrödinger flow is Hamiltonian (2026-09-09, G13):** ★★★
  `Projectivization.schrodingerField_isHamiltonianVectorField`
  (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceSchrodingerFlow.lean`) — for every Hermitian
  `H`, the velocity field of `p ↦ exp(-itH) • p` on `ℂℙⁿ` (the corpus's `schrodingerUnitary`, proved to
  be that velocity) satisfies `ι_X ω_FS = dH` with `H = -2 ⟨H⟩ = -2 ⟪z, Hz⟫.re / ‖z‖²`; the torus (G6) is
  the diagonal case. This is the manifold form of the `U(n+1)` moment map.
  **Existence and uniqueness from non-degeneracy (2026-09-09, G2):** ★★
  `DifferentialForm.hamiltonianVectorField α hnd H = fun x => (ω♭ₓ)⁻¹ (dH_x)` (same module as G1) —
  where the 2-form family is non-degenerate at every point and the model is finite-dimensional,
  every `H` has a Hamiltonian vector field (`hamiltonianVectorField_isHamiltonianVectorField`) and
  it is the only one (`IsHamiltonianVectorField.eq_hamiltonianVectorField`);
  `IsSymplectic.hamiltonianVectorField` for a symplectic form. The torus and Schrödinger fields on
  `ℂℙⁿ` are these constructed fields (`torusField_eq_hamiltonianVectorField`,
  `schrodingerField_eq_hamiltonianVectorField`).
  **Smoothness (2026-09-09, G3):** ★★★ `DifferentialForm.contMDiff_hamiltonianVectorField` (same
  module) — for a `C^∞` 2-form family non-degenerate everywhere and a `C^∞` energy, the constructed
  field is a `C^∞` section of the tangent bundle (`hamiltonianVectorFieldSection`,
  `IsSymplectic.contMDiff_hamiltonianVectorField`); the chart reading is the inverse of the flat map
  of the local representative, smooth at invertible points. On `ℂℙⁿ` both Hamiltonians are `C^∞`
  and so **the torus field and the Schrödinger field are `C^∞` vector fields**
  (`contMDiff_torusField`, `contMDiff_schrodingerField`, `Instances/ProjectiveSpaceSchrodingerFlow.lean`).
  **Integral curves (2026-09-09, G4):** ★★ `exists_isMIntegralCurveAt_hamiltonianVectorField`,
  `isMIntegralCurve_hamiltonianVectorField_eq` (local existence, global uniqueness) and ★★
  `IsHamiltonianVectorField.comp_eq_of_isMIntegralCurve` — **energy conservation**, `H` constant along
  every integral curve of a Hamiltonian vector field of `H`. On `ℂℙⁿ`, ★★★
  `isMIntegralCurve_schrodingerUnitary_smul`: **the Schrödinger flow `t ↦ exp(-itH) • p` is the
  integral curve of its Hamiltonian vector field**, and `⟨H⟩` is conserved by it
  (`expectation_schrodingerUnitary_smul`).
  **Also backed (2026-09-10, G16):** the torus orbits `t ↦ diag(e^{itθ}) • p` are the integral
  curves of `torusField θ` — ★★★ `Projectivization.isMIntegralCurve_torusUnitary_smul`, unique
  through `p` (`eq_torusUnitary_smul_of_isMIntegralCurve`) — and `2 ∑ θₖ μₖ` is conserved along
  them and by the flow (`torusHamiltonian_torusUnitary_smul`).
  **Also backed (2026-09-10, G19):** analyticity — ★★★
  `DifferentialForm.contMDiff_omega_hamiltonianVectorField` (the Hamiltonian vector field of a `C^ω`
  energy for a `C^ω` non-degenerate 2-form is a `C^ω` section, on an analytic manifold: G3 at `ω`)
  and, on `ℂℙⁿ`, `contMDiff_omega_schrodingerField` / `contMDiff_omega_torusField` (both fields are
  analytic vector fields, for the analytic form `fsFormAnalytic` of G12).
  **Also backed (2026-09-11, Q29(a)):** the global flow — on a compact manifold the Hamiltonian
  vector field of a `C^∞` energy has a global integral curve through every point
  (`DifferentialForm.IsSymplectic.exists_isMIntegralCurve_hamiltonianVectorField`), and the flow
  `integralFlow` exists with the group law `integralFlow_add`
  (`Mathlib/Geometry/Manifold/IntegralCurve/GlobalFlow.lean`; Mathlib has no flows on manifolds).
  **NOT established:** joint continuity of the flow in `(t, x)` (Q29(a′)), that its time-`t` maps
  preserve the symplectic volume (Q29(b′)–(d′), `BACKLOG.md` ▶ OUTSTANDING), and the arena statement
  `R-016`.
  Marker: `TERM-SCOPE(Hamiltonian)`.
* ⚠️ **Known retained name.** `RecordLayer/PiecewiseHamiltonian.lean` keeps its name after the
  2026-08-02 flux correction withdrew the reading (`ι_Xω = a·dp` is closed but not exact on `T²`,
  so no global generator exists). Retained deliberately for pin stability, with the correction at
  the top of the file. The accurate name is *piecewise rigid symplectic torus translation*.

## Liouville

* **Means here (backed):** the flow-invariant measure — Liouville in the **dynamics** sense, which
  is what `ConstraintDynamics.flow_preserves` (P4) licenses: each time-`t` map preserves `muL`.
* **Backed by:** `ConstraintDynamics.flow_preserves` (a structure field — *posited* of every
  model, not derived), and `liouville_isProbability` for the Kähler instance.
* **Established (2026-09-08):** `Projectivization.fsVolumeNormalized_eq_fubiniStudyMeasure` (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyVolume.lean`) — the **normalised** measure of the top power of the Fubini–Study form IS `fubiniStudyMeasure p₀`, with no premise: the volume is `U(n+1)`-invariant, finite and nonzero (`specs/top-power-scoping.md`, M1–M6; the premise version of the morning survives as `_of_ne_zero`).
* **Established with its constant (2026-09-08, later the same day):** `Projectivization.fsVolume_eq_smul_fubiniStudyMeasure` (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyMass.lean`) — `fsVolume n = (4π)ⁿ • fubiniStudyMeasure p₀`, the mass `(4π)ⁿ` computed (`fsVolume_univ`). So "this measure **is** the Kähler top-power volume" is now a theorem on `ℂℙⁿ` with every factor visible; the textbook `ω^{∧n}/n!` is a renormalisation of it (the chart form carries the potential's `-4`, the wedge its own normalisation), not a further claim.
* **Established for the torus flow (2026-09-09, G10):** `Projectivization.fsVolume_map_torusUnitary_smul` and `measurePreserving_torusUnitary_smul` (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean`) — every map `p ↦ diag(e^{iθ}) • p`, hence every time-`t` map of the Hamiltonian flow G6 built (`torusUnitary_add_smul` is the group law), preserves `fsVolume n`. Liouville in the dynamics sense for **one** Hamiltonian flow on `ℂℙⁿ`, obtained from unitary invariance (`fsVolume_map_smul`), not from a manifold-level flow theory (G5, queued at XL in `specs/generator-layer-scoping.md` §9). `ConstraintDynamics.flow_preserves` (Posit 3) is untouched: the constraint dynamics' measurement pieces are not globally Hamiltonian.
* **Wired to the sectors (2026-09-10, W1):** on the `ℂℙⁿ` instances of `KahlerOnticSetup` the posited field `flow_preserves_volume` preserves exactly `ω_FS^{∧n}`: `CSD.LF4.unitaryFlowSetup_flow_measurePreserving_fsVolume`, `manyToOneSetup_flow_measurePreserving_fsVolume_prod` (`LF4/SectorManifold.lean`), and the Liouville measure IS the normalised top power (`unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized`).
* **NOT established:** nothing on the `ℂℙⁿ` side of this entry remains open. The arena-level volume (`ℂℙⁿ × T² × …`) is a product of this with Haar factors and is not restated as a top power; `LF4/KahlerVolumeForced.lean` proves the normalisation core. Marker: `TERM-SCOPE(Liouville)`.
* ⚠️ **Precedent:** `nullSeamLiouville` was renamed because it named a measure on an
  odd-dimensional space, which cannot be symplectic (CONVENTIONS §8.3a). That is the failure this
  entry exists to prevent recurring.

## symplectic / manifold

* **Means here (backed, 2026-09-07):** `DifferentialForm.IsSymplectic`
  (`Mathlib/Geometry/Manifold/SymplecticForm.lean`) — a `C^∞` 2-form on a real boundaryless manifold
  that is closed (`mextDeriv α = 0`) and non-degenerate at every point — and its one inhabitant,
  `Projectivization.fsForm_isSymplectic`: **`ℂℙⁿ` with the Fubini–Study form is a symplectic
  manifold** (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`; real dimension `2n`).
  Before that date zero declarations carried either word at manifold level.
* **Also backed (2026-09-08/09):** derived from the structure — the symplectic volume
  (`fsVolume`, `fsVolume_eq_smul_fubiniStudyMeasure`), Hamiltonian vector fields with existence,
  uniqueness, smoothness and integral curves (`HamiltonianVectorField.lean`, G1–G4), moment maps of
  the torus and `U(n+1)` actions (G6, G13), the Kähler predicate (G7, G14a) — see the Hamiltonian,
  moment map and Kähler entries.
* **NOT established (queued in `specs/generator-layer-scoping.md` §9):** Darboux (G18) and Liouville
  for a general Hamiltonian flow (G5). Those keep the marker `TERM-SCOPE(Hamiltonian)`.

## Fubini–Study

* **Means here (backed):** the measure `fubiniStudyMeasure p₀` on `ℂℙ^{N−1}`, defined as the
  Haar-on-`U(N)` pushforward.
* **Backed by:** `fubiniStudyMeasure_unique` — it is the *unique* `U(N)`-invariant probability
  measure, proved; plus `fubiniStudyMeasure_smul_invariant`.
* **Also backed (2026-09-08/10):** it IS the normalised top power of the Kähler form —
  `Projectivization.fsVolumeNormalized_eq_fubiniStudyMeasure` and, with the constant,
  `fsVolume_eq_smul_fubiniStudyMeasure` (`ω_FS^{∧n} = (4π)ⁿ · μ_FS`); and on the sectors,
  `CSD.LF4.unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized` /
  `fsVolumeNormalized_isForcedKahlerVolume` (`LF4/SectorManifold.lean`, W1).
* **Also backed (2026-09-11, G17):** it IS the normalised Riemannian volume of the Fubini–Study
  *metric* — `RiemannianMetric.riemannianVolume` (`Mathlib/Geometry/Manifold/RiemannianVolume.lean`,
  chart Gram densities `√det G` glued along a cover) and ★★★
  `Projectivization.riemannianVolume_fsMetric_eq_smul_fubiniStudyMeasure`
  (`Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`): `vol_g = ((4π)ⁿ/n!) · μ_FS`, via ★★★
  `riemannianVolume_fsMetric` (`vol_g = fsVolume n / n!`, the Kähler identity `vol_g = ω^{∧n}/n!`).
  All three textbook readings of `μ_FS` — unique invariant measure, normalised top power of the Kähler
  form, normalised Riemannian volume of the metric — are now theorems identifying the same measure.
* **Also backed (2026-09-11, Q30 / G17b):** the Riemannian volume is canonical —
  `RiemannianMetric.riemannianVolume_congr_cover` (cover-independence for any bilinear metric family,
  by the Jacobian rule for Gram densities `chartDensity_transition`) and
  `Projectivization.riemannianVolume_fsMetric_congr_cover` (`vol_g = fsVolume n / n!` for every
  cover). Not stated: basis-independence of the Gram construction, and that isometries preserve
  `riemannianVolume`; nothing consumes either. Marker: `TERM-SCOPE(Kahler)` where that reading is
  used.
* ⚠️ **Since CR-4 (2026-09-06) the Born headlines no longer route through it.** The dependency cone
  of `globalBasin_born` contains **no** `fubiniStudyMeasure`: the fibred route is
  `epistemicMeasure = Dirac ⊗ Haar`, the basin measure is a torus-cell width, and the value is the
  moment map. `μ_FS` stays load-bearing for the **ontic** law (`kMuL = μ_FS ⊗ vol`, and
  `kMuL_unique`), for the retained base-side engines, and for the bridge
  `globalBasin_toReal_eq_bornRegion_toReal`. So this gap is inherited by the *justification* of the
  typicality law, not by the Born *computation*.

## smooth

* **Means here (backed):** `ContDiff`. Every `smooth`-named declaration has a `contDiff_*`
  companion (`contDiff_smoothClampDiv`, `contDiff_smoothPointerRamp`).
* ⚠️ **Historical note, resolved:** the smooth-witness ramp ingredients were once Lipschitz and
  proved only `Continuous`; the `Real.smoothTransition` upgrade landed 2026-08-03. Do not
  reintroduce "smooth" for a merely continuous profile.

## completely positive

* **Means here (backed):** `id ⊗ Φ` maps PSD to PSD for every finite ancilla.
* **Backed by:** `lindbladSemigroup_completelyPositive` (`LF6/LindbladPositivity.lean`), with the
  `id ⊗ Φ` identification closed by `idTensor_lindbladSemigroup` (Q23).

## unique / the only

* **Means here:** a genuine uniqueness claim requires `∃!` or an equality derived from an
  arbitrary object satisfying the hypotheses — e.g. `fubiniStudyMeasure_unique`,
  `rankOneDensity_unique_of_certainty`.
* ⚠️ **Not guarded, deliberately.** A scan for docstrings claiming uniqueness without `∃!` in the
  statement returns 34 hits that are almost all ordinary English ("the only nonalgebraic fact used
  below", "the only caller-supplied hypothesis"). A guard here would be noise. Reviewers should
  still read these; a machine should not gate them.

## exhaustive

* **Means here:** nothing claims it. The live use is the measurement **trilemma**, where
  exhaustiveness is explicitly *open, not claimed* (`Q13`, research-rated).

## canonical

* **Means here:** "the standard choice", carrying little mathematical content. 38 declarations use
  it; the risk is low and no marker is required. Flagged here so that a future reader does not
  mistake its frequency for a defect.

---

## The marker

`TERM-SCOPE(<Term>)` in a module docstring declares: *this module uses the restricted sense of
`<Term>`, and the gap above is understood.* `scripts/check-terms.sh` requires it wherever the
restricted vocabulary appears, and ratchets against `docs/terms-baseline.txt` so the unmarked
count can shrink and never grow.

**This is not a licence to use the strong sense.** The marker records that the author knew; it
does not make the claim true. Where the strong sense is actually asserted as a result, that is a
`check-claim-provenance` matter, not a marker.
