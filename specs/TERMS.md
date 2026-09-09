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
* **NOT established:** analyticity (the potential is only known `C^∞`), and a manifold-level Kähler
  *predicate* packaging `J`, `g` and `ω` on `ℂℙⁿ` (`specs/generator-layer-scoping.md`, G7 — cosmetic,
  the triple is proved pointwise). Marker: `TERM-SCOPE(Kahler)`.

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
  **NOT established:** existence of `X_H` from non-degeneracy (G2/G3), smoothness of `torusField` as
  a section, and the arena statement `R-016`. Marker: `TERM-SCOPE(Hamiltonian)`.
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
* **Established for the torus flow (2026-09-09, G10):** `Projectivization.fsVolume_map_torusUnitary_smul` and `measurePreserving_torusUnitary_smul` (`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean`) — every map `p ↦ diag(e^{iθ}) • p`, hence every time-`t` map of the Hamiltonian flow G6 built (`torusUnitary_add_smul` is the group law), preserves `fsVolume n`. Liouville in the dynamics sense for **one** Hamiltonian flow on `ℂℙⁿ`, obtained from unitary invariance (`fsVolume_map_smul`), not from a manifold-level flow theory (G5, not scheduled). `ConstraintDynamics.flow_preserves` (Posit 3) is untouched: the constraint dynamics' measurement pieces are not globally Hamiltonian.
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
* **NOT established:** anything *derived* from the structure — Darboux, the symplectic volume
  (top-power identity), generators of flows on the manifold, moment maps. Those keep the marker
  `TERM-SCOPE(Hamiltonian)` (same wall as the Hamiltonian entry).

## Fubini–Study

* **Means here (backed):** the measure `fubiniStudyMeasure p₀` on `ℂℙ^{N−1}`, defined as the
  Haar-on-`U(N)` pushforward.
* **Backed by:** `fubiniStudyMeasure_unique` — it is the *unique* `U(N)`-invariant probability
  measure, proved; plus `fubiniStudyMeasure_smul_invariant`.
* **NOT established:** that it is the normalised Riemannian volume of the Fubini–Study *metric*,
  or the top power of the Kähler form. Cited as background, not as a corpus result (see the
  glossary entry `fubini-study-measure`). Marker: `TERM-SCOPE(Kahler)` where that reading is used.
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
