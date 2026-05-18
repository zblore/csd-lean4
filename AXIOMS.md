# AXIOMS.md

Axiom audit for the `csd-lean4` formalisation. This file is the canonical record of every external mathematical input the Lean tree depends on, every physical assumption it does not formalise, and every item deferred to LF4 or later. The intent is intellectual honesty: a reader should be able to see, in one place, exactly what the corpus is and is not claiming about the Lean tree.

## 1. Lean foundational axioms (always present)

Every Mathlib-dependent Lean development uses these three axioms. They are inspected via `#print axioms` on any defined term and are not separately listed in theorem-level docstrings.

| Axiom | Role |
|---|---|
| `propext` | Propositional extensionality: equivalent propositions are equal. |
| `Classical.choice` | The (non-constructive) axiom of choice. |
| `Quot.sound` | Soundness of quotient-type formation. |

LF1 and LF3 theorems (including all LF3 chain capstones) cite only these three. `#print axioms LF1_main_theorem_ae`, `#print axioms LF3_singlet_frequency_convergence_born_inner`, and similar checks return the foundational triple only.

## 2. LF2 imported mathematical axioms

LF2 imports three named axioms. Each is documented at its declaration site with a docstring linking back to the spec section that authorises the import. None propagates into LF1; LF3's chain capstones likewise do not depend on any of the three (the singlet is concretely given as a Hilbert vector, not extracted from a Busch operational package).

### 2.1 `invariant_measure_uniqueness`

**Location.** `CsdLean4/LF2/MeasureBridge.lean`.

**Statement.** For an abstract measurable space `P` with a measurable `G`-action that is **transitive** (`htrans : ∀ p q : P, ∃ g, action g p = q`), a `G`-invariant probability measure `μFS` on `P`, and any `G`-invariant finite measure `μ` on `P`, there exists `c : ENNReal` with `μ = c · μFS`.

**Transitivity is required.** Without `htrans` the statement is false: take `P = {0, 1}`, `G` trivial, `μFS = uniform`, `μ = δ_0`. Both are invariant under the trivial action; no `c` satisfies `δ_0 = c · uniform`. The axiom as previously stated (prior to commit fixing this) had no transitivity hypothesis and was therefore technically inconsistent, even though no proof in the tree exploited it. The fix adds `htrans` to the axiom signature and supplies it from a new `epAction_transitive` field on `SectorData`.

**Mathematical content.** Uniqueness of the `G`-invariant probability measure up to scaling on a homogeneous `G`-space. Concretely, in the CSD model: the `SU(N)`-invariant Borel probability measure on `CP^{N-1}` is unique (Fubini-Study). The standard proof requires compactness of `G` (or an equivalent regularity property) in addition to transitivity; the spec authorises the import for the concrete `SU(N)`-on-`CP^{N-1}` setting where compactness holds.

**Spec authorisation.** Paper B §7.4 explicitly carves this out as an imported result. The corpus treats the uniqueness as a structural input rather than reformalising it.

**Mathlib status.** Not currently in Mathlib at the abstract-measurable-space level required. The concrete `SU(N)`-on-`CP^{N-1}` instance is Haar-measure-on-compact-homogeneous-space material; Mathlib has Haar measure on topological groups but the quotient construction is not yet packaged at the required level.

**Discharge target.** When the corresponding Mathlib infrastructure lands, swap `axiom` for `theorem`-via-import. The current signature carries transitivity explicitly so that the eventual replacement theorem has matching hypotheses; concrete LF4 instantiation supplies `epAction_transitive` from the `SU(N)`-on-`CP^{N-1}` model.

### 2.2 `busch_effect_gleason`

**Location.** `CsdLean4/LF2/BornWrapper.lean`.

**Statement.** For `N ≥ 2` and an effect-additive operational package `OP` on `Effect N`, there is a unique density operator `ρ` such that `OP.p E = traceForm ρ E` for every effect `E`.

**Mathematical content.** The Busch effect-Gleason theorem (Busch 2003): effect-additive probability assignments on a finite-dimensional effect algebra are realised by a unique trace-form density.

**Spec authorisation.** Paper B §7.4 directs LF2 to import this rather than rederive.

**Mathlib status.** Not in Mathlib. Effect-algebra / POVM machinery is an open Mathlib gap; the full proof requires Busch 2003's argument.

**Discharge target.** Same as above: signature is stable; the axiom becomes a theorem when the Mathlib infrastructure is in place.

### 2.3 `rankOneDensity_unique_of_certainty`

**Location.** `CsdLean4/LF2/BornWrapper.lean`.

**Statement.** A density operator `ρ` with `traceForm ρ (rankOneEffect ψ hψ) = 1` is `rankOneDensity ψ hψ`.

**Mathematical content.** Standard linear-algebra corollary of the spectral theorem: if `ρ` is a density operator with `⟨ψ, ρψ⟩ = 1`, then `ρ = |ψ⟩⟨ψ|`. The proof routes through `ρ² ≤ ρ` for densities and Cauchy-Schwarz, giving `ρψ = ψ`; trace-one then forces `ρ` to vanish on `ψ^⊥`.

**Spec authorisation.** Not spec-mandated. This is a provable matrix fact axiomatised pending Mathlib spectral-theorem integration (the proof sketch is in the module docstring).

**Mathlib status.** The spectral theorem for Hermitian matrices is in Mathlib (`Matrix.IsHermitian.spectralTheorem`), but the PSD functional-calculus boilerplate needed for the cleanest proof is uneven. Hence the axiomatisation for v1.00.

**Discharge target.** This is an LF4-or-earlier task that does not require external infrastructure beyond what is already in Mathlib. See [`specs/LF4-todo.md`](specs/LF4-todo.md) §4 for the pickup notes.

## 3. Physical assumptions not formalised

Beyond Mathlib's axioms and LF2's three imports, the formalisation carries several physical assumptions as structural data on its types rather than as named axioms. They are honest assumptions about which class of mathematical objects the corpus is talking about; they are not derived inside the Lean tree.

### 3.1 `OnticSetup.μL` is a finite measure (carries D1)

`μL` is a structural field of `OnticSetup`. The Lean tree does not derive `μL` from a symplectic / Kähler volume form on `Σ`. The class of `OnticSetup`s the corpus cares about is `μL`-preserving deterministic flows, but the Lean abstraction is wider: it works for any measurable `Φ` and any finite `μL`. The LF1 frequency theorem is therefore strictly more general than the physical reading suggests.

This is the **D1 debt** in the corpus's labelling (the preparation-measure origin problem in Paper A's framing). Discharge target: LF4 instantiation of `SigmaSpace` as a compact Kähler manifold, with `μL` constructed from the Kähler volume form.

### 3.2 `OnticSetup.hΦ_pres` is structural payload (not consumed)

The Liouville-preservation field `MeasurePreserving Φ μL μL` is carried for physical admissibility of the ontic model. Grep across the corpus confirms LF1, LF2, and LF3 consume only the measurability content of `Φ` (extracted via `measurable_Φ`); the preservation content is never invoked. Liouville's theorem is in the type but not in the proofs.

This becomes load-bearing only when LF4 derives `μL` from a volume form (whereupon `hΦ_pres` follows from Hamilton's equations and ceases to be a stipulation).

### 3.3 `SectorData.(π, G)` is A5 structural data

The projection `π : SigmaSpace → P` and the symmetry group `G` are taken as structural fields with only the two coherence conditions (`μL`-invariance of the ontic action, `π`-equivariance) constraining them. Nothing forces `π` to project onto the quantum-effective sector specifically, and nothing forces `G = SU(N)`. The natural reading is `G = SU(N)` acting on `Σ` via the lift of its action on `CP^{N-1}`, with `π` the standard projection, but no field forces this.

This is the **A5 debt**: the physical motivation for the quantum-effective sector assumption is a load-bearing external input. Concrete instantiation is [`specs/LF4-todo.md`](specs/LF4-todo.md) §8.

### 3.4 `LeakageCompat` parameters `εA`, `εB` are stipulated (carries V ≈ 1 − I)

The finite-leakage stability theorems take `εA`, `εB` as caller-supplied stability parameters; they are not derived from any physical isolation quantity. The bound `εA + εB + εA·εB` matches the V ≈ 1 − I phenomenology to leading order, but the link from per-side leakages to an underlying isolation parameter is not formalised.

This carries the **V ≈ 1 − I debt** explicitly. Structural discharge is gated on the TN0 V ≈ 1 − I forwarding remark being authored, which is far-future.

### 3.5 `MeasurementUnitary.action` is impulsive-readout data

The eigenstate-action field of `MeasurementUnitary` (the impulsive-readout idealisation `u (jointEig (s, t) φA φB) = jointEig (s, t) (ptrTransA s φA) (ptrTransB t φB)`) is caller-supplied. Spec §9.5 explicitly carves this out of v1.00: the operator-exponential `exp(-iHt)` derivation requires Mathlib-level Stone-on-bounded-self-adjoint-operators infrastructure and is LF4-or-later.

### 3.6 `PureSingletPreparation` bundle on the LF3 chain capstones

The three LF3 chain capstones consume a `PureSingletPreparation D ctx` structure (`CsdLean4/LF3/PurePreparation.lean`) bundling the projective outcome family, its ontic correspondence, and the Born identity
`projectiveWeight D μprep (O_st s t) = ENNReal.ofReal (P_st ctx.a ctx.b s t)`
as a single typed argument. This is the LF1↔LF2↔LF3 boundary in packaged form. The transitional constructor `PureSingletPreparation.ofHypothesis` accepts the raw field set for callers who already have an `hLF2`-style equality.

LF4 will discharge the bundle structurally via the preparation-to-Hilbert correspondence + projective-first outcome specification (`specs/LF4-todo.md` §2 + §7), supplying a concrete constructor `PureSingletPreparation.ofKählerPreparation` from a Kähler `SectorData` instantiation (per `specs/LF4-todo.md` §8, the Q1 answer of 2026-05-17). Per the Q4 answer of 2026-05-17, this is a **rewrite** of the capstone bodies, not a wrap: when LF4 lands, the `ofHypothesis` transitional constructor is retired and the LF4 constructor becomes the single entry point.

This bundle is a hypothesis structure, not an axiom: callers must supply the discharge content. It is listed here for the same reason as the other physical-assumption entries: it is load-bearing for the chain capstones and not derived inside the Lean tree.

## 4. Deferred items (LF4 and later)

Nine concrete items are tracked in [`specs/LF4-todo.md`](specs/LF4-todo.md). The summary:

**Group A: chain closure** (priority for LF4)
- §2 Preparation-to-Hilbert-vector correspondence (discharges 3.6 above).
- §3 Rank-1 effects from projective points (currently parameterised by unit vectors).
- §7 Projective-first outcome specification (discharges 3.6 above).
- §8 Concrete `(SigmaSpace, P, G)` instantiation (discharges 3.1, 3.2, 3.3 above for the `SU(N)` / `CP^{N-1}` case).

**Group B: axiom and OperationalPackage refinement**
- §1 Unitary covariance clause of `OperationalPackage` (spec Def 5.1 clause 3).
- §4 Prove `rankOneDensity_unique_of_certainty` from the spectral theorem (discharges 2.3 above).
- §5 Prove the two spec-mandated axioms 2.1 and 2.2 (Mathlib-scale, far-future).
- §6 `σ`-additivity vs finite additivity of `OperationalPackage`.

**Group C: housekeeping**
- §9 Unify `MeasurablePartition` with LF1's intersect-full-measure sketch (discharges the partition-type gap noted in the LF1 `Outcomes.lean` docstring).

LF5 territory: outcome-conditioned update and sequential circuits. Out of scope for AXIOMS.md until the layer is on the roadmap in concrete form.

## 5. What `#print axioms` reports

For each headline exported theorem, the legible axiom citation:

| Theorem | `#print axioms` output |
|---|---|
| `LF1_main_theorem_ae` | `propext, Classical.choice, Quot.sound` |
| `LF1_main_theorem_projective` | `propext, Classical.choice, Quot.sound` |
| `lf1_weight_eq_projective_weight` | `propext, Classical.choice, Quot.sound` |
| `measure_bridge` | `propext, Classical.choice, Quot.sound, invariant_measure_uniqueness` |
| `born_quadratic` | `propext, Classical.choice, Quot.sound` |
| `pure_state_born_weights` | `propext, Classical.choice, Quot.sound` |
| `pure_state_born_weights_of_certainty` | `propext, Classical.choice, Quot.sound, busch_effect_gleason, rankOneDensity_unique_of_certainty` |
| `LF3_main_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_finite_leakage_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_born` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_born_inner` | `propext, Classical.choice, Quot.sound` |
| `PureSingletPreparation.ofHypothesis` | `propext, Classical.choice, Quot.sound` |
| `ProjectorAlgebra.ofTensorEmbedding` | `propext, Classical.choice, Quot.sound` |
| `MeasurementUnitary.ofUnitaryTensorEmbedding` | `propext, Classical.choice, Quot.sound` |

Run `#print axioms <theorem-name>` in any Lean session to verify directly.

## 6. LF3 structural-data carve-outs

LF3 imports **no** axioms beyond Lean's foundational set, but it does take certain structural facts as fields of caller-supplied data rather than as derived theorems. These are not axioms in Lean's sense (they do not appear in `#print axioms` output), but they are load-bearing inputs that downstream proofs consume without verifying. Listed here so the corpus is honest about which v1.00 results are stability-from-assumption rather than stability-from-first-principles.

### 6.1 `LeakageCompat.branchWeight_dev`

**Location.** `CsdLean4/LF3/Projectors/BranchWeight.lean`.

**What it is.** A field of the `LeakageCompat` structure asserting that the operator-form branch weight deviates from `‖cAmp s t‖²` by at most `εA + εB + εA·εB`.

**What it should be (v2).** A theorem derived from a concrete tensor decomposition of `H_SA` plus per-side overlap bounds (Cauchy-Schwarz on the wrong-pointer leakage mass). Spec §9.7 / §9.11.

**Why it matters.** `LF3_finite_leakage_theorem` is a triangle-inequality over `Sign × Sign` summing this field with appropriate prefactors. It is therefore a packaging theorem from this assumption, not a derivation from projector / pointer / Hamiltonian hypotheses.

**Status.** v1.00 carries the deviation bound as caller-supplied data; v2 should derive it. Tracked in the LF3 design-choices section of README and in `specs/LF4-todo.md`.

### 6.2 `PureSingletPreparation.weight_eq_P_st`

**Location.** `CsdLean4/LF3/PurePreparation.lean`.

**What it is.** A field of the `PureSingletPreparation` bundle asserting that the LF2 projective weight of the pointer-sector outcome region equals `ENNReal.ofReal (P_st a b s t)`.

**What it should be (LF4).** A theorem derived from the chain `branchWeight_eq_LF2_Born` + `lf1_weight_eq_projective_weight` + `cst_squared_eq` once LF4 supplies a concrete preparation-to-Hilbert correspondence (LF4-todo §2 + §7).

**Why it matters.** The three LF3 frequency-convergence capstones consume this field directly. The "chain" listed in the LF3 Interface module docstring is what `weight_eq_P_st` *will* be derived from in LF4, not what the proof bodies currently invoke.

**Status.** v1.00 carries the identity as caller-supplied bundle field via the transitional `PureSingletPreparation.ofHypothesis` constructor. LF4 supplies a structural constructor `PureSingletPreparation.ofKählerPreparation` that derives the field.
