# AXIOMS.md

Axiom audit for the `csd-lean4` formalisation. This file is the canonical record of every external mathematical input the Lean tree depends on, every physical assumption it does not formalise, and every item deferred to LF4 or later. The intent is intellectual honesty: a reader should be able to see, in one place, exactly what the corpus is and is not claiming about the Lean tree.

## 0. Three kinds of "axiom" (read this first)

"Axiom" is used loosely, and three categories are easy to conflate. They are not the same kind of thing, and only one of them is a commitment of the physical theory:

1. **Lean foundational axioms** (§1) — `propext`, `Classical.choice`, `Quot.sound`. Every Mathlib development carries these. Not a commitment of CSD.
2. **Imported mathematical results** (§2) — standard theorems not yet in Mathlib, imported as `axiom`. **These are formalisation debt, not commitments of the physical theory** — each is provable in principle and eliminable as the library grows. There is now **exactly one**: the Busch effect-Gleason theorem. The second, invariant-measure uniqueness, was **removed 2026-06-04** — nothing downstream used the abstract statement that carried it, and its concrete `ℂℙ^{N-1}` content is a proved, axiom-free theorem in the tree (§2.1).
3. **CSD's physical postulates** (§3) — the ontic substrate, the deterministic measure-preserving flow, the sector posit, and the typicality reading of probability. **These are what the theory actually asks you to accept.** They are carried as *hypotheses / structure fields*, not `axiom` declarations, because CSD's claims are conditional ("given an ontic substrate with these properties, repeated-trial frequencies converge to the Born weight"). Consequently `#print axioms` never reports them — correctly, because they are antecedents, not axioms.

**So `#print axioms` measures categories 1 and 2 (Lean + library), not category 3 (the physics).** The number "one imported axiom" is a statement about library completeness, *not* about what CSD commits you to. The figure that describes the theory is **category 3**: the ontic substrate + the sector posit + typicality, with the **Born rule now a theorem** of those (Gleason-free, general dimension, including general POVMs) rather than a postulate. Categories 1 and 2 are infrastructure — the triple is unavoidable, the single remaining imported result is an eliminable library gap confined to the operational stratum, and it is **not** in the ontic Born derivation.

## 1. Lean foundational axioms (always present)

Every Mathlib-dependent Lean development uses these three axioms. They are inspected via `#print axioms` on any defined term and are not separately listed in theorem-level docstrings.

| Axiom | Role |
|---|---|
| `propext` | Propositional extensionality: equivalent propositions are equal. |
| `Classical.choice` | The (non-constructive) axiom of choice. |
| `Quot.sound` | Soundness of quotient-type formation. |

LF1 theorems cite only these three. LF3's strong-readout and finite-leakage main theorems (`LF3_main_theorem`, `LF3_finite_leakage_theorem`) cite only these three. **The LF3 chain capstones** (`LF3_singlet_frequency_convergence`, `_born`, `_born_inner`, plus their joint-partition variants from Phase 8) **also cite only these three** since the 2026-06-02 re-route: the chain bridge now goes through the Busch-free ontic volume step (`OP_p_at_jointEig_eq_P_st_direct` via `born_rank_one_direct`), not through `pure_state_born_weights_of_certainty`. (Pre-2026-06-02 revisions of this file recorded the capstones as Busch-carrying; that was true of the option (B) chain as first landed and is no longer the case — see §2.2 and the per-theorem table in §5.)

## 2. Imported mathematical results (formalisation debt, not theory commitments)

These are standard mathematical theorems imported as `axiom` only because they are not yet in Mathlib (see §0, category 2). They are *not* commitments of CSD: each is provable in principle, and `invariant_measure_uniqueness` (§2.1) is already eliminable, its concrete content being a proved axiom-free theorem in the tree. Neither is in the ontic Born derivation.

LF2 now imports **exactly one** such result — `busch_effect_gleason` (§2.2); the invariant-measure-uniqueness import (§2.1) was **removed 2026-06-04** (see §2.1). LF4 introduces **no** axioms (the Duistermaat–Heckman pushforward formerly carried in §2.3 was discharged 2026-05-31 and is now a foundational-triple theorem). `busch_effect_gleason` is documented at its declaration site and propagates into the LF3 chain capstones only via the operational stratum: it enters extensionally through `pure_state_born_weights_of_certainty` inside the OP.p Born identity step. The ontic Born derivation (the volume-frequency route) is Gleason-free. LF3's `LF3_main_theorem` and `LF3_finite_leakage_theorem` remain axiom-clean, as do the LF3 chain capstones after the 2026-06-02 Busch re-route.

A third axiom, `rankOneDensity_unique_of_certainty`, was carried in earlier
revisions and discharged on 2026-05-18 (see commit landing the
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff` route in
`CsdLean4/LF2/BornWrapper.lean`). It is now a proved theorem; the LF4-todo §4
entry has been retired.

### 2.1 `invariant_measure_uniqueness` — REMOVED 2026-06-04

**Status: NO LONGER AN AXIOM.** The axiom, the abstract `measure_bridge` lemma that was its only consumer, and the convenience constructor `MeasureBridgeData.ofSectorData` were all deleted from `CsdLean4/LF2/MeasureBridge.lean` and `Preparation.lean`. Nothing downstream used the abstract statement: the concrete instances realise the measure bridge `π∗μL = c • μFS` **axiom-free** (`CSD.LF4.cp_measure_bridge`, `k_measure_bridge`, `c = 1`), and the `ℂℙ^{N-1}` uniqueness the abstract version would have needed is itself a proved, axiom-free theorem (`Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn`, §2.1 below). The corpus's only remaining imported axiom is `busch_effect_gleason`. The historical record is retained below.

**Former statement.** For an abstract measurable space `P` with a `MulAction G P` whose action is pretransitive (`[MulAction.IsPretransitive G P]`), a `G`-invariant probability measure `μFS` on `P`, and any `G`-invariant finite measure `μ` on `P`, there exists `c : ENNReal` with `μ = c · μFS`.

**Transitivity is required.** Without `IsPretransitive`, the statement is false: take `P = {0, 1}`, `G` trivial, `μFS = uniform`, `μ = δ_0`. Both are invariant under the trivial action; no `c` satisfies `δ_0 = c · uniform`. The axiom as initially stated (prior to commit `1943d26`) had no transitivity hypothesis and was therefore technically inconsistent, even though no proof in the tree exploited it. Commit `1943d26` added an explicit `htrans` field; a subsequent refactor replaced `action : G → P ≃ᵐ P` plus the raw `htrans` with the Mathlib-idiomatic `[MulAction G P] [MulAction.IsPretransitive G P]` typeclass arguments. `SectorData` carries the matching typeclass instances and a per-`g` measurability field (`measurable_smul_P`).

**Mathematical content.** Uniqueness of the `G`-invariant probability measure up to scaling on a homogeneous `G`-space. Concretely, in the CSD model: the `SU(N)`-invariant Borel probability measure on `CP^{N-1}` is unique (Fubini-Study). The standard proof requires compactness of `G` (or an equivalent regularity property) in addition to transitivity; the spec authorises the import for the concrete `SU(N)`-on-`CP^{N-1}` setting where compactness holds.

**Spec authorisation.** The spec explicitly carves this out as an imported result; the corpus treats the uniqueness as a structural input rather than reformalising it.

**Mathlib status.** Not currently in Mathlib at the abstract-measurable-space level required. The concrete `SU(N)`-on-`CP^{N-1}` instance is Haar-measure-on-compact-homogeneous-space material; Mathlib has Haar measure on topological groups but the quotient construction is not yet packaged at the required level.

**Concrete realisation PROVED (2026-05-24).** The axiom's *content* for the `CP^{N-1}` / `U(N)` instantiation is now a proved, axiom-free theorem in the Mathlib-side projectivization tree: `Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn` (`CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`) reproduces the axiom's `∃ c, μ = c • μFS` conclusion for `P := ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `G := Matrix.unitaryGroup (Fin N) ℂ` (with the reference point made explicit), built from `fubiniStudyMeasure_unique` plus `invariant_finiteMeasure_eq_smul_fubiniStudy` (the finite-measure normalisation step). Both cite only the foundational triple; AxiomAudit-pinned.

This does **not** discharge the abstract axiom: as stated over an arbitrary pretransitive `(P, G)` with no topology, the axiom is deliberately stronger than any provable theorem (it omits the compactness/regularity hypotheses the classical result needs — see the declaration docstring), so the concrete theorem cannot prove it. What changed is that the mathematical core is no longer an open problem; only the wiring remains.

**Discharge target.** When LF4 instantiates `SectorData` with `P := ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `G := U(N)`, `μFS := fubiniStudyMeasure p₀`, the concrete `measure_bridge` routes through `invariant_measure_uniqueness_cpn` instead of the axiom, and the LF2 axiom count drops from two to one at that instantiation site. The current abstract signature carries transitivity explicitly so the concrete instantiation supplies `epAction_transitive` from the `SU(N)`-on-`CP^{N-1}` model with matching hypotheses.

### 2.2 `busch_effect_gleason`

**Location.** `CsdLean4/LF2/BornWrapper.lean`.

**Statement.** For `N ≥ 2` and an effect-additive operational package `OP` on `Effect N`, there is a unique density operator `ρ` such that `OP.p E = traceForm ρ E` for every effect `E`.

**Mathematical content.** The Busch effect-Gleason theorem (Busch 2003): effect-additive probability assignments on a finite-dimensional effect algebra are realised by a unique trace-form density.

**Spec authorisation.** The spec directs LF2 to import this rather than rederive it.

**Mathlib status.** Not in Mathlib. Effect-algebra / POVM machinery is an open Mathlib gap; the full proof requires Busch 2003's argument.

**Discharge target.** Same as above: signature is stable; the axiom becomes a theorem when the Mathlib infrastructure is in place.

### 2.3 `fs_moment_pushforward_uniform` (LF4 Duistermaat–Heckman, qubit instance) — DISCHARGED 2026-05-31

**Status: NO LONGER AN AXIOM.** Now a foundational-triple **theorem**
`CSD.LF4.fs_moment_pushforward_uniform` in `CsdLean4/LF4/MomentUniform.lean`.
`DuistermaatHeckman.lean` no longer introduces any axiom; **LF4 introduces no axioms.**

**Statement.** `(fun p => momentMap p 0)∗ fubiniStudyMeasure p₀ = volume.restrict (Set.Icc 0 1)` on `CPN 2 = ℂℙ¹` — the moment-map coordinate pushes the Fubini–Study measure to the uniform measure on the moment polytope `[0,1]`. The `N = 2` Duistermaat–Heckman / Archimedes hat-box fact.

**How it was discharged (plan B; `specs/plan-b-detail.md`).** Identify `fubiniStudyMeasure` with the Gaussian-induced measure on `ℂℙ¹` (`gaussianCP_eq_fubiniStudy`, Part 1: `μ_FS` is the unique `U(2)`-invariant probability measure, and the projectivised standard Gaussian is `U(2)`-invariant), then compute the moment marginal by a change of variables: `‖·‖²∗ N(0,I₂) = Exp(1/2)` (Slice 1, polarCoord), the block-product/independence step (Slice 2), the ratio→uniform crux through the diffeo `Ψ(T,S) = (T·S,(1−T)·S)` (Slice 3, Jacobian determinant `S` + radial `Gamma 2 = 1`), and the `Fin 4 → ℝ ≃ (ℝ²)²` reindex bridge (Slice 4, `finSumFinEquiv`). Foundational-triple-only throughout.

**Consequence.** `fs_born_volume_ratio_qubit_uncond` and `qubit_born_frequency_convergence_uncond` (moved to `MomentUniform.lean`) are now foundational-triple-only — Born derived from the Kähler volume for the qubit with **no** named geometry axiom and **no** `busch_effect_gleason`. The conditional forms (`fs_born_volume_ratio_qubit`, `qubit_born_frequency_convergence`, with `h_uniform` as an explicit hypothesis) remain available.

### 2.4 General-`N` Duistermaat–Heckman / Born-from-Kähler-volume — CLOSED 2026-06-02 (no axioms)

**Not an axiom; an extension.** The qubit discharge above (§2.3) is extended to all `N`, introducing **no axioms** — every result is foundational-triple-only. Files: `MomentBridgeN.lean`, `MomentDirichletN.lean`, `MomentBornN.lean`, `BornFrequencyN.lean`, and the Cat-1 staging `Mathlib/MeasureTheory/PiCurry.lean`.

- `fs_moment_joint_dirichlet_N` (`MomentDirichletN.lean`): the **joint** DH law `(ratioN ∘ momentMap)∗ μ_FS = M!·vol|_{simplex}` on `ℂℙ^M` (Dirichlet(1,…,1)). This is the general-`N` analogue of the discharged qubit fact — itself a theorem, not an axiom.
- `fs_born_volume_ratio_N` (+ `_apex`) (`MomentBornN.lean`): Born = genuine FS-volume ratio of the barycentric regions, **all `N` coordinates**, unconditional.
- `born_frequency_convergence_N` (`BornFrequencyN.lean`): the general-`N` Busch-free empirical chain — frequencies → the full Born vector jointly a.s. **No `busch_effect_gleason`.**

**Posture note.** This does **not** remove `busch_effect_gleason` (§2.2) from the corpus. It establishes a *parallel, Gleason-free* derivation of the Born weights from the symplectic geometry, at general `N`. As of 2026-06-02 the **LF3 empirical chain was re-routed onto this ontic derivation**: `PureSingletPreparation.weight_eq_P_st` now goes through the Busch-free `OP_p_at_jointEig_eq_P_st_direct`, so the six chain capstones, the LF4 `ofKählerPreparation_singlet_frequency_convergence` capstone, and the Empirical `bell_singlet_frequency_convergence` re-export are all foundational-triple-only. `busch_effect_gleason` is now cited **only by the operational-stratum statements**: `pure_state_born_weights_of_certainty`, `PurePreparation.born_rank_one`, `LF3.OP_p_at_jointEig_eq_P_st`, and `LF4.ontic_born_frequency`. Plan + per-result honesty ledger: `specs/general-n-dh-plan.md`. The only standing axioms remain the two of §2.1–§2.2; **LF4 introduces no axioms.**

#### Foundational reading: two strata, and where the Born weights come from

The corpus reaches the Born weights by two distinct derivations, and they belong to two distinct strata. Keeping both is deliberate.

- **Operational / non-ontic stratum.** Given the Hilbert-space formalism alone, effect-additive probability is forced to the trace form. This is the Gleason-class argument, formalised as the import `busch_effect_gleason` (§2.2). It assumes no configuration space and covers arbitrary effects/POVMs. It is retained here as the operational closure of the formalism.
- **Ontic stratum.** Taking the quantum-effective sector with its symmetry as the primitive, the Born weight is the Fubini–Study volume ratio: the U(N) symmetry fixes `μ_FS` uniquely (axiom-free concretely, via the Haar / FS-uniqueness chain `invariant_measure_uniqueness_cpn`), and the moment map identifies the weight with that volume (`fs_born_volume_ratio_N`). This is the CSD-native derivation (LF2 → LF3 → LF4). It is **foundational-triple-only** and does **not** use `busch_effect_gleason`.

**This is a relocation of the primitive, not its elimination.** The ontic derivation does not produce Born from nothing; it produces Born from the posited sector symmetry. That posit is the sector structural datum (§3.3): `SectorData.(π, G)`, the projection onto the quantum-effective sector and its U(N) symmetry. So the honest hierarchy is:

> **Born as a volume ratio**: dischargeable now, for rank-1 projective measurements at general `N`, **modulo the sector posit** — the projective case is now a theorem.
> **The `(π, G)` sector posit (§3.3)**: the residual primitive the ontic derivation rests on. Not discharged in LF4; LF4 instantiates the canonical `(π, G)` and proves Born for it.
> **The underlying dynamics**: the sector posit would itself follow from a derivation of the sector/volume from the deterministic flow. **Measurement dynamics is now exercised at the single-system projective tier** (LF5, complete 2026-06-11: the de-isolation flow `Φ_vN ≠ id`, FS measure-preserving, realises the Naimark dilation and its pointer-block volumes/frequencies are Born — `measurement_flow_born_frequency`). What stands independent is the sector posit itself: the concrete `SectorData` instances still carry `Φ = id`, and deriving the sector from the dynamics (with the entangled/non-local de-isolation tier behind it) remains the deepest open question.

The payoff is real and stateable without overclaim: in the ontic stratum the Born rule is a **theorem of the posited sector symmetry**, not an independent probability postulate. The cost is named: the primitive moves from operational effect-additivity (Gleason) to the geometric sector posit, and the question "why this sector" becomes a question about the underlying deterministic dynamics.

**Scope: the POVM step is closed (2026-06-03).** The ontic derivation covers rank-1 **projective** (von Neumann) measurements **and general POVMs**. The POVM case routes through **Naimark dilation** (`LF4/POVMNaimark.lean` `canonicalNaimark`, the dilation built from the CFC square roots `√Eᵢ = cfc Real.sqrt Eᵢ`, inhabiting `NaimarkDilation P` for every POVM) onto a larger ontic configuration space `Σ' = ℂℙ^{N·|ι|−1}`, where the achieved general-`N` result reads the POVM Born weight `⟨ψ,Eᵢψ⟩` as a **sum of Fubini–Study volumes** (`povm_born_eq_dilated_volume`) and the empirical chain lands `povm_born_frequency_volume` — carving-free, Gleason-free, unconditional. So the ontic stratum now stands alone for **arbitrary** quantum measurements, and `busch_effect_gleason` is no longer on the ontic Born path for *either* projective or POVM measurements; it survives only as the operational-stratum closure (§2.2). Honest cost: the POVM derivation **enlarges the posited sector structure** by the ancilla on `Σ'` (the apparatus/environment). The genericity assumption (`hpos`, no vanishing dilated amplitude) carried by the original forms was **retired 2026-06-11** by the unconditional engine (`LF4/BornRegionUncond.lean`, `*_uncond` variants — every unit state, vanishing amplitudes included; additive, originals untouched). See `specs/povm-plan.md`.

## 3. CSD's physical postulates (the theory's actual commitments)

**This is the category that describes the theory** (see §0, category 3): what CSD asks you to accept. The Born rule is *not* here — it is a theorem of these postulates (Gleason-free, general dimension, general POVMs). The postulates are carried as structural data / hypotheses on the types rather than as `axiom` declarations, because CSD's claims are conditional on the ontic substrate existing with these properties; so they do not appear in `#print axioms`. The load-bearing ones are the **ontic substrate** (§3.1, §3.2: a measure space `(Σ, μL)` with a deterministic, measure-preserving flow `Φ`), the **sector posit** (§3.3: the projection `π` onto the quantum-effective sector and its symmetry `G`), and the **typicality reading** (probability *is* `μL`-volume ratio, the interpretive posit that LF1's repeated-trial law encodes and the strong law shows self-consistent). The deepest open item is the **dynamical origin of the sector**: deriving `π` / the outcome regions / `Φ` from the dynamics rather than positing them (the LF5 measurement flow `Φ_vN ≠ id` is exercised at the single-system projective tier as of 2026-06-11, but the concrete `SectorData` instances still carry `Φ = id` and the sector itself remains posited). These are honest assumptions about which class of mathematical objects the corpus is talking about; they are not derived inside the Lean tree.

### 3.1 `OnticSetup.μL` is a finite measure (preparation-measure origin)

`μL` is a structural field of `OnticSetup`. The Lean tree does not derive `μL` from a symplectic / Kähler volume form on `Σ`. The class of `OnticSetup`s the corpus cares about is `μL`-preserving deterministic flows, but the Lean abstraction is wider: it works for any measurable `Φ` and any finite `μL`. The LF1 frequency theorem is therefore strictly more general than the physical reading suggests.

This is the **preparation-measure-origin assumption**. Discharge target: LF4 instantiation of `SigmaSpace` as a compact Kähler manifold, with `μL` constructed from the Kähler volume form (and, beyond that, the flow `Φ` itself derived rather than asserted — a theory-level question).

### 3.2 `OnticSetup.hΦ_pres` is structural payload (not consumed)

The Liouville-preservation field `MeasurePreserving Φ μL μL` is carried for physical admissibility of the ontic model. Grep across the corpus confirms LF1, LF2, and LF3 consume only the measurability content of `Φ` (extracted via `measurable_Φ`); the preservation content is never invoked. Liouville's theorem is in the type but not in the proofs.

This becomes load-bearing only when LF4 derives `μL` from a volume form (whereupon `hΦ_pres` follows from Hamilton's equations and ceases to be a stipulation).

### 3.3 `SectorData.(π, G)` is posited structural data

The projection `π : SigmaSpace → P` and the symmetry group `G` are taken as structural fields with only the two coherence conditions (`μL`-invariance of the ontic action, `π`-equivariance) constraining them. Nothing forces `π` to project onto the quantum-effective sector specifically, and nothing forces `G = SU(N)`. The natural reading is `G = SU(N)` acting on `Σ` via the lift of its action on `CP^{N-1}`, with `π` the standard projection, but no field forces this.

This is the **sector-posit assumption**: the physical motivation for the quantum-effective sector is a load-bearing external input. Concrete instantiation is [`specs/LF4-todo.md`](specs/LF4-todo.md) §8.

### 3.4 `LeakageCompat` parameters `εA`, `εB` are stipulated

The finite-leakage stability theorems take `εA`, `εB` as caller-supplied stability parameters; they are not derived from any physical isolation quantity. The bound `εA + εB + εA·εB` matches the expected visibility-vs-isolation phenomenology to leading order, but the link from per-side leakages to an underlying isolation parameter is not formalised.

This is a stipulated-parameter assumption. Its structural discharge is gated on theory-level work (relating leakage to an isolation parameter) that is far-future.

### 3.5 `MeasurementUnitary.action` is impulsive-readout data

The eigenstate-action field of `MeasurementUnitary` (the impulsive-readout idealisation `u (jointEig (s, t) φA φB) = jointEig (s, t) (ptrTransA s φA) (ptrTransB t φB)`) is caller-supplied. The spec explicitly carves this out of v1.00: the operator-exponential `exp(-iHt)` derivation requires Mathlib-level Stone-on-bounded-self-adjoint-operators infrastructure and is LF4-or-later.

### 3.6 `PureSingletPreparation` bundle on the LF3 chain capstones (Phase 7 option (B) form)

The three LF3 chain capstones consume a `PureSingletPreparation D ctx N` structure (`CsdLean4/LF3/PurePreparation.lean`) bundling, under the option (B) design adopted 2026-05-18:

- The projective reference measure `μFS` + its `IsProbabilityMeasure` instance.
- The measure bridge data `bridge : LF2.MeasureBridgeData D μFS`.
- The static pure preparation `PP : LF2.PurePreparation D prepMeasure N` (Hilbert-side ψ + Dirac concentration of `Measure.map D.π prepMeasure` on the projective ray of ψ).
- The dimension bound `hN : 2 ≤ N` (required for `busch_effect_gleason`).
- The measurement-context joint eigenstate data `jed : MeasurementJointEig ctx PP.ψ` (the four (s, t) joint spin eigenstates with unit norm, pairwise distinctness, and the Born identity `‖⟨PP.ψ, jed.eig s t⟩‖² = P_st ctx.a ctx.b s t`).
- The per-sector ontic outcome regions `O_region : Sign → Sign → D.toOntic.OutcomeRegion`.
- The **ontic weight ↔ OP.p bridge** `bridge_op_p : ∀ s t, prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))` where `OP = LF2.OperationalPackage.fromPreparation D μFS bridge prepMeasure PP.rep PP.hrep_unit PP.hrep_meas`.

This is the LF1↔LF2↔LF3 boundary in packaged form. The transitional constructor `PureSingletPreparation.ofHypothesis` accepts the raw field set for callers who already have an `hLF2`-style equality (rewritten to match the new field set during Phase 7).

The convenience theorem `PureSingletPreparation.weight_eq_P_st` composes `bridge_op_p` with `LF3.OP_p_at_jointEig_eq_P_st_direct` (the Busch-free, direct volume-ratio Born step via `LF2.PurePreparation.born_rank_one_direct`) to give the full ontic weight ↔ `P_st` identity. The chain capstones consume this composed form and are therefore foundational-triple-only (re-routed off Busch 2026-06-02; the Busch-mediated `OP_p_at_jointEig_eq_P_st` is retained as the operational-stratum statement).

LF4 will discharge the bundle structurally via the preparation-to-Hilbert correspondence + projective-first outcome specification (`specs/LF4-todo.md` §2 + §7), supplying a concrete constructor `PureSingletPreparation.ofKählerPreparation` from a Kähler `SectorData` instantiation (per `specs/LF4-todo.md` §8, the Q1 answer of 2026-05-17). Per the Q4 answer of 2026-05-17, this is a **rewrite** of the capstone bodies, not a wrap: when LF4 lands, the `ofHypothesis` transitional constructor is retired and the LF4 constructor becomes the single entry point.

This bundle is a hypothesis structure, not an axiom: callers must supply the discharge content. It is listed here for the same reason as the other physical-assumption entries: it is load-bearing for the chain capstones and not derived inside the Lean tree.

### 3.7 The SigmaLayer (the projective-sector ontology, Paper C) ledger (P1–P9, B1–B7, T1–T16)

**The canonical postulate ledger of the Σ-layer** (`CsdLean4/SigmaLayer/`, namespace `CSD.SigmaLayer`), quoted from `CsdLean4/SigmaLayer/Adapters.lean`. Like every other category-3 entry, NONE of these is an `axiom` declaration: the core postulates are carried as **structure fields / hypotheses**, the bridges are named assumptions discharged for concrete models, and the theorem targets are `Prop` predicates whose inhabitants are proved theorems. `#print axioms` therefore reports only the foundational triple on every SigmaLayer result. The Σ-layer is built to strict anti-circularity discipline: no Born weight, frequency claim, Fubini–Study equality, projected unitary dynamics, or Schrödinger equation is ever a structure field.

**Core ontic postulates (structure fields).** P1 measurable constraint surface `Σ` (`ConstraintSurface`). P2 finite Liouville measure `μL` (`ConstraintDynamics.muL`). P3 deterministic real-parameter flow forming a one-parameter group (`ConstraintDynamics.flow`, `flow_zero`, `flow_add`). P4 the flow preserves `μL` (`flow_preserves`). P5 records = measurable, contextual, time-indexed regions (`RecordSemantics`; genuinely time-indexed via `SigmaLayer/TimeIndexedRecord.lean`). P6 isolation = conditioning `μL` on the record-compatible region (`HistoryPreparation`, `conditionalMeasure_apply`; post-outcome update `PostMeasurement.appendFact`). P7 the pure-state target is `CP^{N-1}` (`ProjectiveState`). P8 a measurable projection `π : Σ → CP^{N-1}` (`ProjectiveSector.pi`). P9 `π` need not be injective (many-to-one supported).

**Bridge assumptions (named, discharged for concrete models).** B1 `π_* μL = μFS` (`HasFubiniStudyPushforward`; proved `productSector_hasFubiniStudyPushforward`). B2 projectability (`ProjectiveDynamicsBridge.projectable`). B3 unitary/Hamiltonian realisation of the projected flow (`HasUnitaryRealisation`/`HasHamiltonianRealisation`). B4/B5 de-isolation measurement realises measurable a.e.-complete outcome regions / the record matches the outcome region (`DeisolationModel`, `vnDeisolationModel_records`). B6 composite = tensor structure (`CompositeSector.tensor_dimension`; the "why ⊗" derivation P3-parked by standing instruction). B7 repeated experiments satisfy an independent-trial or ergodic hypothesis (`TrialWitness` / `IsErgodicForOutcomeRegions`).

**Theorem targets (never unconditional postulates; `Prop` predicates, inhabited by proofs).** T1 Born from volume; T2 Born from independent-trial frequencies; T3 Born from deterministic-flow frequencies; T4 unitary projected dynamics; T5 Schrödinger evolution; T6 unique contextual outcome a.e. (`vnDeisolationModel_ae_total`); T7 general conditional update (`conditionalUpdate_capstone`); T8 Lüders update (`luders_capstone`); T9 mixed-state representation (`mixedState_capstone`, `isPure_iff_trace_sq_one`); T10 POVM by dilation; T11 composite probabilities; T12 entangled predictions; T13 contextuality (`NoNonContextualValuation`); T14 Bell (`NoLocalHiddenVariableTable`, `bell_general_separation`); T15 no-signalling (`HasNoSignalling`, `tensorSector_no_signalling`); T16 two-path interference (`HasBornInterference`). The forward unification (T5 dynamics + T6/measurement + records + Born on ONE `Σ`) is `unified_projectiveSector_capstone` (`SigmaLayer/UnifiedMeasurement.lean`).

**The single remaining deep posit, unchanged by the Σ-layer:** the sector `(π, G)` + Fubini–Study typicality is POSITED, not derived from the deterministic flow (A5 → D1, tracked as `FND-1` in `specs/future-work.md`; the connectivity-manifest link L7). Everything above is FORWARD (consumes the posited sector); the Σ-layer organises and unifies it under a clean ledger and does not close A5.

**Why the OP.p bridge (option (B)) rather than direct projectiveWeight.** The previous (v0.3.4-lf3) bundle had a `weight_eq_P_st : projectiveWeight D μprep (O_st s t) = ENNReal.ofReal P_st` field — direct measure equality on a projective outcome region. Under the Phase 4 Dirac model of `PurePreparation`, `Measure.map D.π μprep = Dirac ray_point`, and the direct measure of a projective outcome region is 0 or 1, not a generic `P_st ∈ (0, 1)`. The OP.p bridge resolves this: probability is the OP-integral of `effectProjFn` (the CSD-foundational object in the volume-ratios reading), and `OP.p (rankOneEffect (jed.eig s t)) = ‖⟨ψ, jed.eig s t⟩‖² = P_st` via `born_rank_one` + the Born identity, both for a Dirac `μprep`. The bridge_op_p field ties the ontic outcome weight to this OP-integral content; concretely, what LF4 discharges is the structural relationship between the ontic outcome region's preEvent volume and the OP integration. The four-ingredient combinatorial framing applies.

## 4. Deferred items (LF4 and later)

Nine concrete items are tracked in [`specs/LF4-todo.md`](specs/LF4-todo.md). The summary:

**Group A: chain closure** (priority for LF4)
- §2 Preparation-to-Hilbert-vector correspondence (discharges 3.6 above).
- §3 Rank-1 effects from projective points (currently parameterised by unit vectors).
- §7 Projective-first outcome specification (discharges 3.6 above).
- §8 Concrete `(SigmaSpace, P, G)` instantiation (discharges 3.1, 3.2, 3.3 above for the `SU(N)` / `CP^{N-1}` case).

**Group B: axiom and OperationalPackage refinement**
- §1 Unitary covariance clause of `OperationalPackage` (spec Def 5.1 clause 3).
- §4 ~~Prove `rankOneDensity_unique_of_certainty` from the spectral theorem~~ — **discharged 2026-05-18**.
- §5 Prove the two spec-mandated axioms 2.1 and 2.2 (Mathlib-scale, far-future).
- §6 `σ`-additivity vs finite additivity of `OperationalPackage`.

**Group C: housekeeping**
- §9 Unify `MeasurablePartition` with LF1's intersect-full-measure sketch (discharges the partition-type gap noted in the LF1 `Outcomes.lean` docstring).

LF5 (measurement dynamics) is now a concrete layer: the single-system projective tier is **complete 2026-06-11..15** (`specs/lf5-plan.md`, layer headline `measurement_flow_born_frequency` — foundational-triple-only, no new axioms, no new structural posits beyond the A5 datum on the dilated sector already recorded in §3.3). **LF5-F (2026-06-15) discharged the per-microstate outcome *function*** (`bornRegion` pairwise disjointness → `vnPointerOutcome` → `measurement_flow_outcome_frequency`). Outcome-*conditioned* update (Lüders / sequential circuits) remains open. The entangled / non-local de-isolation tier is now **first exercised at LF6-A/B** (2026-06-28, `CsdLean4/LF6/`: `no_product_partition_realises_singlet`, `singletDeisolationFlow`, the decoherence/purity-drop witness) — **introducing no new axioms** (foundational-triple-only); the general-`N` entangled tier remains open. The open-system / decoherence empirical 15-series (`Empirical/CSD/{Einselection,QECDecoherence,WeakMeasurement,QuantumZeno,ChannelCapacity}`) and the metrology branch (`Empirical/Metrology/`) likewise add no axioms.

## 5. What `#print axioms` reports

For each headline exported theorem, the legible axiom citation:

| Theorem | `#print axioms` output |
|---|---|
| `LF1_main_theorem_ae` | `propext, Classical.choice, Quot.sound` |
| `LF1_main_theorem_projective` | `propext, Classical.choice, Quot.sound` |
| `lf1_weight_eq_projective_weight` | `propext, Classical.choice, Quot.sound` |
| `measure_bridge` | *(removed 2026-06-04 together with `invariant_measure_uniqueness` — the abstract statement was unused; the concrete instances carry `cp_measure_bridge` / `k_measure_bridge`, foundational-triple-only)* |
| `born_quadratic` | `propext, Classical.choice, Quot.sound` |
| `pure_state_born_weights` | `propext, Classical.choice, Quot.sound` |
| `pure_state_born_weights_of_certainty` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_main_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_finite_leakage_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence` | `propext, Classical.choice, Quot.sound` (re-routed off Busch 2026-06-02) |
| `LF3_singlet_frequency_convergence_born` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_born_inner` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_joint` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_born_joint` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence_born_inner_joint` | `propext, Classical.choice, Quot.sound` |
| `PureSingletPreparation.ofHypothesis` | `propext, Classical.choice, Quot.sound` |
| `PureSingletPreparation.weight_eq_P_st` | `propext, Classical.choice, Quot.sound` (via `OP_p_at_jointEig_eq_P_st_direct`) |
| `LF3.OP_p_at_jointEig_eq_P_st` (operational-stratum, retained) | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF2.PurePreparation.born_rank_one` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF2.PurePreparation.born_rank_one_direct` | `propext, Classical.choice, Quot.sound` |
| `LF2.PurePreparation.OP_certain_at_ψ` | `propext, Classical.choice, Quot.sound` |
| `LF2.SectorData.outcomeOfProjective` | `propext, Classical.choice, Quot.sound` |
| `LF3.OP_p_at_jointEig_eq_P_st` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3.OP_p_at_jointEig_eq_P_st_direct` | `propext, Classical.choice, Quot.sound` |
| `ProjectorAlgebra.ofTensorEmbedding` | `propext, Classical.choice, Quot.sound` |
| `MeasurementUnitary.ofUnitaryTensorEmbedding` | `propext, Classical.choice, Quot.sound` |
| `LF4.momentMap_mk_eq_inner_sq` | `propext, Classical.choice, Quot.sound` |
| `LF4.born_eq_volume_ratio` | `propext, Classical.choice, Quot.sound` |
| `LF4.fs_born_volume_ratio_qubit` (conditional on `h_uniform`) | `propext, Classical.choice, Quot.sound` |
| `LF4.qubit_born_frequency_convergence` (conditional on `h_uniform`) | `propext, Classical.choice, Quot.sound` |
| `LF4.born_frequency_convergence_partition` | `propext, Classical.choice, Quot.sound` |
| `LF4.fs_born_volume_ratio_qubit_uncond` | `propext, Classical.choice, Quot.sound` (DH discharged 2026-05-31) |
| `LF4.qubit_born_frequency_convergence_uncond` | `propext, Classical.choice, Quot.sound` (DH discharged 2026-05-31) |
| `LF4.fs_moment_joint_dirichlet_N` (general-`N` joint DH) | `propext, Classical.choice, Quot.sound` |
| `LF4.fs_born_volume_ratio_N` (+ `_apex`) | `propext, Classical.choice, Quot.sound` |
| `LF4.born_frequency_convergence_N` (general-`N` Busch-free) | `propext, Classical.choice, Quot.sound` |
| `MeasureTheory.measurePreserving_piCurry` / `map_curryProd_pi` (Cat-1 staging) | `propext, Classical.choice, Quot.sound` |
| `LF4.povm_born_frequency_volume` (POVM Born = FS volume) | `propext, Classical.choice, Quot.sound` |
| `LF4.canonicalNaimark` / `povm_born_eq_dilated_volume` | `propext, Classical.choice, Quot.sound` |
| `LF5.measurement_flow_born_frequency` (layer headline) | `propext, Classical.choice, Quot.sound` |
| `LF5.measurement_flow_outcome_frequency` (LF5-F) | `propext, Classical.choice, Quot.sound` |
| `LF6.no_product_partition_realises_singlet` (entangled tier) | `propext, Classical.choice, Quot.sound` |
| `LF6.singletDeisolationFlow` (Φ ≠ id realises the singlet) | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.Einselection.einselection_degenerate_boundary` (15a) | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.QECDecoherence.qec_corrects_decoherence` (15b) | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume` (15c) | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.QuantumZeno.zeno_freezing` (15d) | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.ChannelCapacity.dephasing_classical_vs_quantum` (15e) | `propext, Classical.choice, Quot.sound` |
| `Empirical.Metrology` Ramsey / QFI / Heisenberg (A1–A3) | `propext, Classical.choice, Quot.sound` |

### Empirical-prediction headline theorems

| Theorem | `#print axioms` output |
|---|---|
| `Empirical.Bell.correlation_eq_neg_dot` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.no_signalling_alice` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.no_signalling_bob` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.singlet_marginal_alice` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.singlet_marginal_bob` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.chsh_classical_bound_violated` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.chsh_singlet_at_optimal_angles` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.chsh_singlet_tsirelson_bound` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.chsh_inner_bound` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Bell.chsh_qm_tsirelson_bound` | `propext, Classical.choice, Quot.sound` |
| `Empirical.NoCloning.no_cloning_two_state` | `propext, Classical.choice, Quot.sound` |
| `Empirical.NoCloning.no_universal_cloner_of_witness` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.ghz_norm` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.ghz_expectation_xxx` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.ghz_expectation_xyy` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.ghz_expectation_yxy` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.ghz_expectation_yyx` | `propext, Classical.choice, Quot.sound` |
| `Empirical.GHZ.no_lhv_assignment_for_ghz` | `propext, Quot.sound` (no `Classical.choice` — pure finite-state arithmetic contradiction) |
| `Empirical.KochenSpecker.no_value_assignment_18_9` | `propext, Classical.choice, Quot.sound` |
| `Empirical.KochenSpecker.cabelloBasis_appears_twice` | `propext, Classical.choice, Quot.sound` |
| `Empirical.KochenSpecker.ks_no_value_assignment_cabello18` | `propext, Classical.choice, Quot.sound` |
| `Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis` | `propext, Classical.choice, Quot.sound` |

### Empirical/CSD bridge readings

CSD-side companions to the Empirical/QM/ predictions. The Bell-family
readings re-export LF3 chain capstones; their axiom citations match
the corresponding capstones (`busch_effect_gleason` propagates
extensionally through `OP_p_at_jointEig_eq_P_st`). The no-cloning
reading reduces to QM without invoking Busch.

| Theorem | `#print axioms` output |
|---|---|
| `Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence` | `propext, Classical.choice, Quot.sound` (re-routed off Busch 2026-06-02) |
| `Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle` | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle` | `propext, Classical.choice, Quot.sound` |
| `Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle` | `propext, Classical.choice, Quot.sound` |

Note: the QM-side `Empirical.GHZ.no_lhv_assignment_for_ghz` cites only
`[propext, Quot.sound]` (no `Classical.choice`). The CSD-side
`no_csd_ghz_lhv_bundle` picks up `Classical.choice` from the
existential-bundle destructure (`rintro ⟨_, lambda, ...⟩`), even
though the underlying arithmetic content is unchanged. Same effect
applies to `Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle`
relative to its QM-side counterpart.

### Tranche 1 Tier A gates (added 2026-05-22)

Pure linear-algebra gate identities. All cite the foundational triple
only.

| Theorem | `#print axioms` output |
|---|---|
| `Empirical.QM.Gates.qmH_mul_self` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmS_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmT_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmCNOT_mul_self` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmSWAP_mul_self` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmCZ_mul_self` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmBellPrep_factorisation` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmBellPrep_yields_phiplus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmToffoli_mul_self` | `propext, Classical.choice, Quot.sound` |
| `Empirical.QM.Gates.qmFredkin_mul_self` | `propext, Classical.choice, Quot.sound` |

### Mathlib upstream candidates (Projectivization §12)

These are CSD-free Mathlib-track lemmas staged under
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/`. Any axiom acquisition
would be an upstream regression and a blocker for the eventual Mathlib PR.

| Theorem | `#print axioms` output |
|---|---|
| `Projectivization.continuous_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.isOpenMap_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.isOpenQuotientMap_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.instT2Space` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.instCompactSpace` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.instMeasurableSingletonClass` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.borel_eq_map_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.lift_measurable` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.measurable_iff_measurable_comp_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.continuous_iff_continuous_comp_mk'` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.continuous_lift` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapOfInjective_continuous` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapEquiv` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapEquiv_continuous` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapEquiv_continuous_of_finiteDim` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapEquiv_one` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.mapEquiv_mul` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.instMulAction` | `propext, Classical.choice, Quot.sound` |
| `Projectivization.instContinuousConstSMul` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.toEuclideanLinearEquiv` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.toEuclideanLinearEquivHom` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instProjectivizationMulAction` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instProjectivizationContinuousConstSMul` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.sum_norm_sq_col` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.val_norm_apply_le_one` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.val_norm_le_one` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instCompactSpace` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instMeasurableSpace` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instBorelSpace` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaar` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaar_isHaarMeasure` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instIsFiniteMeasureUnitaryHaar` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaar_univ_ne_zero` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaar_univ_ne_top` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaarProb` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instIsProbabilityMeasureUnitaryHaarProb` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.unitaryHaarProb_isHaarMeasure` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.toEuclideanLin_apply_continuous` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.orbitMap` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.orbit_map_continuous` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.orbit_map_measurable` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.fubiniStudyMeasure` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.smul_comp_orbitMap` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.fubiniStudyMeasure_smul_invariant` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.exists_unitary_e_zero_eq` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.exists_unitary_map_unit` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.exists_unitary_mapping_nonzero` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.smul_mk_eq_mk` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instIsPretransitive_projectivization` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instContinuousSMul_projectivization` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.instIsMulRightInvariantUnitaryHaarProb` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.haar_orbit_indicator_eq` | `propext, Classical.choice, Quot.sound` |
| `Matrix.UnitaryGroup.fubiniStudyMeasure_unique` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.no_lhv_mermin_peres` | `propext, Quot.sound` |
| `Empirical.MerminPeres.sigmaX_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.sigmaY_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.sigmaZ_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.sigmaX_mul_sigmaY` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.sigmaY_mul_sigmaX` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_R0` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_R1` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_R2` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_C0` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_C1` | `propext, Classical.choice, Quot.sound` |
| `Empirical.MerminPeres.mermin_peres_C2` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.no_lhv_hardy` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQM.hardyAmp_AB` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQM.hardyAmp_A_B'minus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQM.hardyAmp_A'minus_B` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQM.hardyAmp_A'_B'` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQM.exists_hardy_realisation` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.phi_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.phi_cube` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.sqrtPhi_sq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMax_value` | `propext, Classical.choice, Quot.sound` |
| `Empirical.Hardy.HardyQMMax.hardyMax_probability_eq` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_zPlus_zPlus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_zMinus_zPlus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_xPlus_zPlus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_xMinus_zPlus` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_z_basis_complete` | `propext, Classical.choice, Quot.sound` |
| `Empirical.SternGerlach.born_x_basis_complete` | `propext, Classical.choice, Quot.sound` |

Run `#print axioms <theorem-name>` in any Lean session to verify directly.

## 6. LF3 structural-data carve-outs

LF3 imports **no** axioms beyond Lean's foundational set, but it does take certain structural facts as fields of caller-supplied data rather than as derived theorems. These are not axioms in Lean's sense (they do not appear in `#print axioms` output), but they are load-bearing inputs that downstream proofs consume without verifying. Listed here so the corpus is honest about which v1.00 results are stability-from-assumption rather than stability-from-first-principles.

### 6.1 `LeakageCompat.sectorVolume_dev`

**Location.** `CsdLean4/LF3/Projectors/SectorVolume.lean`. (Renamed from `LeakageCompat.branchWeight_dev` in Phase 11, 2026-05-18, to align with the volume-ratios reading.)

**What it is.** A field of the `LeakageCompat` structure asserting that the operator-form sector volume deviates from `‖cAmp s t‖²` by at most `εA + εB + εA·εB`.

**What it should be (v2).** A theorem derived from a concrete tensor decomposition of `H_SA` plus per-side overlap bounds (Cauchy-Schwarz on the cross-sector readout mass).

**Why it matters.** `LF3_finite_leakage_theorem` is a triangle-inequality over `Sign × Sign` summing this field with appropriate prefactors. It is therefore a packaging theorem from this assumption, not a derivation from projector / pointer / Hamiltonian hypotheses.

**Status.** v1.00 carries the deviation bound as caller-supplied data; v2 should derive it. Tracked in the LF3 design-choices section of README and in `specs/LF4-todo.md`.

### 6.2 `PureSingletPreparation.bridge_op_p` and `MeasurementJointEig.born_eq_P_st` (Phase 7 option (B) split)

**Location.** `CsdLean4/LF3/PurePreparation.lean` (the `bridge_op_p` field) and `CsdLean4/LF3/SingletProjective.lean` (the `MeasurementJointEig.born_eq_P_st` field).

**What they are (post-Phase-7 split).** The single `weight_eq_P_st` field in the pre-Phase-7 bundle has been factored into two structurally distinct hypotheses, reflecting the option (B) chain design:

- `MeasurementJointEig.born_eq_P_st : ∀ s t, ‖inner ℂ ψ (eig s t)‖² = P_st ctx.a ctx.b s t` — the **Born identity** for the (s, t) joint eigenstate. Discharge target: LF4-todo §3 (rank-1 effects from projective points) + spectral construction of joint spin eigenstates from `jointSpinProj`. Carried on the measurement-context-driven structure `MeasurementJointEig`, separate from the static pure preparation.
- `PureSingletPreparation.bridge_op_p : ∀ s t, prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (eig s t)))` — the **ontic-weight ↔ OP.p bridge**. Discharge target: LF4-todo §2 (preparation-to-Hilbert correspondence) + §7 (projective-first outcomes). Carried on the singlet bundle, ties the LF1 ontic outcome weight to the LF2 OP integral.

The composition is `PureSingletPreparation.weight_eq_P_st` (a proved theorem on the bundle), which combines `bridge_op_p` with the Busch-free `LF3.OP_p_at_jointEig_eq_P_st_direct` (re-routed 2026-06-02; foundational-triple-only). The three chain capstones consume `weight_eq_P_st` via `LF1_main_theorem_ae` + `ENNReal.toReal_ofReal`.

**What they should be (LF4).** Both fields become theorems derived from a concrete preparation-to-Hilbert correspondence + projective-first outcome specification + spectral construction. LF4-todo §2, §3, §7 are the discharge targets.

**Why this matters.** The Phase 7 split preserves the CSD pure / measurement-context-driven structural separation: the static pure preparation (`PP`) is context-independent; the measurement-context data (`jed`, `O_region`, `bridge_op_p`) depends on the chosen measurement context (a, b). The option (B) chain routes via OP integration (the CSD-foundational content of `effectProjFn`), matching the four-ingredient combinatorial framing.

**Status.** v1.x carries both fields as caller-supplied bundle hypotheses via the transitional `PureSingletPreparation.ofHypothesis` constructor (and `MeasurementJointEig`'s field set, no constructor needed). LF4 supplies a structural constructor that derives both.
