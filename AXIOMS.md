# AXIOMS.md

Axiom audit for the `csd-lean4` formalisation. This file is the canonical record of every external mathematical input the Lean tree depends on, every physical assumption it does not formalise, and every item deferred to LF4 or later. The intent is intellectual honesty: a reader should be able to see, in one place, exactly what the corpus is and is not claiming about the Lean tree.

## 1. Lean foundational axioms (always present)

Every Mathlib-dependent Lean development uses these three axioms. They are inspected via `#print axioms` on any defined term and are not separately listed in theorem-level docstrings.

| Axiom | Role |
|---|---|
| `propext` | Propositional extensionality: equivalent propositions are equal. |
| `Classical.choice` | The (non-constructive) axiom of choice. |
| `Quot.sound` | Soundness of quotient-type formation. |

LF1 theorems cite only these three. LF3's strong-readout and finite-leakage main theorems (`LF3_main_theorem`, `LF3_finite_leakage_theorem`) cite only these three. **The three LF3 chain capstones** (`LF3_singlet_frequency_convergence`, `_born`, `_born_inner`, plus their joint-partition variants from Phase 8) cite the foundational triple **plus** `busch_effect_gleason` — see §2.2 below and the option (B) chain rewrite in §3.6 for the rationale (the chain now routes via OP.p Born identity, which extensionally invokes the Busch axiom through `pure_state_born_weights_of_certainty`).

## 2. LF2 imported mathematical axioms

LF2 imports two named axioms. Each is documented at its declaration site with a docstring linking back to the spec section that authorises the import. Neither propagates into LF1. Both propagate into the LF3 chain capstones after the 2026-05-18 option (B) chain rewrite: `busch_effect_gleason` enters extensionally via `pure_state_born_weights_of_certainty` inside the OP.p Born identity step, and `invariant_measure_uniqueness` enters at any LF4 instantiation site that constructs `MeasureBridgeData` via `MeasureBridgeData.ofSectorData` (the option (b) structural propagation mechanism — the axiom does not appear extensionally on the chain capstone definitions themselves because the bridge enters as a generic structure argument). LF3's `LF3_main_theorem` and `LF3_finite_leakage_theorem` remain axiom-clean.

A third axiom, `rankOneDensity_unique_of_certainty`, was carried in earlier
revisions and discharged on 2026-05-18 (see commit landing the
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff` route in
`CsdLean4/LF2/BornWrapper.lean`). It is now a proved theorem; the LF4-todo §4
entry has been retired.

### 2.1 `invariant_measure_uniqueness`

**Location.** `CsdLean4/LF2/MeasureBridge.lean`.

**Statement.** For an abstract measurable space `P` with a `MulAction G P` whose action is pretransitive (`[MulAction.IsPretransitive G P]`), a `G`-invariant probability measure `μFS` on `P`, and any `G`-invariant finite measure `μ` on `P`, there exists `c : ENNReal` with `μ = c · μFS`.

**Transitivity is required.** Without `IsPretransitive`, the statement is false: take `P = {0, 1}`, `G` trivial, `μFS = uniform`, `μ = δ_0`. Both are invariant under the trivial action; no `c` satisfies `δ_0 = c · uniform`. The axiom as initially stated (prior to commit `1943d26`) had no transitivity hypothesis and was therefore technically inconsistent, even though no proof in the tree exploited it. Commit `1943d26` added an explicit `htrans` field; a subsequent refactor replaced `action : G → P ≃ᵐ P` plus the raw `htrans` with the Mathlib-idiomatic `[MulAction G P] [MulAction.IsPretransitive G P]` typeclass arguments. `SectorData` carries the matching typeclass instances and a per-`g` measurability field (`measurable_smul_P`).

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

The convenience theorem `PureSingletPreparation.weight_eq_P_st` composes `bridge_op_p` with `LF3.OP_p_at_jointEig_eq_P_st` (Phase 6 algebraic identity, cites `busch_effect_gleason` via `LF2.PurePreparation.born_rank_one`) to give the full ontic weight ↔ `P_st` identity. The chain capstones consume this composed form.

LF4 will discharge the bundle structurally via the preparation-to-Hilbert correspondence + projective-first outcome specification (`specs/LF4-todo.md` §2 + §7), supplying a concrete constructor `PureSingletPreparation.ofKählerPreparation` from a Kähler `SectorData` instantiation (per `specs/LF4-todo.md` §8, the Q1 answer of 2026-05-17). Per the Q4 answer of 2026-05-17, this is a **rewrite** of the capstone bodies, not a wrap: when LF4 lands, the `ofHypothesis` transitional constructor is retired and the LF4 constructor becomes the single entry point.

This bundle is a hypothesis structure, not an axiom: callers must supply the discharge content. It is listed here for the same reason as the other physical-assumption entries: it is load-bearing for the chain capstones and not derived inside the Lean tree.

**Why the OP.p bridge (option (B)) rather than direct projectiveWeight.** The previous (v0.3.4-lf3) bundle had a `weight_eq_P_st : projectiveWeight D μprep (O_st s t) = ENNReal.ofReal P_st` field — direct measure equality on a projective outcome region. Under the Phase 4 Dirac model of `PurePreparation`, `Measure.map D.π μprep = Dirac ray_point`, and the direct measure of a projective outcome region is 0 or 1, not a generic `P_st ∈ (0, 1)`. The OP.p bridge resolves this: probability is the OP-integral of `effectProjFn` (the CSD-foundational object in the volume-ratios reading), and `OP.p (rankOneEffect (jed.eig s t)) = ‖⟨ψ, jed.eig s t⟩‖² = P_st` via `born_rank_one` + the Born identity, both for a Dirac `μprep`. The bridge_op_p field ties the ontic outcome weight to this OP-integral content; concretely, what LF4 discharges is the structural relationship between the ontic outcome region's preEvent volume and the OP integration. Spec §5.4 four-ingredient combinatorial framing applies.

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
| `pure_state_born_weights_of_certainty` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_main_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_finite_leakage_theorem` | `propext, Classical.choice, Quot.sound` |
| `LF3_singlet_frequency_convergence` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_inner` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_joint` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_joint` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3_singlet_frequency_convergence_born_inner_joint` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `PureSingletPreparation.ofHypothesis` | `propext, Classical.choice, Quot.sound` |
| `PureSingletPreparation.weight_eq_P_st` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF2.PurePreparation.born_rank_one` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF2.PurePreparation.born_rank_one_direct` | `propext, Classical.choice, Quot.sound` |
| `LF2.PurePreparation.OP_certain_at_ψ` | `propext, Classical.choice, Quot.sound` |
| `LF2.SectorData.outcomeOfProjective` | `propext, Classical.choice, Quot.sound` |
| `LF3.OP_p_at_jointEig_eq_P_st` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
| `LF3.OP_p_at_jointEig_eq_P_st_direct` | `propext, Classical.choice, Quot.sound` |
| `ProjectorAlgebra.ofTensorEmbedding` | `propext, Classical.choice, Quot.sound` |
| `MeasurementUnitary.ofUnitaryTensorEmbedding` | `propext, Classical.choice, Quot.sound` |

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
| `Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence` | `propext, Classical.choice, Quot.sound, busch_effect_gleason` |
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

Run `#print axioms <theorem-name>` in any Lean session to verify directly.

## 6. LF3 structural-data carve-outs

LF3 imports **no** axioms beyond Lean's foundational set, but it does take certain structural facts as fields of caller-supplied data rather than as derived theorems. These are not axioms in Lean's sense (they do not appear in `#print axioms` output), but they are load-bearing inputs that downstream proofs consume without verifying. Listed here so the corpus is honest about which v1.00 results are stability-from-assumption rather than stability-from-first-principles.

### 6.1 `LeakageCompat.sectorVolume_dev`

**Location.** `CsdLean4/LF3/Projectors/SectorVolume.lean`. (Renamed from `LeakageCompat.branchWeight_dev` in Phase 11, 2026-05-18, to align with the volume-ratios reading.)

**What it is.** A field of the `LeakageCompat` structure asserting that the operator-form sector volume deviates from `‖cAmp s t‖²` by at most `εA + εB + εA·εB`.

**What it should be (v2).** A theorem derived from a concrete tensor decomposition of `H_SA` plus per-side overlap bounds (Cauchy-Schwarz on the cross-sector readout mass). Spec §9.7 / §9.11.

**Why it matters.** `LF3_finite_leakage_theorem` is a triangle-inequality over `Sign × Sign` summing this field with appropriate prefactors. It is therefore a packaging theorem from this assumption, not a derivation from projector / pointer / Hamiltonian hypotheses.

**Status.** v1.00 carries the deviation bound as caller-supplied data; v2 should derive it. Tracked in the LF3 design-choices section of README and in `specs/LF4-todo.md`.

### 6.2 `PureSingletPreparation.bridge_op_p` and `MeasurementJointEig.born_eq_P_st` (Phase 7 option (B) split)

**Location.** `CsdLean4/LF3/PurePreparation.lean` (the `bridge_op_p` field) and `CsdLean4/LF3/SingletProjective.lean` (the `MeasurementJointEig.born_eq_P_st` field).

**What they are (post-Phase-7 split).** The single `weight_eq_P_st` field in the pre-Phase-7 bundle has been factored into two structurally distinct hypotheses, reflecting the option (B) chain design:

- `MeasurementJointEig.born_eq_P_st : ∀ s t, ‖inner ℂ ψ (eig s t)‖² = P_st ctx.a ctx.b s t` — the **Born identity** for the (s, t) joint eigenstate. Discharge target: LF4-todo §3 (rank-1 effects from projective points) + spectral construction of joint spin eigenstates from `jointSpinProj`. Carried on the measurement-context-driven structure `MeasurementJointEig`, separate from the static pure preparation.
- `PureSingletPreparation.bridge_op_p : ∀ s t, prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (eig s t)))` — the **ontic-weight ↔ OP.p bridge**. Discharge target: LF4-todo §2 (preparation-to-Hilbert correspondence) + §7 (projective-first outcomes). Carried on the singlet bundle, ties the LF1 ontic outcome weight to the LF2 OP integral.

The composition is `PureSingletPreparation.weight_eq_P_st` (a proved theorem on the bundle), which combines `bridge_op_p` with `LF3.OP_p_at_jointEig_eq_P_st` (Phase 6) and cites `busch_effect_gleason`. The three chain capstones consume `weight_eq_P_st` via `LF1_main_theorem_ae` + `ENNReal.toReal_ofReal`.

**What they should be (LF4).** Both fields become theorems derived from a concrete preparation-to-Hilbert correspondence + projective-first outcome specification + spectral construction. LF4-todo §2, §3, §7 are the discharge targets.

**Why this matters.** The Phase 7 split preserves the CSD pure / measurement-context-driven structural separation: the static pure preparation (`PP`) is context-independent; the measurement-context data (`jed`, `O_region`, `bridge_op_p`) depends on the chosen measurement context (a, b). The option (B) chain routes via OP integration (the CSD-foundational content of `effectProjFn`), matching spec §5.4 four-ingredient framing.

**Status.** v1.x carries both fields as caller-supplied bundle hypotheses via the transitional `PureSingletPreparation.ofHypothesis` constructor (and `MeasurementJointEig`'s field set, no constructor needed). LF4 supplies a structural constructor that derives both.
