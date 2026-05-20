# LF4 TODO: items deferred from LF2

Items LF2 deliberately left for LF4, with rationale and concrete pickup notes.

## 1. Unitary covariance clause of OperationalPackage (spec Def 5.1 clause 3)

**Status:** LF2 omits the `unitary_covariance` field. `Effect.conjugateBy` is in place as the structural helper.

**Why deferred:** Two readings of spec clause 3, and the wrong one over-constrains:

- **Invariance reading** — `p (Effect.conjugateBy U E) = p E` for all U. Rules out pure-state packages.
- **Covariant reading** — a functor `OperationalPackage.conjugateBy U : OperationalPackage N → OperationalPackage N` with `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)`. Mathematically correct, type-heavy.

**Pickup:**
1. Implement `OperationalPackage.conjugateBy` as a function producing a new package.
2. Prove the structure fields (nonneg, le_one, total_one, additivity) carry through conjugation. Most reduce to applying `Effect.conjugateBy` inside and invoking the original field.
3. `total_one` requires showing `Effect.conjugateBy U Effect.one = Effect.one` (since `U† · 1 · U = 1` for unitary `U`).
4. `additivity` requires `Effect.conjugateBy U (Effect.add E F hLe) = Effect.add (conjugateBy U E) (conjugateBy U F) hLe'` for some derived `hLe'`. Distributivity of conjugation over matrix addition closes it.
5. Once the functor is in place, state a covariance theorem: `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)` — tautological by construction.

**Depends on:** `Matrix.unitaryGroup` (already imported in LF2), `Effect.conjugateBy` (LF2).

---

## 2. Preparation-to-Hilbert-vector correspondence — **PARTIAL (pre-LF4 Phase 4 + Phase 7, 2026-05-18)**

**Status:** Substantial structural progress. Pre-LF4 work landed:

- `LF2.PurePreparation` (`CsdLean4/LF2/Preparation.lean`, Phase 4) carries the static pure-preparation data: `ψ` (unit vector), `rep : P → EuclideanSpace ℂ (Fin N)` (caller-supplied projective representative), `ray_point : P`, `rep_at_ray : rep ray_point = ψ`, and the Dirac concentration `push_dirac : Measure.map D.π μprep = Measure.dirac ray_point`.
- `LF2.PurePreparation.born_rank_one` and `LF2.PurePreparation.born_rank_one_direct` (Phase 4) prove `OP.p (rankOneEffect φ hφ) = ‖⟨ψ, φ⟩‖²` for the OP built by `OperationalPackage.fromPreparation`.
- `LF3.PureSingletPreparation` (`CsdLean4/LF3/PurePreparation.lean`, Phase 7) rewrote the LF3 chain bundle in option (B) form: carries `LF2.PurePreparation` + `MeasurementJointEig` + ontic outcome regions + the **ontic-weight ↔ OP.p bridge** `bridge_op_p` as the new LF4 discharge target.

**Design-space decision (resolved 2026-05-18).** Option (b) of the 2026-05-17 design discussion (bundle the discharge into a preparation structure) was adopted. Option (a) — permanent hypothesis — was ruled out per the 2026-05-17 decision. Option (c) — Born-ready typeclass — was rejected at pre-LF4 plan time on ergonomic grounds.

**Remaining LF4 work (the actual discharge):**

1. Specialise LF2's abstract `P` to `Projectivization ℂ (EuclideanSpace ℂ (Fin N))` (waits on §12: `Projectivization` topology / measure API).
2. Construct `LF2.PurePreparation` from a concrete preparation `μprep` whose pushforward `Measure.map D.π μprep` concentrates Dirac on `[ψ]`. This is the **`bridge_op_p` discharge proper**: in a concrete `(Σ, π, Φ, μprep)` instantiation, prove
   `prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t) _))`.
3. Construct `LF3.PureSingletPreparation.ofKählerPreparation` from a concrete Kähler `SectorData` (per §8).

The Phase 4 + 7 work staged the *structural shape* of the chain. The actual measure-theoretic content discharging `bridge_op_p` is LF4 work pending §8 + §12. See also `specs/pre-LF4-plan.md` for the full execution log.

---

## 3. Rank-1 effects from projective points (not from unit vectors) — **PARTIAL (pre-LF4 Phase 1, 2026-05-18)**

**Status:** Step 1 (phase invariance) **DONE**. Steps 2-3 (projective-point lifts) deferred to LF4 + §12 (`Projectivization` topology API).

Pre-LF4 Phase 1 delivered (`CsdLean4/LF2/PhaseInvariance.lean`):

- `outerProduct_phase_invariant : ‖c‖ = 1 → outerProduct (c • φ) = outerProduct φ` — the algebraic phase invariance of the outer product. Algebraic content: `(c • φ) ⊗ (c • φ)* = c · c̄ · (φ ⊗ φ*) = ‖c‖² · (φ ⊗ φ*) = φ ⊗ φ*`.
- `rankOneEffect_phase_invariant` and `rankOneDensity_phase_invariant` — phase invariance of the structure-level wrappers.

Additionally, the LF3 measurement-context bundle (`LF3.MeasurementJointEig`, Phase 6) is parametric in the abstract joint eigenstate vectors rather than requiring projective points; it stages the projective lift as an LF4-discharge target without committing to a `Projectivization` realisation pre-LF4.

**Remaining LF4 work:**

2. Lift to projective points: for `[φ] : Projectivization ℂ (EuclideanSpace ℂ (Fin N))`, define `rankOneEffectProj [φ]` via `Projectivization.lift` + `outerProduct_phase_invariant`. Waits on §12 (Mathlib `Projectivization.lift` measurability API).
3. Similarly for `rankOneDensityProj`.

**Depends on:** §12 (`Projectivization` topology / measure API as a Cat-1 Mathlib contribution).

---

## 4. Prove `rankOneDensity_unique_of_certainty` (remove axiom) — DISCHARGED 2026-05-18

**Status:** Proved in `CsdLean4/LF2/BornWrapper.lean`. Axiom retired; the
declaration is now a `theorem`. AxiomAudit regression updated to drop the
axiom from `pure_state_born_weights_of_certainty`'s `#print axioms` output.

**How discharged.** The route avoided the spectral theorem entirely:

1. **Trace-form to inner-product equation.** `traceForm ρ (rankOneEffect ψ hψ) = 1`
   unfolds to `RCLike.re ((ρ.M * outerProduct ψ).trace) = 1`. Hermitian-product
   trace is real (`Tr(AB)` = `Tr((AB)ᴴ)*` = `Tr(BA)`), so the imaginary part
   is zero and `(ρ.M * P).trace = (1 : ℂ)` outright.
2. **`(I − P) ρ (I − P)` is PSD with trace zero.** Trace cyclicity plus
   `(I − P)² = (I − P)` gives `Tr((I−P) ρ (I−P)) = Tr(ρ) − Tr(ρ · P) = 1 − 1 = 0`.
   `Matrix.PosSemidef.trace_eq_zero_iff` collapses this to `(I − P) ρ (I − P) = 0`.
3. **`ρ · (I − P) = 0`.** Apply `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`
   to `ρ.M` (which is PSD): for any v, `star (Qv) ⬝ᵥ ρ Qv = star v ⬝ᵥ Q ρ Q v = 0`,
   so `ρ Qv = 0` for all v; hence `ρ · Q = 0` (via `Matrix.ext_iff_mulVec`).
4. **`ρ = ρ · P = P · ρ · P`.** Subtraction + Hermitian-adjoint reasoning.
5. **Rank-1 sandwich.** `P · M · P = Tr(M · P) • P` for any `M`, proved
   entry-wise from the `vecMulVec` definition of `outerProduct`. With
   `Tr(ρ · P) = 1`, we get `ρ = 1 • P = P = outerProduct ψ`. Structure
   equality closes.

The key Mathlib infrastructure used: `Matrix.PosSemidef.trace_eq_zero_iff`,
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`, `Matrix.ext_iff_mulVec`,
`Matrix.vecMulVec_apply` + `Finset.sum_comm`. No spectral theorem; no CFC
sqrt; no `Star (Matrix _ _ _ →L[ℂ] _)` synthesis. This makes the proof
robust to the typeclass landscape at Lean 4.29.0-rc8.

**Note for future archaeology.** Earlier scaffolding in the module docstring
sketched a CFC sqrt route. That route would have worked if Matrix had a
`NonUnitalContinuousFunctionalCalculus ℝ (Matrix _ _ _) IsSelfAdjoint`
instance, but Mathlib does not synthesize this for `Matrix (Fin N) (Fin N) ℂ`
under our context. The PSD inner-product route above bypasses the issue.

---

## 5. Prove the two spec-mandated axioms (long-term)

**Status:** `invariant_measure_uniqueness` and `busch_effect_gleason` remain axioms. Spec §7.4 accepts this.

**Why deferred:** Each is a Mathlib-scale contribution.

- `invariant_measure_uniqueness` — Haar measure on compact homogeneous spaces (`SU(N)/U(N-1) ≅ CP^{N-1}`). Mathlib has Haar on topological groups; the quotient/homogeneous-space case requires more work. Months of Mathlib contribution.

- `busch_effect_gleason` — effect-algebra infrastructure (not currently in Mathlib), plus Busch 2003's proof. Larger task; full effect-algebra / POVM machinery is an open Mathlib gap.

**Pickup:**
- Both remain axioms until Mathlib integration makes them theorems. When one lands, swap `axiom` for `theorem`-via-import in LF2. Signatures are already in the right shape — no downstream changes needed.

---

## 6. σ-additivity vs finite additivity of OperationalPackage

**Status:** LF2 encodes only finite additivity (pairwise). Busch's original result uses σ-additivity.

**Why deferred:** In finite dimension the distinction is usually inessential — the effect algebra is "compact enough" that finite additivity implies σ-additivity. But we haven't verified this formally.

**Pickup:**
1. Before LF4 attempts to *prove* `busch_effect_gleason` (rather than import), verify: in finite dim, finite additivity + other Def 5.1 clauses imply σ-additivity.
2. If yes, no code change needed. If no, weaken `OperationalPackage.additivity` to a `σ`-additive form over countable effect families.

---

## 7. Outcome specification: ontic-first vs projective-first — **DONE (pre-LF4 Phase 5, 2026-05-18)**

**Status:** Both pickup items delivered in `CsdLean4/LF2/Interface.lean` (Phase 5).

- `SectorData.outcomeOfProjective : {Oep : Set P} → MeasurableSet Oep → D.toOntic.OutcomeRegion` constructs the ontic outcome region with `Ω := D.π ⁻¹' Oep`.
- `SectorData.outcomeOfProjective_preEvent` discharges the correspondence: under the **flow-projection compatibility** hypothesis `h_flow_π : ∀ x, D.π (D.toOntic.Φ x) = D.π x` (CSD's constraint-surface preservation reading — the ontic flow preserves projective rays), the constructor-built outcome's pre-event equals `D.π ⁻¹' Oep` exactly. Callers of `LF1_main_theorem_projective` no longer need to supply `hCorresp` manually for the constructor-built outcome.
- `SectorData.outcomeOfProjective_weight_eq_projectiveWeight` gives the full weight-side identity by composition with `lf1_weight_eq_projective_weight`.

The flow-projection compatibility hypothesis `h_flow_π` is taken as a constructor argument rather than a `SectorData` field; adding it as a field would commit all `SectorData` instances to the constraint-surface reading at v1.x. LF4 instantiations may elect to promote it to a structural field.

All three exports are foundational-axiom-only; `#guard_msgs` regressions in AxiomAudit pin them.

---

## 8. Concrete SigmaSpace / P / G instantiation

**Status:** LF2's `SectorData` is abstract in `(SigmaSpace, P, G)`. LF4 will want a concrete realisation.

**Pickup:**
1. In LF4, take `SigmaSpace := ` a specific phase space (or continue abstract).
2. `P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` with `[Fintype (Fin N)]`, `[DecidableEq (Fin N)]`.
3. `G := Matrix.specialUnitaryGroup (Fin N) ℂ` (or `Matrix.unitaryGroup` for the full unitary case).
4. Construct the Fubini–Study measure `μFS` as a probability measure on `P` (concretely: via the normalised round measure on the sphere, pushed forward through the quotient `S^{2N-1} → CP^{N-1}`).
5. Verify the invariance / equivariance hypotheses of `SectorData`.

**Depends on:** `Mathlib.LinearAlgebra.Projectivization.Basic`, `Matrix.specialUnitaryGroup` (if available; otherwise construct), the quotient measure theory for compact groups.

---

## 9. Unify `MeasurablePartition` (LF2) with LF1's "intersect full-measure sets" sketch

**Status:** LF1's `OutcomeRegion` formalises one measurable region at a time; the joint almost-sure statement for a finite partition is sketched in the LF1 docstring as "apply the theorem once per element and intersect the resulting full-measure sets" but not written as a lemma. LF2's `Weights.lean` defines `MeasurablePartition` as the partition object the LF1 docstring defers. The two are not yet linked.

**Why deferred:** LF1 deliberately avoided introducing a partition type ("a partition type may become necessary at LF2/LF4 for POVM completeness", per the LF1 `Outcomes.lean` docstring). LF2 introduced `MeasurablePartition` for projective-weight normalisation. The link, "given a `MeasurablePartition`, the LF1 joint almost-sure convergence statement follows from per-element applications of `LF1_main_theorem_ae`", was not written because LF1's frequency theorem is for a single region and no LF2/LF3 consumer needed the joint version.

**Pickup:**
1. In LF4, write a lemma `MeasurablePartition.LF1_joint_convergence` consuming an LF2 `MeasurablePartition π_part` and an LF1 `TrialModel` and yielding the joint almost-sure convergence statement: `∀ᵐ ω, ∀ i, Tendsto (T.empiricalFreq (partElement i) · ω) atTop (nhds (partElement i).weightReal)`.
2. The proof is finite-intersection-of-full-measure-sets, exactly as the LF1 docstring sketches. No new mathematics; just write down the lemma.
3. Once written, the LF3 chain capstones that currently apply `LF1_main_theorem_ae` once per `(s, t) ∈ Sign × Sign` can route through this lemma instead.

**Depends on:** nothing structural; LF1 and LF2 already provide all ingredients. This is bookkeeping that LF4 should land before consuming joint-partition statements at scale.

---

## 10. Framework/ extraction candidates (post-CONVENTIONS.md adoption)

**Status:** All current LF1/LF2/LF3 modules are tagged `Category: 3-Local` per `CONVENTIONS.md`. The initial pass classified by current location, not conceptual category. Several modules are conceptually Cat-2 (framework-level, CSD-adjacent but reusable beyond CSD) and should be extracted to `CsdLean4/Framework/` when LF4 needs them in CSD-free form.

This section is a punch list of the specific modules to consider for extraction, surfaced by the 2026-05-18 OpenAI Codex CLI review. Do not bulk-refactor; reclassify a module only when LF4 has a concrete consumer that needs it CSD-free.

### 10.1 `LF2/BornWrapper.lean` — split into Cat-1 and Cat-2

The matrix lemmas (`outerProduct_posSemidef`, `traceForm`, `mul_conj` and related rank-1 matrix identities) are Cat-1: pure linear-algebra facts on `Matrix (Fin N) (Fin N) ℂ`, no CSD content. They belong at `CsdLean4/Mathlib/LinearAlgebra/Matrix/RankOne.lean` (or a similar Mathlib-natural path) eventually.

The structural machinery (`Effect`, `DensityOperator`, `OperationalPackage`, `rankOneEffect`, `rankOneDensity`, `born_quadratic`) is Cat-2: it encodes the operational-package interface and the Born quadratic form for finite-dimensional effect algebras. Any formalisation programme that needs the Born wrapper would consume this; it does not depend on CSD's ontic typicality story.

**Pickup:**
1. Identify which lemmas are pure matrix algebra vs which carry operational-package structure. Most pure-matrix lemmas are at the top of the file; the `Effect`/`DensityOperator`/`OperationalPackage` block starts further down.
2. Move the Cat-1 lemmas to `CsdLean4/Mathlib/LinearAlgebra/Matrix/RankOne.lean` (or appropriate path). Stage as Mathlib upstream candidates.
3. Move the Cat-2 block to `CsdLean4/Framework/OperationalPackage.lean`. Adjust imports in `LF3/Projectors/LF2Interface.lean` and downstream consumers.

### 10.2 `LF3/Setup.lean::BinaryPointerProjectors` + `LF3/Projectors/Core.lean::ProjectorAlgebra`

`BinaryPointerProjectors` is a framework-level pointer-algebra structure (two-element projective decomposition on an inner-product space). `ProjectorAlgebra` is the corresponding four-element structure for the bipartite case. Together with `StrongReadoutCompat` and `LeakageCompat`, these encode the abstract pointer-readout pattern that any measurement-model formalisation would need — they do not depend on Bell singlet content.

**Pickup:**
1. Move `BinaryPointerProjectors` (and its theorems) to `CsdLean4/Framework/Measurement/BinaryPointer.lean`.
2. Move `ProjectorAlgebra`, `StrongReadoutCompat`, `LeakageCompat` to `CsdLean4/Framework/Measurement/ProjectorAlgebra.lean`.
3. Keep `mHat`, `sectorVolume`, and other LF3-specific consumers in `LF3/Projectors/`. They depend on Framework but stay Cat-3.

### 10.3 `LF3/Projectors/TensorModel.lean::TensorEmbedding`

`TensorEmbedding K_A K_B H_SA` is an abstract bipartite tensor-factor interface (per-wing algebra-homomorphism lifts with commuting images). Not Bell-singlet-specific; usable for any bipartite quantum-system formalisation.

`UnitaryTensorEmbedding` is the same pattern at the unitary-equivalence level.

**Pickup:**
1. Move `TensorEmbedding` and `UnitaryTensorEmbedding` (with their construction lemmas `ProjectorAlgebra.ofTensorEmbedding` and `MeasurementUnitary.ofUnitaryTensorEmbedding`) to `CsdLean4/Framework/TensorProduct/BipartiteEmbedding.lean`.
2. If sufficiently general, these could eventually become Cat-1 — the tensor-product-of-CLM machinery they encode is Mathlib-track material. Defer that promotion until they have actually been used by a non-CSD consumer.

### Ordering note

These three extractions are independent. Do them on demand as LF4 produces specific Framework-level consumers, not preemptively. Bulk reclassification risks regressing the axiom-clean / tagged-release stability of LF1-3 without proportionate benefit. The CONVENTIONS.md "initial pass by current location" policy was chosen precisely to avoid that risk.

---

## 11. Self-adjointness convention switch (deferred to Framework extraction)

**Status:** LF3 modules currently state self-adjointness on continuous linear maps via the inner-product equation `∀ x y, inner ℂ (T x) y = inner ℂ x (T y)`. The canonical Mathlib spelling is `IsSelfAdjoint T`.

**Why deferred:** Diagnostic re-audit on 2026-05-18 (against Mathlib at Lean 4.29.0-rc8) confirmed:

- The `Star (H →L[ℂ] H)` instance required for `IsSelfAdjoint T` synthesis lives in a Mathlib section with `[CompleteSpace E]` as a section hypothesis.
- Mathlib does NOT automatically chain `[FiniteDimensional ℂ H] → [CompleteSpace H]` via `FiniteDimensional.proper_real` (the chain exists for `ℝ`-finite-dim but doesn't navigate `ℂ`-finite-dim through the `NormedSpace ℝ ℂ` link in typeclass synthesis).
- Adding `[CompleteSpace H]` as an explicit typeclass argument resolves the issue but cascades to every caller of LF3 structures.

The inner-product-equation spelling avoids the cascade and is mathematically equivalent.

**Pickup (when extracting to `Framework/Measurement/`):**

1. Add `[CompleteSpace K]` to `BinaryPointerProjectors` (and to `K_A`, `K_B`, `H_SA` for the bipartite structures).
2. Replace `selfAdjoint : ∀ x y, inner ℂ (proj s x) y = inner ℂ x (proj s y)` with `selfAdjoint : ∀ s, IsSelfAdjoint (proj s)`.
3. Same pattern for `TensorFactorReadoutAlgebra.hA_selfAdjoint` / `hB_selfAdjoint`, `ProjectorAlgebra.selfAdjoint`, `mHat_isSelfAdjoint`.
4. Update consumers — `IsSelfAdjoint T` unfolds to `T = star T`, equivalent via `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` to `LinearMap.IsSymmetric (T : K →ₗ[ℂ] K)`, from which `inner` form follows by `IsSymmetric` field application.
5. Concrete `Framework/` callers (typically `K = EuclideanSpace ℂ (Fin n)`) get `CompleteSpace` automatically via Mathlib's `EuclideanSpace.instCompleteSpace`.

**Alternative:** wait for Mathlib's instance synthesis to chain `FiniteDimensional ℂ → CompleteSpace`. If that lands, the refactor becomes a no-op rename (`IsSelfAdjoint T` synthesizes without adding `[CompleteSpace _]` arguments).

**Depends on:** the Framework/ extraction (§10) being underway. Standalone refactor is mechanical but cost is the typeclass-argument cascade.

---

## 12. `Projectivization` topology / measure / lift API in Mathlib — **PARTIAL (Groups 1–2 + full MeasureSpace.lean except 4.6 polish, 2026-05-19/2026-05-20)**

**Status:** Identified as a Mathlib gap via the pre-LF4 spike on 2026-05-18 (see `specs/pre-LF4-plan.md` Spike 1). The pre-LF4 option-(b) chain initially scoped a commitment `ProjectiveHilbert N := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` at the LF2 level; the spike found Mathlib has no `TopologicalSpace`, `MeasurableSpace`, or `BorelSpace` instance on `Projectivization` outside the projective-line case (`OnePoint/ProjectiveLine.lean`). The architectural workaround keeps `SectorData.P` abstract and supplies a caller-side `representative : P → EuclideanSpace ℂ (Fin N)` map.

**Group 1 delivered 2026-05-19** in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` (Cat-1, namespace `Projectivization`, no CSD prefix, strict Mathlib style). Covers items 3.1–3.4 of the `specs/projectivization-plan.md` execution plan:

- `Projectivization.instTopologicalSpace`: explicit forwarding of the quotient topology instance (required because `Projectivization` is a `def`, not `@[reducible]`).
- `Projectivization.continuous_mk'`: continuity of the canonical surjection `{v : V // v ≠ 0} → ℙ K V`.
- `Projectivization.scaleNonzero` + `scaleNonzeroHomeo`: the `Kˣ`-scaling action on the nonzero subtype as a self-homeomorphism (gated on `[TopologicalSpace V] [ContinuousConstSMul K V]`).
- `Projectivization.mk'_preimage_mk'_image`: saturation lemma `mk' ⁻¹' (mk' '' U) = ⋃ a : Kˣ, scaleNonzero a '' U` (the projectivization analogue of `MulAction.quotient_preimage_image_eq_union_mul`).
- `Projectivization.isOpenMap_mk'`: openness of the canonical surjection.
- `Projectivization.isQuotientMap_mk'` + `isOpenQuotientMap_mk'`: quotient-map and open-quotient-map characterisations.

Hypothesis pattern at Group 1: `[DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousConstSMul K V]` for the topological-action lemmas (continuity / openness); algebraic infrastructure (`scaleNonzero_mul`, `scaleNonzero_one`, `mk'_preimage_mk'_image`) does not require any topology. No topology on K is needed — `ContinuousConstSMul K V` is purely a property of the `V`-side action.

**Group 2 delivered 2026-05-20** in the same `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` file, under a new `section NormedFiniteDim`. Adopted the `[RCLike K]` scalar-hypothesis option (per plan §7.2): simpler proofs and sufficient for the LF4 critical path. The earlier sections were enclosed in a new `section AlgebraicTopology` so the `[AddCommGroup V]` from the outer variable block does not create an instance diamond with `[NormedAddCommGroup V]` in the new section. Covers items 3.5–3.6:

- `Projectivization.instT2Space`: Hausdorffness via the open-quotient-map criterion `t2Space_iff_of_isOpenQuotientMap` applied to `isOpenQuotientMap_mk'`, reducing T2 to closedness of the K-collinearity relation `{(v, w) | mk' v = mk' w}`. Closedness routes through `LinearIndependent.pair_iff'` + `isOpen_setOf_linearIndependent` (the set of linearly independent pairs is open in finite-dim normed K-modules over `[RCLike K]`).
- `Projectivization.instCompactSpace`: compactness via continuous surjection from the unit sphere. The sphere `Metric.sphere (0 : V) 1` is compact (`isCompact_sphere` + `FiniteDimensional.proper_rclike`); the map `g : sphere → ℙ K V, v ↦ mk K v hv` is continuous; surjectivity uses normalisation `((‖p.rep‖⁻¹ : ℝ) : K) • p.rep` of the representative.
- `Projectivization.isClosed_collinearity_relation`: closedness of the K-collinearity relation, the supporting lemma for T2.

**Measure-core delivered 2026-05-20** in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` (new file, Cat-1, namespace `Projectivization`). Covers plan items 4.1, 4.3, 4.4, plus a free `SecondCountableTopology` bonus:

- `Projectivization.instMeasurableSpace`: Borel σ-algebra from the quotient topology, gated on `[RCLike K]` + finite-dim normed `V`.
- `Projectivization.instBorelSpace`: witness that the installed measurable space coincides with `borel _` (`rfl`).
- `Projectivization.instMeasurableSingletonClass`: singletons are measurable; T2 (Group 2) + Borel ⟹ closed singletons measurable.
- `Projectivization.measurable_mk'`: the canonical surjection is measurable, via `continuous_mk'.measurable`. Caller supplies `[MeasurableSpace V] [BorelSpace V]` so the source subtype inherits a Borel structure.
- `Projectivization.instSecondCountableTopology`: free consequence of `isQuotientMap_mk'` + `isOpenMap_mk'` + `secondCountable_of_proper`.

**Group 4 + Group 5 delivered 2026-05-20** in the same `MeasureSpace.lean` file:

- `Projectivization.borel_eq_map_mk'`: the coincidence lemma. The Borel σ-algebra on `ℙ K V` equals `MeasurableSpace.map mk' (borel V₀)`. Routes through Mathlib's `Continuous.map_borel_eq` (`Mathlib.MeasureTheory.Constructions.Polish.Basic`), given `PolishSpace V` (automatic from `FiniteDimensional.proper_rclike K V` + `secondCountable_of_proper` + the `Polish.lean:65` instance for separable + completely metrizable) and `PolishSpace {v : V // v ≠ 0}` (via `IsOpen.polishSpace` applied to `isClosed_singleton.isOpen_compl`).
- `Projectivization.lift_measurable`: the **load-bearing user-facing lemma for LF4 §3 + §8**. Lets callers derive measurability of `Projectivization.lift f hf` from measurability of `f` and the scale-invariance hypothesis. Routes through `borel_eq_map_mk'` + `MeasurableSpace.map_def`.
- `Projectivization.measurable_iff_measurable_comp_mk'`: companion characterisation. A function out of `ℙ K V` is measurable iff its precomposition with `mk'` is.

Both `lift_measurable` and `measurable_iff_measurable_comp_mk'` take additional `[MeasurableSpace V] [BorelSpace V]` hypotheses so the source subtype's `Subtype.instMeasurableSpace` coincides with `borel _` via the `Subtype.borelSpace` instance. The `‹BorelSpace ({v // v ≠ 0})›.measurable_eq` bridge inside the proofs handles the conversion.

The §12 API is now feature-complete for LF4 consumption. LF4 §3 + §8 can use `lift_measurable` directly to lift measurable scale-invariant functions on `V \ {0}` to measurable functions on `ℙ K V`, rather than carrying `hrep_meas` as a structural hypothesis at the chain capstone. The pre-LF4 chain (LF3 `PurePreparation` etc.) currently still threads `hrep_meas`; the LF4 instantiation can switch to `lift_measurable` once the concrete `SectorData` is in place.

**Pickup pointer:** see `specs/projectivization-plan.md` for the per-section design plan; `specs/projectivization-plan.md` §6 records the resolved Mathlib infrastructure investigations.

**Why partial:** Building the full quotient-topology + Borel-structure + `Projectivization.lift`-measurability stack for arbitrary `K`, `V` is a multi-day Mathlib contribution. Group 1 (the openness-of-canonical-surjection backbone) is landed; the remaining Groups 2–5 are blocked on a scalar-hypothesis decision and a non-trivial closedness proof.

**Pickup (Cat-1 Mathlib contribution, when scheduled):**

1. ~~Define `TopologicalSpace (Projectivization K V)`.~~ **DONE 2026-05-19 (Group 1).**
1b. ~~T2Space + CompactSpace under `[RCLike K]` + finite-dim normed `V`.~~ **DONE 2026-05-20 (Group 2).**
2. ~~Prove `BorelSpace (Projectivization K V)` for the appropriate `K`-and-`V`-flavoured cases.~~ **DONE 2026-05-20 (measure-core).**
3. ~~Prove `MeasurableSingletonClass (Projectivization K V)`.~~ **DONE 2026-05-20 (measure-core).**
4. ~~Prove `Projectivization.lift_measurable`: if `f : V \ {0} → α` is measurable and `f`-phase-invariant, then `Projectivization.lift f hf : Projectivization K V → α` is measurable.~~ **DONE 2026-05-20** (with the coincidence lemma `borel_eq_map_mk'` + companion `measurable_iff_measurable_comp_mk'`).
5. ~~Land in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` per CONVENTIONS.md `1-Mathlib` tagging.~~ **DONE 2026-05-20.**

**Effect on pre-LF4 / LF4 work:** Until landed, `SectorData.P` stays abstract and `OperationalPackage.fromPreparation` takes a caller-supplied `rep : P → EuclideanSpace ℂ (Fin N)`. When this lands, LF4 can specialise `P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` and the `rep` argument resolves to `Projectivization.rep` or similar. No retrofit needed; the abstract API is monomorphic in `P` so any concrete `P` works at instantiation time.

**Depends on:** nothing in CSD; this is a self-contained Mathlib contribution that other projectivization-using formalisations (algebraic geometry, projective representations of Lie groups, etc.) would also benefit from.
