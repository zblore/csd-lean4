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

## 2. Preparation-to-Hilbert-vector correspondence

**Status:** Not addressed in LF2. This is the missing piece for a full LF1 → Born-form chain.

**Why deferred:** LF1's `μprep : Measure Σ` and LF2-BornWrapper's `ψ : EuclideanSpace ℂ (Fin N)` live in disjoint type universes. Connecting them requires introducing `P ↔ Projectivization ℂ (EuclideanSpace ℂ (Fin N))` and a concentration argument.

**Pickup sketch:**
1. In LF4, specialise LF2's abstract `P` to `Projectivization ℂ (EuclideanSpace ℂ (Fin N))`.
2. Introduce a "pure preparation" predicate on `μprep`: something like "the pushforward `π * μprep` is a Dirac measure at a projective point `[ψ] ∈ CP^{N-1}`."
3. Lift `[ψ]` to a unit vector `ψ : EuclideanSpace ℂ (Fin N)` (choice of representative mod phase).
4. Connect the resulting `OperationalPackage` (derived from `μprep` via the measure bridge + Radon–Nikodym) to `rankOneDensity ψ` via `busch_effect_gleason` + `rankOneDensity_unique_of_certainty`.
5. Chain with `LF1_main_theorem_projective` and `pure_state_born_weights_of_certainty` to obtain: **LF1 frequency → ‖⟨ψ, φ⟩‖²**.

**Depends on:** Mathlib's `Projectivization`, Radon–Nikodym derivatives, Haar-measure / Dirac-concentration arguments.

**Design-space constraint (confirmed 2026-05-17).** The three LF3 chain capstones in `LF3/Interface.lean` currently take an external `hLF2` hypothesis discharged by this item + §7. There are three candidate factorisations for the discharge:

- (a) Keep `hLF2` as a permanent hypothesis and document it as a programme-level open problem.
- (b) Bundle the discharge into a `PurePreparation` structure whose elimination rule supplies `hLF2`.
- (c) Absorb `hLF2` into a `Born-ready preparation` typeclass.

Option **(a) is ruled out**: the chain capstones must reach a discharged form in LF4. The LF4 plan must choose between (b) and (c). The latter two differ in cost and downstream feel; the choice is open and should be made at LF4 plan time, not now.

---

## 3. Rank-1 effects from projective points (not from unit vectors)

**Status:** `rankOneEffect`, `rankOneDensity` take `EuclideanSpace ℂ (Fin N)` unit vectors, not projective points.

**Why deferred:** LF4 needs outcomes specified projectively (`[φ] ∈ CP^{N-1}`), not as unit vectors. Currently a phase-dependent vector is required. Phase-invariance of the outer product `|φ⟩⟨φ|` makes this sound, but LF2 doesn't expose it.

**Pickup:**
1. Prove `rankOneEffect φ hφ = rankOneEffect (c • φ) hφ'` for `|c| = 1` (phase invariance of the outer product). One-line calculation: `(c • φ) * star (c • φ) = c · star c · (φ * star φ) = ‖c‖² · (φ * star φ) = φ * star φ`.
2. Lift to projective points: for `[φ] : Projectivization ℂ (EuclideanSpace ℂ (Fin N))`, define `rankOneEffectProj [φ]` via choice of unit-vector representative, using the phase-invariance lemma to show well-definedness.
3. Similarly for `rankOneDensityProj`.

**Depends on:** `Mathlib.LinearAlgebra.Projectivization.Basic`.

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

## 7. Outcome specification: ontic-first vs projective-first

**Status:** LF1's `OutcomeRegion` has `Ω : Set SigmaSpace` (ontic-first). LF2's `LF1_main_theorem_projective` takes a correspondence hypothesis `O.preEvent = D.π ⁻¹' Oep` linking them.

**Why deferred:** A cleaner LF4 architecture would let callers specify outcomes projectively and derive the ontic counterpart. Currently the caller must supply both and prove the correspondence.

**Pickup:**
1. Build a helper `SectorData.outcomeOfProjective : {Oep : Set P} → MeasurableSet Oep → D.toOntic.OutcomeRegion` that constructs the LF1-side outcome from a projective outcome region (with `Ω := Φ⁻¹(π⁻¹(Oep))` or similar).
2. Prove the correspondence automatically so callers don't need to supply `hCorresp`.

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
3. Keep `mHat`, `branchWeight`, and other LF3-specific consumers in `LF3/Projectors/`. They depend on Framework but stay Cat-3.

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
