> ⚠️ HISTORICAL — layer complete; frozen execution log. Open items live in [BACKLOG.md](BACKLOG.md).
# Projectivization topology / measure / lift plan

Plan for the `CsdLean4/Mathlib/LinearAlgebra/Projectivization/{Topology,MeasureSpace}.lean`
Cat-1 contribution discharging LF4-todo §12.

This work is independent of the TN4 / Sigma1 / LF4 paper sequence
(per the 2026-05-19 paper-sequencing decision, see
`[[project-lf4-decisions]]`): pure mathematics, no CSD-specific content,
unblocks LF4 §3 + §8 when those eventually happen. Eventually
upstreamable to Mathlib proper.

## 0. CSD-aligned design decision (resolved 2026-05-19)

**Borel σ-algebra direction adopted**, matching:

- **Spec alignment**: LF2 v1.00 §7.4 invokes the SU(N)-invariant **Borel**
  probability measure on CP^{N-1} (Fubini–Study). The
  invariant-measure-uniqueness axiom is stated for Borel probability
  measures on a homogeneous G-space, invoking the topological/Borel
  structure rather than a coinduced σ-algebra on the quotient.
- **Mathlib convention**: for nice topological quotients (e.g.
  `AddCircle`), Mathlib installs `BorelSpace` from the topology rather
  than relying on the generic `Quotient.instMeasurableSpace` coinduced
  fallback. `Projectivization K V` in the normed finite-dim case is a
  "nice topological quotient" (second-countable, T2, compact).
- **Upstreamable shape**: the Borel formulation is the canonical
  upstream-PR shape for `ℙ K V` once K and V are normed; the coinduced
  version is for the pure setoid case without analytic content.

**Consequence for the plan**:

- Install `MeasurableSpace (Projectivization K V) := borel _` and
  `BorelSpace (Projectivization K V) := ⟨rfl⟩` under
  `[NormedField K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]`.
- Prove the **coincidence lemma**: under the same hypotheses, the
  Borel σ-algebra equals the coinduced σ-algebra
  `MeasurableSpace.map mk''`. This lets us reuse Mathlib's
  `measurable_from_quotient` machinery for `lift_measurable` while
  keeping the Borel structure as canonical.
- Gate the Borel instance on the normed finite-dim hypotheses so it
  cannot shadow the generic `Quotient.instMeasurableSpace` outside
  that context.

**Tension acknowledged**: someone using `Projectivization K V` as a pure
setoid quotient (e.g. algebraic geometry, no analytic structure) still
gets the coinduced σ-algebra by default; our Borel override only fires
under the normed finite-dim hypothesis. Documented in the file header.

## 1. Scope and decisions

### 1.1 Mathematical scope

Four core pieces in dependency order:

- (T1) Quotient topology on `Projectivization K V` — effectively free from
  Mathlib's `Quotient.instTopologicalSpace`. No new instance declaration;
  expose the inherited one and prove its properties.
- (T2) `Projectivization.mk'` is a continuous open surjection
  (`IsQuotientMap`). Openness is the structurally load-bearing topological
  lemma.
- (T3) `T2Space (Projectivization K V)` for `K` a normed field acting on
  `V` a finite-dimensional normed `K`-module. Sufficient for the LF4
  pipeline; more general infinite-dim form is out of scope.
- (M1) `BorelSpace (Projectivization K V)` — measurable structure from the
  quotient topology, plus the `BorelSpace` class witnessing
  `MeasurableSpace = borel topology`.
- (M2) `MeasurableSingletonClass (Projectivization K V)` from T2 + Borel.
  Required by the LF4 chain for `Measure.dirac` semantics on projective
  outcome regions.
- (M3) `Projectivization.lift_measurable`. Given `f : {v : V // v ≠ 0} → α`
  measurable and scale-invariant, the lift is measurable. Load-bearing
  user-facing lemma for LF4 §3 + §8.
- (M4) `Projectivization.measurable_mk'`. Immediate from continuity.

### 1.2 Scope decisions

| Decision | Choice | Rationale |
|---|---|---|
| Field generality | Topology lemmas at maximum generality (`DivisionRing K`, `TopologicalSpace K`, `IsTopologicalRing K`); Hausdorff + Borel lemmas under `[NormedField K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]` | LF4 needs `K = ℂ`. Maximum-generality topology lemmas are cheap and improve upstream value. |
| ℝ vs ℂ vs general normed field | Single generic statement over `[NormedField K]`; both inferred as instances | One proof covers both. Mathlib idiom. |
| Dimensionality | Finite-dim hypothesis only for Hausdorff and downstream measure work; topology lemmas (continuity / openness of `mk'`) general | Hausdorff in infinite-dim normed `Projectivization` is subtler. Finite-dim closes the argument via the unit-sphere quotient. |
| File structure | `Topology.lean` + `MeasureSpace.lean` | Matches Mathlib import-graph idiom — measure file imports topology + Borel machinery; topology file does not depend on `MeasureTheory`. |
| Eventually upstreamable form | All declarations in `namespace Projectivization`; no `CsdLean4`-namespaced shims | Cat-1 convention. Future upstreaming is a file move only. |
| Notation `ℙ K V` | `open scoped LinearAlgebra.Projectivization` inside our files | Existing Mathlib scoped notation. |

### 1.3 Out of scope

- General topology for non-normed `V` (Hausdorff + Borel in infinite-dim
  Banach spaces — defer until concrete consumer appears).
- The homeomorphism `ℙ ℂ V ≃ S(V) / U(1)`.
- Smooth-manifold structure on projective space.
- Action lemmas on `Projectivization.map` (mapping by semilinear maps).
- `Polish` / `StandardBorelSpace` instances (stronger than `BorelSpace + MeasurableSingletonClass`; not required).

## 2. File structure

```
CsdLean4/Mathlib/LinearAlgebra/Projectivization/
  Topology.lean       -- 1-Mathlib, ~150-250 lines estimated
  MeasureSpace.lean   -- 1-Mathlib, ~100-150 lines estimated
```

Both: `namespace Projectivization`, `open scoped LinearAlgebra.Projectivization`,
no `CsdLean4` namespace pollution. Provenance docstrings on every lemma.
**Strict Mathlib style throughout**: naming, docstring format, import
discipline, typeclass argument shape, simp-attribute hygiene.

Imports:

```
-- Topology.lean
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
```

```
-- MeasureSpace.lean
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
```

## 3. `Topology.lean` declarations

### 3.1 Quotient topology (automatic, no new instance)

`Projectivization K V := Quotient (projectivizationSetoid K V)` inherits a
`TopologicalSpace` automatically from `Quotient.instTopologicalSpace`.
Disclosure-only.

### 3.2 Continuity of the constructor

```lean
theorem Projectivization.continuous_mk' :
    Continuous (mk' K : {v : V // v ≠ 0} → ℙ K V)
```

One-line; `continuous_quot_mk` or `Quotient.continuous_mk`.

### 3.3 Openness of the constructor

```lean
theorem Projectivization.isOpenMap_mk' :
    IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V)
```

Proof: for `U ⊆ {v // v ≠ 0}` open, `mk'⁻¹(mk'(U)) = ⋃_{a ∈ Kˣ} a • U`,
a union of homeomorphic images of `U`. Hence open in `{v // v ≠ 0}`.
By definition of the quotient topology, `mk'(U)` is open in `ℙ K V`.

Standard "open quotient by a group action" result. Mathlib may have it
generically for `MulAction.orbitRel`-style quotients — see §6.

### 3.4 Quotient-map characterisation

```lean
theorem Projectivization.isQuotientMap_mk' :
    IsQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V)
```

Continuous + surjective + topology equality. ~5 min once 3.2 lands.

### 3.5 Hausdorffness in the normed finite-dim case

```lean
variable [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  [FiniteDimensional K V]

instance : T2Space (Projectivization K V)
```

Two candidate proof routes — see §6 investigation for which is tractable
in current Mathlib.

### 3.6 Compactness (supporting, low marginal cost)

```lean
instance : CompactSpace (Projectivization K V)
```

Continuous image of compact (unit sphere).

## 4. `MeasureSpace.lean` declarations (Borel direction)

### 4.1 Borel measurable space instance

```lean
variable {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  [FiniteDimensional K V]

instance Projectivization.instMeasurableSpace :
    MeasurableSpace (Projectivization K V) := borel _

instance Projectivization.instBorelSpace :
    BorelSpace (Projectivization K V) := ⟨rfl⟩
```

Gated on the normed finite-dim hypotheses; coexists with Mathlib's
generic `Quotient.instMeasurableSpace` (which fires when our gating
hypotheses are absent). ~15 min.

### 4.2 Coincidence lemma: Borel σ-algebra equals the coinduced one

```lean
theorem Projectivization.borel_eq_quotient :
    (borel (Projectivization K V) : MeasurableSpace _)
      = MeasurableSpace.map (Quotient.mk'' :
          {v : V // v ≠ 0} → Projectivization K V)
          (borel _)
```

Standard measure theory: under second-countable + open continuous
surjection, the Borel σ-algebra of the quotient topology equals the
coinduced σ-algebra. Mathlib likely has a generic version (search
needed); if not, prove directly using second-countability of the
quotient (from `ContinuousConstSMul.secondCountableTopology`,
`Topology/Algebra/ConstMulAction.lean:619`).

**Routing**: `IsOpenMap` (from 3.3) + `IsQuotientMap` (from 3.4) +
second-countability ⟹ the open quotient map carries the Borel
structure onto the coinduced one. ~3-4 h.

### 4.3 Measurable singleton class

```lean
instance Projectivization.instMeasurableSingletonClass :
    MeasurableSingletonClass (Projectivization K V)
```

T2 (from 3.5) + `BorelSpace` ⟹ singletons closed ⟹ measurable. Routes
through Mathlib's automatic `T1Space.instMeasurableSingletonClass` for
Borel spaces. ~15 min.

### 4.4 Constructor measurability

```lean
theorem Projectivization.measurable_mk' :
    Measurable (mk' K : {v : V // v ≠ 0} → ℙ K V)
```

`Continuous.measurable` applied to 3.2, using the BorelSpace structure
to convert continuity to measurability. ~5 min.

### 4.5 Lift measurability

```lean
theorem Projectivization.lift_measurable {α : Type*} [MeasurableSpace α]
    {f : {v : V // v ≠ 0} → α}
    (hf : ∀ (a b : {v : V // v ≠ 0}) (t : K), a = t • (b : V) → f a = f b)
    (hf_meas : Measurable f) :
    Measurable (Projectivization.lift f hf)
```

Routes through the coincidence lemma 4.2 plus
`measurable_from_quotient` (`MeasureTheory/MeasurableSpace/Constructions.lean:149`).
Schematically: `Measurable (lift f hf)` (Borel) ↔
`Measurable (lift f hf)` (coinduced) [by 4.2] ↔
`Measurable (lift f hf ∘ mk'')` [by `measurable_from_quotient`] ↔
`Measurable f` [by `lift_mk`]. ~30 min after 4.2 is solid.

### 4.6 Characterisation lemma

```lean
theorem Projectivization.measurable_iff_measurable_comp_mk' {α : Type*}
    [MeasurableSpace α] (g : ℙ K V → α) :
    Measurable g ↔ Measurable (g ∘ mk' K)
```

Companion to 4.5. ~10 min.

## 5. Order of operations

```
3.1 (free)
  ↓
3.2 (continuous_mk')  ──→  3.4 (isQuotientMap_mk')
  ↓                          ↓
3.3 (isOpenMap_mk')  ────→  3.5 (T2Space)  ──→  3.6 (CompactSpace)
                              │
                              ↓
                            4.1 (BorelSpace instance)
                              ↓
              ┌───────────────┼───────────────┐
              ↓               ↓               ↓
        4.2 (coincidence  4.3 (singleton  4.4 (measurable_mk')
             lemma)            class)
              ↓
        4.5 (lift_measurable)  ──→  4.6 (characterisation)
```

Key edges:
- 4.2 depends on 3.3 (openness) + 3.4 (quotient map) + second-countability.
- 4.3 depends on 3.5 (T2) + 4.1 (Borel).
- 4.5 depends on 4.2 (coincidence) + 4.4 (measurable_mk'), routing through
  Mathlib's `measurable_from_quotient`.

Recommended landing pattern: one PR-equivalent commit landing the full
pipeline atomically (groups are tightly interdependent; split commits
create transitional API surfaces).

## 6. Mathlib infrastructure investigations — DONE (2026-05-19)

Investigations resolved before starting Lean writing. Findings inline.

### 6.1 Open quotient by group action — RESOLVED

`MulAction.isOpenQuotientMap_quotientMk` at
`Mathlib/Topology/Algebra/ConstMulAction.lean:575` provides
`IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel Γ T))` under
`[ContinuousConstSMul Γ T]`.

**Caveat**: applies to `MulAction.orbitRel Kˣ {v : V // v ≠ 0}` directly.
Mathlib's `projectivizationSetoid K V` is defined as
`(MulAction.orbitRel Kˣ V).comap (↑)` — same equivalence on
`{v // v ≠ 0}`, but a `Setoid.comap`-wrapped shape rather than the direct
orbit relation. Bridge work needed: either show the two setoids agree
(plus a `MulAction Kˣ {v // v ≠ 0}` instance to express the direct
version), or prove openness directly.

**Estimate**: ~30 min if the setoid equality goes through cleanly,
~2 h direct proof otherwise.

### 6.2 Hausdorffness — RESOLVED via direct closed-relation route

`t2Space_quotient_mulAction_of_properSMul` at
`Mathlib/Topology/Algebra/ProperAction/Basic.lean:114` exists but
requires `[ProperSMul Kˣ V]`, and Mathlib has **no instance** of
`ProperSMul` for `Kˣ` acting on a normed K-module. Establishing that
instance is a ~4-6 h side track.

**Better route**: pattern after the proof body of
`t2Space_quotient_mulAction_of_properSMul` (lines 116-127). Use
`t2_iff_isClosed_diagonal` + `IsOpenQuotientMap.isQuotientMap.isClosed_preimage`
to reduce T2 to closedness of the K-collinearity relation on
`(V \ {0}) × (V \ {0})`. For normed finite-dim V, K-collinearity is
`{(v, w) | w ∈ K • v}`, which is closed (1-dim closed K-subspace through
v, intersected with V \ {0}). **~3-4 h.**

### 6.3 Borel σ-algebra equals coinduced σ-algebra — RESOLVED (significant finding)

Mathlib's `MeasureTheory/MeasurableSpace/Constructions.lean:128-183`
already provides the entire coinduced-quotient measurability machinery:

- `Quotient.instMeasurableSpace` (136): generic coinduced σ-algebra
  `MeasurableSpace.map Quotient.mk''`, present automatically.
- `measurableSet_quotient` (145): `MeasurableSet t ↔ MeasurableSet (mk'' ⁻¹' t)`.
- `measurable_from_quotient` (149): `Measurable f ↔ Measurable (f ∘ mk'')`.
- `measurable_quotient_mk'` (154): the quotient map is measurable.

For the **Borel direction** we want, the coincidence lemma 4.2 establishes
that under second-countable + open continuous surjection (which we have:
`mk'` is open and continuous, `{v // v ≠ 0}` is second-countable for
normed finite-dim V, and the quotient is second-countable too via
`ContinuousConstSMul.secondCountableTopology` at
`Topology/Algebra/ConstMulAction.lean:619`), the Borel σ-algebra of the
quotient topology equals the coinduced σ-algebra. **Proof estimate ~3-4 h
direct, or ~30 min if a generic Mathlib lemma can be found.**

**Search targets** (for a generic version of 4.2 in Mathlib):
- `MeasurableSpace.borel_eq_map` / similar coincidence theorems
- `Topology.IsOpenQuotientMap.borelSpace_map`
- `SecondCountableTopology.borel_eq`

If found: 4.2 is a one-line specialisation. If not: prove directly via
`Borel.measurableSet_iff_borel_image` + open-map preserves second-countable
generators.

### 6.4 Subtype topology / measurable structure inheritance — RESOLVED

`Subtype.instTopologicalSpace` and `Subtype.instMeasurableSpace` are
Mathlib standard. Typeclass synthesis finds them automatically. No shim
needed.

### 6.5 `Projectivization.lift_mk` definitional behaviour — CONFIRMED

`Projectivization.lift_mk` at
`Mathlib/LinearAlgebra/Projectivization/Basic.lean:87` is proved by `rfl`.
The composition `Projectivization.lift f hf ∘ mk' = f` is definitional.

## 7. Effort estimate (revised after §6 investigations)

| Group | Estimate | Cumulative | Status |
|---|---|---|---|
| Pre-work: investigations §6 | DONE | — | DONE 2026-05-19 |
| Group 1 (Topology 3.1–3.4: continuity, openness, quotient map) | 0.5 day | 0.5 day | **DONE 2026-05-19** |
| Group 2 (Topology 3.5–3.6: T2 + compact, normed finite-dim) | 1 day | 1.5 days | **DONE 2026-05-20** |
| Group 3 (MeasureSpace 4.1: Borel instance + 4.3: singleton class + 4.4: measurable_mk') | 0.5 day | 2 days | **DONE 2026-05-20** (+ free SecondCountableTopology) |
| Group 4 (MeasureSpace 4.2: coincidence lemma) | 0.5 day | 2.5 days | **DONE 2026-05-20** |
| Group 5 (MeasureSpace 4.5: lift_measurable + 4.6: characterisation) | 0.5 day | 3 days | **DONE 2026-05-20** |
| Group 6 (polish + AxiomAudit + build verification + provenance docstrings) | 0.5 day | 3.5 days | **DONE 2026-05-20** |
| **Total** | **3.5 days focused** | | **3.5 of 3.5 days landed — §12 COMPLETE** |

Down from the initial 5-day estimate because §6 investigations resolved
the highest-uncertainty items (Mathlib's `Quotient.instMeasurableSpace`
machinery, `MulAction.isOpenQuotientMap_quotientMk`, and the
`t2Space_quotient_mulAction_of_properSMul` proof-pattern template
materially reduce the work).

### 7.1 Group 1 execution notes (2026-05-19)

Group 1 landed in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean`. Notable execution details (for the next-session continuation):

- **Explicit `TopologicalSpace (ℙ K V)` instance was required.** `Projectivization` is a `def` (not `@[reducible]`) over `Quotient (projectivizationSetoid K V)`, so the generic `instTopologicalSpaceQuotient` does not fire by typeclass synthesis. We provide `instTopologicalSpace := inferInstanceAs (TopologicalSpace (Quotient _))`. Gated on `[TopologicalSpace V]`.
- **Direct openness proof, not the `MulAction.isOpenQuotientMap_quotientMk` shortcut.** The plan §6.1 anticipated a setoid-bridge to `MulAction.orbitRel Kˣ {v // v ≠ 0}` to reuse the Mathlib lemma directly. We chose the direct route via `mk'_preimage_mk'_image` + per-unit homeomorphism, avoiding the bridge entirely. Cost: ~30 lines for the saturation lemma. Benefit: no auxiliary `MulAction Kˣ {v // v ≠ 0}` instance needed, no setoid-quotient-coercion friction.
- **No topology on K required.** `ContinuousConstSMul K V` is purely a property of the `V`-side action; the unit-scaling self-maps are continuous without topology on K. This relaxes the original plan hypothesis pattern.
- **`open Topology` in the file header.** `IsQuotientMap` and `IsOpenQuotientMap` live in `namespace Topology`; without `open Topology` they don't resolve.

### 7.2 Group 2 execution notes (2026-05-20)

Group 2 (`T2Space` + `CompactSpace`) landed in the same `Topology.lean`. Adopted option (a) `[RCLike K]` per the deferred-decision recommendation. Execution details:

- **Scalar hypothesis: `[RCLike K]`.** `RCLike` provides `[NormedAlgebra ℝ K]` and the `RCLike.ofReal` coercion needed to normalise representatives. `FiniteDimensional.proper_rclike` (in `Mathlib.Analysis.RCLike.Lemmas`) provides `ProperSpace V`, which in turn provides `Metric.sphere.compactSpace`.
- **T2 routes through `t2Space_iff_of_isOpenQuotientMap`.** This Mathlib helper (`Mathlib.Topology.Separation.Hausdorff`) directly reduces `T2Space (ℙ K V)` to closedness of the K-collinearity relation `{(v, w) ∈ V₀ × V₀ | mk' v = mk' w}`. The collinearity relation is identified with the complement (in `V × V`) of `{(w, v) | LinearIndependent K ![w, v]}` via `mk_eq_mk_iff'` + `LinearIndependent.pair_iff'`, pulled back via a continuous map. Closedness of the open complement is then `isOpen_setOf_linearIndependent.isClosed_compl.preimage`.
- **CompactSpace via continuous surjection from sphere.** The map `g : Metric.sphere (0 : V) 1 → ℙ K V, v ↦ mk K v (sphere ⟹ ≠ 0)` is continuous (continuity of `mk'` + subtype coercion). Surjectivity: any `p : ℙ K V` is the image of `((‖p.rep‖⁻¹ : ℝ) : K) • p.rep` (which lies on the sphere by `mem_sphere_zero_iff_norm`). Then `isCompact_range hg_cont` + `hg_surj.range_eq` give `IsCompact (Set.univ : Set (ℙ K V))`, equivalent to `CompactSpace`.
- **Instance diamond mitigation.** Adding `[NormedAddCommGroup V]` to a section that also has `[AddCommGroup V]` (from the outer variable block) creates an `AddCommGroup V` diamond: the two instances are mathematically equal but typeclass synthesis sees two paths. Resolved by enclosing the earlier sections in `section AlgebraicTopology` with the algebraic variables scoped to that section, then opening a fresh `section NormedFiniteDim` with only the normed variables. This is a recurring pattern in mixed algebraic+normed Mathlib code; documented inline.
- **Imports added.** `Mathlib.Analysis.Normed.Module.FiniteDimension` (for `isOpen_setOf_linearIndependent`), `Mathlib.Analysis.RCLike.Basic` + `Mathlib.Analysis.RCLike.Lemmas` (for `RCLike` and `FiniteDimensional.proper_rclike`), `Mathlib.LinearAlgebra.LinearIndependent.Lemmas` (for `LinearIndependent.pair_iff'`), `Mathlib.Topology.Separation.Hausdorff` (for `t2Space_iff_of_isOpenQuotientMap`).

## 8. Exit criteria

1. Both files build clean.
2. Full library `lake build` green (new modules are leaf nodes).
3. AxiomAudit regressions for the four user-facing lemmas
   (`continuous_mk'`, `isOpenMap_mk'`, `lift_measurable`,
   `MeasurableSingletonClass`) pinned to the foundational triple only.
4. Every lemma carries a provenance docstring suitable for Mathlib
   upstream PR review.
5. `specs/LF4-todo.md` §12 marked DONE with reference to the new modules.

## 9. Upstreaming

- Land in `CsdLean4/Mathlib/` first.
- Observe usage for a tag cycle (or until LF4 actually consumes the API).
- Open Mathlib PR after the shape is settled (the contribution then
  reduces to a file move).
- Naming and style decisions follow Mathlib idiom from the start, so
  upstreaming requires no symbol renames.

## 10. Risks (revised after §6 investigations)

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| 3.3 setoid bridge: `projectivizationSetoid` vs `MulAction.orbitRel Kˣ` shape mismatch | Medium | +30 min – 2 h | If setoid equality lands cleanly, reuse `MulAction.isOpenQuotientMap_quotientMk` directly. Otherwise prove openness by hand via `mk'⁻¹(mk'(U)) = ⋃ a ∈ Kˣ, a • U`. Both routes bounded. |
| 3.5 Hausdorff: K-collinearity closedness on `(V\{0}) × (V\{0})` needs hand-rolled proof | Medium | +1-2 h | Template from `t2Space_quotient_mulAction_of_properSMul` proof body (lines 116-127). Direct closed-relation route avoids the missing `ProperSMul Kˣ V` instance entirely. |
| 4.2 coincidence lemma: no generic Mathlib lemma found | Medium | +2-3 h | Direct proof using second-countability of `{v // v ≠ 0}` + open continuous surjection. Worst case, contribute the helper upstream as a sub-contribution. |
| Typeclass synthesis on `{v : V // v ≠ 0}` fails | Low | +30 min | Explicit instance shim. |
| Borel instance shadows generic `Quotient.instMeasurableSpace` outside normed finite-dim context | Low | +0 (resolved) | Gated on normed finite-dim hypotheses; no shadowing in algebraic-geometry contexts. Documented in file header. |

**Resolved by §6 investigations (no longer risks):**

- Open quotient by group action: `MulAction.isOpenQuotientMap_quotientMk` exists.
- T2 via proper action: template proof pattern available even without `ProperSMul`.
- Mathlib quotient measurability machinery: full coinduced-σ-algebra
  infrastructure at `MeasureTheory/MeasurableSpace/Constructions.lean:128-183`.
- Subtype topology / measurable structure inheritance: automatic.
- `lift_mk` definitional behaviour: `rfl`.
