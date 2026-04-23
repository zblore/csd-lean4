# LF2 implementation plan

Companion to `specs/LF2-v1.00.pdf` (extracted text: `specs/LF2-v1.00.txt`).
Drives implementation under `CsdLean4/LF2/`.

## 0. Scope and design choices (confirmed)

- **Abstract projective layer.** `CP^{N-1}` is represented as an abstract `MeasurableSpace P` with a distinguished reference measure `μFS` (required to be a probability measure). No use of Mathlib's `Projectivization`, no construction of the Fubini–Study form. Concrete instantiation is deferred.
- **Symmetry group is abstract.** `SU(N)` is represented by a type parameter `G : Type*` with `Group G` and measurable actions on `Σ` and `P`. The spec's concrete `SU(N)` appears nowhere in LF2 Lean source.
- **Concrete matrix-based operational structures.** `Effect`, `DensityOperator`, and the operational package are concrete N×N complex matrix structures using Mathlib's `Matrix` / `PosDef` / `Hermitian` / `EuclideanSpace` APIs. This is a revision of an earlier "opaque stub" plan: it costs ~200–300 extra lines of Lean but lets us *prove* the Born quadratic form `wᵢ = |⟨ψ|φᵢ⟩|²` as a Lean lemma rather than leave it as narrative. See §2.4 for the structure definitions and the proof sketch.
- **Two `axiom` declarations are permitted** in LF2 (both called for by the spec §7.4):
  1. `invariant_measure_uniqueness` — invariant-measure uniqueness on `P`
  2. `busch_effect_gleason` — effect-additive probability ⇒ unique trace-form density operator
  LF1 remains axiom-free. LF2 introduces these deliberately and documents them in module docstrings.
- **Sorry-free target.** Zero `sorry`s in LF2, same bar as LF1.

## 1. Module layout

```
CsdLean4/LF2/
  Setup.lean          -- SectorData: OnticSetup + projection π + G-action + equivariance/invariance
  MeasureBridge.lean  -- π*μL, invariance transfer, uniqueness axiom, Theorem 1 (measure bridge)
  Weights.lean        -- MeasurablePartition, projective weights wᵢ, normalisation
  BornWrapper.lean    -- OperationalPackage, Busch axiom, Born-form assignment
  Interface.lean      -- lf1_weight_eq_projective_weight (LF1 ontic weight = LF2 projective weight)
```

Root import `CsdLean4.lean` and convenience re-export `CsdLean4/Basic.lean` are extended to transitively pull in the new modules (explicit list, not glob-based — per CLAUDE.md).

Namespace: `CSD.LF2`, with sub-namespace `SectorData` (analogous to LF1's `OnticSetup`).

## 2. Module-by-module specification

### 2.1 `Setup.lean`

Extends LF1's `OnticSetup` with the epistemic projection and symmetry data.

```lean
namespace CSD
namespace LF2

open MeasureTheory

/-- LF2 sector data: LF1 ontic setup + measurable projection π : Σ → P +
    measurable G-actions on Σ and P with invariance of μL and equivariance of π. -/
structure SectorData
    (Sigma P G : Type*)
    [MeasurableSpace Sigma] [Nonempty Sigma]
    [MeasurableSpace P]
    [Group G] where
  /-- Underlying LF1 ontic setup. -/
  toOntic       : CSD.LF1.OnticSetup Sigma
  /-- The epistemic projection. -/
  π             : Sigma → P
  measurable_π  : Measurable π
  /-- Lifted G-action on Σ (measurable equivalences). -/
  onticAction   : G → Sigma ≃ᵐ Sigma
  /-- G-action on P. -/
  epAction      : G → P ≃ᵐ P
  /-- μL is invariant under the Σ-action. -/
  hμL_inv       : ∀ g, MeasurePreserving (onticAction g)
                          (toOntic.μL : Measure Sigma) (toOntic.μL : Measure Sigma)
  /-- π intertwines the two actions. -/
  hπ_equiv      : ∀ g x, π (onticAction g x) = epAction g (π x)
```

**Notes**
- `onticAction`/`epAction` are returned as `MeasurableEquiv` (`≃ᵐ`) so invariance and pushforward compose cleanly with Mathlib.
- Group-action coherence (`onticAction 1 = id`, `onticAction (g*h) = onticAction g ∘ onticAction h`) is **not** required for the theorems LF2 proves. Omitted initially to keep the structure minimal; can be added if any downstream proof needs it.
- Reference measure `μFS` and its probability-measure status are **not** fields of `SectorData`. They enter `MeasureBridge.lean` as explicit arguments, so `SectorData` is `μFS`-agnostic.

### 2.2 `MeasureBridge.lean`

Four pieces:

**(a) Pushforward rewrite.** Thin wrapper over `MeasureTheory.Measure.map_apply`:
```lean
lemma pushforward_apply
    (D : SectorData Sigma P G) (A : Set P) (hA : MeasurableSet A) :
    (Measure.map D.π (D.toOntic.μL : Measure Sigma)) A
      = (D.toOntic.μL : Measure Sigma) (D.π ⁻¹' A) := ...
```

**(b) Preimage-action identity (spec Lemma 1).**
```lean
lemma preimage_action_eq
    (D : SectorData Sigma P G) (g : G) (A : Set P) :
    D.π ⁻¹' (D.epAction g '' A) = (D.onticAction g) '' (D.π ⁻¹' A)
```
Direct from `hπ_equiv` + bijectivity of `onticAction g`.

**(c) Invariance transfer (spec Lemma 2).** `π*μL` is `epAction`-invariant.
```lean
lemma pushforward_epAction_invariant
    (D : SectorData Sigma P G) (g : G) :
    MeasurePreserving (D.epAction g)
      (Measure.map D.π D.toOntic.μL) (Measure.map D.π D.toOntic.μL)
```

**(d) Uniqueness axiom + measure bridge (spec Theorem 1).**
```lean
/-- Abstract form of the invariant-measure uniqueness result for `P` under a
    `G`-action. In the concrete CSD model this is uniqueness of the SU(N)-invariant
    Borel probability measure on CP^{N-1}; LF2 imports it rather than constructing P. -/
axiom invariant_measure_uniqueness
    {P G : Type*} [MeasurableSpace P] [Group G]
    (action : G → P ≃ᵐ P)
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g, MeasurePreserving (action g) μFS μFS)
    (μ : Measure P) [IsFiniteMeasure μ]
    (hμ_inv : ∀ g, MeasurePreserving (action g) μ μ) :
    ∃ c : ℝ≥0∞, μ = c • μFS

theorem measure_bridge
    (D : SectorData Sigma P G)
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g, MeasurePreserving (D.epAction g) μFS μFS) :
    ∃ c : ℝ≥0∞, Measure.map D.π D.toOntic.μL = c • μFS
```
Proof: combine (c) + axiom.

**Risks / uncertainties.** The exact `[IsFiniteMeasure]` / `[IsProbabilityMeasure]` instance machinery and the `≤ ∞` bookkeeping may need tweaking during implementation. Not expected to need `sorry`.

### 2.3 `Weights.lean`

```lean
/-- A measurable partition of P (up to μFS-null sets) indexed by `Fin n`. -/
structure MeasurablePartition (P : Type*) [MeasurableSpace P] (μFS : Measure P) (n : ℕ) where
  parts         : Fin n → Set P
  measurable    : ∀ i, MeasurableSet (parts i)
  pairwise_null : ∀ i j, i ≠ j → μFS (parts i ∩ parts j) = 0
  cover_null    : μFS ((⋃ i, parts i)ᶜ) = 0

/-- Projective weight of outcome region O under the pushforward of a preparation. -/
noncomputable def projectiveWeight
    (D : SectorData Sigma P G)
    (μprep : Measure Sigma)
    (O : Set P) : ℝ≥0∞ :=
  (Measure.map D.π μprep) O

/-- Weights are non-negative (free from ℝ≥0∞ typing). -/
lemma projectiveWeight_nonneg : ... -- trivial, here for completeness

/-- Weights sum to 1 when μprep is a probability measure and the partition covers. -/
theorem weights_sum_eq_one
    (D : SectorData Sigma P G) {n : ℕ}
    (μprep : Measure Sigma) [IsProbabilityMeasure μprep]
    (π_part : MeasurablePartition P (Measure.map D.π μprep) n) :
    ∑ i, projectiveWeight D μprep (π_part.parts i) = 1
```

**Note on the partition's reference measure.** The spec states the partition relative to `μFS`. For `weights_sum_eq_one`, what actually matters is that `μprep` of the uncovered set is zero. If `μprep ≪ π*μFS` via the measure bridge, these coincide. For LF2 we state the sum theorem with the partition taken relative to `π*μprep` directly — cleaner hypothesis, same downstream usability.

### 2.4 `BornWrapper.lean`

**Strategy: concrete matrix-based structures + Busch as imported axiom + Born quadratic form proved as a Lean lemma.**

An earlier version of this plan proposed opaque stubs for `Effect`/`DensityOperator`. On review that under-formalized §5.4 of the spec: the whole point of the wrapper is to exhibit `wᵢ = |⟨ψ|φᵢ⟩|²` for rank-one projectors. Keeping the quadratic form as narrative would leave the observable payoff of LF2 out of Lean.

Revised strategy: represent `Effect` and `DensityOperator` as concrete N×N complex matrices over `Mathlib.Data.Matrix` + `Mathlib.LinearAlgebra.Matrix.PosDef`; state Busch as an axiom over these concrete types; **prove** the Born quadratic form as a lemma by direct computation with Mathlib's trace/inner-product API. The load-bearing theorem (Busch) stays axiomatic per spec §7.4; the verifiable corollary (`wᵢ = |⟨ψ|φᵢ⟩|²`) becomes a real Lean proof.

#### Concrete structures

```lean
variable {N : ℕ}

/-- Effect on an N-dimensional complex Hilbert space:
    a Hermitian matrix with 0 ≤ E ≤ I. -/
structure Effect (N : ℕ) where
  M            : Matrix (Fin N) (Fin N) ℂ
  isHermitian  : M.IsHermitian
  nonneg       : M.PosSemidef
  le_one       : (1 - M).PosSemidef

/-- Density operator: Hermitian PSD matrix with trace 1. -/
structure DensityOperator (N : ℕ) where
  M            : Matrix (Fin N) (Fin N) ℂ
  isHermitian  : M.IsHermitian
  nonneg       : M.PosSemidef
  trace_one    : M.trace = 1

/-- Trace-form pairing. The trace of a Hermitian product is real; we extract
    the real part. Correctness of this cast is a small lemma. -/
noncomputable def traceForm (ρ : DensityOperator N) (E : Effect N) : ℝ :=
  RCLike.re ((ρ.M * E.M).trace)
```

#### Rank-1 constructions

```lean
/-- Rank-1 projector |φ⟩⟨φ| as an Effect, from a unit vector φ. -/
noncomputable def rankOneEffect
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) : Effect N := ...

/-- Rank-1 pure-state density |ψ⟩⟨ψ|. -/
noncomputable def rankOneDensity
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) : DensityOperator N := ...
```

Both are "outer product of a unit vector with itself"; the Hermitian/PSD/trace conditions fall out from `hψ`/`hφ` by direct calculation.

#### Born quadratic form (proved)

```lean
/-- Spec §5.4: for rank-1 outcomes on pure preparations, the trace-form probability
    equals the squared magnitude of the inner product. -/
theorem born_quadratic
    (ψ φ : EuclideanSpace ℂ (Fin N))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceForm (rankOneDensity ψ hψ) (rankOneEffect φ hφ) = ‖⟪ψ, φ⟫_ℂ‖ ^ 2
```

Proof strategy: `Tr(|ψ⟩⟨ψ| · |φ⟩⟨φ|) = ⟨φ|ψ⟩⟨ψ|φ⟩ = |⟨ψ,φ⟩|²`, a standard trace-of-outer-product identity. Uses `Matrix.trace_mul_cycle`, outer-product definition, and the `RCLike.re`/`‖·‖` bookkeeping.

#### Effect constants and conditional addition

Helpers that absorb the matrix-level bookkeeping so the `OperationalPackage` fields stay readable:

```lean
namespace Effect

/-- The identity effect `I`. -/
noncomputable def one : Effect N :=
  { M := 1
    isHermitian := Matrix.isHermitian_one
    nonneg := Matrix.PosSemidef.one
    le_one := by simpa using Matrix.PosSemidef.zero }

/-- Sum of two effects, conditioned on the sum being ≤ I. Hermitian-ness and
    PSD of the sum are automatic from the summands; only `le_one` is a genuine
    precondition, so we take it as an explicit argument. -/
noncomputable def add (E F : Effect N)
    (hLe : (1 - (E.M + F.M)).PosSemidef) : Effect N :=
  { M := E.M + F.M
    isHermitian := E.isHermitian.add F.isHermitian
    nonneg := E.nonneg.add F.nonneg
    le_one := hLe }

end Effect
```

#### Operational package + Busch axiom

```lean
/-- Operational consistency package (spec Definition 5.1). -/
structure OperationalPackage (N : ℕ) where
  p          : Effect N → ℝ
  nonneg     : ∀ E, 0 ≤ p E
  le_one     : ∀ E, p E ≤ 1
  total_one  : p Effect.one = 1
  additivity :
    ∀ E F : Effect N, ∀ (hLe : (1 - (E.M + F.M)).PosSemidef),
      p (Effect.add E F hLe) = p E + p F
  -- Unitary covariance (spec clause 3) is left out of the minimal structure; add
  -- it iff busch_effect_gleason's final statement requires it.

/-- Imported Busch effect-Gleason theorem (spec §5.2, §7.4). -/
axiom busch_effect_gleason
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E
```

**Why this shape over alternatives considered:**
- `Effect.add` takes `hLe` (the only genuine precondition) as an explicit argument and returns an `Effect N` directly, avoiding `Option`-valued addition and the `Decidable (PosSemidef …)` headache (PSD is not decidable without `Classical`).
- `Effect.one` lets `total_one` read as `p Effect.one = 1` instead of an inlined anonymous constructor.
- Bundling `IsHermitian`/`PosSemidef` closure-under-sum into `Effect.add` means the package itself never mentions those predicates — only `le_one`, which is the one genuine constraint.

Exact Mathlib lemma names `Matrix.isHermitian_one`, `Matrix.PosSemidef.one`, `Matrix.PosSemidef.zero`, `Matrix.IsHermitian.add`, `Matrix.PosSemidef.add` are the expected spellings; if any differ, the fix is local to `Effect.add` / `Effect.one`.

#### Wrapper theorem

```lean
theorem born_form_of_package
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E, OP.p E = traceForm ρ E :=
  busch_effect_gleason hN OP
```

#### Composite endpoint

```lean
/-- For a pure preparation |ψ⟩ and rank-1 outcome projectors {|φᵢ⟩}, the Born weights
    from the operational package coincide with |⟨ψ|φᵢ⟩|² — the exact spec §5.4 claim. -/
theorem pure_state_born_weights
    {N n : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (hρ : OP.p (rankOneEffect ψ hψ) = traceForm (rankOneDensity ψ hψ) (rankOneEffect ψ hψ))
      -- ^ the Busch-provided ρ specialised at ψ, via Classical.choose / uniqueness
    (φ : Fin n → EuclideanSpace ℂ (Fin N)) (hφ : ∀ i, ‖φ i‖ = 1) :
    ∀ i, OP.p (rankOneEffect (φ i) (hφ i)) = ‖⟪ψ, φ i⟫_ℂ‖ ^ 2
```

(The exact `hρ`-extraction shape is the main fiddle; `Classical.choose` on `ExistsUnique` + applying uniqueness to fix `ρ = rankOneDensity ψ hψ` under the assumption that the preparation is pure. This last step may want a separate lemma "a pure state determines itself as the trace-form density".)

### 2.5 `Interface.lean`

The cleanest theorem in the stack:

```lean
/-- The LF1 ontic weight of a pulled-back outcome region equals the LF2
    projective weight of that region. Immediate from `Measure.map_apply`. -/
theorem lf1_weight_eq_projective_weight
    (D : SectorData Sigma P G)
    (μprep : Measure Sigma)
    (Oep : Set P) (hOep : MeasurableSet Oep) :
    μprep (D.π ⁻¹' Oep) = projectiveWeight D μprep Oep := by
  simp [projectiveWeight, Measure.map_apply D.measurable_π hOep]
```

(Plus a corollary that specialises this to `T.prepMeasure` from LF1, tying back to `LF1_main_theorem_ae`.)

## 3. LF1 reuse (exact names, verified present in repo)

From `CsdLean4/LF1/`:
- `CSD.LF1.OnticSetup` — embedded as `SectorData.toOntic`
- `CSD.LF1.OnticSetup.TrialModel` — used in Interface corollary
- `CSD.LF1.OnticSetup.OutcomeRegion` — for the pulled-back form
- `prepMeasure_apply` — for explicit rewriting in Interface corollary
- `LF1_main_theorem_ae` — referenced in Interface docstring; not re-proved

**No LF1 source edits.** LF2 only *consumes* LF1.

## 4. Mathlib dependencies

Imports expected per module:

| Module | Imports |
|---|---|
| `Setup.lean` | `CsdLean4.LF1.Setup`, `Mathlib.MeasureTheory.MeasurableSpace.Defs`, `Mathlib.MeasureTheory.Group.MeasurableEquiv`, `Mathlib.Dynamics.Ergodic.MeasurePreserving` |
| `MeasureBridge.lean` | `CsdLean4.LF2.Setup`, `Mathlib.MeasureTheory.Measure.MeasureSpace`, `Mathlib.MeasureTheory.Measure.Map` |
| `Weights.lean` | `CsdLean4.LF2.MeasureBridge` |
| `BornWrapper.lean` | `Mathlib.Data.Matrix.Basic`, `Mathlib.LinearAlgebra.Matrix.Trace`, `Mathlib.LinearAlgebra.Matrix.Hermitian`, `Mathlib.LinearAlgebra.Matrix.PosDef`, `Mathlib.Analysis.InnerProductSpace.PiL2` (for `EuclideanSpace`), `Mathlib.Analysis.RCLike.Basic` |
| `Interface.lean` | `CsdLean4.LF2.Weights`, `CsdLean4.LF1.Preparation`, `CsdLean4.LF1.Outcomes` |

Main Mathlib API used: `Measure.map`, `Measure.map_apply`, `MeasurePreserving`, `MeasurableEquiv`, `IsProbabilityMeasure`, `IsFiniteMeasure`.

No Jacobian / Radon–Nikodym API needed at this layer (spec §7.7).

## 5. Risk register

| Risk | Severity | Mitigation |
|---|---|---|
| `IsFiniteMeasure`/`IsProbabilityMeasure` instance plumbing trips up `measure_bridge` | Low | Adjust to `[IsFiniteMeasure μ]` as an explicit hypothesis if instance synthesis fails |
| Axiom statements don't compose cleanly with the theorems consuming them | Medium | Write consumers first as `example` blocks, tune axiom shapes, then lock them in |
| Mathlib lemma names for PSD/Hermitian closure-under-sum and for `1`/`0` PSD differ from expected (`Matrix.PosSemidef.add`, `Matrix.IsHermitian.add`, `Matrix.PosSemidef.one`, `Matrix.isHermitian_one`) | Low | Fix is localised to `Effect.one` and `Effect.add`; other fields never touch these predicates directly |
| Born quadratic proof (`trace_mul_cycle` + outer-product expansion + `RCLike.re`/`‖·‖` bookkeeping) longer than estimated | Medium | It's a well-known identity, but Mathlib lemma names may need hunting. Budget extra time; fallback is bespoke calculation rather than tactic chains |
| Mathlib's `PosSemidef` API for `(1 - M)` — checking operator inequality on Hermitian matrices — less ergonomic than expected | Medium | State structure fields with `PosSemidef` directly, not via a `≤` instance; accept some verbosity |
| `Classical.choose` extraction of the Busch ρ in `pure_state_born_weights` awkward; uniqueness applied with wrong witness | Medium | Factor into a dedicated lemma "pure preparation ⇒ ρ = rankOneDensity ψ hψ" that applies `ExistsUnique.unique` cleanly |
| Group-action coherence (`onticAction 1 = id` etc.) needed after all | Low | Add fields to `SectorData` if a proof hits it |

## 6. Sorry scope

**Target: zero `sorry`s.** Each theorem above should be provable from the axiom statements + Mathlib API without placeholders. If any proof requires a stepping-stone we can't close immediately, it gets lifted into the axiom surface (deliberately, with documentation) rather than left as `sorry`.

## 7. Root-file updates

`CsdLean4.lean` (explicit import list) adds:
```lean
import CsdLean4.LF2.Setup
import CsdLean4.LF2.MeasureBridge
import CsdLean4.LF2.Weights
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.Interface
```

`CsdLean4/Basic.lean` is unchanged (it re-exports via `MainTheorem`; after LF2, `Interface` becomes the natural "deepest" leaf, so we may add `import CsdLean4.LF2.Interface` there for convenience). Decision: mirror the LF1 pattern — single import of the deepest module.

`CLAUDE.md` gets an LF2 section mirroring the LF1 structure: module chain, internal vs. imported, key lemmas for future layers (LF3+).

## 8. Implementation order (suggested)

1. `Setup.lean` — new structure, compiles.
2. `Interface.lean` skeleton (just the Measure.map_apply wrapper) — sanity-check LF1 interop.
3. `MeasureBridge.lean` — lemmas (a), (b), (c) without the axiom first; then axiom + (d).
4. `Weights.lean`.
5. `BornWrapper.lean` — largest new module (~200–300 lines). Order within: structures (`Effect`, `DensityOperator`) → `traceForm` → `rankOneEffect`/`rankOneDensity` + auxiliary lemmas → `born_quadratic` proof → `OperationalPackage` → Busch axiom → `born_form_of_package` → `pure_state_born_weights`. This is where shape iteration happens; each step builds on the previous.
6. Tighten `Interface.lean` corollary linking to `LF1_main_theorem_ae`.
7. Root import update, CLAUDE.md LF2 section, build green.
