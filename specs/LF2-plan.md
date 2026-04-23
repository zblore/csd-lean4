# LF2 implementation plan

Companion to `specs/LF2-v1.00.pdf` (extracted text: `specs/LF2-v1.00.txt`).
Drives implementation under `CsdLean4/LF2/`.

## 0. Scope and design choices (confirmed)

- **Abstract projective layer.** `CP^{N-1}` is represented as an abstract `MeasurableSpace P` with a distinguished reference measure `μFS` (required to be a probability measure). No use of Mathlib's `Projectivization`, no construction of the Fubini–Study form. Concrete instantiation is deferred.
- **Symmetry group is abstract.** `SU(N)` is represented by a type parameter `G : Type*` with `Group G` and measurable actions on `Σ` and `P`. The spec's concrete `SU(N)` appears nowhere in LF2 Lean source.
- **Minimal operational stubs.** `Effect`, `DensityOperator`, and effect-additive probability are declared as **minimal custom structures** inside `BornWrapper.lean`, with just enough content for the Busch axiom to have a well-typed statement. Mathlib's operator theory is not pulled in.
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

**This is the riskiest module.** The spec gives an "informal" Lean signature that references names (`Effect H`, `DensityOperator H`, `Tr`, `Effect.toMat`) that don't exist in Mathlib in that shape. We introduce **minimal local stubs**:

```lean
/-- Abstract placeholder for a finite-dimensional complex Hilbert space. -/
variable (H : Type*)

/-- Minimal effect-algebra stub: an effect is a self-adjoint operator with 0 ≤ E ≤ I.
    LF2 does not construct this; it is a local stub so the axiom statement is well-typed. -/
structure Effect where
  -- intentionally opaque; real content deferred to later layers
  dummy : Unit := ()

/-- Minimal density-operator stub. -/
structure DensityOperator where
  dummy : Unit := ()

/-- Trace pairing stub. -/
noncomputable def traceForm (ρ : DensityOperator H) (E : Effect H) : ℝ := 0

/-- Operational consistency package (spec Definition 5.1). -/
structure OperationalPackage where
  p         : Effect H → ℝ
  nonneg    : ∀ E, 0 ≤ p E
  le_one    : ∀ E, p E ≤ 1
  additive  : ∀ E F : Effect H, (∃ G : Effect H, True) → p E + p F = p E  -- placeholder shape
  -- spec clauses 1, 2, 3: finite-additivity, p(I)=1, unitary covariance
  -- exact shapes fixed at implementation time

/-- Imported Busch effect-Gleason theorem. For every operational package on a
    finite-dimensional Hilbert space with N ≥ 2, there is a unique density operator
    representing it in trace form. -/
axiom busch_effect_gleason
    (H : Type*) (N : ℕ) (hN : 2 ≤ N) -- dimension recorded as a parameter
    (OP : OperationalPackage H) :
    ∃! ρ : DensityOperator H, ∀ E, OP.p E = traceForm ρ E
```

**Born-form assignment.** A thin theorem stating that the combination of the measure bridge and an operational package yields a trace-form probability assignment:

```lean
theorem born_form_of_package
    (D : SectorData Sigma P G)
    (μprep : Measure Sigma) [IsProbabilityMeasure μprep]
    (H : Type*) (N : ℕ) (hN : 2 ≤ N)
    (OP : OperationalPackage H) :
    ∃! ρ : DensityOperator H, ∀ E, OP.p E = traceForm ρ E := by
  exact busch_effect_gleason H N hN OP
```

The literal `wᵢ = |⟨ψ|φᵢ⟩|²` identification is **not** formalized as a Lean equation — it requires inner products and concrete operator algebra that the abstract setup does not carry. This matches the spec's framing: the wrapper delivers existence of a trace-form density; the quadratic form is the corollary for rank-one projectors, interpreted informally.

**Proposal to flag at review:** if the user wants the quadratic form inside Lean, BornWrapper grows substantially (we'd need to import Mathlib inner-product-space machinery and build the identification for rank-1 projectors). The current plan keeps this as **out of scope** and records it as a "next-layer" task. Flagged in the risk register below.

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
| `BornWrapper.lean` | standalone (no Mathlib operator theory; just `Mathlib.Data.Real.Basic`) |
| `Interface.lean` | `CsdLean4.LF2.Weights`, `CsdLean4.LF1.Preparation`, `CsdLean4.LF1.Outcomes` |

Main Mathlib API used: `Measure.map`, `Measure.map_apply`, `MeasurePreserving`, `MeasurableEquiv`, `IsProbabilityMeasure`, `IsFiniteMeasure`.

No Jacobian / Radon–Nikodym API needed at this layer (spec §7.7).

## 5. Risk register

| Risk | Severity | Mitigation |
|---|---|---|
| `IsFiniteMeasure`/`IsProbabilityMeasure` instance plumbing trips up `measure_bridge` | Low | Adjust to `[IsFiniteMeasure μ]` as an explicit hypothesis if instance synthesis fails |
| Axiom statements don't compose cleanly with the theorems consuming them | Medium | Write consumers first as `example` blocks, tune axiom shapes, then lock them in |
| `OperationalPackage.additive` shape (finite additivity under `E + F ≤ I`) requires an abstract "E + F" we don't have | Medium | Make `OperationalPackage` parametric over an effect-addition operation, or encode the premise as `∃ G, p (E+F) = p G ∧ ...`. Finalise at implementation |
| User actually wants `|⟨ψ\|φᵢ⟩|²` in Lean (not just trace form via axiom) | High if triggered | Would require ~5× more work; keeping out of scope pending user decision |
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
5. `BornWrapper.lean` — axiom first, then consumers; this is where shape iteration happens.
6. Tighten `Interface.lean` corollary linking to `LF1_main_theorem_ae`.
7. Root import update, CLAUDE.md LF2 section, build green.
