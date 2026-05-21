# Empirical/CSD/ bridge architecture plan

Plan landed 2026-05-21. Architectural commitment for the dual-perspective
empirical-prediction structure (QM-validity content paired with CSD
volume-ratio readings).

## 0. Why this plan exists

The existing `CsdLean4/Empirical/` files (`Bell.lean`, `NoCloning.lean`,
`Multipartite/GHZ.lean`, `Contextuality/KS18.lean`) formalise QM-validity
content only: pure linear-algebra theorems on `EuclideanSpace ℂ (Fin n)`
with Pauli operators, with experimental provenance docstrings. The
CSD ontic substrate (Σ, μL, π, prepMeasure, OnticSetup, SectorData)
does not appear in their proofs.

The **only** existing CSD-side reading of an empirical item is the
LF3 chain capstones for the singlet (six `LF3_singlet_frequency_convergence*`
variants in `LF3/Interface.lean`), which use the `PureSingletPreparation`
bundle to state the CSD volume-ratio reading abstractly with the
LF4-discharge hypothesis (`bridge_op_p`) explicitly carried.

For everything else, the CSD-side reading is a verbal caveat at the
bottom of each file's module docstring. This plan promotes the verbal
caveat to a formal companion theorem per item.

## 1. Architectural decision

**Adopt `CsdLean4/Empirical/CSD/<phenomenon>.lean` sub-subtree.** Move
the existing four QM-validity files to `Empirical/QM/<phenomenon>.lean`
for symmetry.

### Alternatives considered and rejected

- **Top-level `Bridge/` subtree** — name implies a logical layer (peer
  of LF1-5). It is not. Misleads readers into expecting load-bearing
  new theory.
- **Top-level `Interpretation/CSD/`** — equivalent extensibility but the
  word *interpretation* is contested in CSD literature (the programme
  aims to be a fundamental theory, not an interpretation of QM).
  Naming would prejudice the framing.
- **Inline two-section files** — putting LF4-discharge hypotheses in a
  file currently provably axiom-clean (e.g. `NoCloning.lean`) silently
  degrades that file's Cat-2 promotion-readiness flag.

### Final layout

```
Empirical/
  QM/
    Bell.lean                                  (moved from Empirical/Bell.lean)
    NoCloning.lean                             (moved)
    Multipartite/GHZ.lean                      (moved)
    Contextuality/KS18.lean                    (moved)
  CSD/
    Framework.lean                             (shared CSDBridgeContext bundle)
    Bell.lean
    NoCloning.lean
    Multipartite/GHZ.lean
    Contextuality/KS18.lean
```

Future expansion to other foundational interpretations
(`Empirical/Bohmian/`, `Empirical/Everettian/`, `Empirical/Operational/`)
is **structurally clean** under this layout — see §6 below for the
concrete extension scenario.

## 2. Bundle design

### Single shared LF2-only context, not three separate structures

My initial off-the-cuff sketch proposed three separate bundles
(`CSDFlow`, `CSDMeasurement`, `CSDCircuit`). The plan rejected this:
each would redundantly carry `D : SectorData + μFS + bridge`. Cleaner
abstraction: **one** `CSDBridgeContext D` carrying the shared LF2
discharge data once, plus **content-specific** preparation bundles
that mirror `PureSingletPreparation`.

Under this design:

- A "unitary flow" is a *theorem* (π-equivariance of `U` against the
  ontic-action) parametric on the context. Not a separate structure.
- A "measurement" is a *partition of preEvent regions with OP-bridge
  identities*. Same.
- A "circuit" is a sequential composition. Same.

### Shared framework bundle skeleton

```lean
-- Empirical/CSD/Framework.lean (LF2-only imports)
structure CSDBridgeContext
    (D : LF2.SectorData SigmaSpace P G) where
  μFS         : Measure P
  hμFS_prob   : IsProbabilityMeasure μFS
  bridge      : LF2.MeasureBridgeData D μFS
```

### Per-phenomenon bundle pattern

Each `Empirical/CSD/<phenomenon>.lean` defines a `Pure<Phenomenon>Preparation`
bundle that `extends CSDBridgeContext D` and adds phenomenon-specific
fields. Example (GHZ):

```lean
structure PureGHZPreparation
    (D : LF2.SectorData SigmaSpace P G)
    (ctx : TripartitePauliContext) (N : ℕ)
  extends CSDBridgeContext D where
  PP             : LF2.PurePreparation D prepMeasure N
  hN             : 2 ≤ N
  jed            : TripartiteJointEig ctx PP.ψ
  O_region       : (Sign × Sign × Sign) → D.toOntic.OutcomeRegion
  bridge_op_p    : ∀ stu, prepMeasure((O_region stu).preEvent)
                          = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig stu)))
                          -- LF4 discharge target, LF4-todo §2 + §7
```

Same template for `PureKSAssignment` (18-vector partition + per-basis
weight identity) and `PureCloningPreparation` (two-state pair +
isometry-non-existence target).

### Chain capstone composition

Each per-item file's headline theorem composes the bundle's
`weight_eq_<phenomenon>` lemma with `LF1_main_theorem_ae`, exactly as
`LF3_singlet_frequency_convergence` already does for the singlet.

## 3. Dependency boundary

- `Empirical/CSD/Framework.lean` imports **only** `LF2/Interface.lean`
  and `LF2/Preparation.lean`. No LF3 imports in the framework.
- Each per-item file imports the framework **plus** whichever LF3
  content it needs:
  - Bell: full singlet machinery (already exists).
  - GHZ: needs new tripartite Pauli + tripartite joint eigenstate
    infrastructure (LF3 currently bipartite throughout).
  - KS: 18-vector projector partition; no time evolution, no joint
    eigenstate.
  - No-cloning: two-state preparation pair + isometry.

LF3 imports live in the per-item file, not the framework.

## 4. Retrofit cost (honest, asymmetric)

| Item | Effort | Notes |
|---|---|---|
| Bell | ~2-3 days | LF3 chain capstones already do the work; mostly re-export + framing prose. |
| GHZ | ~1 week | **Dominant cost**: needs new tripartite Pauli infrastructure (LF3 `Singlet/` is bipartite throughout). New `PureGHZPreparation` bundle + tripartite joint-eigenstate bundle. |
| KS | ~3-4 days | Lighter: new `KSAssignmentBundle D` carrying the 9 outcome-region partitions + per-basis ontic-weight ↔ OP.p bridge. Combinatorial impossibility transfers unchanged. |
| No-cloning | ~3-4 days | Needs `CSDIsometryBundle D` carrying π-equivariance of `U` against a projective unitary; then state "no such bundle exists for cloning". Isometry impossibility = LF4-discharge target pre-LF4. |

**Total: ~2.5-3 weeks honest.** GHZ is the bottleneck.

## 5. LF4 obligation co-design discipline

Pre-LF4 accumulation of bridge files **does** implicitly co-design LF4.
This is unavoidable but manageable via three rules:

1. **Status marker on every load-bearing field.** Every Bridge field
   that is an LF4 discharge target carries:
   - A dedicated docstring marker
     `**Status: load-bearing, externally supplied, undischarged.**`
   - A one-line cross-reference to a numbered item in
     `specs/LF4-todo.md`.

   The existing `PureSingletPreparation.bridge_op_p` already does this
   (cites LF4-todo §2 + §7). This template becomes mandatory.

2. **No-new-obligations-without-LF4-todo-PR rule.** New Bridge files
   cannot introduce LF4 obligations not already in `LF4-todo.md`. If a
   new file needs a new obligation, the obligation is added to LF4-todo
   *first*, in a separate PR, with explicit justification. Prevents
   Bridge accretion from quietly expanding LF4 scope.

3. **`BRIDGE-OBLIGATIONS.md` ledger.** Parallel to `AXIOMS.md`. Lists
   every load-bearing Bridge field across all `Empirical/CSD/` files
   with its LF4-todo citation. Audit obligation drift cross-Bridge-file
   each release.

## 6. Extensibility to other foundations

Concrete scenario: a Bohmian companion `Empirical/Bohmian/Bell.lean`.

A Bohmian file would:
1. Declare a `PilotWaveBundle ψ Q₀` carrying the wavefunction and
   initial configuration data.
2. State `bohmian_singlet_frequency_convergence` from a
   `BohmianTrialModel` with conditional-probability hypotheses.
3. Mark *Bohmian-specific* discharge targets (e.g. the quantum
   equilibrium hypothesis) the same way CSD marks LF4 targets.

The structural template — preparation bundle + theorem composition +
named discharge targets — transfers without restructuring. The CSD
framework bundles do **not** leak into the Bohmian subtree because
`CSDBridgeContext` is import-isolated to `Empirical/CSD/`.

Same template for `Empirical/Everettian/<phenomenon>.lean` (branch-weight
bundle), `Empirical/Operational/<phenomenon>.lean` (Hardy-style
operational axiom bundle).

The strongest argument for `Empirical/CSD/` over a CSD-prefixed
top-level: it generalises a **working pattern** (the LF3
`PureSingletPreparation` template) rather than inventing a new
abstraction. Anything that fits "preparation bundle + chain capstone +
discharge hypotheses" drops in.

## 7. Implementation tranche 0

Execution order, all pre-LF4:

1. **Move existing four to `Empirical/QM/`** (~1 day; mechanical,
   `git mv` to preserve history). Update imports in
   `CsdLean4.lean` root and `Tests/AxiomAudit.lean`.
2. **Land `Empirical/CSD/Framework.lean`** with `CSDBridgeContext`
   (~1 day).
3. **Land `Empirical/CSD/Bell.lean`** as the first companion
   (~2-3 days; mostly re-export of existing LF3 chain capstones).
4. **Add `BRIDGE-OBLIGATIONS.md`** ledger and update `LF4-todo.md`
   with the three discipline rules from §5 (~1 day).

Total Tranche 0: ~5-7 days.

After Tranche 0, the corpus has the two-perspective structure
established. Subsequent retrofits (GHZ, KS, NoCloning) and new
gate/algorithm Bridge companions follow the same pattern.

## 8. Out of scope for this plan

- The Tranche 1+ gate / algorithm work (Hadamard, CNOT, DJ, etc.).
  Those follow once Tranche 0 lands and the framework is proven.
- LF4 concrete Kähler instantiation that would discharge any of the
  Bridge bundles' LF4 hypotheses. Paper-blocked.
- Density-matrix / mixed-state content (LF5 territory).
- Other foundational interpretations (Bohmian, Everettian). Mentioned
  in §6 to verify extensibility; not actually planned.
