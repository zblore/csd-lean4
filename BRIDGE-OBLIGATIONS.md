# BRIDGE-OBLIGATIONS.md

Ledger of every load-bearing structural field across all
`CsdLean4/Empirical/CSD/` bridge files, with its `specs/LF4-todo.md`
cross-reference. Parallel to [`AXIOMS.md`](AXIOMS.md) (per-theorem
axiom audit) and managed under the same discipline.

This file is the canonical record of every externally-supplied
hypothesis that CSD-side bridge bundles carry pre-LF4. The intent is
intellectual honesty: a reader should be able to see, in one place,
exactly what the `Empirical/CSD/` content is and is not claiming.

## 1. Discipline (mandatory for all `Empirical/CSD/` files)

Three rules, per `specs/empirical-csd-bridge-plan.md` §5:

### 1.1 Status-marker template

Every Bridge field that is an LF4 discharge target carries:

- A dedicated docstring marker
  `**Status: load-bearing, externally supplied, undischarged.**`.
- A one-line cross-reference to a numbered item in `specs/LF4-todo.md`.

Working example: `CsdLean4/LF3/PurePreparation.lean`'s
`PureSingletPreparation.bridge_op_p` cites LF4-todo §2 + §7. This
template is mandatory for every new Bridge field.

### 1.2 No-new-obligations-without-LF4-todo-PR

New Bridge files **cannot** introduce LF4 obligations not already in
`specs/LF4-todo.md`. If a new file needs a new obligation:

1. Add the obligation to `LF4-todo.md` in a separate PR, with explicit
   justification.
2. **Then** land the Bridge file referencing the new obligation.

Prevents Bridge accretion from quietly expanding LF4 scope.

### 1.3 Ledger audit per release

This file (`BRIDGE-OBLIGATIONS.md`) is updated in the same commit as
any change to a Bridge bundle field or LF4-todo item. Audit the ledger
for drift cross-Bridge-file at each release tag.

## 2. Current load-bearing fields

### 2.1 LF3 singlet bundle (pre-existing, since 2026-05-18)

Used by `Empirical/CSD/Bell.lean` (and `Empirical/QM/Bell.lean` via
the LF3 chain capstones it re-exports).

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `LF3.PureSingletPreparation` | `bridge_op_p` | `∀ s t, prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))` | §2 + §7 |
| `LF3.MeasurementJointEig` | `born_eq_P_st` | `∀ s t, ‖inner ℂ ψ (eig s t)‖ ^ 2 = P_st ctx.a ctx.b s t` | §2 + §7 |

Both fields are carried inside `CsdLean4/LF3/PurePreparation.lean` and
`CsdLean4/LF3/SingletProjective.lean` respectively. They are
re-exported into the CSD-side bridge content via the chain capstone
re-exports in `CsdLean4/Empirical/CSD/Bell.lean`.

### 2.2 LF2 measure-bridge (pre-existing, since LF2 v1.00)

Used by `Empirical/CSD/Framework.lean`'s `Context` bundle.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.Context` | `bridge : LF2.MeasureBridgeData D μFS` | `π_*μL = c • μFS` + G-invariance, derived via `LF2.MeasureBridgeData.ofSectorData` citing `invariant_measure_uniqueness` | §8 (LF4 Kähler instantiation gives the concrete `SectorData`) |

Note: `invariant_measure_uniqueness` is an LF2 axiom, not a bundle
field — its provenance is in `AXIOMS.md §2.1`. The `bridge` field
above is the *consumer* side of that axiom in the CSD framework.

### 2.3 CSD cloning bundle (added 2026-05-21)

Used by `Empirical/CSD/NoCloning.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.NoCloning.CSDCloningBundle` | (whole bundle's CSD-realisability content) | the Hilbert-space `U` carried by the bundle arises as the projective-action lift of a measure-preserving π-equivariant flow on `Σ × Σ`, for the bundle's `SectorData D`; equivalently, `U` is "CSD-substrate-realisable" | §13 |

Unlike `PureSingletPreparation.bridge_op_p` (which is a specific
field carrying a specific identity), the `CSDCloningBundle`
load-bearing content is implicit in the act of constructing the
bundle — callers asserting "this is a `CSDCloningBundle`" implicitly
commit to LF4-todo §13's realisability claim about the bundle's `U`
field. Pre-LF4 this is structural; post-LF4 it becomes provable from
the concrete Kähler `SectorData`.

The bundle does not carry a dedicated `csd_realisation : Prop` field
because the realisability is a property of the entire (`U`, ontic
substrate, tensor structure) combination rather than a localised
identity. A structurally vacuous `True`-typed field would be an
antipattern; the docstring on the structure carries the LF4-todo §13
citation directly.

## 3. Pending bridge content (planned, not yet landed)

Per `specs/empirical-csd-bridge-plan.md` §4, the following bridge
files are planned but not yet written. Each will add new load-bearing
fields that must satisfy the §1 discipline. The expected obligations
are listed here for early visibility; the actual LF4-todo amendments
will be made in the respective landing PRs.

| File | Expected new bundle(s) | Anticipated load-bearing fields | Anticipated LF4-todo |
|---|---|---|---|
| `Empirical/CSD/Multipartite/GHZ.lean` | `PureGHZPreparation`, `TripartiteJointEig` | `bridge_op_p` (tripartite), `born_eq_<sigma_x>_etc` | §2 + §7 (existing); possibly new tripartite-specific item |
| `Empirical/CSD/Contextuality/KS18.lean` | `KSAssignmentBundle` | per-basis ontic-weight ↔ OP.p bridge (9 of them) | §2 + §7 (existing); possibly new projector-partition-specific item |
| ~~`Empirical/CSD/NoCloning.lean`~~ | ~~`CSDIsometryBundle`~~ | ~~π-equivariance of isometry candidate; non-existence target~~ | **DONE 2026-05-21** (see §2.3 above; LF4-todo §13 added in the same change-set per discipline rule §1.2). |

The third item (`NoCloning`) is the only one anticipated to require a
new LF4-todo entry. Per rule §1.2, that PR must add the LF4-todo entry
*first*, with justification.

## 4. Relation to `AXIOMS.md`

`AXIOMS.md` records what Lean's `#print axioms` reports for headline
theorems. This file (`BRIDGE-OBLIGATIONS.md`) records what
*structural fields* CSD-side bridge bundles carry as hypotheses.

The two are complementary:

- `AXIOMS.md` answers "what mathematical axioms does this theorem cite?"
- `BRIDGE-OBLIGATIONS.md` answers "what physical/ontological hypotheses
  does this bundle ask the caller to supply (pending LF4)?"

A Bridge bundle's structural field that ends up extensionally invoked
inside a `#guard_msgs`-audited theorem will eventually appear in
`AXIOMS.md`'s output (if it's load-bearing for the theorem) — but only
once LF4 discharges the field with concrete content. Pre-LF4, the
field shows up only here.
