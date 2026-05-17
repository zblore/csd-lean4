# CONVENTIONS.md

Module-level conventions for the `csd-lean4` formalisation. This file is the canonical placement / naming / quality policy for new and existing Lean modules in the repository.

It is companion to [`AXIOMS.md`](AXIOMS.md) (per-theorem axiom audit) and to [`README.md`](README.md) (project overview).

## 1. Three categories of local development

Every Lean module in this repository belongs to exactly one of three categories. The category determines its placement, its namespace, its allowed imports, and its quality bar.

### Category 1: Mathlib-track infrastructure

**What.** General mathematics that genuinely belongs in Mathlib eventually. CSD-free in content: depends on no CSD ontology, no `OnticSetup` / `SectorData` / `SystemApparatusSetup`, no Bell-state or singlet machinery.

**Placement.** `CsdLean4/Mathlib/<Mathlib-natural-path>/<Module>.lean`. The path mirrors where the module would eventually live in Mathlib. Example: a tensor-product-of-CLM module goes to `CsdLean4/Mathlib/Analysis/InnerProductSpace/TensorProductOps.lean`.

**Namespace.** `CsdLean4.Mathlib.<Mathlib-natural-path>`. Shim form: when upstreamed, a one-time rename pass replaces `CsdLean4.Mathlib.` with `Mathlib.`. Chosen over direct `Mathlib.*` namespace to avoid homonym collisions if Mathlib later adds the same name.

**Allowed imports.** Mathlib only. No imports from `CsdLean4/Framework/`, `CsdLean4/LF*/`, `CsdLean4/Tests/`, or other CSD-specific subtrees.

**Quality bar.** Mathlib house style: snake_case lemma names; universe polymorphism where natural; minimal hypotheses (avoid baking in concrete `Fin N` if `Module` suffices); docstrings explaining the statement and provenance; one declaration's content per logical paragraph.

**Provenance note.** Every Cat-1 declaration carries an inline `**Provenance.**` note recording where in the CSD tree it was originally needed. This makes the upstreaming PR description easy to write and protects against accidentally orphaning a lemma whose only consumer was removed.

**Examples currently in the repository.**

- `CsdLean4/Util/MathlibCandidates.lean` (will move to `CsdLean4/Mathlib/Topology/Algebra/Module/LinearMap.lean` or similar when content grows past 3-4 lemmas).

### Category 2: CSD-adjacent framework infrastructure

**What.** Framework-level CSD-style infrastructure that should be reusable beyond this specific corpus. Includes the data structures that encode CSD's framework but not its programme-specific content: e.g. abstract pointer-readout patterns, context-indexed outcome-map skeletons, leakage-bound packaging, abstract Born-wrapper machinery.

**Placement.** `CsdLean4/Framework/<Topic>/<Module>.lean`. The `Framework/` subtree does not exist yet (no modules currently classified there). It will be created when LF4 produces the first Cat-2 candidate.

**Namespace.** `CsdLean4.Framework.<Topic>`.

**Allowed imports.** Mathlib, `CsdLean4/Mathlib/`. No imports from `CsdLean4/LF*/` (Framework must be programme-independent).

**Quality bar.** Mathlib-style readability, but does not need to be CSD-free. May encode framework structure that is specifically CSD-adjacent (pointer projectors, basin language). Other formalisation programmes (Bohmian, Everettian, operational reconstruction) should in principle be able to import a Framework module without buying into CSD's specific axioms.

**Examples currently in the repository.** None yet. The initial classification pass tags every existing module by its **current location**, not its conceptual category. Modules under `LF*/` stay Cat-3 even if their content is reusable framework infrastructure (e.g. `LF2/BornWrapper.lean`'s `Effect` / `DensityOperator` machinery). Extraction to `Framework/` is deferred to LF4 and tracked as a separate decision per module.

### Category 3: Programme-specific (CSD layer content)

**What.** Programme-level content of the CSD corpus. Specific to the layer in which it appears: LF1 typicality content, LF2 Born wrapper as currently shaped, LF3 singlet machinery, future LF4/LF5 work.

**Placement.** `CsdLean4/LF<n>/<Module>.lean`.

**Namespace.** `CSD.LF<n>.<...>`.

**Allowed imports.** Mathlib, `CsdLean4/Mathlib/`, `CsdLean4/Framework/`, earlier `CsdLean4/LF<m>/` (for `m < n`).

**Quality bar.** Must build, must be `sorry`-free, must be axiom-audited via `CsdLean4/Tests/AxiomAudit.lean` for any headline theorem.

## 2. Per-module category declaration

Every module declares its category in a `**Category:**` line at the top of its module docstring `/-! -/` block.

**Format.** The `/-! -/` block sits **after** all imports (Lean treats `/-! -/` as a module-docstring command; commands cannot precede `import` statements).

```lean
import <Mathlib...>
import <CsdLean4...>

/-!
# <Module name>

**Category:** <N>-<Tag> (<one-line rationale in parentheses>).

<existing module prose>
-/
```

Where `<N>-<Tag>` is one of:

- `1-Mathlib` — Category 1, Mathlib-track infrastructure.
- `2-Framework` — Category 2, CSD-adjacent framework.
- `3-Local` — Category 3, programme-specific content.
- `Special` — for cross-cutting modules (top-level imports, regression tests, convenience re-exports).

The rationale parenthetical is one short noun phrase: "LF1-specific outcome regions"; "Mathlib-track CLM complement lemmas"; "cross-layer axiom regression".

Modules without an existing module docstring receive a minimal `/-! -/` block of one heading plus the `**Category:**` line.

## 3. Tests/ layout

Tests mirror the category structure. Within `Tests/`:

```
Tests/
  AxiomAudit.lean        -- cross-layer regression for all headline theorems
  Examples.lean          -- cross-layer smoke tests
  Mathlib/               -- tests for CsdLean4/Mathlib/ (empty until populated)
  Framework/             -- tests for CsdLean4/Framework/ (empty until populated)
  LF1/ LF2/ LF3/ LF4/    -- per-layer smoke tests (empty until populated)
```

Cross-layer tests at the top level. Per-category tests in the matching subdirectory. Subdirectories created on first use, not pre-emptively.

## 4. Reclassification policy

The initial pass tags every existing module by **current location**, not conceptual category. This is deliberate: retroactive moves of LF1-3 content would risk churn against axiom-audited, tagged releases without producing new theorem content.

Reclassification of an existing LF*/ module to `Framework/` happens only when LF4 needs the module's content in CSD-free form. The reclassification is a single commit per module, with the move tracked in `specs/LF4-todo.md` and `AXIOMS.md` updated accordingly.

New work follows the category discipline from the start: when an LF4 development produces a Cat-1 or Cat-2 module, it lives in the right subtree immediately.

## 5. Lint and enforcement

There is currently no automated lint. The `**Category:**` line is enforced by review.

Future enforcement (deferred until `Framework/` exists):

- A CI check that `CsdLean4/Mathlib/**/*.lean` modules import only Mathlib (no `CsdLean4.LF*`, no `CsdLean4.Framework.*`).
- A CI check that every module has a `**Category:**` declaration.

These are LF4-scope items, not v1.00 of the conventions doc.

## 6. Relation to upstreaming

Cat-1 modules are eligible to be opened as Mathlib PRs once their content is stable. The repository does not block on upstreaming: Cat-1 modules live in `CsdLean4/Mathlib/` and are imported normally until and unless the upstreaming lands.

Timelines vary by item. Small lemmas can land in days to weeks with engagement from a Mathlib reviewer. Substantive framework (effect algebras, operator exponentials on finite-dim Hilbert, Haar on compact homogeneous spaces) is months to years.

The corpus does not prioritise upstreaming over programme progress. The conventions exist to keep the option open, not to commit to it.
