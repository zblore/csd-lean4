# CONVENTIONS.md

Module-level conventions for the `csd-lean4` formalisation. This file is the canonical placement / naming / quality policy for new and existing Lean modules in the repository.

It is companion to [`AXIOMS.md`](AXIOMS.md) (per-theorem axiom audit) and to [`README.md`](README.md) (project overview).

## 1. Three categories of local development

Every Lean module in this repository belongs to exactly one of three categories. The category determines its placement, its namespace, its allowed imports, and its quality bar.

### Category 1: Mathlib-track infrastructure

**What.** General mathematics that genuinely belongs in Mathlib eventually. CSD-free in content: depends on no CSD ontology, no `OnticSetup` / `SectorData` / `SystemApparatusSetup`, no Bell-state or singlet machinery.

**Placement.** `CsdLean4/Mathlib/<Mathlib-natural-path>/<Module>.lean`. The path mirrors where the module would eventually live in Mathlib. Example: a tensor-product-of-CLM module goes to `CsdLean4/Mathlib/Analysis/InnerProductSpace/TensorProductOps.lean`.

**Namespace.** Declarations live in their **natural Mathlib symbol namespace** (e.g. `ContinuousLinearMap` for `ContinuousLinearMap` lemmas), so dot notation is preserved. The file path `CsdLean4/Mathlib/<path>/` is the staging signal; when upstreamed, the file moves to or is appended onto the matching Mathlib path with no symbol rename. This is the Aesop / `Std4` convention. Earlier drafts of this document specified a `CsdLean4.Mathlib.<path>` outer-namespace wrapper to avoid Mathlib homonym collisions; in practice the cost (loss of dot notation, every lemma path is verbose) outweighs the benefit (rare collisions are easier to handle by renaming the specific lemma at upstream time).

**Allowed imports.** Mathlib only. No imports from `CsdLean4/Framework/`, `CsdLean4/LF*/`, `CsdLean4/Tests/`, or other CSD-specific subtrees.

**Quality bar.** Mathlib house style: snake_case lemma names; universe polymorphism where natural; minimal hypotheses (avoid baking in concrete `Fin N` if `Module` suffices); docstrings explaining the statement and provenance; one declaration's content per logical paragraph.

**Provenance note.** Every Cat-1 declaration carries an inline `**Provenance.**` note recording where in the CSD tree it was originally needed. This makes the upstreaming PR description easy to write and protects against accidentally orphaning a lemma whose only consumer was removed.

**Examples currently in the repository.**

- `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` —
  declarations live under `namespace Projectivization` (Mathlib's
  natural symbol namespace), not `CsdLean4.Mathlib.LinearAlgebra.Projectivization.*`.
  This is intentional and matches the convention above (preserve dot
  notation; the `CsdLean4/Mathlib/...` *path* is the staging signal,
  not an outer-namespace wrapper).
- `CsdLean4/Mathlib/Topology/Algebra/Module/LinearMap.lean` —
  declarations under `namespace ContinuousLinearMap`, same rationale.

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
- `7-SigmaLayer` — Category 3 (programme-specific), reserved for the FND "Choice A" ontology layer
  (`CsdLean4/SigmaLayer/`, namespace `CSD.SigmaLayer`): the anti-circularity postulate/bridge/theorem-target layer
  (`ConstraintDynamics`, `ChoiceASector`, `DeisolationModel`, the P1–P9 / B1–B7 / T1–T16 ledger). It is a
  Category-3 tag with its own directory and namespace, not a fourth top-level category; the `7-` prefix
  simply names the FND stratum. Allowed imports: as Category 3, plus earlier `CsdLean4/LF<m>/` layers.
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

## 6. Self-adjointness convention (LF3)

LF3 modules state self-adjointness on continuous linear maps via the inner-product equation `∀ x y, inner ℂ (T x) y = inner ℂ x (T y)` rather than Mathlib's `IsSelfAdjoint T`. This is forced by typeclass synthesis at v4.29.0-rc8:

- `Star (H →L[ℂ] H)` requires `[CompleteSpace H]`.
- Mathlib does not automatically chain `[FiniteDimensional ℂ H] → [CompleteSpace H]` (the `FiniteDimensional.proper_real → CompleteSpace` chain exists for ℝ but does not navigate from ℂ-finite-dim through `NormedSpace ℝ ℂ` automatically).

Diagnostic re-audit on 2026-05-18 confirmed: adding `[CompleteSpace H]` as an explicit typeclass argument resolves the issue, but cascades to every caller. The current `inner ℂ (T x) y = inner ℂ x (T y)` spelling is mathematically equivalent and avoids the cascade.

**For new modules.** Use the inner-product equation spelling until Mathlib's instance chain navigates `FiniteDimensional ℂ → CompleteSpace`, or until you're extracting to `Framework/` and willing to add the `[CompleteSpace _]` typeclass burden throughout.

**LF4 extraction note.** When LF3's pointer / projector / Hamiltonian structures move to `CsdLean4/Framework/Measurement/` (LF4-todo §10.2), the natural choice is to add `[CompleteSpace K]` typeclass arguments and switch to `IsSelfAdjoint T`. The Framework-level reusable form benefits from Mathlib-canonical naming; the typeclass cascade is acceptable when those modules are explicitly intended for reuse.

## 7. Relation to upstreaming

Cat-1 modules are eligible to be opened as Mathlib PRs once their content is stable. The repository does not block on upstreaming: Cat-1 modules live in `CsdLean4/Mathlib/` and are imported normally until and unless the upstreaming lands.

Timelines vary by item. Small lemmas can land in days to weeks with engagement from a Mathlib reviewer. Substantive framework (effect algebras, operator exponentials on finite-dim Hilbert, Haar on compact homogeneous spaces) is months to years.

The corpus does not prioritise upstreaming over programme progress. The conventions exist to keep the option open, not to commit to it.

## 8. Conventions adopted from the Lean-QIT / Physlib comparison (2026-07-20)

Drawn from an inspection of the QuAIR/Lean-QIT source and Physlib's contribution rules. Most of these also move the corpus toward Physlib's requirements, so adopting them serves both hardening and the upstreaming route. Each item below is marked with its **status**: *already-satisfied* (we do this or better), *policy* (adopted as a rule for new work), or *to-implement* (a concrete follow-up task, tracked in [`specs/BACKLOG.md`](specs/BACKLOG.md)).

### 8.1 Zero-axiom discipline — *policy + to-implement*

No `axiom` declarations anywhere in the corpus. This is Physlib's hard rule ("never use the `axiom` declaration") and the single change that both hardens the corpus and unblocks the canonical upstreaming route.

- **Current state.** Exactly **one** `axiom` declaration exists: `busch_effect_gleason` (`LF2/BornWrapper.lean`; the imported effect-Gleason step, [`AXIOMS.md §2.2`](AXIOMS.md)). Per settled non-goal **NG2** ([`reconstruction-status.md §7a`](specs/reconstruction-status.md)) the ontic Born rule is Gleason-free and this axiom is *cosmetic* — most exports are already `busch_effect_gleason`-free (foundational-triple only).
- **Target.** Discharge or delete `busch_effect_gleason` (finite-dim effect-Gleason, tracked M-tier in `BACKLOG.md`), reaching "three axioms, zero imported" (`propext`, `Classical.choice`, `Quot.sound` only).
- **Enforcement.** Add a **CI zero-user-axiom gate** to `scripts/check-claims.sh`: fail on any `^axiom ` declaration under `CsdLean4/` outside the one whitelisted site (and empty the whitelist once `busch_effect_gleason` is gone). This complements — does not replace — the `#print axioms` pins.

### 8.2 Machine-readable provenance — *policy + to-implement*  (biggest structural win)

A structured `REFERENCES.json` at repo root, and line-precise citations from module docstrings.

- **`REFERENCES.json`** — one entry per source, e.g.
  ```json
  { "key": "Busch2003", "title": "Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem",
    "authors": ["Paul Busch"], "year": 2003, "kind": "article",
    "arxiv_id": "quant-ph/9909073", "doi": "10.1103/PhysRevLett.91.120403", "url": null }
  ```
  Keys are stable citation handles (`Busch2003`, `Wilde2011Qst`, and the CSD preprint itself).
- **Line-precise citations** in docstrings: `[Busch2003, §3]` for external sources and — the foundations-project advantage — `[CSDPreprint, §14.2:L120-134]` pointing at the exact line range of the CSD manuscript each theorem formalises. This makes claims *auditable rather than assertable*, which is exactly what a referee wants.
- **Relation to existing practice.** This is the machine-readable upgrade of the current "always cite `specs/future-work.md` + cross-link theorem names" habit. The `References:` line every module already carries becomes a set of `REFERENCES.json` keys plus line ranges.

### 8.3 The `_statement` / `_of_` / final-theorem pattern — *policy*  (formalises the bridge-obligations ledger)

Three layers per major result:

```lean
-- 1. What the source CLAIMS, as a Prop, decoupled from any proof.
def bornFromVolume_statement (S : SectorData) : Prop := …

-- 2. Conditional theorems taking each ingredient as an explicit hypothesis (…_of_…).
theorem bornFromVolume_of_typicality (S : SectorData) (hTyp : …) : bornFromVolume_statement S := …

-- 3. The payoff: a final theorem with NO side hypotheses.
theorem bornFromVolume (S : SectorData) : bornFromVolume_statement S := …
```

This is a direct upgrade for [`specs/BRIDGE-OBLIGATIONS.md`](specs/BRIDGE-OBLIGATIONS.md): obligations stop being prose in markdown and become **explicit `_of_` hypotheses in code**. Discharging an obligation becomes the visible act of *removing a hypothesis from the final theorem* — machine-checked, and unconditionality is legible at a glance. New bridge results should be shaped this way; the existing prose ledger is migrated opportunistically (not a mass refactor of tagged, axiom-audited layers).

### 8.4 File header and build hygiene — *mixed*

Standard file opening (adapted to this project — copyright and authors are ours, not QuAIR's):

```lean
/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module
public import CsdLean4.LF2.BornWrapper

/-! # <Module name>
… prose, with **Category:** line (§2) and `[Key, file:Lstart-Lend]` citations (§8.2) …
-/
@[expose] public section
```

- **Copyright / licence / authors block** — *policy.* Mathlib-style. Existing files carry `Copyright (c) 2026 CSD contributors`; that is grandfathered (not worth a mass rewrite). New files use the block above with `Authors: Zayn Blore`; an explicit `Authors:` line is the new requirement.
- **Lean 4 module system** (`module` / `public import` / `@[expose] public section`) — *to-implement (migration).* All current files use legacy `import`. Mathlib (v4.33) is on the module system, so the migration is now possible; it is a large, mechanical, separate pass tracked in `BACKLOG.md`, not a per-file requirement yet.
- **`open scoped …`, `namespace`, `universe`, `noncomputable section`** in that order — *policy* (already the de-facto ordering; make it explicit).
- **`autoImplicit=false`** — *to-implement.* Add `moreLeanArgs = ["-DautoImplicit=false"]` (or `leanOptions`) to `lakefile.toml` to kill accidental implicit binders. Must be landed with a full green build (it can surface latent implicit-binder reliance), so it is a dedicated commit, not a silent flip.
- **Mathlib pin** — *policy, with a caveat.* Prefer a **tagged** Mathlib release matching the pinned toolchain over a bare commit SHA (a tag is more legible). **Caveat / current state:** the repo intentionally tracks **Mathlib master HEAD** (commit `c732b96d`, Lean `v4.33.0-rc1`) to stay on the newest APIs; a pinned SHA is still fully reproducible, just less legible than a tag. Revisit and switch to a tag when a tagged release catches up to the toolchain we need.
- **Docstring on every declaration** — *near-satisfied → policy.* The corpus is already close (~1 docstring per 12 lines); make "every `def`/`theorem`/`instance` carries a docstring" an enforced rule for new modules.

### 8.5 What NOT to adopt

- **Their monolithic 200–250 KB files.** Our one-result-per-file discipline (§1, ~291 lines/file) is better and matches how the material is reviewed. Keep it.
- **Their CI's lack of an explicit `sorry`/`axiom` gate.** Our axiom-audit harness (`Tests/AxiomAudit.lean`, the `#print axioms` pins) plus `check-claims.sh` is *superior*. Keep it; §8.1 only adds a zero-`axiom`-declaration gate on top.

### 8.6 Suggested adoption order

1. **Zero-axiom** (§8.1) — gates the Physlib route; add the CI gate now, discharge `busch_effect_gleason` when the effect-Gleason M-item lands.
2. **`REFERENCES.json` + line-precise citations** (§8.2) — the biggest auditability win.
3. **`_statement` / `_of_` pattern** (§8.3) — formalises the bridge-obligations ledger.
4. **`autoImplicit=false`, module system, tagged pin, per-declaration docstrings** (§8.4) — fold the mechanical items into the next toolchain/module-system pass.

Provenance: the 2026-07-20 Lean-QIT / Physlib overlap analysis.
