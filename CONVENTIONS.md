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
- `7-SigmaLayer` — Category 3 (programme-specific), reserved for the SigmaLayer (the projective-sector ontology, Paper C)
  (`CsdLean4/SigmaLayer/`, namespace `CSD.SigmaLayer`): the anti-circularity postulate/bridge/theorem-target layer
  (`ConstraintDynamics`, `ProjectiveSector`, `DeisolationModel`, the P1–P9 / B1–B7 / T1–T16 ledger). It is a
  Category-3 tag with its own directory and namespace, not a fourth top-level category; the `7-` prefix
  simply names the SigmaLayer stratum. Allowed imports: as Category 3, plus earlier `CsdLean4/LF<m>/` layers.
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

### 8.1 Zero-axiom discipline — *ACHIEVED 2026-07-21*

No `axiom` declarations anywhere in the corpus. This is Physlib's hard rule ("never use the `axiom` declaration") and the single change that both hardens the corpus and unblocks the canonical upstreaming route.

- **Current state.** **Zero** `axiom` declarations. The last one, `busch_effect_gleason`, was **proved and deleted 2026-07-21** — it is now the theorem `OperationalPackage.effect_gleason_representation` in `LF2/EffectGleason.lean` ([`AXIOMS.md §2.2`](AXIOMS.md)). Every corpus export is now foundational-triple only (`propext`, `Classical.choice`, `Quot.sound`).
- **Enforcement (live).** `scripts/check-claims.sh` sets `DECLARED_AXIOMS=""` and **fails on any `^axiom ` declaration** under `CsdLean4/` (the whitelist is empty now that `busch_effect_gleason` is gone). This complements — does not replace — the `#print axioms` pins in `Tests/AxiomAudit.lean`.

### 8.2 Machine-readable provenance — *policy + SEEDED 2026-07-31, still to-implement*  (biggest structural win)

> **Status.** [`REFERENCES.json`](REFERENCES.json) now **exists**, created 2026-07-31 to carry the
> `[LeanQIT2026]` citation with the schema below. It holds **only** the entries that have a concrete
> consumer today (`LeanQIT2026`, `Busch2003`) — it is a seed, not coverage. The obligation proper —
> one entry per source, plus line-precise `[Key, file:Lstart-Lend]` citations in module docstrings —
> **remains open** in `specs/BACKLOG.md`. Do not read the file's size as the corpus's citation
> coverage.
>
> The `LeanQIT2026` entry also demonstrates the schema carrying something the original design did not
> anticipate: an **external discharge that is cited but deliberately not imported**, with the reason
> (toolchain skew), the current honest status (our result stays conditional), and the planned route
> (a separate bridge package). That is exactly the auditability §8.2 exists for — a reader can check
> the claim and see precisely what is and is not being asserted.

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

### 8.3a Names are claims: describe the construction, not the interpretation — *policy + ENFORCED 2026-08-04*

Lean checks that a proof establishes its statement. **Nothing** checks that a *name* is
honest about what its object is. Every defect the fourth and fifth external reviews found
lived in that gap, and one was a genuine error: `nullSeamLiouville` named a measure on
`S¹ × ℂℙ²` — real dimension 5, **odd**, hence not symplectic, so "Liouville" asserted
structure the space cannot carry. The theorems were all true; the identifier was the lie.

Rule: if a word carries mathematical content — *Liouville, symplectic, Kähler, Hamiltonian,
smooth, canonical, unique, complete, exhaustive* — then either

1. **make it a `Prop`** and discharge it (the corpus already does this: `IsFubiniStudyKahler`,
   `IsForcedKahlerVolume`, `BlockLudersObligation`), or
2. **name the object after its construction**, so the identifier states a fact rather than an
   interpretation: `nullSeamMeasure`, not `nullSeamLiouville`.

Enforced by `scripts/check-claims.sh` check (7): every declaration whose name contains
Liouville / symplectic / Kähler must be listed in `DECLARED_SYMPLECTIC_VOCAB` with its
arena's **dimension parity** recorded (symplectic ⇒ even). A new such name fails the guard,
which forces the parity question to be answered consciously rather than assumed.

**Parity is a reflex, not a lint.** This was the corpus's *second* odd-dimension slip — the
first was the fibred-Σ row, mislabelled "Mathlib-gated" when `ℂℙⁿ⁻¹ × AddCircle 1` is simply
odd-dimensional and admits no symplectic form at all. Before writing any of those words:
compute the real dimension and check it is even.

Companion, check (8): honest-scope phrases ("remains open", "recorded extension", "not
claimed here") are inventoried per file. They are *good* — they are how a module states its
boundary — so the inventory is not a budget to drive to zero. It exists because
`MeasurementCapstone.lean` still said the conditioned mixed update "remains open" hours
after `MixedLuders.lean` closed it. The guard fires when such a claim is added or removed;
it **cannot** see a claim that stays put while the fact beneath it changes. Discharging a
`BACKLOG.md` row therefore carries a mechanical companion step: re-read the sites check (8)
prints.

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

- **Copyright / licence / authors block** — *DONE 2026-07-22.* Mathlib-style, with an explicit `Authors: Zayn Blore` line. Back-applied to every file (the former `Copyright (c) 2026 CSD contributors` blocks were rewritten); it is now a hard requirement for new files.
- **Lean 4 module system** (`module` / `public import` / `@[expose] public section`) — *DONE 2026-07-22.* The whole corpus was migrated: every file is a `module` with `public import`s and a file-level `@[expose] public section` (the aggregator `CsdLean4.lean` and `CsdLean4.Basic` carry `module` + `public import`s with no section, like `Mathlib.lean`). New files must follow the template above. **Notes for new code:** a `module` file can only import other `module` files (legacy `import` files can't be imported from a module); an `@[expose]`-exposed public body may not reference a `private` declaration (make the helper non-`private`, or don't rely on cross-module unfolding); `#eval`/`meta` code over imported symbols needs a `meta import` (alongside the `public import`); and kernel `decide`/`rfl` over *imported* `Array`-style computations may not reduce at elaboration time — prefer a proven bridge lemma.
- **`open scoped …`, `namespace`, `universe`, `noncomputable section`** in that order — *policy* (already the de-facto ordering; make it explicit).
- **`autoImplicit=false`** — ***DONE 2026-07-31.*** `lakefile.toml` carries package-level `leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }`, so it applies to **both** `lean_lib` targets, tests included. Landed as its own commit with both targets green, as this entry required.
  - **Why it was promoted.** With `autoImplicit` on, an unresolved identifier in a signature is *silently auto-bound as a fresh implicit* rather than reported. On 2026-07-31 `CPN N` (which needed `LF4.CPN N` from outside the `CSD.LF4` namespace) was auto-bound instead of erroring, and surfaced as a cascade of unrelated elaboration failures — "Function expected at", "Unknown identifier `c.nonneg`" — none of which named the actual mistake. That is the failure mode this flag removes, and it matters more once anything external builds against the corpus, where a typo becomes a silent generalisation in a published signature.
  - **Cost of the migration: 5 edits in 3 files**, far less than the entry feared. `Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` (`S` in a `variable` line), `Mathlib/QuantumInfo/Reversible/ModMul.lean` (`n` in two theorem signatures), `SigmaLayer/{CircleFibre,CircleRecord,TorusFibre}.lean` (a missing `variable {n : ℕ}`). Every fix was adding an explicit binder; no proof changed.
- **Mathlib pin** — *policy, with a caveat.* Prefer a **tagged** Mathlib release matching the pinned toolchain over a bare commit SHA (a tag is more legible). **Caveat / current state:** the repo intentionally tracks **Mathlib master HEAD** (commit `c732b96d`, Lean `v4.33.0-rc1`) to stay on the newest APIs; a pinned SHA is still fully reproducible, just less legible than a tag. Revisit and switch to a tag when a tagged release catches up to the toolchain we need.
- **Docstring on every declaration** — *near-satisfied → policy.* The corpus is already close (~1 docstring per 12 lines); make "every `def`/`theorem`/`instance` carries a docstring" an enforced rule for new modules.

### 8.5 What NOT to adopt

- **Their monolithic 200–250 KB files.** Our one-result-per-file discipline (§1, ~291 lines/file) is better and matches how the material is reviewed. Keep it.
- **Their CI's lack of an explicit `sorry`/`axiom` gate.** Our axiom-audit harness (`Tests/AxiomAudit.lean`, the `#print axioms` pins) plus `check-claims.sh` is *superior*. Keep it; §8.1 only adds a zero-`axiom`-declaration gate on top.

### 8.6 Suggested adoption order

1. **Zero-axiom** (§8.1) — **DONE 2026-07-21**: `busch_effect_gleason` discharged, CI gate live (empty whitelist). Gates the Physlib route.
2. **`REFERENCES.json` + line-precise citations** (§8.2) — the biggest auditability win.
3. **`_statement` / `_of_` pattern** (§8.3) — formalises the bridge-obligations ledger.
4. **`autoImplicit=false`, module system, tagged pin, per-declaration docstrings** (§8.4) — fold the mechanical items into the next toolchain/module-system pass.

Provenance: the 2026-07-20 Lean-QIT / Physlib overlap analysis.

## 9. Library-grade quality standard (adopted 2026-08-06)

**The corpus aims for library-level code**: the bar a mathlib reviewer would apply to the
`Mathlib/`-staged tree, and the same bar — with the documented physics exceptions below —
across the physics modules (the Lean-QIT / Physlib route of §8). Adopted by author
decision 2026-08-06, motivated by Ilin & Nugent (arXiv 2606.13925): a corpus can be
kernel-green, zero-axiom, and honestly claimed — all of which §1–§8 and the guard family
already enforce — and still fail review *as a library* (definitions without interfaces,
statements proved too narrow to reuse, names that assert nothing). The kernel cannot see
that defect class; `scripts/check-review-surface.sh` measures it, and this section makes
its target normative rather than descriptive.

**The prioritised work queue is `specs/BACKLOG.md` §F.** The rules, each with its
mechanical tracker:

- **9.1 API-first definitions** *(tracker: review-surface (B)).* A definition that proofs
  reach through carries an interface: a `_def`/`_apply` simp lemma at minimum, component
  lemmas where consumers project. Raw `unfold`/`delta` of a *nonlocal* definition inside a
  finished proof is a smell — it couples the proof to the definition's spelling, and 18
  such couplings (the `alphaOff` case) is a refactoring hazard, not transparency. Local
  plumbing (an `Aux` consumed only in its own file) is exempt. **Hard rule for new
  modules; retrofit per BACKLOG F1–F2 for existing ones.**
- **9.2 Naming** *(tracker: review-surface (E)).* `Mathlib/`-staged files follow mathlib
  naming strictly — defs `lowerCamelCase`, Prop-valued predicates/structures
  `UpperCamelCase`, theorems `snake_case` — since B6 review will demand exactly that.
  Physics modules (`Empirical/`, `LF*`) may use **literature notation** where the name
  mirrors the cited source (Hardy's `A'`/`B'` settings, gate names): domain fidelity beats
  convention there, and the module docstring says which source the notation follows.
  Theorem-style names on definitions (`*_realisable_for`, `b92_encode`) are a defect of
  form: rename **when next touched** — a rename sweep is churn without content.
- **9.3 Rule of two for statements** *(trackers: (A)/(C)).* Single-use support lemmas are
  legitimate factoring — the 1,100-row list is a where-to-look index, not a to-zero
  budget. The rule bites at the *second* consumer: when a new proof nearly-fits an
  existing single-use lemma, **generalise the existing lemma** rather than clone it.
  Obligation `Prop`s (§8.3: spec consumed by its one discharging witness) are refs=1 **by
  design** and exempt; their docstring must name the discharging witness.
- **9.4 Proof style** *(tracker: (D)).* A new proof exceeding ~150 lines extracts named
  lemmas first. Existing outliers (`cuccaroModAdd_spec` at 313, the `have`-density top
  ten) are refactored **on touch**, not as a campaign — they are proven and stable, and
  churn risks regressions for aesthetics.
- **9.5 The ratchet** *(enforcement).* `check-review-surface` stays **non-blocking** — its
  counts include by-design patterns (9.2's physics names, 9.3's obligation Props), and a
  blocking gate on a proxy is the failure mode its own header warns against. Enforcement
  is by **diff discipline** instead: the baseline (`docs/review-surface-baseline-*.txt`)
  is re-captured at each release tag; a landing that *increases* the no-API count (B) or
  adds theorem-style def names (E) says so, with justification, in its commit message.
  Unjustified regressions are review findings.

**What this section does NOT change:** the correctness stack (kernel, AxiomAudit,
`check-claims` and the guard family) remains the authority on soundness and claim
honesty; §9 is an ergonomics-and-reuse bar layered on top, and the only place it is
*load-bearing* is upstreaming (B6 and the Physlib route), which is why BACKLOG F1 leads
the queue.
