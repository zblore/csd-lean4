# Busch–Gleason submission review: current finite-dimensional results

Date: 2026-09-28. Reviewer: Codex, current review session.
Source: **5f77294d6c327d37fe824e6829097600050b1de7**, fetched from origin/main today.
Lean **v4.33.0**, Mathlib **db584cd6d46c92f209a44c0f1c829460d327499d**.

## Integration update — 2026-09-29

The corrections are now **applied to source** in this change, based on main `ff5c7998`.
The old `documentation.patch` is retained as historical review evidence, not pending work.
The integration also replaces the production dependency traversal, checks eight reconstruction
roots, includes the SingletBell witness module, and tests direct and cross-namespace aliases.

| Findings | Disposition in this change |
|---|---|
| CR-GLEASON-006/007/008 | Applied: roadmap, citation, measure terminology and domain qualifications |
| CR-LF2-007 / CR-GLEASON-003 concrete comment errors | Applied: imported-axiom claim, covariance digression, moved theorem pointers, deferred homogeneity and outer-product terminology |
| CR-GLEASON-005 | Integrated: broader production guard, alias controls, SingletBell scope; validation below |
| CR-GLEASON-001/004 optional public API work | Plain-matrix adapters remain checked submission evidence; production compatibility wrappers are retained |

See [integration results](2026-09-29-gleason-integration.md) for the build, current-source
checks, precise scope and commands for an independent check. The original pinned review below
remains the record of what was found before correction. Its 8,001-line count describes that
source revision; corrected comments change line counts without changing the theorems.

## Verdict and suitable submission claim

**Full manual review of the pinned theorem package is complete: 16/16 local modules,
8,001/8,001 lines. No theorem-level mathematical defect or missing terminal hypothesis found.**
The complex projection theorem, complex effect theorem, real projection theorem and real
frame-function theorem pass the statement/interface review, fresh source compilation and
transitive axiom checks. Every supporting local module has now received a full code/comment
read, including the CKM proof body and the current refactored Busch implementation.

**Original review verdict: suitable for specialist submission after presentation corrections
and final-source validation; see the integration update above for their disposition.** The review of the pinned proofs is finished;
source reconciliation/export preparation is a separate remaining step. The patch prepared during review
corrects misleading mathematical descriptions and the obsolete imported-axiom header without
changing a definition or theorem. The production guard correction is now included in the integration update above.

Suggested description: "AI-reviewed finite-dimensional complex and real Gleason representation
results, the real nonnegative frame-function theorem, and finite-dimensional complex Busch
representation. All 16 local proof modules received a full code/comment review, were compiled
freshly, and passed terminal axiom, statement, boundary and dependency probes. The attached
report pins the source and records the findings and review limits."

This does not establish infinite-dimensional versions, validate the wider CSD interpretation,
or predict acceptance. Reviewer attribution identifies this Codex session; the repository
artifacts do not independently attest the selected backend model or constitute a second review
by another agent. Do not describe this as an independently attested second Astra review.

## Exact claims checked

| Result | Input | Conclusion and boundary |
|---|---|---|
| Complex projection Gleason | Nonnegative, normalized, orthogonally additive assignment on all complex orthogonal projections | Unique PSD trace-one complex matrix; N >= 3 |
| Complex Busch | Nonnegative, normalized assignment additive whenever a sum of effects remains an effect; all effects, including noncommuting pairs | Unique PSD trace-one complex matrix; dimensions 1 and 2 included; no continuity input; probability upper bound derivable |
| Real projection Gleason | The analogous assignment on real orthogonal projections | Unique real PSD trace-one matrix; N >= 3 |
| Real frame function | Nonnegativity on the unit sphere and weight W over every orthonormal basis | Unique real PSD matrix of trace W representing the function on the sphere; N >= 3; W = 0 handled, W > 0 normalized, negative W incompatible with the input |

Functions defined on ambient vector/matrix spaces are constrained only on the intended sphere,
projection or effect domain. Off-domain values do not strengthen the representation premise or
conclusion. The frame theorem derives evenness and boundedness; neither is assumed separately.
The two real routes consume the proved real three-dimensional core, not an assumed CoreLemma.
The frame route derives the triple's basis-independent weight by a fixed orthogonal complement,
so it does not smuggle in a projection assignment.

The scope matches the corresponding finite-dimensional cases of
[Gleason 1957, introduction and sections 1–3](https://pages.jh.edu/rrynasi1/Bananaworld/eprints/Gleason1957MeasuresOnTheClosedSubspacesOfAHilbertSpace.pdf)
and [Busch 2003, theorem and proof](https://arxiv.org/html/quant-ph/9909073v3).
Their general Hilbert-space formulations are broader. Busch's proof in the paper extends an
effect assignment to a normal positive functional; this code uses finite spectral decomposition
and polarization. RealFrame formalizes nonnegative frame functions, not all unbounded signed
frame functions. A trace-W PSD matrix is a normalized density matrix only when W = 1.

## Manual review scope

All **16 modules / 8,001 lines** received full code and comment reads. Detailed reasoning,
boundary checks and per-file conclusions are in
[manual-review.md](2026-09-28-gleason-submission/manual-review.md); exact source hashes and
coverage are in [snapshot.json](2026-09-28-gleason-submission/snapshot.json).

| Group | Files | Lines |
|---|---|---:|
| CKM core | Sphere, Piron, Warmup, SimpleFrame, Extremal, General | 3,236 |
| Complex projection setup/reduction | ProjectionPackage, FrameFunction, Reduction, Core | 1,144 |
| Shared reconstruction | Polarization, Descent | 740 |
| Real projection and frame results | Real, RealFrame | 1,354 |
| Busch effects and representation | BornWrapper, EffectGleason | 1,527 |
| **Total** | **16** | **8,001** |

The proof-body review checked the compactness argument without assuming continuity, the
countable-exception squeeze, the geometric descent and its degeneracies, complex polarization
signs, dependent vector cases, real weight-zero cases, effect homogeneity, spectral reduction,
and existence/PSD/trace/uniqueness. BornWrapper and EffectGleason were fully reread at this
revision, closing the earlier review's refactoring/reconciliation gap.

The manual review assesses the code's argument. It does not certify line-by-line identity with
the CKM paper or every historical priority/section reference; the scanned paper was not fully
text-accessible in this session. General explicitly documents a different endgame.

## Checked evidence

- All **16 local modules / 8,001 lines** freshly compiled in an isolated directory, in import
  order, with `autoImplicit=false`, `relaxedAutoImplicit=false`, `warningAsError=true` and two
  Lean threads. Compiler invocations total **262.84 seconds**. No existing local CSD oleans
  supplied those imports; only the matching external dependency cache was reused.
- Toolchain, Lake configuration and lockfile match the pinned source. Installed Mathlib matches
  its pin and has no tracked modifications. All 16 extracted source hashes rechecked afterward.
- [EndpointAudit.lean](2026-09-28-gleason-submission/EndpointAudit.lean): previous closed signatures,
  plain-matrix complex adapters, dimension-1/2 Busch witnesses, nonconstant dimension-3 projection
  witness, dimension-zero contradictions, five guarded terminal axiom outputs. Exit 0.
- [RealAudit.lean](2026-09-28-gleason-submission/RealAudit.lean): closed real signatures, plain-matrix
  and plain-frame adapters, directly constructed nonconstant real input, dimension-3 application,
  arbitrary nonnegative weights with explicit zero and weight-two instances, impossible negative
  weight and normalized dimension-zero input. Eight guarded axiom checks. Exit 0.
- [DependencyAudit.lean](2026-09-28-gleason-submission/DependencyAudit.lean): proof-term traversal
  establishes that complex projection Gleason avoids Busch reconstruction, Busch avoids the
  projection/core routes, real projection avoids both complex terminal results, and the real
  frame theorem avoids all three other terminal results. Positive controls verify both real
  routes actually reach `coreLemma`. Five alias mutations reproduce the current-main guard
  gaps and are detected by the expanded traversal. Exit 0.
- [BoundaryAudit.lean](2026-09-28-gleason-submission/BoundaryAudit.lean): proves the pole's
  coldest vector is zero, its descent is the whole hemisphere, and an equatorial descent is
  the whole equator. This reproduces the docstring boundary issue without changing production
  definitions. Exit 0 with warnings fatal.
- All audited terminal proofs and adapters use only **propext, Classical.choice, Quot.sound**.

This is focused submission validation, not a fresh whole-corpus build or all-CI run. The full
Mathlib/Batteries style-linter suite was not run on this snapshot; warning-fatal Lean compilation
is the check actually performed. No dimension-two countermodel was formalized in this session.

## Findings on the original pinned snapshot

1. **SHOULD-FIX for corpus independence claims; not a representation-theorem defect —
   CR-GLEASON-005.** Current main's `scripts/gleason-free.lean` still forbids only the Busch
   headline and restricts traversal to `CSD.*`. The executed tests show it misses density
   aliases and aliases of all three projection/frame endpoints. An expanded traversal catches
   all five. This does not show that any current production theorem uses a forbidden route.
   Reconcile the prior review-branch guard repair, agree the forbidden roots for the actual
   independence claim, include projection/core/real routes and the relevant test witnesses, then
   rerun the production scan. The artifact is a tested candidate traversal, not an integrated
   corpus guard. This follow-up can remain separate from a submission of the standalone theorems.
2. **NIT — CR-GLEASON-006, `Gleason/Real.lean:34–37`.** The module roadmap still names `ext`,
   `ext_combR`, `exists_ext_plane` and `ext_parallelogramR`, which were renamed to the generic
   `extOf` family. The body uses the correct functions. Update the roadmap names.
3. **SHOULD-FIX before a polished submission — CR-GLEASON-007, `Gleason/Core.lean:26,34`.**
   The scope paragraph calls the input "projection-valued measures", but it is a real-valued
   probability assignment on projections. The source paragraph cites Gleason's Theorem 2.3
   for the nonnegative core; 2.3 assumes continuity, whereas 2.8 is the nonnegative result.
   Correct the terminology and citation. The actual Lean assumptions are already correct.

4. **SHOULD-FIX before a polished submission — CR-GLEASON-008, domain qualifications.**
   `Gleason/Sphere.lean:38–40` says regular frame functions are all frame functions; the core
   result requires nonnegativity (arbitrary unbounded signed frame functions are not covered).
   `Gleason/Piron.lean:24–27,71–76` calls the total helper a unit vector/great half circle
   without excluding the pole; BoundaryAudit proves the pole and equator degeneracies.
   `Gleason/FrameFunction.lean:448–449` says every pair lies in an orthonormal two-plane without
   a dimension premise, though the proof correctly treats dependent pairs by homogeneity.
   `Gleason/General.lean:410` describes reflection without specifying a unit normal.
   These are descriptions exceeding their domains; the consuming theorems supply the right
   hypotheses or handle the degenerate cases. Correct the comments, preserving the code.
5. **SHOULD-FIX before submission — prior CR-LF2-007 / CR-GLEASON-003 recur on this main
   snapshot.** `LF2/BornWrapper.lean:22–30` still says it imports the Busch axiom, contradicting
   the actual proved theorem and the same file's later explanation. Its long covariance/history
   discussion and moved-theorem pointers are stale. `LF2/EffectGleason.lean:187,512–517,888`
   retain a deferred-proof description and call arbitrary outer products projectors. Reconcile
   the earlier branch cleanup; the patch here repairs the concrete misleading descriptions.
   The remaining historical progress narration is editorial cleanup, not a theorem defect.
6. **NIT / public API preparation — prior CR-GLEASON-001 / 004.** The current main package
   retains the redundant `OperationalPackage.le_one` field and the legacy `_hN : 2 ≤ N`
   wrapper premises (`BornWrapper.lean:158–159`, `EffectGleason.lean:1022,1034`). The main Busch
   theorem has no such dimension restriction. The checked matrix adapter derives boundedness
   and exposes the standard theorem without local wrapper types. Use those interfaces for a
   compact submission; avoid a needless compatibility-breaking production refactor merely
   to remove the old wrapper arguments.

[documentation.patch](2026-09-28-gleason-submission/documentation.patch) preserves the original
proposed comment-only corrections in eight files. Those corrections are now applied, with a
sentence-join cleanup in Sphere. No existing theorem or hypothesis is weakened.

## Remaining submission work

The pinned theorem package has received its full manual read. The corrected production source
and guard are delivered by this integration change. A separate submission export, if needed,
should retain the checked definitions and carry the report and manifest; compile any separately
repackaged export before sending it. The optional public matrix API can be taken from the
checked audit interfaces without breaking existing compatibility wrappers.

Unrelated review-branch source edits and the **39/691 (5.64%)** branch coverage register are
preserved. This main-snapshot review does not silently add credit to that separate register.

## Reproduction of the original pinned review

From the review checkout with matching dependency configuration and installed cache:

```powershell
$env:LEAN_NUM_THREADS = '2'
lake env python -u -B specs/reviews/2026-09-28-gleason-submission/run.py
python -u -B specs/reviews/2026-09-28-gleason-submission/probe.py
```

The first script extracts the pinned source and recompiles its closure. The second copies and
runs all four saved audit inputs against those compiled modules. See the archived per-audit
logs, [probe-results.json](2026-09-28-gleason-submission/probe-results.json) and snapshot manifest.

For the **corrected current checkout**, use the build and `validate-current.py` commands in
[integration results](2026-09-29-gleason-integration.md). The scripts above intentionally
reproduce the old pinned snapshot, not the applied corrections.
