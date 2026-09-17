# Physlib bridge — external review briefs (2026-09-16)

Two briefs for an independent reviewer (written for the OpenAI Codex CLI/extension, read-only sandbox).
Run each from the repository root; the outputs belong under `export/` (git-ignored) or in a review record.

## Brief A — the bridge and the export package

You are reviewing Lean 4 / Mathlib library code as a Mathlib reviewer and as a Physlib (leanprover-community/physlib) maintainer would. Be adversarial and concrete. Read the files; do not take the docstrings' word for anything. You are in a read-only sandbox: do not edit files and do not run `lake build`. You may run `lake env lean <file>` on a single file to check something, and `grep`/`rg` freely. Mathlib is pinned at db584cd6d (Lean v4.33.0) under .lake/packages/mathlib.

CONTEXT. This repository built a bridge for Physlib PR #1652 (Nava-Hernandez, Fisher–Rao metric on the open simplex): the Fubini–Study metric of ℂℙⁿ pushes forward, along the torus moment map, to the Fisher–Rao metric on the simplex, with constant one. The Physlib-bound files are (in review order):

1. CsdLean4/Mathlib/Analysis/InformationGeometry/FisherRao.lean — a mirror of Physlib's file (claimed verbatim except the module-system header and field docstrings).
2. CsdLean4/Mathlib/Analysis/InformationGeometry/FubiniStudyFisherRao.lean — the vector-level bridge (bornWeight, bornDeriv, IsHorizontal, fisherRaoInner_bornDeriv, Braunstein–Caves fisherInfo_bornDeriv_le / _eq_iff, and the homogeneous layer normalize / horizontalLift / fsInnerHom / fisherRaoInner_bornDeriv_normalize).
3. CsdLean4/Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFisherRao.lean — the manifold bridge (insertZero, fsMetric_eq_fsInnerHom, momentDeriv + hasMFDerivAt_momentMap / mfderiv_momentMap, verticalSpace / horizontalSpace / mem_horizontalSpace_iff, regularStratum / toOpenSimplex, fsMetric_eq_fisherRaoInner).
4. CsdLean4/Mathlib/LinearAlgebra/Projectivization/MomentMap.lean and CsdLean4/Mathlib/Analysis/Matrix/SchrodingerUnitary.lean — two modules moved out of the CSD layers today so that the manifold closure imports nothing outside Mathlib and CsdLean4/Mathlib/.
5. The export package: CsdLean4/Interop/Physlib/FubiniStudyGeometry.lean (root), CsdLean4/Interop/Physlib/MANIFEST.md, scripts/export_physlib.py, scripts/export-physlib.sh, scripts/physlib-axiom-sweep.lean, and rule (4) of scripts/check-import-hygiene.sh.

The metric these files use is Projectivization.fsMetric in CsdLean4/Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyRiemannian.lean (fsMetric x u v = fsForm x ![fsJ x u, v]; toMatrix_fsModelMetric_zero says the Gram matrix at a chart origin is 4 • 1), with the chart formula fsModelForm_apply in ProjectiveSpaceFubiniStudyMass.lean and fsModelMetric_zero_apply in the Riemannian file. The tangent space of ℂℙⁿ at x is the model Fin n → ℂ (the chart's coordinates), and fsMetric x is definitionally fsModelMetric (chartFun (idx x) x).

QUESTIONS — answer each with file:line references.

Q1 Definitions. Are bornWeight, bornDeriv, IsHorizontal, normalize, horizontalLift, fsInnerHom, insertZero, momentDeriv, verticalSpace, horizontalSpace, regularStratum, toOpenSimplex the right objects, stated at the right generality (ι vs Fin N; ℂ vs RCLike; EuclideanSpace vs an inner product space), with Mathlib-conforming names? Which would a Mathlib reviewer ask to be renamed, generalised or removed? Is anything a "theorem-style definition" or a definition proofs reach through without an API?

Q2 Statements. For each ★ theorem, is the statement the strongest natural one, and is it non-vacuous? Specifically: (a) is horizontalSpace (the BilinForm.orthogonal of the span of torusField values) what a reader expects, and does mem_horizontalSpace_iff prove the characterisation for all n including n = 0? (b) momentDeriv is stated on the model space Fin n → ℂ rather than TangentSpace — is that sound and is the mfderiv identification (mfderiv_momentMap) genuine? (c) fsMetric_eq_fisherRaoInner: are the hypotheses (regularStratum, u ∈ horizontalSpace x) exactly the natural ones; would a stronger form (an isometry statement, injectivity/surjectivity of momentDeriv on the horizontal space, or a statement for all u, v with the vertical part projected out) be expected? (d) fisherRaoInner_bornDeriv needs only u horizontal, not v — is that stated and exploited correctly?

Q3 The constant. Is the claim "constant one" correct for this repository's normalisation? Trace it: fsModelMetric_zero_apply → 4 · Re⟪u,v⟫, fsModelMetric_eq_fsInnerHom, fsInnerHom, inner_horizontalLift, fisherRaoInner_bornDeriv. Say exactly where a factor could hide and confirm or refute that none does.

Q4 Proof quality. Fragile steps (defeq abuse, `show`, rfl across instance paths, TangentSpace-vs-model identifications, reliance on `RCLike.ofReal_eq_complex_ofReal := rfl`), long proofs that should be split, simp sets that a Mathlib reviewer would object to, unused hypotheses.

Q5 Docstring honesty. Any sentence in these files that claims more than the code proves, or less. Include the MANIFEST's claims (closure size, "every declaration on the foundational triple", "built clean against Physlib's pin", hygiene at 0).

Q6 Export machinery. Read scripts/export_physlib.py: is the closure computation right (imports regex, `public import` forms), is the topological slicing correct and deterministic, does the rename (CsdLean4.Mathlib.Analysis.InformationGeometry.* → QuantumInfo.ForMathlib.*, everything else → PhyslibAlpha.*) produce valid module paths and imports, could the hygiene scan miss CSD-specific vocabulary (list tokens it should also catch), and does physlib-axiom-sweep.lean actually cover every declaration of the closure (inClosure uses env.getModuleIdxFor?; is the CsdLean4.Mathlib prefix test right; does it miss private/instance declarations)?

Q7 Physlib reception. What would a Physlib maintainer push back on before merging the vector-level file into QuantumInfo/ForMathlib next to FisherRao.lean (namespace choice, dependency on their unmerged file, Fin-indexing, docstring style), and the geometry slices into PhyslibAlpha?

OUTPUT. A numbered list of findings, most severe first, each with: severity (BLOCKER / SHOULD-FIX / NIT), file:line, the defect in one sentence, and the concrete fix. Then a one-paragraph verdict: is this ready to share with Nava-Hernandez for review, and if not, what must change first. Do not pad; if something is fine, say so in one line.

## Records

* **Brief A** ran on Codex (`67c608a`); its nine findings and the verdict "hold the hand-off" were
  verified both ways and addressed in `a69b632` / `d202da6` (BACKLOG #33 residue (d)).
* **Brief B** was started on Codex (died on the account's usage limit mid-review) and completed by
  three scoped read-only reviewers (slices 1/3/4, 5–6, 7–9) on 2026-09-16; every concrete claim was
  re-verified against the tree before acting. One BLOCKER (the `Projectivization.instMulAction`
  name clash with Mathlib's `Projectivization/Action.lean`, reproduced in both import orders) and
  the cheap confirmed findings were fixed the same day; two findings were rejected on verification
  (the forward-compat measure shim; `[NeZero N]` in `FubiniStudyLebesgue.lean`); the rest are the
  priced residues **B1–B13** in BACKLOG #33 residue (e).
* **The S rows** (B1, B3, B4 ×3, B7, B10, B11's Hamiltonian half, B12) were done on 2026-09-17 at
  the user's request; two re-pricings came out of doing them — B3 (Mathlib's `complexToReal` is a
  `def`, so the suggested `inner ℝ` is not available as an instance) and B13 (no `volume` on a
  complex `EuclideanSpace` at the pin; the real-`2n` transfer is M) — recorded in the same row.

## Brief B — the Fubini–Study machinery the bridge stands on

You are reviewing Lean 4 / Mathlib library code as a Mathlib reviewer and as a Physlib (leanprover-community/physlib) maintainer would. Be adversarial and concrete. Read the files; do not take the docstrings' word for anything. You are in a read-only sandbox: do not edit files and do not run `lake build`. You may run `lake env lean <file>` on a single file to check something, and `grep`/`rg` freely. Mathlib is pinned at db584cd6d (Lean v4.33.0) under .lake/packages/mathlib.

CONTEXT. CsdLean4/Interop/Physlib/MANIFEST.md lists a 44-module, 13,098-line closure under CsdLean4/Mathlib/ that this repository offers to Physlib in six dependency-ordered slices: the manifold structure of ℂℙⁿ with its affine atlas (Geometry/Manifold/Instances/ProjectiveSpace*.lean), differential forms and the exterior derivative built from scratch (Geometry/Manifold/DifferentialForm.lean, WedgeForm.lean, ExteriorDerivative.lean, VectorBundle/AlternatingMap.lean, Analysis/Normed/Module/Alternating/*.lean), symplectic and Kähler structure (Geometry/Manifold/SymplecticForm.lean, HamiltonianVectorField.lean, Analysis/InnerProductSpace/Kahler*.lean, HamiltonianVectorField.lean), the Fubini–Study form, metric and volume (ProjectiveSpaceFubiniStudy{Form,Symplectic,Riemannian,Volume,Mass}.lean, TopFormMeasure.lean, RiemannianVolume.lean, Analysis/SpecialFunctions/JapaneseBracketIntegral.lean), the torus moment map (ProjectiveSpaceMomentMap.lean, LinearAlgebra/Projectivization/MomentMap.lean), unitary actions and invariant measures (LinearAlgebra/Projectivization/*.lean, LinearAlgebra/Matrix/Unitary*.lean, MeasureTheory/MapProbability.lean), and integral curves / global flows (Geometry/Manifold/IntegralCurve/GlobalFlow.lean). A separate review covers the three information-geometry / Fisher–Rao files; this one is about everything the bridge stands on. Start from MANIFEST.md's slice table and read the modules in slice order.

QUESTIONS — answer each with file:line references.

Q1 Soundness red flags (the class the kernel cannot see). Definitions that make the headline theorems easier than they look: (a) fsForm / fsSection is defined chartwise through `idx x` (the chart at x's own preferred index) — is it a well-defined global form, is smoothness across charts (localRep_fsSection, contMDiff_fsSection) genuinely proved or assumed through the definition; (b) `TangentSpace 𝓘(ℝ, Fin n → ℂ) x` is identified with the model `Fin n → ℂ` throughout (tangentToModel, flatFamily, symmL lemmas) — where is that identification load-bearing and is it legitimate; (c) `DifferentialForm.IsSymplectic`, `IsAlmostKahler`, `IsKahler`, `IsHamiltonianVectorField`, `mextDeriv` — do these definitions mean what their names say, and are they consistent with Mathlib's conventions where Mathlib has the notion (e.g. mfderiv, ContMDiff, ContinuousAlternatingMap); (d) TopFormMeasure / RiemannianVolume — is the measure built from a top form a genuine chart-independent object (the chart-cover independence claim riemannianVolume_fsMetric_congr_cover), and does `|·|` hide an orientation issue; (e) any `def` whose body is a case split on a chart index, a `Classical.choice`, or an `if`, that a theorem then reasons about as if canonical.

Q2 Statements weaker than their docstrings. For each ★★/★★★-marked theorem in these modules, compare the docstring claim with the Lean statement and its hypotheses; list every gap.

Q3 Mathlib duplication and drift at pin db584cd6d. What in this closure already exists in Mathlib (ContinuousAlternatingMap wedge/pullback, alternating-map vector bundles, integral curves, Riemannian volume, unitary group compactness/Haar, projectivization topology)? For each duplicate: the Mathlib name, and whether the local version is a strict generalisation, a specialisation, or a plain duplicate. Also flag anything Mathlib has added between this pin and current master that would make a slice unnecessary (say what you know and what you cannot verify offline).

Q4 API and naming as Mathlib review would see it: defs that are lowerCamelCase/Props UpperCamelCase/theorems snake_case violations; definitions without `_apply`/`_def` simp lemmas that proofs then `unfold`; single-use lemmas that should be inlined or generalised; `Fin n`-specialised statements that should be over a finite type; ℂ-specialised statements that should be over RCLike; heavy `simp` sets; proofs over ~150 lines.

Q5 Upstreaming blockers per slice (1–6 in MANIFEST.md): for each slice, the top two things a maintainer would require before merging into PhyslibAlpha, and whether the slice is self-contained (imports only Mathlib and earlier slices — verify against the import lines, not the manifest).

Q6 The "Category 1 by closure" claim: rule (4) in scripts/check-import-hygiene.sh greps direct imports of every file under CsdLean4/Mathlib/ for CsdLean4.(LF1..6|SigmaLayer|RecordLayer|Empirical|CV|Thermo|Incubator|Tests|Basic|Headlines|Interop). Is that grep complete (import syntax variants, `import` inside comments, module-system `public import` / `private import` / `meta import`), and can a CSD-layer dependency still enter (e.g. through `CsdLean4.Mathlib` files that themselves were moved with CSD content in their docstrings or through instances)?

OUTPUT. A numbered list of findings, most severe first, each with: severity (BLOCKER / SHOULD-FIX / NIT), file:line, the defect in one sentence, and the concrete fix. Group per slice at the end with a one-line readiness verdict per slice. Do not pad; if something is fine, say so in one line.
