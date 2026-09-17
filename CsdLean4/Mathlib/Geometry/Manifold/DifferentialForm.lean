/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.VectorBundle.AlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differential forms on a manifold

**TERM-SCOPE(Kahler)** — the phrase "top-power identity" appears below in the *restricted*
sense the source repository's terms register records, and in the negative: this module makes it sayable and leaves it
unproved. (Repository bookkeeping; it goes with the `References` block if sent upstream.)

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Geometry.Manifold`, beside the flat `Analysis/Calculus/DifferentialForm/`).

A differential form on a manifold is a smooth section of the bundle
of alternating maps on the tangent bundle. Every ingredient existed at the pin except the one
that makes "smooth" mean anything — the `ContMDiffVectorBundle` instance for the
alternating-map bundle, built in
[`VectorBundle/AlternatingMap.lean`](VectorBundle/AlternatingMap.lean) on top of the pullback
analyticity in
[`Analysis/Normed/Module/Alternating/Pullback.lean`](../../Analysis/Normed/Module/Alternating/Pullback.lean).

* `DifferentialForm` — the type: a `C^n` section of `x ↦ TₓM [⋀^ι]→L[𝕜] G`.

On `ℂℙⁿ` the type is well-formed because the charted-space and analytic-manifold instances of
`Instances/ProjectiveSpace.lean` feed the tangent bundle, the tangent bundle feeds the alternating
bundle, and the alternating bundle's smooth structure is what makes the section type well-formed;
that chain is exercised where a form is actually built, not here. (Until 2026-09-16 this module
imported the projective instances to state `projectiveDifferentialForm_nonempty`, whose witness
was the zero form; the theorem and the import are gone, and the genuine non-vacuity certificate is
`Projectivization.fsForm_ne_zero` downstream.)

## Honest scope

⚠️ **Existence of the type is not existence of a form anyone wants.** This module builds no
form. The **Fubini–Study** form as a `C^∞` section of this bundle is built downstream, in
[`Instances/ProjectiveSpaceFubiniStudyForm.lean`](Instances/ProjectiveSpaceFubiniStudyForm.lean)
(`Projectivization.fsForm`, with `fsForm_ne_zero`), from the chart-overlap agreement proved in
`Instances/ProjectiveSpaceFubiniStudy.lean`.

⚠️ **No exterior derivative in this module.** `d` on manifolds is step (2b) — upstream's own
stated TODO — and is built downstream in
[`ExteriorDerivative.lean`](ExteriorDerivative.lean) (`mextDerivFamily` on families,
`DifferentialForm.mextDeriv` on forms, `d ∘ d = 0`, for the real
boundaryless model at `∞`). The top-power identity is statable after steps (0), (1) and (2a) and
is not proved anywhere.

⚠️ **No physics.** Nothing downstream waits on any of it: the geometry the projective-space
modules need is done on the ambient space and in charts.

**Provenance and references.** The Mathlib-gaps register (Kahler / symplectic manifold API, step (2a));
the backlog (XL, "Manifold exterior calculus");
`CsdLean4/Mathlib/Geometry/Manifold/VectorBundle/AlternatingMap.lean` (the instance that makes
this well-formed); `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (the flat case).
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle Topology ContDiff

section

variable {𝕜 EM HM : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]

/-- **A `C^n` differential form** of degree `ι` on `M`, valued in `G`: a `C^n` section of the
bundle whose fibre at `x` is the continuous alternating maps `(TₓM)^ι → G`.

Explicit arguments in the order `DifferentialForm IM M n ι G`. -/
abbrev DifferentialForm (IM : ModelWithCorners 𝕜 EM HM) (M : Type*) [TopologicalSpace M]
    [ChartedSpace HM M] [IsManifold IM 1 M] (n : WithTop ℕ∞) (ι : Type*) [Fintype ι]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :=
  ContMDiffSection IM (EM [⋀^ι]→L[𝕜] G) n
    (fun x : M => TangentSpace IM x [⋀^ι]→L[𝕜] Bundle.Trivial M G x)

end

/-! ### The payoff: `ℂℙⁿ` carries analytic differential forms -/
