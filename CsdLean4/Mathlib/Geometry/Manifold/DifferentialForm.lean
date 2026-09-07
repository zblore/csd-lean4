/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.VectorBundle.AlternatingMap
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpace
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differential forms on a manifold

**TERM-SCOPE(Kahler)** — the phrase "top-power identity" appears below in the *restricted*
sense `specs/TERMS.md` records, and in the negative: this module makes it sayable and leaves it
unproved. (Repository bookkeeping; it goes with the `References` block if sent upstream.)

**Category:** 1-Mathlib-staging (CSD-free; upstream target
`Mathlib.Geometry.Manifold`, beside the flat `Analysis/Calculus/DifferentialForm/`).

**Step (2a) of the manifold exterior-calculus plan, completed** (`MATHLIB-GAPS.md`,
`specs/BACKLOG.md` XL). A differential form on a manifold is a smooth section of the bundle
of alternating maps on the tangent bundle. Every ingredient existed at the pin except the one
that makes "smooth" mean anything — the `ContMDiffVectorBundle` instance for the
alternating-map bundle, built in
[`VectorBundle/AlternatingMap.lean`](VectorBundle/AlternatingMap.lean) on top of the pullback
analyticity in
[`Analysis/Normed/Module/Alternating/Pullback.lean`](../../Analysis/Normed/Module/Alternating/Pullback.lean).

* `DifferentialForm` — the type: a `C^n` section of `x ↦ TₓM [⋀^ι]→L[𝕜] G`;
* ★ `projectiveDifferentialForm_nonempty` — **`ℂℙⁿ` carries analytic differential forms of
  every degree**, which is the whole chain from step (0) to here in one statement: the
  charted-space and analytic-manifold instances of `ProjectiveSpace.lean` feed the tangent
  bundle, the tangent bundle feeds the alternating bundle, and the alternating bundle's
  smooth structure is what makes the section type well-formed.

## Honest scope

⚠️ **Existence of the type is not existence of a form anyone wants.** The witness *in this
module* is the zero section. The **Fubini–Study** form as a `C^∞` section of this bundle is
built downstream, in
[`Instances/ProjectiveSpaceFubiniStudyForm.lean`](Instances/ProjectiveSpaceFubiniStudyForm.lean)
(`Projectivization.fsForm`, with `fsForm_ne_zero`), from the chart-overlap agreement proved in
`Instances/ProjectiveSpaceFubiniStudy.lean`.

⚠️ **Still no exterior derivative.** `d` on manifolds is step (2b) — upstream's own stated TODO
— and none of this touches it. So `dω = 0` and the top-power identity remain exactly as
unprovable as they were this morning; what changed is that both are now *statable*, which was
the entire point of steps (0), (1) and (2a).

⚠️ **No physics.** Nothing in this repository waits on any of it. The corpus's geometry is done
on the ambient space and in charts, and `R-016` is untouched.

References: `MATHLIB-GAPS.md` (Kahler / symplectic manifold API, step (2a));
`specs/BACKLOG.md` (XL, "Manifold exterior calculus");
`CsdLean4/Mathlib/Geometry/Manifold/VectorBundle/AlternatingMap.lean` (the instance that makes
this well-formed); `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (the flat case).
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization

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

section Projective

open Projectivization

variable {ι : Type*} [Fintype ι]

/-- ★ **Complex projective space carries analytic differential forms of every degree.**

This is the whole chain in one statement. `ℂℙⁿ` is a charted space and an analytic manifold
(step (0)); that makes its tangent bundle an analytic vector bundle; the alternating-map
bundle over it is then an analytic vector bundle (step (2a)'s instance); and only then is the
type of analytic `ι`-forms on `ℂℙⁿ` well-formed at all.

⚠️ The witness here is the **zero** form; the Fubini–Study form as a section is
`Projectivization.fsForm` in `Instances/ProjectiveSpaceFubiniStudyForm.lean`. -/
theorem projectiveDifferentialForm_nonempty (m : ℕ) :
    Nonempty (DifferentialForm (IM := modelWithCornersSelf ℂ (Fin m → ℂ))
      (M := ℙ ℂ (Ambient m)) (n := ω) (ι := ι) (G := ℂ)) :=
  ⟨0⟩

end Projective
