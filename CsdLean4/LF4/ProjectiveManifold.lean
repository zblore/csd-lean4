/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.Instance
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpace
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.AddCircle
public import CsdLean4.LF4.KahlerInstance

/-!
# The projective sector `CPN` is an analytic manifold

**Category:** 3-Local (a one-line transport of the Category-1 instance built in
[`Mathlib/Geometry/Manifold/Instances/ProjectiveSpace.lean`](../Mathlib/Geometry/Manifold/Instances/ProjectiveSpace.lean)
onto the corpus's own name for the space).

`CPN (N+1)` is `ℙ ℂ (EuclideanSpace ℂ (Fin (N+1)))`, which is exactly the space the staged
instance is about, so the transport is `inferInstance`. It is worth having a name for
anyway: until 2026-09-07 the sector the whole reconstruction is stated over was not a
manifold in Lean, and every geometric word applied to it — chart, form, flow, moment map —
was prose about a space with no smooth structure.

* ★ `CSD.LF4.cpn_isManifold` — `ℂℙ^N` is an analytic (`ω`) manifold. It typechecks only if
  the charted-space instance is also found, so it witnesses both.

## Honest scope

⚠️ *Scope updated 2026-09-11 (Q33):* the section below the sector instance closes A3 of
`reconstruction-status.md` §2a — the arena is a manifold and `π` is smooth — so the paragraph that
follows describes the state before Q33.

⚠️ **This changes no CSD claim, and closes no residue.** The corpus's geometry is done on
the ambient space and on charts (`SigmaLayer/ChartIntegralCurve.lean`,
`Mathlib/Analysis/InnerProductSpace/KahlerClosed.lean`); nothing in it was waiting for
`ℂℙ^N` to carry a `ChartedSpace` instance, and `R-016` — the arena-level transport of
Hamiltonian generation — is untouched. What a manifold structure makes possible is
*stating* manifold-level facts; steps (2)–(4) of the plan (forms on manifolds, top-forms to
measures, the symplectic layer) are what would let one prove them.

References: `MATHLIB-GAPS.md` (Kahler / symplectic manifold API, step (0));
`specs/BACKLOG.md` (XL, "Manifold exterior calculus"); `CsdLean4/LF4/Instance.lean` (`CPN`).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

namespace CSD
namespace LF4

/-- ★ **The projective sector is an analytic manifold.** `CPN (N+1) = ℂℙ^N` carries the
standard affine atlas, and its transition maps are analytic.

The statement mentions `IsManifold`, which takes a `ChartedSpace` instance as an argument,
so this also witnesses that `ℂℙ^N` is a charted space. -/
theorem cpn_isManifold (N : ℕ) :
    IsManifold (modelWithCornersSelf ℂ (Fin N → ℂ)) ω (CPN (N + 1)) :=
  inferInstance

/-! ### The arena `KSigma = ℂℙⁿ × T²` is a manifold, and the sector projection is smooth (Q33) -/

instance instFactOneNeZero : Fact ((1 : ℝ) ≠ 0) := ⟨one_ne_zero⟩

/-- ★ **The torus fibre `KTorus = AddCircle 1 × AddCircle 1` is an analytic manifold**
(`AddCircle.instIsManifoldProd`, transported from `Circle`). Until 2026-09-11 the fibre was a
product *type* with a product *measure* and no smooth structure. -/
theorem ktorus_isManifold : IsManifold ((𝓡 1).prod (𝓡 1)) ω KTorus :=
  inferInstance

/-- ★★ **The arena `KSigma (N+1) = ℂℙ^N × T²` is an analytic manifold**, over the real model of
`ℂℙ^N` (the one the Fubini–Study form lives on, `instIsManifoldReal`) and the torus's model. -/
theorem ksigma_isManifold (N : ℕ) :
    IsManifold ((modelWithCornersSelf ℝ (Fin N → ℂ)).prod ((𝓡 1).prod (𝓡 1))) ω
      (KSigma (N + 1)) :=
  inferInstance

/-- ★★ **The sector projection `π = Prod.fst : KSigma → CPN` is analytic** — Paper C's A3
("smooth many-to-one projection"), which `reconstruction-status.md` §2a had classified as blocked
on an absent API. It is Mathlib's `contMDiff_fst` once both factors are manifolds. The
`manyToOneSetup`'s `pi` field IS this map (`manyToOneSetup_pi_contMDiff`, `LF4/SectorManifold.lean`). -/
theorem contMDiff_ksigma_fst (N : ℕ) :
    ContMDiff ((modelWithCornersSelf ℝ (Fin N → ℂ)).prod ((𝓡 1).prod (𝓡 1)))
      (modelWithCornersSelf ℝ (Fin N → ℂ)) ω (Prod.fst : KSigma (N + 1) → CPN (N + 1)) :=
  contMDiff_fst

end LF4
end CSD
