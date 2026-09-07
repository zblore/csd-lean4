/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.Instance
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpace

/-!
# The projective sector `CPN` is an analytic manifold

**Category:** 2-Interface (a one-line transport of the Category-1 instance built in
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

end LF4
end CSD
