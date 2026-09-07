/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ExteriorDerivative

/-!
# Symplectic forms on a manifold

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

With differential forms (`DifferentialForm.lean`, step (2a)) and their exterior derivative
(`ExteriorDerivative.lean`, step (2b)) in place, the sentence "a symplectic form on `M`" can be
written down:

* `DifferentialForm.IsSymplectic α` — a `C^∞` 2-form `α` on a real boundaryless manifold is
  **symplectic** when it is **closed** (`α.mextDeriv = 0`) and **non-degenerate at every point**
  (for every nonzero tangent vector `v` some `w` has `α x (v, w) ≠ 0`).

This is a predicate, not a theory. Its purpose is to let the corpus *state* that `ℂℙⁿ` with the
Fubini–Study form is a symplectic manifold, and to hold that statement to the two obligations the
word carries. The one inhabitant is `Projectivization.fsForm_isSymplectic`
(`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`).

## Honest scope

⚠️ **Nothing is derived from the predicate.** No Darboux theorem, no symplectic volume, no
generators of flows, no moment maps — none of the symplectic-geometry API is here, only the
condition. The corpus's `R-016` (the arena-level generator identity) is untouched.

⚠️ **Non-degeneracy is the finite-dimensional reading** — "`v ≠ 0 → ∃ w, α x (v, w) ≠ 0`" is
weak non-degeneracy in general; for the finite-dimensional real manifolds the corpus uses it is
the usual condition, and it forces the dimension to be even wherever the form is inhabited.

⚠️ **`∞` and `𝓘(ℝ, E)` only**, inherited from `ExteriorDerivative.lean`.

References: `Geometry/Manifold/ExteriorDerivative.lean` (`mextDeriv`);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudySymplectic.lean` (the inhabitant);
`specs/TERMS.md` ("symplectic / manifold"); `MATHLIB-GAPS.md` (Kahler / symplectic manifold API);
`specs/BACKLOG.md` (XL, "Manifold exterior calculus", step (4)); `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) ∞ M]

/-- **A symplectic form**: a `C^∞` 2-form that is closed and non-degenerate at every point. -/
structure IsSymplectic (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) :
    Prop where
  /-- Closedness: `d α = 0`. -/
  closed : α.mextDeriv = 0
  /-- Non-degeneracy at every point: every nonzero tangent vector pairs non-trivially with some
  other. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
    ∃ w, α x ![v, w] ≠ 0

end DifferentialForm
