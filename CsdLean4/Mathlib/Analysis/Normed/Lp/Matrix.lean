/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Mathlib upstream candidate: `Matrix.ofLp_toEuclideanLin`

**Category:** 1-Mathlib (CSD-free helper lemma staged as a Mathlib upstream
candidate).

Non-deprecated `rfl`-alias for the matrix-vector adapter
`((Matrix.toEuclideanLin M) v).ofLp = M *ᵥ v.ofLp`.

`Matrix.ofLp_toEuclideanLin_apply` was deprecated in favour of
`Matrix.ofLp_toLpLin` in a recent Mathlib refresh. The replacement
exposes the `p q : ENNReal` Lp parameters and routes through
`Matrix.toLin'`, which forces typeclass friction at every callsite.
This local alias keeps the cleaner spelling available while the
upstream API stabilises; it is a one-line `rfl`, so it is genuinely
trivial — its value is the name, not the proof.

Declarations live in `namespace Matrix` (Mathlib's natural symbol
namespace), so dot notation is preserved and upstreaming requires no
symbol rename — only a file move to (or append onto)
`Mathlib/Analysis/Normed/Lp/Matrix.lean`.

## Provenance

Originally declared in `CsdLean4/LF3/Setup.lean` inside `namespace CSD.LF3`,
which inadvertently shadowed the intended `Matrix.*` symbol path. Moved
here on 2026-05-19 to fix the namespace and stage for upstreaming.

## Consumers

- `CsdLean4/LF3/Projectors/LF2Interface.lean` (Born identity step).
- `CsdLean4/LF3/Singlet/Expectations.lean` (Pauli expectation calc).

## Tags

matrix, euclidean space, Lp, adapter
-/

namespace Matrix

/-- **`rfl`-alias for the matrix-vector adapter on `EuclideanSpace`.**
For a matrix `M : Matrix m n ℂ` and a vector `v : EuclideanSpace ℂ n`,
the underlying `(n → ℂ)`-representation of `(M.toEuclideanLin v)` is
the matrix-vector product `M *ᵥ v.ofLp`. Trivial (`rfl`), but a named
lemma anchors the rewrite step in proof scripts and avoids the
deprecation warning attached to the older `*_apply` form. -/
theorem ofLp_toEuclideanLin {m n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ((Matrix.toEuclideanLin M) v).ofLp = M *ᵥ v.ofLp := rfl

end Matrix
