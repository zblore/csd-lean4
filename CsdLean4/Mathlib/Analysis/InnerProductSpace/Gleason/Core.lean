/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Reduction

/-!
# Gleason's theorem, finite-dimensional: the core lemma (OPEN) and the theorem it would give

**Category:** 1-Mathlib (CSD-free). **Branch `gleason-feasibility` only — this file carries a
`sorry` and is not part of `main`.** `specs/gleason-feasibility.md`, Layer B.

* `frameFunction_regular_sphere` — **Gleason's core lemma, `sorry`:** every nonnegative frame
  function on the unit sphere of `ℝ³` is the restriction of a symmetric quadratic form. The
  elementary proof is Cooke–Keane–Moran 1985 (Piron's descending paths → continuity → quadratic
  form); its sizing is in the feasibility note.
* `gleason_representation` — **Gleason's theorem for `ℂᴺ`, `N ≥ 3`**, which depends on exactly
  that `sorry` (`#print axioms` lists `sorryAx`): `gleason_representation_of_core` applied to the
  core lemma.

Status wording, until the `sorry` is gone: "finite-dimensional Gleason, reductions and descent
proved, core lemma open". No claim of the theorem is made anywhere.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Gleason

/-- **Gleason's core lemma (OPEN).** Every nonnegative frame function on `S² ⊂ ℝ³` is the
restriction of a symmetric quadratic form.

Cooke–Keane–Moran 1985, Theorem (elementary proof); Gleason 1957, Theorem 2.3 (via spherical
harmonics). Not proved here. -/
theorem frameFunction_regular_sphere (f : EuclideanSpace ℝ (Fin 3) → ℝ) {W : ℝ}
    (hf : IsFrameFunction ℝ f W) (h0 : ∀ x, ‖x‖ = 1 → 0 ≤ f x) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ ∀ x, ‖x‖ = 1 → f x = ⇑x ⬝ᵥ (A *ᵥ ⇑x) := by
  sorry

/-- The core lemma, in the form `Reduction.lean` consumes. -/
theorem coreLemma : CoreLemma := fun f _ hf h0 => frameFunction_regular_sphere f hf h0

variable {N : ℕ}

/-- **Gleason's theorem for `ℂᴺ`, `N ≥ 3`** — conditional on `frameFunction_regular_sphere`
(`sorry`). For every projection package there is a unique density matrix `ρ` with
`p P = Re Tr(ρ P)` for every orthogonal projection `P`. -/
theorem ProjectionPackage.gleason_representation (OP : ProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  OP.gleason_representation_of_core coreLemma hN

end Gleason

end
