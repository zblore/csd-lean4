/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.FrameFunction

/-!
# Gleason's theorem, finite-dimensional: the reduction to the core lemma on `S²`

**Category:** 1-Mathlib (CSD-free; staged for upstream). The assembly of
`specs/gleason-feasibility.md`: Layers A and C proved in this tree reduce Gleason's theorem for
`ℂᴺ`, `N ≥ 3`, to one statement about the real sphere `S² ⊂ ℝ³`.

* `CoreLemma` — **Gleason's core lemma, as a proposition:** every nonnegative frame function on
  `S²` is the restriction of a symmetric quadratic form. Gleason proved it with spherical
  harmonics (1957, §2); Cooke–Keane–Moran (1985) and Richman–Bridges (1999) proved it with
  elementary geometry of great circles. It is **not proved here** — `specs/gleason-feasibility.md`
  sizes the elementary proof.
* ★★ `ProjectionPackage.gleason_representation_of_core` — **Gleason's theorem from the core
  lemma:** for `N ≥ 3`, every projection package on `ℂᴺ` is `P ↦ Re Tr(ρ P)` for a unique density
  matrix `ρ`. The chain: A2 restricts the frame function to every completely real `3`-space
  (`isFrameFunction_realRestrict`); the core lemma makes each restriction a quadratic form;
  `isRealPlaneRegular_of_triples` transports that to every completely real plane; A3
  (`exists_isHermitian_of_isRealPlaneRegular`) produces the Hermitian matrix; Layer C
  (`existsUnique_density_of_frame_quadratic`) makes it the unique density matrix.

Nothing in this file claims Gleason's theorem: the theorem's only hypothesis beyond `N ≥ 3` is
`CoreLemma`, stated as a proposition so that the dependency is visible in the statement itself.

## Source

Gleason 1957, *J. Math. Mech.* **6**, 885; Cooke, Keane, Moran 1985, *Math. Proc. Cambridge
Philos. Soc.* **98**, 117; Richman, Bridges 1999, *J. Funct. Anal.* **162**, 287.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Gleason

/-- **Gleason's core lemma, as a proposition.** Every nonnegative frame function on the unit
sphere of `ℝ³` is the restriction of a symmetric quadratic form: for `f` with
`∑ᵢ f (bᵢ) = W` over every orthonormal basis and `f ≥ 0` on the sphere, there is a symmetric
`A` with `f x = x ⬝ᵥ A x` for every unit `x`. -/
def CoreLemma : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (W : ℝ), IsFrameFunction ℝ f W →
    (∀ x, ‖x‖ = 1 → 0 ≤ f x) →
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ ∀ x, ‖x‖ = 1 → f x = ⇑x ⬝ᵥ (A *ᵥ ⇑x)

variable {N : ℕ}

/-- ★★ **Gleason's theorem for `ℂᴺ`, `N ≥ 3`, from the core lemma.** For every projection
package `OP` there is a unique density matrix `ρ` with `OP.p P = Re Tr(ρ P)` for every orthogonal
projection `P`. -/
theorem ProjectionPackage.gleason_representation_of_core (hcore : CoreLemma) (hN : 3 ≤ N)
    (OP : ProjectionPackage N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re := by
  have hreg : IsRealPlaneRegular OP.frame :=
    OP.isRealPlaneRegular_of_triples hN fun e he =>
      hcore (OP.realRestrict e) _ (OP.isFrameFunction_realRestrict he)
        fun x hx => OP.realRestrict_nonneg he hx
  obtain ⟨A, hA, hf⟩ := OP.exists_isHermitian_of_isRealPlaneRegular hreg
  exact OP.existsUnique_density_of_frame_quadratic hA hf

end Gleason

end
