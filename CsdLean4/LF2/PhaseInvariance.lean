/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.BornWrapper

/-!
# Phase invariance of rank-1 outer products and wrappers

**Category:** 3-Local (pre-LF4 plan Phase 1 — phase invariance of
`outerProduct`, `rankOneEffect`, and `rankOneDensity` under unit-modulus
scalar action).

For a unit-modulus scalar `c`, the rank-1 outer product `|c·φ⟩⟨c·φ|`
equals `|φ⟩⟨φ|`. The rank-1 projector through a unit vector depends
only on the projective ray of the vector, not on its specific
unit-vector representative.

Used downstream by the volume-ratio effect function `effectProjFn`
(pre-LF4 plan Phase 2) to justify well-definedness under a caller-
supplied phase-arbitrary `rep : P → EuclideanSpace ℂ (Fin N)` map.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ}

/-- **Phase invariance of `outerProduct`.** For a unit-modulus scalar
    `c` and any vector `φ`, the outer product of `c • φ` equals the
    outer product of `φ`. Algebraic content: `(c • φ) ⊗ (c • φ)* =
    c · c̄ · (φ ⊗ φ*) = ‖c‖² · (φ ⊗ φ*) = φ ⊗ φ*`. -/
lemma outerProduct_phase_invariant
    (φ : EuclideanSpace ℂ (Fin N)) (c : ℂ) (hc : ‖c‖ = 1) :
    outerProduct (c • φ) = outerProduct φ := by
  have hc_norm_sq : c * star c = 1 := by
    have h : c * (starRingEnd ℂ) c = ((‖c‖ : ℂ)) ^ 2 := RCLike.mul_conj c
    have hstar : (star c : ℂ) = (starRingEnd ℂ) c := rfl
    rw [hstar, h, hc]
    norm_num
  ext i j
  simp only [outerProduct, Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul]
  -- Goal: (c * φ i) * star (c * φ j) = φ i * star (φ j)
  rw [show star (c * φ j) = star (φ j) * star c from StarMul.star_mul c (φ j)]
  calc (c * φ i) * (star (φ j) * star c)
      = (c * star c) * (φ i * star (φ j)) := by ring
    _ = 1 * (φ i * star (φ j)) := by rw [hc_norm_sq]
    _ = φ i * star (φ j) := one_mul _

/-- **Phase invariance of `rankOneEffect`.** For a unit-modulus scalar
    `c`, `rankOneEffect (c • φ) = rankOneEffect φ` under matching
    unit-norm hypotheses. The rank-1 effect depends only on the
    projective ray of `φ`. -/
lemma rankOneEffect_phase_invariant
    (φ : EuclideanSpace ℂ (Fin N)) (c : ℂ) (hc : ‖c‖ = 1) (hφ : ‖φ‖ = 1)
    (hcφ : ‖c • φ‖ = 1) :
    rankOneEffect (c • φ) hcφ = rankOneEffect φ hφ := by
  -- `rankOneEffect ψ h` unfolds to `Effect.mk (outerProduct ψ) _ _ _`.
  -- `Effect.mk.injEq` collapses structure equality to M-equality (Prop
  -- fields are proof-irrelevant).
  show (⟨outerProduct (c • φ), _, _, _⟩ : Effect N) =
       (⟨outerProduct φ, _, _, _⟩ : Effect N)
  rw [Effect.mk.injEq]
  exact outerProduct_phase_invariant φ c hc

/-- **Phase invariance of `rankOneDensity`.** For a unit-modulus scalar
    `c`, `rankOneDensity (c • φ) = rankOneDensity φ` under matching
    unit-norm hypotheses. The rank-1 density depends only on the
    projective ray of `φ`. -/
lemma rankOneDensity_phase_invariant
    (φ : EuclideanSpace ℂ (Fin N)) (c : ℂ) (hc : ‖c‖ = 1) (hφ : ‖φ‖ = 1)
    (hcφ : ‖c • φ‖ = 1) :
    rankOneDensity (c • φ) hcφ = rankOneDensity φ hφ := by
  show (⟨outerProduct (c • φ), _, _, _⟩ : DensityOperator N) =
       (⟨outerProduct φ, _, _, _⟩ : DensityOperator N)
  rw [DensityOperator.mk.injEq]
  exact outerProduct_phase_invariant φ c hc

end LF2
end CSD
