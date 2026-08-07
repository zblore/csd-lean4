/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The diagonal bound for the L2 operator norm

**Category:** 1-Mathlib (CSD-free, staged for upstream).

`Matrix.l2_opNorm_diagonal_le`: a diagonal matrix with uniformly bounded
entries has L2 operator norm at most that bound, `(∀ i, ‖w i‖ ≤ C) →
‖diagonal w‖ ≤ C`. The action of `diagonal w` is coordinatewise
multiplication, so the image's Euclidean norm is bounded factor-by-factor.
Only the `≤` direction is staged — it is what operator-norm pricing
consumes (`CV/InteractionPrice.lean`, the CV-9 Duhamel route); the equality
(`= ⨆ i, ‖w i‖`) is a separate upstream item.

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` beside `l2_opNorm_mulVec`.

## Tags

matrix, operator norm, diagonal
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **A diagonal matrix with uniformly bounded entries has L2 operator norm
at most that bound**: `(∀ i, ‖w i‖ ≤ C) → ‖diagonal w‖ ≤ C`. -/
theorem l2_opNorm_diagonal_le (w : n → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i, ‖w i‖ ≤ C) : ‖Matrix.diagonal w‖ ≤ C := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have hval : ((toEuclideanLin (𝕜 := 𝕜)).trans LinearMap.toContinuousLinearMap
        (Matrix.diagonal w)) x
      = (EuclideanSpace.equiv n 𝕜).symm (Matrix.diagonal w *ᵥ x) := rfl
  rw [hval]
  calc ‖(EuclideanSpace.equiv n 𝕜).symm (Matrix.diagonal w *ᵥ x)‖
      = Real.sqrt (∑ a, ‖w a * x a‖ ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        show ‖(Matrix.diagonal w *ᵥ x) a‖ = ‖w a * x a‖
        rw [Matrix.mulVec_diagonal]
    _ ≤ Real.sqrt (∑ a, (C * ‖x a‖) ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => ?_)
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hw a) (norm_nonneg _)
    _ = C * ‖x‖ := by
        rw [EuclideanSpace.norm_eq,
          show (∑ a, (C * ‖x a‖) ^ 2) = C ^ 2 * ∑ a, ‖x a‖ ^ 2 from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring,
          Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

end Matrix
