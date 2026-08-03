/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The entrywise bound for the L2 operator norm

**Category:** 1-Mathlib (CSD-free, staged for upstream).

`Matrix.norm_entry_le_l2_opNorm`: every entry of a matrix is bounded in norm by the L2
operator norm, `‖M a b‖ ≤ ‖M‖`. The entry is a coordinate of the image of a unit basis
vector, `M a b = (M *ᵥ e_b) a`, a Euclidean coordinate is at most the Euclidean norm, and
`l2_opNorm_mulVec` bounds the image norm.

This is the bridge from operator-norm estimates (e.g. the Duhamel bound
`Matrix.norm_exp_smul_neg_I_sub_le`) to **entrywise** continuity statements, which live in the
`Matrix` Pi topology and therefore compose with topology-agnostic downstream API without
touching the scoped `Matrix.Norms.L2Operator` instances.

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` (beside `entry_norm_bound_of_unitary`, which is
the special case of a unitary matrix combined with `l2_opNorm_of_unitary`).

## Tags

matrix, operator norm, entrywise bound
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A Euclidean coordinate is at most the Euclidean norm. -/
theorem _root_.EuclideanSpace.norm_coord_le_norm (v : EuclideanSpace 𝕜 m) (a : m) :
    ‖v a‖ ≤ ‖v‖ := by
  calc ‖v a‖ = Real.sqrt (‖v a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum
          (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ a))
    _ = ‖v‖ := (EuclideanSpace.norm_eq v).symm

/-- **Every matrix entry is bounded by the L2 operator norm**: `‖M a b‖ ≤ ‖M‖`. -/
theorem norm_entry_le_l2_opNorm (M : Matrix m n 𝕜) (a : m) (b : n) :
    ‖M a b‖ ≤ ‖M‖ := by
  set x : EuclideanSpace 𝕜 n := EuclideanSpace.single b (1 : 𝕜) with hx
  set v : EuclideanSpace 𝕜 m := (EuclideanSpace.equiv m 𝕜).symm (M *ᵥ x) with hv
  have hva : v a = M a b := by
    show (M *ᵥ x) a = M a b
    show ∑ k, M a k * x k = M a b
    have hxk : ∀ k, x k = if k = b then (1 : 𝕜) else 0 := fun k => by
      rw [hx]; exact PiLp.single_apply 2 𝕜 b 1 k
    simp [hxk, mul_ite, mul_one, mul_zero]
  calc ‖M a b‖ = ‖v a‖ := by rw [hva]
    _ ≤ ‖v‖ := EuclideanSpace.norm_coord_le_norm v a
    _ ≤ ‖M‖ * ‖x‖ := M.l2_opNorm_mulVec x
    _ = ‖M‖ := by rw [hx, PiLp.norm_single, norm_one, mul_one]

end Matrix
