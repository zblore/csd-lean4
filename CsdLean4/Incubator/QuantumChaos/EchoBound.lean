/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.Diagnostics
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The echo-perturbation bound: Loschmidt decay is priced by drive distance

**Category:** Special (incubator — CSD-free; `upstream-candidate(physlib)`).

The quantitative link between the Loschmidt echo and the operator distance
of the two drives:

  `1 − L(n) ≤ 2·n·‖U − W‖`.

* `norm_toEuclideanLin_apply_le` — the action bound `‖M·ψ‖ ≤ ‖M‖·‖ψ‖`
  (L2 operator norm; definitionally `l2_opNorm_mulVec`).
* `norm_iterate_sub_iterate_le` — the telescoping perturbation bound for
  the matrix adapter: `‖Uⁿψ − Wⁿψ‖ ≤ n·‖U − W‖·‖ψ‖` (each step splits
  into an isometry factor and one fresh `U − W` action).
* ★ `one_sub_loschmidtEcho_le` — the echo bound: on unit states,
  `1 − L(n) ≤ 2·(n·‖U − W‖)`, via `1 − |z|² ≤ 2|1 − z|` and
  `1 − z = ⟨Wⁿψ, (Wⁿ − Uⁿ)ψ⟩`.

**Echo decay is at most linear in period count and drive distance** — the
diagnostics-side rhyme of the record half-life bound `μ ≤ n·ε` and of the
CV pricing ladder: instantiated on the interacting field
(`CV/ChaosBounds.lean`), the drive distance is the CV-9 Duhamel price, so
echo decay is bounded by `2n·|τ|·|λ|·C`. Honest scope: an upper bound on
the decay — no claim the echo actually decays at this (or any) rate.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace QuantumChaos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The action of a matrix on a Euclidean vector is bounded by its L2
operator norm (definitionally `l2_opNorm_mulVec`). -/
lemma norm_toEuclideanLin_apply_le (M : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin M v‖ ≤ ‖M‖ * ‖v‖ := by
  have h : Matrix.toEuclideanLin M v
      = (EuclideanSpace.equiv ι ℂ).symm (M *ᵥ v.ofLp) := rfl
  rw [h]
  exact Matrix.l2_opNorm_mulVec M v

/-- **The telescoping perturbation bound**: iterating two matrix drives
from the same state separates at most linearly, one fresh `U − W` action
per period (the other factor is an isometry). -/
theorem norm_iterate_sub_iterate_le (U W : Matrix.unitaryGroup ι ℂ)
    (n : ℕ) (ψ : EuclideanSpace ℂ ι) :
    ‖(FloquetEvolution.ofUnitaryMatrix U).iterate n ψ
        - (FloquetEvolution.ofUnitaryMatrix W).iterate n ψ‖
      ≤ n * ‖U.val - W.val‖ * ‖ψ‖ := by
  induction n with
  | zero =>
    rw [FloquetEvolution.iterate_zero]
    simp
  | succ n ih =>
    set F₁ := FloquetEvolution.ofUnitaryMatrix U with hF₁
    set F₂ := FloquetEvolution.ofUnitaryMatrix W with hF₂
    have hsplit : F₁.iterate (n + 1) ψ - F₂.iterate (n + 1) ψ
        = (F₁.step (F₁.iterate n ψ) - F₁.step (F₂.iterate n ψ))
          + (F₁.step (F₂.iterate n ψ) - F₂.step (F₂.iterate n ψ)) := by
      rw [F₁.iterate_succ_apply', F₂.iterate_succ_apply']
      abel
    have h1 : ‖F₁.step (F₁.iterate n ψ) - F₁.step (F₂.iterate n ψ)‖
        = ‖F₁.iterate n ψ - F₂.iterate n ψ‖ := by
      rw [← map_sub F₁.step, F₁.step.norm_map]
    have h2 : ‖F₁.step (F₂.iterate n ψ) - F₂.step (F₂.iterate n ψ)‖
        ≤ ‖U.val - W.val‖ * ‖ψ‖ := by
      set v := F₂.iterate n ψ with hv
      have hstep : F₁.step v - F₂.step v
          = Matrix.toEuclideanLin (U.val - W.val) v := by
        rw [hF₁, hF₂, FloquetEvolution.ofUnitaryMatrix_step_apply,
          FloquetEvolution.ofUnitaryMatrix_step_apply, map_sub]
        rfl
      rw [hstep]
      calc ‖Matrix.toEuclideanLin (U.val - W.val) v‖
          ≤ ‖U.val - W.val‖ * ‖v‖ := norm_toEuclideanLin_apply_le _ _
        _ = ‖U.val - W.val‖ * ‖ψ‖ := by rw [hv, F₂.norm_iterate_apply]
    calc ‖F₁.iterate (n + 1) ψ - F₂.iterate (n + 1) ψ‖
        ≤ ‖F₁.step (F₁.iterate n ψ) - F₁.step (F₂.iterate n ψ)‖
            + ‖F₁.step (F₂.iterate n ψ) - F₂.step (F₂.iterate n ψ)‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ n * ‖U.val - W.val‖ * ‖ψ‖ + ‖U.val - W.val‖ * ‖ψ‖ := by
          rw [h1]
          exact add_le_add ih h2
      _ = (n + 1 : ℕ) * ‖U.val - W.val‖ * ‖ψ‖ := by
          push_cast
          ring

/-- ★ **The echo-perturbation bound**: on unit states,
`1 − L(n) ≤ 2·(n·‖U − W‖)` — Loschmidt decay is at most linear in period
count and drive distance. -/
theorem one_sub_loschmidtEcho_le (U W : Matrix.unitaryGroup ι ℂ)
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (n : ℕ) :
    1 - loschmidtEcho (FloquetEvolution.ofUnitaryMatrix U)
        (FloquetEvolution.ofUnitaryMatrix W) ψ n
      ≤ 2 * (n * ‖U.val - W.val‖) := by
  set F₁ := FloquetEvolution.ofUnitaryMatrix U with hF₁
  set F₂ := FloquetEvolution.ofUnitaryMatrix W with hF₂
  set z : ℂ := inner ℂ (F₂.iterate n ψ) (F₁.iterate n ψ) with hz
  have hecho : loschmidtEcho F₁ F₂ ψ n = ‖z‖ ^ 2 := rfl
  have hz1 : ‖z‖ ≤ 1 := by
    calc ‖z‖ ≤ ‖F₂.iterate n ψ‖ * ‖F₁.iterate n ψ‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by
          rw [F₁.norm_iterate_apply, F₂.norm_iterate_apply, hψ, mul_one]
  have hone : (1 : ℂ) - z
      = inner ℂ (F₂.iterate n ψ) (F₂.iterate n ψ - F₁.iterate n ψ) := by
    rw [inner_sub_right, hz]
    congr 1
    rw [inner_self_eq_norm_sq_to_K, F₂.norm_iterate_apply, hψ]
    norm_num
  have hbound : ‖(1 : ℂ) - z‖ ≤ n * ‖U.val - W.val‖ := by
    rw [hone]
    calc ‖inner ℂ (F₂.iterate n ψ) (F₂.iterate n ψ - F₁.iterate n ψ)‖
        ≤ ‖F₂.iterate n ψ‖ * ‖F₂.iterate n ψ - F₁.iterate n ψ‖ :=
          norm_inner_le_norm _ _
      _ = ‖F₂.iterate n ψ - F₁.iterate n ψ‖ := by
          rw [F₂.norm_iterate_apply, hψ, one_mul]
      _ ≤ n * ‖W.val - U.val‖ * ‖ψ‖ :=
          norm_iterate_sub_iterate_le W U n ψ
      _ = n * ‖U.val - W.val‖ := by rw [norm_sub_rev, hψ, mul_one]
  have h2 : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
    calc 1 - ‖z‖ = ‖(1 : ℂ)‖ - ‖z‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [hecho]
  nlinarith [norm_nonneg z, norm_nonneg ((1 : ℂ) - z), hz1, h2, hbound]

end QuantumChaos
