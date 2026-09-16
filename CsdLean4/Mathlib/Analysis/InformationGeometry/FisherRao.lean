/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fisher–Rao metric on the open simplex (mirror of Physlib PR #1652)

**Category:** 1-Mathlib (CSD-free; a verbatim mirror of a Physlib file, to be deleted when the
PR merges).

**Provenance.** This file mirrors the metric half of `QuantumInfo/ForMathlib/FisherRao.lean`
from Physlib pull request #1652 (`leanprover-community/physlib`, branch
`naype888-cloud:nava-fisher-rao-cramer-rao`, commit `5e6f0837630b`, 2026-09-15), by Eduardo
Nava-Hernandez. The declarations are copied unchanged, under the same namespace `FisherRao`,
so that a theorem stated against them here is the same theorem in Physlib with one import
line changed. The only edits are the module-system header (`module`, `public import`,
`@[expose] public section`) and docstrings on the three fields of `OpenSimplex`, both of which
this repository's lints require. The Cramér–Rao half of the
source file (`expect`, `variance`, `cramerRao`) is not needed by the bridge and is not
mirrored.

**Delete this file and import Physlib when the PR merges.** Until then csd-lean4 does not
depend on Physlib, and must not depend on an unmerged branch.

## Main definitions

* `FisherRao.OpenSimplex` — a point on the open probability simplex
* `FisherRao.OpenSimplex.fisherRaoInner` — the Fisher–Rao inner product gₚ(u,v) = Σᵢ uᵢvᵢ/pᵢ
* `FisherRao.fisherInfo` — classical Fisher information I(θ) for a parametric family

## References

* C. R. Rao, *Information and the accuracy attainable in the estimation
  of statistical parameters*, Bull. Calcutta Math. Soc. 37, 81–91 (1945)
* H. Cramér, *Mathematical Methods of Statistics*, Princeton (1946)
* `specs/future-work.md` (the completed-work ledger; the bridge this file serves).
-/

@[expose] public section

noncomputable section

open Finset BigOperators

variable {α : Type*} [Fintype α]

namespace FisherRao

/-! ## Open probability simplex -/

/-- A point on the open probability simplex: strictly positive weights summing to 1. -/
structure OpenSimplex (α : Type*) [Fintype α] where
  /-- The weights. -/
  val : α → ℝ
  /-- Every weight is strictly positive. -/
  pos : ∀ i, 0 < val i
  /-- The weights sum to one. -/
  sum_one : ∑ i : α, val i = 1

namespace OpenSimplex

variable (p : OpenSimplex α)

theorem val_ne_zero (i : α) : p.val i ≠ 0 := ne_of_gt (p.pos i)

theorem val_nonneg (i : α) : 0 ≤ p.val i := le_of_lt (p.pos i)

/-! ## Fisher–Rao inner product -/

/-- The Fisher–Rao inner product at p ∈ Δ°(α): gₚ(u, v) = Σᵢ uᵢ vᵢ / pᵢ. -/
def fisherRaoInner (u v : α → ℝ) : ℝ :=
  ∑ i : α, u i * v i / p.val i

/-- The Fisher–Rao quadratic form. -/
def fisherRaoSq (u : α → ℝ) : ℝ := p.fisherRaoInner u u

theorem fisherRaoSq_nonneg (u : α → ℝ) : 0 ≤ p.fisherRaoSq u := by
  apply Finset.sum_nonneg
  intro i _
  apply div_nonneg
  · exact mul_self_nonneg (u i)
  · exact p.val_nonneg i

theorem fisherRaoSq_eq_zero_iff (u : α → ℝ) :
    p.fisherRaoSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ u i * u i / p.val i := by
      intro i _
      exact div_nonneg (mul_self_nonneg _) (p.val_nonneg i)
    have hall := Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp h
    ext i
    simp only [Pi.zero_apply]
    have hi := hall i (Finset.mem_univ i)
    rcases div_eq_zero_iff.mp hi with hmul | habs
    · exact mul_self_eq_zero.mp hmul
    · exact absurd habs (p.val_ne_zero i)
  · intro h
    simp [fisherRaoSq, fisherRaoInner, h]

theorem fisherRaoInner_comm (u v : α → ℝ) :
    p.fisherRaoInner u v = p.fisherRaoInner v u := by
  simp only [fisherRaoInner]
  congr 1; ext i; ring

/-! ## Cauchy–Schwarz for the Fisher–Rao inner product -/

private theorem fisherRaoInner_sub_smul (u v : α → ℝ) (t : ℝ) :
    p.fisherRaoSq (fun i => u i - t * v i) =
      p.fisherRaoSq u - 2 * t * p.fisherRaoInner u v +
        t ^ 2 * p.fisherRaoSq v := by
  simp only [fisherRaoSq, fisherRaoInner]
  rw [show (∑ i : α, (u i - t * v i) * (u i - t * v i) / p.val i) =
    (∑ i : α, u i * u i / p.val i) - 2 * t * (∑ i : α, u i * v i / p.val i) +
      t ^ 2 * (∑ i : α, v i * v i / p.val i) from by
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring]

/-- **Cauchy–Schwarz** for the Fisher–Rao inner product:
gₚ(u, v)² ≤ gₚ(u, u) · gₚ(v, v). -/
theorem fisherRao_cauchy_schwarz (u v : α → ℝ) :
    p.fisherRaoInner u v ^ 2 ≤ p.fisherRaoSq u * p.fisherRaoSq v := by
  by_cases hv : p.fisherRaoSq v = 0
  · rw [p.fisherRaoSq_eq_zero_iff] at hv
    simp [fisherRaoInner, fisherRaoSq, hv]
  · have hvpos : 0 < p.fisherRaoSq v :=
      lt_of_le_of_ne (p.fisherRaoSq_nonneg v) (Ne.symm hv)
    set t := p.fisherRaoInner u v / p.fisherRaoSq v with ht_def
    have key := p.fisherRaoSq_nonneg (fun i => u i - t * v i)
    rw [p.fisherRaoInner_sub_smul u v t] at key
    have ht2 : t * p.fisherRaoInner u v =
        p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v := by
      rw [ht_def]; field_simp
    have ht3 : t ^ 2 * p.fisherRaoSq v =
        p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v := by
      rw [ht_def]; field_simp
    rw [show 2 * t * p.fisherRaoInner u v =
        2 * (p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v) from by
      linarith [ht2]] at key
    rw [ht3] at key
    have h1 : p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v ≤ p.fisherRaoSq u :=
      by linarith
    rwa [div_le_iff₀ hvpos] at h1

end OpenSimplex

/-! ## Classical Fisher information -/

/-- Classical Fisher information for a 1-parameter discrete family θ ↦ p(·|θ),
defined as I(θ) = Σᵢ (∂pᵢ/∂θ)² / pᵢ(θ). -/
def fisherInfo (p : α → ℝ) (dp : α → ℝ) : ℝ :=
  ∑ i : α, dp i ^ 2 / p i

theorem fisherInfo_nonneg (p dp : α → ℝ) (hpos : ∀ i, 0 < p i) :
    0 ≤ fisherInfo p dp := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hpos i))

/-- Fisher information equals the Fisher–Rao squared norm of the derivative vector. -/
theorem fisherInfo_eq_fisherRaoSq (q : OpenSimplex α) (dp : α → ℝ) :
    fisherInfo q.val dp = q.fisherRaoSq dp := by
  simp only [fisherInfo, OpenSimplex.fisherRaoSq, OpenSimplex.fisherRaoInner]
  congr 1; ext i; ring

end FisherRao
