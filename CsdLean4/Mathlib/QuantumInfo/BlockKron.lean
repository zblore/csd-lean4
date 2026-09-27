/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ControlledSingle

/-!
# The tensor product over blocks

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #86, step (a) of its route: the
layer a *concatenated* code needs, where a register is a family of blocks and an operator is one
operator per block.

`blockKron M` is the matrix on the label space `β → L` whose entry at `(k, l)` is the product
`∏_b (M b) (k b) (l b)`. It is the `β`-fold tensor product written on function labels instead of
through `Matrix.kron`, which keeps the label space of a `k`-fold concatenation literally recursive
(`Fin 7 → Fin 7 → ⋯ → Fin 2`) instead of a tower of reindexings.

* `blockKron_one`, ★ `blockKron_mul`, `blockKron_conjTranspose`, `blockKron_smul` — the algebra.
  Multiplicativity and the expansion below are both `Fintype.prod_sum`: a product of sums over the
  blocks is a sum over the *functions* choosing one summand per block;
* ★ `blockKron_sum` — **multilinearity**: expanding each block over a finite family expands the
  tensor over the function space of choices. This is what lets an arbitrary operator per block be
  written in a fixed finite family (`Matrix.matrix_eq_sum_single` at the leaves);
* ★ `blockKron_single_eq_gateOf` — the family with one slot filled and the identity elsewhere **is**
  #83's single-qubit gate `gateOf b₀ G` on a qubit register, which ties the layer back to the
  controlled-gate vocabulary.

## Honest scope

⚠️ No `Matrix.kron` bridge: `blockKron` is not identified with an iterated Kronecker product here.
Nothing in the concatenation needs that identification, and stating it would need the reindexing
`(β → L) ≃ β × L`-style equivalences this layer exists to avoid.
⚠️ Unitarity of `blockKron M` for unitary blocks is not proved here (it follows from
`blockKron_mul` and `blockKron_conjTranspose` where it is wanted).

## Source

M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information* §10.6.1 (concatenated codes);
`QuantumInfo/ControlledSingle.lean` (#84), `QuantumInfo/ControlledGate.lean` (#83);
`specs/BACKLOG.md` #86; `specs/steane-plan.md`; `specs/future-work.md`.
-/

@[expose] public section

open Finset Matrix

namespace QuantumInfo

/-- The **tensor product over blocks**: one matrix per block, acting on the labels `β → L`. -/
def blockKron {β L L' : Type*} [Fintype β] (M : β → Matrix L L' ℂ) :
    Matrix (β → L) (β → L') ℂ :=
  fun k l => ∏ b, M b (k b) (l b)

theorem blockKron_apply {β L L' : Type*} [Fintype β] (M : β → Matrix L L' ℂ)
    (k : β → L) (l : β → L') : blockKron M k l = ∏ b, M b (k b) (l b) := rfl

theorem blockKron_one {β L : Type*} [Fintype β] [DecidableEq L] :
    blockKron (fun _ : β => (1 : Matrix L L ℂ)) = 1 := by
  ext k l
  by_cases h : k = l
  · subst h
    rw [Matrix.one_apply_eq, blockKron_apply]
    exact Finset.prod_eq_one fun b _ => Matrix.one_apply_eq _
  · rw [Matrix.one_apply_ne h, blockKron_apply]
    obtain ⟨b, hb⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ b) (Matrix.one_apply_ne hb)

/-- ★ **The tensor over blocks is multiplicative**: a product of sums over the blocks is a sum over
the functions choosing one summand per block (`Fintype.prod_sum`). -/
theorem blockKron_mul {β L L' L'' : Type*} [Fintype β] [DecidableEq β] [Fintype L']
    (M : β → Matrix L L' ℂ) (N : β → Matrix L' L'' ℂ) :
    blockKron M * blockKron N = blockKron (fun b => M b * N b) := by
  ext k l
  rw [Matrix.mul_apply, blockKron_apply]
  simp only [Matrix.mul_apply]
  rw [Fintype.prod_sum fun (b : β) (j : L') => M b (k b) j * N b j (l b)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [blockKron_apply, blockKron_apply, ← Finset.prod_mul_distrib]

theorem blockKron_conjTranspose {β L L' : Type*} [Fintype β] (M : β → Matrix L L' ℂ) :
    (blockKron M)ᴴ = blockKron (fun b => (M b)ᴴ) := by
  ext k l
  rw [Matrix.conjTranspose_apply, blockKron_apply, blockKron_apply, star_prod]
  exact Finset.prod_congr rfl fun b _ => (Matrix.conjTranspose_apply _ _ _).symm

/-- A zero block kills the tensor. -/
theorem blockKron_eq_zero {β L L' : Type*} [Fintype β] {M : β → Matrix L L' ℂ} {b : β}
    (hb : M b = 0) : blockKron M = 0 := by
  ext k l
  rw [blockKron_apply, Matrix.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hb, Matrix.zero_apply])

/-- Scalars pull out of every block at once. -/
theorem blockKron_smul {β L L' : Type*} [Fintype β] (c : β → ℂ) (M : β → Matrix L L' ℂ) :
    blockKron (fun b => c b • M b) = (∏ b, c b) • blockKron M := by
  ext k l
  simp only [blockKron_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-- ★ **Multilinearity**: expanding every block over a finite family expands the tensor over the
functions choosing one index per block. -/
theorem blockKron_sum {β L L' ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι]
    (f : β → ι → Matrix L L' ℂ) :
    blockKron (fun b => ∑ i, f b i) = ∑ g : β → ι, blockKron (fun b => f b (g b)) := by
  ext k l
  rw [blockKron_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, blockKron_apply]
  exact Fintype.prod_sum fun (b : β) (i : ι) => f b i (k b) (l b)

/-- The same expansion with coefficients, the form the concatenation uses: an arbitrary operator per
block is a combination of a fixed finite family. -/
theorem blockKron_sum_smul {β L L' ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι]
    (a : β → ι → ℂ) (f : β → ι → Matrix L L' ℂ) :
    blockKron (fun b => ∑ i, a b i • f b i)
      = ∑ g : β → ι, (∏ b, a b (g b)) • blockKron (fun b => f b (g b)) := by
  rw [blockKron_sum fun b i => a b i • f b i]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [blockKron_smul (fun b => a b (g b)) fun b => f b (g b)]

/-- ★ **One slot filled, the identity elsewhere, is a single-qubit gate**: the tensor over blocks
with `G` at `b₀` is #83's `gateOf b₀ G` on the qubit register. -/
theorem blockKron_single_eq_gateOf {m : ℕ} (b₀ : Fin m) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    blockKron (fun b : Fin m => if b = b₀ then G else 1) = Controlled.gateOf b₀ G := by
  ext k l
  rw [blockKron_apply]
  by_cases hag : ∀ i, i ≠ b₀ → k i = l i
  · rw [Controlled.gateOf, Controlled.singleGate,
      Controlled.ctrlSet_apply_of_ctrl hag (by simp), Controlled.blockEntry_eq_apply,
      ← Matrix.eta_fin_two G]
    rw [Finset.prod_eq_single b₀]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb, Matrix.one_apply, if_pos (hag b hb)]
    · intro h
      exact absurd (Finset.mem_univ b₀) h
  · rw [Controlled.gateOf, Controlled.singleGate, Controlled.ctrlSet_apply_of_not_agree hag]
    obtain ⟨b, hb⟩ := not_forall.mp hag
    rw [Classical.not_imp] at hb
    refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    rw [if_neg hb.1, Matrix.one_apply, if_neg hb.2]

end QuantumInfo
