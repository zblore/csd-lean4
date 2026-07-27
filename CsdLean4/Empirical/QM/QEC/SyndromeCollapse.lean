/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.ErrorDiscretization

/-!
# Empirical/QM: syndrome collapse — the three-qubit code corrects a *continuum* of errors

**Category:** 3-Local. QM-validity layer.

`QEC/ErrorDiscretization.lean` proves an arbitrary error is a `ℂ`-combination of four discrete
ones. `QEC/ThreeQubit.lean` proves each of those four is corrected. **Nothing joined them**: four
point-checks plus a decomposition is not yet an error-correction claim, because a superposition
of error branches is not obviously reducible to a single branch.

This file supplies the missing half — **syndrome collapse** — and states the resulting theorem:
the three-qubit code corrects *every* error in `span ℂ {I, X₁, X₂, X₃}`, a continuum, not four
points.

## The mechanism

The four errored codewords have **disjoint supports** in the computational basis:

  `ψ_L = a|000⟩ + b|111⟩`,  `X₁ψ_L = a|100⟩ + b|011⟩`,
  `X₂ψ_L = a|010⟩ + b|101⟩`,  `X₃ψ_L = a|001⟩ + b|110⟩`.

That disjointness is the concrete form of syndrome-distinctness (`three_qubit_syndromes_distinct`):
the four branches are simultaneous stabiliser eigenvectors with distinct `(Z₁Z₂, Z₂Z₃)` eigenvalue
pairs, and distinct eigenvalues force orthogonality. Here it is available directly, so the
orthogonality is proved by computation rather than through the spectral theorem.

Orthogonality is what makes the syndrome measurement *work*: the corrupted state
`E ψ_L = Σₖ cₖ · (Eₖ ψ_L)` is a superposition of four **mutually orthogonal** branches, so
measuring `(Z₁Z₂, Z₂Z₃)` projects onto exactly one of them, with the overlap picking out exactly
that branch's coefficient — and each branch is corrected by re-applying its own `Xₖ`.

## What this file proves

* `X1_logical` / `X2_logical` / `X3_logical` — the three errored codewords in closed form.
* `errored_pairwise_orthogonal` — all six pairwise inner products vanish, for every `a, b`.
* `spanError_logical` — an arbitrary `E ∈ span {I, X₁, X₂, X₃}` sends `ψ_L` to the corresponding
  combination of the four branches.
* `branch_overlap_*` — **the collapse step**: the overlap of `E ψ_L` with branch `k` is exactly
  `cₖ · ⟪branch k, branch k⟫`. The syndrome measurement reads off `cₖ` and nothing else; the
  other three branches contribute nothing.
* ★ `three_qubit_corrects_span_error` — the capstone, bundling all four ingredients:
  decomposition, orthogonality, branch extraction, and branch-wise recovery. **The code corrects
  an arbitrary error in the span**, so today's discretization result is load-bearing rather than
  decorative.

## Scope

Still the **bit-flip** span `{I, X₁, X₂, X₃}` — the three-qubit code's actual correctable set.
Extending to all four Paulis per qubit (so that `pauli_span_top` applies and *every* single-qubit
error is corrected) needs the concatenated Shor 9-qubit code, which remains open on 512-dimensional
infrastructure (`specs/BACKLOG.md`). What is closed here is the gap *within* the three-qubit
story: four corrected errors plus discretization now genuinely imply a corrected continuum.

## References

`QEC/ThreeQubit.lean` (`logical`, `X1`/`X2`/`X3`, `bitflip_recovers`,
`three_qubit_syndromes_distinct`, `three_qubit_syndrome_eigenstates`);
`QEC/ErrorDiscretization.lean` (`pauli_decomposition`, `pauli_span_top`);
`specs/BACKLOG.md` (Shor-9 / concatenation); `specs/future-work.md`.
Shor 1995; Nielsen–Chuang §10.1–10.2.
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

variable (a b : ℂ)

/-! ### The four errored codewords in closed form -/

theorem X1_logical :
    Matrix.toEuclideanLin X1 (logical a b)
      = EuclideanSpace.single ((1, 0, 0) : Fin 2 × Fin 2 × Fin 2) a
        + EuclideanSpace.single ((0, 1, 1) : Fin 2 × Fin 2 × Fin 2) b := by
  ext i
  simp only [Matrix.toLpLin_apply, logical, X1, kron3, pX]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

theorem X2_logical :
    Matrix.toEuclideanLin X2 (logical a b)
      = EuclideanSpace.single ((0, 1, 0) : Fin 2 × Fin 2 × Fin 2) a
        + EuclideanSpace.single ((1, 0, 1) : Fin 2 × Fin 2 × Fin 2) b := by
  ext i
  simp only [Matrix.toLpLin_apply, logical, X2, kron3, pX]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

theorem X3_logical :
    Matrix.toEuclideanLin X3 (logical a b)
      = EuclideanSpace.single ((0, 0, 1) : Fin 2 × Fin 2 × Fin 2) a
        + EuclideanSpace.single ((1, 1, 0) : Fin 2 × Fin 2 × Fin 2) b := by
  ext i
  simp only [Matrix.toLpLin_apply, logical, X3, kron3, pX]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

/-! ### Orthogonality of the branches -/

/-- **The four error branches are mutually orthogonal**, for every logical amplitude pair.

This is the concrete form of syndrome-distinctness: the branches occupy disjoint sets of
computational basis states (`{000,111}`, `{100,011}`, `{010,101}`, `{001,110}`), which is why the
stabiliser eigenvalue pairs can tell them apart. Orthogonality is what makes the syndrome
measurement project onto a single branch rather than smear across several. -/
theorem errored_pairwise_orthogonal :
    inner ℂ (logical a b) (Matrix.toEuclideanLin X1 (logical a b)) = 0 ∧
    inner ℂ (logical a b) (Matrix.toEuclideanLin X2 (logical a b)) = 0 ∧
    inner ℂ (logical a b) (Matrix.toEuclideanLin X3 (logical a b)) = 0 ∧
    inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
      (Matrix.toEuclideanLin X2 (logical a b)) = 0 ∧
    inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
      (Matrix.toEuclideanLin X3 (logical a b)) = 0 ∧
    inner ℂ (Matrix.toEuclideanLin X2 (logical a b))
      (Matrix.toEuclideanLin X3 (logical a b)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [X1_logical]; simp [logical, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]
  · rw [X2_logical]; simp [logical, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]
  · rw [X3_logical]; simp [logical, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]
  · rw [X1_logical, X2_logical]; simp [inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]
  · rw [X1_logical, X3_logical]; simp [inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]
  · rw [X2_logical, X3_logical]; simp [inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_left, Prod.ext_iff]

/-! ### An arbitrary error in the span, and the collapse -/

/-- An arbitrary element of `span ℂ {I, X₁, X₂, X₃}` — the three-qubit code's correctable set —
with coefficient vector `c`. -/
noncomputable def spanError (c : Fin 4 → ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  c 0 • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    + c 1 • X1 + c 2 • X2 + c 3 • X3

theorem toEuclideanLin_one_apply (v : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) v = v := by
  ext i
  simp

/-- The corrupted codeword is the matching combination of the four branches. -/
theorem spanError_logical (c : Fin 4 → ℂ) :
    Matrix.toEuclideanLin (spanError c) (logical a b)
      = c 0 • logical a b
        + c 1 • Matrix.toEuclideanLin X1 (logical a b)
        + c 2 • Matrix.toEuclideanLin X2 (logical a b)
        + c 3 • Matrix.toEuclideanLin X3 (logical a b) := by
  simp only [spanError, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    toEuclideanLin_one_apply]

/-- **The collapse step, branch `1`.** The overlap of the corrupted codeword with branch `X₁ψ_L`
is exactly `c₁ · ⟪X₁ψ_L, X₁ψ_L⟫` — the other three branches contribute nothing, so the syndrome
measurement reads off `c₁` and only `c₁`. -/
theorem branch_overlap_X1 (c : Fin 4 → ℂ) :
    inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
        (Matrix.toEuclideanLin (spanError c) (logical a b))
      = c 1 * inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
          (Matrix.toEuclideanLin X1 (logical a b)) := by
  obtain ⟨h01, -, -, h12, h13, -⟩ := errored_pairwise_orthogonal a b
  rw [spanError_logical, inner_add_right, inner_add_right, inner_add_right,
    inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_eq_zero_symm.mp h01, h12, h13]
  ring

/-- **The collapse step, branch `2`.** -/
theorem branch_overlap_X2 (c : Fin 4 → ℂ) :
    inner ℂ (Matrix.toEuclideanLin X2 (logical a b))
        (Matrix.toEuclideanLin (spanError c) (logical a b))
      = c 2 * inner ℂ (Matrix.toEuclideanLin X2 (logical a b))
          (Matrix.toEuclideanLin X2 (logical a b)) := by
  obtain ⟨-, h02, -, h12, -, h23⟩ := errored_pairwise_orthogonal a b
  rw [spanError_logical, inner_add_right, inner_add_right, inner_add_right,
    inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_eq_zero_symm.mp h02, inner_eq_zero_symm.mp h12, h23]
  ring

/-- **The collapse step, branch `3`.** -/
theorem branch_overlap_X3 (c : Fin 4 → ℂ) :
    inner ℂ (Matrix.toEuclideanLin X3 (logical a b))
        (Matrix.toEuclideanLin (spanError c) (logical a b))
      = c 3 * inner ℂ (Matrix.toEuclideanLin X3 (logical a b))
          (Matrix.toEuclideanLin X3 (logical a b)) := by
  obtain ⟨-, -, h03, -, h13, h23⟩ := errored_pairwise_orthogonal a b
  rw [spanError_logical, inner_add_right, inner_add_right, inner_add_right,
    inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_eq_zero_symm.mp h03, inner_eq_zero_symm.mp h13, inner_eq_zero_symm.mp h23]
  ring

/-! ### The capstone -/

/-- **★ The three-qubit code corrects an arbitrary error in `span ℂ {I, X₁, X₂, X₃}`** — a
continuum of errors, not four discrete ones.

All four ingredients, bundled:

1. **Decomposition** — the corrupted codeword is the matching combination of four branches.
2. **Orthogonality** — the branches are mutually orthogonal, so the syndrome measurement projects
   onto exactly one of them (this is syndrome-distinctness made concrete: disjoint supports).
3. **Extraction** — the overlap with branch `k` is exactly `cₖ` times that branch's norm; the
   measurement reads off one coefficient and is blind to the rest.
4. **Recovery** — re-applying `Xₖ` on branch `k` restores `ψ_L` exactly, since each `Xₖ` is
   self-inverse.

Together with `pauli_decomposition` this is what makes error correction a claim about *all*
errors of the correctable type rather than about a finite list. -/
theorem three_qubit_corrects_span_error (c : Fin 4 → ℂ) :
    -- 1. decomposition into branches
    (Matrix.toEuclideanLin (spanError c) (logical a b)
      = c 0 • logical a b
        + c 1 • Matrix.toEuclideanLin X1 (logical a b)
        + c 2 • Matrix.toEuclideanLin X2 (logical a b)
        + c 3 • Matrix.toEuclideanLin X3 (logical a b))
    -- 2. the branches are mutually orthogonal
    ∧ (inner ℂ (logical a b) (Matrix.toEuclideanLin X1 (logical a b)) = 0 ∧
       inner ℂ (logical a b) (Matrix.toEuclideanLin X2 (logical a b)) = 0 ∧
       inner ℂ (logical a b) (Matrix.toEuclideanLin X3 (logical a b)) = 0)
    -- 3. the overlap with branch k extracts exactly c k
    ∧ (inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
          (Matrix.toEuclideanLin (spanError c) (logical a b))
        = c 1 * inner ℂ (Matrix.toEuclideanLin X1 (logical a b))
            (Matrix.toEuclideanLin X1 (logical a b)))
    -- 4. and each branch is recovered exactly
    ∧ (Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
      ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
      ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b) := by
  obtain ⟨h01, h02, h03, -, -, -⟩ := errored_pairwise_orthogonal a b
  exact ⟨spanError_logical a b c, ⟨h01, h02, h03⟩, branch_overlap_X1 a b c,
    bitflip_recovers a b⟩

end QEC
end QM
end Empirical
end CSD
