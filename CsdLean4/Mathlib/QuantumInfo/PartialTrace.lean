/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.BigOperators

/-!
# Matrix partial trace (K1-B.1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **partial trace** of a bipartite matrix `M : Matrix (n × m) (n × m) ℂ`. Mathlib has **no**
matrix partial trace (the only `partialTrace` declarations are category-theoretic / probability
kernels), so this is genuinely new infrastructure. It is the shared prerequisite for K1-B
subadditivity (`specs/k1-plan.md`), the gated decoherence / entangled D1 tier, and the
Landauer / ontic-entropy touchpoint.

For `M : Matrix (n × m) (n × m) ℂ`:

* `partialTraceRight M : Matrix n n ℂ`, `(Tr_B M) i j = ∑ₖ M (i,k) (j,k)` — trace out the
  second (B) factor, leaving the first (A) factor;
* `partialTraceLeft M : Matrix m m ℂ`, `(Tr_A M) k l = ∑ᵢ M (i,k) (i,l)` — trace out the
  first (A) factor.

Delivered, foundational-triple-only and AxiomAudit-pinned:

* **linearity** (`_add`, `_smul`, and the bundled `partialTraceRightₗ`/`partialTraceLeftₗ`
  `LinearMap`s);
* **trace preservation** `trace (Tr_B M) = trace M` (`partialTraceRight_trace`,
  `partialTraceLeft_trace`), via `Fintype.sum_prod_type`;
* **tensor reduction** `Tr_B (ρ ⊗ₖ σ) = (trace σ) • ρ` and `Tr_A (ρ ⊗ₖ σ) = (trace ρ) • σ`
  (`partialTraceRight_kronecker`, `partialTraceLeft_kronecker`) — note the trace of the
  **traced-out** factor multiplies the surviving one;
* **`IsHermitian` preservation** (`partialTraceRight_isHermitian`,
  `partialTraceLeft_isHermitian`);
* **`PosSemidef` preservation** (`partialTraceRight_posSemidef`, `partialTraceLeft_posSemidef`),
  via the witness vectors `w_k (i,k') = if k' = k then v i else 0` (a `v ⊗ eₖ` tensor),
  for which `star v ⬝ᵥ (Tr_B M) *ᵥ v = ∑ₖ star (w_k) ⬝ᵥ M *ᵥ (w_k)`, each summand `≥ 0` by
  `M.PosSemidef`;
* **density ↦ density** (`partialTraceRight_density`, `partialTraceLeft_density`): the reduced
  state of a density operator is a density operator.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ## Definitions -/

/-- The **right partial trace** `Tr_B : Matrix (n × m) (n × m) ℂ → Matrix n n ℂ`, tracing out the
second (B) factor: `(Tr_B M) i j = ∑ₖ M (i,k) (j,k)`. Leaves the first (A) factor. -/
noncomputable def partialTraceRight (M : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k : m, M (i, k) (j, k)

/-- The **left partial trace** `Tr_A : Matrix (n × m) (n × m) ℂ → Matrix m m ℂ`, tracing out the
first (A) factor: `(Tr_A M) k l = ∑ᵢ M (i,k) (i,l)`. Leaves the second (B) factor. -/
noncomputable def partialTraceLeft (M : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  Matrix.of fun k l => ∑ i : n, M (i, k) (i, l)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem partialTraceRight_apply (M : Matrix (n × m) (n × m) ℂ) (i j : n) :
    partialTraceRight M i j = ∑ k : m, M (i, k) (j, k) := rfl

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem partialTraceLeft_apply (M : Matrix (n × m) (n × m) ℂ) (k l : m) :
    partialTraceLeft M k l = ∑ i : n, M (i, k) (i, l) := rfl

/-! ## Linearity -/

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem partialTraceRight_add (A B : Matrix (n × m) (n × m) ℂ) :
    partialTraceRight (A + B) = partialTraceRight A + partialTraceRight B := by
  ext i j; simp [partialTraceRight_apply, Finset.sum_add_distrib]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem partialTraceRight_smul (c : ℂ) (A : Matrix (n × m) (n × m) ℂ) :
    partialTraceRight (c • A) = c • partialTraceRight A := by
  ext i j; simp [partialTraceRight_apply, Finset.mul_sum]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem partialTraceLeft_add (A B : Matrix (n × m) (n × m) ℂ) :
    partialTraceLeft (A + B) = partialTraceLeft A + partialTraceLeft B := by
  ext k l; simp [partialTraceLeft_apply, Finset.sum_add_distrib]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem partialTraceLeft_smul (c : ℂ) (A : Matrix (n × m) (n × m) ℂ) :
    partialTraceLeft (c • A) = c • partialTraceLeft A := by
  ext k l; simp [partialTraceLeft_apply, Finset.mul_sum]

/-- The **right partial trace** bundled as a `ℂ`-linear map. -/
noncomputable def partialTraceRightₗ : Matrix (n × m) (n × m) ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' := partialTraceRight_smul

/-- The **left partial trace** bundled as a `ℂ`-linear map. -/
noncomputable def partialTraceLeftₗ : Matrix (n × m) (n × m) ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' := partialTraceLeft_smul

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
@[simp] theorem partialTraceRightₗ_apply (M : Matrix (n × m) (n × m) ℂ) :
    partialTraceRightₗ M = partialTraceRight M := rfl

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
@[simp] theorem partialTraceLeftₗ_apply (M : Matrix (n × m) (n × m) ℂ) :
    partialTraceLeftₗ M = partialTraceLeft M := rfl

/-! ## Trace preservation -/

omit [DecidableEq n] [DecidableEq m] in
/-- **Trace preservation:** `trace (Tr_B M) = trace M`.
`∑ᵢ ∑ₖ M (i,k) (i,k) = ∑_{(i,k)} M (i,k) (i,k) = trace M` via `Fintype.sum_prod_type`. -/
@[simp] theorem partialTraceRight_trace (M : Matrix (n × m) (n × m) ℂ) :
    (partialTraceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceRight_apply]
  rw [Fintype.sum_prod_type]

omit [DecidableEq n] [DecidableEq m] in
/-- **Trace preservation:** `trace (Tr_A M) = trace M`. -/
@[simp] theorem partialTraceLeft_trace (M : Matrix (n × m) (n × m) ℂ) :
    (partialTraceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceLeft_apply]
  rw [Fintype.sum_prod_type_right]

/-! ## Tensor reduction -/

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- **Tensor reduction:** `Tr_B (ρ ⊗ₖ σ) = (trace σ) • ρ`. The trace of the **traced-out**
factor `σ` multiplies the surviving factor `ρ`:
`(ρ⊗σ)((i,k),(j,k)) = ρ i j · σ k k`, so `∑ₖ ρ i j · σ k k = ρ i j · trace σ`. -/
@[simp] theorem partialTraceRight_kronecker (ρ : Matrix n n ℂ) (σ : Matrix m m ℂ) :
    partialTraceRight (ρ ⊗ₖ σ) = σ.trace • ρ := by
  ext i j
  simp only [partialTraceRight_apply, Matrix.kronecker_apply, Matrix.smul_apply,
    Matrix.trace, Matrix.diag_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_comm]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- **Tensor reduction:** `Tr_A (ρ ⊗ₖ σ) = (trace ρ) • σ`. The trace of the **traced-out**
factor `ρ` multiplies the surviving factor `σ`. -/
@[simp] theorem partialTraceLeft_kronecker (ρ : Matrix n n ℂ) (σ : Matrix m m ℂ) :
    partialTraceLeft (ρ ⊗ₖ σ) = ρ.trace • σ := by
  ext k l
  simp only [partialTraceLeft_apply, Matrix.kronecker_apply, Matrix.smul_apply,
    Matrix.trace, Matrix.diag_apply, smul_eq_mul]
  rw [← Finset.sum_mul]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- **Reduced product state:** `Tr_B (ρ ⊗ₖ σ) = ρ` when `trace σ = 1`. The K1-B.2 consumer:
the right reduced state of a product density operator is its left factor. -/
theorem partialTraceRight_kronecker_trace_one (ρ : Matrix n n ℂ) (σ : Matrix m m ℂ)
    (hσ : σ.trace = 1) : partialTraceRight (ρ ⊗ₖ σ) = ρ := by
  rw [partialTraceRight_kronecker, hσ, one_smul]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- **Reduced product state:** `Tr_A (ρ ⊗ₖ σ) = σ` when `trace ρ = 1`. -/
theorem partialTraceLeft_kronecker_trace_one (ρ : Matrix n n ℂ) (σ : Matrix m m ℂ)
    (hρ : ρ.trace = 1) : partialTraceLeft (ρ ⊗ₖ σ) = σ := by
  rw [partialTraceLeft_kronecker, hρ, one_smul]

/-! ## `IsHermitian` preservation -/

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- **`IsHermitian` preservation:** `M.IsHermitian → (Tr_B M).IsHermitian`. From
`M (a) (b) = star (M b a)` (the Hermitian condition `Mᴴ = M`), the sum
`(Tr_B M)ᴴ i j = star (∑ₖ M (j,k) (i,k)) = ∑ₖ M (i,k) (j,k) = (Tr_B M) i j`. -/
theorem partialTraceRight_isHermitian {M : Matrix (n × m) (n × m) ℂ} (hM : M.IsHermitian) :
    (partialTraceRight M).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, partialTraceRight_apply, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := congrFun (congrFun hM.eq (i, k)) (j, k)
  simpa [Matrix.conjTranspose_apply] using this

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- **`IsHermitian` preservation:** `M.IsHermitian → (Tr_A M).IsHermitian`. -/
theorem partialTraceLeft_isHermitian {M : Matrix (n × m) (n × m) ℂ} (hM : M.IsHermitian) :
    (partialTraceLeft M).IsHermitian := by
  ext k l
  simp only [Matrix.conjTranspose_apply, partialTraceLeft_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun (congrFun hM.eq (i, k)) (i, l)
  simpa [Matrix.conjTranspose_apply] using this

/-! ## `PosSemidef` preservation -/

/-- The Hermitian quadratic form expanded as an explicit double sum:
`star u ⬝ᵥ (M *ᵥ u) = ∑ p, ∑ q, star (u p) * M p q * u q`. A bookkeeping helper for the
partial-trace `PosSemidef` proofs. -/
private theorem star_dotProduct_mulVec_eq_sum {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (u : ι → ℂ) :
    star u ⬝ᵥ (M *ᵥ u) = ∑ p, ∑ q, star (u p) * M p q * u q := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

omit [DecidableEq n] in
/-- **`PosSemidef` preservation:** `M.PosSemidef → (Tr_B M).PosSemidef`.

The quadratic form on the reduced operator unfolds, for any `v : n → ℂ`, into a sum over the
traced-out index `k` of the quadratic form of `M` on the tensor witnesses
`wₖ : n × m → ℂ`, `wₖ (i, k') = if k' = k then v i else 0` (i.e. `v ⊗ eₖ`):

  `star v ⬝ᵥ (Tr_B M) *ᵥ v = ∑ₖ star (wₖ) ⬝ᵥ M *ᵥ (wₖ) ≥ 0`,

each summand `≥ 0` by `M.PosSemidef`. -/
theorem partialTraceRight_posSemidef {M : Matrix (n × m) (n × m) ℂ} (hM : M.PosSemidef) :
    (partialTraceRight M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (partialTraceRight_isHermitian hM.1) fun v => ?_
  -- witness vectors wₖ : n × m → ℂ, wₖ (i, k') = if k' = k then v i else 0
  set w : m → (n × m → ℂ) := fun k => fun p => if p.2 = k then v p.1 else 0 with hw
  -- each witness quadratic form collapses to ∑ i, ∑ j, star (v i) * M (i,k) (j,k) * v j.
  have hwk : ∀ k : m, star (w k) ⬝ᵥ (M *ᵥ (w k))
      = ∑ i : n, ∑ j : n, star (v i) * M (i, k) (j, k) * v j := by
    intro k
    rw [star_dotProduct_mulVec_eq_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- collapse the inner k'-component (p = (i, k')): witness support is k' = k.
    rw [Finset.sum_eq_single k]
    · -- now the q-sum, with q = (j, l), witness support l = k.
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single k]
      · simp only [hw, if_pos rfl]
      · intro l _ hl; simp only [hw, if_neg hl, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    · intro k' _ hk'
      simp only [hw, if_neg hk', star_zero, zero_mul, Finset.sum_const_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  -- the reduced quadratic form is the sum over k of those (Fubini in the traced index).
  have key : star v ⬝ᵥ (partialTraceRight M *ᵥ v) = ∑ k : m, star (w k) ⬝ᵥ (M *ᵥ (w k)) := by
    rw [star_dotProduct_mulVec_eq_sum]
    simp_rw [hwk]
    -- LHS: ∑ i, ∑ j, star (v i) * (∑ k, M (i,k) (j,k)) * v j
    -- RHS: ∑ k, ∑ i, ∑ j, star (v i) * M (i,k) (j,k) * v j
    rw [Finset.sum_comm (γ := m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := m)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [partialTraceRight_apply, Finset.mul_sum, Finset.sum_mul, mul_right_comm]
  rw [key]
  exact Finset.sum_nonneg fun k _ => hM.dotProduct_mulVec_nonneg (w k)

omit [DecidableEq m] in
/-- **`PosSemidef` preservation:** `M.PosSemidef → (Tr_A M).PosSemidef`. Witnesses
`wᵢ : n × m → ℂ`, `wᵢ (i', k) = if i' = i then v k else 0` (i.e. `eᵢ ⊗ v`). -/
theorem partialTraceLeft_posSemidef {M : Matrix (n × m) (n × m) ℂ} (hM : M.PosSemidef) :
    (partialTraceLeft M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (partialTraceLeft_isHermitian hM.1) fun v => ?_
  set w : n → (n × m → ℂ) := fun i => fun p => if p.1 = i then v p.2 else 0 with hw
  have hwi : ∀ i : n, star (w i) ⬝ᵥ (M *ᵥ (w i))
      = ∑ k : m, ∑ l : m, star (v k) * M (i, k) (i, l) * v l := by
    intro i
    rw [star_dotProduct_mulVec_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- collapse the i'-component (p = (i', k)): witness support is i' = i.
    rw [Finset.sum_eq_single i]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single i]
      · simp only [hw, if_pos rfl]
      · intro i' _ hi'; simp only [hw, if_neg hi', mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · intro i' _ hi'
      simp only [hw, if_neg hi', star_zero, zero_mul, Finset.sum_const_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have key : star v ⬝ᵥ (partialTraceLeft M *ᵥ v) = ∑ i : n, star (w i) ⬝ᵥ (M *ᵥ (w i)) := by
    rw [star_dotProduct_mulVec_eq_sum]
    simp_rw [hwi]
    -- LHS: ∑ k, ∑ l, star (v k) * (∑ i, M (i,k) (i,l)) * v l
    -- RHS: ∑ i, ∑ k, ∑ l, star (v k) * M (i,k) (i,l) * v l
    rw [Finset.sum_comm (γ := n)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm (γ := n)]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [partialTraceLeft_apply, Finset.mul_sum, Finset.sum_mul, mul_right_comm]
  rw [key]
  exact Finset.sum_nonneg fun i _ => hM.dotProduct_mulVec_nonneg (w i)

/-! ## Density ↦ density -/

omit [DecidableEq n] in
/-- **The reduced state of a density operator is a density operator** (right factor).
From PSD preservation + trace preservation: if `M` is PSD with unit trace then so is
`Tr_B M`. -/
theorem partialTraceRight_density {M : Matrix (n × m) (n × m) ℂ} (hM : M.PosSemidef)
    (htr : M.trace = 1) :
    (partialTraceRight M).PosSemidef ∧ (partialTraceRight M).trace = 1 :=
  ⟨partialTraceRight_posSemidef hM, by rw [partialTraceRight_trace, htr]⟩

omit [DecidableEq m] in
/-- **The reduced state of a density operator is a density operator** (left factor). -/
theorem partialTraceLeft_density {M : Matrix (n × m) (n × m) ℂ} (hM : M.PosSemidef)
    (htr : M.trace = 1) :
    (partialTraceLeft M).PosSemidef ∧ (partialTraceLeft M).trace = 1 :=
  ⟨partialTraceLeft_posSemidef hM, by rw [partialTraceLeft_trace, htr]⟩

end QuantumInfo
