/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Register

/-!
# The two-factor joint register: tensor states, partial operators, and the Born marginal

**Category:** 1-Mathlib (CSD-free).

The product-index register `EuclideanSpace ℂ (ι₁ × ι₂)` over arbitrary finite factors, with the
four pieces every two-register algorithm argument consumes:

* **`tensorState φ ψ`** — the product state, coordinate `φ c * ψ y`, with bilinearity
  (`tensorState_smul_left/right`, `tensorState_sum_left/right`, two-sided `tensorState_smul_smul`)
  and `|c⟩ ⊗ |y⟩ = |(c,y)⟩` (`tensorState_basis`); nonvanishing on nonzero factors
  (`tensorState_ne_zero`) and jointly continuous (`tensorState_continuous`), the two facts a
  projective (Segre) argument needs.
* **`matrixLeft M Φ`** — a matrix kernel acting on the **first factor only** (the shape of "the
  inverse QFT on the counting register"), linear (`matrixLeft_smul`/`matrixLeft_sum`), with the
  key reduction ★ `matrixLeft_tensorState`: on a product state it acts on the first factor and
  leaves the second alone.
* **`sliceLeft Φ c`** — the second-register slice at first-register outcome `c`, the vector
  whose norm² is the marginal weight.
* **`probLeft Φ c`** — the **Born marginal on the first register**, `∑_y ‖Φ (c, y)‖²`; on a
  product state it is the product law (`probLeft_tensorState`), and — the load-bearing fact —
  ★★ `probLeft_sum_tensor_orthogonal`: for a sum of product states whose second factors are
  **pairwise orthogonal**, the marginal is the **mixture** of the branch marginals, with every
  cross-term dead. This is the lemma that turns a multi-branch kickback state into a classical
  mixture of single-phase distributions.

Extracted 2026-08-29 (plan `specs/amplitude-amplification-plan.md`, AA-5b step 1) from the
`Fin T × ZMod N`-typed originals in `Empirical/QM/Algorithms/ShorCore.lean` (`tensorCN`,
`qftInvCount`, `probCount`), which are now the instances; the second consumer is the amplitude
-estimation kickback marginal (AA-5b), whose two branches have orthogonal eigenvector
companions. The mixture lemma is new here — Shor's file never needed the general form, and the
`8/π²` assembly does.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-! ## The tensor state -/

/-- The **tensor product** of two register states, as a vector on the product index:
coordinate `(tensorState φ ψ) (c, y) = φ c * ψ y`. -/
noncomputable def tensorState (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) :
    EuclideanSpace ℂ (ι₁ × ι₂) :=
  (WithLp.equiv 2 (ι₁ × ι₂ → ℂ)).symm (fun p => φ p.1 * ψ p.2)

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
@[simp] lemma tensorState_apply (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂)
    (c : ι₁) (y : ι₂) : tensorState φ ψ (c, y) = φ c * ψ y := rfl

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The tensor is linear in the first factor. -/
lemma tensorState_smul_left (k : ℂ) (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) :
    tensorState (k • φ) ψ = k • tensorState φ ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, tensorState_apply, tensorState_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The tensor commutes with finite sums in the first factor. -/
lemma tensorState_sum_left {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ ι₁)
    (ψ : EuclideanSpace ℂ ι₂) :
    tensorState (∑ k ∈ s, f k) ψ = ∑ k ∈ s, tensorState (f k) ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [tensorState_apply, sum_coord, sum_coord, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [tensorState_apply]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The tensor is linear in the second factor. -/
lemma tensorState_smul_right (k : ℂ) (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) :
    tensorState φ (k • ψ) = k • tensorState φ ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, tensorState_apply, tensorState_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The tensor commutes with finite sums in the second factor. -/
lemma tensorState_sum_right {κ : Type*} (φ : EuclideanSpace ℂ ι₁) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι₂) :
    tensorState φ (∑ k ∈ s, f k) = ∑ k ∈ s, tensorState φ (f k) := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [tensorState_apply, sum_coord, sum_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [tensorState_apply]

omit [Fintype ι₁] [Fintype ι₂] in
/-- On basis states the tensor is the joint basis state: `|c⟩ ⊗ |y⟩ = |(c, y)⟩`. -/
@[simp] lemma tensorState_basis (c : ι₁) (y : ι₂) :
    tensorState (basisState c) (basisState y) = basisState ((c, y) : ι₁ × ι₂) := by
  ext p
  obtain ⟨c', y'⟩ := p
  rw [tensorState_apply, basisState_apply, basisState_apply, basisState_apply]
  by_cases hc : c' = c <;> by_cases hy : y' = y <;>
    simp [hc, hy, Prod.ext_iff]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The tensor is additive in the second factor. -/
lemma tensorState_add_right (φ : EuclideanSpace ℂ ι₁) (ψ χ : EuclideanSpace ℂ ι₂) :
    tensorState φ (ψ + χ) = tensorState φ ψ + tensorState φ χ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_add, Pi.add_apply, tensorState_apply, tensorState_apply, tensorState_apply,
    WithLp.ofLp_add, Pi.add_apply]
  ring

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The two-sided homogeneity law: scaling both factors scales the product by the product of the
scalars. The form a projective (ray) argument consumes. -/
lemma tensorState_smul_smul (a b : ℂ) (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) :
    tensorState (a • φ) (b • ψ) = (a * b) • tensorState φ ψ := by
  rw [tensorState_smul_left, tensorState_smul_right, smul_smul]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **A product of nonzero factors is nonzero**: the coordinates of the tensor state are the
products of the coordinates, and `ℂ` has no zero divisors. -/
lemma tensorState_ne_zero {φ : EuclideanSpace ℂ ι₁} {ψ : EuclideanSpace ℂ ι₂}
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) : tensorState φ ψ ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, φ c ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (by apply PiLp.ext; intro c; simpa using h c)
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (by apply PiLp.ext; intro y; simpa using h y)
  intro h0
  have := congrArg (fun w : EuclideanSpace ℂ (ι₁ × ι₂) => w (c, y)) h0
  simp only [tensorState_apply] at this
  exact mul_ne_zero hc hy (by simpa using this)

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **The product map is jointly continuous.** Coordinatewise it is a product of two coordinate
evaluations, and the `PiLp` topology is the product topology. -/
lemma tensorState_continuous :
    Continuous fun p : EuclideanSpace ℂ ι₁ × EuclideanSpace ℂ ι₂ => tensorState p.1 p.2 := by
  show Continuous fun p : EuclideanSpace ℂ ι₁ × EuclideanSpace ℂ ι₂ =>
    (WithLp.toLp 2 (fun q : ι₁ × ι₂ => p.1 q.1 * p.2 q.2) : EuclideanSpace ℂ (ι₁ × ι₂))
  refine (PiLp.continuous_toLp _ _).comp ?_
  refine continuous_pi fun q => ?_
  exact ((continuous_apply q.1).comp ((PiLp.continuous_ofLp _ _).comp continuous_fst)).mul
    ((continuous_apply q.2).comp ((PiLp.continuous_ofLp _ _).comp continuous_snd))

/-! ## A matrix kernel on the first factor -/

/-- A matrix kernel acting on the **first factor only**: coordinate
`(matrixLeft M Φ) (c, y) = ∑_x M c x · Φ (x, y)`. This is the shape of "apply the inverse QFT
to the counting register of a joint state". -/
noncomputable def matrixLeft (M : Matrix ι₁ ι₁ ℂ) (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) :
    EuclideanSpace ℂ (ι₁ × ι₂) :=
  (WithLp.equiv 2 (ι₁ × ι₂ → ℂ)).symm (fun p => ∑ x, M p.1 x * Φ (x, p.2))

omit [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
@[simp] lemma matrixLeft_apply (M : Matrix ι₁ ι₁ ℂ) (Φ : EuclideanSpace ℂ (ι₁ × ι₂))
    (c : ι₁) (y : ι₂) : matrixLeft M Φ (c, y) = ∑ x, M c x * Φ (x, y) := rfl

omit [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
/-- The partial matrix action is homogeneous. -/
lemma matrixLeft_smul (M : Matrix ι₁ ι₁ ℂ) (k : ℂ) (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) :
    matrixLeft M (k • Φ) = k • matrixLeft M Φ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, matrixLeft_apply, matrixLeft_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
/-- The partial matrix action commutes with finite sums. -/
lemma matrixLeft_sum {κ : Type*} (M : Matrix ι₁ ι₁ ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ (ι₁ × ι₂)) :
    matrixLeft M (∑ k ∈ s, f k) = ∑ k ∈ s, matrixLeft M (f k) := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [matrixLeft_apply, sum_coord]
  simp_rw [sum_coord, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [matrixLeft_apply]

set_option linter.unusedSectionVars false in
/-- The coordinate of the Euclidean matrix action: `(M ψ) c = ∑_x M c x · ψ x`. -/
lemma toEuclideanLin_coord (M : Matrix ι₁ ι₁ ℂ) (φ : EuclideanSpace ℂ ι₁) (c : ι₁) :
    Matrix.toEuclideanLin M φ c = ∑ x, M c x * φ x := by
  rw [Matrix.toLpLin_apply]
  rfl

omit [Fintype ι₂] [DecidableEq ι₂] in
/-- ★ **Key reduction:** on a product state, a first-factor kernel acts on the first factor and
leaves the second alone: `matrixLeft M (φ ⊗ ψ) = (M φ) ⊗ ψ`. -/
lemma matrixLeft_tensorState (M : Matrix ι₁ ι₁ ℂ) (φ : EuclideanSpace ℂ ι₁)
    (ψ : EuclideanSpace ℂ ι₂) :
    matrixLeft M (tensorState φ ψ) = tensorState (Matrix.toEuclideanLin M φ) ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [matrixLeft_apply, tensorState_apply, toEuclideanLin_coord, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [tensorState_apply, mul_assoc]

omit [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
/-- The partial matrix action is additive. -/
lemma matrixLeft_add (M : Matrix ι₁ ι₁ ℂ) (Φ Ψ : EuclideanSpace ℂ (ι₁ × ι₂)) :
    matrixLeft M (Φ + Ψ) = matrixLeft M Φ + matrixLeft M Ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_add, Pi.add_apply, matrixLeft_apply, matrixLeft_apply, matrixLeft_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [WithLp.ofLp_add, Pi.add_apply]
  ring

/-! ## The second-register slice and the Born marginal on the first register -/

/-- The **second-register slice** of a joint state at first-register outcome `c`: the (not
normalized) vector `y ↦ Φ (c, y)` whose norm² is the marginal weight of `c`. -/
noncomputable def sliceLeft (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) (c : ι₁) :
    EuclideanSpace ℂ ι₂ :=
  (WithLp.equiv 2 (ι₂ → ℂ)).symm (fun y => Φ (c, y))

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
@[simp] lemma sliceLeft_apply (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) (c : ι₁) (y : ι₂) :
    sliceLeft Φ c y = Φ (c, y) := rfl

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- Slicing commutes with finite sums. -/
lemma sliceLeft_sum {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (ι₁ × ι₂))
    (c : ι₁) :
    sliceLeft (∑ k ∈ s, f k) c = ∑ k ∈ s, sliceLeft (f k) c := by
  ext y
  rw [sliceLeft_apply, sum_coord, sum_coord]
  exact Finset.sum_congr rfl fun k _ => by rw [sliceLeft_apply]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The slice of a product state is the scaled second factor. -/
lemma sliceLeft_tensorState (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) (c : ι₁) :
    sliceLeft (tensorState φ ψ) c = φ c • ψ := by
  ext y
  rw [sliceLeft_apply, tensorState_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- The **Born marginal on the first register**: `probLeft Φ c = ∑_y ‖Φ (c, y)‖²`. -/
noncomputable def probLeft (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) (c : ι₁) : ℝ :=
  ∑ y : ι₂, ‖Φ (c, y)‖ ^ 2

omit [Fintype ι₁] [DecidableEq ι₁] [DecidableEq ι₂] in
lemma probLeft_nonneg (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) (c : ι₁) : 0 ≤ probLeft Φ c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ι₁] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The marginal weight is the squared norm of the slice, as an inner product. -/
lemma probLeft_eq_inner (Φ : EuclideanSpace ℂ (ι₁ × ι₂)) (c : ι₁) :
    ((probLeft Φ c : ℝ) : ℂ) = inner ℂ (sliceLeft Φ c) (sliceLeft Φ c) := by
  rw [probLeft, PiLp.inner_apply]
  simp only [RCLike.inner_apply', RCLike.conj_mul, sliceLeft_apply]
  norm_cast

omit [Fintype ι₁] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **The product law:** the marginal of a product state is the first-factor Born weight scaled
by the second factor's norm². -/
lemma probLeft_tensorState (φ : EuclideanSpace ℂ ι₁) (ψ : EuclideanSpace ℂ ι₂) (c : ι₁) :
    probLeft (tensorState φ ψ) c = ‖φ c‖ ^ 2 * ∑ y, ‖ψ y‖ ^ 2 := by
  rw [probLeft, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [tensorState_apply, norm_mul, mul_pow]

omit [Fintype ι₁] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- ★★ **The orthogonal-branch mixture law.** For a sum of product states whose second factors
are **pairwise orthogonal**, the Born marginal on the first register is the **mixture** of the
branch marginals — every cross-term dies against the orthogonality. This is what turns a
multi-branch kickback state `∑_s φ_s ⊗ u_s` (orthogonal eigenvector companions `u_s`) into a
classical mixture of single-branch counting distributions. -/
theorem probLeft_sum_tensor_orthogonal {κ : Type*} (s : Finset κ)
    (φ : κ → EuclideanSpace ℂ ι₁) (u : κ → EuclideanSpace ℂ ι₂)
    (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → inner ℂ (u k) (u l) = 0) (c : ι₁) :
    probLeft (∑ k ∈ s, tensorState (φ k) (u k)) c
      = ∑ k ∈ s, ‖φ k c‖ ^ 2 * ∑ y, ‖u k y‖ ^ 2 := by
  have hself : ∀ k, (inner ℂ (u k) (u k) : ℂ) = ((∑ y, ‖u k y‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply', RCLike.conj_mul]
    norm_cast
  have hslice : sliceLeft (∑ k ∈ s, tensorState (φ k) (u k)) c
      = ∑ k ∈ s, φ k c • u k := by
    rw [sliceLeft_sum]
    exact Finset.sum_congr rfl fun k _ => sliceLeft_tensorState (φ k) (u k) c
  have hrow : ∀ k ∈ s, (inner ℂ (φ k c • u k) (∑ l ∈ s, φ l c • u l) : ℂ)
      = ((‖φ k c‖ ^ 2 * ∑ y, ‖u k y‖ ^ 2 : ℝ) : ℂ) := by
    intro k hk
    rw [inner_sum]
    rw [Finset.sum_eq_single k
      (fun l hl hlk => by
        rw [inner_smul_left, inner_smul_right, horth k hk l hl fun h => hlk h.symm,
          mul_zero, mul_zero])
      (fun hks => absurd hk hks)]
    rw [inner_smul_left, inner_smul_right, hself k, ← mul_assoc, RCLike.conj_mul]
    norm_cast
    exact (Complex.ofReal_mul _ _).symm
  have hC : ((probLeft (∑ k ∈ s, tensorState (φ k) (u k)) c : ℝ) : ℂ)
      = ((∑ k ∈ s, ‖φ k c‖ ^ 2 * ∑ y, ‖u k y‖ ^ 2 : ℝ) : ℂ) := by
    rw [probLeft_eq_inner, hslice, sum_inner, Finset.sum_congr rfl hrow]
    norm_cast
  exact_mod_cast hC

omit [Fintype ι₁] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- ★ **The two-branch mixture law:** for two product states with orthogonal second factors,
the first-register marginal is the sum of the branch marginals — the form the two-eigenvector
kickback state consumes. -/
theorem probLeft_add_tensor_orthogonal (φ₁ φ₂ : EuclideanSpace ℂ ι₁)
    (u₁ u₂ : EuclideanSpace ℂ ι₂) (h12 : inner ℂ u₁ u₂ = 0) (c : ι₁) :
    probLeft (tensorState φ₁ u₁ + tensorState φ₂ u₂) c
      = ‖φ₁ c‖ ^ 2 * ∑ y, ‖u₁ y‖ ^ 2 + ‖φ₂ c‖ ^ 2 * ∑ y, ‖u₂ y‖ ^ 2 := by
  have h21 : inner ℂ u₂ u₁ = 0 := by rw [← inner_conj_symm, h12, map_zero]
  have key := probLeft_sum_tensor_orthogonal (Finset.univ : Finset (Fin 2))
    ![φ₁, φ₂] ![u₁, u₂]
    (by
      intro k _ l _ hkl
      fin_cases k <;> fin_cases l <;> simp_all) c
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  exact key

end QuantumInfo
