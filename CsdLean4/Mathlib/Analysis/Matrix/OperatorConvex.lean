import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block

/-!
# Operator convexity / concavity for matrix functions (foundational rungs)

This file develops the first rungs of the operator-convexity ladder over Hermitian /
positive-definite complex matrices, using the **Löwner order** (`Matrix.instPartialOrder`,
scoped `MatrixOrder`: `A ≤ B := (B - A).PosSemidef`) and the continuous functional calculus
`cfc`.

## Main definitions

* `Matrix.OperatorConvexOn s f` / `Matrix.OperatorConcaveOn s f` : a real function `f` is
  operator convex (resp. concave) on `s ⊆ ℝ` if, for *every* finite index type `n` and all
  Hermitian `A, B : Matrix n n ℂ` whose spectra (and the spectrum of their convex combination)
  lie in `s`, the CFC satisfies
  `cfc f (t • A + (1 - t) • B) ≤ t • cfc f A + (1 - t) • cfc f B`  (resp. `≥`)
  for `t ∈ [0,1]`. Operator convexity is genuinely an **all-dimensions** notion, so the
  predicate quantifies over `n`.

## Main results

* `Matrix.inv_loewner_convex` : the Löwner inverse inequality for positive-definite matrices,
  `(t A + (1-t) B)⁻¹ ≤ t A⁻¹ + (1-t) B⁻¹`, proved via the Schur-complement PSD characterisation
  `Matrix.PosDef.fromBlocks₁₁`.
* `Matrix.cfc_inv_posDef` : `cfc (·⁻¹) A = A⁻¹` for positive-definite `A` (CFC ↔ matrix inverse
  bridge).
* `Matrix.operatorConvexOn_inv` : `x ↦ x⁻¹` is operator convex on `(0, ∞)` (the predicate form,
  the foundational rung L.1 of the ladder).

## Implementation notes

The convex combination is taken with **complex scalars** `(t : ℂ)` rather than real scalars:
the `Matrix.PosSemidef.smul` API requires `0 ≤ (a : ℂ)` (a `ComplexOrder` nonnegativity), and
`Complex.coe_smul` bridges `(t : ℂ) • A = (t : ℝ) • A`. This is the natural setting for matrices
over `ℂ` and does not weaken the statement.

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib upstream candidate). Natural Mathlib
namespace `Matrix`.

## Provenance

Foundational rungs (L.0 predicate + L.1 inverse) of the operator-convexity ladder whose summit is
the data-processing inequality `hDPI` of
`CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity.strong_subadditivity_of_relEntropy_monotone`
(K1-C). The ladder L.1 → L.5 is recorded in `specs/operator-convexity-plan.md`.

## Tags

operator convex, operator monotone, Löwner order, Schur complement, functional calculus
-/

open scoped MatrixOrder ComplexOrder
open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The operator-convexity predicate (L.0) -/

/-- `OperatorConvexOn s f` : the real function `f` is **operator convex** on `s ⊆ ℝ`.

For every finite index type `n` and all Hermitian `A B : Matrix n n ℂ` with spectra
(and the spectrum of `t A + (1-t) B`) contained in `s`, and every `t ∈ [0,1]`, the continuous
functional calculus satisfies the Löwner inequality
`cfc f (t • A + (1 - t) • B) ≤ t • cfc f A + (1 - t) • cfc f B`.

The quantification is over **all dimensions** `n`: operator convexity is strictly stronger than
ordinary (scalar) convexity and is a genuinely dimension-uniform notion. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ},
    A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      spectrum ℝ ((t : ℂ) • A + ((1 : ℂ) - t) • B) ⊆ s →
      cfc f ((t : ℂ) • A + ((1 : ℂ) - t) • B)
        ≤ (t : ℂ) • cfc f A + ((1 : ℂ) - t) • cfc f B

/-- `OperatorConcaveOn s f` : the real function `f` is **operator concave** on `s ⊆ ℝ`, i.e. `-f`
is operator convex. Equivalently, the reversed Löwner inequality holds. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ},
    A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      spectrum ℝ ((t : ℂ) • A + ((1 : ℂ) - t) • B) ⊆ s →
      (t : ℂ) • cfc f A + ((1 : ℂ) - t) • cfc f B
        ≤ cfc f ((t : ℂ) • A + ((1 : ℂ) - t) • B)

/-! ### L.1 : operator convexity of `x ↦ x⁻¹` -/

/-- For a positive-definite `A`, the block matrix `⟦A, 1; 1, A⁻¹⟧` is positive semidefinite.
This is the Schur-complement witness of operator convexity of the inverse: the Schur complement of
the `A`-block is `A⁻¹ - 1·A⁻¹·1 = 0 ≥ 0`. -/
theorem fromBlocks_inv_posSemidef {A : Matrix n n ℂ} (hA : A.PosDef) :
    (fromBlocks A 1 1 A⁻¹).PosSemidef := by
  letI : Invertible A := hA.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℂ) A⁻¹ hA
  rw [show (1 : Matrix n n ℂ)ᴴ = 1 from Matrix.conjTranspose_one] at h
  rw [h]; simpa using PosSemidef.zero

omit [Fintype n] [DecidableEq n] in
/-- A convex combination (complex weights `t, 1-t ∈ [0,1]`) of positive-definite matrices is
positive definite. -/
theorem convexComb_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t : ℂ) • A + ((1 : ℂ) - t) • B).PosDef := by
  have hc1 : (0 : ℂ) ≤ ((1 : ℂ) - t) := by
    have h := (by linarith : (0 : ℝ) ≤ 1 - t)
    have he : ((1 : ℂ) - t) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [he]; exact_mod_cast h
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h
    simp only [Complex.ofReal_zero, zero_smul, zero_add, sub_zero, one_smul]
    exact hB
  · have hcpos : (0 : ℂ) < (t : ℂ) := by exact_mod_cast h
    exact (hA.smul hcpos).add_posSemidef (hB.posSemidef.smul hc1)

/-- **Operator convexity of the matrix inverse (Löwner form).** For positive-definite `A, B` and
`t ∈ [0,1]`,
`(t • A + (1 - t) • B)⁻¹ ≤ t • A⁻¹ + (1 - t) • B⁻¹`
in the Löwner order. Proof: convexity of the PSD cone applied to the Schur-complement block
witnesses `⟦A,1;1,A⁻¹⟧`, then the backward Schur characterisation `Matrix.PosDef.fromBlocks₁₁`. -/
theorem inv_loewner_convex {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t : ℂ) • A + ((1 : ℂ) - t) • B)⁻¹ ≤ (t : ℂ) • A⁻¹ + ((1 : ℂ) - t) • B⁻¹ := by
  have hc0 : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht0
  have hc1 : (0 : ℂ) ≤ ((1 : ℂ) - t) := by
    have h := (by linarith : (0 : ℝ) ≤ 1 - t)
    have he : ((1 : ℂ) - t) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [he]; exact_mod_cast h
  have hCpd : ((t : ℂ) • A + ((1 : ℂ) - t) • B).PosDef := convexComb_posDef hA hB ht0 ht1
  letI : Invertible ((t : ℂ) • A + ((1 : ℂ) - t) • B) := hCpd.isUnit.invertible
  -- convex combination of the two block PSD witnesses
  have hPSD : ((t : ℂ) • fromBlocks A 1 1 A⁻¹ + ((1 : ℂ) - t) • fromBlocks B 1 1 B⁻¹).PosSemidef :=
    ((fromBlocks_inv_posSemidef hA).smul hc0).add ((fromBlocks_inv_posSemidef hB).smul hc1)
  -- it equals a single block matrix with Schur complement the RHS minus the LHS
  have hblock : (t : ℂ) • fromBlocks A 1 1 A⁻¹ + ((1 : ℂ) - t) • fromBlocks B 1 1 B⁻¹
      = fromBlocks ((t : ℂ) • A + ((1 : ℂ) - t) • B) 1 1
          ((t : ℂ) • A⁻¹ + ((1 : ℂ) - t) • B⁻¹) := by
    rw [fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    congr 1 <;> module
  rw [hblock] at hPSD
  have hs := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℂ)
    ((t : ℂ) • A⁻¹ + ((1 : ℂ) - t) • B⁻¹) hCpd
  rw [show (1 : Matrix n n ℂ)ᴴ = 1 from Matrix.conjTranspose_one] at hs
  rw [hs] at hPSD
  rw [Matrix.le_iff]
  simpa using hPSD

/-! ### CFC ↔ matrix-inverse bridge -/

/-- The real spectrum of a positive-definite matrix is positive. -/
theorem posDef_spectrum_pos {A : Matrix n n ℂ} (hA : A.PosDef) :
    ∀ x ∈ spectrum ℝ A, 0 < x := by
  intro x hx
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_pos i

/-- For positive-definite `A`, the continuous functional calculus of `x ↦ x⁻¹` agrees with the
matrix (nonsingular) inverse: `cfc (·⁻¹) A = A⁻¹`. -/
theorem cfc_inv_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    cfc (fun x : ℝ => x⁻¹) A = A⁻¹ := by
  have hsa : IsSelfAdjoint A := hA.1
  have hspec := posDef_spectrum_pos hA
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ continuousOn_id (fun x hx => (hspec x hx).ne')
  have hli : cfc (fun x : ℝ => x⁻¹) A * A = 1 := by
    nth_rewrite 2 [← cfc_id ℝ A]
    rw [← cfc_mul _ _ A, ← cfc_one (R := ℝ) A]
    apply cfc_congr
    intro x hx
    simp only [id_eq]
    exact inv_mul_cancel₀ (hspec x hx).ne'
  exact (inv_eq_left_inv hli).symm

/-- A Hermitian matrix whose real spectrum is positive is positive definite. -/
theorem posDef_of_spectrum_pos {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hspec : ∀ x ∈ spectrum ℝ A, 0 < x) : A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro i
  apply hspec
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact ⟨i, rfl⟩

/-! ### L.1, predicate form -/

/-- **L.1 of the ladder.** The function `x ↦ x⁻¹` is operator convex on `(0, ∞)`.

This is the predicate-form repackaging of `inv_loewner_convex` via the CFC ↔ matrix-inverse
bridge `cfc_inv_posDef`: a Hermitian matrix with spectrum in `(0, ∞)` is positive definite. -/
theorem operatorConvexOn_inv : OperatorConvexOn (Set.Ioi 0) (fun x : ℝ => x⁻¹) := by
  intro n _ _ A B hA hB hAspec hBspec t ht0 ht1 hCspec
  -- spectra in (0,∞) ⇒ positive definite
  have hApd : A.PosDef := posDef_of_spectrum_pos hA (fun x hx => hAspec hx)
  have hBpd : B.PosDef := posDef_of_spectrum_pos hB (fun x hx => hBspec hx)
  have hCpd : ((t : ℂ) • A + ((1 : ℂ) - t) • B).PosDef := convexComb_posDef hApd hBpd ht0 ht1
  -- rewrite the CFC of `·⁻¹` to the matrix inverse on each PD argument
  rw [cfc_inv_posDef hCpd, cfc_inv_posDef hApd, cfc_inv_posDef hBpd]
  exact inv_loewner_convex hApd hBpd ht0 ht1
