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
* `Matrix.inv_shift_loewner_convex` / `Matrix.operatorConcaveOn_neg_add_inv` : the shifted
  resolvent `x ↦ (x + s)⁻¹` is operator convex, equivalently `x ↦ -(x + s)⁻¹` is operator concave,
  for each `s > 0` (the L.2 per-shift building block; the negation of L.1 translated by `s`).
* `Matrix.OperatorConcaveOn.affine_output` : the increasing-affine output transform
  `f ↦ (fun x => c * f x + d)` with `c ≥ 0` preserves operator concavity (the Step-C algebra in
  the `log` route, `c = p⁻¹`, `d = -p⁻¹`, lifting `x^p` concavity to `p⁻¹(x^p − 1)` concavity).

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

/-! ### Shifted-inverse rungs (the resolvent family `x ↦ (x + s)⁻¹`)

These are the building blocks of the integral-representation route to operator concavity of
`log` and `x ↦ x^p`: each resolvent `x ↦ -(x + s)⁻¹` is operator concave (a translate + negate
of L.1's `inv_loewner_convex`), and the target functions are positive integral mixtures of these.
They are proved here directly in the matrix / Löwner / CFC setting, with no new axiom. -/

omit [Fintype n] in
/-- For positive-definite `A` and `s > 0`, the shifted matrix `A + s • 1` is positive definite. -/
theorem add_smul_one_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {s : ℝ} (hs : 0 < s) :
    (A + (s : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
  have hsc : (0 : ℂ) < (s : ℂ) := by exact_mod_cast hs
  have hdiag : (s : ℂ) • (1 : Matrix n n ℂ) = diagonal (fun _ : n => (s : ℂ)) := by
    rw [Matrix.smul_one_eq_diagonal]
  have h1 : ((s : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
    rw [hdiag, Matrix.posDef_diagonal_iff]
    intro i; exact hsc
  simpa [add_comm] using h1.add_posSemidef hA.posSemidef

/-- The real spectrum of a positive-definite matrix shifted by `s ≥ 0` is bounded below by `s`,
hence `x + s ≠ 0` whenever `x` is in the spectrum and `s > 0` (or `x > 0`). -/
theorem posDef_add_pos {A : Matrix n n ℂ} (hA : A.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x ∈ spectrum ℝ A, 0 < x + s :=
  fun x hx => by have := posDef_spectrum_pos hA x hx; linarith

/-- **CFC ↔ shifted matrix inverse bridge.** For positive-definite `A` and `s > 0`, the continuous
functional calculus of `x ↦ (x + s)⁻¹` agrees with the matrix inverse of the shift:
`cfc (fun x => (x + s)⁻¹) A = (A + s • 1)⁻¹`. -/
theorem cfc_add_inv_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {s : ℝ} (hs : 0 < s) :
    cfc (fun x : ℝ => (x + s)⁻¹) A = (A + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹ := by
  have hsa : IsSelfAdjoint A := hA.1
  have hshift : (A + (s : ℂ) • (1 : Matrix n n ℂ)).PosDef := add_smul_one_posDef hA hs
  have hspec := posDef_add_pos hA hs.le
  -- `cfc (·+s) A = A + s • 1`
  have hcfc_shift : cfc (fun x : ℝ => x + s) A = A + (s : ℂ) • (1 : Matrix n n ℂ) := by
    rw [cfc_add (a := A) (fun x : ℝ => x) (fun _ : ℝ => s) (by fun_prop) (by fun_prop),
      cfc_id' ℝ A, cfc_const s A, Algebra.algebraMap_eq_smul_one]
    congr 1
  -- continuity of the resolvent on the spectrum
  have hres_cont : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ (by fun_prop) (fun x hx => (hspec x hx).ne')
  -- the product of the two CFCs is the identity, so the first is the inverse of the second
  have hli : cfc (fun x : ℝ => (x + s)⁻¹) A * (A + (s : ℂ) • (1 : Matrix n n ℂ)) = 1 := by
    rw [← hcfc_shift,
      ← cfc_mul _ _ A (hf := hres_cont) (hg := by fun_prop), ← cfc_one (R := ℝ) A]
    apply cfc_congr
    intro x hx
    exact inv_mul_cancel₀ (hspec x hx).ne'
  exact (inv_eq_left_inv hli).symm

/-- **Operator convexity of the resolvent `x ↦ (x + s)⁻¹` (Löwner form).** For positive-definite
`A, B`, `t ∈ [0,1]` and `s > 0`,
`(t • A + (1 - t) • B + s • 1)⁻¹ ≤ t • (A + s • 1)⁻¹ + (1 - t) • (B + s • 1)⁻¹`.
This is `inv_loewner_convex` applied to the PD shifts `A + s • 1`, `B + s • 1`, using that the
convex combination of the shifts is the shift of the convex combination (since `t + (1-t) = 1`). -/
theorem inv_shift_loewner_convex {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℝ} (hs : 0 < s) :
    ((t : ℂ) • A + ((1 : ℂ) - t) • B + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹
      ≤ (t : ℂ) • (A + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹
        + ((1 : ℂ) - t) • (B + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹ := by
  have hAs := add_smul_one_posDef hA hs
  have hBs := add_smul_one_posDef hB hs
  have key := inv_loewner_convex hAs hBs ht0 ht1
  -- the convex combination of the shifts is the shift of the convex combination
  have hcomb : (t : ℂ) • (A + (s : ℂ) • (1 : Matrix n n ℂ))
        + ((1 : ℂ) - t) • (B + (s : ℂ) • (1 : Matrix n n ℂ))
      = (t : ℂ) • A + ((1 : ℂ) - t) • B + (s : ℂ) • (1 : Matrix n n ℂ) := by
    module
  rwa [hcomb] at key

/-! ### Predicate-form resolvent concavity -/

/-- The CFC of the negated resolvent `x ↦ -(x + s)⁻¹` on a positive-definite matrix is
`-(A + s • 1)⁻¹`. -/
theorem cfc_neg_add_inv_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {s : ℝ} (hs : 0 < s) :
    cfc (fun x : ℝ => -(x + s)⁻¹) A = -(A + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹ := by
  have hres_cont : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ (by fun_prop) (fun x hx => (posDef_add_pos hA hs.le x hx).ne')
  rw [show (fun x : ℝ => -(x + s)⁻¹) = (fun x : ℝ => -(x + s)⁻¹) from rfl,
    cfc_neg (fun x : ℝ => (x + s)⁻¹) A, cfc_add_inv_posDef hA hs]

/-- **Operator concavity of the negated resolvent.** For each `s > 0`, the function
`x ↦ -(x + s)⁻¹` is operator concave on `(0, ∞)`. This is the per-shift building block of the
integral-representation route to operator concavity of `log` and `x ↦ x^p`: each negated
resolvent is operator concave, and those target functions are positive integral mixtures of
these resolvents. Proof: the negation of `inv_shift_loewner_convex`. -/
theorem operatorConcaveOn_neg_add_inv {s : ℝ} (hs : 0 < s) :
    OperatorConcaveOn (Set.Ioi 0) (fun x : ℝ => -(x + s)⁻¹) := by
  intro n _ _ A B hA hB hAspec hBspec t ht0 ht1 hCspec
  have hApd : A.PosDef := posDef_of_spectrum_pos hA (fun x hx => hAspec hx)
  have hBpd : B.PosDef := posDef_of_spectrum_pos hB (fun x hx => hBspec hx)
  have hCpd : ((t : ℂ) • A + ((1 : ℂ) - t) • B).PosDef := convexComb_posDef hApd hBpd ht0 ht1
  rw [cfc_neg_add_inv_posDef hApd hs, cfc_neg_add_inv_posDef hBpd hs,
    cfc_neg_add_inv_posDef hCpd hs]
  -- goal: t • (-(A+s)⁻¹) + (1-t) • (-(B+s)⁻¹) ≤ -((tA+(1-t)B)+s)⁻¹
  have key := inv_shift_loewner_convex hApd hBpd ht0 ht1 hs
  -- rearrange to the negated form via the Löwner order's `neg_le_neg`
  rw [smul_neg, smul_neg, ← neg_add]
  rw [show -((t : ℂ) • A + ((1 : ℂ) - t) • B + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹
        = -(((t : ℂ) • A + ((1 : ℂ) - t) • B) + (s : ℂ) • (1 : Matrix n n ℂ))⁻¹ from rfl]
  exact neg_le_neg key

/-! ### Affine output transform preserves operator concavity

The map `f ↦ (fun x => c * f x + d)` with `c ≥ 0` is the increasing-affine transform of the
*output*; it preserves operator concavity. This is the algebraic step needed to pass from
`x ↦ x ^ p` operator concave to `x ↦ p⁻¹ (x ^ p − 1)` operator concave (Step C of the log route:
`c = p⁻¹ > 0`, `d = -p⁻¹`). -/

/-- CFC of an increasing-affine output transform: for Hermitian `A` and `f` continuous on the
spectrum, `cfc (fun x => c * f x + d) A = c • cfc f A + d • 1`. -/
theorem cfc_affine_output {A : Matrix n n ℂ} (hA : A.IsHermitian) {c d : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc (fun x : ℝ => c * f x + d) A = (c : ℂ) • cfc f A + (d : ℂ) • (1 : Matrix n n ℂ) := by
  have hsa : IsSelfAdjoint A := hA
  rw [cfc_add (a := A) (fun x : ℝ => c * f x) (fun _ : ℝ => d) (by fun_prop) (by fun_prop),
    cfc_const d A, cfc_const_mul (a := A) c f hf, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]
  congr 1

/-- **Affine output transform preserves operator concavity.** If `f` is operator concave on `s`
and `c ≥ 0`, then `x ↦ c * f x + d` is operator concave on `s`, *provided* `f` is continuous on
each relevant spectrum (`hcont`), which is needed for the CFC of the transform to split. This is
the algebraic step in the `log` route: with `c = p⁻¹ ≥ 0`, `d = -p⁻¹`, it lifts operator concavity
of `x ↦ x^p` to operator concavity of `x ↦ p⁻¹ (x^p − 1)`. -/
theorem OperatorConcaveOn.affine_output {s : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConcaveOn s f)
    {c d : ℝ} (hc : 0 ≤ c)
    (hcont : ∀ {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m ℂ},
      M.IsHermitian → ContinuousOn f (spectrum ℝ M)) :
    OperatorConcaveOn s (fun x : ℝ => c * f x + d) := by
  intro n _ _ A B hA hB hAspec hBspec t ht0 ht1 hCspec
  have hsaT : IsSelfAdjoint (t : ℂ) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  have hsa1T : IsSelfAdjoint ((1 : ℂ) - t) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.one (R := ℂ)) hsaT
  have hcombHerm : ((t : ℂ) • A + ((1 : ℂ) - t) • B).IsHermitian :=
    (hA.smul hsaT).add (hB.smul hsa1T)
  -- split the CFC of the transform on all three arguments
  have hcA := cfc_affine_output (A := A) hA (c := c) (d := d) (hcont hA)
  have hcB := cfc_affine_output (A := B) hB (c := c) (d := d) (hcont hB)
  have hcC := cfc_affine_output (A := (t : ℂ) • A + ((1 : ℂ) - t) • B) hcombHerm
    (c := c) (d := d) (hcont hcombHerm)
  rw [hcA, hcB, hcC]
  -- the underlying concavity inequality
  have key := hf hA hB hAspec hBspec ht0 ht1 hCspec
  have hcc : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc
  -- LHS: t • (c • cfc f A + d • 1) + (1-t) • (c • cfc f B + d • 1)
  --    = c • (t • cfc f A + (1-t) • cfc f B) + d • 1
  -- RHS: c • cfc f (comb) + d • 1
  have hsmul : (c : ℂ) • ((t : ℂ) • cfc f A + ((1 : ℂ) - t) • cfc f B)
      ≤ (c : ℂ) • cfc f ((t : ℂ) • A + ((1 : ℂ) - t) • B) :=
    smul_le_smul_of_nonneg_left key hcc
  calc (t : ℂ) • ((c : ℂ) • cfc f A + (d : ℂ) • (1 : Matrix n n ℂ))
        + ((1 : ℂ) - t) • ((c : ℂ) • cfc f B + (d : ℂ) • (1 : Matrix n n ℂ))
      = (c : ℂ) • ((t : ℂ) • cfc f A + ((1 : ℂ) - t) • cfc f B)
        + (d : ℂ) • (1 : Matrix n n ℂ) := by module
    _ ≤ (c : ℂ) • cfc f ((t : ℂ) • A + ((1 : ℂ) - t) • B) + (d : ℂ) • (1 : Matrix n n ℂ) := by
        gcongr

