/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.POVMDilation
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# LF4: the canonical Naimark dilation of a POVM exists (P.5)

**Category:** 3-Local (LF4 POVM existence layer).

This is **P.5** of the POVM tranche (`specs/povm-plan.md`): the construction that
inhabits `NaimarkDilation P` for **every** POVM, making the Phase-1 results
(`born_transfer`, `povm_born_eq_dilated_volume`, `povm_born_frequency_volume`)
unconditional — no longer conditional on a *supplied* dilation.

## The construction

The canonical Naimark isometry is `V ψ = ∑ᵢ (√Eᵢ ψ) ⊗ |i⟩`, i.e. the matrix
`V_{(n,i), m} = (√Eᵢ)_{n,m}`, where `√Eᵢ = cfc Real.sqrt Eᵢ` is the positive square
root via the continuous functional calculus on `Matrix n n ℂ` (the bespoke Hermitian
CFC instance — **P.5a is a library call**, `√Eᵢ √Eᵢ = Eᵢ` by `cfc_mul` + `√x·√x = x`
on the nonneg spectrum + `cfc_id`; no hand-built spectral construction). Then:

- **isometry** `Vᴴ V = ∑ᵢ √Eᵢ √Eᵢ = ∑ᵢ Eᵢ = I` (uses `povmSqrt_mul_self` and the
  POVM completeness `∑ Eᵢ = I`);
- **pullback** `Vᴴ Πᵢ V = √Eᵢ √Eᵢ = Eᵢ` (the ancilla-`i` projector compresses to `Eᵢ`).

Both reduce to the same inner column sum `∑ₙ conj(√Eᵢ)_{n,m} (√Eᵢ)_{n,m'} = (Eᵢ)_{m,m'}`
(`sqrt_inner_sum`), using that `√Eᵢ` is Hermitian.

## Honest scope

This removes the "supplied dilation" caveat: every POVM has a Naimark dilation, so
the ontic POVM Born = Kähler-volume reading holds for every POVM. What remains
posited is the *enlarged* sector structure on `Σ' = ℂℙ^{N·|ι|−1}` (the **SO-1** sector datum
on the dilated space — the ancilla is the apparatus/environment), and, beneath it,
the dynamics (**D1**). The dilation is still non-canonical as a *choice* (Naimark
dilations are non-unique); `canonicalNaimark` is *one* explicit, always-available
inhabitant, not a forced one.
-/

@[expose] public section

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

namespace CSD
namespace LF4

open CSD.LF2

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-! ### The positive square root of an effect -/

/-- `√Eᵢ` is Hermitian (any `cfc` of a real function is self-adjoint). -/
lemma povmSqrt_isHermitian (P : POVM N ι) (i : ι) : (cfc Real.sqrt (P.E i).M).IsHermitian := by
  have h : star (cfc Real.sqrt (P.E i).M) = cfc Real.sqrt (P.E i).M :=
    (cfc_predicate Real.sqrt (P.E i).M).star_eq
  rwa [Matrix.star_eq_conjTranspose] at h

/-- `√Eᵢ √Eᵢ = Eᵢ` (the defining square-root property; on `spectrum ℝ Eᵢ ⊆ [0,∞)`,
`√x · √x = x`, and `cfc id Eᵢ = Eᵢ`). -/
lemma povmSqrt_mul_self (P : POVM N ι) (i : ι) :
    cfc Real.sqrt (P.E i).M * cfc Real.sqrt (P.E i).M = (P.E i).M := by
  have hsa : IsSelfAdjoint (P.E i).M := (P.E i).isHermitian
  have hle : (0 : Matrix (Fin N) (Fin N) ℂ) ≤ (P.E i).M := (P.E i).nonneg.nonneg
  have hcongr : cfc (fun x => Real.sqrt x * Real.sqrt x) (P.E i).M
      = cfc (id : ℝ → ℝ) (P.E i).M := by
    refine cfc_congr (fun x hx => ?_)
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hle hx)
  rw [← cfc_mul Real.sqrt Real.sqrt (P.E i).M, hcongr, cfc_id ℝ (P.E i).M]

/-- Entry-level Hermitian symmetry: `conj (√Eᵢ)_{n,m} = (√Eᵢ)_{m,n}`. -/
lemma povmSqrt_conj_entry (P : POVM N ι) (i : ι) (n m : Fin N) :
    star (cfc Real.sqrt (P.E i).M n m) = cfc Real.sqrt (P.E i).M m n := by
  have h : (cfc Real.sqrt (P.E i).M)ᴴ m n = cfc Real.sqrt (P.E i).M m n := by
    rw [(povmSqrt_isHermitian P i)]
  rwa [Matrix.conjTranspose_apply] at h

/-- The common inner column sum: `∑ₙ conj(√Eᵢ)_{n,m} (√Eᵢ)_{n,m'} = (Eᵢ)_{m,m'}`. -/
lemma sqrt_inner_sum (P : POVM N ι) (i : ι) (m m' : Fin N) :
    (∑ n : Fin N, star (cfc Real.sqrt (P.E i).M n m) * cfc Real.sqrt (P.E i).M n m')
      = (P.E i).M m m' := by
  conv_rhs => rw [← povmSqrt_mul_self P i]
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun n _ => by rw [povmSqrt_conj_entry])

/-! ### The canonical Naimark isometry -/

/-- The **canonical Naimark isometry** `V_{(n,i), m} = (√Eᵢ)_{n,m}`, i.e.
`V ψ = ∑ᵢ (√Eᵢ ψ) ⊗ |i⟩` as a matrix `ℂ^N → ℂ^N ⊗ ℂ^ι`. -/
noncomputable def naimarkV (P : POVM N ι) : Matrix (Fin N × ι) (Fin N) ℂ :=
  Matrix.of fun p m => cfc Real.sqrt (P.E p.2).M p.1 m

/-- `V` is an isometry: `Vᴴ V = ∑ᵢ Eᵢ = I`. -/
theorem naimarkV_isom (P : POVM N ι) : (naimarkV P)ᴴ * naimarkV P = 1 := by
  rw [← P.complete]
  ext m m'
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.conjTranspose_apply, naimarkV, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => sqrt_inner_sum P i m m')

variable [DecidableEq ι]

/-- The action of the ancilla projector on `V`:
`(Πᵢ V)_{(n,j), m} = if j = i then (√Eᵢ)_{n,m} else 0`. -/
lemma blockProj_mul_naimarkV (P : POVM N ι) (i : ι) (n : Fin N) (j : ι) (m : Fin N) :
    (blockProj N i * naimarkV P) (n, j) m
      = if j = i then cfc Real.sqrt (P.E i).M n m else 0 := by
  have hrw : (blockProj N i * naimarkV P) (n, j) m
      = (blockProj N i *ᵥ fun q => naimarkV P q m) (n, j) := by
    rw [Matrix.mul_apply]; rfl
  rw [hrw, blockProj_mulVec]
  by_cases hj : j = i
  · simp only [if_pos hj, naimarkV, Matrix.of_apply]
  · simp only [if_neg hj]

/-- **Naimark pullback:** the ancilla-`i` projector compresses `V` back to the
effect, `Vᴴ Πᵢ V = Eᵢ`. -/
theorem naimarkV_pullback (P : POVM N ι) (i : ι) :
    (naimarkV P)ᴴ * blockProj N i * naimarkV P = (P.E i).M := by
  rw [Matrix.mul_assoc]
  ext m m'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hsum : ∀ n : Fin N, ∀ j : ι,
      (naimarkV P)ᴴ m (n, j) * (blockProj N i * naimarkV P) (n, j) m'
        = if j = i then star (cfc Real.sqrt (P.E i).M n m) * cfc Real.sqrt (P.E i).M n m' else 0 := by
    intro n j
    rw [blockProj_mul_naimarkV, Matrix.conjTranspose_apply, naimarkV, Matrix.of_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp only [hsum]
  rw [show (∑ n : Fin N, ∑ j : ι,
        if j = i then star (cfc Real.sqrt (P.E i).M n m) * cfc Real.sqrt (P.E i).M n m' else 0)
      = ∑ n : Fin N, star (cfc Real.sqrt (P.E i).M n m) * cfc Real.sqrt (P.E i).M n m' from
    Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_ite_eq' Finset.univ i]; simp)]
  exact sqrt_inner_sum P i m m'

/-- **Every POVM has a Naimark dilation.** The canonical inhabitant of
`NaimarkDilation P`, built from the CFC square roots `√Eᵢ`. This makes the Phase-1
ontic POVM Born = Kähler-volume results hold for every POVM, modulo the dilation
genericity condition. -/
noncomputable def canonicalNaimark (P : POVM N ι) : NaimarkDilation P where
  V := naimarkV P
  isom := naimarkV_isom P
  pullback := naimarkV_pullback P

end LF4
end CSD
