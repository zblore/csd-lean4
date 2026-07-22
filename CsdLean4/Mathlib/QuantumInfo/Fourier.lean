/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Register
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Quantum Fourier transform and its unitarity (R5)

**Category:** 1-Mathlib (CSD-free).

Phase R5 of `specs/nqubit-register-plan.md`: the **quantum Fourier transform** on `N`
levels, as the `N × N` matrix

  `F j k = (1/√N) · ω^{jk}`,   `ω = exp(2πi/N)` a primitive `N`-th root of unity,

and the key fact that it is **unitary** (`qft_unitary`, `Fᴴ * F = 1`). Entrywise the unitary
identity reads

  `(Fᴴ F) j j' = (1/N) ∑ₖ ω^{k(j'-j)} = [j = j']`,

i.e. the **roots-of-unity orthogonality** `∑_{k=0}^{N-1} ζ^k = N·[ζ=1]` (a geometric series),
which is the ℂ-analogue of the `±1`-character orthogonality behind the Hadamard transform
(R3). The QFT is a finite `N × N` unitary; nothing here leaves the finite-dimensional
setting.

The transform is defined on a general level count `N` (not specialised to `N = 2ⁿ`), so it is
directly the discrete Fourier unitary; the qubit instance is the `N = 2ⁿ` case.
-/

open scoped ComplexConjugate
open scoped Matrix

namespace QuantumInfo

variable (N : ℕ)

/-- The primitive `N`-th root of unity `ω = exp(2πi/N)`. -/
noncomputable def qftω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- `ω` is a primitive `N`-th root of unity. -/
lemma qftω_primitive [NeZero N] : IsPrimitiveRoot (qftω N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- `ωᴺ = 1`. -/
lemma qftω_pow_N [NeZero N] : qftω N ^ N = 1 := (qftω_primitive N).pow_eq_one

/-- `ω` is nonzero (a value of `exp`). -/
lemma qftω_ne_zero : qftω N ≠ 0 := Complex.exp_ne_zero _

/-- `ω` is unimodular: conjugation inverts it. -/
lemma qftω_conj : conj (qftω N) = (qftω N)⁻¹ := by
  rw [qftω, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
  ring

/-- `√N · √N = N` over `ℂ`. -/
lemma sqrtN_mul_self : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]

/-- `(√N)⁻¹ · (√N)⁻¹ = N⁻¹`. -/
lemma inv_sqrtN_sq : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv, sqrtN_mul_self]

/-- The **quantum Fourier transform** as an `N × N` matrix: `F j k = (1/√N) ω^{jk}`. -/
noncomputable def qftMatrix : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => (Real.sqrt N : ℂ)⁻¹ * qftω N ^ (j.val * k.val)

@[simp] lemma qftMatrix_apply (j k : Fin N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * qftω N ^ (j.val * k.val) := rfl

/-- The QFT matrix is **symmetric** (`Fᵀ = F`), since `jk = kj`. -/
lemma qftMatrix_symm (j k : Fin N) : qftMatrix N j k = qftMatrix N k j := by
  rw [qftMatrix_apply, qftMatrix_apply, Nat.mul_comm]

/-- **The quantum Fourier transform is unitary:** `Fᴴ * F = 1`. The entrywise identity is the
roots-of-unity orthogonality `(1/N) ∑ₖ ω^{k(j'-j)} = [j = j']`, a geometric series that
vanishes for `j ≠ j'` and sums to `N` for `j = j'`. -/
theorem qft_unitary [NeZero N] : (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  ext j j'
  rw [Matrix.mul_apply, Matrix.one_apply]
  set ζ : ℂ := conj (qftω N) ^ j.val * qftω N ^ j'.val with hζdef
  -- each summand is `N⁻¹ · ζ^k`
  have hsum : ∀ k : Fin N, (qftMatrix N)ᴴ j k * qftMatrix N k j' = (N : ℂ)⁻¹ * ζ ^ k.val := by
    intro k
    have hpow : ζ ^ k.val
        = conj (qftω N) ^ (k.val * j.val) * qftω N ^ (k.val * j'.val) := by
      rw [hζdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm j.val k.val, mul_comm j'.val k.val]
    rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, qftMatrix_apply, qftMatrix_apply,
        map_mul, map_pow, map_inv₀, Complex.conj_ofReal, hpow]
    rw [show ((Real.sqrt N : ℂ)⁻¹ * conj (qftω N) ^ (k.val * j.val))
            * ((Real.sqrt N : ℂ)⁻¹ * qftω N ^ (k.val * j'.val))
          = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹)
            * (conj (qftω N) ^ (k.val * j.val) * qftω N ^ (k.val * j'.val)) from by ring,
        inv_sqrtN_sq]
  -- collect into `N⁻¹ · ∑_{i<N} ζ^i`
  have hrw : (∑ k : Fin N, (qftMatrix N)ᴴ j k * qftMatrix N k j')
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ζ ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) N, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hsum k
  by_cases h : j = j'
  · -- `ζ = 1`, the sum is `N`, so `N⁻¹ · N = 1`
    have hζ1 : ζ = 1 := by
      rw [hζdef, h, qftω_conj, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero _ (qftω_ne_zero N))]
    rw [hrw, hζ1, if_pos h]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hN]
  · -- `ζ ≠ 1` is an `N`-th root of unity, so the geometric sum vanishes
    have hζN : ζ ^ N = 1 := by
      have hcN : conj (qftω N) ^ N = 1 := by rw [← map_pow, qftω_pow_N, map_one]
      rw [hζdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm j.val N, mul_comm j'.val N,
        pow_mul, pow_mul, hcN, qftω_pow_N, one_pow, one_pow, mul_one]
    have hζne : ζ ≠ 1 := by
      intro hζ1
      have hω : qftω N ^ j.val ≠ 0 := pow_ne_zero _ (qftω_ne_zero N)
      have h2 : (qftω N ^ j.val)⁻¹ * qftω N ^ j'.val = 1 := by
        rw [hζdef, qftω_conj, inv_pow] at hζ1; exact hζ1
      have key : qftω N ^ j.val = qftω N ^ j'.val := (inv_mul_eq_one₀ hω).mp h2
      exact h (Fin.ext ((qftω_primitive N).pow_inj j.isLt j'.isLt key))
    rw [hrw, geom_sum_eq hζne N, hζN, sub_self, zero_div, mul_zero, if_neg h]

end QuantumInfo
