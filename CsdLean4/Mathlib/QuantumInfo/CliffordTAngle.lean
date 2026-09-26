/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Magic
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The rotation angle of `T·HTH` is an irrational multiple of `π`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #68, part (a) of `R-005`
(`specs/magic-plan.md`, "The split").

`T·HTH` is `e^{iπ/4}` times an element of `SU(2)` whose half-trace is `cos²(π/8)`
(`trace_htht`, `det_htht`): a rotation by the angle `htAngle` with
`cos(htAngle/2) = cos²(π/8)`, so `cos htAngle = (2√2 − 1)/4`. That angle is an **irrational**
multiple of `2π`, which is why the powers of one Clifford+T word already fill a whole
one-parameter rotation subgroup — the engine of Clifford+T universality.

The obstruction is arithmetic. If `θ` is a rational multiple of `2π` then `e^{iθ}` is a root of
unity, hence an algebraic integer, and so is its inverse, so `2 cos θ` is an algebraic integer
(★ `isIntegral_two_mul_cos_of_eq_two_pi_mul`, a general fact Mathlib lacks at the pin). But
`x = 2 cos htAngle = √2 − 1/2` satisfies `x² + x = 7/4`, so if it were an algebraic integer then
`7/4` would be one too, and `ℤ` is integrally closed in `ℚ`
(★ `not_isIntegral_of_sq_add_self_eq`).

* ★ `isIntegral_two_mul_cos_of_eq_two_pi_mul` — `2 cos(2πq)` is an algebraic integer;
* ★ `not_isIntegral_of_sq_add_self_eq` — no algebraic integer satisfies `x² + x = 7/4`;
* `htHalfAngle`, `htAngle`; `cos_sq_pi_div_eight`, `cos_htHalfAngle`, `cos_htAngle`;
* ★★ `irrational_htAngle_div_two_pi` — **`htAngle/(2π)` is irrational**;
* ★ `denseRange_zsmul_htAngle` — the integer multiples of `htAngle` are dense in the circle
  `ℝ/2πℤ`; ★★ `exists_zsmul_htAngle_approx` — the concrete form: every angle is approximated by
  `k·htAngle` modulo `2π`, to any accuracy;
* `hGateM`, `tGateM`, `htht`; `trace_htht`, `det_htht`, ★ `trace_htht_eq_cos_htAngle` —
  **the gate's angle is `htAngle`**: `tr(T·HTH) = 2 cos(htAngle/2) e^{iπ/4}` and
  `det(T·HTH) = e^{iπ/2}`.

## Honest scope

⚠️ This is the angle of one Clifford+T word and the density of its own powers. That
`⟨H, T⟩` is dense in `U(2)` modulo phase needs a second axis and the Euler decomposition: BACKLOG
#81, **done 2026-09-26** in `CsdLean4/Mathlib/QuantumInfo/CliffordTDensity.lean`. The extension to
`U(2ⁿ)` is #70–#73. No efficiency claim: Solovay–Kitaev is
#74 and is not attempted.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.5.3 and
Exercise 4.11; C. M. Dawson, M. A. Nielsen, quant-ph/0505030 §2 (the Solovay–Kitaev setting);
`specs/magic-plan.md`; `specs/BACKLOG.md` #68; `specs/future-work.md`.
-/

@[expose] public section

open Polynomial
open scoped Real

/-! ### Two cosines of rational angles are algebraic integers -/

/-- ★ **`2 cos θ` is an algebraic integer whenever `θ` is a rational multiple of `2π`**: `e^{iθ}`
is then a root of unity, so it and its inverse are algebraic integers, and `2 cos θ` is their
sum. -/
theorem isIntegral_two_mul_cos_of_eq_two_pi_mul {θ : ℝ} {q : ℚ} (hθ : θ = 2 * π * q) :
    IsIntegral ℤ (2 * Real.cos θ) := by
  have hd0 : q.den ≠ 0 := q.den_nz
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζdef
  -- `d · θ = 2π · num`, so `ζ` is a `d`-th root of unity
  have hdθ : (q.den : ℝ) * θ = 2 * π * (q.num : ℝ) := by
    rw [hθ, Rat.cast_def]
    have hne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    field_simp
  have hζd : ζ ^ q.den = 1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have hcast : ((q.den : ℂ)) * ((θ : ℂ) * Complex.I)
        = (q.num : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) hdθ
      push_cast at h
      calc ((q.den : ℂ)) * ((θ : ℂ) * Complex.I) = ((q.den : ℂ) * (θ : ℂ)) * Complex.I := by ring
        _ = (2 * (π : ℂ) * (q.num : ℂ)) * Complex.I := by rw [h]
        _ = (q.num : ℂ) * (2 * (π : ℂ) * Complex.I) := by ring
    rw [hcast, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  -- a root of unity is an algebraic integer
  have hζint : IsIntegral ℤ ζ := by
    refine ⟨X ^ q.den - 1, ?_, ?_⟩
    · simpa using monic_X_pow_sub_C (1 : ℤ) hd0
    · simp [hζd]
  -- so is its inverse, and `2 cos θ` is their sum
  have hpow : ζ ^ (q.den - 1) * ζ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd0)]
    exact hζd
  have hinv : ζ ^ (q.den - 1) = ζ⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hsum : IsIntegral ℤ (ζ + ζ⁻¹) := by
    rw [← hinv]
    exact hζint.add (hζint.pow _)
  have hcos : ζ + ζ⁻¹ = ((2 * Real.cos θ : ℝ) : ℂ) := by
    have h2 := Complex.two_cos (θ : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, h2, hζdef,
      show -(θ : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) by ring, Complex.exp_neg]
  rw [hcos] at hsum
  rwa [← isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ) Complex.ofReal_injective,
    Complex.coe_algebraMap]

/-! ### `x² + x = 7/4` has no algebraic-integer solution -/

/-- ★ **No algebraic integer satisfies `x² + x = 7/4`**: it would make `7/4` an algebraic integer,
and `ℤ` is integrally closed in `ℚ`. -/
theorem not_isIntegral_of_sq_add_self_eq {x : ℝ} (hx : x ^ 2 + x = 7 / 4) : ¬ IsIntegral ℤ x := by
  intro h
  have h74 : IsIntegral ℤ ((7 / 4 : ℝ)) := by
    rw [← hx]
    exact (h.pow 2).add h
  have hq : IsIntegral ℤ ((7 / 4 : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℝ) Rat.cast_injective]
    have hmap : (algebraMap ℚ ℝ) (7 / 4 : ℚ) = (7 / 4 : ℝ) := by norm_num
    rw [hmap]
    exact h74
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hy' : (y : ℚ) = 7 / 4 := by simpa using hy
  have h4' : y * 4 = 7 := by
    field_simp at hy'
    exact_mod_cast hy'
  omega

/-! ### The angle of `T·HTH` -/

namespace QuantumInfo

namespace CliffordT

/-- Half the rotation angle of `T·HTH`: the angle whose cosine is `cos²(π/8)`. -/
noncomputable def htHalfAngle : ℝ := Real.arccos (Real.cos (π / 8) ^ 2)

/-- The rotation angle of `T·HTH`. -/
noncomputable def htAngle : ℝ := 2 * htHalfAngle

theorem cos_sq_pi_div_eight : Real.cos (π / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [Real.cos_sq, show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four]
  ring

theorem cos_htHalfAngle : Real.cos htHalfAngle = Real.cos (π / 8) ^ 2 := by
  refine Real.cos_arccos ?_ ?_
  · nlinarith [sq_nonneg (Real.cos (π / 8))]
  · nlinarith [Real.cos_le_one (π / 8), Real.neg_one_le_cos (π / 8)]

theorem sq_sqrt_two : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem cos_htAngle : Real.cos htAngle = (2 * Real.sqrt 2 - 1) / 4 := by
  rw [htAngle, Real.cos_two_mul, cos_htHalfAngle, cos_sq_pi_div_eight]
  nlinarith [sq_sqrt_two]

theorem sq_add_self_two_mul_cos_htAngle :
    (2 * Real.cos htAngle) ^ 2 + 2 * Real.cos htAngle = 7 / 4 := by
  rw [cos_htAngle]
  nlinarith [sq_sqrt_two]

/-- ★★ **The angle of `T·HTH` is an irrational multiple of `2π`.** -/
theorem irrational_htAngle_div_two_pi : Irrational (htAngle / (2 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hθ : htAngle = 2 * π * q := by
    field_simp at hq
    linarith [hq]
  exact not_isIntegral_of_sq_add_self_eq sq_add_self_two_mul_cos_htAngle
    (isIntegral_two_mul_cos_of_eq_two_pi_mul hθ)

/-- ★ The integer multiples of `htAngle` are dense in the circle `ℝ/2πℤ`. -/
theorem denseRange_zsmul_htAngle :
    DenseRange fun k : ℤ => k • (htAngle : AddCircle (2 * π)) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr irrational_htAngle_div_two_pi

/-- The subgroup generated by `htAngle` and `2π` is dense in `ℝ`. -/
theorem dense_closure_htAngle :
    Dense (AddSubgroup.closure {htAngle, 2 * π} : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.mpr irrational_htAngle_div_two_pi

/-- ★★ **Every angle is an integer multiple of `htAngle` modulo `2π`, to any accuracy.** This is
the form the gate-approximation argument consumes: repeating the Clifford+T word `T·HTH` `k` times
realises any rotation about its axis, as closely as required. -/
theorem exists_zsmul_htAngle_approx (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k m : ℤ, |(k : ℝ) * htAngle + (m : ℝ) * (2 * π) - α| < ε := by
  obtain ⟨y, hy, hdist⟩ := dense_closure_htAngle.exists_dist_lt α hε
  obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp hy
  refine ⟨k, m, ?_⟩
  rw [Real.dist_eq] at hdist
  rw [zsmul_eq_mul, zsmul_eq_mul] at hkm
  rw [hkm, abs_sub_comm]
  exact hdist

/-! ### The gate -/

/-- The Hadamard as a `2 × 2` matrix. -/
noncomputable def hGateM : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- The `T` gate as a `2 × 2` matrix. -/
noncomputable def tGateM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, tPhase]

/-- The Clifford+T word `T·H·T·H`. -/
noncomputable def htht : Matrix (Fin 2) (Fin 2) ℂ := tGateM * hGateM * tGateM * hGateM

theorem sqrt_two_inv_sq_two : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem htht_eq : htht = (((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) •
    !![1 + tPhase, 1 - tPhase; tPhase * (1 - tPhase), tPhase * (1 + tPhase)]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [htht, hGateM, tGateM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The trace of the Clifford+T word: `(1 + e^{iπ/4})²/2`. -/
theorem trace_htht : htht.trace = (1 + tPhase) ^ 2 / 2 := by
  rw [htht_eq, Matrix.trace_smul, Matrix.trace_fin_two_of, smul_eq_mul]
  have h := sqrt_two_inv_sq_two
  linear_combination ((1 + tPhase) ^ 2 / 2) * h

/-- The determinant of the Clifford+T word: `e^{iπ/2} = i`. -/
theorem det_htht : htht.det = tPhase ^ 2 := by
  rw [htht_eq, Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin]
  have h := sqrt_two_inv_sq_two
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) ^ 2 * 4 = 1 := by
    have h4 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2) ^ 2 = 1 := by rw [h]; norm_num
    linear_combination h4
  linear_combination (tPhase ^ 2) * hsq

/-- `e^{iπ/8}`, the square root of the `T` phase. -/
noncomputable def tPhase8 : ℂ := Complex.exp (((π / 8 : ℝ) : ℂ) * Complex.I)

theorem tPhase8_sq : tPhase8 ^ 2 = tPhase := by
  rw [tPhase8, tPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem tPhase8_ne_zero : tPhase8 ≠ 0 := Complex.exp_ne_zero _

theorem tPhase8_add_inv : tPhase8 + tPhase8⁻¹ = 2 * (Real.cos (π / 8) : ℂ) := by
  have h2 := Complex.two_cos (((π / 8 : ℝ)) : ℂ)
  have hneg : Complex.exp (-(((π / 8 : ℝ)) : ℂ) * Complex.I) = tPhase8⁻¹ := by
    rw [tPhase8,
      show -(((π / 8 : ℝ)) : ℂ) * Complex.I = -((((π / 8 : ℝ)) : ℂ) * Complex.I) by ring,
      Complex.exp_neg]
  rw [Complex.ofReal_cos, h2, hneg, tPhase8]

/-- `1 + e^{iπ/4} = 2 cos(π/8) e^{iπ/8}`. -/
theorem one_add_tPhase : 1 + tPhase = 2 * (Real.cos (π / 8) : ℂ) * tPhase8 := by
  have h := tPhase8_add_inv
  have hne := tPhase8_ne_zero
  rw [← tPhase8_sq, ← h]
  field_simp
  ring

/-- ★ **The gate's rotation angle is `htAngle`**: `tr(T·HTH) = 2 cos(htAngle/2) e^{iπ/4}`, and
`det(T·HTH) = e^{iπ/2}` (`det_htht`), so `e^{−iπ/4}·T·HTH` lies in `SU(2)` with half-trace
`cos(htAngle/2) = cos²(π/8)`: it is a rotation by `htAngle`. -/
theorem trace_htht_eq_cos_htAngle :
    htht.trace = 2 * (Real.cos (htAngle / 2) : ℂ) * tPhase := by
  have hhalf : htAngle / 2 = htHalfAngle := by rw [htAngle]; ring
  rw [trace_htht, hhalf, cos_htHalfAngle, one_add_tPhase]
  push_cast
  rw [mul_pow, mul_pow, tPhase8_sq]
  ring

end CliffordT

end QuantumInfo

end
