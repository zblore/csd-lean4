/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.EulerDecomposition
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Clifford+T fills `SU(2)`: two orthogonal dense circles and the Euler decomposition

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #81, part (b2) of `R-005`; the
single-qubit half of Clifford+T universality. #68 and #80 built one dense circle, #84 the Euler
decomposition; this file closes the gap between them.

★★ `det_one_mem_cliffordTLim`: **every determinant-one `2 × 2` unitary is a limit of Clifford+T
words**, and hence ★★ `exists_phase_mem_cliffordTLim`: **Clifford+T is dense in `U(2)` modulo
phase**. The obstruction that shaped the proof is worth recording: no two axes in the Clifford orbit
of the word's own axis are orthogonal, so a *third* axis has to be manufactured, and the mechanism
is the cross product.

**The second axis.** The `π` rotation about the word's axis `(htA, htB, htA)` — available because
#80's circle is dense and the closure is closed — followed by `H`, is a rotation about
`(1, 0, -1)/√2`, the cross product of the two axes (★ `axisRot_htAxis_pi_mul_hGateM`; the `y`
components cancel because the word's axis has equal `x` and `z` components). Its angle `wAngle`
satisfies `2 cos wAngle = (6 + 16√2)/17`.

**That angle is irrational over `2π`,** and the cheap test of #68 cannot see it: `x² + x = q` needs
an integer linear coefficient, and here the minimal polynomial is `X² - (12/17)X - 28/17`. So this
file proves the general form, ★ `not_isIntegral_of_quadratic`: a monic rational quadratic whose
linear coefficient is not an integer has no algebraic-integer root, because the minimal polynomial
of an algebraic integer has integer coefficients and, for an irrational root, that quadratic *is*
the minimal polynomial. With #68's `isIntegral_two_mul_cos_of_eq_two_pi_mul` that gives ★★
`irrational_wAngle_div_two_pi`.

**Two orthogonal circles.** Conjugating the new circle by `Z = T⁴` reflects its axis to
`(1, 0, 1)/√2` (★★ `axisRot_uAxis_mem`), which is orthogonal to it. The Euler decomposition about
that pair, ★★ `exists_euler_two_axes`, comes from #84's `z`-`y`-`z` form by two conjugations:
`R_z(π/2)` turns the `y` axis into `x` (`rzMat_conj_ryMat`), and `R_y(π/4)` tilts `z` and `x` onto
`(1, 0, 1)/√2` and `(1, 0, -1)/√2` (`ryMat_conj_rzMat`, `ryMat_conj_axisRot_x`).

* ★ `not_isIntegral_of_quadratic`;
* `htB_pos`, `htA_sq`, `htB_sq` — the word's axis in closed form, `htA² = (5 + 2√2)/17`;
* `wHalfCos`, `wAngle`, `wHalfCos_sq`, `wHalfCos_mem`, `cos_wAngle_half`, `sin_wAngle_half`,
  `two_mul_cos_wAngle`, `irrational_two_mul_cos_wAngle`, `not_isIntegral_two_mul_cos_wAngle`,
  ★★ `irrational_wAngle_div_two_pi`, `irrational_wAngle_div_four_pi`;
* `axisRot_neg_axis`, `ryMat_conj_rzMat`, `ryMat_conj_axisRot_x`, `rzMat_conj_ryMat`,
  `conj_mul_three`, `exists_euler_zxz`, ★★ `exists_euler_two_axes`;
* `hGateM_mul_self`, `tGateM_pow`, `tGateM_pow_eight`, `pow_mul_pow_eq_one`, `cliffordT`,
  `cliffordTLim`, `hGateM_mem`, `tGateM_mem`, `cliffordT_le_lim`, `isClosed_cliffordTLim`;
* `mem_closure_range_axisRot_of_irrational`, `axisRot_int_mul_mem`,
  ★ `axisRot_mem_of_irrational` — one rotation with an irrationally related angle gives the whole
  circle, inside any closed submonoid containing it and its inverse;
* `wAxis_unit`, `uAxis_unit`, `sqrt_two_inv_eq`, `hGateM_eq_smul_su2`,
  ★ `axisRot_htAxis_pi_mul_hGateM`;
* `htht_mem`, `hthtInv_mem`, `htht_mul_inv`, `axisRot_htAxis_eight`, `irrational_eight_htAngle`,
  ★★ `axisRot_htAxis_mem` — the first circle;
* `piRot_mul_hGateM_mem`, `hGateM_mul_piRot_mem`, `piRot_mul_hGateM_mul_inv`,
  `axisRot_wAxis_four`, `irrational_four_wAngle`, ★★ `axisRot_wAxis_mem` — the second;
* `zGateM`, `tPhase_pow_four`, `zGateM_eq`, `zGateM_conj_su2`, `zGateM_conj_axisRot`,
  ★★ `axisRot_uAxis_mem` — the third, orthogonal to the second;
* ★★ `det_one_mem_cliffordTLim`, ★★ `exists_phase_mem_cliffordTLim`.

## Honest scope

⚠️ One qubit, and density rather than exactness: the statement is that `SU(2)` lies in the
*topological closure* of the Clifford+T monoid, which is what a synthesis theorem needs and all that
is true (the monoid itself is countable). The `n`-qubit statement is BACKLOG #73, which assembles
this with #70, #71 and #85.
⚠️ No efficiency claim. How many gates an `ε`-approximation costs is Solovay–Kitaev, BACKLOG #74,
deliberately not claimed.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.5.3 and
Exercise 4.11; C. M. Dawson, M. A. Nielsen, quant-ph/0505030 §2;
`CsdLean4/Mathlib/QuantumInfo/CliffordTAngle.lean` and `SU2Rotation.lean` for the first circle,
`EulerDecomposition.lean` for the `z`-`y`-`z` form; `specs/magic-plan.md`; `specs/BACKLOG.md` #81,
#73; `specs/future-work.md`.
-/

@[expose] public section

open Matrix Polynomial
open scoped Real

/-! ### No algebraic integer satisfies a monic rational quadratic with a fractional coefficient -/

/-- ★ **A monic rational quadratic whose linear coefficient is not an integer has no
algebraic-integer root**, provided the root is irrational: the minimal polynomial of an algebraic
integer has integer coefficients, and for an irrational root this quadratic *is* the minimal
polynomial. The `x² + x = 7/4` helper of #68 is the case where the trick is cheaper; this is the
general form, needed because the second axis of #81 has `17` in its denominators. -/
theorem not_isIntegral_of_quadratic {x : ℝ} {p q : ℚ}
    (hx : x ^ 2 + (p : ℝ) * x + (q : ℝ) = 0) (hirr : Irrational x) (hp : p.den ≠ 1) :
    ¬ IsIntegral ℤ x := by
  intro h
  set P : ℚ[X] := X ^ 2 + C p * X + C q with hP
  have hPmonic : P.Monic := by rw [hP]; monicity!
  have hPdeg : P.natDegree = 2 := by rw [hP]; compute_degree!
  have hroot : (aeval x) P = 0 := by
    rw [hP]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    linear_combination hx
  have hxint : IsIntegral ℚ x := ⟨P, hPmonic, hroot⟩
  have hdvd : minpoly ℚ x ∣ P := minpoly.dvd ℚ x hroot
  have hge : 2 ≤ (minpoly ℚ x).natDegree := by
    refine (minpoly.two_le_natDegree_iff hxint).mpr ?_
    intro hmem
    obtain ⟨y, hy⟩ := hmem
    exact hirr ⟨y, by rw [← hy]; simp⟩
  have hle : (minpoly ℚ x).natDegree ≤ 2 := by
    rw [← hPdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := le_antisymm hle hge
  have heq : minpoly ℚ x = P := by
    obtain ⟨C', hC'⟩ := hdvd
    have hC'ne : C' ≠ 0 := fun hz => hPmonic.ne_zero (by rw [hC', hz, mul_zero])
    have hdegs : P.natDegree = (minpoly ℚ x).natDegree + C'.natDegree := by
      rw [hC', Polynomial.natDegree_mul (minpoly.ne_zero hxint) hC'ne]
    have hC'deg : C'.natDegree = 0 := by
      rw [hPdeg, hdeg2] at hdegs
      omega
    have hC'monic : C'.Monic :=
      Polynomial.Monic.of_mul_monic_left (minpoly.monic hxint) (hC' ▸ hPmonic)
    rw [hC', Polynomial.eq_one_of_monic_natDegree_zero hC'monic hC'deg, mul_one]
  have hmap : minpoly ℚ x = Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h
  have h1 : (minpoly ℚ x).coeff 1 = p := by
    rw [heq, hP]
    simp
  rw [hmap, Polynomial.coeff_map] at h1
  exact hp (by rw [← h1]; simp)

namespace QuantumInfo

namespace SU2

open CliffordT

/-! ### The word's axis in closed form -/

theorem htB_pos : 0 < htB := by
  rw [htB]
  have h1 : Real.sqrt 2 < 2 := sqrt_two_lt_two
  exact div_pos (by linarith) htSin_pos

theorem htA_sq : htA ^ 2 = (5 + 2 * Real.sqrt 2) / 17 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 2 := sqrt_two_lt_two
  have hd : (10 : ℝ) - 4 * Real.sqrt 2 ≠ 0 := by nlinarith
  have hprod : htA ^ 2 * htSin ^ 2 = 2 / 16 := by
    rw [htA, div_pow, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 htSin_ne_zero),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have key : htA ^ 2 * ((10 : ℝ) - 4 * Real.sqrt 2) = 2 := by
    rw [htSin_sq] at hprod
    linear_combination 16 * hprod
  have expand : (5 + 2 * Real.sqrt 2) * ((10 : ℝ) - 4 * Real.sqrt 2) = 34 := by nlinarith [h2]
  have h17 : (17 : ℝ) * htA ^ 2 = 5 + 2 * Real.sqrt 2 := by
    refine mul_right_cancel₀ hd ?_
    rw [expand]
    linear_combination 17 * key
  linarith

theorem htB_sq : htB ^ 2 = (7 - 4 * Real.sqrt 2) / 17 := by
  have h := htAxis_unit
  rw [htA_sq] at h
  linarith

/-! ### The second axis and its angle

The `π` rotation about the word's axis, followed by `H`, is a rotation about `(1, 0, -1)/√2`: the
cross product of the two axes. Its angle is `wAngle`.
-/

/-- The cosine of half the second rotation's angle. -/
noncomputable def wHalfCos : ℝ := -(Real.sqrt 2 * htA)

/-- The angle of the second rotation. -/
noncomputable def wAngle : ℝ := 2 * Real.arccos wHalfCos

theorem wHalfCos_sq : wHalfCos ^ 2 = (10 + 4 * Real.sqrt 2) / 17 := by
  rw [wHalfCos, neg_sq, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), htA_sq]
  ring

theorem sqrt_two_lt_seven_quarters : Real.sqrt 2 < 7 / 4 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem wHalfCos_sq_lt_one : wHalfCos ^ 2 < 1 := by
  rw [wHalfCos_sq]
  nlinarith [sqrt_two_lt_seven_quarters]

theorem wHalfCos_mem : -1 ≤ wHalfCos ∧ wHalfCos ≤ 1 := by
  have h := wHalfCos_sq_lt_one
  constructor <;> nlinarith [sq_nonneg (wHalfCos + 1), sq_nonneg (wHalfCos - 1)]

theorem cos_wAngle_half : Real.cos (wAngle / 2) = wHalfCos := by
  rw [wAngle, show 2 * Real.arccos wHalfCos / 2 = Real.arccos wHalfCos by ring,
    Real.cos_arccos wHalfCos_mem.1 wHalfCos_mem.2]

theorem sin_wAngle_half : Real.sin (wAngle / 2) = htB := by
  have hb := htB_sq
  rw [wAngle, show 2 * Real.arccos wHalfCos / 2 = Real.arccos wHalfCos by ring, Real.sin_arccos,
    show 1 - wHalfCos ^ 2 = htB ^ 2 by rw [wHalfCos_sq, hb]; ring, Real.sqrt_sq htB_pos.le]

/-- The second angle in the form the algebraic-integer test wants. -/
theorem two_mul_cos_wAngle : 2 * Real.cos wAngle = (6 + 16 * Real.sqrt 2) / 17 := by
  have hdouble : Real.cos wAngle = 2 * Real.cos (wAngle / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (wAngle / 2)
    rwa [show 2 * (wAngle / 2) = wAngle by ring] at h
  rw [hdouble, cos_wAngle_half, wHalfCos_sq]
  ring

theorem irrational_two_mul_cos_wAngle : Irrational (2 * Real.cos wAngle) := by
  rw [two_mul_cos_wAngle]
  rintro ⟨q, hq⟩
  refine irrational_sqrt_two ⟨(17 * q - 6) / 16, ?_⟩
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

theorem not_isIntegral_two_mul_cos_wAngle : ¬ IsIntegral ℤ (2 * Real.cos wAngle) := by
  refine not_isIntegral_of_quadratic (p := -12 / 17) (q := -28 / 17) ?_
    irrational_two_mul_cos_wAngle (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [two_mul_cos_wAngle]
  push_cast
  nlinarith [h2]

/-- ★★ **The second angle is an irrational multiple of `2π`**, so the powers of the second rotation
fill its own circle. -/
theorem irrational_wAngle_div_two_pi : Irrational (wAngle / (2 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hθ : wAngle = 2 * π * q := by
    field_simp at hq
    linarith [hq]
  exact not_isIntegral_two_mul_cos_wAngle (isIntegral_two_mul_cos_of_eq_two_pi_mul hθ)

theorem irrational_wAngle_div_four_pi : Irrational (wAngle / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_wAngle_div_two_pi ⟨2 * q, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-! ### Conjugation moves the axis -/

theorem axisRot_neg_axis (a b c θ : ℝ) : axisRot (-a) (-b) (-c) θ = axisRot a b c (-θ) := by
  rw [axisRot, axisRot, show -θ / 2 = -(θ / 2) by ring, Real.cos_neg, Real.sin_neg]
  congr 1 <;> ring

/-- Conjugating a `z` rotation by `R_y(π/4)` tilts its axis to `(1, 0, 1)/√2`. -/
theorem ryMat_conj_rzMat (t : ℝ) :
    Euler.ryMat (π / 4) * Euler.rzMat t * Euler.ryMat (-(π / 4))
      = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) t := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpy : Real.sin (π / 8) ^ 2 + Real.cos (π / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hdiff : Real.cos (π / 8) ^ 2 - Real.sin (π / 8) ^ 2 = Real.sqrt 2 / 2 := by
    have h := Real.cos_two_mul' (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four] at h
    linarith [h]
  have hprod : 2 * (Real.sin (π / 8) * Real.cos (π / 8)) = Real.sqrt 2 / 2 := by
    have h := Real.sin_two_mul (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four] at h
    linarith [h]
  rw [Euler.ryMat, Euler.rzMat, Euler.ryMat, axisRot, axisRot, axisRot, axisRot,
    show π / 4 / 2 = π / 8 by ring, show -(π / 4) / 2 = -(π / 8) by ring,
    Real.cos_neg, Real.sin_neg, su2_mul, su2_mul]
  congr 1
  · linear_combination Real.cos (t / 2) * hpy
  · linear_combination Real.sin (t / 2) * hprod
  · ring
  · linear_combination Real.sin (t / 2) * hdiff

/-- Conjugating an `x` rotation by `R_y(π/4)` tilts its axis to `(1, 0, -1)/√2`. -/
theorem ryMat_conj_axisRot_x (t : ℝ) :
    Euler.ryMat (π / 4) * axisRot 1 0 0 t * Euler.ryMat (-(π / 4))
      = axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) t := by
  have hpy : Real.sin (π / 8) ^ 2 + Real.cos (π / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hdiff : Real.cos (π / 8) ^ 2 - Real.sin (π / 8) ^ 2 = Real.sqrt 2 / 2 := by
    have h := Real.cos_two_mul' (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four] at h
    linarith [h]
  have hprod : 2 * (Real.sin (π / 8) * Real.cos (π / 8)) = Real.sqrt 2 / 2 := by
    have h := Real.sin_two_mul (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four] at h
    linarith [h]
  rw [Euler.ryMat, axisRot, Euler.ryMat, axisRot, axisRot, axisRot,
    show π / 4 / 2 = π / 8 by ring, show -(π / 4) / 2 = -(π / 8) by ring,
    Real.cos_neg, Real.sin_neg, su2_mul, su2_mul]
  congr 1
  · linear_combination Real.cos (t / 2) * hpy
  · linear_combination Real.sin (t / 2) * hdiff
  · ring
  · linear_combination (-(Real.sin (t / 2))) * hprod

/-- Conjugating a `y` rotation by `R_z(-π/2)` turns its axis into `x`. -/
theorem rzMat_conj_ryMat (γ : ℝ) :
    Euler.rzMat (-(π / 2)) * Euler.ryMat γ * Euler.rzMat (π / 2) = axisRot 1 0 0 γ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Euler.rzMat, Euler.ryMat, Euler.rzMat, axisRot, axisRot, axisRot, axisRot,
    show -(π / 2) / 2 = -(π / 4) by ring, show π / 2 / 2 = π / 4 by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, su2_mul, su2_mul]
  congr 1
  · linear_combination (Real.cos (γ / 2) / 2) * h2
  · linear_combination (Real.sin (γ / 2) / 2) * h2
  · ring
  · ring

/-! ### The Euler decomposition about two explicit orthogonal axes -/

theorem conj_mul_three {g g' A B C : Matrix (Fin 2) (Fin 2) ℂ} (h : g' * g = 1) :
    g * A * g' * (g * B * g') * (g * C * g') = g * (A * B * C) * g' := by
  calc g * A * g' * (g * B * g') * (g * C * g')
      = g * A * (g' * g) * B * (g' * g) * C * g' := by simp only [mul_assoc]
    _ = g * (A * B * C) * g' := by
        rw [h]
        simp only [mul_one, mul_assoc]

/-- The `z`-`x`-`z` Euler decomposition, from the `z`-`y`-`z` one by conjugating with `R_z(π/2)`. -/
theorem exists_euler_zxz {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = Euler.rzMat β * axisRot 1 0 0 γ * Euler.rzMat δ := by
  have hgg : Euler.rzMat (π / 2) * Euler.rzMat (-(π / 2)) = 1 := by
    rw [Euler.rzMat_mul, show π / 2 + -(π / 2) = 0 by ring, Euler.rzMat_zero]
  have hgg' : Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2) = 1 := by
    rw [Euler.rzMat_mul, show -(π / 2) + π / 2 = 0 by ring, Euler.rzMat_zero]
  have hVmem : Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2))
      ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.rzMat_mem_unitaryGroup _) hU) (Euler.rzMat_mem_unitaryGroup _)
  have hVdet : (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2))).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, Euler.rzMat, Euler.rzMat,
      axisRot_det (by norm_num), axisRot_det (by norm_num)]
    norm_num
  obtain ⟨β, γ, δ, hV⟩ := Euler.exists_euler_of_det_one hVmem hVdet
  refine ⟨β, γ, δ, ?_⟩
  have hU' : U = Euler.rzMat (-(π / 2)) * (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2)))
      * Euler.rzMat (π / 2) := by
    rw [show Euler.rzMat (-(π / 2)) * (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2)))
        * Euler.rzMat (π / 2)
        = (Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2)) * U
          * (Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2)) by simp only [mul_assoc], hgg']
    simp
  rw [hU', hV, ← conj_mul_three hgg, rzMat_conj_ryMat]
  congr 1
  · congr 1
    rw [Euler.rzMat_mul, Euler.rzMat_mul]
    congr 1
    ring
  · rw [Euler.rzMat_mul, Euler.rzMat_mul]
    congr 1
    ring

/-- ★★ **The Euler decomposition about the two orthogonal axes `(1, 0, ±1)/√2`**: every
determinant-one unitary is a product of three rotations about them, alternating. These are the two
axes the Clifford+T words reach. -/
theorem exists_euler_two_axes {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) β
        * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) γ
        * axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) δ := by
  have hgg : Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4)) = 1 := by
    rw [Euler.ryMat_mul, show π / 4 + -(π / 4) = 0 by ring, Euler.ryMat_zero]
  have hgg' : Euler.ryMat (-(π / 4)) * Euler.ryMat (π / 4) = 1 := by
    rw [Euler.ryMat_mul, show -(π / 4) + π / 4 = 0 by ring, Euler.ryMat_zero]
  have hVmem : Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.ryMat_mem_unitaryGroup _) hU) (Euler.ryMat_mem_unitaryGroup _)
  have hVdet : (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, Euler.ryMat, Euler.ryMat,
      axisRot_det (by norm_num), axisRot_det (by norm_num)]
    norm_num
  obtain ⟨β, γ, δ, hV⟩ := exists_euler_zxz hVmem hVdet
  refine ⟨β, γ, δ, ?_⟩
  have hU' : U = Euler.ryMat (π / 4) * (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4))
      * Euler.ryMat (-(π / 4)) := by
    rw [show Euler.ryMat (π / 4) * (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4))
        * Euler.ryMat (-(π / 4))
        = (Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4))) * U
          * (Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4))) by simp only [mul_assoc], hgg]
    simp
  rw [hU', hV, ← conj_mul_three hgg', ryMat_conj_rzMat, ryMat_conj_axisRot_x, ryMat_conj_rzMat]

/-! ### The generators as a monoid -/

theorem hGateM_mul_self : hGateM * hGateM = 1 := by
  have h := sqrt_two_inv_sq_two
  rw [hGateM, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> linear_combination h

theorem tGateM_pow (n : ℕ) : tGateM ^ n = !![1, 0; 0, tPhase ^ n] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih, tGateM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem tGateM_pow_eight : tGateM ^ 8 = 1 := by
  rw [tGateM_pow, tPhase_pow_eight]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pow_mul_pow_eq_one {A B : Matrix (Fin 2) (Fin 2) ℂ} (h : A * B = 1) (n : ℕ) :
    A ^ n * B ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc A ^ (n + 1) * B ^ (n + 1) = A ^ n * (A * B) * B ^ n := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
      _ = A ^ n * B ^ n := by rw [h, mul_one]
      _ = 1 := ih

/-- The monoid of Clifford+T words on one qubit. -/
noncomputable def cliffordT : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) :=
  Submonoid.closure {hGateM, tGateM}

/-- The limits of Clifford+T words: a closed submonoid of the `2 × 2` matrices. -/
noncomputable def cliffordTLim : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) :=
  cliffordT.topologicalClosure

theorem hGateM_mem : hGateM ∈ cliffordT := Submonoid.subset_closure (by simp)

theorem tGateM_mem : tGateM ∈ cliffordT := Submonoid.subset_closure (by simp)

theorem cliffordT_le_lim : cliffordT ≤ cliffordTLim := Submonoid.le_topologicalClosure _

theorem isClosed_cliffordTLim : IsClosed (cliffordTLim : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Submonoid.isClosed_topologicalClosure _

/-! ### A dense circle of angles fills the circle -/

/-- The rotations about a fixed axis by the integer multiples of an angle that is an irrational
multiple of `4π` are dense in the whole circle of rotations about that axis. -/
theorem mem_closure_range_axisRot_of_irrational {a b c θ : ℝ}
    (hirr : Irrational (θ / (4 * π))) (α : ℝ) :
    axisRot a b c α ∈ closure (Set.range fun k : ℤ => axisRot a b c ((k : ℝ) * θ)) := by
  set f : ℝ → Matrix (Fin 2) (Fin 2) ℂ := axisRot a b c with hf
  have hdense : Dense (AddSubgroup.closure {θ, 4 * π} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  have hsub : f '' (AddSubgroup.closure {θ, 4 * π} : Set ℝ)
      ⊆ Set.range fun k : ℤ => f ((k : ℝ) * θ) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp ht
    refine ⟨k, ?_⟩
    rw [← hkm, zsmul_eq_mul, zsmul_eq_mul, hf]
    exact (axisRot_add_int_mul_four_pi a b c ((k : ℝ) * θ) m).symm
  have hcl : f '' closure (AddSubgroup.closure {θ, 4 * π} : Set ℝ)
      ⊆ closure (f '' (AddSubgroup.closure {θ, 4 * π} : Set ℝ)) :=
    image_closure_subset_closure_image (continuous_axisRot a b c)
  have hmem : f α ∈ f '' closure (AddSubgroup.closure {θ, 4 * π} : Set ℝ) := by
    refine ⟨α, ?_, rfl⟩
    rw [hdense.closure_eq]
    trivial
  exact closure_mono hsub (hcl hmem)

theorem axisRot_int_mul_mem {K : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)} {a b c θ : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hg : axisRot a b c θ ∈ K)
    (hg' : axisRot a b c (-θ) ∈ K) (k : ℤ) : axisRot a b c ((k : ℝ) * θ) ∈ K := by
  induction k using Int.induction_on with
  | zero =>
    simp only [Int.cast_zero, zero_mul, axisRot_zero]
    exact K.one_mem
  | succ n ih =>
    push_cast
    rw [show ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ by ring, axisRot_add hu]
    exact mul_mem (by push_cast at ih; exact ih) hg
  | pred n ih =>
    push_cast
    rw [show (-(n : ℝ) - 1) * θ = -(n : ℝ) * θ + -θ by ring, axisRot_add hu]
    exact mul_mem (by push_cast at ih; exact ih) hg'

/-- ★ **One rotation with an irrationally related angle gives the whole circle**, inside any closed
submonoid that contains it and its inverse. -/
theorem axisRot_mem_of_irrational {K : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : IsClosed (K : Set (Matrix (Fin 2) (Fin 2) ℂ))) {a b c θ : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hirr : Irrational (θ / (4 * π)))
    (hg : axisRot a b c θ ∈ K) (hg' : axisRot a b c (-θ) ∈ K) (α : ℝ) :
    axisRot a b c α ∈ K := by
  refine hK.closure_subset_iff.mpr ?_ (mem_closure_range_axisRot_of_irrational hirr α)
  rintro y ⟨k, rfl⟩
  exact axisRot_int_mul_mem hu hg hg' k

/-! ### The two circles the words reach -/

theorem wAxis_unit : (Real.sqrt 2 / 2) ^ 2 + (0 : ℝ) ^ 2 + (-(Real.sqrt 2 / 2)) ^ 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

theorem uAxis_unit : (Real.sqrt 2 / 2) ^ 2 + (0 : ℝ) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

theorem sqrt_two_inv_eq : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith [h2]

/-- `H` is the `π` rotation about `(1, 0, 1)/√2`, up to the phase `i`. -/
theorem hGateM_eq_smul_su2 :
    hGateM = Complex.I • su2 0 ((Real.sqrt 2)⁻¹) 0 ((Real.sqrt 2)⁻¹) := by
  rw [hGateM, su2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]

/-- ★ **The second axis.** The `π` rotation about the word's axis, followed by `H`, is (up to the
phase `i`) a rotation about `(1, 0, -1)/√2` — the cross product of the two axes — through
`wAngle`. -/
theorem axisRot_htAxis_pi_mul_hGateM :
    axisRot htA htB htA π * hGateM
      = Complex.I • axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) wAngle := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hGateM_eq_smul_su2, sqrt_two_inv_eq, axisRot, axisRot, Real.cos_pi_div_two,
    Real.sin_pi_div_two, cos_wAngle_half, sin_wAngle_half, wHalfCos, Matrix.mul_smul, su2_mul]
  congr 1
  congr 1 <;> nlinarith [h2]

/-! ### The first circle is reached by the word's powers -/

theorem htht_mem : htht ∈ cliffordT := by
  rw [htht]
  exact mul_mem (mul_mem (mul_mem tGateM_mem hGateM_mem) tGateM_mem) hGateM_mem

theorem hthtInv_mem : hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7 ∈ cliffordT :=
  mul_mem (mul_mem (mul_mem hGateM_mem (pow_mem tGateM_mem 7)) hGateM_mem)
    (pow_mem tGateM_mem 7)

theorem htht_mul_inv : htht * (hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7) = 1 := by
  have hh : hGateM * hGateM = 1 := hGateM_mul_self
  have ht8 : tGateM * tGateM ^ 7 = 1 := by
    rw [← pow_succ' tGateM 7, show 7 + 1 = 8 from rfl]
    exact tGateM_pow_eight
  rw [htht]
  simp only [mul_assoc]
  rw [← mul_assoc hGateM hGateM, hh, one_mul, ← mul_assoc tGateM (tGateM ^ 7), ht8, one_mul,
    ← mul_assoc hGateM hGateM, hh, one_mul]
  exact ht8

theorem axisRot_htAxis_eight : axisRot htA htB htA (8 * htAngle) = htht ^ 8 := by
  rw [htht_pow, tPhase_pow_eight, one_smul]
  norm_num

theorem axisRot_htAxis_eight_mem : axisRot htA htB htA (8 * htAngle) ∈ cliffordTLim := by
  rw [axisRot_htAxis_eight]
  exact cliffordT_le_lim (pow_mem htht_mem 8)

theorem axisRot_htAxis_neg_eight_mem :
    axisRot htA htB htA (-(8 * htAngle)) ∈ cliffordTLim := by
  have h1 : axisRot htA htB htA (8 * htAngle)
      * (hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7) ^ 8 = 1 := by
    rw [axisRot_htAxis_eight]
    exact pow_mul_pow_eq_one htht_mul_inv 8
  have h2 : axisRot htA htB htA (8 * htAngle) * axisRot htA htB htA (-(8 * htAngle)) = 1 := by
    rw [← axisRot_add htAxis_unit]
    simp
  rw [(Matrix.inv_eq_right_inv h2).symm.trans (Matrix.inv_eq_right_inv h1)]
  exact cliffordT_le_lim (pow_mem hthtInv_mem 8)

theorem irrational_eight_htAngle : Irrational ((8 * htAngle) / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_htAngle_div_four_pi ⟨q / 8, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- ★★ **Every rotation about the word's own axis is a limit of Clifford+T words.** -/
theorem axisRot_htAxis_mem (α : ℝ) : axisRot htA htB htA α ∈ cliffordTLim :=
  axisRot_mem_of_irrational isClosed_cliffordTLim htAxis_unit irrational_eight_htAngle
    axisRot_htAxis_eight_mem axisRot_htAxis_neg_eight_mem α

/-! ### The second circle -/

theorem piRot_mul_hGateM_mem : axisRot htA htB htA π * hGateM ∈ cliffordTLim :=
  mul_mem (axisRot_htAxis_mem π) (cliffordT_le_lim hGateM_mem)

theorem hGateM_mul_piRot_mem : hGateM * axisRot htA htB htA (-π) ∈ cliffordTLim :=
  mul_mem (cliffordT_le_lim hGateM_mem) (axisRot_htAxis_mem (-π))

theorem piRot_mul_hGateM_mul_inv :
    (axisRot htA htB htA π * hGateM) * (hGateM * axisRot htA htB htA (-π)) = 1 := by
  calc (axisRot htA htB htA π * hGateM) * (hGateM * axisRot htA htB htA (-π))
      = axisRot htA htB htA π * (hGateM * hGateM) * axisRot htA htB htA (-π) := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [hGateM_mul_self, mul_one, ← axisRot_add htAxis_unit]
        simp

theorem axisRot_wAxis_four :
    (axisRot htA htB htA π * hGateM) ^ 4
      = axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle) := by
  rw [axisRot_htAxis_pi_mul_hGateM, smul_pow,
    show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num,
    one_smul, show (4 : ℝ) * wAngle = ((4 : ℕ) : ℝ) * wAngle by norm_num,
    axisRot_nat_mul wAxis_unit]

theorem irrational_four_wAngle : Irrational ((4 * wAngle) / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_wAngle_div_four_pi ⟨q / 4, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- ★★ **Every rotation about `(1, 0, -1)/√2` is a limit of Clifford+T words.** -/
theorem axisRot_wAxis_mem (α : ℝ) :
    axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) α ∈ cliffordTLim := by
  refine axisRot_mem_of_irrational isClosed_cliffordTLim wAxis_unit irrational_four_wAngle ?_ ?_ α
  · rw [← axisRot_wAxis_four]
    exact pow_mem piRot_mul_hGateM_mem 4
  · have h1 : axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle)
        * (hGateM * axisRot htA htB htA (-π)) ^ 4 = 1 := by
      rw [← axisRot_wAxis_four]
      exact pow_mul_pow_eq_one piRot_mul_hGateM_mul_inv 4
    have h2 : axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle)
        * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (-(4 * wAngle)) = 1 := by
      rw [← axisRot_add wAxis_unit]
      simp
    rw [(Matrix.inv_eq_right_inv h2).symm.trans (Matrix.inv_eq_right_inv h1)]
    exact pow_mem hGateM_mul_piRot_mem 4

/-! ### The third circle: conjugating by `Z` -/

/-- `Z`, as the fourth power of `T`. -/
noncomputable def zGateM : Matrix (Fin 2) (Fin 2) ℂ := tGateM ^ 4

theorem tPhase_pow_four : tPhase ^ 4 = -1 := by
  have h : tPhase ^ 2 = Complex.I := by
    rw [pow_two]
    exact tPhase_sq
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, Complex.I_sq]

theorem zGateM_eq : zGateM = !![1, 0; 0, -1] := by
  rw [zGateM, tGateM_pow, tPhase_pow_four]

theorem zGateM_conj_su2 (w x y z : ℝ) :
    zGateM * su2 w x y z * zGateM = su2 w (-x) (-y) z := by
  rw [zGateM_eq, su2, su2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

theorem zGateM_conj_axisRot (α : ℝ) :
    zGateM * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (-α) * zGateM
      = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) α := by
  rw [axisRot, zGateM_conj_su2, axisRot, show -α / 2 = -(α / 2) by ring, Real.cos_neg,
    Real.sin_neg]
  congr 1 <;> ring

/-- ★★ **Every rotation about `(1, 0, 1)/√2` is a limit of Clifford+T words** — the `Z` conjugate of
the second circle, and the axis orthogonal to it. -/
theorem axisRot_uAxis_mem (α : ℝ) :
    axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) α ∈ cliffordTLim := by
  have hz : zGateM ∈ cliffordTLim := cliffordT_le_lim (pow_mem tGateM_mem 4)
  rw [← zGateM_conj_axisRot α]
  exact mul_mem (mul_mem hz (axisRot_wAxis_mem (-α))) hz

/-! ### Clifford+T fills `SU(2)` -/

/-- ★★ **Every determinant-one `2 × 2` unitary is a limit of Clifford+T words.** The two circles
`(1, 0, ±1)/√2` are orthogonal, so the Euler decomposition about them writes any such unitary as a
product of three rotations, each of them a limit of words. -/
theorem det_one_mem_cliffordTLim {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) : U ∈ cliffordTLim := by
  obtain ⟨β, γ, δ, hU'⟩ := exists_euler_two_axes hU hdet
  rw [hU']
  exact mul_mem (mul_mem (axisRot_uAxis_mem β) (axisRot_wAxis_mem γ)) (axisRot_uAxis_mem δ)

/-- ★★ **Clifford+T is dense in `U(2)` modulo phase**: every `2 × 2` unitary becomes a limit of
Clifford+T words after multiplication by one phase. -/
theorem exists_phase_mem_cliffordTLim {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ φ : ℝ, Euler.expI φ • U ∈ cliffordTLim := by
  obtain ⟨α, β, γ, δ, hU'⟩ := Euler.exists_euler hU
  refine ⟨-α, ?_⟩
  have hW : Euler.rzMat β * Euler.ryMat γ * Euler.rzMat δ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.rzMat_mem_unitaryGroup β) (Euler.ryMat_mem_unitaryGroup γ))
      (Euler.rzMat_mem_unitaryGroup δ)
  rw [hU', smul_smul, ← Euler.expI_add, show -α + α = 0 by ring, Euler.expI_zero, one_smul]
  exact det_one_mem_cliffordTLim hW (Euler.rz_ry_rz_det β γ δ)

end SU2

end QuantumInfo
