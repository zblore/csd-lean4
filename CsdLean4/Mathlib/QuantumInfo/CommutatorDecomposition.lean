/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.SU2Rotation
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The commutator decomposition: a small rotation is a commutator of two `√ε` rotations

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #114, the third brick of #74's split.

#112 proved that a commutator of two near-identity unitaries is *quadratically* nearer the identity.
This file proves the converse direction the Solovay–Kitaev recursion needs: a rotation by a small
angle **is** such a commutator, with both factors `O(√ε)` from the identity. Together the two make
the iteration contract.

Everything runs on the quaternion product `su2_mul`, so the matrix work is real algebra.

## What is proved

* ★★★ `exists_commutator_of_det_one` — **the target: every determinant-one unitary is a group
  commutator of two unitaries within `√2·√‖U - 1‖` of the identity**, with the commutator *exact*.
  Read with #112's contraction, that is the Solovay-Kitaev step in both directions. **The two factors
  are themselves determinant one** (`SU2Rotation.axisRot_det`, `det_conj_of_mem_unitary`), which the construction
  always produced and the statement records since #116 — that is what lets the Solovay-Kitaev
  recursion re-enter itself on them;
* ★★ `norm_su2_sub_one` — **the distance to the identity is `√(2 - 2w)`**, where `w` is the scalar
  part: `star M * M` is a *scalar* for `M = su2 w x y z - 1`, so the C\*-identity `‖M‖² = ‖M⋆M‖` gives
  the norm with no eigenvalue computation. For a rotation this is ★ `norm_axisRot_sub_one`;
* ★★★ `skComm_eq` — **the exact commutator identity**: for `V` the rotation by `φ` about `x̂` and `W`
  the rotation by `φ` about `ŷ`, `V W V⋆ W⋆ = su2 (1 - 2s⁴) (2cs³) (-2cs³) (2c²s²)` with
  `c = cos(φ/2)`, `s = sin(φ/2)`. The scalar part is the angle relation — **quartic in `s`, hence
  quadratic in the angle** — and the rest is the axis, which depends on `φ`;
* ★★ `norm_skComm_sub_one` = `2sin²(φ/2)`, ★★★ `norm_skV_sub_one_le` — **the `√2·√ε` bound** — and
  ★★★ `exists_skComm_norm_eq`: every distance in `[0, 2]` is realised **exactly**, at factor angle
  `2 arcsin √(ε/2)`;
* ★★ `exists_su2_of_det_one` — **the `su2` parametrisation is onto the determinant-one unitaries**
  (the surjectivity #113 found missing): for `det U = 1` the inverse is the adjugate and for a unitary
  it is the adjoint, so comparing them forces `U 1 1 = conj (U 0 0)` and `U 1 0 = -conj (U 0 1)`,
  which is exactly the shape `su2` has;
* ★★ `su2_conj_pure` — **conjugating by a `π`-rotation reflects the axis**, `v ↦ 2(m̂·v)m̂ - v`, and
  ★★ `bisector_reflect` — **the bisector reflection swaps two vectors of equal length**, so the axis
  can be moved anywhere except to its exact opposite. ★ `star_groupCommutator` disposes of that last
  case: the opposite axis belongs to the *adjoint* of the commutator, which is the same pair in the
  other order — **no perpendicular-vector construction is needed anywhere**;
* ★★ `norm_conj_sub_one` and ★★ `conj_groupCommutator` — the transport: conjugation changes no
  distance to the identity, and a conjugate of a commutator is the commutator of the conjugates.

## Honest scope

⚠️ **`V` and `W` are unitaries, not gate words.** The commutator is exact and the factors are
rotations; nothing here expresses them in a generating set. That is the division of labour the
algorithm needs — the net (#113) supplies words, the recursion (#115) approximates these factors by
them — and it means this row alone implies no gate count.

⚠️ **Determinant one, and `2 × 2`.** A general unitary needs a phase, exactly as in #81; nothing is
claimed for `U(2)` modulo phase here, and nothing in higher dimension.

⚠️ **The constant is `√2`, and it is not claimed optimal.** It comes from
`sin(φ/4) ≤ sin(φ/2) = √(sin(θ/4))`, which is lossy by design: the Solovay-Kitaev exponent does not
depend on it.

⚠️ **The factor bound needs `0 ≤ φ ≤ π`** for the standard pair, which is where the sign analysis
`(2c + 1)(c - 1) ≤ 0` holds; `exists_skComm_norm_eq` only ever produces angles in that range.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
§4 (the group-commutator decomposition); M. Nielsen, I. Chuang, *Quantum Computation and Quantum
Information*, Appendix 3; `SU2Rotation.lean` (#80, `su2`, `su2_mul`, `axisRot`),
`GroupCommutator.lean` (#112); `specs/BACKLOG.md` #114, #74, #112, #113, #115, #116.
-/

@[expose] public section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace QuantumInfo.SU2

/-! ### The quaternion conjugate, and the distance to the identity -/

theorem su2_star (w x y z : ℝ) : star (su2 w x y z) = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Matrix.star_apply, Complex.ext_iff]

theorem su2_star_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z) * su2 w x y z = 1 := by
  rw [su2_star, su2_mul, ← su2_one]
  congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)

theorem su2_add_star (w x y z : ℝ) :
    su2 w x y z + star (su2 w x y z) = ((2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [su2_star]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff] <;> ring

theorem star_su2_sub_one_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z - 1) * (su2 w x y z - 1)
      = ((2 - 2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have key : star (su2 w x y z - 1) * (su2 w x y z - 1)
      = star (su2 w x y z) * su2 w x y z + 1 - (su2 w x y z + star (su2 w x y z)) := by
    rw [star_sub, star_one]
    noncomm_ring
  rw [key, su2_star_mul_self hu, su2_add_star]
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 = ((2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    push_cast
    rw [two_smul]
  rw [h2, ← sub_smul]
  congr 1
  push_cast
  ring

/-- ★★ **The distance to the identity is `√(2 − 2w)`**, with `w` the scalar part. `star M * M` is a
scalar multiple of `1`, so the C\*-identity `‖M‖² = ‖M⋆M‖` settles the norm without computing any
eigenvalue. -/
theorem norm_su2_sub_one {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ‖su2 w x y z - 1‖ = Real.sqrt (2 - 2 * w) := by
  have hw : w ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hw' : w ≤ 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hsq : ‖su2 w x y z - 1‖ * ‖su2 w x y z - 1‖ = 2 - 2 * w := by
    rw [← CStarRing.norm_star_mul_self, star_su2_sub_one_mul_self hu, norm_smul, norm_one,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [← Real.sqrt_mul_self (norm_nonneg (su2 w x y z - 1)), hsq]

/-- ★ **The distance from a rotation to the identity.** -/
theorem norm_axisRot_sub_one {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    ‖axisRot a b c θ - 1‖ = Real.sqrt (2 - 2 * Real.cos (θ / 2)) := by
  rw [axisRot]
  refine norm_su2_sub_one ?_
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [hu, h]

/-! ### The commutator of two rotations about orthogonal axes -/

/-- The first factor of the standard pair: rotation by `φ` about `x̂`. -/
noncomputable def skV (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 1 0 0 φ

/-- The second factor of the standard pair: rotation by `φ` about `ŷ`. -/
noncomputable def skW (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 1 0 φ

/-- The group commutator of the standard pair. `star` is the inverse here, both factors being unit
quaternions. -/
noncomputable def skComm (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  skV φ * skW φ * star (skV φ) * star (skW φ)

/-- ★★★ **The exact commutator identity.** With `c = cos(φ/2)` and `s = sin(φ/2)`, the commutator of
the two standard rotations is the unit quaternion `(1 - 2s⁴, 2cs³, -2cs³, 2c²s²)`.

The scalar part `1 - 2s⁴` is the angle relation — **quartic in `s`, hence quadratic in the angle** —
and the three vector components are the axis, which depends on `φ` and is *not* `x̂`, `ŷ` or their
cross product. Only `su2_mul` is used: the matrix work is quaternion algebra. -/
theorem skComm_eq (φ : ℝ) :
    skComm φ = su2 (1 - 2 * Real.sin (φ / 2) ^ 4)
      (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
  rw [skComm, skV, skW, axisRot, axisRot, su2_star, su2_star, su2_mul, su2_mul, su2_mul]
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  congr 1
  · linear_combination (s ^ 2 + c ^ 2 + 1) * h
  · ring
  · ring
  · ring

/-- The commutator is a unit quaternion. -/
theorem skComm_unit (φ : ℝ) :
    (1 - 2 * Real.sin (φ / 2) ^ 4) ^ 2 + (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  linear_combination (4 * s ^ 4 * (s ^ 2 + c ^ 2 + 1)) * h

/-- ★★ **The commutator's distance to the identity is `2sin²(φ/2)`** — quadratic in the factors'
angle, which is #112's contraction seen from the other side. -/
theorem norm_skComm_sub_one (φ : ℝ) : ‖skComm φ - 1‖ = 2 * Real.sin (φ / 2) ^ 2 := by
  rw [skComm_eq, norm_su2_sub_one (skComm_unit φ),
    show (2 : ℝ) - 2 * (1 - 2 * Real.sin (φ / 2) ^ 4)
      = (2 * Real.sin (φ / 2) ^ 2) ^ 2 from by ring]
  exact Real.sqrt_sq (by positivity)

/-- The factors' distance to the identity. -/
theorem norm_skV_sub_one (φ : ℝ) :
    ‖skV φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skV]
  exact norm_axisRot_sub_one (by norm_num) φ

theorem norm_skW_sub_one (φ : ℝ) :
    ‖skW φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skW]
  exact norm_axisRot_sub_one (by norm_num) φ

/-! ### The square-root bound -/

/-- ★★★ **The factors are within `√2·√ε` of the identity**, where `ε` is the commutator's own
distance. This is the half of Solovay-Kitaev that #112 does not give: not only is a commutator of
small things smaller, but the factors needed to *produce* a given smallness are only square-root
large. -/
theorem norm_skV_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  have hpi' := Real.pi_pos
  have hs : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc1 : Real.cos (φ / 2) ≤ 1 := Real.cos_le_one _
  have hsc : Real.sin (φ / 2) ^ 2 = 1 - Real.cos (φ / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (φ / 2)]
  rw [norm_skV_sub_one, norm_skComm_sub_one, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [show (2 : ℝ) * (2 * Real.sin (φ / 2) ^ 2) = 4 * Real.sin (φ / 2) ^ 2 from by ring, hsc]
  nlinarith [hc, hc1]

theorem norm_skW_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  rw [norm_skW_sub_one, ← norm_skV_sub_one]
  exact norm_skV_sub_one_le h0 hpi

/-- ★★★ **Every distance in `[0, 2]` is realised by an exact commutator whose factors are
`√2·√ε`-close to the identity.** The accuracy is attained exactly, not approached: the factors'
angle is `2 arcsin √(ε/2)`. -/
theorem exists_skComm_norm_eq {ε : ℝ} (h0 : 0 ≤ ε) (h2 : ε ≤ 2) :
    ∃ φ : ℝ, 0 ≤ φ ∧ φ ≤ Real.pi ∧ ‖skComm φ - 1‖ = ε ∧
      ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε ∧ ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε := by
  have hhalf : Real.sqrt (ε / 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hnn : 0 ≤ Real.sqrt (ε / 2) := Real.sqrt_nonneg _
  have harc0 : 0 ≤ Real.arcsin (Real.sqrt (ε / 2)) := Real.arcsin_nonneg.2 hnn
  have harc1 : Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have h0φ : (0 : ℝ) ≤ 2 * Real.arcsin (Real.sqrt (ε / 2)) := by linarith
  have hpiφ : 2 * Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi := by linarith
  have hsin : Real.sin (2 * Real.arcsin (Real.sqrt (ε / 2)) / 2) = Real.sqrt (ε / 2) := by
    rw [show 2 * Real.arcsin (Real.sqrt (ε / 2)) / 2 = Real.arcsin (Real.sqrt (ε / 2)) from by
      ring]
    exact Real.sin_arcsin (by linarith) hhalf
  have hnorm : ‖skComm (2 * Real.arcsin (Real.sqrt (ε / 2))) - 1‖ = ε := by
    rw [norm_skComm_sub_one, hsin, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨2 * Real.arcsin (Real.sqrt (ε / 2)), h0φ, hpiφ, hnorm, ?_, ?_⟩
  · have hV := norm_skV_sub_one_le h0φ hpiφ
    rwa [hnorm] at hV
  · have hW := norm_skW_sub_one_le h0φ hpiφ
    rwa [hnorm] at hW

/-! ### Every determinant-one unitary is a unit quaternion -/

/-- ★★ **The `su2` parametrisation is onto the determinant-one unitaries.** For `det U = 1` the
inverse is the adjugate, and for a unitary it is the adjoint, so comparing the two gives
`U 1 1 = conj (U 0 0)` and `U 1 0 = -conj (U 0 1)` — which is exactly the shape `su2` has.

This is the surjectivity #113 found missing. -/
theorem exists_su2_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ w x y z : ℝ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ U = su2 w x y z := by
  have hstar : U⁻¹ = star U :=
    Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hU)
  have hadj : U⁻¹ = U.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have hkey : star U = !![U 1 1, -U 0 1; -U 1 0, U 0 0] := by
    rw [← hstar, hadj, Matrix.adjugate_fin_two]
  have h11 : U 1 1 = starRingEnd ℂ (U 0 0) := by
    have h : (star U) 0 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination -h
  have h10 : U 1 0 = -starRingEnd ℂ (U 0 1) := by
    have h : (star U) 1 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination h
  have hrow : U 0 0 * starRingEnd ℂ (U 0 0) + U 0 1 * starRingEnd ℂ (U 0 1) = 1 := by
    have h : (U * star U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      rw [Unitary.mul_star_self_of_mem hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h
    linear_combination h
  have hrow' : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj] at hrow
    exact_mod_cast hrow
  refine ⟨(U 0 0).re, -(U 0 1).im, -(U 0 1).re, -(U 0 0).im, ?_, ?_⟩
  · simp only [Complex.normSq_apply] at hrow'
    nlinarith [hrow']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [su2, h11, h10, Complex.ext_iff]

/-! ### Moving the axis: conjugation by a `π`-rotation reflects it -/

/-- ★★ **Conjugating by a `π`-rotation about `m̂` reflects the vector part in `m̂`**, fixing the
scalar part: `v ↦ 2(m̂·v)m̂ − v`. The `π`-rotation about `m̂` is the *pure* unit quaternion
`su2 0 m₁ m₂ m₃`, and this is the whole conjugacy engine: a reflection in the bisector of two axes
swaps them. -/
theorem su2_conj_pure {m₁ m₂ m₃ : ℝ} (hm : m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1) (w x y z : ℝ) :
    su2 0 m₁ m₂ m₃ * su2 w x y z * star (su2 0 m₁ m₂ m₃)
      = su2 w (2 * (m₁ * x + m₂ * y + m₃ * z) * m₁ - x)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₂ - y)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₃ - z) := by
  rw [su2_star, su2_mul, su2_mul]
  congr 1
  · linear_combination w * hm
  · linear_combination (-x) * hm
  · linear_combination (-y) * hm
  · linear_combination (-z) * hm

/-- A unit quaternion is a unitary matrix. -/
theorem su2_mem_unitary {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    su2 w x y z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine Unitary.mem_iff.2 ⟨su2_star_mul_self hu, ?_⟩
  rw [su2_star, su2_mul, ← su2_one]
  congr 1
  · linear_combination hu
  · ring
  · ring
  · ring

theorem axisRot_mem_unitary {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    axisRot a b c θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [axisRot]
  refine su2_mem_unitary ?_
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [hu, h]

/-- ★★ **The bisector reflection swaps two vectors of equal length.** No normalisation is needed: the
same bisector works at any common length, which is what keeps the assembly free of axis arithmetic.
The hypothesis is exactly that the two are not opposite. -/
theorem bisector_reflect {p₁ p₂ p₃ n₁ n₂ n₃ ρ : ℝ} (hp : p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 = ρ)
    (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = ρ)
    (hsum : 0 < (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2) :
    ∃ m₁ m₂ m₃ : ℝ, m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1 ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₁ - p₁ = n₁ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₂ - p₂ = n₂ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₃ - p₃ = n₃ := by
  obtain ⟨r, hrpos, hr⟩ : ∃ r : ℝ, 0 < r ∧
      r ^ 2 = (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2 :=
    ⟨Real.sqrt ((p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2), Real.sqrt_pos.2 hsum,
      Real.sq_sqrt (le_of_lt hsum)⟩
  have hrne : r ≠ 0 := ne_of_gt hrpos
  refine ⟨(p₁ + n₁) / r, (p₂ + n₂) / r, (p₃ + n₃) / r, ?_, ?_, ?_, ?_⟩
  · field_simp
    rw [hr]
  · field_simp
    rw [hr]
    linear_combination (p₁ + n₁) * hp - (p₁ + n₁) * hn
  · field_simp
    rw [hr]
    linear_combination (p₂ + n₂) * hp - (p₂ + n₂) * hn
  · field_simp
    rw [hr]
    linear_combination (p₃ + n₃) * hp - (p₃ + n₃) * hn

/-! ### Transport along a unitary conjugation -/

/-- ★★ **Conjugating by a unitary changes no distance to the identity.** -/
theorem norm_conj_sub_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] {S : E}
    (hS : S ∈ unitary E) (K : E) : ‖S * K * star S - 1‖ = ‖K - 1‖ := by
  have hexp : S * (K - 1) * star S = S * K * star S - S * star S := by noncomm_ring
  have h1 : S * K * star S - 1 = S * (K - 1) * star S := by
    rw [hexp, Unitary.mul_star_self_of_mem hS]
  rw [h1, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hS),
    CStarRing.norm_mem_unitary_mul _ hS]

/-- ★★ **A conjugate of a commutator is the commutator of the conjugates**, so a decomposition at
one axis transports to every unitary conjugate of it — and by `norm_conj_sub_one` the factors keep
their distances. This is the consumer for the missing same-angle conjugacy step. -/
theorem conj_groupCommutator {E : Type*} [Monoid E] [StarMul E] {S : E} (hS : S ∈ unitary E)
    (V W : E) :
    (S * V * star S) * (S * W * star S) * star (S * V * star S) * star (S * W * star S)
      = S * (V * W * star V * star W) * star S := by
  have hss : star S * S = 1 := Unitary.star_mul_self_of_mem hS
  have hsv : star (S * V * star S) = S * star V * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  have hsw : star (S * W * star S) = S * star W * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  rw [hsv, hsw]
  calc S * V * star S * (S * W * star S) * (S * star V * star S) * (S * star W * star S)
      = S * V * (star S * S) * W * (star S * S) * star V * (star S * S) * star W * star S := by
        noncomm_ring
    _ = S * (V * W * star V * star W) * star S := by
        rw [hss]
        noncomm_ring

/-- ★ **The adjoint of a group commutator is the commutator of the same pair, swapped.** This is what
removes the antipodal case from the axis argument: an axis opposite the standard commutator's belongs
to its adjoint, which is the same two factors in the other order. -/
theorem star_groupCommutator {E : Type*} [Monoid E] [StarMul E] (V W : E) :
    star (V * W * star V * star W) = W * V * star W * star V := by
  simp only [star_mul, star_star]
  noncomm_ring

/-! ### The theorem: every determinant-one unitary is such a commutator -/

/-- Conjugation by a unitary leaves the determinant alone. -/
theorem det_conj_of_mem_unitary {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (S * X * star S).det = X.det := by
  have hone : S.det * (star S).det = 1 := by
    rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem hS, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc S.det * X.det * (star S).det = S.det * (star S).det * X.det := by ring
    _ = X.det := by rw [hone, one_mul]


/-- ★★★ **#114's target: every determinant-one unitary is a group commutator of two unitaries that
are only square-root far from the identity.**

`‖V - 1‖, ‖W - 1‖ ≤ √2·√‖U - 1‖`, with the commutator *exact*. Read with #112's contraction this is
the Solovay-Kitaev step in both directions: the commutator of two `δ`-close unitaries is `2δ²`-close,
and every `ε`-close unitary is the commutator of two `√(2ε)`-close ones.

The proof assembles the file: `exists_su2_of_det_one` writes `U` as a unit quaternion;
`exists_skComm_norm_eq` produces a standard-pair commutator at exactly the same distance, hence
(by `norm_su2_sub_one`) with the same scalar part; the vector parts then have the same length, so
`bisector_reflect` and `su2_conj_pure` rotate one onto the other unless they are opposite — and in
that case `U` is the *adjoint* of the commutator, which is the same pair in the other order. -/
theorem exists_commutator_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : U.det = 1) :
    ∃ V W : Matrix (Fin 2) (Fin 2) ℂ,
      V ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ W ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧
      V.det = 1 ∧ W.det = 1 ∧
      U = V * W * star V * star W ∧
      ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ ∧
      ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ := by
  obtain ⟨w, x, y, z, hunit, hUeq⟩ := exists_su2_of_det_one hU hdet
  have hw1 : w ≤ 1 := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hwm1 : -1 ≤ w := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hnormU : ‖U - 1‖ = Real.sqrt (2 - 2 * w) := by
    rw [hUeq]
    exact norm_su2_sub_one hunit
  have hε0 : (0 : ℝ) ≤ ‖U - 1‖ := norm_nonneg _
  have hε2 : ‖U - 1‖ ≤ 2 := by
    rw [hnormU]
    calc Real.sqrt (2 - 2 * w) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num)
  obtain ⟨φ, hφ0, hφpi, hφnorm, hVb, hWb⟩ := exists_skComm_norm_eq hε0 hε2
  -- the scalar parts agree
  have h2s : 2 * Real.sin (φ / 2) ^ 2 = ‖U - 1‖ := by
    rw [← hφnorm, norm_skComm_sub_one]
  have hsq : (2 * Real.sin (φ / 2) ^ 2) ^ 2 = 2 - 2 * w := by
    rw [h2s, hnormU, Real.sq_sqrt hnn]
  have hw' : w = 1 - 2 * Real.sin (φ / 2) ^ 4 := by nlinarith [hsq]
  -- the commutator as a quaternion with the same scalar part
  have hKeq : skComm φ = su2 w (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
    rw [skComm_eq, hw']
  have hKunit := skComm_unit φ
  rw [← hw'] at hKunit
  -- the two vector parts have the same length
  have hlenU : x ^ 2 + y ^ 2 + z ^ 2 = 1 - w ^ 2 := by linarith [hunit]
  have hlenK : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 - w ^ 2 := by
    nlinarith [hKunit]
  have hVu : skV φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skV]; exact axisRot_mem_unitary (by norm_num) φ
  have hWu : skW φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skW]; exact axisRot_mem_unitary (by norm_num) φ
  by_cases hopp : (0 : ℝ) < (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2
  · -- the generic case: rotate the commutator's axis onto `U`'s
    obtain ⟨m₁, m₂, m₃, hm, hr₁, hr₂, hr₃⟩ := bisector_reflect hlenK hlenU hopp
    have hSu : su2 0 m₁ m₂ m₃ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
      su2_mem_unitary (by linarith)
    have hconj : su2 0 m₁ m₂ m₃ * skComm φ * star (su2 0 m₁ m₂ m₃) = U := by
      rw [hKeq, su2_conj_pure hm, hUeq, hr₁, hr₂, hr₃]
    refine ⟨su2 0 m₁ m₂ m₃ * skV φ * star (su2 0 m₁ m₂ m₃),
      su2 0 m₁ m₂ m₃ * skW φ * star (su2 0 m₁ m₂ m₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_mem (mul_mem hSu hVu) (Unitary.star_mem hSu)
    · exact mul_mem (mul_mem hSu hWu) (Unitary.star_mem hSu)
    · rw [det_conj_of_mem_unitary hSu, skV, axisRot_det (by norm_num)]
    · rw [det_conj_of_mem_unitary hSu, skW, axisRot_det (by norm_num)]
    · rw [conj_groupCommutator hSu, ← skComm, hconj]
    · rw [norm_conj_sub_one hSu]
      exact hVb
    · rw [norm_conj_sub_one hSu]
      exact hWb
  · -- the opposite case: `U` is the adjoint of the commutator, i.e. the same pair swapped
    have hzero : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      have hge : (0 : ℝ) ≤ (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
          + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
          + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 := by positivity
      linarith [not_lt.1 hopp]
    have hsq1 : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq2 : (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq3 : (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hx : x = -(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) := by
      have h := sq_eq_zero_iff.1 hsq1
      linarith
    have hy : y = 2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 := by
      have h := sq_eq_zero_iff.1 hsq2
      linarith
    have hz : z = -(2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
      have h := sq_eq_zero_iff.1 hsq3
      linarith
    have hUstar : U = star (skComm φ) := by
      rw [hKeq, su2_star, hUeq, hx, hy, hz]
      congr 1
      ring
    refine ⟨skW φ, skV φ, hWu, hVu, ?_, ?_, ?_, ?_, ?_⟩
    · rw [skW, axisRot_det (by norm_num)]
    · rw [skV, axisRot_det (by norm_num)]
    · rw [hUstar, skComm, star_groupCommutator]
    · exact hWb
    · exact hVb

end QuantumInfo.SU2

end
