/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.SU2Rotation

/-!
# The `z`-`y`-`z` Euler decomposition of a `2 × 2` unitary, and the `ABC` identity

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #84, part (e2) of `R-005`
(`specs/magic-plan.md`, "The split"); the piece #81 and #85 share.

Nielsen–Chuang Theorem 4.1: **every `2 × 2` unitary is a phase times a product of three rotations
about the `z`, `y` and `z` axes** — ★★ `exists_euler`. The proof is the textbook trigonometry, with
one economy: passing to determinant one first (★★ `exists_euler_of_det_one`) leaves only *two*
entries to match, because a determinant-one unitary is `!![a, -star b; b, star a]`
(`adjugate_entries`, from `Uᴴ = adjugate U`). Writing `a` and `b` in polar form then gives the three
angles outright,
`γ = 2 arccos ‖a‖`, `β = arg b - arg a`, `δ = -arg a - arg b`,
with **no case split**: where a column degenerates the matching entry is killed by
`cos (γ/2) = ‖a‖ = 0` or `sin (γ/2) = ‖b‖ = 0`, and `Complex.norm_mul_exp_arg_mul_I` holds at `0`
too.

Then Nielsen–Chuang Corollary 4.2, the `ABC` identity: ★ `abc_identity` and ★ `abc_prod_eq_one`
exhibit `A`, `B`, `C` with
`A X B X C = R_z(β) R_y(γ) R_z(δ)` and `A B C = 1`,
so ★★ `exists_abc` writes any `2 × 2` unitary as `e^{iα} · A X B X C` with `A B C = 1`. That is the
form a controlled gate needs: the `X`s become the two `CNOT`s of a one-control circuit, since the
control bit `0` leaves `A B C = 1` and the control bit `1` inserts them.

* `expI`, `expI_add`, `star_expI`, `polar`, `polar_star` — the unit circle written additively;
* `rzMat`, `ryMat` (`SU2.axisRot` about `z` and `y`), `rzMat_eq`, `ryMat_eq`, `rzMat_mul`,
  `ryMat_mul`, and their unitarity through the new `SU2.su2_mem_unitaryGroup`,
  `SU2.axisRot_mem_unitaryGroup`;
* `xMat`, `xMat_mul_self`, `xMat_conj_rzMat`, `xMat_conj_ryMat`, `xMat_conj_mul` — conjugation by
  `X` negates both angles, and distributes over products;
* ★ `rz_ry_rz_eq` — the Euler product as an explicit matrix;
* `normSq_col_zero`, `adjugate_entries` — what unitarity and `det = 1` give;
* ★★ `exists_euler_of_det_one`, ★★ `exists_euler`, ★ `abc_prod_eq_one`, ★ `abc_identity`,
  ★★ `exists_abc`.

## Honest scope

⚠️ This file is `2 × 2` matrices only. The circuit-level statement — that the one-control gate
`ctrlSet {a} j` of #83 is a product of two `CNOT`s and single-qubit gates — is
`CsdLean4/Mathlib/QuantumInfo/ControlledSingle.lean`, which turns `exists_abc` into that product.
⚠️ `expI t` is `Complex.exp (t * I)`, kept as a definition only to keep the entries of the rotation
matrices readable; upstream it would be `Circle.exp t`. Nothing here needs the circle group.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* Theorem 4.1
and Corollary 4.2 (§4.2, §4.3); `CsdLean4/Mathlib/QuantumInfo/SU2Rotation.lean` for the axis–angle
layer; `specs/magic-plan.md`; `specs/BACKLOG.md` #84, #81, #85; `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace SU2

/-! ### Unitarity of the quaternion matrices

The `2 × 2` layer of `SU2Rotation.lean` gains the three facts this file needs: a unit quaternion is
a unitary matrix.
-/

theorem su2_conjTranspose (w x y z : ℝ) : (su2 w x y z)ᴴ = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff]

/-- A **unit** quaternion is a unitary matrix. -/
theorem su2_mem_unitaryGroup {w x y z : ℝ} (h : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    su2 w x y z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, su2_conjTranspose, su2_mul]
  rw [show w * w - x * -x - y * -y - z * -z = 1 by linear_combination h,
    show w * -x + x * w + y * -z - z * -y = 0 by ring,
    show w * -y - x * -z + y * w + z * -x = 0 by ring,
    show w * -z + x * -y - y * -x + z * w = 0 by ring]
  exact su2_one

/-- A rotation about a unit axis is unitary. -/
theorem axisRot_mem_unitaryGroup {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    axisRot a b c θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [axisRot]
  refine su2_mem_unitaryGroup ?_
  linear_combination (Real.sin (θ / 2)) ^ 2 * hu + Real.sin_sq_add_cos_sq (θ / 2)

end SU2

namespace Euler

open SU2

/-! ### The unit circle, written additively -/

/-- `expI t = e^{it}`. A definition only so that the entries of the rotation matrices below read as
phases; upstream this is `Circle.exp t`. -/
noncomputable def expI (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] theorem expI_zero : expI 0 = 1 := by simp [expI]

theorem expI_add (s t : ℝ) : expI (s + t) = expI s * expI t := by
  simp [expI, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem expI_eq (t : ℝ) : expI t = (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
  rw [expI, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

@[simp] theorem star_expI (t : ℝ) : star (expI t) = expI (-t) := by
  simp [expI_eq, Complex.ext_iff, Real.cos_neg, Real.sin_neg]

@[simp] theorem expI_mul_neg (t : ℝ) : expI t * expI (-t) = 1 := by
  rw [← expI_add]
  simp

/-- The polar form of a complex number: `z = ‖z‖ e^{i arg z}`, at `z = 0` too. -/
theorem polar (z : ℂ) : (‖z‖ : ℂ) * expI z.arg = z :=
  Complex.norm_mul_exp_arg_mul_I z

/-- The polar form of the conjugate. -/
theorem polar_star (z : ℂ) : (‖z‖ : ℂ) * expI (-z.arg) = star z := by
  have h : star ((‖z‖ : ℂ) * expI z.arg) = star z := by rw [polar]
  rw [star_mul, star_expI, Complex.star_def, Complex.conj_ofReal] at h
  rw [Complex.star_def, ← h, mul_comm]

/-! ### The two rotations and the bit flip -/

/-- `R_z(β)`: the rotation by `β` about the `z` axis, `diag (e^{-iβ/2}, e^{iβ/2})`. -/
noncomputable def rzMat (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 0 1 β

/-- `R_y(γ)`: the rotation by `γ` about the `y` axis, the real rotation matrix. -/
noncomputable def ryMat (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 1 0 γ

/-- The `2 × 2` bit flip (`X`, the first Pauli matrix). -/
def xMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem rzMat_eq (β : ℝ) : rzMat β = !![expI (-(β / 2)), 0; 0, expI (β / 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzMat, axisRot, su2, expI_eq, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]

theorem ryMat_eq (γ : ℝ) :
    ryMat γ = !![(Real.cos (γ / 2) : ℂ), -(Real.sin (γ / 2) : ℂ);
                 (Real.sin (γ / 2) : ℂ), (Real.cos (γ / 2) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ryMat, axisRot, su2, Complex.ext_iff]

theorem rzMat_mul (s t : ℝ) : rzMat s * rzMat t = rzMat (s + t) :=
  (axisRot_add (by norm_num) s t).symm

theorem ryMat_mul (s t : ℝ) : ryMat s * ryMat t = ryMat (s + t) :=
  (axisRot_add (by norm_num) s t).symm

@[simp] theorem rzMat_zero : rzMat 0 = 1 := axisRot_zero 0 0 1

@[simp] theorem ryMat_zero : ryMat 0 = 1 := axisRot_zero 0 1 0

theorem rzMat_mem_unitaryGroup (β : ℝ) : rzMat β ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  axisRot_mem_unitaryGroup (by norm_num) β

theorem ryMat_mem_unitaryGroup (γ : ℝ) : ryMat γ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  axisRot_mem_unitaryGroup (by norm_num) γ

theorem xMat_mem_unitaryGroup : xMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem xMat_mul_self : xMat * xMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating by `X` negates a `z` rotation: `X R_z(β) X = R_z(-β)`. -/
theorem xMat_conj_rzMat (β : ℝ) : xMat * rzMat β * xMat = rzMat (-β) := by
  rw [rzMat_eq, rzMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two, neg_div, neg_neg]

/-- Conjugating by `X` negates a `y` rotation: `X R_y(γ) X = R_y(-γ)`. -/
theorem xMat_conj_ryMat (γ : ℝ) : xMat * ryMat γ * xMat = ryMat (-γ) := by
  rw [ryMat_eq, ryMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two, neg_div, Real.cos_neg, Real.sin_neg]

/-- Conjugation by `X` is multiplicative. -/
theorem xMat_conj_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    xMat * M * xMat * (xMat * N * xMat) = xMat * (M * N) * xMat := by
  calc xMat * M * xMat * (xMat * N * xMat)
      = xMat * M * (xMat * xMat) * (N * xMat) := by simp only [mul_assoc]
    _ = xMat * (M * N) * xMat := by
        rw [xMat_mul_self, mul_one]
        simp only [mul_assoc]

/-! ### The Euler product -/

/-- ★ **The `z`-`y`-`z` product as an explicit matrix** (Nielsen–Chuang (4.12)). -/
theorem rz_ry_rz_eq (β γ δ : ℝ) :
    rzMat β * ryMat γ * rzMat δ =
      !![expI (-((β + δ) / 2)) * (Real.cos (γ / 2) : ℂ),
          -(expI (-((β - δ) / 2)) * (Real.sin (γ / 2) : ℂ));
         expI ((β - δ) / 2) * (Real.sin (γ / 2) : ℂ),
          expI ((β + δ) / 2) * (Real.cos (γ / 2) : ℂ)] := by
  have e1 : expI (-(β / 2)) * expI (-(δ / 2)) = expI (-((β + δ) / 2)) := by
    rw [← expI_add]
    congr 1
    ring
  have e2 : expI (-(β / 2)) * expI (δ / 2) = expI (-((β - δ) / 2)) := by
    rw [← expI_add]
    congr 1
    ring
  have e3 : expI (β / 2) * expI (-(δ / 2)) = expI ((β - δ) / 2) := by
    rw [← expI_add]
    congr 1
    ring
  have e4 : expI (β / 2) * expI (δ / 2) = expI ((β + δ) / 2) := by
    rw [← expI_add]
    congr 1
    ring
  rw [rzMat_eq, ryMat_eq, rzMat_eq]
  set c : ℂ := (Real.cos (γ / 2) : ℂ)
  set s : ℂ := (Real.sin (γ / 2) : ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination c * e1
  · linear_combination s * e2
  · linear_combination s * e3
  · linear_combination c * e4

/-! ### What unitarity gives -/

/-- The first column of a unitary matrix is a unit vector. -/
theorem normSq_col_zero {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj']
    push_cast
    ring
  have h0 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq, e] at h0
  exact_mod_cast h0

/-- **A determinant-one unitary is `!![a, -star b; b, star a]`**, because `Uᴴ` is its adjugate. -/
theorem adjugate_entries {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    U 1 1 = star (U 0 0) ∧ U 0 1 = -star (U 1 0) := by
  have hinv : U⁻¹ = Uᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h1 : Uᴴ = U.adjugate := by
    rw [← hinv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [Matrix.adjugate_fin_two] at h1
  refine ⟨?_, ?_⟩
  · simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun h1 0) 0).symm
  · have h2 : star (U 1 0) = -U 0 1 := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun h1 0) 1
    rw [h2, neg_neg]

/-! ### The Euler decomposition -/

/-- ★★ **The `z`-`y`-`z` Euler decomposition in `SU(2)`**: a determinant-one `2 × 2` unitary is
`R_z(β) R_y(γ) R_z(δ)`. Half of Nielsen–Chuang Theorem 4.1, and the half that carries the
trigonometry: passing to determinant one leaves only two entries to match. -/
theorem exists_euler_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = rzMat β * ryMat γ * rzMat δ := by
  obtain ⟨h11, h01⟩ := adjugate_entries hU hdet
  have hcol := normSq_col_zero hU
  have hle : ‖U 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (U 0 0), norm_nonneg (U 1 0)]
  have hge : (-1 : ℝ) ≤ ‖U 0 0‖ := by nlinarith [norm_nonneg (U 0 0)]
  refine ⟨(U 1 0).arg - (U 0 0).arg, 2 * Real.arccos ‖U 0 0‖,
    -(U 0 0).arg - (U 1 0).arg, ?_⟩
  have hhalf : 2 * Real.arccos ‖U 0 0‖ / 2 = Real.arccos ‖U 0 0‖ := by ring
  have hcos : Real.cos (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 0 0‖ := by
    rw [hhalf, Real.cos_arccos hge hle]
  have hsin : Real.sin (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 1 0‖ := by
    rw [hhalf, Real.sin_arccos, show 1 - ‖U 0 0‖ ^ 2 = ‖U 1 0‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  have hp : -(((U 1 0).arg - (U 0 0).arg + (-(U 0 0).arg - (U 1 0).arg)) / 2) = (U 0 0).arg := by
    ring
  have hp' : ((U 1 0).arg - (U 0 0).arg + (-(U 0 0).arg - (U 1 0).arg)) / 2 = -(U 0 0).arg := by
    ring
  have hq : ((U 1 0).arg - (U 0 0).arg - (-(U 0 0).arg - (U 1 0).arg)) / 2 = (U 1 0).arg := by
    ring
  rw [rz_ry_rz_eq, hcos, hsin, hp, hp', hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -polar (U 0 0)
  · linear_combination h01 + polar_star (U 1 0)
  · linear_combination -polar (U 1 0)
  · linear_combination h11 - polar_star (U 0 0)

/-- ★★ **Nielsen–Chuang Theorem 4.1**: every `2 × 2` unitary is a phase times a `z`-`y`-`z` product
of rotations. -/
theorem exists_euler {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = expI α • (rzMat β * ryMat γ * rzMat δ) := by
  have hstar : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hdet : star U.det * U.det = 1 := by
    have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hU)
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,
      Matrix.det_one] at h
  have hnorm : ‖U.det‖ = 1 := by
    have h : ((‖U.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hdet, mul_comm, ← starRingEnd_apply, Complex.mul_conj']
      push_cast
      ring
    have h2 : ‖U.det‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg U.det]
  have hdetU : U.det = expI U.det.arg := by
    conv_lhs => rw [← polar U.det]
    rw [hnorm]
    simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, U.det = expI t := ⟨U.det.arg, hdetU⟩
  have hW : expI (-(t / 2)) • U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hstar, star_expI, neg_neg, ← expI_add]
    simp
  have hWdet : (expI (-(t / 2)) • U).det = 1 := by
    rw [Matrix.det_smul, ht, show Fintype.card (Fin 2) = 2 from rfl, pow_two, ← expI_add,
      ← expI_add, show -(t / 2) + -(t / 2) + t = 0 by ring, expI_zero]
  obtain ⟨β, γ, δ, hbgd⟩ := exists_euler_of_det_one hW hWdet
  refine ⟨t / 2, β, γ, δ, ?_⟩
  rw [← hbgd, smul_smul, ← expI_add]
  simp

/-! ### The `ABC` identity -/

/-- ★ The three factors of Nielsen–Chuang Corollary 4.2 multiply to `1`. -/
theorem abc_prod_eq_one (β γ δ : ℝ) :
    rzMat β * ryMat (γ / 2) * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)))
        * rzMat ((δ - β) / 2) = 1 := by
  have key : rzMat β * ryMat (γ / 2) * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)))
        * rzMat ((δ - β) / 2)
      = rzMat β * (ryMat (γ / 2) * ryMat (-(γ / 2)))
          * (rzMat (-((δ + β) / 2)) * rzMat ((δ - β) / 2)) := by
    simp only [mul_assoc]
  rw [key, ryMat_mul, rzMat_mul, show γ / 2 + -(γ / 2) = 0 by ring, ryMat_zero, mul_one,
    show -((δ + β) / 2) + (δ - β) / 2 = -β by ring, rzMat_mul, show β + -β = 0 by ring, rzMat_zero]

/-- ★ **The `ABC` identity** (Nielsen–Chuang Corollary 4.2): inserting the two `X`s turns the
product of the three factors into the Euler product. -/
theorem abc_identity (β γ δ : ℝ) :
    rzMat β * ryMat (γ / 2) * xMat * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2))) * xMat
        * rzMat ((δ - β) / 2) = rzMat β * ryMat γ * rzMat δ := by
  have hconj : xMat * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2))) * xMat
      = ryMat (γ / 2) * rzMat ((δ + β) / 2) := by
    rw [← xMat_conj_mul, xMat_conj_ryMat, xMat_conj_rzMat, neg_neg, neg_neg]
  have hassoc : ∀ M N P : Matrix (Fin 2) (Fin 2) ℂ,
      M * xMat * N * xMat * P = M * (xMat * N * xMat) * P := by
    intro M N P
    simp only [mul_assoc]
  rw [hassoc, hconj]
  have key : rzMat β * ryMat (γ / 2) * (ryMat (γ / 2) * rzMat ((δ + β) / 2))
        * rzMat ((δ - β) / 2)
      = rzMat β * (ryMat (γ / 2) * ryMat (γ / 2))
          * (rzMat ((δ + β) / 2) * rzMat ((δ - β) / 2)) := by
    simp only [mul_assoc]
  rw [key, ryMat_mul, rzMat_mul, show γ / 2 + γ / 2 = γ by ring,
    show (δ + β) / 2 + (δ - β) / 2 = δ by ring]

/-- ★★ **Every `2 × 2` unitary is `e^{iα} A X B X C` with `A B C = 1`** — the form a controlled gate
needs: on the control bit `0` the two `X`s are absent and the target gets `A B C = 1`, on the control
bit `1` they are present and it gets `e^{-iα} U`. -/
theorem exists_abc {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A * B * C = 1 ∧
          U = expI α • (A * xMat * B * xMat * C) := by
  obtain ⟨α, β, γ, δ, hU'⟩ := exists_euler hU
  refine ⟨α, rzMat β * ryMat (γ / 2), ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)),
    rzMat ((δ - β) / 2), mul_mem (rzMat_mem_unitaryGroup β) (ryMat_mem_unitaryGroup (γ / 2)),
    mul_mem (ryMat_mem_unitaryGroup (-(γ / 2))) (rzMat_mem_unitaryGroup (-((δ + β) / 2))),
    rzMat_mem_unitaryGroup ((δ - β) / 2), abc_prod_eq_one β γ δ, ?_⟩
  rw [hU', abc_identity]

end Euler

end QuantumInfo
