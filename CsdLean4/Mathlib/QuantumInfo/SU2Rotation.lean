/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.CliffordTAngle
public import Mathlib.Topology.Instances.Matrix

/-!
# `SU(2)` in axis–angle form, and the dense rotation circle of one Clifford+T word

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #80, part (a) of the re-split
row #69 (`R-005`; `specs/magic-plan.md`, "The split").

The unit-quaternion parametrisation of the determinant-one `2 × 2` unitaries, written as a matrix
directly: `su2 w x y z = w·1 − i(x σ₁ + y σ₂ + z σ₃)`. Its algebra is the quaternion product
(★ `su2_mul`), its determinant is `w² + x² + y² + z²` (`su2_det`) and its trace is `2w`
(`su2_trace`), so `axisRot a b c θ`, the rotation by `θ` about a unit vector `(a, b, c)`, is a
one-parameter group in `θ` (★ `axisRot_add`) with period `4π` (`axisRot_add_int_mul_four_pi`),
continuous in `θ` (`continuous_axisRot`).

The Clifford+T word `T·HTH` of `CliffordTAngle.lean` is, up to the phase `e^{iπ/4}`, exactly such a
rotation: ★★ `htht_eq_su2` gives its quaternion coordinates
`(cos²(π/8), √2/4, (2−√2)/4, √2/4)` — no radicals beyond `√2` — and ★ `htht_eq_axisRot` reads
them as the axis `(1, √2−1, 1)/‖·‖` and the angle `htAngle` of #68. Because that angle is an
irrational multiple of `2π` (and hence of `4π`), the powers of the word fill its own rotation
circle densely: ★★ `mem_closure_range_axisRot`.

* `su2`, ★ `su2_mul`, `su2_one`, `su2_det`, `su2_trace`;
* `axisRot`, `axisRot_zero`, ★ `axisRot_add`, `axisRot_nat_mul`, `axisRot_add_int_mul_four_pi`,
  `continuous_axisRot`;
* `htSin`, `htSin_sq`, `htSin_pos`, `htA`, `htB`, ★ `htAxis_unit` — the unit axis, radical-free
  through the products `htSin · htA = √2/4` and `htSin · htB = (2−√2)/4`;
* ★★ `htht_eq_su2`, ★ `htht_eq_axisRot`, `htht_pow` — the word, its powers, and their phases;
* ★ `irrational_htAngle_div_four_pi`, `dense_closure_htAngle_four_pi`;
* ★★ `mem_closure_range_axisRot` — **every rotation about the word's own axis is a limit of
  integer multiples of its angle**, so (up to phase) of its powers.

## Honest scope

⚠️ One axis. Filling `SU(2)` needs a second, non-parallel axis and the Euler decomposition
`U = R_u(α) R_v(β) R_u(γ)`: that is BACKLOG #81, which also records the route worked out here
(conjugating by `H` reflects the axis `(1, √2−1, 1)` to `(1, 1−√2, 1)`, the two are orthogonal to
`(1, 0, −1)`, and the product of the two `π`-rotations is a rotation about `(1, 0, −1)` through an
angle that is again an irrational multiple of `2π` — so two *orthogonal* dense circles are
reachable, where the Euler decomposition is the textbook `z`-`y`-`z` one). Nothing here claims
density in `U(2)`.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.2 (the
Bloch/axis–angle form) and §4.5.3; `specs/magic-plan.md`; `specs/BACKLOG.md` #80, #81;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix
open scoped Real

namespace QuantumInfo

namespace SU2

/-! ### The unit-quaternion parametrisation -/

/-- `su2 w x y z = w·1 − i(x σ₁ + y σ₂ + z σ₃)`: the quaternion `w + xi + yj + zk` as a `2 × 2`
complex matrix. It has determinant `w² + x² + y² + z²`. -/
noncomputable def su2 (w x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(w : ℂ) - Complex.I * z, -Complex.I * ((x : ℂ) - Complex.I * y);
     -Complex.I * ((x : ℂ) + Complex.I * y), (w : ℂ) + Complex.I * z]

/-- ★ **The quaternion product.** -/
theorem su2_mul (w x y z w' x' y' z' : ℝ) :
    su2 w x y z * su2 w' x' y' z' =
      su2 (w * w' - x * x' - y * y' - z * z') (w * x' + x * w' + y * z' - z * y')
        (w * y' - x * z' + y * w' + z * x') (w * z' + x * y' - y * x' + z * w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> constructor <;> ring

theorem su2_one : su2 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2]

theorem su2_det (w x y z : ℝ) : (su2 w x y z).det = ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  rw [su2, Matrix.det_fin_two_of]
  push_cast
  simp [Complex.ext_iff, ← Complex.ofReal_pow]
  constructor <;> ring

theorem su2_trace (w x y z : ℝ) : (su2 w x y z).trace = 2 * (w : ℂ) := by
  rw [su2, Matrix.trace_fin_two_of]
  ring

/-! ### Rotation by an angle about an axis -/

/-- The rotation by `θ` about the unit vector `(a, b, c)`. -/
noncomputable def axisRot (a b c θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  su2 (Real.cos (θ / 2)) (a * Real.sin (θ / 2)) (b * Real.sin (θ / 2)) (c * Real.sin (θ / 2))

@[simp] theorem axisRot_zero (a b c : ℝ) : axisRot a b c 0 = 1 := by
  rw [axisRot]
  norm_num [su2_one]

/-- ★ **The rotations about a fixed unit axis form a one-parameter group.** -/
theorem axisRot_add {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (α β : ℝ) :
    axisRot a b c (α + β) = axisRot a b c α * axisRot a b c β := by
  rw [axisRot, axisRot, axisRot, su2_mul]
  have hc : Real.cos ((α + β) / 2)
      = Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.cos_add]
  have hs : Real.sin ((α + β) / 2)
      = Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.sin_add]
  rw [hc, hs]
  congr 1
  · linear_combination (Real.sin (α / 2) * Real.sin (β / 2)) * hu
  · ring
  · ring
  · ring

theorem axisRot_nat_mul {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) (k : ℕ) :
    axisRot a b c ((k : ℝ) * θ) = axisRot a b c θ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← ih, ← axisRot_add hu]
    congr 1
    push_cast
    ring

/-- The rotations have period `4π` in the angle (a `2π` rotation is `−1`). -/
theorem axisRot_add_int_mul_four_pi (a b c θ : ℝ) (k : ℤ) :
    axisRot a b c (θ + (k : ℝ) * (4 * π)) = axisRot a b c θ := by
  have h : (θ + (k : ℝ) * (4 * π)) / 2 = θ / 2 + (k : ℝ) * (2 * π) := by ring
  rw [axisRot, axisRot, h, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem continuous_axisRot (a b c : ℝ) : Continuous (axisRot a b c) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [axisRot, su2] <;> fun_prop

/-! ### The Clifford+T word in axis–angle form -/

open CliffordT

theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity

/-- `sin(htAngle/2)`, the sine of the half-angle of `T·HTH`. -/
noncomputable def htSin : ℝ := Real.sin htHalfAngle

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]

theorem htSin_sq : htSin ^ 2 = (10 - 4 * Real.sqrt 2) / 16 := by
  have hu : Real.cos (π / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := cos_sq_pi_div_eight
  have hle : (0 : ℝ) ≤ 1 - (Real.cos (π / 8) ^ 2) ^ 2 := by
    rw [hu]
    nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]
  rw [htSin, htHalfAngle, Real.sin_arccos, Real.sq_sqrt hle, hu]
  nlinarith [sq_sqrt_two]

theorem htSin_nonneg : 0 ≤ htSin := by
  rw [htSin, htHalfAngle, Real.sin_arccos]
  positivity

theorem htSin_pos : 0 < htSin := by
  have h2 : 0 < htSin ^ 2 := by
    rw [htSin_sq]
    nlinarith [sqrt_two_lt_two]
  rcases htSin_nonneg.lt_or_eq with h | h
  · exact h
  · rw [← h] at h2
    norm_num at h2

theorem htSin_ne_zero : htSin ≠ 0 := ne_of_gt htSin_pos

/-- The first and third components of the unit axis of `T·HTH`. -/
noncomputable def htA : ℝ := Real.sqrt 2 / 4 / htSin

/-- The second component of the unit axis of `T·HTH`. -/
noncomputable def htB : ℝ := (2 - Real.sqrt 2) / 4 / htSin

theorem htSin_mul_htA : htSin * htA = Real.sqrt 2 / 4 := by
  rw [htA, mul_comm, div_mul_cancel₀ _ htSin_ne_zero]

theorem htSin_mul_htB : htSin * htB = (2 - Real.sqrt 2) / 4 := by
  rw [htB, mul_comm, div_mul_cancel₀ _ htSin_ne_zero]

/-- ★ **The axis is a unit vector.** -/
theorem htAxis_unit : htA ^ 2 + htB ^ 2 + htA ^ 2 = 1 := by
  have hs := htSin_sq
  have hne := htSin_ne_zero
  rw [htA, htB]
  field_simp
  nlinarith [sq_sqrt_two, hs]

/-- ★★ **The Clifford+T word in quaternion coordinates**: `T·HTH = e^{iπ/4}·su2(cos²(π/8), √2/4,
(2−√2)/4, √2/4)`. -/
theorem htht_eq_su2 :
    htht = tPhase • su2 ((2 + Real.sqrt 2) / 4) (Real.sqrt 2 / 4) ((2 - Real.sqrt 2) / 4)
      (Real.sqrt 2 / 4) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  have hhalf : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, h2]
  have hT : tPhase = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I) := by
    rw [tPhase_eq]
    congr 1
    field_simp
    first
      | linear_combination h2
      | linear_combination -h2
  rw [htht_eq, hhalf, hT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff] <;>
    constructor <;> nlinarith [sq_sqrt_two]

/-- ★ **The word is its own rotation**: `T·HTH = e^{iπ/4}·R_n̂(htAngle)` with the unit axis
`n̂ = (1, √2−1, 1)/‖·‖`. -/
theorem htht_eq_axisRot : htht = tPhase • axisRot htA htB htA htAngle := by
  rw [htht_eq_su2, axisRot]
  congr 2
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, cos_htHalfAngle,
      cos_sq_pi_div_eight]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htA]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htB]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htA]

/-- The powers of the word are its rotation's multiples, up to the phase. -/
theorem htht_pow (k : ℕ) :
    htht ^ k = tPhase ^ k • axisRot htA htB htA ((k : ℝ) * htAngle) := by
  rw [axisRot_nat_mul htAxis_unit, htht_eq_axisRot, smul_pow]

/-! ### The dense rotation circle -/

theorem irrational_htAngle_div_four_pi : Irrational (htAngle / (4 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  refine irrational_htAngle_div_two_pi ⟨2 * q, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

theorem dense_closure_htAngle_four_pi :
    Dense (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.mpr irrational_htAngle_div_four_pi

/-- ★★ **The word's powers fill its own rotation circle.** Every rotation about the axis of
`T·HTH` is a limit of integer multiples of its angle — equivalently, up to phase, of its powers
(`htht_pow`). -/
theorem mem_closure_range_axisRot (α : ℝ) :
    axisRot htA htB htA α
      ∈ closure (Set.range fun k : ℤ => axisRot htA htB htA ((k : ℝ) * htAngle)) := by
  set f : ℝ → Matrix (Fin 2) (Fin 2) ℂ := axisRot htA htB htA with hf
  -- the angle subgroup is dense in `ℝ`, and `f` maps it into the range of the multiples
  have hsub : f '' (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)
      ⊆ Set.range fun k : ℤ => f ((k : ℝ) * htAngle) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp ht
    refine ⟨k, ?_⟩
    rw [← hkm, zsmul_eq_mul, zsmul_eq_mul, hf]
    exact (axisRot_add_int_mul_four_pi htA htB htA ((k : ℝ) * htAngle) m).symm
  have hcl : f '' closure (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)
      ⊆ closure (f '' (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)) :=
    image_closure_subset_closure_image (continuous_axisRot htA htB htA)
  have hmem : f α ∈ f '' closure (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ) := by
    refine ⟨α, ?_, rfl⟩
    rw [dense_closure_htAngle_four_pi.closure_eq]
    trivial
  exact closure_mono hsub (hcl hmem)

end SU2

end QuantumInfo

end
