/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Riesz projector of a Hermitian matrix

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #158 (out of ~~#88~~, the first brick of Kato's adiabatic theorem).

For a Hermitian `H : Matrix (Fin N) (Fin N) ℂ`, a centre `c` and a radius `r ≥ 0` such that no
eigenvalue of `H` lies on the circle `|z − c| = r`, the **Riesz projector**

  `rieszProj hH c r = (2πi)⁻¹ ∮_{|z−c|=r} (z·1 − H)⁻¹ dz`

is the orthogonal projection onto the span of the eigenvectors whose eigenvalue lies **inside** the
disc. Mathlib has the continuous functional calculus for a self-adjoint element, but no projector
of an isolated part of the spectrum written as a contour integral — and it is the integral form
that the adiabatic theorem differentiates along a path (#159).

* `conjD hH d = U diag(d) U†` — the conjugation of a diagonal by the eigenvector unitary `U` of
  `spectral_theorem`; every operator in the file has this form, and the form is closed under the
  algebra operations with the diagonals composing pointwise (`conjD_mul_conjD`, `conjD_smul`,
  `conjD_sub`, `conjD_conjTranspose`, `rank_conjD`, `conjD_mulVec_eigenvectorBasis`); `eq_conjD` is
  the spectral theorem as `H = conjD eigC`, and `eigenProj j = conjD (Pi.single j 1)` is the
  eigenprojection of the `j`-th eigenvector (`conjD_eq_sum`);
* `smul_one_sub_eq_conjD`, ★ `inv_smul_one_sub_eq_conjD` — **the resolvent in the eigenbasis**:
  off the spectrum, `(z·1 − H)⁻¹ = U diag((z − μⱼ)⁻¹) U†`, equivalently
  `∑ⱼ (z − μⱼ)⁻¹ • eigenProj j` (`inv_smul_one_sub_eq_sum`);
* `circleIntegral_sub_inv_eq_ite` — **the Cauchy evaluation**: `∮ (z − μ)⁻¹ dz` is `2πi` if `μ`
  is inside the disc and `0` if outside (Cauchy's integral formula on one side, Cauchy's theorem
  on the other);
* ★★ `rieszProj_eq_sum` / ★★ `rieszProj_eq_conjD` — **the Riesz projector is the spectral
  projection**: `∑ⱼ discInd j • eigenProj j = conjD discInd`, `discInd` the indicator
  `𝟙_{|μⱼ−c|<r}` of the disc on the eigenvalues;
* the corollaries: `rieszProj_mul_self` (idempotent), `rieszProj_isHermitian`,
  `rieszProj_mul_comm` (`H P = P H`), `rank_rieszProj` (the number of eigenvalues in the disc),
  ★ `mul_rieszProj_eq_smul` — when the disc isolates one eigenvalue `λ`, `H P = λ • P`;
  `rieszProj_mulVec_eigenvectorBasis` — on the eigenbasis it keeps or kills each vector.

## Honest scope

* Finite dimensions, `Fin N`, and `𝕜 = ℂ`, as the adiabatic theorem needs; the matrix norm is
  the `L2Operator` scope's, under which `Matrix` is a complete normed `ℂ`-algebra and the circle
  integral is a Bochner integral.
* The eigenvalues are Mathlib's `hH.eigenvalues`, so "inside the disc" is a condition on those
  reals; nothing about multiplicities is assumed.

References: T. Kato, *Perturbation Theory for Linear Operators*, I §5.3 (the Riesz projector);
`Mathlib/Analysis/Matrix/Spectrum.lean` (`spectral_theorem`, `eigenvectorUnitary`),
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean` (`integral_sub_inv_of_mem_ball`,
`integral_smul_const`, `integral_fun_sum`), `Mathlib/Analysis/Complex/CauchyIntegral.lean`;
`specs/BACKLOG.md` #158, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open Matrix Metric Set Complex Real

noncomputable section

namespace Matrix

/-- **The Riesz projector** of a matrix `H` over the disc `|z − c| < r`:
`(2πi)⁻¹ ∮_{|z−c|=r} (z·1 − H)⁻¹ dz`. -/
def rieszProj {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (r : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (2 * π * I)⁻¹ • ∮ z in C(c, r), (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹

namespace IsHermitian

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)

/-! ### The eigenbasis and the conjugation `d ↦ U diag(d) U†` -/

/-- The eigenvector unitary, as a matrix. -/
def eigU : Matrix (Fin N) (Fin N) ℂ := (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

/-- The `j`-th eigenvalue, as a complex number. -/
def eigC (j : Fin N) : ℂ := (RCLike.ofReal (hH.eigenvalues j) : ℂ)

theorem star_eigU_mul_eigU : star hH.eigU * hH.eigU = 1 :=
  Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary

theorem eigU_mul_star_eigU : hH.eigU * star hH.eigU = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2

/-- The conjugation of a diagonal by the eigenvector unitary: `U diag(d) U†`. Every operator in
this file is of this form, and the form is closed under the algebra operations. -/
def conjD (d : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := hH.eigU * diagonal d * star hH.eigU

/-- The spectral theorem, in product form. -/
theorem eq_conjD : H = hH.conjD hH.eigC := by
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

theorem conjD_mul_conjD (d e : Fin N → ℂ) : hH.conjD d * hH.conjD e = hH.conjD (d * e) := by
  unfold conjD
  calc hH.eigU * diagonal d * star hH.eigU * (hH.eigU * diagonal e * star hH.eigU)
      = hH.eigU * (diagonal d * (star hH.eigU * hH.eigU) * diagonal e) * star hH.eigU := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [star_eigU_mul_eigU, Matrix.mul_one, diagonal_mul_diagonal]; rfl

theorem conjD_one : hH.conjD 1 = 1 := by
  unfold conjD
  rw [diagonal_one', Matrix.mul_one, eigU_mul_star_eigU]

theorem conjD_smul (a : ℂ) (d : Fin N → ℂ) : hH.conjD (a • d) = a • hH.conjD d := by
  unfold conjD
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem conjD_sub (d e : Fin N → ℂ) : hH.conjD (d - e) = hH.conjD d - hH.conjD e := by
  unfold conjD
  rw [show d - e = fun i => d i - e i from rfl, ← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem conjD_conjTranspose (d : Fin N → ℂ) : (hH.conjD d)ᴴ = hH.conjD (star d) := by
  unfold conjD
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose hH.eigU,
    conjTranspose_conjTranspose, ← Matrix.mul_assoc]

theorem rank_conjD (d : Fin N → ℂ) : (hH.conjD d).rank = (diagonal d).rank := by
  unfold conjD
  have hU : IsUnit hH.eigU.det := isUnit_det_of_right_inverse hH.eigU_mul_star_eigU
  have hU' : IsUnit (star hH.eigU).det := isUnit_det_of_right_inverse hH.star_eigU_mul_eigU
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU]

/-- On the `j`-th eigenvector, `conjD d` acts as the scalar `d j`. -/
theorem conjD_mulVec_eigenvectorBasis (d : Fin N → ℂ) (j : Fin N) :
    hH.conjD d *ᵥ ⇑(hH.eigenvectorBasis j) = d j • ⇑(hH.eigenvectorBasis j) := by
  unfold conjD
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  have h1 : star hH.eigU *ᵥ ⇑(hH.eigenvectorBasis j) = Pi.single j 1 :=
    hH.star_eigenvectorUnitary_mulVec j
  have h2 : (Pi.single j (d j) : Fin N → ℂ) = d j • (Pi.single j (1 : ℂ) : Fin N → ℂ) := by
    funext i
    simp [Pi.single_apply]
  rw [h1, diagonal_mulVec_single, mul_one, h2, mulVec_smul]
  exact congrArg _ (hH.eigenvectorUnitary_mulVec j)

/-- The eigenprojection of the `j`-th eigenvector: `U Eⱼⱼ U†`. -/
def eigenProj (j : Fin N) : Matrix (Fin N) (Fin N) ℂ := hH.conjD (Pi.single j (1 : ℂ))

/-- A diagonal matrix is the sum of its entries times the unit diagonals. -/
theorem _root_.Matrix.diagonal_eq_sum_smul (d : Fin N → ℂ) :
    diagonal d = ∑ j, d j • diagonal (Pi.single j (1 : ℂ)) := by
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, Pi.single_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

/-- `conjD d` as a combination of eigenprojections. -/
theorem conjD_eq_sum (d : Fin N → ℂ) : hH.conjD d = ∑ j, d j • hH.eigenProj j := by
  unfold conjD eigenProj
  rw [diagonal_eq_sum_smul d, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-! ### The resolvent in the eigenbasis -/

/-- `z·1 − H` in the eigenbasis. -/
theorem smul_one_sub_eq_conjD (z : ℂ) :
    z • (1 : Matrix (Fin N) (Fin N) ℂ) - H = hH.conjD (fun j => z - hH.eigC j) := by
  have h : hH.conjD (fun j => z - hH.eigC j) = z • hH.conjD 1 - hH.conjD hH.eigC := by
    rw [← conjD_smul, ← conjD_sub]
    congr 1
    funext j
    simp
  rw [h, conjD_one, ← hH.eq_conjD]

/-- ★ **The resolvent in the eigenbasis**, off the spectrum. -/
theorem inv_smul_one_sub_eq_conjD {z : ℂ} (hz : ∀ j, z ≠ hH.eigC j) :
    (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹ = hH.conjD (fun j => (z - hH.eigC j)⁻¹) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [hH.smul_one_sub_eq_conjD z, conjD_mul_conjD]
  have : ((fun j => (z - hH.eigC j)⁻¹) * fun j => z - hH.eigC j) = 1 := by
    funext j
    exact inv_mul_cancel₀ (sub_ne_zero.2 (hz j))
  rw [this, conjD_one]

/-- The resolvent as a combination of eigenprojections. -/
theorem inv_smul_one_sub_eq_sum {z : ℂ} (hz : ∀ j, z ≠ hH.eigC j) :
    (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹ = ∑ j, (z - hH.eigC j)⁻¹ • hH.eigenProj j := by
  rw [hH.inv_smul_one_sub_eq_conjD hz, conjD_eq_sum]

/-! ### The Cauchy evaluation -/

/-- `∮ (z − μ)⁻¹ dz` over the circle `|z − c| = r` is `2πi` inside and `0` outside. -/
theorem _root_.circleIntegral_sub_inv_eq_ite {c μ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hne : dist μ c ≠ r) :
    (∮ z in C(c, r), (z - μ)⁻¹) = if dist μ c < r then 2 * π * I else 0 := by
  by_cases hin : dist μ c < r
  · simp only [hin, ↓reduceIte]
    exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball.2 hin)
  · simp only [hin, ↓reduceIte]
    have hout : r < dist μ c := lt_of_le_of_ne (not_lt.1 hin) (Ne.symm hne)
    have hne' : ∀ z ∈ closedBall c r, z - μ ≠ 0 := by
      intro z hz
      refine sub_ne_zero.2 fun h => ?_
      rw [mem_closedBall] at hz
      rw [h] at hz
      exact absurd hz (not_le.2 hout)
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr (s := ∅)
      countable_empty ?_ ?_
    · exact ((continuousOn_id.sub continuousOn_const).inv₀ hne')
    · intro z hz
      exact ((differentiableAt_id.sub_const μ).inv (hne' z (ball_subset_closedBall hz.1)))

/-! ### The Riesz projector -/

/-- No eigenvalue on the circle means the resolvent is defined on it. -/
theorem ne_eigC_of_mem_sphere {c z : ℂ} {r : ℝ} (hcirc : ∀ j, dist (hH.eigC j) c ≠ r)
    (hz : z ∈ sphere c r) (j : Fin N) : z ≠ hH.eigC j := by
  intro h
  rw [mem_sphere] at hz
  exact hcirc j (h ▸ hz)

/-- Each term `(z − μⱼ)⁻¹ • Eⱼ` is circle-integrable when `μⱼ` is off the circle. -/
theorem circleIntegrable_term {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r)
    (j : Fin N) :
    CircleIntegrable (E := Matrix (Fin N) (Fin N) ℂ)
      (fun z : ℂ => (z - hH.eigC j)⁻¹ • hH.eigenProj j) c r := by
  refine ContinuousOn.circleIntegrable hr ?_
  have hc : ContinuousOn (fun z : ℂ => (z - hH.eigC j)⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
      sub_ne_zero.2 (hH.ne_eigC_of_mem_sphere hcirc hz j)
  exact hc.smul continuousOn_const

/-- The indicator of the disc, on the eigenvalues. -/
def discInd (c : ℂ) (r : ℝ) (j : Fin N) : ℂ := if dist (hH.eigC j) c < r then 1 else 0

/-- ★★ **The Riesz projector is the spectral projection onto the eigenvalues in the disc.** -/
theorem rieszProj_eq_sum {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) :
    rieszProj H c r = ∑ j, hH.discInd c r j • hH.eigenProj j := by
  unfold rieszProj
  have hcongr : (∮ z in C(c, r), (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹)
      = ∮ z in C(c, r), ∑ j, (z - hH.eigC j)⁻¹ • hH.eigenProj j := by
    refine circleIntegral.integral_congr hr fun z hz => ?_
    exact hH.inv_smul_one_sub_eq_sum (hH.ne_eigC_of_mem_sphere hcirc hz)
  rw [hcongr, circleIntegral.integral_fun_sum fun j _ => hH.circleIntegrable_term hr hcirc j,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleIntegral.integral_smul_const, smul_smul, circleIntegral_sub_inv_eq_ite hr (hcirc j)]
  unfold discInd
  by_cases hin : dist (hH.eigC j) c < r
  · simp only [hin, ↓reduceIte, inv_mul_cancel₀ two_pi_I_ne_zero]
  · simp only [hin, ↓reduceIte, mul_zero]

/-- ★★ **The Riesz projector in the eigenbasis**: `U diag(𝟙_{|μⱼ−c|<r}) U†`. -/
theorem rieszProj_eq_conjD {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) :
    rieszProj H c r = hH.conjD (hH.discInd c r) := by
  rw [hH.rieszProj_eq_sum hr hcirc, conjD_eq_sum]

/-! ### The corollaries -/

theorem discInd_mul_self (c : ℂ) (r : ℝ) : hH.discInd c r * hH.discInd c r = hH.discInd c r := by
  funext j
  unfold discInd
  simp only [Pi.mul_apply]
  split_ifs <;> simp

theorem star_discInd (c : ℂ) (r : ℝ) : star (hH.discInd c r) = hH.discInd c r := by
  funext j
  unfold discInd
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- **Idempotent.** -/
theorem rieszProj_mul_self {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) :
    rieszProj H c r * rieszProj H c r = rieszProj H c r := by
  rw [hH.rieszProj_eq_conjD hr hcirc, conjD_mul_conjD, discInd_mul_self]

/-- **Hermitian.** -/
theorem rieszProj_isHermitian {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) : (rieszProj H c r).IsHermitian := by
  rw [hH.rieszProj_eq_conjD hr hcirc]
  unfold Matrix.IsHermitian
  rw [conjD_conjTranspose, star_discInd]

/-- **Commutes with `H`.** -/
theorem rieszProj_mul_comm {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) :
    H * rieszProj H c r = rieszProj H c r * H := by
  rw [hH.rieszProj_eq_conjD hr hcirc]
  have h := hH.eq_conjD
  calc H * hH.conjD (hH.discInd c r) = hH.conjD hH.eigC * hH.conjD (hH.discInd c r) := by rw [← h]
    _ = hH.conjD (hH.discInd c r) * hH.conjD hH.eigC := by
        rw [conjD_mul_conjD, conjD_mul_conjD, mul_comm]
    _ = hH.conjD (hH.discInd c r) * H := by rw [← h]

/-- ★ **When the disc isolates a single eigenvalue `λ`, `H P = λ • P`.** -/
theorem mul_rieszProj_eq_smul {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r)
    {lam : ℂ} (hlam : ∀ j, dist (hH.eigC j) c < r → hH.eigC j = lam) :
    H * rieszProj H c r = lam • rieszProj H c r := by
  rw [hH.rieszProj_eq_conjD hr hcirc]
  have h := hH.eq_conjD
  calc H * hH.conjD (hH.discInd c r) = hH.conjD hH.eigC * hH.conjD (hH.discInd c r) := by rw [← h]
    _ = hH.conjD (lam • hH.discInd c r) := by
        rw [conjD_mul_conjD]
        congr 1
        funext j
        simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, discInd]
        by_cases hin : dist (hH.eigC j) c < r
        · simp [hlam j hin]
        · simp [hin]
    _ = lam • hH.conjD (hH.discInd c r) := conjD_smul hH lam _

/-- **The rank is the number of eigenvalues in the disc.** -/
theorem rank_rieszProj {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) :
    (rieszProj H c r).rank = Fintype.card {j // dist (hH.eigC j) c < r} := by
  classical
  rw [hH.rieszProj_eq_conjD hr hcirc, rank_conjD, rank_diagonal]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  unfold discInd
  by_cases hin : dist (hH.eigC j) c < r <;> simp [hin]

/-- On the eigenbasis the projector keeps the eigenvectors inside the disc and kills the others. -/
theorem rieszProj_mulVec_eigenvectorBasis {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hcirc : ∀ j, dist (hH.eigC j) c ≠ r) (j : Fin N) :
    rieszProj H c r *ᵥ ⇑(hH.eigenvectorBasis j)
      = if dist (hH.eigC j) c < r then ⇑(hH.eigenvectorBasis j) else 0 := by
  rw [hH.rieszProj_eq_conjD hr hcirc, conjD_mulVec_eigenvectorBasis]
  unfold discInd
  by_cases hin : dist (hH.eigC j) c < r <;> simp [hin]

end IsHermitian

end Matrix

end

end
