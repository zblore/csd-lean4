/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapMixing

/-!
# Lyapunov exponents of linear maps, and the cat map's

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #148; consumed by `SigmaLayer/FibreLyapunov.lean`.

Mathlib has no notion of Lyapunov exponent (MATHLIB-ABSENT(lyapunovExponent)). This file defines
the one notion that needs no manifold: for a continuous linear map `A` of a real normed space and
a direction `v`, `HasLyapunovExponent A v l` says `log ‖Aⁿ v‖ / n → l`. For the derivative of a
smooth map this is the Lyapunov exponent of the tangent direction `v`; for a linear map the
derivative is the map itself, and for a translation it is the identity.

## The cat map

`catR : ℝ² →L ℝ²` is the matrix `[[2,1],[1,1]]`, the lift of `cat` (`cat_coe`) and the action
`catZ` on frequencies (`catR_intCast`). Its eigenvalues are `φ²` and `φ⁻² = 2 − φ`; the
expanding and contracting linear forms `ellUR`, `ellSR` of `CatMapMixing.lean`'s integer argument
are the real ones here, and the geometric sandwich `hasLyapunovExponent_of_geometric_bounds` turns
their scaling into the exponents:

* ★★ `hasLyapunovExponent_catR`: every direction off the stable line has exponent `2 log φ`;
* ★ `hasLyapunovExponent_catR_stable`: every nonzero direction on it has exponent `−2 log φ`;
* `hasLyapunovExponent_id`: the identity has exponent `0` in every direction.

## Honest scope

* **Linear maps only.** The exponent of a nonlinear map at a point, in a tangent direction, is the
  exponent of its derivative there; the Oseledets theorem (existence of exponents almost everywhere
  for a measure-preserving map) is not formalised and is not needed for the maps downstream, whose
  derivatives are constant.
* `log ‖0‖ = 0` in Lean, so the zero direction has exponent `0` trivially; the theorems are stated
  for nonzero directions where that matters.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8
(the cat map's exponents) and Supplement S; `Mathlib/Dynamics/CatMapWitness.lean` (`cat`, `catZ`),
`Mathlib/Dynamics/CatMapMixing.lean` (`ellU`, `ellS`, the golden-ratio facts);
`specs/BACKLOG.md` #148.
-/

@[expose] public section

open Filter Topology Real
open scoped goldenRatio

/-! ### The exponent of a direction under a linear map -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `HasLyapunovExponent A v l`: the direction `v` has **Lyapunov exponent** `l` under the
continuous linear map `A`, i.e. `log ‖Aⁿ v‖ / n → l`. -/
def HasLyapunovExponent (A : E →L[ℝ] E) (v : E) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log ‖(A ^ n) v‖ / n) atTop (𝓝 l)

theorem HasLyapunovExponent.unique {A : E →L[ℝ] E} {v : E} {l l' : ℝ}
    (h : HasLyapunovExponent A v l) (h' : HasLyapunovExponent A v l') : l = l' :=
  tendsto_nhds_unique h h'

/-- The identity stretches nothing: exponent `0` in every direction. -/
theorem hasLyapunovExponent_id (v : E) : HasLyapunovExponent (ContinuousLinearMap.id ℝ E) v 0 := by
  have h : ∀ n : ℕ, ((ContinuousLinearMap.id ℝ E) ^ n) v = v := fun n => by
    rw [← ContinuousLinearMap.one_def, one_pow]
    rfl
  unfold HasLyapunovExponent
  simp only [h]
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **The geometric sandwich**: a direction squeezed between two geometric envelopes with the same
ratio `r` has exponent `log r`. -/
theorem hasLyapunovExponent_of_geometric_bounds (A : E →L[ℝ] E) (v : E) {a b r : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hlow : ∀ n : ℕ, a * r ^ n ≤ ‖(A ^ n) v‖)
    (hup : ∀ n : ℕ, ‖(A ^ n) v‖ ≤ b * r ^ n) :
    HasLyapunovExponent A v (Real.log r) := by
  have hg : ∀ c : ℝ, 0 < c →
      Tendsto (fun n : ℕ => Real.log (c * r ^ n) / n) atTop (𝓝 (Real.log r)) := by
    intro c hc
    have h1 : ∀ n : ℕ, Real.log (c * r ^ n) / n
        = Real.log c / n + (n : ℝ) * Real.log r / n := fun n => by
      rw [Real.log_mul hc.ne' (pow_pos hr n).ne', Real.log_pow, add_div]
    simp_rw [h1]
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) * Real.log r / n) atTop (𝓝 (Real.log r)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)).symm
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hg a ha) (hg b hb) (fun n => ?_) (fun n => ?_)
  · exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (hlow n)) (Nat.cast_nonneg n)
  · exact div_le_div_of_nonneg_right
      (Real.log_le_log (lt_of_lt_of_le (by positivity) (hlow n)) (hup n)) (Nat.cast_nonneg n)

end General

namespace MeasureTheory

/-! ### The real cat matrix and its two eigenforms -/

/-- The cat matrix `[[2,1],[1,1]]` as a continuous linear map of `ℝ²`: the lift of `cat` to the
plane, and the derivative of `cat` at every point. -/
noncomputable def catR : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (2 * v.1 + v.2, v.1 + v.2)
      map_add' := fun u v => by ext <;> simp <;> ring
      map_smul' := fun c v => by ext <;> simp <;> ring }

@[simp] lemma catR_apply (v : ℝ × ℝ) : catR v = (2 * v.1 + v.2, v.1 + v.2) := rfl

/-- `cat` is `catR` read modulo `ℤ²`. -/
theorem cat_coe (x y : ℝ) :
    cat ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((catR (x, y)).1 : AddCircle (1 : ℝ)), ((catR (x, y)).2 : AddCircle (1 : ℝ))) := by
  have h : ((2 * x : ℝ) : AddCircle (1 : ℝ)) = (2 : ℤ) • (x : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    norm_num
  simp [cat, h]

/-- The frequency action `catZ` is `catR` on integer points. -/
lemma catR_intCast (v : ℤ × ℤ) :
    catR ((v.1 : ℝ), (v.2 : ℝ)) = (((catZ v).1 : ℝ), ((catZ v).2 : ℝ)) := by
  simp [catZ]

/-- The expanding linear form `v ↦ v₁ + (φ − 1) v₂` on `ℝ²`: `catR` scales it by `φ²`. -/
noncomputable def ellUR (v : ℝ × ℝ) : ℝ := v.1 + (φ - 1) * v.2

/-- The contracting linear form `v ↦ v₁ − φ v₂` on `ℝ²`: `catR` scales it by `2 − φ = φ⁻²`. -/
noncomputable def ellSR (v : ℝ × ℝ) : ℝ := v.1 - φ * v.2

lemma ellU_eq_ellUR (v : ℤ × ℤ) : ellU v = ellUR ((v.1 : ℝ), (v.2 : ℝ)) := rfl

lemma ellS_eq_ellSR (v : ℤ × ℤ) : ellS v = ellSR ((v.1 : ℝ), (v.2 : ℝ)) := rfl

lemma ellUR_catR (v : ℝ × ℝ) : ellUR (catR v) = φ ^ 2 * ellUR v := by
  simp only [ellUR, catR_apply]
  linear_combination (-(v.1 + φ * v.2)) * goldenRatio_sq

lemma ellSR_catR (v : ℝ × ℝ) : ellSR (catR v) = (2 - φ) * ellSR v := by
  simp only [ellSR, catR_apply]
  linear_combination (-v.2) * goldenRatio_sq

lemma ellUR_catR_pow (v : ℝ × ℝ) (n : ℕ) : ellUR ((catR ^ n) v) = φ ^ (2 * n) * ellUR v := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      show ellUR (catR ((catR ^ k) v)) = _
      rw [ellUR_catR, ih]
      ring

lemma ellSR_catR_pow (v : ℝ × ℝ) (n : ℕ) : ellSR ((catR ^ n) v) = (2 - φ) ^ n * ellSR v := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      show ellSR (catR ((catR ^ k) v)) = _
      rw [ellSR_catR, ih]
      ring

lemma two_sub_goldenRatio_pos : 0 < 2 - φ := by linarith [goldenRatio_lt_two]

lemma two_sub_goldenRatio_lt_one : 2 - φ < 1 := by linarith [one_lt_goldenRatio]

/-- `2 − φ = φ⁻²`. -/
lemma two_sub_goldenRatio_eq : 2 - φ = φ⁻¹ ^ 2 := by
  rw [inv_goldenRatio, neg_sq, goldenConj_sq, ← one_sub_goldenConj]
  ring

/-! ### The sup norm against the two forms -/

lemma abs_ellUR_le (v : ℝ × ℝ) : |ellUR v| ≤ φ * ‖v‖ := by
  have hφ : 0 ≤ φ - 1 := by linarith [one_lt_goldenRatio]
  have h1 : |v.1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_snd_le v
  calc |ellUR v| ≤ |v.1| + (φ - 1) * |v.2| := by
        rw [ellUR]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hφ]
    _ ≤ ‖v‖ + (φ - 1) * ‖v‖ := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hφ)
    _ = φ * ‖v‖ := by ring

lemma abs_ellSR_le (v : ℝ × ℝ) : |ellSR v| ≤ φ ^ 2 * ‖v‖ := by
  have hφ : 0 < φ := goldenRatio_pos
  have h1 : |v.1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_snd_le v
  calc |ellSR v| ≤ |v.1| + φ * |v.2| := by
        rw [ellSR]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ ‖v‖ + φ * ‖v‖ := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hφ.le)
    _ = φ ^ 2 * ‖v‖ := by rw [goldenRatio_sq]; ring

/-- A vector is recovered from its two eigenforms: `‖v‖ ≤ |ℓU v| + |ℓS v|`. -/
lemma norm_le_abs_ellUR_add_abs_ellSR (v : ℝ × ℝ) : ‖v‖ ≤ |ellUR v| + |ellSR v| := by
  have h5 : (2 : ℝ) < 2 * φ - 1 := by linarith [three_halves_lt_goldenRatio]
  have hv2 : v.2 = (ellUR v - ellSR v) / (2 * φ - 1) := by
    rw [eq_div_iff (by linarith)]
    simp only [ellUR, ellSR]
    ring
  have hv1 : v.1 = (φ * ellUR v + (φ - 1) * ellSR v) / (2 * φ - 1) := by
    rw [eq_div_iff (by linarith)]
    simp only [ellUR, ellSR]
    ring
  have hU := abs_nonneg (ellUR v)
  have hS := abs_nonneg (ellSR v)
  have hφ1 : 0 ≤ φ - 1 := by linarith [one_lt_goldenRatio]
  have h2 : |v.2| ≤ (|ellUR v| + |ellSR v|) / 2 := by
    rw [hv2, abs_div, abs_of_pos (show (0 : ℝ) < 2 * φ - 1 by linarith)]
    calc |ellUR v - ellSR v| / (2 * φ - 1)
        ≤ (|ellUR v| + |ellSR v|) / (2 * φ - 1) := by gcongr; exact abs_sub _ _
      _ ≤ (|ellUR v| + |ellSR v|) / 2 := by gcongr
  have h1 : |v.1| ≤ |ellUR v| + |ellSR v| := by
    rw [hv1, abs_div, abs_of_pos (show (0 : ℝ) < 2 * φ - 1 by linarith),
      div_le_iff₀ (by linarith)]
    calc |φ * ellUR v + (φ - 1) * ellSR v| ≤ φ * |ellUR v| + (φ - 1) * |ellSR v| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos goldenRatio_pos, abs_of_nonneg hφ1]
      _ ≤ (|ellUR v| + |ellSR v|) * (2 * φ - 1) := by
          nlinarith [mul_nonneg hφ1 hU, mul_nonneg goldenRatio_pos.le hS]
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  exact ⟨h1, by linarith [h2]⟩

/-! ### The exponents of the cat map -/

lemma norm_catR_pow_le (v : ℝ × ℝ) (n : ℕ) :
    ‖(catR ^ n) v‖ ≤ (|ellUR v| + |ellSR v|) * (φ ^ 2) ^ n := by
  have h := norm_le_abs_ellUR_add_abs_ellSR ((catR ^ n) v)
  rw [ellUR_catR_pow, ellSR_catR_pow, abs_mul, abs_mul, abs_of_pos (pow_pos goldenRatio_pos _),
    abs_of_pos (pow_pos two_sub_goldenRatio_pos _)] at h
  have h1 : (2 - φ) ^ n ≤ 1 :=
    pow_le_one₀ two_sub_goldenRatio_pos.le two_sub_goldenRatio_lt_one.le
  have h2 : (1 : ℝ) ≤ φ ^ (2 * n) := one_le_pow₀ one_lt_goldenRatio.le
  rw [← pow_mul]
  nlinarith [abs_nonneg (ellUR v), abs_nonneg (ellSR v)]

lemma abs_ellUR_div_mul_le_norm_catR_pow (v : ℝ × ℝ) (n : ℕ) :
    |ellUR v| / φ * (φ ^ 2) ^ n ≤ ‖(catR ^ n) v‖ := by
  have h := abs_ellUR_le ((catR ^ n) v)
  rw [ellUR_catR_pow, abs_mul, abs_of_pos (pow_pos goldenRatio_pos _)] at h
  rw [← pow_mul, div_mul_eq_mul_div, div_le_iff₀ goldenRatio_pos]
  linarith [h]

/-- ★★ **The cat map stretches every direction off the stable line at rate `2 log φ`**: for
`v` with `ellUR v ≠ 0`, `log ‖catRⁿ v‖ / n → 2 log φ`. -/
theorem hasLyapunovExponent_catR {v : ℝ × ℝ} (hv : ellUR v ≠ 0) :
    HasLyapunovExponent catR v (2 * Real.log φ) := by
  have hl : 2 * Real.log φ = Real.log (φ ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hl]
  exact hasLyapunovExponent_of_geometric_bounds catR v (div_pos (abs_pos.2 hv) goldenRatio_pos)
    (add_pos_of_pos_of_nonneg (abs_pos.2 hv) (abs_nonneg _)) (pow_pos goldenRatio_pos 2)
    (abs_ellUR_div_mul_le_norm_catR_pow v) (norm_catR_pow_le v)

lemma ellSR_ne_zero_of_ne_zero {v : ℝ × ℝ} (hv : v ≠ 0) (hU : ellUR v = 0) : ellSR v ≠ 0 := by
  intro hS
  apply hv
  have h2 : v.2 = 0 := by
    have h : (2 * φ - 1) * v.2 = 0 := by
      simp only [ellUR, ellSR] at hU hS
      linear_combination hU - hS
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (by linarith [three_halves_lt_goldenRatio])
    · exact h
  have h1 : v.1 = 0 := by
    simp only [ellUR] at hU
    rw [h2] at hU
    linarith
  exact Prod.ext h1 h2

lemma norm_catR_pow_le_of_ellUR_eq_zero {v : ℝ × ℝ} (hU : ellUR v = 0) (n : ℕ) :
    ‖(catR ^ n) v‖ ≤ |ellSR v| * (2 - φ) ^ n := by
  have h := norm_le_abs_ellUR_add_abs_ellSR ((catR ^ n) v)
  rw [ellUR_catR_pow, ellSR_catR_pow, hU, mul_zero, abs_zero, zero_add, abs_mul,
    abs_of_pos (pow_pos two_sub_goldenRatio_pos _)] at h
  linarith [h]

lemma abs_ellSR_div_mul_le_norm_catR_pow (v : ℝ × ℝ) (n : ℕ) :
    |ellSR v| / φ ^ 2 * (2 - φ) ^ n ≤ ‖(catR ^ n) v‖ := by
  have h := abs_ellSR_le ((catR ^ n) v)
  rw [ellSR_catR_pow, abs_mul, abs_of_pos (pow_pos two_sub_goldenRatio_pos _)] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos goldenRatio_pos 2)]
  linarith [h]

/-- ★ **On the stable line the cat map contracts at rate `2 log φ`**: for `v ≠ 0` with
`ellUR v = 0`, `log ‖catRⁿ v‖ / n → −2 log φ`. -/
theorem hasLyapunovExponent_catR_stable {v : ℝ × ℝ} (hv : v ≠ 0) (hU : ellUR v = 0) :
    HasLyapunovExponent catR v (-(2 * Real.log φ)) := by
  have hS := ellSR_ne_zero_of_ne_zero hv hU
  have hl : -(2 * Real.log φ) = Real.log (2 - φ) := by
    rw [two_sub_goldenRatio_eq, Real.log_pow, Real.log_inv]
    push_cast
    ring
  rw [hl]
  exact hasLyapunovExponent_of_geometric_bounds catR v
    (div_pos (abs_pos.2 hS) (pow_pos goldenRatio_pos 2)) (abs_pos.2 hS) two_sub_goldenRatio_pos
    (abs_ellSR_div_mul_le_norm_catR_pow v) (norm_catR_pow_le_of_ellUR_eq_zero hU)

end MeasureTheory

end
