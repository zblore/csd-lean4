/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.LyapunovExponent

/-!
# The cat map is two transverse shears, and neither shear stretches on its own

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #153; consumed by `SigmaLayer/FibreTwoShears.lean`.

Arnold's cat map `(x, y) ↦ (2x + y, x + y)` factors as the **vertical shear** `shearY : (x, y) ↦
(x, x + y)` followed by the **horizontal shear** `shearX : (x, y) ↦ (x + y, y)`
(`cat_eq_shearX_comp_shearY`). Each factor is a continuous automorphism of `T²`, so each preserves
Haar measure (`measurePreserving_shearX`, `measurePreserving_shearY`), and each lifts to a
unipotent linear map of the plane preserving the area form `u₁v₂ − u₂v₁` (`shearXR_area`,
`shearYR_area`): the factors are symplectic.

The point of the factoring is the Lyapunov exponents. A unipotent shear moves a vector by at most
a linear amount in the iterate count — `(shearXR ^ n) v = (v₁ + n v₂, v₂)` (`shearXR_pow_apply`) —
so its exponent is `0` in **every** direction (`hasLyapunovExponent_shearXR`,
`hasLyapunovExponent_shearYR`), while the composition `catR = shearXR ∘ shearYR`
(`catR_eq_shearXR_comp_shearYR`) has exponent `2 log φ` off its stable line
(`hasLyapunovExponent_catR`). ★★★ `cat_two_shears` states the whole package: **hyperbolicity is
produced by the transversality of the two shears, not by either shear.** A shear along one
coordinate, however often repeated, stretches nothing exponentially.

The general lemma behind the exponents, `hasLyapunovExponent_zero_of_linear_growth`, is stated for
any continuous linear map of a real normed space: a direction bounded below and growing at most
linearly has exponent `0`. It is the sub-exponential sibling of `hasLyapunovExponent_of_geometric_bounds`.

## Honest scope

* The shears here are the **linear** toral automorphisms `[[1,1],[0,1]]` and `[[1,0],[1,1]]`. They are
  not time-one maps of vector fields on `T²`: the plane flow `(x, y) ↦ (x, y + t x)` descends to the
  torus only at integer `t`. So nothing here is a flow, and the flux obstruction for *translation*
  fields on the torus (`LF4/ArenaStrokeFlux.lean`) is a statement about a different kind of map.
* `log ‖0‖ = 0` in Lean, so the zero direction has exponent `0` trivially; the shear theorems hold
  for every direction, zero included, which is why no nonvanishing hypothesis appears.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8;
`Mathlib/Dynamics/CatMapWitness.lean` (`cat`, `catHom`, `measurePreserving_cat`),
`Mathlib/Dynamics/LyapunovExponent.lean` (`HasLyapunovExponent`, `catR`, `hasLyapunovExponent_catR`);
`specs/BACKLOG.md` #153, #19, #148.
-/

@[expose] public section

open Filter Topology Real
open scoped goldenRatio

/-! ### Exponent zero from linear growth -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `log (n + 1) / n → 0`. -/
theorem tendsto_log_natCast_add_one_div : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (h.comp h2).congr fun n => ?_
  simp [Function.comp]

/-- **Exponent zero from linear growth**: a direction bounded away from zero whose iterates grow at
most linearly in the iterate count has Lyapunov exponent `0`. -/
theorem hasLyapunovExponent_zero_of_linear_growth (A : E →L[ℝ] E) (v : E) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hlow : ∀ n : ℕ, a ≤ ‖(A ^ n) v‖)
    (hup : ∀ n : ℕ, ‖(A ^ n) v‖ ≤ b * ((n : ℝ) + 1)) :
    HasLyapunovExponent A v 0 := by
  unfold HasLyapunovExponent
  have hlower : Tendsto (fun n : ℕ => Real.log a / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hupper : Tendsto (fun n : ℕ => Real.log b / n + Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log b)).add
      tendsto_log_natCast_add_one_div
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun n => ?_) (fun n => ?_)
  · exact div_le_div_of_nonneg_right (Real.log_le_log ha (hlow n)) (Nat.cast_nonneg n)
  · have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [← add_div, ← Real.log_mul hb.ne' hn1.ne']
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (lt_of_lt_of_le ha (hlow n)) (hup n)) (Nat.cast_nonneg n)

end General

namespace MeasureTheory

/-! ### The two shears on the torus -/

/-- The **horizontal shear** `(x, y) ↦ (x + y, y)` on `T²`: the first coordinate is translated by
the second. -/
noncomputable def shearX : Torus2 → Torus2 := fun p => (p.1 + p.2, p.2)

/-- The **vertical shear** `(x, y) ↦ (x, x + y)` on `T²`: the second coordinate is translated by
the first. -/
noncomputable def shearY : Torus2 → Torus2 := fun p => (p.1, p.1 + p.2)

/-- ★ **The cat map is the vertical shear followed by the horizontal one.** -/
theorem cat_eq_shearX_comp_shearY : cat = shearX ∘ shearY := by
  funext p
  exact Prod.ext (by simp only [cat, shearX, shearY, Function.comp_apply, two_zsmul]; abel)
    (by simp only [cat, shearX, shearY, Function.comp_apply])

lemma shearX_add (a b : Torus2) : shearX (a + b) = shearX a + shearX b :=
  Prod.ext (by simp only [shearX, Prod.fst_add, Prod.snd_add]; abel)
    (by simp only [shearX, Prod.snd_add])

lemma shearY_add (a b : Torus2) : shearY (a + b) = shearY a + shearY b :=
  Prod.ext (by simp only [shearY, Prod.fst_add])
    (by simp only [shearY, Prod.fst_add, Prod.snd_add]; abel)

/-- The horizontal shear as an additive monoid hom. -/
noncomputable def shearXHom : Torus2 →+ Torus2 := AddMonoidHom.mk' shearX shearX_add

/-- The vertical shear as an additive monoid hom. -/
noncomputable def shearYHom : Torus2 →+ Torus2 := AddMonoidHom.mk' shearY shearY_add

lemma continuous_shearX : Continuous shearX := by unfold shearX; fun_prop

lemma continuous_shearY : Continuous shearY := by unfold shearY; fun_prop

/-- The inverse horizontal shear `(x, y) ↦ (x − y, y)`. -/
noncomputable def shearXInv : Torus2 → Torus2 := fun q => (q.1 - q.2, q.2)

/-- The inverse vertical shear `(x, y) ↦ (x, y − x)`. -/
noncomputable def shearYInv : Torus2 → Torus2 := fun q => (q.1, q.2 - q.1)

lemma shearX_shearXInv (q : Torus2) : shearX (shearXInv q) = q := by
  refine Prod.ext ?_ ?_ <;> simp [shearX, shearXInv]

lemma shearXInv_shearX (p : Torus2) : shearXInv (shearX p) = p := by
  refine Prod.ext ?_ ?_ <;> simp [shearX, shearXInv]

lemma shearY_shearYInv (q : Torus2) : shearY (shearYInv q) = q := by
  refine Prod.ext ?_ ?_ <;> simp [shearY, shearYInv]

lemma shearYInv_shearY (p : Torus2) : shearYInv (shearY p) = p := by
  refine Prod.ext ?_ ?_ <;> simp [shearY, shearYInv]

lemma surjective_shearX : Function.Surjective shearX := fun q => ⟨shearXInv q, shearX_shearXInv q⟩

lemma surjective_shearY : Function.Surjective shearY := fun q => ⟨shearYInv q, shearY_shearYInv q⟩

/-- Each shear is a bijection of the torus. -/
theorem bijective_shearX : Function.Bijective shearX :=
  ⟨Function.LeftInverse.injective shearXInv_shearX, surjective_shearX⟩

theorem bijective_shearY : Function.Bijective shearY :=
  ⟨Function.LeftInverse.injective shearYInv_shearY, surjective_shearY⟩

/-- ★ **Each shear preserves Haar measure** — a continuous surjective endomorphism of a compact
group does. -/
theorem measurePreserving_shearX :
    MeasurePreserving shearX (volume : Measure Torus2) (volume : Measure Torus2) :=
  shearXHom.measurePreserving (μ := volume) (ν := volume) continuous_shearX surjective_shearX rfl

theorem measurePreserving_shearY :
    MeasurePreserving shearY (volume : Measure Torus2) (volume : Measure Torus2) :=
  shearYHom.measurePreserving (μ := volume) (ν := volume) continuous_shearY surjective_shearY rfl

/-! ### The linear lifts -/

/-- The horizontal shear `[[1,1],[0,1]]` of the plane: the lift of `shearX`. -/
noncomputable def shearXR : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The vertical shear `[[1,0],[1,1]]` of the plane: the lift of `shearY`. -/
noncomputable def shearYR : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma shearXR_apply (v : ℝ × ℝ) : shearXR v = (v.1 + v.2, v.2) := rfl

@[simp] lemma shearYR_apply (v : ℝ × ℝ) : shearYR v = (v.1, v.1 + v.2) := rfl

/-- `shearX` is `shearXR` read modulo `ℤ²`. -/
theorem shearX_coe (x y : ℝ) :
    shearX ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((shearXR (x, y)).1 : AddCircle (1 : ℝ)), ((shearXR (x, y)).2 : AddCircle (1 : ℝ))) := by
  simp [shearX]

/-- `shearY` is `shearYR` read modulo `ℤ²`. -/
theorem shearY_coe (x y : ℝ) :
    shearY ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((shearYR (x, y)).1 : AddCircle (1 : ℝ)), ((shearYR (x, y)).2 : AddCircle (1 : ℝ))) := by
  simp [shearY]

/-- ★ **The cat matrix is the product of the two shear matrices.** -/
theorem catR_eq_shearXR_comp_shearYR : catR = shearXR.comp shearYR := by
  refine ContinuousLinearMap.ext fun v => Prod.ext ?_ ?_
  · simp only [catR_apply, ContinuousLinearMap.comp_apply, shearXR_apply, shearYR_apply]
    ring
  · simp only [catR_apply, ContinuousLinearMap.comp_apply, shearXR_apply, shearYR_apply]

/-! ### The shears are symplectic -/

/-- The horizontal shear preserves the area form `u₁v₂ − u₂v₁`. -/
theorem shearXR_area (u v : ℝ × ℝ) :
    (shearXR u).1 * (shearXR v).2 - (shearXR u).2 * (shearXR v).1 = u.1 * v.2 - u.2 * v.1 := by
  simp; ring

/-- The vertical shear preserves the area form `u₁v₂ − u₂v₁`. -/
theorem shearYR_area (u v : ℝ × ℝ) :
    (shearYR u).1 * (shearYR v).2 - (shearYR u).2 * (shearYR v).1 = u.1 * v.2 - u.2 * v.1 := by
  simp; ring

/-- The cat matrix preserves the area form — as the composition of two maps that do. -/
theorem catR_area (u v : ℝ × ℝ) :
    (catR u).1 * (catR v).2 - (catR u).2 * (catR v).1 = u.1 * v.2 - u.2 * v.1 := by
  simp; ring

/-! ### Neither shear stretches -/

/-- The iterates of the horizontal shear: `(x, y) ↦ (x + n y, y)`. -/
theorem shearXR_pow_apply (n : ℕ) (v : ℝ × ℝ) :
    (shearXR ^ n) v = (v.1 + (n : ℝ) * v.2, v.2) := by
  induction n generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih]
      exact Prod.ext (by simp; ring) (by simp)

/-- The iterates of the vertical shear: `(x, y) ↦ (x, n x + y)`. -/
theorem shearYR_pow_apply (n : ℕ) (v : ℝ × ℝ) :
    (shearYR ^ n) v = (v.1, (n : ℝ) * v.1 + v.2) := by
  induction n generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih]
      exact Prod.ext (by simp) (by simp; ring)

/-- A pair whose first entry is `x + n y` has norm at most `(n + 1)` times the norm of `(x, y)`. -/
lemma norm_shear_pair_le (x y : ℝ) (n : ℕ) :
    ‖(x + (n : ℝ) * y, y)‖ ≤ ‖(x, y)‖ * ((n : ℝ) + 1) := by
  have h1 : ‖x‖ ≤ ‖(x, y)‖ := norm_fst_le (x, y)
  have h2 : ‖y‖ ≤ ‖(x, y)‖ := norm_snd_le (x, y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖x + (n : ℝ) * y‖ ≤ ‖x‖ + ‖(n : ℝ) * y‖ := norm_add_le _ _
      _ = ‖x‖ + (n : ℝ) * ‖y‖ := by rw [norm_mul, Real.norm_natCast]
      _ ≤ ‖(x, y)‖ + (n : ℝ) * ‖(x, y)‖ := by gcongr
      _ = ‖(x, y)‖ * ((n : ℝ) + 1) := by ring
  · calc ‖y‖ ≤ ‖(x, y)‖ := h2
      _ ≤ ‖(x, y)‖ * ((n : ℝ) + 1) :=
          le_mul_of_one_le_right (norm_nonneg _) (by linarith)

/-- The vertical twin: a pair whose second entry is `n x + y` has norm at most `(n + 1)` times the
norm of `(x, y)`. -/
lemma norm_shear_pair_le' (x y : ℝ) (n : ℕ) :
    ‖(x, (n : ℝ) * x + y)‖ ≤ ‖(x, y)‖ * ((n : ℝ) + 1) := by
  have h1 : ‖x‖ ≤ ‖(x, y)‖ := norm_fst_le (x, y)
  have h2 : ‖y‖ ≤ ‖(x, y)‖ := norm_snd_le (x, y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖x‖ ≤ ‖(x, y)‖ := h1
      _ ≤ ‖(x, y)‖ * ((n : ℝ) + 1) :=
          le_mul_of_one_le_right (norm_nonneg _) (by linarith)
  · calc ‖(n : ℝ) * x + y‖ ≤ ‖(n : ℝ) * x‖ + ‖y‖ := norm_add_le _ _
      _ = (n : ℝ) * ‖x‖ + ‖y‖ := by rw [norm_mul, Real.norm_natCast]
      _ ≤ (n : ℝ) * ‖(x, y)‖ + ‖(x, y)‖ := by gcongr
      _ = ‖(x, y)‖ * ((n : ℝ) + 1) := by ring

/-- ★★ **The horizontal shear has Lyapunov exponent `0` in every direction.** -/
theorem hasLyapunovExponent_shearXR (v : ℝ × ℝ) : HasLyapunovExponent shearXR v 0 := by
  by_cases hv : v.2 = 0
  · -- the direction is fixed: `(shearXR ^ n) v = v`
    have h : ∀ n : ℕ, (shearXR ^ n) v = v := fun n => by
      rw [shearXR_pow_apply]
      exact Prod.ext (by simp [hv]) rfl
    unfold HasLyapunovExponent
    simp only [h]
    exact tendsto_const_div_atTop_nhds_zero_nat _
  · refine hasLyapunovExponent_zero_of_linear_growth shearXR v (a := ‖v.2‖) (b := ‖v‖)
      (norm_pos_iff.2 hv) (norm_pos_iff.2 fun h => hv (by rw [h]; rfl)) (fun n => ?_) (fun n => ?_)
    · rw [shearXR_pow_apply]
      exact norm_snd_le ((v.1 + (n : ℝ) * v.2, v.2) : ℝ × ℝ)
    · rw [shearXR_pow_apply]
      exact norm_shear_pair_le v.1 v.2 n

/-- ★★ **The vertical shear has Lyapunov exponent `0` in every direction.** -/
theorem hasLyapunovExponent_shearYR (v : ℝ × ℝ) : HasLyapunovExponent shearYR v 0 := by
  by_cases hv : v.1 = 0
  · have h : ∀ n : ℕ, (shearYR ^ n) v = v := fun n => by
      rw [shearYR_pow_apply]
      exact Prod.ext rfl (by simp [hv])
    unfold HasLyapunovExponent
    simp only [h]
    exact tendsto_const_div_atTop_nhds_zero_nat _
  · refine hasLyapunovExponent_zero_of_linear_growth shearYR v (a := ‖v.1‖) (b := ‖v‖)
      (norm_pos_iff.2 hv) (norm_pos_iff.2 fun h => hv (by rw [h]; rfl)) (fun n => ?_) (fun n => ?_)
    · rw [shearYR_pow_apply]
      exact norm_fst_le ((v.1, (n : ℝ) * v.1 + v.2) : ℝ × ℝ)
    · rw [shearYR_pow_apply]
      exact norm_shear_pair_le' v.1 v.2 n

/-! ### ★★★ The package -/

/-- ★★★ **The cat map is two transverse shears, and the stretching belongs to neither.** The cat map
is the vertical shear followed by the horizontal one; each shear preserves Haar measure; the lift
of each shear has Lyapunov exponent `0` in every direction; and their composition `catR` has
exponent `2 log φ` in every direction off the stable line. Hyperbolicity is the work of the
transversality, not of either factor. -/
theorem cat_two_shears :
    cat = shearX ∘ shearY
      ∧ MeasurePreserving shearX (volume : Measure Torus2) volume
      ∧ MeasurePreserving shearY (volume : Measure Torus2) volume
      ∧ catR = shearXR.comp shearYR
      ∧ (∀ v : ℝ × ℝ, HasLyapunovExponent shearXR v 0)
      ∧ (∀ v : ℝ × ℝ, HasLyapunovExponent shearYR v 0)
      ∧ (∀ v : ℝ × ℝ, ellUR v ≠ 0 → HasLyapunovExponent catR v (2 * Real.log φ)) :=
  ⟨cat_eq_shearX_comp_shearY, measurePreserving_shearX, measurePreserving_shearY,
    catR_eq_shearXR_comp_shearYR, hasLyapunovExponent_shearXR, hasLyapunovExponent_shearYR,
    fun _ hv => hasLyapunovExponent_catR hv⟩

end MeasureTheory

end
