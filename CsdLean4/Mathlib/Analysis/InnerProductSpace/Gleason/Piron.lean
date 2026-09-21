/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Gleason's theorem, finite-dimensional: latitudes, descents and Piron's geometric lemma

**Category:** 1-Mathlib (CSD-free; staged for upstream). `specs/gleason-feasibility.md`, stage
57(b): Cooke–Keane–Moran §4 (the vocabulary) and the **geometric lemma** of §5, due to Piron —
the one step of the core lemma with no Mathlib support, and the decision point of the plan.

Fix a unit vector `p`, the *north pole*. For a unit vector `s`:

* `latitude p s = ⟪p, s⟫²`; `northern p` is the closed northern hemisphere `⟪p, s⟫ ≥ 0`,
  `equator p` its boundary;
* `coldest p s` is the unit vector orthogonal to `s` in the plane of `p` and `s` with
  `latitude p (coldest p s) = 1 − latitude p s` — the coldest vector orthogonal to `s`;
* `descent p s = {t ∈ northern p : t ⟂ coldest p s}` is the great (half) circle through `s`
  that has `s` as its northernmost point (CKM's `D_s`).

**The gnomonic dictionary.** Projecting the open northern hemisphere from the origin onto the
tangent plane at `p` sends `s` to `⟪p, s⟫⁻¹ s − p`; conversely `lift p v = (p + v)/‖p + v‖` for
`v ⟂ p`. Latitude circles become circles centred at `p`, and `lift p w ∈ descent p (lift p v)`
iff `⟪w, v⟫ = ‖v‖²` (`lift_mem_descent_iff`) — the descent through `s` is the tangent line to
its latitude circle. Reading the tangent plane as `ℂ` through an orthonormal pair `e₁, e₂ ⟂ p`
(`tangent e₁ e₂ z = Re z • e₁ + Im z • e₂`), the condition is `Re (w · conj z) = ‖z‖²`.

**Piron's geometric lemma** (`exists_descent_chain`): if `s, t ∈ northern p \ {p}` and
`latitude p t < latitude p s`, there is a finite chain `s = c 0, c 1, …, c n = t` with each
`c (i+1) ∈ descent p (c i)`. Proof, in the plane: the explicit spiral
`zₖ = z₀ (cos θ)⁻ᵏ e^{ikθ}` with `θ = δ/n` turns by the angle `δ` from `z₀` to the ray of `ζ`
while growing by the factor `(cos θ)⁻ⁿ`, which tends to `1` (`cos x ≥ 1 − x²/2` and Bernoulli),
so for large `n` it stops short of `ζ` on its ray; two more steps along that ray reach `ζ`
(`descent_step_ray`). A target on the equator is reached from any point orthogonal to it
(`mem_descent_of_equator`), so the spiral is aimed at the direction perpendicular to `t`.

## Source

Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117–128, §4 and the
Geometric Lemma of §5 (with Figs. 1–3); Piron, *Foundations of Quantum Physics* (1976).
-/

@[expose] public section

open Matrix Real
open scoped Matrix InnerProductSpace ComplexConjugate

namespace Gleason

/-! ### The pole, latitudes, the coldest vector, descents -/

/-- The latitude of `s` seen from the pole `p`: `cos² θ(p, s) = ⟪p, s⟫²`. -/
noncomputable def latitude (p s : EuclideanSpace ℝ (Fin 3)) : ℝ := ⟪p, s⟫_ℝ ^ 2

/-- The closed northern hemisphere. -/
def northern (p : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {s | ‖s‖ = 1 ∧ 0 ≤ ⟪p, s⟫_ℝ}

/-- The equator. -/
def equator (p : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {s | ‖s‖ = 1 ∧ ⟪p, s⟫_ℝ = 0}

/-- The coldest unit vector orthogonal to `s`: the normalisation of `p − ⟪p, s⟫ s`. -/
noncomputable def coldest (p s : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (‖p - ⟪p, s⟫_ℝ • s‖⁻¹ : ℝ) • (p - ⟪p, s⟫_ℝ • s)

/-- The descent through `s`: the great half circle in the northern hemisphere orthogonal to
`coldest p s`, which has `s` as its northernmost point. -/
def descent (p s : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {t | t ∈ northern p ∧ ⟪t, coldest p s⟫_ℝ = 0}

lemma equator_subset_northern (p : EuclideanSpace ℝ (Fin 3)) : equator p ⊆ northern p :=
  fun _ h => ⟨h.1, h.2.ge⟩

lemma inner_coldest_self (p : EuclideanSpace ℝ (Fin 3)) {s : EuclideanSpace ℝ (Fin 3)}
    (hs : ‖s‖ = 1) : ⟪s, coldest p s⟫_ℝ = 0 := by
  rw [coldest, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hs, real_inner_comm]
  ring

/-- A point of the equator orthogonal to `s` lies on the descent through `s`. -/
lemma mem_descent_of_equator {p s t : EuclideanSpace ℝ (Fin 3)} (ht : t ∈ equator p)
    (hts : ⟪t, s⟫_ℝ = 0) : t ∈ descent p s := by
  refine ⟨equator_subset_northern p ht, ?_⟩
  rw [coldest, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_comm p t, ht.2,
    hts]
  ring

/-- Every point is on its own descent. -/
lemma self_mem_descent {p s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    s ∈ descent p s :=
  ⟨hs, inner_coldest_self p hs.1⟩

/-! ### The gnomonic lift -/

/-- The point of the open northern hemisphere over the tangent vector `v ⟂ p`:
`(p + v)/‖p + v‖`. -/
noncomputable def lift (p v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (‖p + v‖⁻¹ : ℝ) • (p + v)

section Lift

variable {p v w : EuclideanSpace ℝ (Fin 3)}

lemma norm_sq_add_of_inner_zero (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) :
    ‖p + v‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, hp, hv]; ring

lemma norm_add_pos (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : 0 < ‖p + v‖ := by
  have h := norm_sq_add_of_inner_zero hp hv
  have := norm_nonneg (p + v)
  nlinarith [sq_nonneg ‖v‖]

lemma norm_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : ‖lift p v‖ = 1 := by
  have h := norm_add_pos hp hv
  rw [lift, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']

lemma inner_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : ⟪p, lift p v⟫_ℝ = ‖p + v‖⁻¹ := by
  rw [lift, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hp, hv]
  ring

lemma inner_lift_pos (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : 0 < ⟪p, lift p v⟫_ℝ := by
  rw [inner_lift hp hv]; exact inv_pos.mpr (norm_add_pos hp hv)

lemma lift_mem_northern (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) : lift p v ∈ northern p :=
  ⟨norm_lift hp hv, (inner_lift_pos hp hv).le⟩

lemma lift_ne_pole (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hv0 : v ≠ 0) : lift p v ≠ p := by
  intro h
  have h1 : ⟪p, lift p v⟫_ℝ = 1 := by rw [h, real_inner_self_eq_norm_sq, hp]; norm_num
  rw [inner_lift hp hv, inv_eq_one] at h1
  have h2 := norm_sq_add_of_inner_zero hp hv
  rw [h1] at h2
  have : ‖v‖ ^ 2 = 0 := by linarith
  exact hv0 (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

lemma latitude_lift (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) :
    latitude p (lift p v) = 1 / (1 + ‖v‖ ^ 2) := by
  rw [latitude, inner_lift hp hv, inv_pow, ← norm_sq_add_of_inner_zero hp hv, one_div]

/-- Latitudes of lifts compare inversely to the norms of the tangent vectors. -/
lemma latitude_lift_lt_iff (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hw : ⟪p, w⟫_ℝ = 0) :
    latitude p (lift p w) < latitude p (lift p v) ↔ ‖v‖ < ‖w‖ := by
  rw [latitude_lift hp hv, latitude_lift hp hw, one_div_lt_one_div (by positivity) (by positivity)]
  constructor
  · intro h; nlinarith [norm_nonneg v, norm_nonneg w]
  · intro h; nlinarith [norm_nonneg v, norm_nonneg w]

/-- Every point of the open northern hemisphere is the lift of `⟪p, s⟫⁻¹ s − p`. -/
lemma eq_lift_of_northern (hp : ‖p‖ = 1) {s : EuclideanSpace ℝ (Fin 3)} (hs : ‖s‖ = 1)
    (hps : 0 < ⟪p, s⟫_ℝ) :
    ⟪p, (⟪p, s⟫_ℝ)⁻¹ • s - p⟫_ℝ = 0 ∧ s = lift p ((⟪p, s⟫_ℝ)⁻¹ • s - p) := by
  have h1 : ⟪p, (⟪p, s⟫_ℝ)⁻¹ • s - p⟫_ℝ = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hp,
      inv_mul_cancel₀ hps.ne']
    ring
  refine ⟨h1, ?_⟩
  have h2 : p + ((⟪p, s⟫_ℝ)⁻¹ • s - p) = (⟪p, s⟫_ℝ)⁻¹ • s := by abel
  rw [lift, h2, norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hps), inv_inv,
    smul_smul, mul_inv_cancel₀ hps.ne', one_smul]

/-- **The gnomonic dictionary.** `lift p w` lies on the descent through `lift p v` iff
`⟪w, v⟫ = ‖v‖²`: the descent is the tangent line to the latitude circle. -/
lemma lift_mem_descent_iff (hp : ‖p‖ = 1) (hv : ⟪p, v⟫_ℝ = 0) (hw : ⟪p, w⟫_ℝ = 0)
    (hv0 : v ≠ 0) : lift p w ∈ descent p (lift p v) ↔ ⟪w, v⟫_ℝ = ‖v‖ ^ 2 := by
  have hc := inner_lift hp hv
  set c : ℝ := ‖p + v‖⁻¹ with hcdef
  have hcpos : 0 < c := inv_pos.mpr (norm_add_pos hp hv)
  have hc2 : c ^ 2 * (1 + ‖v‖ ^ 2) = 1 := by
    rw [hcdef, inv_pow, ← norm_sq_add_of_inner_zero hp hv, inv_mul_cancel₀]
    exact (pow_pos (norm_add_pos hp hv) 2).ne'
  -- the unnormalised coldest vector
  have hx : p - ⟪p, lift p v⟫_ℝ • lift p v = (1 - c ^ 2) • p - c ^ 2 • v := by
    rw [hc, lift, ← hcdef, smul_smul, ← sq, smul_add, sub_smul, one_smul]
    abel
  have hxne : (1 - c ^ 2) • p - c ^ 2 • v ≠ 0 := by
    intro h
    have h1 : ⟪v, (1 - c ^ 2) • p - c ^ 2 • v⟫_ℝ = -(c ^ 2 * ‖v‖ ^ 2) := by
      rw [inner_sub_right, inner_smul_right, inner_smul_right, real_inner_comm p v, hv,
        real_inner_self_eq_norm_sq]
      ring
    rw [h, inner_zero_right] at h1
    have h2 : c ^ 2 * ‖v‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (pow_pos hcpos 2).ne' h3
    · exact hv0 (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))
  have hin : ⟪lift p w, coldest p (lift p v)⟫_ℝ
      = ‖p + w‖⁻¹ * ‖(1 - c ^ 2) • p - c ^ 2 • v‖⁻¹ * ((1 - c ^ 2) - c ^ 2 * ⟪w, v⟫_ℝ) := by
    rw [coldest, hx, lift, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
      inner_sub_right, inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hp, hv, real_inner_comm p w, hw]
    simp only [RCLike.conj_to_real]
    ring
  constructor
  · rintro ⟨-, h⟩
    rw [hin] at h
    have hne : ‖p + w‖⁻¹ * ‖(1 - c ^ 2) • p - c ^ 2 • v‖⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero (norm_add_pos hp hw).ne') (inv_ne_zero (norm_ne_zero_iff.mpr hxne))
    have h' : (1 - c ^ 2) - c ^ 2 * ⟪w, v⟫_ℝ = 0 := (mul_eq_zero.mp h).resolve_left hne
    have hc0 : c ^ 2 ≠ 0 := (pow_pos hcpos 2).ne'
    field_simp
    nlinarith [hc2, h']
  · intro h
    refine ⟨lift_mem_northern hp hw, ?_⟩
    rw [hin, h]
    have : (1 - c ^ 2) - c ^ 2 * ‖v‖ ^ 2 = 0 := by linarith
    rw [this, mul_zero]

end Lift

/-! ### The tangent plane as `ℂ` -/

/-- The tangent vector with complex coordinate `z` in the orthonormal frame `(e₁, e₂)` of the
tangent plane at the pole. -/
noncomputable def tangent (e₁ e₂ : EuclideanSpace ℝ (Fin 3)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  z.re • e₁ + z.im • e₂

section Tangent

variable {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)} (he : Orthonormal ℝ ![p, e₁, e₂])
include he

lemma inner_tangent_tangent (z w : ℂ) :
    ⟪tangent e₁ e₂ z, tangent e₁ e₂ w⟫_ℝ = (z * conj w).re := by
  obtain ⟨-, h1, h2, -, -, h12⟩ := orthonormal_triple_iff.mp he
  have h21 : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm, h12]
  have h11 : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : ⟪e₂, e₂⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h2]; norm_num
  simp only [tangent, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h11,
    h22, h12, h21, RCLike.conj_to_real, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma norm_sq_tangent (z : ℂ) : ‖tangent e₁ e₂ z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangent_tangent he, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_re]

lemma norm_tangent (z : ℂ) : ‖tangent e₁ e₂ z‖ = ‖z‖ := by
  have h := norm_sq_tangent he z
  have := norm_nonneg (tangent e₁ e₂ z)
  have := norm_nonneg z
  nlinarith

lemma inner_pole_tangent (z : ℂ) : ⟪p, tangent e₁ e₂ z⟫_ℝ = 0 := by
  obtain ⟨-, -, -, h01, h02, -⟩ := orthonormal_triple_iff.mp he
  simp [tangent, inner_add_right, inner_smul_right, h01, h02]

lemma tangent_ne_zero {z : ℂ} (hz : z ≠ 0) : tangent e₁ e₂ z ≠ 0 := by
  intro h
  have := norm_tangent he z
  rw [h, norm_zero] at this
  exact hz (norm_eq_zero.mp this.symm)

/-- Every tangent vector has a complex coordinate. -/
lemma exists_tangent_eq {v : EuclideanSpace ℝ (Fin 3)} (hv : ⟪p, v⟫_ℝ = 0) :
    ∃ z : ℂ, tangent e₁ e₂ z = v := by
  refine ⟨⟨⟪e₁, v⟫_ℝ, ⟪e₂, v⟫_ℝ⟩, ?_⟩
  have h := (orthonormalBasisOfTriple he).sum_repr' v
  simp only [coe_orthonormalBasisOfTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, hv, zero_smul, zero_add] at h
  simpa [tangent] using h

end Tangent

/-! ### Descent steps in the plane -/

/-- The complex form of the gnomonic dictionary: `lift (tangent w) ∈ descent (lift (tangent z))`
iff `Re (w · conj z) = ‖z‖²`. -/
lemma lift_tangent_mem_descent_iff {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)}
    (he : Orthonormal ℝ ![p, e₁, e₂]) {z w : ℂ} (hz : z ≠ 0) :
    lift p (tangent e₁ e₂ w) ∈ descent p (lift p (tangent e₁ e₂ z))
      ↔ (w * conj z).re = ‖z‖ ^ 2 := by
  have hp : ‖p‖ = 1 := (orthonormal_triple_iff.mp he).1
  rw [lift_mem_descent_iff hp (inner_pole_tangent he z) (inner_pole_tangent he w)
    (tangent_ne_zero he hz), inner_tangent_tangent he, norm_sq_tangent he]

/-- **Two steps along a ray:** from `ρ ζ` to `ζ` (`0 < ρ ≤ 1`) through `ρ ζ (1 + i μ)` with
`μ² = 1/ρ − 1`. -/
lemma descent_step_ray (ζ : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I) * conj ((ρ : ℂ) * ζ)).re
        = ‖(ρ : ℂ) * ζ‖ ^ 2 ∧
      (ζ * conj ((ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I))).re
        = ‖(ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I)‖ ^ 2 := by
  have hμ : Real.sqrt (1 / ρ - 1) ^ 2 = 1 / ρ - 1 := Real.sq_sqrt (by
    rw [sub_nonneg, one_div, one_le_inv₀ hρ0]; exact hρ1)
  have hμρ : ρ * Real.sqrt (1 / ρ - 1) ^ 2 = 1 - ρ := by
    rw [hμ]; field_simp
  constructor
  · simp only [Complex.sq_norm, Complex.normSq_apply, map_mul, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.sq_norm, Complex.normSq_apply, map_mul, map_add, map_one,
      Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
      Complex.neg_im]
    linear_combination (-(ρ * (ζ.re ^ 2 + ζ.im ^ 2))) * hμρ

/-! ### The spiral -/

/-- The spiral `zₖ = z₀ (cos θ)⁻ᵏ e^{ikθ}`: each point lies on the descent through the previous
one (`spiral_step`), the argument advances by `θ` and the modulus grows by `(cos θ)⁻¹`. -/
noncomputable def spiral (z₀ : ℂ) (θ : ℝ) (k : ℕ) : ℂ :=
  z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ k * Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)

lemma spiral_zero (z₀ : ℂ) (θ : ℝ) : spiral z₀ θ 0 = z₀ := by
  simp [spiral]

lemma spiral_ne_zero {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    spiral z₀ θ k ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero hz₀ (pow_ne_zero _ ?_)) (Complex.exp_ne_zero _)
  exact_mod_cast (inv_pos.mpr hcos).ne'

lemma norm_sq_spiral {z₀ : ℂ} {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    ‖spiral z₀ θ k‖ ^ 2 = ‖z₀‖ ^ 2 * ((Real.cos θ)⁻¹) ^ (2 * k) := by
  rw [spiral, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcos), mul_pow, ← pow_mul,
    mul_comm k 2]

/-- The product `zₖ₊₁ · conj zₖ = ‖z₀‖² (cos θ)⁻⁽²ᵏ⁺¹⁾ e^{iθ}`. -/
lemma spiral_succ_mul_conj (z₀ : ℂ) (θ : ℝ) (k : ℕ) :
    spiral z₀ θ (k + 1) * conj (spiral z₀ θ k)
      = ((Complex.normSq z₀ : ℝ) : ℂ) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
        * Complex.exp ((θ : ℂ) * Complex.I) := by
  have hconj : conj (Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hexp : Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
      * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [spiral, map_mul, map_pow, Complex.conj_ofReal, hconj]
  calc z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (k + 1)
        * Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
        * (conj z₀ * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ k
          * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)))
      = (z₀ * conj z₀) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
        * (Complex.exp (((((k + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I))) := by
        rw [show 2 * k + 1 = (k + 1) + k by ring, pow_add]
        ring
    _ = _ := by rw [Complex.mul_conj, hexp]

/-- **Each spiral point lies on the descent through the previous one.** -/
lemma spiral_step (z₀ : ℂ) {θ : ℝ} (hcos : 0 < Real.cos θ) (k : ℕ) :
    (spiral z₀ θ (k + 1) * conj (spiral z₀ θ k)).re = ‖spiral z₀ θ k‖ ^ 2 := by
  rw [spiral_succ_mul_conj, norm_sq_spiral hcos]
  have h1 : ((Complex.normSq z₀ : ℝ) : ℂ) * (((Real.cos θ)⁻¹ : ℝ) : ℂ) ^ (2 * k + 1)
      = ((Complex.normSq z₀ * ((Real.cos θ)⁻¹) ^ (2 * k + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.normSq_eq_norm_sq]
  have h2 : (Real.cos θ)⁻¹ ^ (2 * k + 1) * Real.cos θ = (Real.cos θ)⁻¹ ^ (2 * k) := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hcos.ne', mul_one]
  rw [mul_assoc, h2]

/-- The spiral's endpoint when the angle is `arg u / n`: `zₙ = z₀ (cos θ)⁻ⁿ u`. -/
lemma spiral_end {z₀ u : ℂ} (hu : ‖u‖ = 1) {n : ℕ} (hn : n ≠ 0) :
    spiral z₀ (Complex.arg u / n) n
      = z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u := by
  rw [spiral]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : ((n : ℝ) * (Complex.arg u / n) : ℝ) = Complex.arg u := by field_simp
  rw [this]
  have h := Complex.norm_mul_exp_arg_mul_I u
  rwa [hu, Complex.ofReal_one, one_mul] at h

/-- `cos θ > 0` for `θ = arg u / n`, `n ≥ 3`. -/
lemma cos_arg_div_pos (u : ℂ) {n : ℕ} (hn : 3 ≤ n) : 0 < Real.cos (Complex.arg u / n) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have habs := Complex.abs_arg_le_pi u
  have hpi := Real.pi_pos
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by linarith)]
    have := (abs_le.mp habs).1
    nlinarith
  · rw [div_lt_iff₀ (by linarith)]
    have := (abs_le.mp habs).2
    nlinarith

/-- **The growth factor tends to one:** `(cos (arg u / n))ⁿ ≥ 1 − π²/(2n)` for `n ≥ 3`, by
`cos x ≥ 1 − x²/2` and Bernoulli's inequality. -/
lemma one_sub_le_cos_arg_div_pow (u : ℂ) {n : ℕ} (hn : 3 ≤ n) :
    1 - Real.pi ^ 2 / (2 * n) ≤ Real.cos (Complex.arg u / n) ^ n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have habs := Complex.abs_arg_le_pi u
  have hpi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  set a : ℝ := -(Real.pi ^ 2 / (2 * n ^ 2)) with ha
  have ha2 : -2 ≤ a := by
    rw [ha, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    nlinarith
  have hcos : 1 + a ≤ Real.cos (Complex.arg u / n) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := Complex.arg u / n)
    have h2 : (Complex.arg u / n) ^ 2 ≤ Real.pi ^ 2 / n ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right
        (by nlinarith [sq_abs (Complex.arg u), abs_nonneg (Complex.arg u)]) (by positivity)
    rw [ha]
    have : Real.pi ^ 2 / (2 * n ^ 2) = (Real.pi ^ 2 / n ^ 2) / 2 := by ring
    rw [this]
    linarith
  have h0 : 0 ≤ 1 + a := by
    rw [ha, ← sub_eq_add_neg, sub_nonneg, div_le_one (by positivity)]
    nlinarith
  calc 1 - Real.pi ^ 2 / (2 * n) = 1 + n * a := by rw [ha]; field_simp; ring
    _ ≤ (1 + a) ^ n := one_add_mul_le_pow ha2 n
    _ ≤ Real.cos (Complex.arg u / n) ^ n := pow_le_pow_left₀ h0 hcos n

/-! ### Piron's geometric lemma -/

/-- A descent chain of length `n` from `s` to `t` in the northern hemisphere minus the pole. -/
structure IsDescentChain (p s t : EuclideanSpace ℝ (Fin 3)) (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin 3)) : Prop where
  /-- The chain starts at `s`. -/
  head : c 0 = s
  /-- The chain ends at `t`. -/
  last : c n = t
  /-- Every point is in the northern hemisphere and is not the pole. -/
  mem : ∀ i, i ≤ n → c i ∈ northern p ∧ c i ≠ p
  /-- Each point lies on the descent through the previous one. -/
  step : ∀ i, i < n → c (i + 1) ∈ descent p (c i)

section Spiral

variable {p e₁ e₂ : EuclideanSpace ℝ (Fin 3)} (he : Orthonormal ℝ ![p, e₁, e₂])
include he

/-- The lifted spiral is a descent chain of its own points. -/
lemma spiral_chain_step {z₀ : ℂ} {θ : ℝ} (hz₀ : z₀ ≠ 0) (hcos : 0 < Real.cos θ) (k : ℕ) :
    lift p (tangent e₁ e₂ (spiral z₀ θ (k + 1)))
      ∈ descent p (lift p (tangent e₁ e₂ (spiral z₀ θ k))) := by
  rw [lift_tangent_mem_descent_iff he (spiral_ne_zero hz₀ hcos k)]
  exact spiral_step z₀ hcos k

lemma lift_tangent_mem (z : ℂ) (hz : z ≠ 0) :
    lift p (tangent e₁ e₂ z) ∈ northern p ∧ lift p (tangent e₁ e₂ z) ≠ p :=
  have hp : ‖p‖ = 1 := (orthonormal_triple_iff.mp he).1
  ⟨lift_mem_northern hp (inner_pole_tangent he z),
    lift_ne_pole hp (inner_pole_tangent he z) (tangent_ne_zero he hz)⟩

end Spiral

/-- **Piron's geometric lemma (CKM §5).** If `s, t` lie in the northern hemisphere, are not the
pole, and `t` is strictly lower than `s`, there is a finite chain of descents from `s` to `t`. -/
theorem exists_descent_chain {p s t : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1)
    (hs : s ∈ northern p) (hsp : s ≠ p) (ht : t ∈ northern p) (htp : t ≠ p)
    (hl : latitude p t < latitude p s) :
    ∃ (n : ℕ) (c : ℕ → EuclideanSpace ℝ (Fin 3)), 1 ≤ n ∧ IsDescentChain p s t n c := by
  -- the frame of the tangent plane
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  set e₂ := cross p e₁ with he₂
  have he : Orthonormal ℝ ![p, e₁, e₂] := orthonormal_cross hp he₁ hpe₁
  -- `s` is the lift of a nonzero tangent vector with coordinate `z₀`
  have hps : 0 < ⟪p, s⟫_ℝ := by
    rcases eq_or_lt_of_le hs.2 with h | h
    · exfalso
      have : latitude p s = 0 := by rw [latitude, ← h]; ring
      rw [this] at hl
      exact absurd hl (not_lt.mpr (sq_nonneg _))
    · exact h
  obtain ⟨hvs, hsl⟩ := eq_lift_of_northern hp hs.1 hps
  obtain ⟨z₀, hz₀⟩ := exists_tangent_eq he hvs
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl
    apply hsp
    rw [hsl, ← hz₀]
    simp [tangent, lift, hp]
  have hx : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀0
  -- the spiral construction, shared by both cases: aim at the unit direction `u`
  have spiral_reach : ∀ u : ℂ, ‖u‖ = 1 → ∀ n : ℕ, 3 ≤ n →
      ∃ c : ℕ → EuclideanSpace ℝ (Fin 3), c 0 = s ∧
        c n = lift p (tangent e₁ e₂ (z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u))
        ∧ (∀ i, i ≤ n → c i ∈ northern p ∧ c i ≠ p) ∧
        ∀ i, i < n → c (i + 1) ∈ descent p (c i) := by
    intro u hu n hn
    have hcos := cos_arg_div_pos u hn
    refine ⟨fun k => lift p (tangent e₁ e₂ (spiral z₀ (Complex.arg u / n) k)), ?_, ?_, ?_, ?_⟩
    · simp only [spiral_zero]
      rw [hz₀, ← hsl]
    · show lift p (tangent e₁ e₂ (spiral z₀ (Complex.arg u / n) n)) = _
      rw [spiral_end hu (by omega)]
    · intro i _
      exact lift_tangent_mem he _ (spiral_ne_zero hz₀0 hcos i)
    · intro i _
      exact spiral_chain_step he hz₀0 hcos i
  rcases eq_or_lt_of_le ht.2 with hpt | hpt
  · -- `t` on the equator: aim the spiral at the direction perpendicular to `t`
    obtain ⟨τ, hτ⟩ := exists_tangent_eq he hpt.symm
    have hτ1 : ‖τ‖ = 1 := by rw [← norm_tangent he τ, hτ, ht.1]
    set u : ℂ := Complex.I * τ * (‖z₀‖ : ℂ) / z₀ with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, norm_mul, Complex.norm_I, hτ1, Complex.norm_real,
        Real.norm_eq_abs, abs_norm, one_mul, one_mul, div_self hx.ne']
    obtain ⟨c, hc0, hcn, hcmem, hcstep⟩ := spiral_reach u hu1 3 le_rfl
    refine ⟨4, fun k => if k ≤ 3 then c k else t, le_add_left le_rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hc0
    · simp
    · intro i hi
      split_ifs with h
      · exact hcmem i h
      · exact ⟨ht, htp⟩
    · intro i hi
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · rw [if_pos (by omega : i + 1 ≤ 3), if_pos h3.le]
        exact hcstep i h3
      · have hi3 : i = 3 := by omega
        rw [hi3, if_neg (by omega : ¬ (3 + 1 ≤ 3)), if_pos le_rfl, hcn]
        refine mem_descent_of_equator ⟨ht.1, hpt.symm⟩ ?_
        -- `⟪t, lift (tangent w)⟫ = 0` because `Re (τ · conj w) = 0` for `w ∝ i τ`
        rw [lift, inner_smul_right, inner_add_right, real_inner_comm p t, hpt.symm, ← hτ,
          inner_tangent_tangent he]
        have hw : (τ * conj (z₀ * (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ : ℝ) : ℂ) ^ 3
            * u)).re = 0 := by
          have hz₀' : z₀ * (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ : ℝ) : ℂ) ^ 3 * u
              = (((Real.cos (Complex.arg u / ((3 : ℕ) : ℝ)))⁻¹ ^ 3 * ‖z₀‖ : ℝ) : ℂ)
                * (Complex.I * τ) := by
            rw [hu]
            field_simp
            push_cast
            ring
          simp only [hz₀', map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
            Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
          ring
        rw [hw]
        ring
  · -- `t` is the lift of a nonzero tangent vector with coordinate `ζ`, `‖z₀‖ < ‖ζ‖`
    obtain ⟨hvt, htl⟩ := eq_lift_of_northern hp ht.1 hpt
    obtain ⟨ζ, hζ⟩ := exists_tangent_eq he hvt
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      apply htp
      rw [htl, ← hζ]
      simp [tangent, lift, hp]
    have hy : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    have hxy : ‖z₀‖ < ‖ζ‖ := by
      rw [hsl, htl, ← hz₀, ← hζ, latitude_lift_lt_iff hp (inner_pole_tangent he z₀)
        (inner_pole_tangent he ζ), norm_tangent he, norm_tangent he] at hl
      exact hl
    -- the direction of `ζ` seen from `z₀`
    set u : ℂ := ζ * (‖z₀‖ : ℂ) / (z₀ * (‖ζ‖ : ℂ)) with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm, mul_comm ‖z₀‖,
        div_self (mul_ne_zero hy.ne' hx.ne')]
    -- `n` large enough that the spiral stops short of `ζ`
    have hratio : ‖z₀‖ / ‖ζ‖ < 1 := (div_lt_one hy).mpr hxy
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (Real.pi ^ 2 / (2 * (1 - ‖z₀‖ / ‖ζ‖)))
    set n : ℕ := n₀ + 3 with hn
    have hn3 : 3 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
    have hcos := cos_arg_div_pos u hn3
    have hpow : ‖z₀‖ / ‖ζ‖ ≤ Real.cos (Complex.arg u / n) ^ n := by
      refine le_trans ?_ (one_sub_le_cos_arg_div_pow u hn3)
      have h1 : Real.pi ^ 2 / (2 * (1 - ‖z₀‖ / ‖ζ‖)) ≤ n := by
        rw [hn]; push_cast; linarith
      rw [div_le_iff₀ (by linarith)] at h1
      rw [sub_nonneg.mpr hratio.le |> fun _ => le_sub_comm, div_le_iff₀ (by positivity)]
      nlinarith
    set ρ : ℝ := ‖z₀‖ / ‖ζ‖ * ((Real.cos (Complex.arg u / n))⁻¹) ^ n with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; positivity
    have hρ1 : ρ ≤ 1 := by
      rw [hρ, inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hcos n)]
      exact hpow
    -- the spiral ends at `ρ ζ`
    have hend : z₀ * (((Real.cos (Complex.arg u / n))⁻¹ : ℝ) : ℂ) ^ n * u = (ρ : ℂ) * ζ := by
      rw [hu, hρ]
      field_simp
      push_cast
      ring
    obtain ⟨c, hc0, hcn, hcmem, hcstep⟩ := spiral_reach u hu1 n hn3
    rw [hend] at hcn
    -- the two extra steps along the ray of `ζ`
    set z' : ℂ := (ρ : ℂ) * ζ * (1 + (Real.sqrt (1 / ρ - 1) : ℂ) * Complex.I) with hz'
    have hz'0 : z' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ0.ne') hζ0) ?_
      intro h
      have := congrArg Complex.re h
      simp at this
    obtain ⟨hstep1, hstep2⟩ := descent_step_ray ζ hρ0 hρ1
    have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
    refine ⟨n + 2, fun k => if k ≤ n then c k else if k = n + 1 then lift p (tangent e₁ e₂ z')
      else t, by omega, ?_, ?_, ?_, ?_⟩
    · simp [hc0]
    · simp
    · intro i hi
      split_ifs with h1 h2
      · exact hcmem i h1
      · exact lift_tangent_mem he z' hz'0
      · exact ⟨ht, htp⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with h1 | h1
      · rw [if_pos (by omega : i + 1 ≤ n), if_pos h1.le]
        exact hcstep i h1
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [← h2, if_neg (by omega : ¬ (n + 1 ≤ n)), if_pos rfl, if_pos le_rfl, hcn,
            lift_tangent_mem_descent_iff he (mul_ne_zero hρC hζ0)]
          exact hstep1
        · have h3 : i = n + 1 := by omega
          rw [h3, if_neg (by omega : ¬ (n + 1 + 1 ≤ n)), if_neg (by omega : n + 1 + 1 ≠ n + 1),
            if_neg (by omega : ¬ (n + 1 ≤ n)), if_pos rfl, htl, ← hζ,
            lift_tangent_mem_descent_iff he hz'0]
          exact hstep2

end Gleason

end
