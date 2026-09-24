/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.GeometricPhase
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Berry's phase for a spin-½ around a cone: minus half the solid angle

**Category:** 3-Local (QM-validity). BACKLOG #10, brick BP-2 of `specs/berry-phase-scoping.md`.

The state `ψ(t) = (cos θ/2, e^{it} sin θ/2)` of a spin-½ precesses once around a cone of
half-angle `θ` on the Bloch sphere as `t` runs over `[0, 2π]`; its ray returns to itself with total
phase `0`. The general theory of `Mathlib/Analysis/InnerProductSpace/GeometricPhase.lean` gives:

* `connectionForm_coneCurve` — the connection form along the curve is the constant `sin²(θ/2)`;
* `coneCurve_cyclic` — the curve is cyclic with total phase `0`;
* ★★ `geometricPhase_coneCurve` — **the geometric phase is `−2π sin²(θ/2) = −π(1 − cos θ)`,
  minus half the solid angle `2π(1 − cos θ)` of the cone** (`geometricPhase_coneCurve_solidAngle`)
  — Berry's 1984 result for spin-½, the phase Tomita–Chiao measured with light in a coiled fibre.

## Honest scope

⚠️ One curve, computed directly (its disc and the curvature formula are `BerryPhaseCurvature.lean`);
the adiabatic setting (a spin in a slowly rotating field) is not modelled
(`specs/berry-phase-scoping.md` BP-5). The curve is the Schrödinger evolution generated
by `H = diag(0, −1)`, but that reading is not stated here.

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45, §5; A. Tomita, R. Chiao, PRL 57 (1986)
937; `specs/berry-phase-scoping.md`; `specs/qm-empirical-tests.md` ER3.
-/

@[expose] public section

open GeometricPhase
open scoped Real ComplexConjugate

namespace CSD
namespace Empirical
namespace QM
namespace BerryPhase

/-- The spin-½ state precessing around a cone of half-angle `θ`: `(cos θ/2, e^{it} sin θ/2)`. -/
noncomputable def coneCurve (θ : ℝ) (t : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos (θ / 2) : ℂ), Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)]

/-- The solid angle of the cone of half-angle `θ`: `2π(1 − cos θ)`. -/
noncomputable def solidAngle (θ : ℝ) : ℝ := 2 * π * (1 - Real.cos θ)

/-- The derivative of the cone curve: `(0, i e^{it} sin θ/2)`. -/
theorem hasDerivAt_coneCurve (θ t : ℝ) :
    HasDerivAt (coneCurve θ)
      (WithLp.toLp 2 ![(0 : ℂ), Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)])
      t := by
  have h0 : HasDerivAt (fun _ : ℝ => (Real.cos (θ / 2) : ℂ)) (0 : ℂ) t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ))
      (Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)) t := by
    have := ((((hasDerivAt_id' (x := t)).ofReal_comp).mul_const Complex.I).cexp).mul_const
      (Real.sin (θ / 2) : ℂ)
    refine this.congr_deriv ?_
    rw [Complex.ofReal_one]
    ring
  have h : HasDerivAt (fun s : ℝ => ![(Real.cos (θ / 2) : ℂ),
      Complex.exp ((s : ℂ) * Complex.I) * Real.sin (θ / 2)])
      ![(0 : ℂ), Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)] t := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
  set e : PiLp 2 (fun _ : Fin 2 => ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 => ℂ with he
  have h2 : HasDerivAt (⇑e.symm ∘ fun s : ℝ => ![(Real.cos (θ / 2) : ℂ),
      Complex.exp ((s : ℂ) * Complex.I) * Real.sin (θ / 2)])
      (e.symm ![(0 : ℂ), Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)]) t :=
    e.symm.hasFDerivAt.comp_hasDerivAt t h
  exact h2

theorem norm_coneCurve (θ t : ℝ) : ‖coneCurve θ t‖ = 1 := by
  rw [coneCurve, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.norm_real, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, sq_abs]
  exact Real.cos_sq_add_sin_sq _

theorem contDiff_coneCurve (θ : ℝ) : ContDiff ℝ 1 (coneCurve θ) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_coneCurve θ t).differentiableAt, ?_⟩
  have h : deriv (coneCurve θ) = fun t : ℝ => WithLp.toLp 2
      ![(0 : ℂ), Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (θ / 2)] :=
    funext fun t => (hasDerivAt_coneCurve θ t).deriv
  rw [h]
  fun_prop

/-- The connection form along the cone curve is the constant `sin²(θ/2)`. -/
theorem connectionForm_coneCurve (θ t : ℝ) :
    connectionForm (coneCurve θ) t = Real.sin (θ / 2) ^ 2 := by
  rw [connectionForm, (hasDerivAt_coneCurve θ t).deriv, coneCurve, PiLp.inner_apply,
    Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  have h : conj (Complex.exp ((t : ℂ) * Complex.I)) * (Real.sin (θ / 2) : ℂ)
      * (Complex.I * Complex.exp ((t : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ))
      = Complex.I * ((Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)) := by
    have hc := conj_cexp_mul_self t
    linear_combination (Complex.I * ((Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ))) * hc
  rw [mul_zero, zero_add, h, ← Complex.ofReal_mul]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The cone curve is cyclic over `[0, 2π]` with total phase `0`. -/
theorem coneCurve_cyclic (θ : ℝ) :
    coneCurve θ (2 * π) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • coneCurve θ 0 := by
  rw [coneCurve, coneCurve]
  simp [Complex.exp_two_pi_mul_I]

/-- ★★ **Berry's phase for the spin-½ cone**: `−2π sin²(θ/2) = −π(1 − cos θ)`. -/
theorem geometricPhase_coneCurve (θ : ℝ) :
    geometricPhase (coneCurve θ) (2 * π) 0 = -π * (1 - Real.cos θ) := by
  rw [geometricPhase, dynamicalPhase]
  have h : (fun t => connectionForm (coneCurve θ) t) = fun _ => Real.sin (θ / 2) ^ 2 :=
    funext fun t => connectionForm_coneCurve θ t
  rw [h, intervalIntegral.integral_const, Real.sin_sq_eq_half_sub, mul_div_cancel₀ _ two_ne_zero]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- ★★ **The geometric phase is minus half the solid angle of the cone.** -/
theorem geometricPhase_coneCurve_solidAngle (θ : ℝ) :
    geometricPhase (coneCurve θ) (2 * π) 0 = -(solidAngle θ / 2) := by
  rw [geometricPhase_coneCurve, solidAngle]
  ring

end BerryPhase
end QM
end Empirical
end CSD

end
