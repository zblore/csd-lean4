/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.BerryPhase
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.GeometricPhaseCurvature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The curvature formula on the spin-½ cone: the disc integral is half the solid angle

**Category:** 3-Local (QM-validity). BACKLOG #54, brick BP-3 of `specs/berry-phase-scoping.md`,
checked on Berry's example.

The cone curve `ψ(t) = (cos θ/2, e^{it} sin θ/2)` of `BerryPhase.lean` bounds the disc
`Ψ(s, t) = (cos(sθ/2), e^{it} sin(sθ/2))`, `s ∈ [0, 1]`, `t ∈ [0, 2π]`: at `s = 0` the disc is the
north pole, at `s = 1` it is the cone curve, and the cut `t = 0 ≡ 2π` closes with no phase. The
curvature `2 Im⟪∂_sΨ, ∂_tΨ⟫` is `(θ/2) sin(sθ)`, and its integral over the disc is
`π(1 − cos θ)`, **half the solid angle** of the cone.

* `coneSurface θ`, `coneSurface_one` — the disc, whose outer edge is `coneCurve θ`;
  `contDiff_coneSurface`, `norm_coneSurface`, the two partial derivatives;
* ★ `curvature_coneSurface` — the curvature is `(θ/2) sin(sθ)`;
* ★ `integral_curvature_coneSurface` — **its integral over the disc is `solidAngle θ / 2`**;
* ★★ `geometricPhase_coneCurve_eq_neg_integral_curvature` — the general curvature formula
  (`GeometricPhase.geometricPhase_eq_neg_integral_curvature`) applied to the cone;
* ★★ `curvature_formula_consistent` — the same equation proved the other way, from Berry's direct
  computation `β = −Ω/2` (`geometricPhase_coneCurve_solidAngle`) and the disc integral: **the two
  derivations agree.**

## Honest scope

⚠️ One surface, computed directly. Berry's adiabatic setting is `specs/berry-phase-scoping.md`
BP-5 (BACKLOG #56); the discrete Aharonov–Bohm ring is BP-4 (#55).

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45, §§3, 5; `specs/berry-phase-scoping.md`;
`specs/qm-empirical-tests.md` ER3; `specs/BACKLOG.md` #54.
-/

@[expose] public section

open GeometricPhase intervalIntegral
open scoped Real ComplexConjugate

namespace CSD
namespace Empirical
namespace QM
namespace BerryPhase

/-- The disc of the cone: `Ψ(s, t) = (cos(sθ/2), e^{it} sin(sθ/2))`. -/
noncomputable def coneSurface (θ : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos (p.1 * (θ / 2)) : ℂ),
    Complex.exp ((p.2 : ℂ) * Complex.I) * Real.sin (p.1 * (θ / 2))]

/-- The outer edge `s = 1` of the disc is the cone curve. -/
theorem coneSurface_one (θ t : ℝ) : coneSurface θ (1, t) = coneCurve θ t := by
  simp [coneSurface, coneCurve]

theorem norm_coneSurface (θ : ℝ) (p : ℝ × ℝ) : ‖coneSurface θ p‖ = 1 := by
  rw [coneSurface, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.norm_real, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, sq_abs]
  exact Real.cos_sq_add_sin_sq _

/-- A pair of derivatives of the components gives the derivative of the `EuclideanSpace` curve. -/
theorem hasDerivAt_toLp_two {f g : ℝ → ℂ} {f' g' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => (WithLp.toLp 2 ![f x, g x] : EuclideanSpace ℂ (Fin 2)))
      (WithLp.toLp 2 ![f', g']) x := by
  have h : HasDerivAt (fun x => ![f x, g x]) ![f', g'] x := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · exact hf
    · exact hg
  set e : PiLp 2 (fun _ : Fin 2 => ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 => ℂ with he
  have h2 : HasDerivAt (⇑e.symm ∘ fun x => ![f x, g x]) (e.symm ![f', g']) x :=
    e.symm.hasFDerivAt.comp_hasDerivAt x h
  exact h2

/-- `∂_sΨ = (−(θ/2) sin(sθ/2), (θ/2) e^{it} cos(sθ/2))`. -/
theorem hasDerivAt_coneSurface_left (θ s t : ℝ) :
    HasDerivAt (fun s => coneSurface θ (s, t))
      (WithLp.toLp 2 ![-((Real.sin (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ)),
        Complex.exp ((t : ℂ) * Complex.I) * ((Real.cos (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ))]) s := by
  have h0 : HasDerivAt (fun s : ℝ => (Real.cos (s * (θ / 2)) : ℂ))
      (-((Real.sin (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ))) s := by
    have := ((Real.hasDerivAt_cos (s * (θ / 2))).comp s
      ((hasDerivAt_id' (x := s)).mul_const (θ / 2))).ofReal_comp
    refine this.congr_deriv ?_
    push_cast
    ring
  have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (Real.sin (s * (θ / 2)) : ℂ))
      (Complex.exp ((t : ℂ) * Complex.I) * ((Real.cos (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ))) s := by
    have := (((Real.hasDerivAt_sin (s * (θ / 2))).comp s
      ((hasDerivAt_id' (x := s)).mul_const (θ / 2))).ofReal_comp).const_mul
      (Complex.exp ((t : ℂ) * Complex.I))
    refine this.congr_deriv ?_
    push_cast
    ring
  exact hasDerivAt_toLp_two h0 h1

/-- `∂_tΨ = (0, i e^{it} sin(sθ/2))`. -/
theorem hasDerivAt_coneSurface_right (θ s t : ℝ) :
    HasDerivAt (fun t => coneSurface θ (s, t))
      (WithLp.toLp 2 ![(0 : ℂ),
        Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (s * (θ / 2))]) t := by
  have h0 : HasDerivAt (fun _ : ℝ => (Real.cos (s * (θ / 2)) : ℂ)) (0 : ℂ) t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * (Real.sin (s * (θ / 2)) : ℂ))
      (Complex.I * Complex.exp ((t : ℂ) * Complex.I) * Real.sin (s * (θ / 2))) t := by
    have := ((((hasDerivAt_id' (x := t)).ofReal_comp).mul_const Complex.I).cexp).mul_const
      (Real.sin (s * (θ / 2)) : ℂ)
    refine this.congr_deriv ?_
    rw [Complex.ofReal_one]
    ring
  exact hasDerivAt_toLp_two h0 h1

theorem contDiff_coneSurface (θ : ℝ) : ContDiff ℝ 2 (coneSurface θ) := by
  have h : ContDiff ℝ 2 (fun p : ℝ × ℝ => ![(Real.cos (p.1 * (θ / 2)) : ℂ),
      Complex.exp ((p.2 : ℂ) * Complex.I) * Real.sin (p.1 * (θ / 2))]) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp
        (Real.contDiff_cos.comp (contDiff_fst.mul contDiff_const))
    · exact (Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)).mul
        (Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp (contDiff_fst.mul contDiff_const)))
  exact (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 => ℂ).symm.contDiff.comp h

/-- ★ **The curvature on the cone's disc is `(θ/2) sin(sθ)`.** -/
theorem curvature_coneSurface (θ s t : ℝ) :
    curvature (coneSurface θ) (s, t) = θ / 2 * Real.sin (s * θ) := by
  have hd : DifferentiableAt ℝ (coneSurface θ) (s, t) :=
    (contDiff_coneSurface θ).differentiable (by norm_num) _
  rw [curvature, fderiv_apply_one_zero hd, fderiv_apply_zero_one hd,
    (hasDerivAt_coneSurface_left θ s t).deriv, (hasDerivAt_coneSurface_right θ s t).deriv,
    PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    RCLike.inner_apply', map_mul, map_neg, Complex.conj_ofReal, mul_zero, zero_add]
  have hc := conj_cexp_mul_self t
  have h : conj (Complex.exp ((t : ℂ) * Complex.I))
      * ((Real.cos (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ))
      * (Complex.I * Complex.exp ((t : ℂ) * Complex.I) * (Real.sin (s * (θ / 2)) : ℂ))
      = Complex.I * ((Real.cos (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ)
          * (Real.sin (s * (θ / 2)) : ℂ)) := by
    linear_combination (Complex.I * ((Real.cos (s * (θ / 2)) : ℂ) * ((θ / 2 : ℝ) : ℂ)
      * (Real.sin (s * (θ / 2)) : ℂ))) * hc
  rw [h, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add]
  rw [show s * θ = 2 * (s * (θ / 2)) by ring, Real.sin_two_mul]
  ring

/-- ★ **The curvature integral over the cone's disc is half the solid angle**, `π(1 − cos θ)`. -/
theorem integral_curvature_coneSurface (θ : ℝ) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(2 * π), curvature (coneSurface θ) (s, t)
      = solidAngle θ / 2 := by
  have h : ∀ s, ∫ t in (0 : ℝ)..(2 * π), curvature (coneSurface θ) (s, t)
      = 2 * π * (θ / 2 * Real.sin (s * θ)) := by
    intro s
    simp only [curvature_coneSurface]
    rw [integral_const, sub_zero, smul_eq_mul]
  simp only [h]
  rw [integral_const_mul, integral_const_mul]
  by_cases hθ : θ = 0
  · subst hθ
    simp [solidAngle]
  · rw [integral_comp_mul_right Real.sin hθ]
    simp only [zero_mul, one_mul, integral_sin, Real.cos_zero, smul_eq_mul, solidAngle]
    field_simp

/-- ★★ **The curvature formula on the cone**: the general theorem
`geometricPhase_eq_neg_integral_curvature` applied to the disc `coneSurface θ`. -/
theorem geometricPhase_coneCurve_eq_neg_integral_curvature (θ : ℝ) :
    geometricPhase (coneCurve θ) (2 * π) 0
      = -∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(2 * π), curvature (coneSurface θ) (s, t) := by
  have hleft : ∀ t, coneSurface θ (0, t) = coneSurface θ (0, 0) := by
    intro t
    simp [coneSurface]
  have htop : ∀ s, coneSurface θ (s, 2 * π)
      = Complex.exp ((((fun _ : ℝ => (0 : ℝ)) s : ℝ) : ℂ) * Complex.I) • coneSurface θ (s, 0) := by
    intro s
    simp only [coneSurface, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    push_cast
    rw [Complex.exp_two_pi_mul_I]
  have h := geometricPhase_eq_neg_integral_curvature (contDiff_coneSurface θ) (norm_coneSurface θ)
    (φ := fun _ => 0) contDiff_const rfl hleft htop
  have hc : (fun t => coneSurface θ (1, t)) = coneCurve θ := funext (coneSurface_one θ)
  rw [hc] at h
  exact h

/-- ★★ **The two derivations agree**: Berry's direct computation `β = −Ω/2`
(`geometricPhase_coneCurve_solidAngle`) and the disc integral of the curvature
(`integral_curvature_coneSurface`) give the same equation as the general curvature formula. -/
theorem curvature_formula_consistent (θ : ℝ) :
    -∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(2 * π), curvature (coneSurface θ) (s, t)
      = geometricPhase (coneCurve θ) (2 * π) 0 := by
  rw [integral_curvature_coneSurface, geometricPhase_coneCurve_solidAngle]

end BerryPhase
end QM
end Empirical
end CSD

end
