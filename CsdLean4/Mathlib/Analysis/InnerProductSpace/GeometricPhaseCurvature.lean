/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.GeometricPhase
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The curvature formula for the geometric phase

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #54, brick BP-3 of
`specs/berry-phase-scoping.md`.

Let `Ψ : ℝ × ℝ → E` be a `C²` family of unit vectors on the rectangle `[0, 1] × [0, T]`, thought
of as a disc in polar form: the edge `s = 0` is collapsed to a point (`Ψ (0, t) = Ψ (0, 0)`), the
edge `s = 1` is the loop `ψ t = Ψ (1, t)`, and the edges `t = 0`, `t = T` are the same curve of rays,
`Ψ (s, T) = e^{iφ(s)} Ψ (s, 0)` (the phase mismatch at the cut). Then the geometric phase of the
loop is **minus the integral of the curvature** over the disc:

`β = −∫₀¹ ∫₀ᵀ 2 Im⟪∂_sΨ, ∂_tΨ⟫ ds dt`.

The connection form `A = Im⟪Ψ, dΨ⟫` has the two components `A_s = Im⟪Ψ, ∂_sΨ⟫`,
`A_t = Im⟪Ψ, ∂_tΨ⟫`, and its curvature `dA(∂_s, ∂_t) = ∂_s A_t − ∂_t A_s` is `2 Im⟪∂_sΨ, ∂_tΨ⟫` by the
symmetry of second derivatives — the pullback of the Kähler form `Im⟪·, ·⟫` of the Fubini–Study
metric `Re⟪·, ·⟫` (twice it, in that normalisation; on `ℂℙ¹` it integrates to half the solid angle).
Green's theorem on the rectangle (Mathlib's divergence theorem on `ℝ × ℝ`) turns the integral of
`dA` into the circulation of `A` along the boundary: the loop contributes the dynamical phase, the
collapsed edge nothing, and the cut contributes `−(φ 1 − φ 0) = −φ`, the total phase.

* `connectionFormS`, `connectionFormT` — the components of the connection form of a family;
  `curvature Ψ p = 2 Im⟪∂_sΨ, ∂_tΨ⟫`;
* `fderiv_apply_one_zero`, `fderiv_apply_zero_one` — the partial derivatives are the derivatives
  of the restricted curves, so the edge values of `A_s`, `A_t` are the `connectionForm` of the
  edge curves (`connectionFormS_eq`, `connectionFormT_eq`);
* `hasFDerivAt_connectionFormS/T` — the components are `C¹` with explicit derivative
  (`connectionFormS'`, `connectionFormT'`, through `fderivInnerCLM`);
* ★ `curvature_eq` — **the curvature is `∂_s A_t − ∂_t A_s`** (symmetric second derivatives);
* ★★ `geometricPhase_eq_neg_integral_curvature` — **the curvature formula**
  `β = −∫∫ curvature`.

## Honest scope

⚠️ The disc is the rectangle in polar form: any `C²` map of the closed disc gives such a family
(`Ψ (s, t) = F (s cos t, s sin t)`), so nothing is lost for `C²` discs, but the statement is not
Stokes on a manifold. The identification of `curvature` with the pullback of the corpus's
bundle-level Fubini–Study form (`fsForm` of `ProjectiveSpaceFubiniStudyForm.lean`) along the
projection of `Ψ` to `ℙ(E)` is BACKLOG #65.

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45, §3; B. Simon, PRL 51 (1983) 2167;
Y. Aharonov, J. Anandan, PRL 58 (1987) 1593; `specs/berry-phase-scoping.md` BP-3;
`specs/BACKLOG.md` #54; `specs/future-work.md`.
-/

@[expose] public section

open scoped ComplexConjugate
open intervalIntegral MeasureTheory

namespace GeometricPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The connection form of a two-parameter family and its curvature -/

/-- The `s`-component of the connection form of a family: `A_s = Im⟪Ψ, ∂_sΨ⟫`. -/
noncomputable def connectionFormS (Ψ : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ :=
  (inner ℂ (Ψ p) (fderiv ℝ Ψ p (1, 0))).im

/-- The `t`-component of the connection form of a family: `A_t = Im⟪Ψ, ∂_tΨ⟫`. -/
noncomputable def connectionFormT (Ψ : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ :=
  (inner ℂ (Ψ p) (fderiv ℝ Ψ p (0, 1))).im

/-- The curvature `dA(∂_s, ∂_t) = 2 Im⟪∂_sΨ, ∂_tΨ⟫` of the connection along a family. -/
noncomputable def curvature (Ψ : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ :=
  2 * (inner ℂ (fderiv ℝ Ψ p (1, 0)) (fderiv ℝ Ψ p (0, 1))).im

variable {Ψ : ℝ × ℝ → E}

/-- The partial derivative in `s` is the derivative of the restricted curve. -/
theorem fderiv_apply_one_zero {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    fderiv ℝ Ψ (s, t) (1, 0) = deriv (fun s => Ψ (s, t)) s := by
  have h : HasDerivAt (fun s => Ψ (s, t)) (fderiv ℝ Ψ (s, t) (1, 0)) s :=
    HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun s => (s, t)) (x := s) hΨ.hasFDerivAt
      ((hasDerivAt_id' (x := s)).prodMk (hasDerivAt_const s t))
  exact h.deriv.symm

/-- The partial derivative in `t` is the derivative of the restricted curve. -/
theorem fderiv_apply_zero_one {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    fderiv ℝ Ψ (s, t) (0, 1) = deriv (fun t => Ψ (s, t)) t := by
  have h : HasDerivAt (fun t => Ψ (s, t)) (fderiv ℝ Ψ (s, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun t => (s, t)) (x := t) hΨ.hasFDerivAt
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id' (x := t)))
  exact h.deriv.symm

theorem connectionFormS_eq {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    connectionFormS Ψ (s, t) = connectionForm (fun s => Ψ (s, t)) s := by
  rw [connectionFormS, connectionForm, fderiv_apply_one_zero hΨ]

theorem connectionFormT_eq {s t : ℝ} (hΨ : DifferentiableAt ℝ Ψ (s, t)) :
    connectionFormT Ψ (s, t) = connectionForm (fun t => Ψ (s, t)) t := by
  rw [connectionFormT, connectionForm, fderiv_apply_zero_one hΨ]

/-! ### The components are `C¹` -/

/-- The derivative of `p ↦ ∂_vΨ(p)` for a `C²` family: `w ↦ D²Ψ(p)(w, v)`. -/
theorem hasFDerivAt_fderiv_apply (hΨ : ContDiff ℝ 2 Ψ) (p v : ℝ × ℝ) :
    HasFDerivAt (fun p => fderiv ℝ Ψ p v)
      ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (fderiv ℝ Ψ) p)) p := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp p
    (h1.differentiable one_ne_zero p).hasFDerivAt

/-- The derivative of `A_s`. -/
noncomputable def connectionFormS' (Ψ : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((fderivInnerCLM ℂ (Ψ p, fderiv ℝ Ψ p (1, 0))).comp
    ((fderiv ℝ Ψ p).prod ((ContinuousLinearMap.apply ℝ E (1, 0)).comp (fderiv ℝ (fderiv ℝ Ψ) p))))

/-- The derivative of `A_t`. -/
noncomputable def connectionFormT' (Ψ : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((fderivInnerCLM ℂ (Ψ p, fderiv ℝ Ψ p (0, 1))).comp
    ((fderiv ℝ Ψ p).prod ((ContinuousLinearMap.apply ℝ E (0, 1)).comp (fderiv ℝ (fderiv ℝ Ψ) p))))

theorem hasFDerivAt_connectionFormS (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    HasFDerivAt (connectionFormS Ψ) (connectionFormS' Ψ p) p := by
  have hΨ' : HasFDerivAt Ψ (fderiv ℝ Ψ p) p := (hΨ.differentiable (by norm_num) p).hasFDerivAt
  exact Complex.imCLM.hasFDerivAt.comp p (hΨ'.inner ℂ (hasFDerivAt_fderiv_apply hΨ p (1, 0)))

theorem hasFDerivAt_connectionFormT (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    HasFDerivAt (connectionFormT Ψ) (connectionFormT' Ψ p) p := by
  have hΨ' : HasFDerivAt Ψ (fderiv ℝ Ψ p) p := (hΨ.differentiable (by norm_num) p).hasFDerivAt
  exact Complex.imCLM.hasFDerivAt.comp p (hΨ'.inner ℂ (hasFDerivAt_fderiv_apply hΨ p (0, 1)))

theorem connectionFormS'_apply (p w : ℝ × ℝ) :
    connectionFormS' Ψ p w
      = (inner ℂ (Ψ p) (fderiv ℝ (fderiv ℝ Ψ) p w (1, 0))
          + inner ℂ (fderiv ℝ Ψ p w) (fderiv ℝ Ψ p (1, 0))).im := by
  simp [connectionFormS']

theorem connectionFormT'_apply (p w : ℝ × ℝ) :
    connectionFormT' Ψ p w
      = (inner ℂ (Ψ p) (fderiv ℝ (fderiv ℝ Ψ) p w (0, 1))
          + inner ℂ (fderiv ℝ Ψ p w) (fderiv ℝ Ψ p (0, 1))).im := by
  simp [connectionFormT']

/-- ★ **The curvature is `∂_s A_t − ∂_t A_s`**: the second-derivative terms cancel by symmetry. -/
theorem curvature_eq (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    connectionFormT' Ψ p (1, 0) + (-connectionFormS' Ψ p) (0, 1) = curvature Ψ p := by
  have hsymm : IsSymmSndFDerivAt ℝ Ψ p :=
    hΨ.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  rw [neg_apply, connectionFormT'_apply, connectionFormS'_apply, curvature,
    hsymm (0, 1) (1, 0), ← inner_conj_symm (fderiv ℝ Ψ p (1, 0)) (fderiv ℝ Ψ p (0, 1))]
  simp only [Complex.add_im, Complex.conj_im]
  ring

/-! ### The curvature formula -/

/-- The edge curve `s ↦ Ψ (s, t)` of a `C²` family is `C¹`. -/
theorem contDiff_edgeS (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) : ContDiff ℝ 1 fun s => Ψ (s, t) :=
  (hΨ.of_le (by norm_num)).comp (contDiff_prodMk_left t)

theorem continuous_curvature (hΨ : ContDiff ℝ 2 Ψ) : Continuous (curvature Ψ) := by
  have hD : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv (by norm_num)
  have h1 : Continuous fun p => fderiv ℝ Ψ p (1, 0) :=
    (ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : ℝ))).continuous.comp hD
  have h2 : Continuous fun p => fderiv ℝ Ψ p (0, 1) :=
    (ContinuousLinearMap.apply ℝ E ((0 : ℝ), (1 : ℝ))).continuous.comp hD
  exact continuous_const.mul (Complex.continuous_im.comp (h1.inner h2))

/-- ★★ **The curvature formula for the geometric phase.** For a `C²` family of unit vectors
`Ψ` on `[0, 1] × [0, T]` — the disc in polar form: the edge `s = 0` collapsed to a point, the edges
`t = 0` and `t = T` the same curve of rays up to the phase `e^{iφ(s)}`, `φ 0 = 0` — the geometric
phase of the loop `t ↦ Ψ (1, t)` (total phase `φ 1`) is minus the integral of the curvature
`2 Im⟪∂_sΨ, ∂_tΨ⟫` over the disc. -/
theorem geometricPhase_eq_neg_integral_curvature (hΨ : ContDiff ℝ 2 Ψ) (hunit : ∀ p, ‖Ψ p‖ = 1)
    {T : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφ0 : φ 0 = 0)
    (hleft : ∀ t, Ψ (0, t) = Ψ (0, 0))
    (htop : ∀ s, Ψ (s, T) = Complex.exp ((φ s : ℂ) * Complex.I) • Ψ (s, 0)) :
    geometricPhase (fun t => Ψ (1, t)) T (φ 1)
      = -∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..T, curvature Ψ (s, t) := by
  have hdiff : ∀ p, DifferentiableAt ℝ Ψ p := fun p => hΨ.differentiable (by norm_num) p
  -- Green's theorem on the rectangle, with `f = A_t` and `g = −A_s`
  have hcT : Continuous (connectionFormT Ψ) :=
    continuous_iff_continuousAt.2 fun p => (hasFDerivAt_connectionFormT hΨ p).continuousAt
  have hcS : Continuous (connectionFormS Ψ) :=
    continuous_iff_continuousAt.2 fun p => (hasFDerivAt_connectionFormS hΨ p).continuousAt
  have hint : IntegrableOn
      (fun p => connectionFormT' Ψ p (1, 0) + (fun p => -connectionFormS' Ψ p) p (0, 1))
      (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (0 : ℝ) T) := by
    have h : (fun p => connectionFormT' Ψ p (1, 0) + (fun p => -connectionFormS' Ψ p) p (0, 1))
        = curvature Ψ := funext fun p => curvature_eq hΨ p
    rw [h]
    exact (continuous_curvature hΨ).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)
  have hG := integral2_divergence_prod_of_hasFDerivAt_off_countable (connectionFormT Ψ)
    (fun p => -connectionFormS Ψ p) (connectionFormT' Ψ) (fun p => -connectionFormS' Ψ p)
    0 0 1 T ∅ Set.countable_empty hcT.continuousOn hcS.neg.continuousOn
    (fun p _ => hasFDerivAt_connectionFormT hΨ p)
    (fun p _ => (hasFDerivAt_connectionFormS hΨ p).neg) hint
  simp only [curvature_eq hΨ] at hG
  -- the four edges
  have hleft' : ∫ t in (0 : ℝ)..T, connectionFormT Ψ (0, t) = 0 := by
    have h : ∀ t, connectionFormT Ψ (0, t) = 0 := by
      intro t
      rw [connectionFormT_eq (hdiff _)]
      have hc : (fun t => Ψ (0, t)) = fun _ => Ψ (0, 0) := funext hleft
      rw [connectionForm, hc, deriv_const]
      simp
    simp [h]
  have hright : ∫ t in (0 : ℝ)..T, connectionFormT Ψ (1, t) = dynamicalPhase (fun t => Ψ (1, t)) T :=
    integral_congr fun t _ => connectionFormT_eq (hdiff _)
  have hbot : ∫ s in (0 : ℝ)..1, connectionFormS Ψ (s, 0) = dynamicalPhase (fun s => Ψ (s, 0)) 1 :=
    integral_congr fun s _ => connectionFormS_eq (hdiff _)
  have htop' : ∫ s in (0 : ℝ)..1, connectionFormS Ψ (s, T)
      = dynamicalPhase (fun s => Ψ (s, 0)) 1 + φ 1 := by
    have hre : rephase φ (fun s => Ψ (s, 0)) = fun s => Ψ (s, T) := by
      funext s
      rw [rephase, htop s]
    have h := dynamicalPhase_rephase hφ (contDiff_edgeS hΨ 0) (fun s => hunit (s, 0)) 1
    rw [hre, hφ0, sub_zero] at h
    rw [← h]
    exact integral_congr fun s _ => connectionFormS_eq (hdiff _)
  simp only [intervalIntegral.integral_neg, hleft', hright, hbot, htop'] at hG
  rw [hG, geometricPhase]
  ring

end GeometricPhase

end
