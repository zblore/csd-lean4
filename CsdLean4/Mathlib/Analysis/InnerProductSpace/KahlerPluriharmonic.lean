/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerPotential
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# `dd^c` calculus: pluriharmonicity, naturality, linearity

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
the source repository's terms register records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free; flat differential forms on a complex inner product
space, in the `d^c` vocabulary of `KahlerPotential.lean`).

The three facts about `dd^c K = d(d^c K)` that a chart-invariance argument for the
Fubini–Study form needs, none of which existed:

* ★ `dcForm_re_eq_neg_dForm_im` — **Cauchy–Riemann** in this vocabulary: for holomorphic `f`,
  `d^c(Re f) = -d(Im f)`; hence ★ `ddcForm_re_eq_zero` — the real part of a holomorphic
  function is **pluriharmonic**, `dd^c (Re f) = 0` — by `d² = 0` (`extDeriv_extDeriv_apply`);
* ★ `ddcForm_log_norm_eq_zero` — `log ‖L ·‖` is pluriharmonic away from the kernel of a
  complex-linear functional `L`. Proved from the previous item with a *local* holomorphic
  logarithm: `Complex.log` off the slit plane, `Complex.log ∘ (-·)` on it
  (`Complex.mem_slitPlane_or_neg_mem_slitPlane`), so no branch is ever chosen globally;
* ★ `ddcForm_comp` — **naturality**: for holomorphic `τ`, `dd^c (K ∘ τ)` is the pullback of
  `dd^c K` along `fderiv ℝ τ`. Its `d^c` half (`dcForm_comp`) is the chain rule plus the fact
  that the real derivative of a holomorphic map commutes with `J`
  (`DifferentiableAt.fderiv_restrictScalars`); its `d` half is upstream's `extDeriv_pullback`;
* `ddcForm_sub'`, `ddcForm_const_smul'`, `contDiffAt_dcForm` — linearity in the potential, in
  the **local** (`ContDiffAt`) form that a potential singular off an open set needs.

## Honest scope

Everything here is on a **flat** complex inner product space, in the `E → E [⋀^Fin k]→L[ℝ] ℝ`
representation. The manifold-level `d` does not exist (step (2b)); these are the flat lemmas a
chart-by-chart argument composes. No CSD content.

**Provenance and references.** `KahlerPotential.lean` (`dcForm`, `ddcForm`, `fsChartForm`);
`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (`extDeriv_pullback`,
`extDeriv_extDeriv_apply`); `Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean`
(`contDiffAt_log`).
-/

@[expose] public section

open ContinuousAlternatingMap Filter Topology

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem dcForm_re_eq_neg_dForm_im {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) :
    dcForm (fun w => (f w).re) x = - dForm (fun w => (f w).im) x := by
  ext v
  have hR : HasFDerivAt f ((fderiv ℂ f x).restrictScalars ℝ) x := by
    rw [← hf.fderiv_restrictScalars ℝ]
    exact (hf.restrictScalars ℝ).hasFDerivAt
  have hre : fderiv ℝ (fun w => (f w).re) x
      = Complex.reCLM.comp ((fderiv ℂ f x).restrictScalars ℝ) :=
    (Complex.reCLM.hasFDerivAt.comp x hR).fderiv
  have him : fderiv ℝ (fun w => (f w).im) x
      = Complex.imCLM.comp ((fderiv ℂ f x).restrictScalars ℝ) :=
    (Complex.imCLM.hasFDerivAt.comp x hR).fderiv
  simp only [dcForm_apply, dForm, packL_apply, ContinuousAlternatingMap.neg_apply, hre, him,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', map_smul,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.I_mul_re]

/-- B2b: the real part of a holomorphic function is pluriharmonic: `dd^c (Re f) = 0`. -/
theorem ddcForm_re_eq_zero {f : E → ℂ} {x : E} (hf : ContDiffAt ℂ ⊤ f x) :
    ddcForm (fun w => (f w).re) x = 0 := by
  have hev : dcForm (fun w => (f w).re) =ᶠ[𝓝 x] ((-1 : ℝ) • dForm (fun w => (f w).im)) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    rw [dcForm_re_eq_neg_dForm_im (hy.differentiableAt (by simp))]
    exact (neg_one_smul ℝ _).symm
  rw [ddcForm, Filter.EventuallyEq.extDeriv_eq hev, extDeriv_fun_smul]
  have hd : dForm (fun w => (f w).im)
      = extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y).im) :=
    funext fun y => dForm_eq_extDeriv _ y
  rw [hd, extDeriv_extDeriv_apply (r := ⊤) ?_ (by simp), smul_zero]
  have him : ContDiffAt ℝ ⊤ (fun y => (f y).im) x :=
    Complex.imCLM.contDiff.contDiffAt.comp x (hf.restrict_scalars ℝ)
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv
    |>.contDiff.contDiffAt.comp x him

/-- B2c: `log ‖L ·‖` is pluriharmonic away from the kernel, for `L` complex-linear. -/
theorem ddcForm_log_norm_eq_zero (L : E →L[ℂ] ℂ) {x : E} (hx : L x ≠ 0) :
    ddcForm (fun w => Real.log ‖L w‖) x = 0 := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hx with h | h
  · have hf : ContDiffAt ℂ ⊤ (fun w => Complex.log (L w)) x :=
      (Complex.contDiffAt_log h).comp x L.contDiff.contDiffAt
    have : (fun w => Real.log ‖L w‖) = fun w => (Complex.log (L w)).re := by
      funext w; rw [Complex.log_re]
    rw [this]; exact ddcForm_re_eq_zero hf
  · have hf : ContDiffAt ℂ ⊤ (fun w => Complex.log (-L w)) x :=
      (Complex.contDiffAt_log h).comp x (L.contDiff.neg).contDiffAt
    have : (fun w => Real.log ‖L w‖) = fun w => (Complex.log (-L w)).re := by
      funext w; rw [Complex.log_re, norm_neg]
    rw [this]; exact ddcForm_re_eq_zero hf

/-! ### Naturality and linearity -/

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

/-- B2e: `dd^c` is additive in the potential (globally smooth potentials). -/
theorem ddcForm_sub {K₁ K₂ : E → ℝ} (h₁ : ContDiff ℝ (⊤ : ℕ∞) K₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) K₂)
    (x : E) : ddcForm (K₁ - K₂) x = ddcForm K₁ x - ddcForm K₂ x := by
  have hd : dcForm (K₁ - K₂) = dcForm K₁ + (-1 : ℝ) • dcForm K₂ := by
    funext y; ext v
    have hsub : fderiv ℝ (K₁ - K₂) y = fderiv ℝ K₁ y - fderiv ℝ K₂ y :=
      fderiv_sub (h₁.differentiable (by simp) y) (h₂.differentiable (by simp) y)
    simp only [dcForm_apply, hsub, _root_.sub_apply, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  rw [ddcForm, ddcForm, ddcForm, hd, extDeriv_add, extDeriv_fun_smul, neg_one_smul, sub_eq_add_neg]
  · exact ((contDiff_dcForm h₁).differentiable (by simp)) x
  · exact (((contDiff_dcForm h₂).const_smul (-1 : ℝ)).differentiable (by simp)) x

/-- B2d, step 1: `d^c` is natural under holomorphic maps. -/
theorem dcForm_comp {K : E' → ℝ} {τ : E → E'} {y : E}
    (hK : DifferentiableAt ℝ K (τ y)) (hτ : DifferentiableAt ℂ τ y) :
    dcForm (K ∘ τ) y = (dcForm K (τ y)).compContinuousLinearMap (fderiv ℝ τ y) := by
  ext v
  have hτR : fderiv ℝ τ y = (fderiv ℂ τ y).restrictScalars ℝ := hτ.fderiv_restrictScalars ℝ
  have hchain : fderiv ℝ (K ∘ τ) y = (fderiv ℝ K (τ y)).comp (fderiv ℝ τ y) :=
    fderiv_comp y hK (hτ.restrictScalars ℝ)
  simp only [dcForm_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hchain, hτR]
  simp [ContinuousLinearMap.coe_restrictScalars', map_smul]

/-- B2d: `dd^c` is natural under holomorphic maps (the pullback of `dd^c K` is `dd^c (K ∘ τ)`). -/
theorem ddcForm_comp {K : E' → ℝ} {τ : E → E'} {x : E}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hτ : ContDiffAt ℂ ⊤ τ x) :
    ddcForm (K ∘ τ) x = (ddcForm K (τ x)).compContinuousLinearMap (fderiv ℝ τ x) := by
  have hev : dcForm (K ∘ τ) =ᶠ[𝓝 x]
      fun y => (dcForm K (τ y)).compContinuousLinearMap (fderiv ℝ τ y) := by
    filter_upwards [hτ.eventually (by simp)] with y hy
    exact dcForm_comp (hK.differentiable (by simp) (τ y)) (hy.differentiableAt (by simp))
  rw [ddcForm, Filter.EventuallyEq.extDeriv_eq hev, ddcForm]
  exact extDeriv_pullback (r := ⊤) (((contDiff_dcForm hK).differentiable (by simp)) (τ x))
    (hτ.restrict_scalars ℝ) (by simp)


/-- Local smoothness of `d^c K` from local smoothness of `K`. -/
theorem contDiffAt_dcForm {m : WithTop ℕ∞} {K : E → ℝ} {x : E}
    (hK : ContDiffAt ℝ (m + 1) K x) : ContDiffAt ℝ m (dcForm K) x := by
  have hf : ContDiffAt ℝ m (fderiv ℝ K) x := hK.fderiv_right le_rfl
  exact (packL.contDiff.comp (compJL.contDiff)).contDiffAt.comp x hf

/-- Local additivity of `dd^c` in the potential. -/
theorem ddcForm_sub' {K₁ K₂ : E → ℝ} {x : E}
    (h₁ : ContDiffAt ℝ 2 K₁ x) (h₂ : ContDiffAt ℝ 2 K₂ x) :
    ddcForm (K₁ - K₂) x = ddcForm K₁ x - ddcForm K₂ x := by
  have hev : dcForm (K₁ - K₂) =ᶠ[𝓝 x] (dcForm K₁ + (-1 : ℝ) • dcForm K₂) := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y hy₁ hy₂
    ext v
    have hsub : fderiv ℝ (K₁ - K₂) y = fderiv ℝ K₁ y - fderiv ℝ K₂ y :=
      fderiv_sub (hy₁.differentiableAt (by simp)) (hy₂.differentiableAt (by simp))
    simp only [dcForm_apply, hsub, _root_.sub_apply, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  rw [ddcForm, ddcForm, ddcForm, Filter.EventuallyEq.extDeriv_eq hev, extDeriv_add,
    extDeriv_fun_smul, neg_one_smul, sub_eq_add_neg]
  · exact (contDiffAt_dcForm (m := 1) h₁).differentiableAt one_ne_zero
  · exact ((contDiffAt_dcForm (m := 1) h₂).const_smul (-1 : ℝ)).differentiableAt one_ne_zero

/-- Local homogeneity of `dd^c` in the potential. -/
theorem ddcForm_const_smul' {K : E → ℝ} {x : E} (c : ℝ) (hK : ContDiffAt ℝ 2 K x) :
    ddcForm (c • K) x = c • ddcForm K x := by
  have hev : dcForm (c • K) =ᶠ[𝓝 x] (c • dcForm K) := by
    filter_upwards [hK.eventually (by simp)] with y hy
    ext v
    have hs : fderiv ℝ (c • K) y = c • fderiv ℝ K y :=
      fderiv_const_smul (hy.differentiableAt (by simp)) c
    simp [dcForm_apply, hs]
  rw [ddcForm, ddcForm, Filter.EventuallyEq.extDeriv_eq hev, extDeriv_fun_smul]


end Kahler
