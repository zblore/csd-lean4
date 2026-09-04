/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.HamiltonianVectorField
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Kähler potentials: `dd^c` forms are closed, and the Fubini–Study chart form

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; differential forms on normed spaces).

`KahlerClosed.lean` proved `dω = 0` for the **constant** fundamental form — the flat statement,
where closedness is immediate because the form does not vary. This module takes the next step of
the A4/KG-1 narrowing (`specs/mathlib-gaps-plan.md` MG-4): the **non-constant** form built from a
Kähler *potential*, and in particular the genuine Fubini–Study form of an affine chart, whose
potential is `log (1 + ‖z‖²)`.

The route is exactness rather than computation. Mathlib's pin carries `d² = 0`
(`extDeriv_extDeriv`), so a form presented as `d` of something is closed for free. The `dd^c`
construction does exactly that:

* `dForm K` — the 1-form `dK`, packaged through `ofSubsingletonLIE`; `dForm_eq_extDeriv` checks
  it really is the exterior derivative of the 0-form `K` (`extDeriv_constOfIsEmpty`), so the
  packaging is not ad hoc.
* `dcForm K` — the twisted differential `d^c K`, i.e. `(d^cK)_x v = (dK)_x (Jv)`, using the
  complex structure `J u = i • u` bundled as a real-linear map (`complexStructureL`).
* `ddcForm K := extDeriv (dcForm K)` — the `dd^c` 2-form of the potential.
* ★ `extDeriv_ddcForm` — **`dd^c K` is closed for every smooth potential `K`**.
* `fsPotential z = log (1 + ‖z‖²)`, `contDiff_fsPotential` — the Fubini–Study chart potential is
  smooth (`1 + ‖z‖² ≥ 1 > 0`, so the logarithm never meets its singularity).
* ★★ `extDeriv_fsChartForm` — **the Fubini–Study chart form is closed.**

## ⚠️ Honest scope — read before citing

* **The chart form is DEFINED by its potential**, `fsChartForm := ddcForm fsPotential`. That is
  the standard potential-theoretic definition of the Fubini–Study form on an affine chart (up to
  the usual normalisation constant, which closedness does not see). ★ **The identification is
  now proved** (2026-09-01, `fsChartForm_apply`): the second-derivative computation on
  `log (1 + ‖z‖²)` is carried out, giving the components in terms of `Kahler.metric` and
  `Kahler.fundamentalForm`, and at the chart origin `fsChartForm 0 = (-4 : ℝ) • fundamentalFormAlt`
  (`fsChartForm_zero`) — the literal identification with the constant fundamental form.
* **Still the chart, not the quotient.** Everything lives on the flat model `E`; forms on the
  manifold `ℂℙ^{N-1}` remain outside Mathlib's API (its own `DifferentialForm/Basic.lean` TODO).
  The Q8/KG-1 gap is now narrowed to the quotient/manifold glue alone, the identification above
  having landed; the top-power volume identity is untouched (`KahlerVolumeForced.lean` forces the
  volume independently), and it is the one that would need a wedge API.
* No wedge-product API exists upstream, which is why the coordinate route (`ω = i∂∂̄K` expanded
  in a basis) is not taken; there are no `∂`/`∂̄` operators in Mathlib either.

## References

`KahlerClosed.lean` (the constant/flat case this extends), `KahlerForm.lean`
(`complexStructure`, `fundamentalForm`), `MATHLIB-GAPS.md` (the Kähler-manifold row this
narrows), `specs/mathlib-gaps-plan.md` (MG-4).
-/

@[expose] public section

open ContinuousAlternatingMap

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The complex structure as a real-linear continuous map -/

/-- **The complex structure `J`, bundled**: multiplication by `i`, as a continuous
`ℝ`-linear map. The bundled companion of `Kahler.complexStructure`. -/
noncomputable def complexStructureL : E →L[ℝ] E :=
  (Complex.I • (ContinuousLinearMap.id ℂ E)).restrictScalars ℝ

@[simp] lemma complexStructureL_apply (u : E) :
    complexStructureL u = Complex.I • u := rfl

lemma complexStructureL_eq_complexStructure (u : E) :
    complexStructureL u = complexStructure u := rfl

/-! ### `d`, `d^c` and `dd^c` of a potential -/

/-- The packaging of a functional as a continuous alternating `1`-form, bundled as a
continuous linear map (the vehicle for transporting smoothness). -/
noncomputable def packL : (E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  (ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma packL_apply (f : E →L[ℝ] ℝ) (v : Fin 1 → E) :
    packL f v = f (v 0) := rfl

/-- The **1-form `dK`** of a real potential, packaged as a continuous alternating 1-form. -/
noncomputable def dForm (K : E → ℝ) : E → (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  fun x => packL (fderiv ℝ K x)

/-- The packaging is honest: `dForm K` **is** the exterior derivative of the `0`-form `K`. -/
lemma dForm_eq_extDeriv (K : E → ℝ) (x : E) :
    dForm K x
      = extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (K y)) x := by
  rw [extDeriv_constOfIsEmpty]
  ext v
  simp [dForm]

/-- **The twisted differential `d^c K`**: `(d^cK)_x v = (dK)_x (J v)`, the `1`-form obtained by
precomposing `dK` with the complex structure. -/
noncomputable def dcForm (K : E → ℝ) : E → (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  fun x => packL ((fderiv ℝ K x).comp complexStructureL)

@[simp] lemma dcForm_apply (K : E → ℝ) (x : E) (v : Fin 1 → E) :
    dcForm K x v = fderiv ℝ K x (Complex.I • v 0) := rfl

/-- **The `dd^c` two-form of a potential.** -/
noncomputable def ddcForm (K : E → ℝ) : E → (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  extDeriv (dcForm K)

/-! ### Smoothness, and ★ closedness -/

/-- Precomposition with the complex structure, as a continuous linear map on `1`-forms'
underlying functionals — the vehicle for transporting smoothness through `d^c`. -/
noncomputable def compJL : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E E ℝ).flip complexStructureL

@[simp] lemma compJL_apply (f : E →L[ℝ] ℝ) : compJL f = f.comp complexStructureL := rfl

/-- `d^c K` is smooth when `K` is: the derivative of a smooth map is smooth, and both the
precomposition with `J` and the alternating-form packaging are continuous linear. -/
lemma contDiff_dcForm {K : E → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) :
    ContDiff ℝ (⊤ : ℕ∞) (dcForm K) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => compJL (fderiv ℝ K x)) :=
    (ContinuousLinearMap.contDiff compJL).comp hfd
  exact (ContinuousLinearMap.contDiff (packL (E := E))).comp hcomp

/-- ★ **The `dd^c` form of any smooth potential is closed.** Immediate from `d² = 0` once the
form is presented as an exterior derivative — which is what the `dd^c` construction does. -/
theorem extDeriv_ddcForm {K : E → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) :
    extDeriv (ddcForm K) = 0 :=
  extDeriv_extDeriv (contDiff_dcForm hK) (by
    have h2 : (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := rfl
    simp only [minSmoothness_of_isRCLikeNormedField, h2]
    exact WithTop.coe_le_coe.mpr le_top)

/-! ### The Fubini–Study chart potential -/

/-- **The Fubini–Study Kähler potential** of an affine chart: `K z = log (1 + ‖z‖²)`. -/
noncomputable def fsPotential (z : E) : ℝ := Real.log (1 + ‖z‖ ^ 2)

/-- The Fubini–Study potential is smooth: `1 + ‖z‖² ≥ 1`, so the logarithm stays away from its
singularity, and `‖·‖²` is smooth on an inner-product space. -/
lemma contDiff_fsPotential : ContDiff ℝ (⊤ : ℕ∞) (fsPotential (E := E)) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z : E => 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℂ)
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  exact hsq.contDiffAt.log (by positivity)

/-- **The Fubini–Study form of an affine chart**, defined by its potential. -/
noncomputable def fsChartForm : E → (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  ddcForm fsPotential

/-- ★★ **The Fubini–Study chart form is closed**: `dω = 0` for the genuine (non-constant)
Fubini–Study form of an affine chart, not merely for the constant form on the tangent model.

The form is the one *defined by* the Fubini–Study potential; `fsChartForm_apply` below computes
its components and `fsChartForm_zero` identifies it at the chart origin with
`Kahler.fundamentalFormAlt`, so this is closedness of an identified object, not of an opaque one.
⚠️ The manifold statement on `ℂℙ^{N-1}` remains Mathlib-blocked. -/
theorem extDeriv_fsChartForm : extDeriv (fsChartForm (E := E)) = 0 :=
  extDeriv_ddcForm contDiff_fsPotential

/-! ### ★ The identification: what `fsChartForm` actually IS, in components

`extDeriv_fsChartForm` says a form *defined by a potential* is closed. That is only worth
having once the form is identified, and until now nothing computed its pointwise value —
so the closedness was true of an object never evaluated. These lemmas close that gap: the
`dd^c` of the Fubini–Study potential is computed in components, and at the chart origin it
is the constant fundamental form of `KahlerForm.lean` up to the normalisation `-4`. -/

/-- `v ↦ g x v = re ⟪x, v⟫`, bundled. -/
noncomputable def metricCLM (x : E) : E →L[ℝ] ℝ :=
  Complex.reCLM.comp ((innerSL ℂ x).restrictScalars ℝ)

@[simp] lemma metricCLM_apply (x v : E) : metricCLM x v = metric x v := rfl

theorem hasFDerivAt_one_add_normSq (x : E) :
    HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2) ((2:ℝ) • metricCLM x) x := by
  have h := hasFDerivAt_quadraticEnergy (E := E) (ContinuousLinearMap.id ℂ E)
    (fun u v => by simp) x
  have h2 := h.const_mul (2:ℝ)
  have heq : (fun y : E => 2 * quadraticEnergy (ContinuousLinearMap.id ℂ E) y)
      = fun y : E => ‖y‖ ^ 2 := by
    funext y
    simp only [quadraticEnergy, metric, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [heq] at h2
  simpa [metricCLM] using h2.const_add 1

theorem hasFDerivAt_fsPotential (x : E) :
    HasFDerivAt (fsPotential (E := E)) ((2 * (1 + ‖x‖ ^ 2)⁻¹) • metricCLM x) x := by
  have hne : (1 : ℝ) + ‖x‖ ^ 2 ≠ 0 := by positivity
  have h := (hasFDerivAt_one_add_normSq x).log hne
  have hfp : (fsPotential (E := E)) = fun y : E => Real.log (1 + ‖y‖ ^ 2) := rfl
  rw [hfp]
  convert h using 1
  rw [smul_smul]
  ring_nf

/-- ★ B2: the twisted differential of the FS potential in closed form. -/
theorem dcForm_fsPotential_apply (x : E) (v : Fin 1 → E) :
    dcForm (fsPotential (E := E)) x v
      = -(2 * (1 + ‖x‖ ^ 2)⁻¹) * fundamentalForm x (v 0) := by
  rw [dcForm_apply, (hasFDerivAt_fsPotential x).fderiv]
  simp only [_root_.smul_apply, metricCLM_apply, smul_eq_mul]
  rw [metric, fundamentalForm, inner_smul_right]
  simp

/-- B3: the derivative of `y ↦ (d^c K)_y u`, evaluated. -/
theorem fderiv_dcForm_fsPotential_apply (x : E) (u : Fin 1 → E) (w : E) :
    fderiv ℝ (fun y : E => dcForm (fsPotential (E := E)) y u) x w
      = -(2 * (1 + ‖x‖ ^ 2)⁻¹) * fundamentalForm w (u 0)
        + 4 * (1 + ‖x‖ ^ 2)⁻¹ ^ 2 * fundamentalForm x (u 0) * metric x w := by
  have hne : (1 : ℝ) + ‖x‖ ^ 2 ≠ 0 := by positivity
  have hrw : (fun y : E => dcForm (fsPotential (E := E)) y u)
      = fun y : E => (-2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹ * fundamentalForm y (u 0) := by
    funext y
    rw [dcForm_fsPotential_apply y u]; ring
  rw [hrw]
  have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt x (hasFDerivAt_one_add_normSq x)
  have hc := hinv.const_mul (-2 : ℝ)
  have hF : HasFDerivAt (fun y : E => fundamentalForm y (u 0))
      (fundamentalFormCLM.flip (u 0)) x := (fundamentalFormCLM.flip (u 0)).hasFDerivAt
  have hprod : HasFDerivAt
      (fun y : E => (-2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹ * fundamentalForm y (u 0)) _ x := hc.mul hF
  rw [hprod.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.flip_apply,
    fundamentalFormCLM_apply, metricCLM_apply, smul_eq_mul, Function.comp_apply]
  field_simp
  ring

/-- ★★ B4: the Fubini–Study chart form, in components. -/
theorem fsChartForm_apply (x : E) (v : Fin 2 → E) :
    fsChartForm x v
      = -4 * ((1 + ‖x‖ ^ 2)⁻¹ * fundamentalForm (v 0) (v 1)
          - (1 + ‖x‖ ^ 2)⁻¹ ^ 2
            * (metric x (v 0) * fundamentalForm x (v 1)
              - metric x (v 1) * fundamentalForm x (v 0))) := by
  have hdiff : DifferentiableAt ℝ (dcForm (fsPotential (E := E))) x :=
    ((contDiff_dcForm (contDiff_fsPotential (E := E))).differentiable (by simp)) x
  rw [fsChartForm, ddcForm, extDeriv_apply hdiff]
  rw [Fin.sum_univ_two]
  have h0 : (0 : Fin 2).removeNth v = ![v 1] := by
    ext i; fin_cases i; simp [Fin.removeNth]
  have h1 : (1 : Fin 2).removeNth v = ![v 0] := by
    ext i; fin_cases i; simp [Fin.removeNth]
  rw [h0, h1]
  rw [fderiv_dcForm_fsPotential_apply, fderiv_dcForm_fsPotential_apply]
  simp only [Matrix.cons_val_zero, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul]
  rw [fundamentalForm_antisymm (v 1) (v 0)]
  ring

/-- ★★ B5: at the chart origin the FS chart form IS the constant fundamental form,
up to the normalisation `-4`. -/
theorem fsChartForm_zero : fsChartForm (0 : E) = (-4 : ℝ) • fundamentalFormAlt := by
  ext v
  rw [fsChartForm_apply]
  simp [metric, fundamentalForm, fundamentalFormAlt_apply]


end Kahler
