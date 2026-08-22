/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Kähler potentials: `dd^c` forms are closed, and the Fubini–Study chart form

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
  the usual normalisation constant, which closedness does not see). What is **not** proved here
  is the *identification* of this form with the pullback of the metric's fundamental form
  `Kahler.fundamentalForm` — that is a second-derivative computation on `log (1 + ‖z‖²)` and is
  the named residue of this brick.
* **Still the chart, not the quotient.** Everything lives on the flat model `E`; forms on the
  manifold `ℂℙ^{N-1}` remain outside Mathlib's API (its own `DifferentialForm/Basic.lean` TODO).
  The Q8/KG-1 gap is narrowed to the quotient/manifold glue plus the identification above, and
  the top-power volume identity is untouched (`KahlerVolumeForced.lean` forces the volume
  independently).
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

⚠️ The form is the one *defined by* the Fubini–Study potential (see the module's honest-scope
note): its identification with the pullback of `Kahler.fundamentalForm` is not proved here, and
the manifold statement on `ℂℙ^{N-1}` remains Mathlib-blocked. -/
theorem extDeriv_fsChartForm : extDeriv (fsChartForm (E := E)) = 0 :=
  extDeriv_ddcForm contDiff_fsPotential

end Kahler
