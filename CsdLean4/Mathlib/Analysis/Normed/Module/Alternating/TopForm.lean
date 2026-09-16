/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Top-degree continuous alternating forms

**Category:** 1-Mathlib (CSD-free; upstream target
`Mathlib.Analysis.Normed.Module.Alternating`).

Milestone **M1** of the top-power plan. A continuous alternating form on `E` whose
degree is a basis index type of `E` is a scalar multiple of that basis's determinant, and
pulling it back along an endomorphism scales the scalar by the endomorphism's determinant. Both
are upstream facts about `AlternatingMap` (`AlternatingMap.eq_smul_basis_det`,
`Module.Basis.det_comp`); this module states them for `ContinuousAlternatingMap`, which is the
type differential forms are made of, in the form the measure of a top form consumes:

* `apply_eq_mul_basis_det` — `α v = α e * e.det v`;
* `ext_basis` — two top-degree forms agreeing on a basis are equal;
* ★ `compContinuousLinearMap_apply_basis` — `(α.compContinuousLinearMap L) e = L.det * α e`,
  the **Jacobian rule** for the coefficient of a top form: this is the exact factor the change of
  variables formula carries (`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`), so
  the density of a top form transforms as a density should.

## Honest scope

⚠️ Real scalars only, and the degree is an arbitrary finite type `ι` with a basis indexed by it;
no `finrank` bookkeeping is done here. Nothing about manifolds.

**Provenance and references.** The top-power plan (M1); `Mathlib/LinearAlgebra/Determinant.lean`
(`AlternatingMap.eq_smul_basis_det`, `Module.Basis.det_comp`, `Module.Basis.det_self`);
the completed-work ledger.
-/

@[expose] public section

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- A top-degree continuous alternating form is its value on a basis times that basis's
determinant. -/
theorem apply_eq_mul_basis_det (e : Module.Basis ι ℝ E) (α : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) :
    α v = α e * e.det v := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[ℝ] ℝ => f v)
    (AlternatingMap.eq_smul_basis_det e α.toAlternatingMap)
  simpa [smul_eq_mul] using h

/-- Two top-degree forms that agree on a basis are equal. -/
theorem ext_basis (e : Module.Basis ι ℝ E) {α β : E [⋀^ι]→L[ℝ] ℝ} (h : α e = β e) : α = β := by
  ext v
  rw [apply_eq_mul_basis_det e α, apply_eq_mul_basis_det e β, h]

/-- ★ **The Jacobian rule.** Pulling a top-degree form back along an endomorphism multiplies its
coefficient on a basis by the determinant of the endomorphism. -/
theorem compContinuousLinearMap_apply_basis (e : Module.Basis ι ℝ E) (α : E [⋀^ι]→L[ℝ] ℝ)
    (L : E →L[ℝ] E) :
    (α.compContinuousLinearMap L) e = L.det * α e := by
  have h := Module.Basis.det_comp e (L : E →ₗ[ℝ] E) e
  rw [Module.Basis.det_self, mul_one] at h
  rw [compContinuousLinearMap_apply, apply_eq_mul_basis_det e α, ContinuousLinearMap.det]
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h]
  ring

end ContinuousAlternatingMap
