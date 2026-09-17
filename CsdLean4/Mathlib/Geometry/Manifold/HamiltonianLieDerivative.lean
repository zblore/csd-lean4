/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianVectorField

/-!
# The flat Cartan formula, and the Lie derivative of a symplectic form along its Hamiltonian field

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). Q29(c′) of
`specs/generator-layer-scoping.md`.

`Analysis/ODE/FlowDerivative.lean` defines the flat Lie derivative `flatLieDeriv X Ω` of a 2-form
along a vector field and proves that a form with vanishing Lie derivative is preserved by the
flow. This file identifies that Lie derivative with the exterior calculus and applies it to the
one case the corpus needs.

* `flatInteriorProduct X Ω` — the 1-form `ι_X Ω = Ω(X, ·)`; `differentiableAt_flatInteriorProduct`;
* `fderiv_apply_vecCons_const` — the product rule for `z ↦ Ω z (X z, u)`;
* ★ `flatLieDeriv_eq_extDeriv_flatInteriorProduct_add` — **Cartan's formula** on a normed space,
  `L_X Ω = d(ι_X Ω) + ι_X (dΩ)`, a `Fin 2`/`Fin 3` computation from Mathlib's `extDeriv_apply`;
* `DifferentialForm.localRep_apply_localHamiltonianVector` — in a chart, the local Hamiltonian
  vector satisfies `ω_loc (X_loc, u) = d(H ∘ chart⁻¹) u`, so
  `DifferentialForm.flatInteriorProduct_localHamiltonianVector`: `ι_X ω_loc` is the chart
  differential of `H`; hence `d(ι_X ω_loc) = d(d(H ∘ chart⁻¹)) = 0`
  (`extDeriv_flatInteriorProduct_localHamiltonianVector`, by `extDeriv_extDeriv_apply`);
* `DifferentialForm.extDeriv_localRep_eq_zero` — the local representative of a closed form is
  closed on the chart's target (`localRep_mextDerivFamily`);
* ★★ `DifferentialForm.flatLieDeriv_localHamiltonianVector_localRep_eq_zero` — **the flat Lie
  derivative of a symplectic form's local representative along its Hamiltonian field vanishes**
  at every point of the chart's target. Together with
  `ContDiffAt.exists_localFlow_form_invariant` this says the chart flow of a Hamiltonian field
  preserves the form; the manifold assembly is Q29(d′).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Manifold

section FlatCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flat interior product `ι_X Ω` of a 2-form with a vector field: the 1-form
`v ↦ Ω z (X z, v)`. -/
noncomputable def flatInteriorProduct (X : E → E) (Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) :
    E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.curryLeft (Ω z) (X z)

theorem flatInteriorProduct_apply (X : E → E) (Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E)
    (m : Fin 1 → E) : flatInteriorProduct X Ω z m = Ω z (Matrix.vecCons (X z) m) :=
  ContinuousAlternatingMap.curryLeft_apply_apply _ _ _

theorem differentiableAt_flatInteriorProduct {X : E → E} {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {z : E}
    (hX : ContDiffAt ℝ 1 X z) (hΩ : ContDiffAt ℝ 1 Ω z) :
    DifferentiableAt ℝ (flatInteriorProduct X Ω) z := by
  have h1 : ContDiffAt ℝ 1 (fun z => ContinuousAlternatingMap.curryLeft (Ω z)) z :=
    (IsBoundedLinearMap.contDiff (𝕜 := ℝ) (n := 1)
      (f := fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ)
      ⟨⟨fun ξ ξ' => ContinuousAlternatingMap.curryLeft_add ξ ξ',
        fun c ξ => ContinuousAlternatingMap.curryLeft_smul c ξ⟩,
        1, one_pos, fun ξ => le_of_eq
          ((ContinuousAlternatingMap.norm_curryLeft ξ).trans (one_mul _).symm)⟩).contDiffAt.comp z hΩ
  exact (h1.differentiableAt one_ne_zero).clm_apply (hX.differentiableAt one_ne_zero)

/-- `Fin.removeNth` on two-element tuples. -/
theorem Fin.removeNth_zero_two {β : Type*} (m : Fin 2 → β) : (0 : Fin 2).removeNth m = ![m 1] := by
  funext j; fin_cases j; rfl

theorem Fin.removeNth_one_two {β : Type*} (m : Fin 2 → β) : (1 : Fin 2).removeNth m = ![m 0] := by
  funext j; fin_cases j; rfl

/-- `Fin.removeNth` on three-element tuples. -/
theorem Fin.removeNth_zero_three {β : Type*} (a : β) (m : Fin 2 → β) :
    (0 : Fin 3).removeNth (Matrix.vecCons a m) = m := by
  funext j; fin_cases j <;> rfl

theorem Fin.removeNth_one_three {β : Type*} (a : β) (m : Fin 2 → β) :
    (1 : Fin 3).removeNth (Matrix.vecCons a m) = ![a, m 1] := by
  funext j; fin_cases j <;> rfl

theorem Fin.removeNth_two_three {β : Type*} (a : β) (m : Fin 2 → β) :
    (2 : Fin 3).removeNth (Matrix.vecCons a m) = ![a, m 0] := by
  funext j; fin_cases j <;> rfl

/-- The derivative of `z ↦ Ω z ![X z, u]` in the direction `v`. -/
theorem fderiv_apply_vecCons_const {X : E → E} {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {z : E}
    (hX : DifferentiableAt ℝ X z) (hΩ : DifferentiableAt ℝ Ω z) (u v : E) :
    fderiv ℝ (fun z => Ω z ![X z, u]) z v
      = fderiv ℝ Ω z v ![X z, u] + Ω z ![fderiv ℝ X z v, u] := by
  have h := fderiv_continuousAlternatingMap_apply_apply (g := ![X, fun _ => u]) hΩ
    (fun i => by fin_cases i <;> simp [hX]) v
  have hg : (fun z => Ω z ![X z, u]) = fun z => Ω z (fun i => ![X, fun _ => u] i z) := by
    funext z; congr 1; funext i; fin_cases i <;> rfl
  rw [hg, h, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_fun_const,
    Pi.zero_apply, zero_apply, ContinuousAlternatingMap.map_update_zero,
    add_zero]
  congr 2 <;> funext i <;> fin_cases i <;> rfl

/-- Antisymmetry of a 2-form on the model. -/
theorem ContinuousAlternatingMap.apply_swap_two (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (a b : E) :
    ξ ![b, a] = -ξ ![a, b] := by
  have h := ξ.toAlternatingMap.map_swap ![a, b] (i := 0) (j := 1) (by decide)
  have e : (![a, b] ∘ Equiv.swap (0 : Fin 2) 1) = ![b, a] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  exact h

/-- ★ **The flat Cartan formula** for a 2-form: `L_X Ω = d(ι_X Ω) + ι_X (dΩ)`. -/
theorem flatLieDeriv_eq_extDeriv_flatInteriorProduct_add {X : E → E}
    {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {z : E} (hX' : ContDiffAt ℝ 1 X z)
    (hΩ' : ContDiffAt ℝ 1 Ω z) (m : Fin 2 → E) :
    flatLieDeriv X Ω z m
      = extDeriv (flatInteriorProduct X Ω) z m + extDeriv Ω z (Matrix.vecCons (X z) m) := by
  have hX : DifferentiableAt ℝ X z := hX'.differentiableAt one_ne_zero
  have hΩ : DifferentiableAt ℝ Ω z := hΩ'.differentiableAt one_ne_zero
  have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
  rw [extDeriv_apply (differentiableAt_flatInteriorProduct hX' hΩ'), extDeriv_apply hΩ,
    Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [Fin.removeNth_zero_two, Fin.removeNth_one_two, Fin.removeNth_zero_three,
    Fin.removeNth_one_three, Fin.removeNth_two_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul,
    neg_one_smul, flatInteriorProduct_apply]
  rw [fderiv_apply_vecCons_const hX hΩ (m 1) (m 0), fderiv_apply_vecCons_const hX hΩ (m 0) (m 1)]
  have hc : ∀ c : Fin 2 → E, fderiv ℝ (fun z => Ω z c) z = fun v => fderiv ℝ Ω z v c := by
    intro c
    funext v
    exact (fderiv_continuousAlternatingMap_apply_const_apply hΩ c v)
  simp only [flatLieDeriv, Fin.sum_univ_two]
  rw [show Function.update m 0 (fderiv ℝ X z (m 0)) = ![fderiv ℝ X z (m 0), m 1] from by
        rw [hm]; funext i; fin_cases i <;> rfl,
      show Function.update m 1 (fderiv ℝ X z (m 1)) = ![m 0, fderiv ℝ X z (m 1)] from by
        rw [hm]; funext i; fin_cases i <;> rfl]
  rw [ContinuousAlternatingMap.apply_swap_two (Ω z) (fderiv ℝ X z (m 1)) (m 0)]
  have h0 := congrFun (hc m) (X z)
  have h1 := congrFun (hc ![X z, m 1]) (m 0)
  have h2 := congrFun (hc ![X z, m 0]) (m 1)
  simp only [neg_one_sq, one_smul, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
    Function.comp_apply]
  rw [h0, h1, h2]
  ring

end FlatCartan

section Hamiltonian

open Bundle
open scoped Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℝ E) ∞ M]

namespace DifferentialForm

variable (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) (H : M → ℝ)

/-- The defining identity of the local Hamiltonian vector, in the chart:
`ω_loc (X_loc w, u) = d(H ∘ chart⁻¹)_w u`. -/
theorem localRep_apply_localHamiltonianVector
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) (u : E) :
    localRep (fun x => α x) x₀ w ![localHamiltonianVector α H x₀ w, u]
      = fderiv ℝ (H ∘ (chartAt E x₀).symm) w u := by
  have hω := localRep_nondegenerate α hnd x₀ hw
  rw [localHamiltonianVector, inverse_curryLeft_apply _ hω, apply_flatVec]

/-- The interior product of the local representative with the local Hamiltonian vector is the
chart differential of `H`, as a 1-form. -/
theorem flatInteriorProduct_localHamiltonianVector
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    flatInteriorProduct (localHamiltonianVector α H x₀) (localRep (fun x => α x) x₀) w
      = ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
          (fderiv ℝ (H ∘ (chartAt E x₀).symm) w) := by
  ext m
  rw [flatInteriorProduct_apply, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  have hm : Matrix.vecCons (localHamiltonianVector α H x₀ w) m
      = ![localHamiltonianVector α H x₀ w, m 0] := by
    funext i; fin_cases i <;> rfl
  rw [hm, localRep_apply_localHamiltonianVector α H hnd x₀ hw]

/-- `d(ι_X ω_loc) = d(d(H ∘ chart⁻¹)) = 0` in the chart. -/
theorem extDeriv_flatInteriorProduct_localHamiltonianVector
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) :
    extDeriv (flatInteriorProduct (localHamiltonianVector α H x₀) (localRep (fun x => α x) x₀)) w
      = 0 := by
  have hev : flatInteriorProduct (localHamiltonianVector α H x₀) (localRep (fun x => α x) x₀)
      =ᶠ[𝓝 w] fun z => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
        (fderiv ℝ (H ∘ (chartAt E x₀).symm) z) := by
    filter_upwards [(chartAt E x₀).open_target.mem_nhds hw] with z hz
    exact flatInteriorProduct_localHamiltonianVector α H hnd x₀ hz
  rw [hev.extDeriv_eq]
  have hd : (fun z => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
        (fderiv ℝ (H ∘ (chartAt E x₀).symm) z))
      = extDeriv (fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0)
          ((H ∘ (chartAt E x₀).symm) z)) := by
    funext z
    rw [extDeriv_constOfIsEmpty]
  rw [hd]
  have hHloc : ContDiffAt ℝ ∞ (H ∘ (chartAt E x₀).symm) w := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact (hH _).comp _ ((contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
      ((chartAt E x₀).open_target.mem_nhds hw))
  have hc : ContDiffAt ℝ ∞ (fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0)
      ((H ∘ (chartAt E x₀).symm) z)) w :=
    ((ContinuousAlternatingMap.constOfIsEmptyLIE (𝕜 := ℝ) (E := E) ℝ (Fin 0)).contDiff.contDiffAt
      (x := (H ∘ (chartAt E x₀).symm) w)).comp w hHloc
  exact extDeriv_extDeriv_apply hc minSmoothness_two_le_infty

omit [FiniteDimensional ℝ E] in
/-- The local representative of a closed form is closed in the chart: `d ω_loc = 0` on the
chart's target. -/
theorem extDeriv_localRep_eq_zero (hα : IsSymplectic α) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) :
    extDeriv (localRep (fun x => α x) x₀) w = 0 := by
  rw [← localRep_mextDerivFamily (fun x => α x) α.contMDiff_toFun x₀ hw]
  have h0 : mextDerivFamily (fun x => α x) = fun _ => 0 := by
    funext x
    have h := congrArg (fun β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 3) ℝ => β x)
      hα.closed
    simpa using h
  rw [h0]
  have hy : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have h := trivializationAt_snd (fun x : M => (0 : TangentSpace (modelWithCornersSelf ℝ E) x
    [⋀^Fin 3]→L[ℝ] Bundle.Trivial M ℝ x)) x₀ _ hy
  show (trivializationAt (E [⋀^Fin 3]→L[ℝ] ℝ)
    (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 3]→L[ℝ] Bundle.Trivial M ℝ x)
    x₀ ⟨(chartAt E x₀).symm w, 0⟩).2 = 0
  rw [h]
  ext m
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

/-- ★★ **The flat Lie derivative of the local representative of a symplectic form along the local
Hamiltonian vector vanishes**, at every point of the chart's target: Cartan's formula with
`d(ι_X ω_loc) = d(dH) = 0` (`extDeriv_flatInteriorProduct_localHamiltonianVector`) and the closedness of
the local representative (`extDeriv_localRep_eq_zero`). -/
theorem flatLieDeriv_localHamiltonianVector_localRep_eq_zero (hα : IsSymplectic α)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) (m : Fin 2 → E) :
    flatLieDeriv (localHamiltonianVector α H x₀) (localRep (fun x => α x) x₀) w m = 0 := by
  rw [flatLieDeriv_eq_extDeriv_flatInteriorProduct_add
    ((contDiffAt_localHamiltonianVector α H hα.nondegenerate hH x₀ hw).of_le (by simp))
    ((contDiffAt_localRep (fun x => α x) α.contMDiff_toFun x₀ hw).of_le (by simp)),
    extDeriv_flatInteriorProduct_localHamiltonianVector α H hα.nondegenerate hH x₀ hw,
    extDeriv_localRep_eq_zero α hα x₀ hw]
  simp

end DifferentialForm

end Hamiltonian

