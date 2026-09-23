/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Darboux
public import CsdLean4.Mathlib.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Darboux's theorem in the standard form `∑ dpᵢ ∧ dqᵢ`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #50, Darboux residue (b).

`Geometry/Manifold/Darboux.lean` produces, by Moser's trick, a `C¹` chart in which a closed
non-degenerate 2-form is the **constant** form `ω(x₀)`. This file composes that chart with the
linear change of coordinates given by a **symplectic basis** of `ω(x₀)`
(`LinearAlgebra/BilinearForm/SymplecticBasis.lean`) and obtains the textbook statement: a `C^n`
chart into `ℝ^{2n}` in which the form is the **standard symplectic form**
`ω_std = ∑ᵢ dpᵢ ∧ dqᵢ`, i.e. `ω = Ψ^* ω_std`; in particular the dimension is `2n`.

* `ContinuousAlternatingMap.toBilinForm` — the bilinear form `(u, v) ↦ ξ ![u, v]` of a 2-form;
  it is alternating (`toBilinForm_isAlt`) and non-degenerate when `ξ` is
  (`toBilinForm_nondegenerate`);
* `standardSymplecticForm ι` — the standard symplectic form on `ι ⊕ ι → ℝ`,
  `ω_std(u, v) = ∑ᵢ (u_{pᵢ} v_{qᵢ} − u_{qᵢ} v_{pᵢ})` (`inl` = the `p`'s, `inr` = the `q`'s), as a
  continuous alternating 2-form (`standardSymplecticForm_apply`);
* ★ `exists_continuousLinearEquiv_eq_standardSymplecticForm_comp` — **linear Darboux**: a
  non-degenerate 2-form on a finite-dimensional real space is the pullback of `ω_std` on
  `ℝ^{2n}` by a linear isomorphism, and `finrank E = 2n` (the symplectic basis);
* ★★ `exists_openPartialHomeomorph_pullback_standard` — **Darboux on a ball, standard form**:
  for `ω` of class `C^k` (`1 ≤ k ≤ ∞`) and closed on `ball x₀ R` with `ω(x₀)` non-degenerate, there
  is `n` with `finrank E = 2n` and a `C^k` chart `Ψ : E → ℝ^{2n}` with `C^k` inverse,
  `x₀ ∈ Ψ.source ⊆ ball x₀ R`,
  differentiable at every point `y` of its source with invertible derivative `D`, and
  `ω(y)(u, v) = ω_std(D u, D v)`: `ω = Ψ^* ω_std`;
* ★★ `DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_standard` —
  **Darboux on a symplectic manifold, standard form**: at every point the local representative
  of the form is, in a further `C^∞` chart `Ψ` of the model space into `ℝ^{2n}`, the pullback of
  `ω_std`; the Darboux chart is `Ψ ∘ chartAt E x₀`;
* ★ `DifferentialForm.IsSymplectic.even_finrank` — **a symplectic manifold has even dimension**.

## Honest scope

**Order `k`.** The chart inherits the regularity of `Darboux.lean`: `C^k` for `ω` of class `C^k`
(`1 ≤ k ≤ ∞`), `C^∞` on a symplectic manifold. The linear change of coordinates is `C^∞`.

References: J. Moser, *On the volume elements on a manifold*, Trans. AMS 120 (1965);
D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Thm 3.2.2 and Lemma 2.1.2 (the
symplectic basis); `Geometry/Manifold/Darboux.lean`; `LinearAlgebra/BilinearForm/SymplecticBasis.lean`;
`specs/BACKLOG.md` #50; `specs/generator-layer-scoping.md` Q31.
-/

@[expose] public section

open Set Metric Module
open scoped Manifold

noncomputable section

/-! ### The bilinear form of a 2-form -/

section ToBilinForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Additivity of a continuous alternating map in the head of a `vecCons`. -/
theorem ContinuousAlternatingMap.apply_vecCons_add {n : ℕ} (ξ : E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (m : Fin n → E) (x y : E) :
    ξ (Matrix.vecCons (x + y) m) = ξ (Matrix.vecCons x m) + ξ (Matrix.vecCons y m) :=
  ξ.toAlternatingMap.map_vecCons_add m x y

/-- Homogeneity of a continuous alternating map in the head of a `vecCons`. -/
theorem ContinuousAlternatingMap.apply_vecCons_smul {n : ℕ} (ξ : E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (m : Fin n → E) (c : ℝ) (x : E) :
    ξ (Matrix.vecCons (c • x) m) = c • ξ (Matrix.vecCons x m) :=
  ξ.toAlternatingMap.map_vecCons_smul m c x

/-- The bilinear form `(u, v) ↦ ξ ![u, v]` of a continuous 2-form. -/
def ContinuousAlternatingMap.toBilinForm (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun u v => ξ ![u, v])
    (fun u u' v => ξ.apply_vecCons_add ![v] u u')
    (fun c u v => ξ.apply_vecCons_smul ![v] c u)
    (fun u v v' => by
      rw [ξ.apply_swap_two (v + v') u, ξ.apply_vecCons_add, ξ.apply_swap_two u v,
        ξ.apply_swap_two u v']
      ring)
    (fun c u v => by
      rw [ξ.apply_swap_two (c • v) u, ξ.apply_vecCons_smul, ξ.apply_swap_two u v]
      simp only [smul_eq_mul]
      ring)

@[simp] theorem ContinuousAlternatingMap.toBilinForm_apply (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) :
    ξ.toBilinForm u v = ξ ![u, v] :=
  rfl

/-- The bilinear form of a 2-form is alternating. -/
theorem ContinuousAlternatingMap.toBilinForm_isAlt (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ξ.toBilinForm.IsAlt := fun u =>
  ξ.map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl (by decide)

/-- The bilinear form of a non-degenerate 2-form is non-degenerate. -/
theorem ContinuousAlternatingMap.toBilinForm_nondegenerate (ξ : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) : ξ.toBilinForm.Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ξ.toBilinForm_isAlt.isRefl).mpr
    fun v hv => by
      by_contra h
      obtain ⟨u, hu⟩ := hnd v h
      exact hu (hv u)

end ToBilinForm

/-! ### The standard symplectic form on `ℝ^{2n}` -/

section Standard

variable (ι : Type*) [Fintype ι]

/-- The standard symplectic form on `ι ⊕ ι → ℝ` as a bilinear map,
`(u, v) ↦ ∑ᵢ (u_{pᵢ} v_{qᵢ} − u_{qᵢ} v_{pᵢ})` with `p = inl`, `q = inr`. -/
def standardSymplecticBilin : (ι ⊕ ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.proj (Sum.inl i) : (ι ⊕ ι → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (Sum.inr i) : (ι ⊕ ι → ℝ) →L[ℝ] ℝ)
    - (ContinuousLinearMap.proj (Sum.inr i) : (ι ⊕ ι → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (Sum.inl i) : (ι ⊕ ι → ℝ) →L[ℝ] ℝ))

theorem standardSymplecticBilin_apply (u v : ι ⊕ ι → ℝ) :
    standardSymplecticBilin ι u v
      = ∑ i, (u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i)) := by
  simp [standardSymplecticBilin]

theorem standardSymplecticBilin_self (u : ι ⊕ ι → ℝ) : standardSymplecticBilin ι u u = 0 := by
  simp [standardSymplecticBilin_apply, mul_comm]

/-- The standard symplectic form as a continuous multilinear map on `Fin 2 → (ι ⊕ ι → ℝ)`. -/
def standardSymplecticMulti : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => (ι ⊕ ι → ℝ)) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (((continuousMultilinearCurryFin1 ℝ (ι ⊕ ι → ℝ) ℝ).symm.toLinearIsometry.toContinuousLinearMap).comp
      (standardSymplecticBilin ι))

@[simp] theorem standardSymplecticMulti_apply (v : Fin 2 → ι ⊕ ι → ℝ) :
    standardSymplecticMulti ι v = standardSymplecticBilin ι (v 0) (v 1) := by
  simp [standardSymplecticMulti, Fin.tail]

/-- **The standard symplectic form** `ω_std = ∑ᵢ dpᵢ ∧ dqᵢ` on `ι ⊕ ι → ℝ`, as a continuous
alternating 2-form: `ω_std(u, v) = ∑ᵢ (u_{pᵢ} v_{qᵢ} − u_{qᵢ} v_{pᵢ})`. -/
def standardSymplecticForm : (ι ⊕ ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ where
  toContinuousMultilinearMap := standardSymplecticMulti ι
  map_eq_zero_of_eq' := by
    intro v i j hv hne
    fin_cases i <;> fin_cases j <;>
      simp_all [standardSymplecticMulti_apply, standardSymplecticBilin_self]

@[simp] theorem standardSymplecticForm_apply (v : Fin 2 → ι ⊕ ι → ℝ) :
    standardSymplecticForm ι v
      = ∑ i, (v 0 (Sum.inl i) * v 1 (Sum.inr i) - v 0 (Sum.inr i) * v 1 (Sum.inl i)) := by
  rw [← standardSymplecticBilin_apply]
  exact standardSymplecticMulti_apply ι v

end Standard

/-! ### Linear Darboux -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- ★ **Linear Darboux.** A non-degenerate 2-form on a finite-dimensional real space is the
pullback of the standard symplectic form on `ℝ^{2n}` by a linear isomorphism `L`, and
`finrank E = 2n`: the coordinates of a symplectic basis of `ξ`. -/
theorem exists_continuousLinearEquiv_eq_standardSymplecticForm_comp (ξ : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) :
    ∃ (n : ℕ) (L : E ≃L[ℝ] (Fin n ⊕ Fin n → ℝ)), finrank ℝ E = 2 * n ∧
      ξ = (standardSymplecticForm (Fin n)).compContinuousLinearMap
        (L : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)) := by
  obtain ⟨n, e, he⟩ :=
    ξ.toBilinForm_isAlt.exists_isSymplecticBasis (ξ.toBilinForm_nondegenerate hnd)
  refine ⟨n, e.equivFun.toContinuousLinearEquiv, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis e, Fintype.card_sum, Fintype.card_fin]
    ring
  · ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have h1 := he.apply_eq_sum ξ.toBilinForm_isAlt (v 0) (v 1)
    rw [ContinuousAlternatingMap.toBilinForm_apply] at h1
    have hv : ![v 0, v 1] = v := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at h1
    rw [h1, standardSymplecticForm_apply]
    simp [Basis.equivFun_apply]

end Linear

/-! ### Darboux on a ball, standard form -/

section Darboux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

/-- ★★ **Darboux's theorem on a ball, standard form.** If `ω` is `C^k` (`1 ≤ k ≤ ∞`) and closed
on `ball x₀ R` and `ω(x₀)` is non-degenerate, then `finrank E = 2n` for some `n` and there is a
`C^k` chart `Ψ : E → ℝ^{2n}` with `C^k` inverse, `x₀ ∈ Ψ.source ⊆ ball x₀ R`, differentiable at
every point `y` of its source with an invertible derivative `D`, such that
`ω(y)(u, v) = ω_std(D u, D v)`: `ω = Ψ^* ω_std` with `ω_std = ∑ᵢ dpᵢ ∧ dqᵢ`. -/
theorem exists_openPartialHomeomorph_pullback_standard {k : ℕ∞} (hk : 1 ≤ k)
    (hω : ContDiffOn ℝ k ω (ball x₀ R))
    (hR : 0 < R) (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) :
    ∃ (n : ℕ) (Ψ : OpenPartialHomeomorph E (Fin n ⊕ Fin n → ℝ)), finrank ℝ E = 2 * n ∧
      Ψ.source ⊆ ball x₀ R ∧ x₀ ∈ Ψ.source ∧
      ContDiffOn ℝ k Ψ Ψ.source ∧ ContDiffOn ℝ k Ψ.symm Ψ.target ∧
      ∀ y ∈ Ψ.source, ∃ D : E ≃L[ℝ] (Fin n ⊕ Fin n → ℝ),
        HasFDerivAt Ψ (D : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)) y ∧
        ω y = (standardSymplecticForm (Fin n)).compContinuousLinearMap
          (D : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)) := by
  obtain ⟨Φ, hsub, htsub, hx₀, hfix, hΦ1, hΦs1, hD⟩ :=
    exists_openPartialHomeomorph_symm_pullback_eq hk hω hR hclosed hnd
  obtain ⟨n, L, hn, hL⟩ := exists_continuousLinearEquiv_eq_standardSymplecticForm_comp (ω x₀) hnd
  -- the chart `Ψ = L ∘ Φ⁻¹`
  set Ψ : OpenPartialHomeomorph E (Fin n ⊕ Fin n → ℝ) :=
    Φ.symm.trans L.toHomeomorph.toOpenPartialHomeomorph with hΨ
  have hΨs : Ψ.source = Φ.target := by
    rw [hΨ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ, OpenPartialHomeomorph.symm_source]
  have hΨc : (⇑Ψ : E → Fin n ⊕ Fin n → ℝ) = ⇑L ∘ ⇑Φ.symm := by
    rw [hΨ, OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph]
  have hΨc' : (⇑Ψ.symm : (Fin n ⊕ Fin n → ℝ) → E) = ⇑Φ ∘ ⇑L.symm := by
    funext y
    rfl
  have hΨt : ∀ y ∈ Ψ.target, L.symm y ∈ Φ.source := by
    intro y hy
    rw [hΨ, OpenPartialHomeomorph.trans_target] at hy
    exact hy.2
  have hx₀t : x₀ ∈ Φ.target := by
    have := Φ.map_source hx₀
    rwa [hfix] at this
  refine ⟨n, Ψ, hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΨs]
    exact htsub
  · rw [hΨs]
    exact hx₀t
  · rw [hΨs, hΨc]
    exact L.contDiff.contDiffOn.comp hΦs1 (mapsTo_univ _ _)
  · rw [hΨc']
    exact hΦ1.comp L.symm.contDiff.contDiffOn fun y hy => hΨt y hy
  · intro y hy
    rw [hΨs] at hy
    obtain ⟨D, hDf, hDp⟩ := hD y hy
    refine ⟨D.trans L, ?_, ?_⟩
    · have hcoe : ((D.trans L : E ≃L[ℝ] (Fin n ⊕ Fin n → ℝ)) : E →L[ℝ] (Fin n ⊕ Fin n → ℝ))
          = (L : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)).comp (D : E →L[ℝ] E) :=
        ContinuousLinearMap.ext fun x => rfl
      rw [hcoe, hΨc]
      exact L.hasFDerivAt.comp y hDf
    · rw [hDp, hL]
      ext m
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]

end Darboux

/-! ### Darboux on a symplectic manifold, standard form -/

section Manifold

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

namespace DifferentialForm

/-- ★★ **Darboux's theorem on a symplectic manifold, standard form.** At every point `x₀`,
`finrank E = 2n` and there is a `C^∞` chart `Ψ` of the model space into `ℝ^{2n}` with `C^∞`
inverse, containing `chartAt E x₀ x₀` and contained in the chart's target, along which the local
representative of the form is the pullback of the standard symplectic form
`ω_std = ∑ᵢ dpᵢ ∧ dqᵢ`: the Darboux chart is `Ψ ∘ chartAt E x₀`. -/
theorem IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_standard
    {α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ} (hα : IsSymplectic α) (x₀ : M) :
    ∃ (n : ℕ) (Ψ : OpenPartialHomeomorph E (Fin n ⊕ Fin n → ℝ)), finrank ℝ E = 2 * n ∧
      Ψ.source ⊆ (chartAt E x₀).target ∧ chartAt E x₀ x₀ ∈ Ψ.source ∧
      ContDiffOn ℝ ∞ Ψ Ψ.source ∧ ContDiffOn ℝ ∞ Ψ.symm Ψ.target ∧
      ∀ w ∈ Ψ.source, ∃ D : E ≃L[ℝ] (Fin n ⊕ Fin n → ℝ),
        HasFDerivAt Ψ (D : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)) w ∧
        localRep (fun x => α x) x₀ w
          = (standardSymplecticForm (Fin n)).compContinuousLinearMap
            (D : E →L[ℝ] (Fin n ⊕ Fin n → ℝ)) := by
  have : IsManifold (𝓘(ℝ, E)) (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle ∞ E (TangentSpace (𝓘(ℝ, E)) : M → Type _) (𝓘(ℝ, E)) :=
    TangentBundle.contMDiffVectorBundle
  set w₀ := chartAt E x₀ x₀ with hw₀
  have hw₀t : w₀ ∈ (chartAt E x₀).target := (chartAt E x₀).map_source (mem_chart_source E x₀)
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp (chartAt E x₀).open_target w₀ hw₀t
  have hω : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (localRep (fun x => α x) x₀) (ball w₀ R) :=
    fun w hw => (contDiffAt_localRep (fun x => α x) α.contMDiff_toFun x₀ (hRt hw)).contDiffWithinAt
  have hclosed : ∀ y ∈ ball w₀ R, extDeriv (localRep (fun x => α x) x₀) y = 0 :=
    fun y hy => extDeriv_localRep_eq_zero α hα x₀ (hRt hy)
  have hnd := localRep_nondegenerate α hα.nondegenerate x₀ hw₀t
  obtain ⟨n, Ψ, hn, hsub, hmem, hΨ1, hΨs1, hD⟩ :=
    exists_openPartialHomeomorph_pullback_standard (k := ⊤) le_top hω hR hclosed hnd
  exact ⟨n, Ψ, hn, hsub.trans hRt, hmem, hΨ1, hΨs1, hD⟩

/-- ★ **A symplectic manifold has even dimension.** -/
theorem IsSymplectic.even_finrank {α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ}
    (hα : IsSymplectic α) (x₀ : M) : Even (finrank ℝ E) := by
  obtain ⟨n, _, hn, -⟩ := hα.exists_openPartialHomeomorph_localRep_pullback_standard x₀
  exact ⟨n, by rw [hn]; ring⟩

end DifferentialForm

end Manifold

end
