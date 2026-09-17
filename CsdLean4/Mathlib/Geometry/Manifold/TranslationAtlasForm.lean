/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.ProductSelfModel
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.AddCircleTranslation
public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed

/-!
# Constant forms on a translation atlas, and the area form of the torus

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

A form on a manifold is a family of alternating maps on the tangent spaces with a smoothness
condition read through the charts. When every chart transition is a translation, the tangent
coordinate changes are all the identity, and a *constant* alternating map on the model is a
global smooth form whose local representative in every chart is that constant. This module says
that once, as a predicate on the atlas, and then reads the torus's area form off it.

* `HasTranslationAtlas E M` — the derivative of every chart transition is the identity, at every
  point where the local-representative machinery of `ExteriorDerivative.lean` reads it. Instances:
  `AddCircle T` charted by translation (`Instances/AddCircleTranslation.lean`), and a product of two
  such (`ProductSelfModel.lean`);
* `DifferentialForm.constForm ξ` — the constant family as a `C^∞` `ι`-form, with
  ★ `localRep_constForm` (its local representative in every chart is `ξ`) and
  ★ `constForm_mextDeriv` (**it is closed**: the flat `d` of a constant is zero);
* `areaForm` — the area form `(u, v) ↦ u₁ v₂ − u₂ v₁` on `ℝ × ℝ`, as a continuous alternating
  2-form, with `areaForm_nondegenerate`;
* ★★ `torusAreaForm` — **the area form `dθ₁ ∧ dθ₂` on `AddCircle T × AddCircle T'`**, a term of
  `DifferentialForm 𝓘(ℝ, ℝ × ℝ) (AddCircle T × AddCircle T') ∞ (Fin 2) ℝ`, and
  ★★ `torusAreaForm_isSymplectic` — **the torus is a symplectic manifold**;
* `AddCircle.translationChartCover` (two charts cover the circle) and
  `AddCircle.hasMFDerivAt_coe_comp` (a real curve pushed to the circle has the curve's derivative).

## Honest scope

⚠️ **Nothing is said about the torus's stereographic structure** (`Instances/AddCircle.lean`);
the symplectic torus here is the one charted by translation, over the model `ℝ × ℝ`.

⚠️ **No volume identity.** That `torusAreaForm` integrates to the Haar measure of the torus is
not stated; the corpus's torus measure stays the product Haar measure it always was.

References: `Geometry/Manifold/ExteriorDerivative.lean` (`localRep`, `trivializationAt_snd`,
`mextDeriv`); `Geometry/Manifold/SymplecticForm.lean` (`IsSymplectic`);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (the same construction for the
Fubini–Study form, where the transitions are not translations and chart invariance is a theorem);
`Analysis/InnerProductSpace/KahlerClosed.lean` (`extDeriv_const_apply`);
`specs/BACKLOG.md` (`R-016′`).
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology
open scoped Manifold Bundle Topology ContDiff

/-! ### Atlases whose transitions are translations -/

/-- **A translation atlas**: the derivative of every chart transition is the identity, at every
point where `ExteriorDerivative.lean`'s local-representative machinery reads it. -/
class HasTranslationAtlas (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] : Prop where
  fderiv_chart_transition : ∀ x₀ y : M, y ∈ (chartAt E x₀).source →
    fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) = ContinuousLinearMap.id ℝ E

instance AddCircle.instHasTranslationAtlas {T : ℝ} [Fact (0 < T)] :
    HasTranslationAtlas ℝ (AddCircle T) :=
  ⟨fun x₀ y _ => AddCircle.fderiv_chart_transition x₀ y⟩

section Product

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- A product of translation atlases is a translation atlas. -/
instance Prod.instHasTranslationAtlas [HasTranslationAtlas E M] [HasTranslationAtlas F N] :
    HasTranslationAtlas (E × F) (M × N) := by
  refine ⟨?_⟩
  rintro ⟨x₀, y₀⟩ ⟨x, y⟩ h
  rw [Prod.chartAt_prod_source] at h
  obtain ⟨hx, hy⟩ := Set.mem_prod.1 h
  rw [Prod.chartAt_prod_apply]
  rw [Prod.fderiv_chart_transition_prod x₀ x y₀ y (w := (chartAt E x₀ x, chartAt F y₀ y))
    ((chartAt E x₀).map_source hx)
    (by rw [(chartAt E x₀).left_inv hx]; exact mem_chart_source E x)
    ((chartAt F y₀).map_source hy)
    (by rw [(chartAt F y₀).left_inv hy]; exact mem_chart_source F y)]
  rw [HasTranslationAtlas.fderiv_chart_transition x₀ x hx,
    HasTranslationAtlas.fderiv_chart_transition y₀ y hy]
  exact ContinuousLinearMap.ext fun _ => rfl

end Product

/-! ### Constant forms -/

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [HasTranslationAtlas E M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

/-- The constant family `x ↦ ξ` on the tangent spaces. -/
def constFamily (ξ : E [⋀^ι]→L[ℝ] G) (x : M) :
    TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x := ξ

omit [IsManifold 𝓘(ℝ, E) ∞ M] [HasTranslationAtlas E M] [Fintype ι] in
theorem constFamily_apply (ξ : E [⋀^ι]→L[ℝ] G) (x : M) : constFamily ξ x = ξ := rfl

/-- Through the tangent trivialisation at `x₀`, the constant family reads as the constant: the
coordinate change is the identity on a translation atlas. -/
theorem trivializationAt_constFamily_snd (ξ : E [⋀^ι]→L[ℝ] G) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt (E [⋀^ι]→L[ℝ] G)
      (fun x : M => TangentSpace 𝓘(ℝ, E) x [⋀^ι]→L[ℝ] Bundle.Trivial M G x) x₀
      ⟨y, constFamily ξ y⟩).2 = ξ := by
  rw [trivializationAt_snd (constFamily ξ) x₀ y hy,
    HasTranslationAtlas.fderiv_chart_transition x₀ y hy]
  exact ContinuousAlternatingMap.ext fun _ => rfl

/-- ★ The local representative of the constant family, in every chart, is the constant. -/
theorem localRep_constFamily (ξ : E [⋀^ι]→L[ℝ] G) (x₀ : M) {w : E}
    (hw : w ∈ (chartAt E x₀).target) :
    localRep (constFamily ξ) x₀ w = ξ :=
  trivializationAt_constFamily_snd ξ x₀ _ ((chartAt E x₀).map_target hw)

/-- The constant family is a `C^∞` section. -/
theorem contMDiff_constFamily (ξ : E [⋀^ι]→L[ℝ] G) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) ∞
      (fun x : M => TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) x (constFamily ξ x)) := by
  intro x₀
  rw [contMDiffAt_section]
  refine (contMDiffAt_const (c := ξ)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_constFamily_snd ξ x₀ y hy

/-- ★ **The constant form** `x ↦ ξ` on a manifold with a translation atlas. -/
def constForm (ξ : E [⋀^ι]→L[ℝ] G) : DifferentialForm 𝓘(ℝ, E) M ∞ ι G :=
  ⟨constFamily ξ, contMDiff_constFamily ξ⟩

@[simp] theorem constForm_apply (ξ : E [⋀^ι]→L[ℝ] G) (x : M) : constForm ξ x = ξ := rfl

/-- The constant form is closed, pointwise: its local representative near the chart image of
`x` is the constant, whose flat `d` is zero. -/
theorem mextDerivFamily_constFamily {k : ℕ} (ξ : E [⋀^Fin k]→L[ℝ] G) (x : M) :
    mextDerivFamily (constFamily ξ : ∀ x : M, TangentSpace 𝓘(ℝ, E) x [⋀^Fin k]→L[ℝ]
      Bundle.Trivial M G x) x = 0 := by
  show extDeriv (localRep (constFamily ξ) x) (chartAt E x x) = 0
  have hev : localRep (constFamily ξ) x =ᶠ[𝓝 (chartAt E x x)] fun _ => ξ := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with w hw
    exact localRep_constFamily ξ x hw
  rw [hev.extDeriv_eq]
  exact extDeriv_const_apply ξ _

/-- ★ **The constant form is closed.** -/
theorem constForm_mextDeriv {k : ℕ} (ξ : E [⋀^Fin k]→L[ℝ] G) :
    (constForm (M := M) ξ).mextDeriv = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact mextDerivFamily_constFamily ξ x

end DifferentialForm

/-! ### The area form on `ℝ × ℝ` -/

namespace TorusForm

/-- The area pairing `(u, v) ↦ u₁ v₂ − u₂ v₁` on `ℝ × ℝ`. -/
def area (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

theorem area_self (u : ℝ × ℝ) : area u u = 0 := by simp [area, mul_comm]

theorem area_swap (u v : ℝ × ℝ) : area u v = -area v u := by simp [area]; ring

theorem abs_area_le (u v : ℝ × ℝ) : |area u v| ≤ 2 * (‖u‖ * ‖v‖) := by
  have h1 : |u.1| ≤ ‖u‖ := by simpa using norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by simpa using norm_snd_le u
  have h3 : |v.1| ≤ ‖v‖ := by simpa using norm_fst_le v
  have h4 : |v.2| ≤ ‖v‖ := by simpa using norm_snd_le v
  calc |area u v| = |u.1 * v.2 - u.2 * v.1| := rfl
    _ ≤ |u.1 * v.2| + |u.2 * v.1| := abs_sub _ _
    _ = |u.1| * |v.2| + |u.2| * |v.1| := by rw [abs_mul, abs_mul]
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := by gcongr
    _ = 2 * (‖u‖ * ‖v‖) := by ring

/-- The area pairing as a bilinear map. -/
def areaBilin : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ area
    (fun u u' v => by simp [area]; ring)
    (fun r u v => by simp [area]; ring)
    (fun u v v' => by simp [area]; ring)
    (fun r u v => by simp [area]; ring)

/-- The area pairing as a continuous bilinear map. -/
def areaCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ areaBilin 2 fun u v => by
    simpa [areaBilin, Real.norm_eq_abs, mul_assoc] using abs_area_le u v

@[simp] theorem areaCLM_apply (u v : ℝ × ℝ) : areaCLM u v = area u v := rfl

/-- The area pairing as a continuous multilinear map on `Fin 2 → ℝ × ℝ`. -/
def areaMulti : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (((continuousMultilinearCurryFin1 ℝ (ℝ × ℝ) ℝ).symm.toLinearIsometry.toContinuousLinearMap).comp
      areaCLM)

@[simp] theorem areaMulti_apply (v : Fin 2 → ℝ × ℝ) : areaMulti v = area (v 0) (v 1) := by
  simp [areaMulti, Fin.tail]

/-- ★ **The area form** `dx ∧ dy` on `ℝ × ℝ`, as a continuous alternating 2-form. -/
def areaForm : (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ where
  toContinuousMultilinearMap := areaMulti
  map_eq_zero_of_eq' := by
    intro v i j hv hne
    fin_cases i <;> fin_cases j <;> simp_all [areaMulti_apply, area_self]

@[simp] theorem areaForm_apply (v : Fin 2 → ℝ × ℝ) : areaForm v = area (v 0) (v 1) :=
  areaMulti_apply v

/-- ★ **The area form is non-degenerate**: a nonzero vector pairs non-trivially with its quarter
turn. -/
theorem areaForm_nondegenerate {v : ℝ × ℝ} (hv : v ≠ 0) :
    ∃ w, areaForm ![v, w] ≠ 0 := by
  refine ⟨(-v.2, v.1), ?_⟩
  simp only [areaForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, area]
  have : v.1 * v.1 + v.2 * v.2 ≠ 0 := by
    intro h
    apply hv
    have h1 : v.1 = 0 := by nlinarith
    have h2 : v.2 = 0 := by nlinarith
    exact Prod.ext h1 h2
  intro h
  apply this
  linarith

end TorusForm

/-! ### A two-chart cover of the circle -/

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

theorem coe_half_ne_zero : ((T / 2 : ℝ) : AddCircle T) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff T).1 h0
  have hTpos := hT.out
  rw [zsmul_eq_mul] at hn
  have h2 : ((n * 2 : ℤ) : ℝ) * T = 1 * T := by push_cast; linarith
  have h3 : (n * 2 : ℤ) = 1 := by exact_mod_cast mul_right_cancel₀ hTpos.ne' h2
  omega

theorem cutPoint_zero : cutPoint (0 : AddCircle T) = T / 2 := by
  have h : ((equivIco T 0 (0 : AddCircle T) : ℝ)) = 0 := by
    have := equivIco_coe_of_mem (p := T) (a := 0) (y := 0)
      ⟨le_refl _, by simpa using hT.out⟩
    simpa using this
  simp [cutPoint, h]

theorem cutPoint_coe_half : cutPoint ((T / 2 : ℝ) : AddCircle T) = T := by
  have hTpos := hT.out
  have h : ((equivIco T 0 ((T / 2 : ℝ) : AddCircle T) : ℝ)) = T / 2 :=
    equivIco_coe_of_mem ⟨by linarith, by linarith⟩
  rw [cutPoint, h]
  ring

/-- Two translation charts cover the circle: the ones with cut points `T/2` and `T ≡ 0`. -/
def translationChartCover : ChartCover ℝ (AddCircle T) where
  m := 2
  pt := ![(0 : AddCircle T), ((T / 2 : ℝ) : AddCircle T)]
  cover := fun y => by
    by_cases h : y = ((T / 2 : ℝ) : AddCircle T)
    · refine ⟨1, ?_⟩
      show y ∈ (chartAt ℝ ((T / 2 : ℝ) : AddCircle T)).source
      rw [chartAt_eq, translationChart_source, cutPoint_coe_half, coe_period]
      rw [h]
      exact coe_half_ne_zero
    · refine ⟨0, ?_⟩
      show y ∈ (chartAt ℝ (0 : AddCircle T)).source
      rw [chartAt_eq, translationChart_source, cutPoint_zero]
      exact h

end AddCircle

/-! ### Curves on the circle -/

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]

/-- A real curve pushed to the circle: the manifold derivative is the curve's derivative
(`hasMFDerivAt_coe` composed with the curve). -/
theorem hasMFDerivAt_coe_comp {g : ℝ → ℝ} {g' : ℝ} {s : ℝ} (hg : HasDerivAt g g' s) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ => ((g u : ℝ) : AddCircle T)) s
      (ContinuousLinearMap.smulRight (M₂ := TangentSpace 𝓘(ℝ, ℝ) ((g s : ℝ) : AddCircle T))
        (1 : ℝ →L[ℝ] ℝ) g') := by
  -- elaborate the flat derivative at its own type first; feeding it straight into the manifold
  -- iff makes `smulRight` look for `ContinuousSMul` along the `TangentSpace` instance path
  have hg' : HasFDerivAt g ((1 : ℝ →L[ℝ] ℝ).smulRight g') s := hasDerivAt_iff_hasFDerivAt.1 hg
  have hg'' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g s ((1 : ℝ →L[ℝ] ℝ).smulRight g') :=
    hasMFDerivAt_iff_hasFDerivAt.2 hg'
  have h := (hasMFDerivAt_coe (T := T) (g s)).comp s hg''
  refine h.congr_deriv ?_
  ext
  rfl

end AddCircle

/-! ### The torus as a symplectic manifold -/

namespace AddCircle

open TorusForm DifferentialForm

variable {T T' : ℝ} [Fact (0 < T)] [Fact (0 < T')]

/-- ★★ **The area form `dθ₁ ∧ dθ₂` on the torus** `AddCircle T × AddCircle T'`, charted by
translation over `ℝ × ℝ`: the constant form with model `areaForm`. -/
def torusAreaForm : DifferentialForm 𝓘(ℝ, ℝ × ℝ) (AddCircle T × AddCircle T') ∞ (Fin 2) ℝ :=
  constForm areaForm

@[simp] theorem torusAreaForm_apply (x : AddCircle T × AddCircle T') :
    torusAreaForm (T := T) (T' := T') x = areaForm := rfl

/-- ★★ **The torus is a symplectic manifold**: the area form is closed (it is constant in every
chart) and non-degenerate (it is the area form). -/
theorem torusAreaForm_isSymplectic : (torusAreaForm (T := T) (T' := T')).IsSymplectic :=
  ⟨constForm_mextDeriv areaForm, fun _ _ hv => areaForm_nondegenerate hv⟩

end AddCircle

end
