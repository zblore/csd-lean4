/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyMass
public import CsdLean4.Mathlib.Geometry.Manifold.TranslationAtlasForm
public import CsdLean4.Mathlib.Geometry.Manifold.ProductForm
public import CsdLean4.Mathlib.Geometry.Manifold.WedgePowPairs
public import Mathlib.MeasureTheory.Group.AddCircle

/-!
# The volume of `ℂℙⁿ × T²`: the top power of `π₁^* ω_FS + π₂^* (dθ₁ ∧ dθ₂)`

**Category:** 1-Mathlib (CSD-free).

On the product `ℙ ℂ (Ambient n) × (AddCircle T × AddCircle T')`, charted over
`(Fin n → ℂ) × (ℝ × ℝ)`, the sum of the Fubini–Study form and the torus area form
(`prodForm`, `ProductForm.lean`) has an `(n + 1)`-st power whose coefficient on the product
basis is `(n + 1)` times the Fubini–Study coefficient: the product basis is a weighted pair tuple
for the flat sum, with weight `-4` on the `n` sector pairs and `1` on the torus pair
(`WedgePowPairs.lean`), and the model form at every chart point is a pullback of the model form at
the origin (`fsModelForm_eq_comp`). The measure of the top power on a product chart domain then
factorises through Tonelli into `(n + 1)` times the mass of the Fubini–Study volume
(`fsVolume_univ`) times the area of the torus chart.

* `prodTorusBasis n` — the basis of the product model: the standard basis of `Fin n → ℂ`
  followed by the two coordinate vectors of `ℝ × ℝ`, re-indexed along `powEquiv n`;
* `prodTorusWeight`, `isWeightedPairFamily_prodTorus`, `isWeightedPairTuple_prodTorusBasis`,
  ★ `wedgePow_prodSum_stdForm_areaForm_prodTorusBasis` — **the count** on the product basis:
  `(-4)ⁿ (n + 1)!`;
* ★★ `wedgePow_prodSum_fsModelForm_areaForm_prodTorusBasis` — **the coefficient everywhere on
  the chart**: `(-4)ⁿ (n + 1)! (1 + ‖w‖²)^{-(n+1)}`, so `(n + 1)` times the Fubini–Study
  coefficient (`wedgePow_fsModelForm_stdBasis`);
* ★ `chartDensity_prodTorus` — the chart density of the product top form at a product chart point
  is `(n + 1)` times the Fubini–Study chart density of the sector coordinate;
* `AddCircle.volume_singleton`, `AddCircle.volume_compl_singleton`, `volume_prod_chartAt_target`
  — the Lebesgue area of a torus chart target is `T · T'`;
* ★★ `topFormMeasure_prodTorus_chartAt_source` — **the measure of the top power of the product
  form on a product chart domain is `(n + 1) (4π)ⁿ · T T'`**, for every chart cover;
  ★ `topFormMeasure_prodTorus_ne_zero`.

## Honest scope

⚠️ **One chart domain, not the whole product.** The measure of the complement of a product chart
domain is not shown null here; a consumer that has identified the measure with a product measure
(as the source repository does by uniqueness of the invariant measures) reads the total mass off
the chart value. The general statement, that the top-power measure of `π₁^* α + π₂^* β` is
`(m + 1)` times the product of the factors' top-power measures, is not proved
(`ProductForm.lean`, honest scope): the count here is for this pair of forms on this basis.

⚠️ **The torus factor is `AddCircle T × AddCircle T'` charted by translation** (`TranslationAtlasForm.lean`);
nothing is said about the torus area form on its own (its top-form measure is not identified
with Haar measure).

References: `Geometry/Manifold/WedgePowPairs.lean`; `Geometry/Manifold/ProductForm.lean`
(`localRep_prodFamily`); `Geometry/Manifold/TranslationAtlasForm.lean` (`areaForm`,
`torusAreaForm`, `localRep_constFamily`); `Instances/ProjectiveSpaceFubiniStudyMass.lean`
(`fsModelForm_eq_comp`, `fsVolume_univ_eq_lintegral`, `fsVolume_univ`);
`Geometry/Manifold/TopFormMeasure.lean` (`topFormMeasure_apply_of_subset_source`,
`chartMeasure_apply`); `Mathlib/MeasureTheory/Measure/Prod.lean` (`lintegral_prod_mul`).
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology Set MeasureTheory DifferentialForm ContinuousAlternatingMap
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization ENNReal Real

namespace Projectivization

variable {n : ℕ}

/-! ### The basis of the product model -/

/-- The real basis of the product model `(Fin n → ℂ) × (ℝ × ℝ)`: the standard basis of the
sector factor followed by the two coordinate vectors of the torus factor, indexed by
`Fin (2 * (n + 1))` along `powEquiv n`. -/
def prodTorusBasis (n : ℕ) : Module.Basis (Fin (2 * (n + 1))) ℝ ((Fin n → ℂ) × (ℝ × ℝ)) :=
  ((stdBasis n).prod (Module.Basis.finTwoProd ℝ)).reindex (DifferentialForm.powEquiv n)

theorem prodTorusBasis_powEquiv (x : Fin (2 * n) ⊕ Fin 2) :
    prodTorusBasis n (DifferentialForm.powEquiv n x)
      = (stdBasis n).prod (Module.Basis.finTwoProd ℝ) x := by
  rw [prodTorusBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply]

/-! ### The count on the product basis -/

/-- The weights of the product basis for `π₁^*(-4 ω_std) + π₂^* (dθ₁ ∧ dθ₂)`: `-4` on the `n`
sector pairs, `1` on the torus pair. -/
def prodTorusWeight (n : ℕ) (j : Fin (n + 1)) : ℝ := if j = Fin.last n then 1 else -4

theorem prod_prodTorusWeight (n : ℕ) : ∏ j, prodTorusWeight n j = (-4 : ℝ) ^ n := by
  rw [Fin.prod_univ_castSucc]
  simp [prodTorusWeight, (Fin.castSucc_lt_last _).ne]

/-- The product basis, as a family on `Fin (2n) ⊕ Fin 2`, is a weighted pair family for
`π₁^*(-4 ω_std) + π₂^* (dθ₁ ∧ dθ₂)`. -/
theorem isWeightedPairFamily_prodTorus :
    IsWeightedPairFamily (prodSum ((-4 : ℝ) • stdForm n) TorusForm.areaForm) (prodTorusWeight n)
      ((stdBasis n).prod (Module.Basis.finTwoProd ℝ)) := by
  intro x y
  have hne' : ∀ i : Fin n, Fin.castSucc i ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
  rw [prodSum_pair]
  rcases x with i | a <;> rcases y with i' | b
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inl_snd,
      ContinuousAlternatingMap.smul_apply, stdBasis_eq_pairFamily, stdBasis_eq_pairFamily,
      slotPair_inl_eq_castSucc, slotPair_inl_eq_castSucc, slotMem_inl_eq_memIdx,
      slotMem_inl_eq_memIdx]
    simp only [pairFamily, stdForm_single, id, im_conj_mul_pairs, TorusForm.areaForm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, TorusForm.area_self, add_zero, smul_eq_mul,
      prodTorusWeight, hne', if_false, Fin.castSucc_inj]
    split_ifs <;> ring
  · have h1 : ((-4 : ℝ) • stdForm n) ![stdBasis n i, 0] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 1 rfl
    have h2 : TorusForm.areaForm ![0, Module.Basis.finTwoProd ℝ b] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 0 rfl
    rw [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd, slotPair_inr,
      slotPair_inl_eq_castSucc, if_neg (hne' _), h1, h2, add_zero]
  · have h1 : ((-4 : ℝ) • stdForm n) ![0, stdBasis n i'] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 0 rfl
    have h2 : TorusForm.areaForm ![Module.Basis.finTwoProd ℝ a, 0] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 1 rfl
    rw [Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inr_snd, Module.Basis.prod_apply_inl_snd, slotPair_inr,
      slotPair_inl_eq_castSucc, if_neg (hne' _).symm, h1, h2, add_zero]
  · have h1 : ((-4 : ℝ) • stdForm n) ![0, 0] = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 0 rfl
    rw [Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inr_snd, Module.Basis.prod_apply_inr_snd, slotPair_inr,
      slotPair_inr, slotMem_inr, slotMem_inr, if_pos rfl, h1, zero_add, prodTorusWeight,
      if_pos rfl, one_mul, TorusForm.areaForm_apply]
    fin_cases a <;> fin_cases b <;>
      simp [TorusForm.area, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, pairSign]

/-- The product basis is a weighted pair tuple for `π₁^*(-4 ω_std) + π₂^* (dθ₁ ∧ dθ₂)`. -/
theorem isWeightedPairTuple_prodTorusBasis :
    IsWeightedPairTuple (prodSum ((-4 : ℝ) • stdForm n) TorusForm.areaForm) (prodTorusWeight n)
      (prodTorusBasis n) := by
  rw [isWeightedPairTuple_iff]
  simpa only [prodTorusBasis_powEquiv] using isWeightedPairFamily_prodTorus (n := n)

/-- ★ **The count on the product basis**: the `(n + 1)`-st power of
`π₁^*(-4 ω_std) + π₂^* (dθ₁ ∧ dθ₂)` on the product basis is `(-4)ⁿ (n + 1)!`. -/
theorem wedgePow_prodSum_stdForm_areaForm_prodTorusBasis :
    wedgePow (prodSum ((-4 : ℝ) • stdForm n) TorusForm.areaForm) (n + 1) (prodTorusBasis n)
      = (-4 : ℝ) ^ n * (n + 1).factorial := by
  rw [wedgePow_apply_of_isWeightedPairTuple _ _ _ _ isWeightedPairTuple_prodTorusBasis,
    prod_prodTorusWeight, mul_comm]

/-- ★★ **The coefficient of the top power of the product form on the product basis, everywhere
on the chart**: `(-4)ⁿ (n + 1)! (1 + ‖w‖²)^{-(n+1)}`, i.e. `(n + 1)` times the Fubini–Study
coefficient `wedgePow_fsModelForm_stdBasis`. The model form at `w` is the pullback of the model
form at the origin along `L` (`fsModelForm_eq_comp`), so the flat sum at `w` is the pullback of the
flat sum at the origin along `L × id`, whose determinant is that of `L`. -/
theorem wedgePow_prodSum_fsModelForm_areaForm_prodTorusBasis (w : Fin n → ℂ) :
    wedgePow (prodSum (fsModelForm w) TorusForm.areaForm) (n + 1) (prodTorusBasis n)
      = (-4 : ℝ) ^ n * (n + 1).factorial * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1) := by
  obtain ⟨L, hL, hdet⟩ := fsModelForm_eq_comp w
  have hid : TorusForm.areaForm
      = TorusForm.areaForm.compContinuousLinearMap (ContinuousLinearMap.id ℝ (ℝ × ℝ)) :=
    ContinuousAlternatingMap.ext fun _ => rfl
  have hdet' : (L.prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).det = L.det := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
      ContinuousLinearMap.coe_id, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  rw [hL, hid, ← prodSum_compContinuousLinearMap_prodMap, ← wedgePow_compContinuousLinearMap,
    compContinuousLinearMap_apply_basis, hdet', hdet, fsModelForm_zero,
    wedgePow_prodSum_stdForm_areaForm_prodTorusBasis]
  ring

/-! ### The chart density of the product form -/

/-- Lebesgue measure on the torus model `ℝ × ℝ`, as an explicit product, is Haar (instance search
does not see it through `volume`). -/
instance instIsAddHaarMeasure_torusModel :
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on the product model `(Fin n → ℂ) × (ℝ × ℝ)`, as an explicit product, is
Haar. -/
instance instIsAddHaarMeasure_prodTorusModel (n : ℕ) :
    ((volume : Measure (Fin n → ℂ)).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

section Torus

variable {T T' : ℝ} [hT : Fact (0 < T)] [hT' : Fact (0 < T')]

/-- ★ **The chart density of the top power of the product form at a product chart point** is
`(n + 1)` times the Fubini–Study chart density of the sector coordinate: the torus factor's
constant form has coefficient `1` in every translation chart. -/
theorem chartDensity_prodTorus (x₀ : ℙ ℂ (Ambient n)) (y₀ : AddCircle T × AddCircle T')
    (w₁ : Fin n → ℂ) {w₂ : ℝ × ℝ} (hw₂ : w₂ ∈ (chartAt (ℝ × ℝ) y₀).target) :
    chartDensity (prodTorusBasis n)
      (fun p => wedgePow (prodForm (fsForm (n := n)) (AddCircle.torusAreaForm (T := T) (T' := T')))
        (n + 1) p) (x₀, y₀) (w₁, w₂)
      = ENNReal.ofReal (n + 1) * chartDensity (stdBasis n) (fun x => fsTopForm n x) x₀ w₁ := by
  have hw : (w₁, w₂) ∈ (chartAt ((Fin n → ℂ) × (ℝ × ℝ)) (x₀, y₀)).target := by
    rw [Prod.chartAt_prod_target]
    exact Set.mk_mem_prod (Set.mem_univ _) hw₂
  have h1 : localRep (fun p => prodForm (fsForm (n := n))
      (AddCircle.torusAreaForm (T := T) (T' := T')) p) (x₀, y₀) (w₁, w₂)
      = prodSum (fsModelForm w₁) TorusForm.areaForm := by
    rw [show (fun p => prodForm (fsForm (n := n)) (AddCircle.torusAreaForm (T := T) (T' := T')) p)
        = prodFamily (fun x => fsForm (n := n) x)
          (fun y => AddCircle.torusAreaForm (T := T) (T' := T') y) from rfl,
      localRep_prodFamily _ _ x₀ y₀ hw]
    congr 1
    · exact localRep_fsSection' x₀ w₁
    · exact localRep_constFamily _ y₀ hw₂
  have key : ∀ t : ℝ, |(-4 : ℝ) ^ n * ((n + 1).factorial : ℝ) * t|
      = (n + 1) * |(-4 : ℝ) ^ n * (n.factorial : ℝ) * t| := fun t => by
    rw [Nat.factorial_succ]
    push_cast
    rw [show (-4 : ℝ) ^ n * ((n + 1) * n.factorial) * t
        = (n + 1) * ((-4 : ℝ) ^ n * n.factorial * t) by ring,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  unfold chartDensity
  rw [localRep_wedgePow _ _ hw, localRep_fsTopForm, h1,
    wedgePow_prodSum_fsModelForm_areaForm_prodTorusBasis, wedgePow_fsModelForm_stdBasis,
    ← ENNReal.ofReal_mul (by positivity), key]

/-! ### The area of a torus chart -/

/-- A point of the circle is null. -/
theorem _root_.AddCircle.volume_singleton (a : AddCircle T) :
    volume ({a} : Set (AddCircle T)) = 0 := by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  simp [hT.out.le]

/-- The circle minus a point has full measure `T`. -/
theorem _root_.AddCircle.volume_compl_singleton (a : AddCircle T) :
    volume ({a}ᶜ : Set (AddCircle T)) = ENNReal.ofReal T := by
  rw [measure_compl (measurableSet_singleton a) (measure_ne_top _ _), AddCircle.volume_singleton,
    AddCircle.measure_univ, tsub_zero]

/-- The Lebesgue area of the torus chart target `(a, a + T) × (b, b + T')` is `T · T'`. -/
theorem volume_prod_chartAt_target (y₀ : AddCircle T × AddCircle T') :
    (volume : Measure ℝ).prod volume (chartAt (ℝ × ℝ) y₀).target
      = ENNReal.ofReal T * ENNReal.ofReal T' := by
  obtain ⟨y₁, y₂⟩ := y₀
  rw [Prod.chartAt_prod_target, Measure.prod_prod, AddCircle.chartAt_eq, AddCircle.chartAt_eq,
    AddCircle.translationChart_target, AddCircle.translationChart_target, Real.volume_Ioo,
    Real.volume_Ioo, add_sub_cancel_left, add_sub_cancel_left]

/-! ### The measure of a product chart domain -/

/-- ★★ **The measure of the top power of the product form on a product chart domain** is
`(n + 1) (4π)ⁿ · T T'`, for every chart cover: on the chart at `(origin 0, y₀)` the chart integral
factorises through Tonelli into `(n + 1)` times the mass of the Fubini–Study volume
(`fsVolume_univ`) times the area of the torus chart. -/
theorem topFormMeasure_prodTorus_chartAt_source
    (c : ChartCover ((Fin n → ℂ) × (ℝ × ℝ)) (ℙ ℂ (Ambient n) × (AddCircle T × AddCircle T')))
    (y₀ : AddCircle T × AddCircle T') :
    topFormMeasure ((volume : Measure (Fin n → ℂ)).prod ((volume : Measure ℝ).prod volume))
      (prodTorusBasis n)
      (fun p => wedgePow (prodForm (fsForm (n := n)) (AddCircle.torusAreaForm (T := T) (T' := T')))
        (n + 1) p) c (chartAt ((Fin n → ℂ) × (ℝ × ℝ)) (origin 0, y₀)).source
      = ENNReal.ofReal ((n + 1) * (4 * π) ^ n * (T * T')) := by
  set s := fun p : ℙ ℂ (Ambient n) × (AddCircle T × AddCircle T') =>
    wedgePow (prodForm (fsForm (n := n)) (AddCircle.torusAreaForm (T := T) (T' := T'))) (n + 1) p
    with hs
  set e := chartAt ((Fin n → ℂ) × (ℝ × ℝ)) (origin (n := n) 0, y₀) with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  rw [topFormMeasure_apply_of_subset_source _ _ _ c (origin 0, y₀) hS subset_rfl,
    chartMeasure_apply _ _ _ _ hS]
  have hT₀ : e.target ∩ e.symm ⁻¹' e.source = e.target :=
    Set.inter_eq_left.2 fun w hw => e.map_target hw
  rw [hT₀]
  have hdens : Set.EqOn (chartDensity (prodTorusBasis n) s (origin 0, y₀))
      (fun w => ENNReal.ofReal (n + 1)
        * chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin 0) w.1) e.target := by
    rintro ⟨w₁, w₂⟩ hw
    rw [he, Prod.chartAt_prod_target] at hw
    exact chartDensity_prodTorus (origin 0) y₀ w₁ hw.2
  rw [setLIntegral_congr_fun e.open_target.measurableSet hdens, he, Prod.chartAt_prod_target,
    ← Measure.prod_restrict, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hf : AEMeasurable (chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin 0))
      ((volume : Measure (Fin n → ℂ)).restrict
        (chartAt (Fin n → ℂ) (origin (n := n) 0)).target) :=
    measurable_chartDensity_fsTopForm_origin_zero.aemeasurable
  have hg : AEMeasurable (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))
      (((volume : Measure ℝ).prod volume).restrict (chartAt (ℝ × ℝ) y₀).target) :=
    aemeasurable_const
  have hprod := lintegral_prod_mul hf hg
  simp only [mul_one] at hprod
  rw [hprod, lintegral_one, Measure.restrict_apply_univ, volume_prod_chartAt_target,
    show (chartAt (Fin n → ℂ) (origin (n := n) 0)).target = Set.univ from rfl,
    Measure.restrict_univ, ← fsVolume_univ_eq_lintegral, fsVolume_univ,
    ← ENNReal.ofReal_mul hT.out.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 * π) ^ n),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  congr 1
  ring

/-- ★ The measure of the top power of the product form is nonzero. -/
theorem topFormMeasure_prodTorus_ne_zero
    (c : ChartCover ((Fin n → ℂ) × (ℝ × ℝ)) (ℙ ℂ (Ambient n) × (AddCircle T × AddCircle T'))) :
    topFormMeasure ((volume : Measure (Fin n → ℂ)).prod ((volume : Measure ℝ).prod volume))
      (prodTorusBasis n)
      (fun p => wedgePow (prodForm (fsForm (n := n)) (AddCircle.torusAreaForm (T := T) (T' := T')))
        (n + 1) p) c ≠ 0 := by
  intro h
  have h0 := topFormMeasure_prodTorus_chartAt_source (n := n) (T := T) (T' := T') c 0
  rw [h, Measure.coe_zero, Pi.zero_apply] at h0
  have hTpos := hT.out
  have hT'pos := hT'.out
  exact absurd h0.symm (ENNReal.ofReal_pos.2 (by positivity)).ne'

end Torus

end Projectivization

end
