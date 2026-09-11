/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A measurable unit section of the ray map

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The ray map `mk : {v // v ≠ 0} → ℙ 𝕜 (EuclideanSpace 𝕜 ι)` has no continuous section (the
tautological bundle is non-trivial), but it has a **measurable** one, and a canonical one: send a
ray to its unit-norm representative whose **first non-zero coordinate is real and positive**.

* `firstIndex` — the first non-zero coordinate of a non-zero vector (`ι` linearly ordered);
* `unitScalar`, `unitRep` — the normalising scalar `conj(vᵢ)/|vᵢ| · ‖v‖⁻¹` and the representative
  it produces; `unitRep_smul` is scale-invariance, so `unitRep` descends to the quotient;
* `unitSection` — the section `ℙ 𝕜 (EuclideanSpace 𝕜 ι) → EuclideanSpace 𝕜 ι`, with
  `norm_unitSection : ‖unitSection p‖ = 1` and `mk_unitSection : mk (unitSection p) = p`;
* ★ `measurable_unitSection` — it is Borel measurable: `unitRep` is the finite sum over `i` of the
  candidate `i` (a measurable function of `v`) restricted to the measurable set "first index
  `= i`" (`measurableSet_firstIndex_eq`), and `Projectivization.lift_measurable` descends it.

This discharges the hypothesis every preparation-level construction of the corpus takes (a
unit-norm measurable `rep` with `mk (rep p) = p`): `Projectivization.unitSection` is such a
`rep`, for every finite-dimensional `EuclideanSpace` over `ℝ` or `ℂ`.

References: `CsdLean4/Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean`
(`lift_measurable`); `CsdLean4/LF2/FlowChannel.lean` (`isUnitaryLift_unitSection`, the consumer);
`specs/qit-chain-scoping.md` (W6″).
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### The first non-zero coordinate -/

/-- The support of a vector, as a finset of coordinates. -/
def coordSupport (v : EuclideanSpace 𝕜 ι) : Finset ι := Finset.univ.filter fun i => v i ≠ 0

omit [LinearOrder ι] in
theorem mem_coordSupport {v : EuclideanSpace 𝕜 ι} {i : ι} : i ∈ coordSupport v ↔ v i ≠ 0 := by
  simp [coordSupport]

omit [LinearOrder ι] in
theorem coordSupport_nonempty {v : EuclideanSpace 𝕜 ι} (hv : v ≠ 0) : (coordSupport v).Nonempty := by
  by_contra h
  apply hv
  ext i
  have : i ∉ coordSupport v := fun hi => h ⟨i, hi⟩
  simpa [mem_coordSupport] using this

omit [LinearOrder ι] in
theorem coordSupport_smul {v : EuclideanSpace 𝕜 ι} {t : 𝕜} (ht : t ≠ 0) :
    coordSupport (t • v) = coordSupport v := by
  ext i
  simp [mem_coordSupport, ht]

/-- The first non-zero coordinate of a non-zero vector. -/
noncomputable def firstIndex (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : ι :=
  (coordSupport v.1).min' (coordSupport_nonempty v.2)

theorem apply_firstIndex_ne_zero (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) :
    v.1 (firstIndex v) ≠ 0 :=
  mem_coordSupport.mp (Finset.min'_mem _ _)

theorem firstIndex_le (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) {i : ι} (hi : v.1 i ≠ 0) :
    firstIndex v ≤ i :=
  Finset.min'_le _ _ (mem_coordSupport.mpr hi)

theorem apply_eq_zero_of_lt_firstIndex (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) {j : ι}
    (hj : j < firstIndex v) : v.1 j = 0 := by
  by_contra h
  exact absurd (firstIndex_le v h) (not_le.mpr hj)

theorem firstIndex_eq_iff (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) (i : ι) :
    firstIndex v = i ↔ v.1 i ≠ 0 ∧ ∀ j, j < i → v.1 j = 0 := by
  constructor
  · rintro rfl
    exact ⟨apply_firstIndex_ne_zero v, fun j hj => apply_eq_zero_of_lt_firstIndex v hj⟩
  · rintro ⟨hi, hlt⟩
    refine le_antisymm (firstIndex_le v hi) ?_
    by_contra h
    exact apply_firstIndex_ne_zero v (hlt _ (not_le.mp h))

theorem firstIndex_smul (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) {t : 𝕜} (ht : t ≠ 0) :
    firstIndex ⟨t • v.1, smul_ne_zero ht v.2⟩ = firstIndex v := by
  simp only [firstIndex]
  congr 1
  exact coordSupport_smul ht

/-! ### The unit section -/

/-- The normalising scalar of a non-zero vector: the conjugate phase of its first non-zero
coordinate, over the norm. -/
noncomputable def unitScalar (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : 𝕜 :=
  (starRingEnd 𝕜 (v.1 (firstIndex v)) / (‖v.1 (firstIndex v)‖ : 𝕜)) * ((‖v.1‖⁻¹ : ℝ) : 𝕜)

theorem norm_unitScalar (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : ‖unitScalar v‖ * ‖v.1‖ = 1 := by
  have h1 : ‖v.1 (firstIndex v)‖ ≠ 0 := norm_ne_zero_iff.mpr (apply_firstIndex_ne_zero v)
  have h2 : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  simp only [unitScalar, norm_mul, norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _), abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  field_simp

theorem unitScalar_ne_zero (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : unitScalar v ≠ 0 := by
  intro h
  have := norm_unitScalar v
  rw [h, norm_zero, zero_mul] at this
  exact zero_ne_one this

/-- The unit representative of a non-zero vector: normalised, with its first non-zero coordinate
real and positive. -/
noncomputable def unitRep (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : EuclideanSpace 𝕜 ι :=
  unitScalar v • v.1

theorem norm_unitRep (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : ‖unitRep v‖ = 1 := by
  rw [unitRep, norm_smul, norm_unitScalar]

theorem unitRep_ne_zero (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) : unitRep v ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_unitRep]; exact one_ne_zero)

/-- The unit representative is scale-invariant. -/
theorem unitRep_smul (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) {t : 𝕜} (ht : t ≠ 0) :
    unitRep ⟨t • v.1, smul_ne_zero ht v.2⟩ = unitRep v := by
  have hi := firstIndex_smul v ht
  have hne : ‖v.1 (firstIndex v)‖ ≠ 0 := norm_ne_zero_iff.mpr (apply_firstIndex_ne_zero v)
  have hvn : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  simp only [unitRep, unitScalar, hi, PiLp.smul_apply, smul_eq_mul, map_mul, norm_mul, norm_smul,
    smul_smul, mul_inv, RCLike.ofReal_inv]
  congr 1
  have hconj : starRingEnd 𝕜 t * t = ((‖t‖ : ℝ) : 𝕜) ^ 2 := RCLike.conj_mul t
  have h2 : ((‖t‖ : ℝ) : 𝕜) ≠ 0 := by rw [RCLike.ofReal_ne_zero]; exact htn
  have h3 : ((‖v.1 (firstIndex v)‖ : ℝ) : 𝕜) ≠ 0 := by rw [RCLike.ofReal_ne_zero]; exact hne
  have h4 : ((‖v.1‖ : ℝ) : 𝕜) ≠ 0 := by rw [RCLike.ofReal_ne_zero]; exact hvn
  field_simp
  linear_combination (starRingEnd 𝕜 ((v : EuclideanSpace 𝕜 ι) (firstIndex v))) * hconj

theorem unitRep_scale_invariant (a b : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) (t : 𝕜)
    (h : (a : EuclideanSpace 𝕜 ι) = t • (b : EuclideanSpace 𝕜 ι)) : unitRep a = unitRep b := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact a.2 (by rw [h, zero_smul])
  have : a = ⟨t • b.1, smul_ne_zero ht b.2⟩ := Subtype.ext h
  rw [this]
  exact unitRep_smul b ht

/-- **The unit section of the ray map**: a unit-norm representative of every ray, chosen so that
the first non-zero coordinate is real and positive. -/
noncomputable def unitSection : ℙ 𝕜 (EuclideanSpace 𝕜 ι) → EuclideanSpace 𝕜 ι :=
  Projectivization.lift unitRep unitRep_scale_invariant

theorem unitSection_mk (v : EuclideanSpace 𝕜 ι) (hv : v ≠ 0) :
    unitSection (Projectivization.mk 𝕜 v hv) = unitRep ⟨v, hv⟩ :=
  Projectivization.lift_mk _ _ v hv

theorem norm_unitSection (p : ℙ 𝕜 (EuclideanSpace 𝕜 ι)) : ‖unitSection p‖ = 1 := by
  induction p using Projectivization.ind with
  | h v hv => rw [unitSection_mk]; exact norm_unitRep _

theorem unitSection_ne_zero (p : ℙ 𝕜 (EuclideanSpace 𝕜 ι)) : unitSection p ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_unitSection]; exact one_ne_zero)

/-- The unit section is a section: `mk (unitSection p) = p`. -/
theorem mk_unitSection (p : ℙ 𝕜 (EuclideanSpace 𝕜 ι)) :
    Projectivization.mk 𝕜 (unitSection p) (unitSection_ne_zero p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [(Projectivization.mk_eq_mk_iff' 𝕜 _ _ _ hv)]
    refine ⟨unitScalar ⟨v, hv⟩, ?_⟩
    rw [unitSection_mk]
    rfl

/-! ### Measurability -/

omit [Fintype ι] [LinearOrder ι] in
theorem measurable_coord (i : ι) : Measurable fun v : EuclideanSpace 𝕜 ι => v i :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (ι → 𝕜))

/-- The set of vectors whose first non-zero coordinate is `i` is measurable. -/
theorem measurableSet_firstIndex_eq (i : ι) :
    MeasurableSet {v : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex v = i} := by
  have : {v : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex v = i}
      = Subtype.val ⁻¹' ({v : EuclideanSpace 𝕜 ι | v i ≠ 0} ∩ ⋂ j ∈ {j | j < i}, {v | v j = 0}) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
      firstIndex_eq_iff]
  rw [this]
  refine measurable_subtype_coe (MeasurableSet.inter ?_ (MeasurableSet.biInter (Set.to_countable _)
    fun j _ => ?_))
  · exact (measurable_coord i) (measurableSet_singleton (0 : 𝕜)).compl
  · exact (measurable_coord j) (measurableSet_singleton (0 : 𝕜))

omit [LinearOrder ι] in
/-- The candidate representative for a given first index, as a function on all vectors. -/
noncomputable def candidateRep (i : ι) (v : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 ι :=
  ((starRingEnd 𝕜 (v i) / (‖v i‖ : 𝕜)) * ((‖v‖⁻¹ : ℝ) : 𝕜)) • v

omit [LinearOrder ι] in
theorem measurable_candidateRep (i : ι) : Measurable (candidateRep (𝕜 := 𝕜) i) := by
  have h1 : Measurable fun v : EuclideanSpace 𝕜 ι => starRingEnd 𝕜 (v i) :=
    (RCLike.continuous_conj.measurable).comp (measurable_coord i)
  have h2 : Measurable fun v : EuclideanSpace 𝕜 ι => ((‖v i‖ : ℝ) : 𝕜) :=
    (RCLike.continuous_ofReal.measurable).comp (measurable_norm.comp (measurable_coord i))
  have h3 : Measurable fun v : EuclideanSpace 𝕜 ι => ((‖v‖⁻¹ : ℝ) : 𝕜) :=
    (RCLike.continuous_ofReal.measurable).comp (measurable_inv.comp measurable_norm)
  exact ((h1.div h2).mul h3).smul measurable_id

theorem unitRep_eq_sum (v : {v : EuclideanSpace 𝕜 ι // v ≠ 0}) :
    unitRep v = ∑ i, Set.indicator {w : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex w = i}
      (fun w => candidateRep i w.1) v := by
  rw [Finset.sum_eq_single (firstIndex v)]
  · rw [Set.indicator_of_mem
      (show v ∈ {w : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex w = firstIndex v} from rfl)]
    rfl
  · intro i _ hi
    exact Set.indicator_of_notMem (s := {w : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex w = i})
      (fun h => hi (Eq.symm h)) _
  · intro h; exact absurd (Finset.mem_univ _) h

theorem measurable_unitRep : Measurable (unitRep (𝕜 := 𝕜) (ι := ι)) := by
  have : unitRep (𝕜 := 𝕜) (ι := ι) = fun v => ∑ i, Set.indicator
      {w : {v : EuclideanSpace 𝕜 ι // v ≠ 0} | firstIndex w = i} (fun w => candidateRep i w.1) v :=
    funext unitRep_eq_sum
  rw [this]
  refine Finset.measurable_sum _ fun i _ => Measurable.indicator ?_ (measurableSet_firstIndex_eq i)
  exact (measurable_candidateRep i).comp measurable_subtype_coe

/-- ★ **The unit section is measurable.** -/
theorem measurable_unitSection : Measurable (unitSection (𝕜 := 𝕜) (ι := ι)) :=
  Projectivization.lift_measurable _ _ measurable_unitRep

end Projectivization
