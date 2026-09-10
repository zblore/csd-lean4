/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUnitaryAction
public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.WedgeShuffle
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceChartCover
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# The volume of the top power of the Fubini–Study form

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Liouville)** — this module uses the *restricted* senses of
"Kahler" and "Liouville"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free).

Milestones **M5** and **M6** of `specs/top-power-scoping.md`, Route U (uniqueness). The
`2n`-form `fsTopForm n` (the `n`-th exterior power of the Fubini–Study form,
`ProjectiveSpaceFubiniStudyForm.lean`) has a measure on `ℂℙⁿ` (`TopFormMeasure.lean`, against
Lebesgue measure on the model `Fin n → ℂ` and the affine chart cover). This module shows it is
`U(n+1)`-invariant, finite and nonzero, and concludes:

* `stdBasis n` — the standard real basis of `Fin n → ℂ`, indexed by `Fin (2n)`;
* `fsVolume n` — **the volume measure of the top power of the Fubini–Study form**;
* `chartAt_smul_comp_symm`, `smul_symm_mem_source_iff` — the chart expression of `U • ·` is
  `uTrans U (idx x₀) (idx z)`, defined where the action lands in the target chart;
* `localRep_fsSection'`, `localRep_fsTopForm` — the local representative of the top power in
  every chart is the flat power of the model form;
* ★★ `fsVolume_map_smul` — **`fsVolume n` is invariant under the unitary group**
  (`topFormMeasure_map_eq` with the chart invariance `fsModelForm_uTrans` lifted to the top
  power by `wedgePow_compContinuousLinearMap`);
* ★ `isFiniteMeasure_fsVolume` — it is finite (`isFiniteMeasure_topFormMeasure`: locally finite
  on a compact manifold);
* `fsVolumeNormalized n` — the normalised volume, with `fsVolumeNormalized_map_smul`;
  `isProbabilityMeasure_fsVolumeNormalized_of_ne_zero` and
  `fsVolumeNormalized_eq_fubiniStudyMeasure_of_ne_zero` are the M6(c) conclusions **under the
  premise `fsVolume n ≠ 0`** (`fubiniStudyMeasure_unique` applied to a `U(n+1)`-invariant
  probability measure);
* **M6(b), the flat count** — `stdForm n` (the standard symplectic form on the model,
  `fundamentalFormAlt` through `toLpCLM`; `fsModelForm_zero`: the model form at the origin is
  `-4 • stdForm n`), `pairFamily a` (the `k` standard pairs `(e_{a i}, i e_{a i})`),
  `isPairFamily_pairFamily` (they are a pair family for `stdForm`, `WedgeShuffle.lean`), and
  ★★ `wedgePow_stdForm_pairFamily` — **the `k`-th power of the standard symplectic form on `k`
  distinct standard pairs is `k!`**, by induction on `k` through the shuffle sum
  `wedge_mul_apply_pairs`: each of the `k + 1` surviving classes removes one pair
  (`removePair`) and contributes `k!`. On the standard basis (`stdBasis_eq_pairFamily`),
  ★★ `wedgePow_fsModelForm_zero_stdBasis`: the coefficient of the top power at the origin is
  `(-4)ⁿ · n!`, in particular nonzero;
* ★★ `fsVolume_ne_zero` — **the volume is nonzero** (`topFormMeasure_ne_zero_of_localRep_ne_zero`
  at the origin of the chart at `origin 0`), so `isProbabilityMeasure_fsVolumeNormalized` holds
  unconditionally;
* ★★★ `fsVolumeNormalized_eq_fubiniStudyMeasure` — **the normalised volume of the top power of
  the Fubini–Study form IS the Fubini–Study measure**, `fubiniStudyMeasure p₀`, for every base
  point `p₀`. No premise.

## Honest scope

⚠️ **No constant here.** The identity of this module is for the normalised measure; `(-4)ⁿ n!` is
the coefficient at one point, not the total mass. The mass, `(4π)ⁿ`, and the identity with its
constant are `ProjectiveSpaceFubiniStudyMass.lean` (M7).

⚠️ **`n ≥ 1` is not assumed and not needed**: for `n = 0` the manifold is a point, the top power
is the constant `0`-form `1` (`wedgePow_stdForm_pairFamily` at `k = 0`), and every statement holds.

⚠️ **The count is for the standard form on the standard pairs only**; nothing is said about the
top power of `stdForm` on other families, nor about `fsModelForm w` away from `w = 0` (the
measure argument needs one point).

References: `specs/top-power-scoping.md` (M5, M6); `Geometry/Manifold/TopFormMeasure.lean`
(`topFormMeasure_map_eq`, `isFiniteMeasure_topFormMeasure`,
`topFormMeasure_ne_zero_of_localRep_ne_zero`);
`Analysis/Normed/Module/Alternating/WedgeShuffle.lean` (`wedge_mul_apply_pairs`);
`Geometry/Manifold/Instances/ProjectiveSpaceUnitaryAction.lean` (`fsModelForm_uTrans`);
`Geometry/Manifold/WedgeForm.lean` (`localRep_wedgePow`, `wedgePow_compContinuousLinearMap`);
`LinearAlgebra/Projectivization/FubiniStudyUnique.lean` (★★ `fubiniStudyMeasure_unique`);
`specs/TERMS.md` (Liouville); `specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology Set MeasureTheory
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization ENNReal

noncomputable section

namespace Projectivization

open Kahler Matrix.UnitaryGroup DifferentialForm

variable {n : ℕ}

/-- The standard real basis of the model `Fin n → ℂ`, indexed by `Fin (2n)`. -/
def stdBasis (n : ℕ) : Module.Basis (Fin (2 * n)) ℝ (Fin n → ℂ) :=
  (Pi.basis fun _ : Fin n => Complex.basisOneI).reindex
    ((Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans (finProdFinEquiv.trans (finCongr (by ring))))

/-- **The volume of the top power of the Fubini–Study form**: the measure of the `2n`-form
`fsTopForm n` on `ℂℙⁿ`, against Lebesgue measure on the model and the affine chart cover. -/
def fsVolume (n : ℕ) : Measure (ℙ ℂ (Ambient n)) :=
  topFormMeasure volume (stdBasis n) (fun x => fsTopForm n x) (affineChartCover n)

/-! ### The action in charts -/

/-- The chart expression of the unitary action, from the chart at `x₀` to the chart at `z`, is
`uTrans U (idx x₀) (idx z)`. -/
theorem chartAt_smul_comp_symm (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (x₀ z : ℙ ℂ (Ambient n)) :
    (chartAt (Fin n → ℂ) z ∘ (fun p => U • p) ∘ (chartAt (Fin n → ℂ) x₀).symm)
      = uTrans U (idx x₀) (idx z) := by
  funext w
  show chartFun (idx z) (U • chartInv (idx x₀) w) = _
  exact chartFun_smul_chartInv U _ _ w

theorem smul_symm_mem_source_iff (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (x₀ z : ℙ ℂ (Ambient n)) (w : Fin n → ℂ) :
    U • (chartAt (Fin n → ℂ) x₀).symm w ∈ (chartAt (Fin n → ℂ) z).source
      ↔ toEuclideanLinearEquiv U (insertOne (idx x₀) w) (idx z) ≠ 0 := by
  show U • chartInv (idx x₀) w ∈ chartSource (idx z) ↔ _
  rw [smul_chartInv]
  exact mem_chartSource_mk _ _ _

/-! ### Local representatives of the form and its top power -/

/-- The local representative of the Fubini–Study section, in `localRep` form. -/
theorem localRep_fsSection' (x₀ : ℙ ℂ (Ambient n)) (w : Fin n → ℂ) :
    localRep fsSection x₀ w = fsModelForm w := by
  have h := localRep_fsSection x₀ ((chartAt (Fin n → ℂ) x₀).symm w)
    ((chartAt (Fin n → ℂ) x₀).map_target (Set.mem_univ w))
  have hw : chartFun (idx x₀) ((chartAt (Fin n → ℂ) x₀).symm w) = w :=
    (chartAt (Fin n → ℂ) x₀).right_inv (Set.mem_univ w)
  rw [hw] at h
  exact h

/-- The local representative of the top power is the flat power of the model form. -/
theorem localRep_fsTopForm (x₀ : ℙ ℂ (Ambient n)) (w : Fin n → ℂ) :
    localRep (fun x => fsTopForm n x) x₀ w
      = ContinuousAlternatingMap.wedgePow (fsModelForm w) n := by
  rw [fsTopForm, localRep_wedgePow (fsForm (n := n)) x₀ (Set.mem_univ w) n]
  congr 1
  exact localRep_fsSection' x₀ w

/-! ### Invariance and finiteness -/

/-- ★★ **The Fubini–Study volume is invariant under the unitary group.** -/
theorem fsVolume_map_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    Measure.map (fun p : ℙ ℂ (Ambient n) => U • p) (fsVolume n) = fsVolume n := by
  have h := topFormMeasure_map_eq volume (stdBasis n) (fun x => fsTopForm n x) (affineChartCover n)
    (Homeomorph.smul U) ?_ ?_
  · exact h
  · intro x₀ z w _ hmem
    rw [show (⇑(Homeomorph.smul U) : ℙ ℂ (Ambient n) → ℙ ℂ (Ambient n)) = fun p => U • p from rfl,
      chartAt_smul_comp_symm]
    have hne : toEuclideanLinearEquiv U (insertOne (idx x₀) w) (idx z) ≠ 0 :=
      (smul_symm_mem_source_iff U x₀ z w).1 hmem
    exact (((contDiffOn_uTrans U (idx x₀) (idx z)).contDiffAt
      ((isOpen_uDomain U (idx x₀) (idx z)).mem_nhds hne)).restrict_scalars ℝ).of_le le_top
  · intro x₀ z w _ hmem
    rw [show (⇑(Homeomorph.smul U) : ℙ ℂ (Ambient n) → ℙ ℂ (Ambient n)) = fun p => U • p from rfl,
      chartAt_smul_comp_symm]
    have hne : toEuclideanLinearEquiv U (insertOne (idx x₀) w) (idx z) ≠ 0 :=
      (smul_symm_mem_source_iff U x₀ z w).1 hmem
    rw [localRep_fsTopForm, localRep_fsTopForm,
      ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, fsModelForm_uTrans U _ _ hne]

/-- ★ The Fubini–Study volume is a finite measure (`ℂℙⁿ` is compact and the density is
continuous). -/
instance isFiniteMeasure_fsVolume (n : ℕ) : IsFiniteMeasure (fsVolume n) :=
  isFiniteMeasure_topFormMeasure volume (stdBasis n) _ (fsTopForm n).contMDiff_toFun
    (affineChartCover n)

/-! ### The normalised volume and the identity -/

/-- The Fubini–Study volume, normalised to total mass one. -/
def fsVolumeNormalized (n : ℕ) : Measure (ℙ ℂ (Ambient n)) :=
  (fsVolume n Set.univ)⁻¹ • fsVolume n

theorem fsVolumeNormalized_map_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    Measure.map (fun p : ℙ ℂ (Ambient n) => U • p) (fsVolumeNormalized n)
      = fsVolumeNormalized n := by
  rw [fsVolumeNormalized, Measure.map_smul, fsVolume_map_smul]

/-- If the volume is nonzero, its normalisation is a probability measure. -/
theorem isProbabilityMeasure_fsVolumeNormalized_of_ne_zero (hne : fsVolume n ≠ 0) :
    IsProbabilityMeasure (fsVolumeNormalized n) := by
  have := isFiniteMeasure_fsVolume n
  refine ⟨?_⟩
  rw [fsVolumeNormalized, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 hne) (measure_ne_top _ _)

/-- ★★ The identity under the premise that the volume is nonzero: `fubiniStudyMeasure_unique`
applied to a `U(n+1)`-invariant probability measure. The premise is discharged below
(`fsVolume_ne_zero`). -/
theorem fsVolumeNormalized_eq_fubiniStudyMeasure_of_ne_zero (hne : fsVolume n ≠ 0)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    fsVolumeNormalized n = fubiniStudyMeasure p₀ := by
  have := isProbabilityMeasure_fsVolumeNormalized_of_ne_zero hne
  exact fubiniStudyMeasure_unique p₀ _ fun U => fsVolumeNormalized_map_smul U

/-! ### The flat count: the top power of the model form at the origin (M6(b)) -/

section FlatCount

open ContinuousAlternatingMap (slotPair slotMem pairRep pairSign IsPairFamily pairRep_inl
  wedge_mul_apply_pairs)

/-- The standard symplectic form on the model `Fin n → ℂ`: the flat fundamental form
`Kahler.fundamentalFormAlt` read through `toLpCLM`. -/
def stdForm (n : ℕ) : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (fundamentalFormAlt : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ).compContinuousLinearMap toLpCLM

/-- At the origin the model form is `-4` times the standard form (`fsChartForm_zero`). -/
theorem fsModelForm_zero : fsModelForm (n := n) 0 = (-4 : ℝ) • stdForm n := by
  ext v
  simp [fsModelForm, stdForm, fsChartForm_zero]

/-- The standard form on two coordinate vectors: `Im (conj x · y)` on the same coordinate, `0`
on different ones. -/
theorem stdForm_single (j j' : Fin n) (x y : ℂ) :
    stdForm n ![Pi.single j x, Pi.single j' y]
      = if j = j' then ((starRingEnd ℂ) x * y).im else 0 := by
  simp only [stdForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    fundamentalFormAlt_apply, fundamentalForm, Function.comp_def, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [show toLpCLM (Pi.single j x) = EuclideanSpace.single j x from rfl,
    show toLpCLM (Pi.single j' y) = EuclideanSpace.single j' y from rfl,
    EuclideanSpace.inner_single_left]
  simp only [PiLp.single_apply]
  split_ifs with h
  · rfl
  · simp

/-- On the pair `(1, i)` the imaginary part of `conj · × ·` is `pairSign`. -/
theorem im_conj_mul_pairs (a b : Fin 2) :
    ((starRingEnd ℂ) (![1, Complex.I] a) * ![1, Complex.I] b).im = pairSign a b := by
  fin_cases a <;> fin_cases b <;> simp [pairSign, Complex.conj_I]

/-- The pair a slot of `Fin (2k)` belongs to. -/
def pairIdx {k : ℕ} (p : Fin (2 * k)) : Fin k := ⟨p / 2, by omega⟩

/-- Which member of its pair a slot of `Fin (2k)` is. -/
def memIdx {k : ℕ} (p : Fin (2 * k)) : Fin 2 := ⟨p % 2, by omega⟩

/-- The family of `k` standard pairs `(e_{a i}, i • e_{a i})`, in order. -/
def pairFamily {k : ℕ} (a : Fin k → Fin n) : Fin (2 * k) → (Fin n → ℂ) :=
  fun p => Pi.single (a (pairIdx p)) (![1, Complex.I] (memIdx p))

theorem coe_powEquiv_inl {k : ℕ} (p : Fin (2 * k)) :
    ((DifferentialForm.powEquiv k (Sum.inl p) : Fin (2 * (k + 1))) : ℕ) = p := rfl

theorem coe_powEquiv_inr {k : ℕ} (b : Fin 2) :
    ((DifferentialForm.powEquiv k (Sum.inr b) : Fin (2 * (k + 1))) : ℕ) = 2 * k + b := rfl

theorem pairIdx_powEquiv_inl {k : ℕ} (p : Fin (2 * k)) :
    pairIdx (DifferentialForm.powEquiv k (Sum.inl p)) = slotPair (Sum.inl p) :=
  Fin.ext (by simp [pairIdx, slotPair, coe_powEquiv_inl])

theorem memIdx_powEquiv_inl {k : ℕ} (p : Fin (2 * k)) :
    memIdx (DifferentialForm.powEquiv k (Sum.inl p)) = slotMem (Sum.inl p) :=
  Fin.ext (by simp [memIdx, slotMem, coe_powEquiv_inl])

theorem pairIdx_powEquiv_inr {k : ℕ} (b : Fin 2) :
    pairIdx (DifferentialForm.powEquiv k (Sum.inr b)) = slotPair (Sum.inr b) :=
  Fin.ext (by simp [pairIdx, slotPair, coe_powEquiv_inr]; omega)

theorem memIdx_powEquiv_inr {k : ℕ} (b : Fin 2) :
    memIdx (DifferentialForm.powEquiv k (Sum.inr b)) = slotMem (k := k) (Sum.inr b) :=
  Fin.ext (by simp [memIdx, slotMem, coe_powEquiv_inr]; omega)

/-- Through `powEquiv`, the pair family reads off `slotPair` and `slotMem`. -/
theorem pairFamily_powEquiv {k : ℕ} (a : Fin (k + 1) → Fin n) (x : Fin (2 * k) ⊕ Fin 2) :
    pairFamily a (DifferentialForm.powEquiv k x)
      = Pi.single (a (slotPair x)) (![1, Complex.I] (slotMem x)) := by
  rcases x with p | b
  · rw [pairFamily, pairIdx_powEquiv_inl, memIdx_powEquiv_inl]
  · rw [pairFamily, pairIdx_powEquiv_inr, memIdx_powEquiv_inr]

/-- The family the recursion evaluates on is a pair family for the standard form. -/
theorem isPairFamily_pairFamily {k : ℕ} (a : Fin (k + 1) → Fin n) (ha : Function.Injective a) :
    IsPairFamily (stdForm n) (fun x => pairFamily a (DifferentialForm.powEquiv k x)) := by
  intro x y
  simp only [pairFamily_powEquiv, stdForm_single, ha.eq_iff, im_conj_mul_pairs]

/-- The index map with pair `j` replaced by the last pair. -/
def removePair {k : ℕ} (a : Fin (k + 1) → Fin n) (j : Fin (k + 1)) : Fin k → Fin n :=
  fun i => if Fin.castSucc i = j then a (Fin.last k) else a (Fin.castSucc i)

theorem removePair_injective {k : ℕ} {a : Fin (k + 1) → Fin n} (ha : Function.Injective a)
    (j : Fin (k + 1)) : Function.Injective (removePair a j) := by
  intro i i' h
  simp only [removePair] at h
  split_ifs at h with h1 h2 h2
  · exact Fin.castSucc_injective k (h1.trans h2.symm)
  · exact absurd (ha h) (Fin.castSucc_lt_last i').ne'
  · exact absurd (ha h) (Fin.castSucc_lt_last i).ne
  · exact Fin.castSucc_injective k (ha h)

/-- The two-transposition representative `pairRep j` moves pair `j` into the `β`-slots and
leaves the pair family with pair `j` replaced by the last one. -/
theorem pairFamily_pairRep {k : ℕ} (a : Fin (k + 1) → Fin n) (j : Fin (k + 1))
    (i : Fin (2 * k)) :
    pairFamily a (DifferentialForm.powEquiv k (pairRep j (Sum.inl i)))
      = pairFamily (removePair a j) i := by
  have hc : Fin.castSucc (pairIdx i) = slotPair (Sum.inl i) := Fin.ext rfl
  have hm : memIdx i = slotMem (Sum.inl i) := Fin.ext rfl
  rw [pairRep_inl]
  split_ifs with h
  · rw [pairFamily_powEquiv]
    simp only [pairFamily, removePair, hc, h, if_true, hm]
    rfl
  · rw [pairFamily_powEquiv]
    simp only [pairFamily, removePair, hc, h, if_false, hm]

/-- ★★ **The count.** The `k`-th power of the standard symplectic form on `k` distinct standard
pairs is `k!`: through the shuffle sum, each of the `k + 1` surviving classes removes one pair
and contributes `k!` by induction. -/
theorem wedgePow_stdForm_pairFamily :
    ∀ (k : ℕ) (a : Fin k → Fin n), Function.Injective a →
      ContinuousAlternatingMap.wedgePow (stdForm n) k (pairFamily a) = (k.factorial : ℝ)
  | 0, _, _ => by simp [ContinuousAlternatingMap.wedgePow]
  | k + 1, a, ha => by
    simp only [ContinuousAlternatingMap.wedgePow]
    rw [ContinuousAlternatingMap.domDomCongr_apply,
      wedge_mul_apply_pairs (isPairFamily_pairFamily a ha)]
    have hterm : ∀ j : Fin (k + 1),
        ContinuousAlternatingMap.wedgePow (stdForm n) k
          (fun i => pairFamily a (DifferentialForm.powEquiv k (pairRep j (Sum.inl i))))
          = (k.factorial : ℝ) := fun j => by
      rw [← wedgePow_stdForm_pairFamily k (removePair a j) (removePair_injective ha j)]
      congr 1
      funext i
      exact pairFamily_pairRep a j i
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.factorial_succ]
    push_cast
    ring

/-- The standard basis is the pair family of the identity. -/
theorem stdBasis_eq_pairFamily (p : Fin (2 * n)) :
    stdBasis n p = pairFamily (id : Fin n → Fin n) p := by
  simp only [stdBasis, Module.Basis.reindex_apply, Pi.basis_apply, Equiv.symm_trans_apply,
    finCongr_symm, finCongr_apply, finProdFinEquiv_symm_apply, Equiv.sigmaEquivProd_symm_apply,
    Complex.coe_basisOneI, pairFamily, pairIdx, memIdx, id]
  congr 1

/-- ★★ **The coefficient of the top power at the origin, on the standard basis, is
`(-4)ⁿ · n!`.** -/
theorem wedgePow_fsModelForm_zero_stdBasis :
    ContinuousAlternatingMap.wedgePow (fsModelForm (n := n) 0) n (stdBasis n)
      = (-4 : ℝ) ^ n * n.factorial := by
  rw [fsModelForm_zero, ContinuousAlternatingMap.wedgePow_smul, ContinuousAlternatingMap.smul_apply,
    show ⇑(stdBasis n) = pairFamily (id : Fin n → Fin n) from funext stdBasis_eq_pairFamily,
    wedgePow_stdForm_pairFamily n id Function.injective_id, smul_eq_mul]

theorem wedgePow_fsModelForm_zero_stdBasis_ne_zero :
    ContinuousAlternatingMap.wedgePow (fsModelForm (n := n) 0) n (stdBasis n) ≠ 0 := by
  rw [wedgePow_fsModelForm_zero_stdBasis]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)

end FlatCount

/-! ### Non-vanishing, and the identity -/

/-- ★★ **The Fubini–Study volume is nonzero**: the coefficient of the top power against the
standard basis at the origin of the chart at `origin 0` is `(-4)ⁿ · n!`. -/
theorem fsVolume_ne_zero (n : ℕ) : fsVolume n ≠ 0 :=
  topFormMeasure_ne_zero_of_localRep_ne_zero volume (stdBasis n) (fun x => fsTopForm n x)
    (fsTopForm n).contMDiff_toFun (affineChartCover n) (origin 0) (Set.mem_univ (0 : Fin n → ℂ))
    (by rw [localRep_fsTopForm]; exact wedgePow_fsModelForm_zero_stdBasis_ne_zero)

/-- The normalised Fubini–Study volume is a probability measure. -/
instance isProbabilityMeasure_fsVolumeNormalized (n : ℕ) :
    IsProbabilityMeasure (fsVolumeNormalized n) :=
  isProbabilityMeasure_fsVolumeNormalized_of_ne_zero (fsVolume_ne_zero n)

/-- ★★★ **The normalised volume of the top power of the Fubini–Study form is the Fubini–Study
measure**, for every base point `p₀`. -/
theorem fsVolumeNormalized_eq_fubiniStudyMeasure (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    fsVolumeNormalized n = fubiniStudyMeasure p₀ :=
  fsVolumeNormalized_eq_fubiniStudyMeasure_of_ne_zero (fsVolume_ne_zero n) p₀

end Projectivization
