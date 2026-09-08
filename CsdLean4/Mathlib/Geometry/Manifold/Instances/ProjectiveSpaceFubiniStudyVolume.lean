/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUnitaryAction
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceChartCover
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# The volume of the top power of the Fubini–Study form

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Liouville)** — this module uses the *restricted* senses of
"Kahler" and "Liouville"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free).

Milestones **M5** and **M6(a),(c)** of `specs/top-power-scoping.md`, Route U (uniqueness). The
`2n`-form `fsTopForm n` (the `n`-th exterior power of the Fubini–Study form,
`ProjectiveSpaceFubiniStudyForm.lean`) has a measure on `ℂℙⁿ` (`TopFormMeasure.lean`, against
Lebesgue measure on the model `Fin n → ℂ` and the affine chart cover). This module shows it is
`U(n+1)`-invariant and finite, and concludes:

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
* `fsVolumeNormalized n` — the normalised volume, with `fsVolumeNormalized_map_smul` and, once
  the volume is nonzero, `isProbabilityMeasure_fsVolumeNormalized`;
* ★★★ `fsVolumeNormalized_eq_fubiniStudyMeasure` — **the normalised volume of the top power of
  the Fubini–Study form IS the Fubini–Study measure**, `fubiniStudyMeasure p₀`, for every base
  point `p₀` — **under the hypothesis that the volume is nonzero**. This is
  `fubiniStudyMeasure_unique` applied to a `U(n+1)`-invariant probability measure.

## Honest scope

⚠️ **The identity carries a premise: `fsVolume n ≠ 0`.** Discharging it is milestone M6(b) of
the plan — the flat statement that the `n`-th power of the standard symplectic form does not
vanish on the standard basis (a shuffle count), transported to the origin chart by
`fsChartForm_zero` — and it is **not proved here**. Until it is, the theorem says: *if* the
top power has nonzero volume, that volume normalised is the Fubini–Study measure. The premise is
visible in the statement, per the plan's §6 stop condition; nothing is hidden.

⚠️ **No constant.** The total mass `fsVolume n univ` is not computed (M7); the identity is for the
normalised measure.

⚠️ **`n ≥ 1` is not assumed and not needed for the statements**, but for `n = 0` the premise
`fsVolume 0 ≠ 0` is the only content.

References: `specs/top-power-scoping.md` (M5, M6); `Geometry/Manifold/TopFormMeasure.lean`
(`topFormMeasure_map_eq`, `isFiniteMeasure_topFormMeasure`);
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
theorem isFiniteMeasure_fsVolume (n : ℕ) : IsFiniteMeasure (fsVolume n) :=
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
theorem isProbabilityMeasure_fsVolumeNormalized (hne : fsVolume n ≠ 0) :
    IsProbabilityMeasure (fsVolumeNormalized n) := by
  have := isFiniteMeasure_fsVolume n
  refine ⟨?_⟩
  rw [fsVolumeNormalized, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 hne) (measure_ne_top _ _)

/-- ★★★ **The normalised volume of the top power of the Fubini–Study form is the Fubini–Study
measure** — for every base point `p₀`, under the hypothesis that the volume is nonzero
(milestone M6(b), open). `fubiniStudyMeasure_unique` applied to a `U(n+1)`-invariant probability
measure. -/
theorem fsVolumeNormalized_eq_fubiniStudyMeasure (hne : fsVolume n ≠ 0)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    fsVolumeNormalized n = fubiniStudyMeasure p₀ := by
  have := isProbabilityMeasure_fsVolumeNormalized hne
  exact fubiniStudyMeasure_unique p₀ _ fun U => fsVolumeNormalized_map_smul U

end Projectivization
