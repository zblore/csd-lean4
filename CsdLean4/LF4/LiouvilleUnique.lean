/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The sector measure is forced, not chosen

**Category:** 3-CSD. The `(b)` half of the A1 ontic-sector row in `specs/BACKLOG.md` — *"exhibit the
fibre measure as Liouville rather than merely Haar"*.

## The gap this closes

`LF4.KahlerOnticSetup` carries a field `liouvilleMeasure : Measure Sigma` together with
`liouville_isProbability`. The name says **Liouville**; the type says only **probability measure**.
Nothing in the structure forced the sector's measure to be the canonical one, so `kMuL = μ_FS ⊗ Haar`
read as a *choice*, and a reviewer was entitled to ask why that measure rather than another.

★★ `kMuL_unique` answers it: `kMuL p₀` is **the only** probability measure on `Σ = ℂℙ^{N-1} × T²`
invariant under the sector's own symmetry — unitaries on the base, translations on the fibre. The
measure is **forced by the symmetry**, not selected.

## ⚠️ Why this is the right reading of "Liouville"

The textbook definition is the top exterior power of the Kähler form, and it is **not available and
will not be**: `specs/connectivity-manifest.md` L1 records that manifold residual (`dω = 0`, the
top-power volume identity) as blocked on Mathlib, with `Q8` rating the fix XL.

Symmetry-uniqueness is the formalisable content of the same fact — on a homogeneous space the
Liouville measure *is* the invariant one — and it is the reading the corpus already uses for the
base (`invariant_measure_uniqueness_cpn`). This extends that reading to the whole fibred sector.

## The proof, in two independent halves

* **The fibre** (`fst_prod_volume_of_fibreShift_invariant`). For each measurable base set `A`, push
  `μ` restricted to `A ×ˢ univ` forward to the fibre: a finite translation-invariant measure on
  `T²`. ★ Because `T²` is **compact**, `isAddInvariant_eq_smul_of_compactSpace` pins it to a multiple
  of Haar with **no regularity side conditions**. Compactness of the fibre is load-bearing here, not
  decoration — and it is exactly what `TorusFibre`/`GlobalRecordClosure` bought in July, when the
  record layer moved off the non-compact `ℝ` fibre.
* **The base**. The marginal is `U(N)`-invariant, so `invariant_measure_uniqueness_cpn` pins it to a
  multiple of `μ_FS`; total mass one fixes the multiplier.

`Measure.prod_eq` joins them: agreement on rectangles suffices.

## ⚠️ Scope

The measure is forced **given** the symmetry group. This does not derive the group, and Σ remains
the floor — deriving Σ is a non-question (`specs/CSD-CHARTER.md`). Nor does it touch the record
layer's other open item: no `H_int(M)` produces the basins.

Reference: `specs/BACKLOG.md` (the A1 ontic-sector row, item `(b)`);
`specs/connectivity-manifest.md` L1; `specs/CSD-CHARTER.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set Matrix.UnitaryGroup

namespace CSD
namespace LF4

variable {N : ℕ}

/-- Haar measure on the fibre torus, reached through the product form. -/
instance instIsAddHaarMeasureKTorusVolume :
    (volume : Measure KTorus).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- **The fibre shift**: translate the torus coordinate, fix the base ray. -/
noncomputable def fibreShift (v : KTorus) (p : KSigma N) : KSigma N := (p.1, v + p.2)

/-- **The base rotation**: move the ray, fix the fibre. -/
noncomputable def baseRotate (U : Matrix.unitaryGroup (Fin N) ℂ) (p : KSigma N) : KSigma N :=
  (U • p.1, p.2)

@[simp] lemma fibreShift_apply (v : KTorus) (p : KSigma N) :
    fibreShift v p = (p.1, v + p.2) := rfl

@[simp] lemma baseRotate_apply (U : Matrix.unitaryGroup (Fin N) ℂ) (p : KSigma N) :
    baseRotate U p = (U • p.1, p.2) := rfl

lemma measurable_fibreShift (v : KTorus) : Measurable (fibreShift (N := N) v) :=
  measurable_fst.prodMk ((measurable_const_add v).comp measurable_snd)

lemma measurable_baseRotate (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (baseRotate (N := N) U) :=
  ((measurable_const_smul U).comp measurable_fst).prodMk measurable_snd

/-- The fibre shift leaves every base cylinder set where it is. -/
lemma fibreShift_preimage_prod_univ (v : KTorus) (A : Set (CPN N)) :
    fibreShift (N := N) v ⁻¹' (A ×ˢ (univ : Set KTorus)) = A ×ˢ univ := by
  ext p
  simp [fibreShift]

/-! ### The fibre half -/

/-- The fibre marginal of `μ` above a base set `A`. -/
noncomputable def fibreSlice (μ : Measure (KSigma N)) (A : Set (CPN N)) : Measure KTorus :=
  (μ.restrict (A ×ˢ (univ : Set KTorus))).map Prod.snd

lemma fibreSlice_apply (μ : Measure (KSigma N)) {A : Set (CPN N)} {B : Set KTorus}
    (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    fibreSlice μ A B = μ (A ×ˢ B) := by
  rw [fibreSlice, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  tauto

instance instIsFiniteMeasureFibreSlice (μ : Measure (KSigma N)) [IsFiniteMeasure μ]
    (A : Set (CPN N)) : IsFiniteMeasure (fibreSlice μ A) := by
  rw [fibreSlice]
  infer_instance

/-- ★ **The fibre slice is translation-invariant.** The shift moves only the torus coordinate, so it
preserves every base cylinder, and measure preservation on `Σ` descends to the slice. -/
lemma isAddLeftInvariant_fibreSlice (μ : Measure (KSigma N))
    (hT : ∀ v : KTorus, MeasurePreserving (fibreShift (N := N) v) μ μ)
    (A : Set (CPN N)) (hA : MeasurableSet A) :
    (fibreSlice μ A).IsAddLeftInvariant := by
  refine ⟨fun v => ?_⟩
  have hres : (μ.restrict (A ×ˢ (univ : Set KTorus))).map (fibreShift (N := N) v)
      = μ.restrict (A ×ˢ (univ : Set KTorus)) := by
    have hmp := (hT v).restrict_preimage (hA.prod MeasurableSet.univ)
    rw [fibreShift_preimage_prod_univ] at hmp
    exact hmp.map_eq
  calc (fibreSlice μ A).map (fun y => v + y)
      = (μ.restrict (A ×ˢ (univ : Set KTorus))).map (Prod.snd ∘ fibreShift (N := N) v) := by
        rw [fibreSlice, Measure.map_map (measurable_const_add v) measurable_snd]
        rfl
    _ = ((μ.restrict (A ×ˢ (univ : Set KTorus))).map (fibreShift (N := N) v)).map Prod.snd := by
        rw [Measure.map_map measurable_snd (measurable_fibreShift v)]
    _ = fibreSlice μ A := by rw [hres, fibreSlice]

/-- ★★ **Invariance under the fibre shift forces a product with Haar.**

`T²` is compact, so `isAddInvariant_eq_smul_of_compactSpace` applies with no regularity side
conditions, and the scalar is read off at `univ`. -/
theorem fst_prod_volume_of_fibreShift_invariant (μ : Measure (KSigma N)) [IsFiniteMeasure μ]
    (hT : ∀ v : KTorus, MeasurePreserving (fibreShift (N := N) v) μ μ) :
    μ.fst.prod (volume : Measure KTorus) = μ := by
  refine Measure.prod_eq (fun A B hA hB => ?_)
  have := isAddLeftInvariant_fibreSlice μ hT A hA
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, fibreSlice μ A = c • (volume : Measure KTorus) :=
    ⟨_, Measure.isAddInvariant_eq_smul_of_compactSpace (fibreSlice μ A)
      (volume : Measure KTorus)⟩
  have huniv : fibreSlice μ A univ = μ.fst A := by
    rw [fibreSlice_apply μ hA MeasurableSet.univ, Measure.fst_apply hA]
    congr 1
    ext p
    simp [mem_prod]
  have hcval : c = μ.fst A := by
    rw [← huniv, hc]
    simp
  rw [← fibreSlice_apply μ hA hB, hc, hcval]
  simp

/-! ### The base half, and the uniqueness statement -/

/-- The base marginal inherits unitary invariance. -/
lemma measurePreserving_fst_of_baseRotate (μ : Measure (KSigma N))
    (hU : ∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (baseRotate (N := N) U) μ μ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    MeasurePreserving (fun p : CPN N => U • p) μ.fst μ.fst := by
  refine ⟨measurable_const_smul U, ?_⟩
  rw [Measure.fst, Measure.map_map (measurable_const_smul U) measurable_fst]
  have hcomp : (fun p : CPN N => U • p) ∘ Prod.fst
      = Prod.fst ∘ baseRotate (N := N) U := rfl
  rw [hcomp, ← Measure.map_map measurable_fst (measurable_baseRotate U), (hU U).map_eq]

/-- ★★★ **The sector measure is forced by its symmetry.**

`kMuL p₀` is the unique probability measure on `Σ = ℂℙ^{N-1} × T²` invariant under `U(N)` acting on
the base and `T²` acting on the fibre. So the record layer's Liouville measure is not a modelling
choice — it is the only measure compatible with the sector's own symmetry.

⚠️ Forced **given** the group. This does not derive the symmetry, and Σ stays the floor. -/
theorem kMuL_unique [NeZero N] (p₀ : CPN N) (μ : Measure (KSigma N)) [IsProbabilityMeasure μ]
    (hU : ∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (baseRotate (N := N) U) μ μ)
    (hT : ∀ v : KTorus, MeasurePreserving (fibreShift (N := N) v) μ μ) :
    μ = kMuL p₀ := by
  have : IsProbabilityMeasure μ.fst := by
    rw [Measure.fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  obtain ⟨c, hc⟩ := invariant_measure_uniqueness_cpn p₀ (fubiniStudyMeasure p₀)
    (fun U => ⟨measurable_const_smul U, fubiniStudyMeasure_smul_invariant U p₀⟩) μ.fst
    (measurePreserving_fst_of_baseRotate μ hU)
  have hcone : c = 1 := by
    have h := congrArg (fun ν : Measure (CPN N) => ν univ) hc
    simpa using h.symm
  rw [hcone, one_smul] at hc
  rw [← fst_prod_volume_of_fibreShift_invariant μ hT, hc, kMuL]

end LF4
end CSD
