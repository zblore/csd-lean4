/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.BornFibrePartition
public import CsdLean4.LF4.KahlerInstance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# SigmaLayer/CircleFibre: the Born partition on a COMPACT fibre

**Category:** 7-SigmaLayer (the record layer — A1 compactness).

## Why this exists

The corpus had two record-layer constructions, and **compactness and fibre-activity sat in
different ones**:

* `KSigmaRecord.lean` puts a P5 `RecordSemantics` on the **compact** `KSigma = ℂℙⁿ⁻¹ × T²` — but
  its events are `π⁻¹' bornRegion ψ i`, *pulled back from the base*. The torus fibre is **inert**,
  and the construction inherits the preparation-indexed base regions.
* `FibredSigma.lean` has an **active** fibre — it carries the CDF Born cells — but that fibre is
  `ℝ` with Lebesgue restricted to `[0,1)`, which is **not compact**, so it cannot be a Paper C A1
  ontic surface.

Since the general-`N` A7 work concluded that contextuality has to live in the **fibre**
(`specs/sigma-fibre-contextuality.md`), the construction actually needed is
*active-fibre-on-compact-Σ*, and neither module supplied it.

This file supplies the fibre half: **the Born partition, on the circle.**

## What is proved

* `circleCell` — the Born cell as a subset of `AddCircle 1`, defined as the set of circle points
  whose canonical representative in `(0,1]` lies in the CDF interval. Defined as a **preimage**
  (not an image), so measurability is immediate.
* `measurableSet_circleCell`, `volume_circleCell` — each cell is measurable with
  `volume (circleCell r i) = ENNReal.ofReal (r i)`: the same Born weights as the `ℝ` construction,
  now on a compact fibre carrying a probability measure.
* `circleCell_pairwiseDisjoint` — distinct outcomes remain mutually exclusive.
* `volume_circleBornCell` — fed the Born rates, the cell measure is `‖ψ i‖²`.
* `circleFibre_isProbabilityMeasure`, `circleFibre_compactSpace` — the fibre is compact and its
  Haar measure is a probability measure, which is what `ℝ` could not give.

## Scope — what this does and does not settle

It gives a **compact fibre carrying the active Born partition**, which is the piece A1 was missing.
It does **not** by itself make the fibred `Σ` a Paper C A1 ontic surface, and the fibre measure is
not *shown* to be a Liouville measure, only exhibited as Haar. The remaining record-layer modules
(`FibreRecord`, `Measurement`, `RecordLayerClosure`) still run on the `ℝ` fibre and would need
re-plumbing onto this one; that is mechanical but not done here.

⚠️ **A SINGLE CIRCLE CANNOT COMPLETE A1 — a dimension-parity fact, corrected 2026-07-30.** An earlier
version of this docstring said the missing Kähler structure was blocked on Mathlib's absent manifold
exterior calculus. **That was a misdiagnosis.** `ℂℙⁿ⁻¹` has real dimension `2n-2`, so
`ℂℙⁿ⁻¹ × AddCircle 1` has real dimension `2n-1` — **odd**. A symplectic form needs `ωᵏ` as a volume
form, so no odd-dimensional manifold carries one, hence none carries a Kähler structure. The A1
obstruction here is therefore **not** missing tooling: it would survive any amount of Mathlib API.
(The same parity objection applies retroactively to `FibredSigma`'s `ℂℙⁿ⁻¹ × ℝ`, also `2n-1`.)

**The fix is already in the corpus and is cheap.** `LF4/KahlerInstance.lean` has
`KTorus = AddCircle 1 × AddCircle 1` and `KSigma N = CPN N × KTorus`, of real dimension `2n` —
**even**, and a product of Kähler manifolds. The intended successor construction puts *this* file's
`circleCell` on the **first** torus coordinate, leaving the second as its symplectic partner. Every
theorem below is stated about one `AddCircle 1` and transports to that factor; what is missing is
the product-measure step, not new fibre mathematics. See `specs/BACKLOG.md` (the ★★ row).

## References

`SigmaLayer/BornFibrePartition.lean` (`cdfCell`, `loSum`, `bornRate` — the `ℝ` construction);
`SigmaLayer/FibredSigma.lean` (the active-fibre Σ); `SigmaLayer/KSigmaRecord.lean` (the compact but
inert-fibre Σ); `LF4/KahlerInstance.lean` (`KTorus = AddCircle 1 × AddCircle 1`);
`specs/sigma-fibre-contextuality.md`; `specs/BACKLOG.md` (the ★★ fibre/A1 row).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {n : ℕ}

/-! ### The compact fibre -/

/-- The **compact record fibre**: the unit circle, the same factor the corpus's `KTorus` is built
from. Replaces the non-compact `ℝ` of `FibredSigma`. -/
abbrev CircleFibre : Type := AddCircle (1 : ℝ)

instance circleFibre_factPos : Fact ((0:ℝ) < 1) := ⟨zero_lt_one⟩

instance circleFibre_compactSpace : CompactSpace CircleFibre :=
  AddCircle.compactSpace (p := (1:ℝ))

/-- The fibre's Haar measure is a **probability** measure — the property the restricted Lebesgue
measure on `ℝ` only had by fiat. -/
theorem circleFibre_volume_univ : (volume : Measure CircleFibre) univ = 1 :=
  UnitAddCircle.measure_univ

instance circleFibre_isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure CircleFibre) :=
  ⟨circleFibre_volume_univ⟩

/-! ### The Born partition, transported to the circle -/

/-- The canonical representative of a circle point in `(0, 1]`. -/
noncomputable def rep (x : CircleFibre) : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 x : ℝ)

theorem measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

/-- The **Born cell on the circle**: the points whose canonical representative lies in the CDF
interval. A *preimage*, so measurability is immediate — unlike the image of `cdfCell`. -/
noncomputable def circleCell (r : Fin n → ℝ) (i : Fin n) : Set CircleFibre :=
  rep ⁻¹' Ioc (loSum r i) (loSum r i + r i)

theorem measurableSet_circleCell (r : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (circleCell r i) :=
  measurable_rep measurableSet_Ioc

/-- **Distinct outcomes stay mutually exclusive on the circle.** Inherited from the disjointness of
the underlying CDF intervals, since each cell is the `rep`-preimage of its own interval. -/
theorem circleCell_pairwiseDisjoint (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Pairwise (Function.onFun Disjoint (circleCell r)) := by
  -- The cells are `rep`-preimages of the CDF intervals, which are ordered by `loSum`.
  have key : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → Disjoint (circleCell r i) (circleCell r j) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have h1 : rep x ≤ loSum r i + r i := hxi.2
    have h2 : loSum r j < rep x := hxj.1
    have h3 : loSum r i + r i ≤ loSum r j := loSum_add_le_loSum r hr hij
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ### The Born weights survive the transport -/

/-- **The circle cell carries exactly the Born weight `rᵢ`.** The whole point of the swap: moving
to a compact fibre changes nothing about the outcome probabilities. Requires the rates to be a
sub-probability vector, so the cells fit inside one turn of the circle. -/
theorem volume_circleCell (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∀ i : Fin n, loSum r i + r i ≤ 1) (i : Fin n) :
    (volume : Measure CircleFibre) (circleCell r i) = ENNReal.ofReal (r i) := by
  have hlo : 0 ≤ loSum r i := Finset.sum_nonneg fun j _ => hr j
  have hS : MeasurableSet (Subtype.val ⁻¹' Ioc (loSum r i) (loSum r i + r i) :
      Set (Ioc (0:ℝ) ((0:ℝ) + 1))) := measurable_subtype_coe measurableSet_Ioc
  have hpre : circleCell r i
      = (AddCircle.equivIoc (1:ℝ) 0) ⁻¹'
        (Subtype.val ⁻¹' Ioc (loSum r i) (loSum r i + r i)) := rfl
  rw [hpre, (AddCircle.measurePreserving_equivIoc (T := (1:ℝ)) (a := 0)).measure_preimage
    hS.nullMeasurableSet,
    Measure.comap_apply _ Subtype.val_injective
      (fun s hs => measurableSet_Ioc.subtype_image hs) _ hS]
  -- The image of the preimage is the interval cut down to one turn — which changes nothing.
  have himg : (Subtype.val '' (Subtype.val ⁻¹' Ioc (loSum r i) (loSum r i + r i) :
      Set (Ioc (0:ℝ) ((0:ℝ) + 1)))) = Ioc (loSum r i) (loSum r i + r i) := by
    rw [Subtype.image_preimage_coe]
    apply Set.inter_eq_self_of_subset_right
    intro x hx
    exact ⟨lt_of_le_of_lt hlo hx.1, le_trans hx.2 (by simpa using hsum i)⟩
  rw [himg, Real.volume_Ioc]
  congr 1
  ring

/-- **Born rates on the compact fibre.** For a unit state the circle cell for outcome `i` has
measure `‖ψ i‖²` — the same Born weight the `ℝ` fibre gave, now on a compact space with a genuine
Haar probability measure. -/
theorem volume_circleBornCell (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    (volume : Measure CircleFibre) (circleCell (bornRate ψ) i) = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  refine volume_circleCell _ (bornRate_nonneg ψ) (fun j => ?_) i
  -- `loSum r j + r j` sums `r` over `{k < j} ∪ {j} ⊆ univ`, so it is at most the total, which is 1.
  classical
  have hnot : j ∉ Finset.univ.filter (fun k : Fin n => (k : ℕ) < (j : ℕ)) := by simp
  have hins : loSum (bornRate ψ) j + bornRate ψ j
      = ∑ k ∈ insert j (Finset.univ.filter (fun k : Fin n => (k : ℕ) < (j : ℕ))), bornRate ψ k := by
    rw [Finset.sum_insert hnot, loSum]; ring
  have hle : ∑ k ∈ insert j (Finset.univ.filter (fun k : Fin n => (k : ℕ) < (j : ℕ))), bornRate ψ k
      ≤ ∑ k, bornRate ψ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => bornRate_nonneg ψ k)
  rw [hins]
  exact le_trans hle (le_of_eq (sum_bornRate_unit ψ hψ))

end CSD.RecordLayer
