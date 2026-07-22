/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.MeasureBridge

/-!
# LF2 Projective Weights

**Category:** 3-Local (LF2 measurable partitions on the projective target and their weight normalisation).

Spec §4:

- `MeasurablePartition` — measurable partition of `P` up to null sets
  (spec §4.1).
- `projectiveWeight` — the weight of an outcome region under the pushforward
  of a preparation measure (spec §4.2).
- `weights_sum_eq_one` — normalisation (spec §4.3).

The partition is stated relative to the pushforward measure `π*μprep`, not
`μFS` directly. This is cleaner than the spec's `μFS`-relative formulation:
via the measure bridge, the two agree, but this form lets `weights_sum_eq_one`
be proved without dragging `μFS` through.
-/

open MeasureTheory Set Function

namespace CSD
namespace LF2

/-- A finite measurable partition of `P` up to `μ`-null sets: measurable
    parts, pairwise intersections of `μ`-measure zero, and complement of the
    union of `μ`-measure zero. -/
structure MeasurablePartition (P : Type*) [MeasurableSpace P]
    (μ : Measure P) (n : ℕ) where
  /-- The parts, indexed by `Fin n`. -/
  parts         : Fin n → Set P
  /-- Each part is measurable. -/
  measurable    : ∀ i, MeasurableSet (parts i)
  /-- Pairwise intersections are null. -/
  pairwise_null : ∀ i j, i ≠ j → μ (parts i ∩ parts j) = 0
  /-- The complement of the union is null. -/
  cover_null    : μ ((⋃ i, parts i)ᶜ) = 0

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- Projective weight of an outcome region `O ⊆ P` under the pushforward of
    a preparation measure. -/
noncomputable def projectiveWeight
    (D : SectorData SigmaSpace P G)
    (μprep : Measure SigmaSpace)
    (O : Set P) : ENNReal :=
  (Measure.map D.π μprep) O

/-- Unfolding lemma: `projectiveWeight` is the pushforward measure of the
    region. Not `@[simp]` — leaving `projectiveWeight` as a named
    abstraction makes downstream proofs and theorem statements
    readable; callers `unfold projectiveWeight` (or rewrite with this
    lemma explicitly) when they need to expose the underlying
    pushforward. -/
lemma projectiveWeight_def
    (D : SectorData SigmaSpace P G) (μprep : Measure SigmaSpace) (O : Set P) :
    projectiveWeight D μprep O = (Measure.map D.π μprep) O := rfl

/-- **Spec §4.3 normalisation.** For a probability preparation measure and a
    measurable partition of `P` up to `π*μprep`-null sets, the weights sum
    to one. -/
theorem weights_sum_eq_one
    (D : SectorData SigmaSpace P G) {n : ℕ}
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (π_part : MeasurablePartition P (Measure.map D.π μprep) n) :
    ∑ i : Fin n, projectiveWeight D μprep (π_part.parts i) = 1 := by
  haveI : IsProbabilityMeasure (Measure.map D.π μprep) :=
    Measure.isProbabilityMeasure_map D.measurable_π.aemeasurable
  have hpw : Pairwise (AEDisjoint (Measure.map D.π μprep) on π_part.parts) :=
    fun i j hij => π_part.pairwise_null i j hij
  have hnm : ∀ i, NullMeasurableSet (π_part.parts i) (Measure.map D.π μprep) :=
    fun i => (π_part.measurable i).nullMeasurableSet
  have hunion :
      (Measure.map D.π μprep) (⋃ i, π_part.parts i)
        = ∑' i, (Measure.map D.π μprep) (π_part.parts i) :=
    measure_iUnion₀ hpw hnm
  have hsum :
      ∑' i : Fin n, (Measure.map D.π μprep) (π_part.parts i)
        = ∑ i, (Measure.map D.π μprep) (π_part.parts i) :=
    tsum_fintype _
  have hunion_meas : MeasurableSet (⋃ i, π_part.parts i) :=
    MeasurableSet.iUnion fun i => π_part.measurable i
  have hunion_eq_one : (Measure.map D.π μprep) (⋃ i, π_part.parts i) = 1 := by
    have h := measure_add_measure_compl (μ := Measure.map D.π μprep) hunion_meas
    rw [π_part.cover_null, add_zero, measure_univ] at h
    exact h
  calc ∑ i, projectiveWeight D μprep (π_part.parts i)
      = ∑ i, (Measure.map D.π μprep) (π_part.parts i) := rfl
    _ = ∑' i, (Measure.map D.π μprep) (π_part.parts i) := hsum.symm
    _ = (Measure.map D.π μprep) (⋃ i, π_part.parts i) := hunion.symm
    _ = 1 := hunion_eq_one

end LF2
end CSD
