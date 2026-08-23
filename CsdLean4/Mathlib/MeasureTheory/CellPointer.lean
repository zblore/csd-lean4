/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# A total pointer from a family of cells

**Category:** 1-Mathlib. No CSD content.

A recurring pattern: a probability space is carved into finitely many disjoint measurable *cells*
carrying prescribed weights, and one wants a **total** readout function whose fibres are those
cells. Totality is the only wrinkle — the cells generally cover the space up to a null set, not
exactly — so the leftover is sent to a default index and shown not to matter.

Extracted at the second consumer (`CONVENTIONS.md` §9, rule of two):

* `RecordLayer.cdfDeIsolationInteraction` — the CDF cells on the fibre `ℝ`;
* the competing-clock race cells on the fibre `Fin (n+1) → ℝ`
  (`Mathlib/Probability/CompetingExponentials.lean`).

Both need exactly `cellPointer` and `measure_cellPointer_preimage`.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {F ι : Type*} [MeasurableSpace F] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

open Classical in
/-- **The total pointer of a cell family**: report the cell containing `x`, or the default `i₀`
when `x` lies in none of them. -/
noncomputable def cellPointer (C : ι → Set F) (i₀ : ι) (x : F) : ι :=
  if h : ∃ i, x ∈ C i then h.choose else i₀

omit [MeasurableSpace F] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma cellPointer_eq_of_mem {C : ι → Set F} (hdisj : Pairwise (Function.onFun Disjoint C))
    (i₀ : ι) {x : F} {i : ι} (hx : x ∈ C i) : cellPointer C i₀ x = i := by
  classical
  have hex : ∃ j, x ∈ C j := ⟨i, hx⟩
  rw [cellPointer, dif_pos hex]
  by_contra hne
  exact absurd hx (Set.disjoint_left.mp (hdisj hne) hex.choose_spec)

omit [MeasurableSpace F] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The pointer's fibre over `i`: the cell, together with the leftover when `i` is the default. -/
lemma cellPointer_preimage {C : ι → Set F} (hdisj : Pairwise (Function.onFun Disjoint C))
    (i₀ i : ι) :
    cellPointer C i₀ ⁻¹' {i} = C i ∪ (if i = i₀ then (⋃ j, C j)ᶜ else ∅) := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union]
  by_cases hx : ∃ j, x ∈ C j
  · obtain ⟨j, hj⟩ := hx
    have hpt : cellPointer C i₀ x = j := cellPointer_eq_of_mem hdisj i₀ hj
    have hin : x ∈ ⋃ k, C k := Set.mem_iUnion.mpr ⟨j, hj⟩
    rw [hpt]
    refine ⟨fun h => Or.inl (h ▸ hj), ?_⟩
    rintro (hmem | hmem)
    · exact (cellPointer_eq_of_mem hdisj i₀ hmem) ▸ hpt ▸ rfl
    · by_cases hii : i = i₀
      · rw [if_pos hii, Set.mem_compl_iff] at hmem
        exact absurd hin hmem
      · rw [if_neg hii] at hmem
        exact absurd hmem (by simp)
  · have hpt : cellPointer C i₀ x = i₀ := by rw [cellPointer, dif_neg hx]
    have hout : x ∈ (⋃ j, C j)ᶜ := by
      rw [Set.mem_compl_iff, Set.mem_iUnion]
      exact fun ⟨j, hj⟩ => hx ⟨j, hj⟩
    rw [hpt]
    refine ⟨fun h => Or.inr (by rw [if_pos h.symm]; exact hout), ?_⟩
    rintro (hmem | hmem)
    · exact absurd ⟨i, hmem⟩ hx
    · by_cases hii : i = i₀
      · exact hii.symm
      · rw [if_neg hii] at hmem
        exact absurd hmem (by simp)

omit [MeasurableSingletonClass ι] in
lemma measurable_cellPointer {C : ι → Set F} (hmeas : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (Function.onFun Disjoint C)) (i₀ : ι) :
    Measurable (cellPointer C i₀) := by
  classical
  refine measurable_to_countable' (fun i => ?_)
  rw [cellPointer_preimage hdisj i₀ i]
  refine (hmeas i).union ?_
  by_cases hii : i = i₀
  · rw [if_pos hii]
    exact (MeasurableSet.iUnion hmeas).compl
  · rw [if_neg hii]
    exact MeasurableSet.empty

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- ★ **The pointer's fibres carry the cell weights.** The leftover is null because the cells are
disjoint and their weights already exhaust the probability, so the default index gains nothing. -/
theorem measure_cellPointer_preimage {ν : Measure F} [IsProbabilityMeasure ν] {C : ι → Set F}
    (hmeas : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (Function.onFun Disjoint C))
    {r : ι → ℝ} (hrnn : ∀ i, 0 ≤ r i) (hr : ∀ i, ν (C i) = ENNReal.ofReal (r i))
    (hsum : ∑ i, r i = 1) (i₀ i : ι) :
    ν (cellPointer C i₀ ⁻¹' {i}) = ENNReal.ofReal (r i) := by
  classical
  have htot : ν (⋃ j, C j) = 1 := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype]
    simp_rw [hr]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hrnn j), hsum, ENNReal.ofReal_one]
  have hnull : ν ((⋃ j, C j)ᶜ) = 0 := by
    rw [measure_compl (MeasurableSet.iUnion hmeas) (by rw [htot]; exact ENNReal.one_ne_top), htot,
      measure_univ, tsub_self]
  rw [cellPointer_preimage hdisj i₀ i]
  by_cases hii : i = i₀
  · rw [if_pos hii]
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_union_le _ _) ?_
      rw [hr i, hnull, add_zero]
    · rw [← hr i]
      exact measure_mono Set.subset_union_left
  · rw [if_neg hii, Set.union_empty, hr i]

end MeasureTheory
