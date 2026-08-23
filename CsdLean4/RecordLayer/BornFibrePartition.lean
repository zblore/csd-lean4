/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SigmaLayer/BornFibrePartition: the record-layer fibre partition (MD-1)

**Category:** 7-SigmaLayer (the record layer — measurement as a Born partition of the fibre).

The record-layer (MD-1) obligation, discharged on a concrete fibre. For a *sharp* preparation the
epistemic base is pinned (`π(ω) = [ψ]`) and the measurement carves the **ontic fibre** into outcome
cells; the outcome is the ontic selection of which cell the fibre point occupies, and Born is the
**fibre measure** of the cell. Per the decomposition in `specs/record-layer-plan.md` §3b–§3c, a
measurement factorises as

  **(moment-map rates)  ×  (a Born partition of the fibre)** ,

where the rates `rᵢ = |⟨eᵢ|ψ⟩|² = momentMap([ψ])ᵢ` come from the torus moment map (Papers A/B,
`LF4/MomentMap.lean`), and the fibre-partition factor produces, from any probability vector `r`, a
partition of the fibre into cells of measure `rᵢ`. **This file discharges the fibre-partition
factor** on the fibre `F = ℝ` with Lebesgue measure, via the cumulative (CDF) cells: `cdfCell r i`
is the interval `[∑_{j<i} rⱼ, ∑_{j≤i} rⱼ)`, and `volume (cdfCell r i) = rᵢ` (`volume_cdfCell`). The
cells are pairwise disjoint (`cdfCell_pairwiseDisjoint`), so — feeding the **Born rates**
`rᵢ = ‖ψ i‖²` — the fibre measure of outcome `i` is exactly the Born weight (`volume_bornCell`), and
the outcome map (`fibreOutcome`) is the ontic selection `ξ ↦ i`.

Honest scope: the interval `[0,1)`+CDF is *one* concrete Born partition — the point here is the
**interface + the measure identity**, foundational-triple, no `sorry`. The genuinely open piece is
the *dynamical* realisation (a de-isolation flow / mixing environment whose target-measures are
`∝ the moment map` — the first-passage picture, `record-layer-plan.md` §3c); the fibre object it
must produce is exactly `cdfCell` here.

## References
`specs/record-layer-plan.md` (the record layer, MD-1; §3b–§3c the decomposition + dynamics);
`LF1/Outcomes.lean` (`OutcomeRegion`, the volume-ratio weight); `LF4/MomentMap.lean`
(`momentMap_mk_eq_inner_sq`, the rates).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {n : ℕ}

/-- Cumulative sum strictly below `i`: `∑_{j < i} rⱼ`. -/
noncomputable def loSum (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ)), r j

/-- The cumulative (CDF) outcome cell for outcome `i`: the fibre interval
`[∑_{j<i} rⱼ, (∑_{j<i} rⱼ) + rᵢ)` on `F = ℝ`. For a probability vector `r` these partition `[0,1)`. -/
def cdfCell (r : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  Ico (loSum r i) (loSum r i + r i)

theorem measurableSet_cdfCell (r : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (cdfCell r i) := measurableSet_Ico

/-- **The fibre-partition measure identity: the fibre measure of outcome `i` equals the rate `rᵢ`.**
The CDF cell has Lebesgue measure exactly `rᵢ`. This is the record-layer obligation for the
fibre-partition factor; feeding the Born rates gives the Born weight (`volume_bornCell`). -/
theorem volume_cdfCell (r : Fin n → ℝ) (i : Fin n) :
    volume (cdfCell r i) = ENNReal.ofReal (r i) := by
  rw [cdfCell, Real.volume_Ico]
  congr 1
  ring

/-- The cumulative cell for `i` ends at or before the cell for `j > i` begins:
`(∑_{k<i} rₖ) + rᵢ ≤ ∑_{k<j} rₖ` (needs `r ≥ 0`). This is the ordering that makes the cells a genuine
partition of the fibre. -/
theorem loSum_add_le_loSum (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) {i j : Fin n}
    (hij : (i : ℕ) < (j : ℕ)) : loSum r i + r i ≤ loSum r j := by
  have hnotmem : i ∉ Finset.univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ)) := by simp
  have hsub : insert i (Finset.univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ)))
      ⊆ Finset.univ.filter (fun k : Fin n => (k : ℕ) < (j : ℕ)) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hij
  calc loSum r i + r i
      = ∑ k ∈ insert i (Finset.univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ))), r k := by
        rw [Finset.sum_insert hnotmem, loSum]; ring
    _ ≤ loSum r j := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hr k)

/-- The CDF cells of outcomes `i < j` are disjoint (given `r ≥ 0`): cell `i` ends before cell `j`
starts. -/
theorem cdfCell_disjoint_of_lt (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) {i j : Fin n}
    (hij : (i : ℕ) < (j : ℕ)) : Disjoint (cdfCell r i) (cdfCell r j) := by
  rw [cdfCell, cdfCell, Set.Ico_disjoint_Ico]
  calc min (loSum r i + r i) (loSum r j + r j) ≤ loSum r i + r i := min_le_left _ _
    _ ≤ loSum r j := loSum_add_le_loSum r hr hij
    _ ≤ max (loSum r i) (loSum r j) := le_max_right _ _

/-- **The CDF cells are pairwise disjoint** (given `r ≥ 0`): the fibre is genuinely *partitioned* into
outcome cells, so the outcome map is a well-defined ontic selection and the Born weights are
additive. -/
theorem cdfCell_pairwiseDisjoint (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Pairwise (Function.onFun Disjoint (cdfCell r)) := by
  intro i j hij
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · exact cdfCell_disjoint_of_lt r hr h
  · exact absurd (Fin.ext h) hij
  · exact (cdfCell_disjoint_of_lt r hr h).symm

open Classical in
/-- **The outcome map (the ontic record):** the fibre point `ξ` selects outcome `i` when it lies in
`cdfCell r i`; `none` off the cells. For a probability vector this is total off a null set. -/
noncomputable def fibreOutcome (r : Fin n → ℝ) (ξ : ℝ) : Option (Fin n) :=
  if h : ∃ i, ξ ∈ cdfCell r i then some h.choose else none

/-- **The ontic selection is the record.** For `r ≥ 0` (disjoint cells) the outcome map records `i`
at a fibre point exactly when that point lies in the outcome-`i` cell: `fibreOutcome r ξ = some i ↔
ξ ∈ cdfCell r i`. So reading the outcome and testing membership in the record event agree. -/
theorem fibreOutcome_eq_some_iff (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (ξ : ℝ) (i : Fin n) :
    fibreOutcome r ξ = some i ↔ ξ ∈ cdfCell r i := by
  unfold fibreOutcome
  split
  · next h =>
    rw [Option.some_inj]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hi
      by_contra hne
      exact absurd hi (Set.disjoint_left.mp (cdfCell_pairwiseDisjoint r hr hne) h.choose_spec)
  · next h =>
    constructor
    · intro hcon; exact absurd hcon (by simp)
    · intro hi; exact (h ⟨i, hi⟩).elim

/-! ### The Born rates and the record-layer Born identity -/

/-- The Born rate of outcome `i` for state `ψ`: the squared component magnitude
`‖ψ i‖² = |⟨eᵢ, ψ⟩|²` (standard/computational-basis context). -/
noncomputable def bornRate (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) : ℝ := ‖ψ i‖ ^ 2

theorem bornRate_nonneg (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) : 0 ≤ bornRate ψ i := by
  unfold bornRate; positivity

/-- The Born rates form a probability vector on a unit state: `∑ᵢ ‖ψ i‖² = ‖ψ‖² = 1`. -/
theorem sum_bornRate (ψ : EuclideanSpace ℂ (Fin n)) : ∑ i, bornRate ψ i = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rfl

theorem sum_bornRate_unit (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    ∑ i, bornRate ψ i = 1 := by rw [sum_bornRate, hψ, one_pow]

/-- **Record-layer Born identity.** The fibre measure of the outcome-`i` cell, at the Born rates,
equals the Born weight `‖ψ i‖² = |⟨eᵢ, ψ⟩|²`. So measurement outcome frequencies are the fibre
volumes of the CDF cells fed by the moment-map rates — the record layer's measure content,
foundational-triple, no `sorry`. -/
theorem volume_bornCell (ψ : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    volume (cdfCell (bornRate ψ) i) = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
  volume_cdfCell _ i

/-- **Additivity.** The disjoint CDF cells cover a fibre set of total measure `∑ᵢ rᵢ` — the fibre
partition is measure-additive across outcomes (via `measure_iUnion` on the pairwise-disjoint cells). -/
theorem volume_iUnion_cdfCell (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume (⋃ i, cdfCell r i) = ENNReal.ofReal (∑ i, r i) := by
  rw [measure_iUnion (cdfCell_pairwiseDisjoint r hr) (measurableSet_cdfCell r), tsum_fintype]
  simp_rw [volume_cdfCell]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i)]

/-- **The record-layer Born normalisation.** For a *unit* state the Born cells partition a fibre set
of measure exactly `1`: the total ontic typicality of all outcomes is certainty. The fibre measure of
each cell is the Born weight (`volume_bornCell`), the cells are disjoint (`cdfCell_pairwiseDisjoint`),
and together they carry unit measure — the complete measure content of the record layer's
fibre-partition factor, foundational-triple, no `sorry`. -/
theorem volume_iUnion_bornCell_unit (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    volume (⋃ i, cdfCell (bornRate ψ) i) = 1 := by
  rw [volume_iUnion_cdfCell _ (bornRate_nonneg ψ), sum_bornRate_unit ψ hψ, ENNReal.ofReal_one]

/-- `fibreOutcome` is `none` exactly off every cell — the companion of
`fibreOutcome_eq_some_iff`, and what identifies the leftover set as a complement. -/
theorem fibreOutcome_eq_none_iff (r : Fin n → ℝ) (ξ : ℝ) :
    fibreOutcome r ξ = none ↔ ∀ i, ξ ∉ cdfCell r i := by
  unfold fibreOutcome
  split
  · next h => exact ⟨by simp, fun hall => absurd h.choose_spec (hall _)⟩
  · next h => exact ⟨fun _ i hi => h ⟨i, hi⟩, fun _ => rfl⟩

end CSD.RecordLayer
