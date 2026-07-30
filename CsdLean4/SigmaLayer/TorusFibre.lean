/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.CircleFibre

/-!
# SigmaLayer/TorusFibre: the Born partition on the corpus's `T²` fibre

**Category:** 7-SigmaLayer (the record layer — A1 compactness *and parity*).

## Why this exists

`CircleFibre.lean` moved the Born partition onto a compact fibre, `AddCircle 1`. That closed the
compactness objection but left a second one, which an external review of `29c6afd` identified and
which is **not** a missing-tooling problem:

> `ℂℙⁿ⁻¹` has real dimension `2n-2`, so `ℂℙⁿ⁻¹ × AddCircle 1` has real dimension `2n-1` — **odd**.
> A symplectic form needs `ωᵏ` as a volume form, so no odd-dimensional manifold carries one, hence
> none carries a Kähler structure.

So a *single* circle can never serve as the fibre of a Paper C A1 ontic surface, no matter how much
differential-geometry API Mathlib grows. (The same objection applies retroactively to
`FibredSigma`'s `ℂℙⁿ⁻¹ × ℝ`, also `2n-1`.)

The corpus already contains the fix: `LF4/KahlerInstance.lean`'s
`KTorus = AddCircle 1 × AddCircle 1`, with `KSigma N = CPN N × KTorus` of real dimension `2n` —
**even**, compact, and a product of Kähler manifolds. This file moves the Born partition onto that
fibre, putting the cells on the **first** torus coordinate and leaving the second free as its
symplectic partner.

## What is proved

* `torusCell` — the Born cell on `T²`: `circleCell r i ×ˢ univ`. Constrains `θ₁` only.
* `mem_torusCell_iff` — membership depends on `θ₁` alone; `θ₂` is unconstrained. This is the
  content of "the second coordinate is the free symplectic partner", stated as a theorem rather
  than left to the prose.
* `measurableSet_torusCell`, `volume_torusCell` — measurable, with
  `volume (torusCell r i) = ENNReal.ofReal (r i)`: **the Born weights survive the move**, since the
  free coordinate contributes a factor of `1` (`instProbKTorusVolume`).
* `torusCell_pairwiseDisjoint` — distinct outcomes stay mutually exclusive.
* `volume_torusBornCell` — fed the Born rates, the cell measure is `‖ψ i‖²`.
* `torusCell_ae_total` — the cells cover `T²` up to a null set.

## Scope — read this before citing the file

It supplies the **even-dimensional, compact arena** the Kähler question needs, and shows the Born
content is unchanged by the move. It does **not** prove `KSigma` is a Kähler manifold, and it does
not prove the fibre measure is a Liouville measure — Haar is what is exhibited, as on the circle.
Removing an *obstruction* to A1 is not the same as *establishing* A1, and this file does only the
former.

It is also still **kinematic**, and still **preparation-indexed**: `r` is an arbitrary rate vector,
and the intended consumer feeds it `bornRate ψ`, which comes from the preparation. Making the
partition genuinely context-fixed is the *successor* construction — the global basin
`Bᵢ(M) = {(p, θ₁, θ₂) : θ₁ ∈ circleCell (m_M p) i}` with the moment map evaluated at the **ontic
point** — and it is not in this file. ⚠️ That step needs measurability of `momentMap`, which the
corpus does **not** currently have (`LF4/MomentMap.lean` proves `momentMap_nonneg`,
`momentMap_le_one`, `momentMap_sum_eq_one`, but no measurability or continuity).

Nothing outside `Tests/AxiomAudit.lean` consumes this yet; the corpus's record-layer capstones
(`Measurement`, `RecordLayerClosure`, `FiniteQMClosure`, `KSigmaRecord`) still run on the `ℝ` fibre.

## References

`SigmaLayer/CircleFibre.lean` (`circleCell` and its Born weights — every theorem here transports one
of those); `LF4/KahlerInstance.lean` (`KTorus`, `KSigma`, `instProbKTorusVolume`);
`SigmaLayer/BornFibrePartition.lean` (`bornRate`, `loSum`); `specs/BACKLOG.md` (the ★★ row and its
successor target); `specs/reconstruction-status.md` §2a (the parity correction).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

/-! ### The Born cell on the two-torus -/

/-- **The Born cell on `T²`**: the circle cell in the *first* coordinate, with the second
coordinate free. The free coordinate is the symplectic partner that makes the total space
even-dimensional, which is exactly what a single circle could not supply. -/
noncomputable def torusCell (r : Fin n → ℝ) (i : Fin n) : Set LF4.KTorus :=
  circleCell r i ×ˢ (univ : Set (AddCircle (1 : ℝ)))

/-- **Only the first coordinate is constrained.** The partition reads `θ₁` and ignores `θ₂`, so the
second torus coordinate is genuinely free — the statement that the symplectic partner carries no
record content. -/
@[simp] theorem mem_torusCell_iff (r : Fin n → ℝ) (i : Fin n) (x : LF4.KTorus) :
    x ∈ torusCell r i ↔ x.1 ∈ circleCell r i := by
  simp [torusCell]

theorem measurableSet_torusCell (r : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (torusCell r i) :=
  (measurableSet_circleCell r i).prod MeasurableSet.univ

/-! ### The Born weights survive the move to `T²` -/

/-- **The torus cell carries exactly the Born weight `rᵢ`.** The free second coordinate contributes
a factor of `1`, because `T²`'s Haar measure is a probability measure — so moving from the circle to
the even-dimensional torus changes no outcome probability, just as moving from `ℝ` to the circle
did not. -/
theorem volume_torusCell (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∀ i : Fin n, loSum r i + r i ≤ 1) (i : Fin n) :
    (volume : Measure LF4.KTorus) (torusCell r i) = ENNReal.ofReal (r i) := by
  rw [torusCell, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  exact volume_circleCell r hr hsum i

/-- **Distinct outcomes stay mutually exclusive on `T²`.** Inherited coordinatewise: two points of
disjoint cells already differ in their first coordinate. -/
theorem torusCell_pairwiseDisjoint (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Pairwise (Function.onFun Disjoint (torusCell r)) := by
  intro i j hij
  have h := circleCell_pairwiseDisjoint r hr hij
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  exact Set.disjoint_left.mp h ((mem_torusCell_iff r i x).mp hxi)
    ((mem_torusCell_iff r j x).mp hxj)

/-- **Born rates on the `T²` fibre.** For a unit state the torus cell for outcome `i` has measure
`‖ψ i‖²` — the same Born weight the `ℝ` and circle fibres gave. -/
theorem volume_torusBornCell (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    (volume : Measure LF4.KTorus) (torusCell (bornRate ψ) i) = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  rw [torusCell, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  exact volume_circleBornCell ψ hψ i

/-! ### Totality -/

/-- **The cells cover `T²` up to a null set**, so a.e. microstate of the even-dimensional fibre
yields a record. As on the circle — and unlike on `ℝ` — this is a statement about the *whole*
space, since the whole space has measure one. -/
theorem torusCell_ae_total (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∀ i : Fin n, loSum r i + r i ≤ 1) (htot : ∑ i, r i = 1) :
    (volume : Measure LF4.KTorus) (univ \ ⋃ i, torusCell r i) = 0 := by
  classical
  have hmeas : ∀ i, MeasurableSet (torusCell r i) := measurableSet_torusCell r
  have hcover : (volume : Measure LF4.KTorus) (⋃ i, torusCell r i) = 1 := by
    rw [measure_iUnion (torusCell_pairwiseDisjoint r hr) hmeas, tsum_fintype,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => volume_torusCell r hr hsum i,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i), htot, ENNReal.ofReal_one]
  rw [measure_diff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    measure_univ, hcover, tsub_self]

/-- **Totality for the Born rates**, the form the record layer consumes. -/
theorem torusBornCell_ae_total (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    (volume : Measure LF4.KTorus) (univ \ ⋃ i, torusCell (bornRate ψ) i) = 0 := by
  refine torusCell_ae_total _ (bornRate_nonneg ψ) (fun j => ?_) (sum_bornRate_unit ψ hψ)
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
