/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.NullSeamWitness

/-!
# SigmaLayer/NullSeamLift: the third horn on an even-dimensional arena

**Category:** dynamical measurement — `specs/BACKLOG.md` **B2**.

`NullSeamWitness.lean` builds the third measurement horn on `S¹ × ℂℙ²`. That arena has
real dimension `1 + 4 = 5` — **odd** — so it admits no symplectic structure, which is why
its invariant measure had to be renamed `nullSeamMeasure` (the original
`nullSeamLiouville` was the corpus's second odd-dimension slip; `scripts/check-claims.sh`
check (7) now enforces the parity question).

This module removes that obstruction by giving the register its conjugate coordinate:
the arena becomes `T² × ℂℙ²`, real dimension `2 + 4 = 6`. The construction is otherwise
**unchanged** — the crossing angle still reads `θ₁`, and `θ₂` is carried along untouched,
exactly as a conjugate variable should be when the Hamiltonian does not depend on it.

## What transfers, and how

Everything, and cheaply, because the lift is a product with the identity:

* `continuous_nullSeamEvolveLift`, `nullSeamEvolveLift_measurePreserving` — continuity and
  invariance of `(vol ⊗ vol) ⊗ μ_FS`.
* `nullSeamLift_landing_neg` / `_pos` — records exact and correct off the seam.
* `nullSeamLift_seam_null` — the seam is `(two points) × T¹`, still null.
* ★ `nullSeamLift_born_left` / `_right` — **exact** Born `r` and `1 − r`, now measured on
  an even-dimensional register: the outcome sets are cylinders `S ×ˢ univ`, so their
  measure is `vol S · 1` by `Measure.prod_prod`.
* ★★ `nullSeamLiftClosure` — the third horn, restated on the even-dimensional arena.

## What this does and does not earn

**Earned:** the *parity obstruction* is gone. `T²` and `ℂℙ²` are each even-dimensional
Kähler factors, so the product admits a symplectic structure, and the invariant measure is
the corresponding volume — the name `nullSeamLiftMeasure` no longer asserts something the
space cannot carry.

⚠️ **NOT earned, and deliberately not claimed:** the symplectic form itself is still not
constructed. Mathlib has no symplectic-manifold API (verified 2026-08-04), so "this measure
*is* the Liouville volume of `ω^3/3!`" remains the same §2a-scoped statement as everywhere
else in the corpus (`MATHLIB-GAPS.md`, A4). Even dimension is *necessary*, not sufficient,
and the guard's parity ledger records this arena as even without asserting the form. The
horn's other prices are unchanged: exactness is at the Dirac-calibrated ready pointer, and
"Born" is still carried by the free cell-split parameter `r` rather than by a preparation's
moment map (`NullSeamWitness.lean`'s scope note).

## References

`specs/BACKLOG.md` B2 (this row), A4 (the blocked arrow); `SigmaLayer/NullSeamWitness.lean`
(the construction lifted here); `docs/TOUR.md` §"Which horn is the right one?" (the
trilemma).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix.UnitaryGroup

/-- The even-dimensional seam arena: `T² × ℂℙ²`, real dimension `2 + 4 = 6`. -/
abbrev SeamArenaLift : Type := (CircleFibre × CircleFibre) × Pointer 2

/-- **The lifted propagator**: the crossing acts through `θ₁` exactly as before; `θ₂`, the
register's conjugate coordinate, is carried along untouched — which is what a conjugate
variable does when the generator does not depend on it. Written as a reindexing of the
unlifted map so that every transfer below is a one-liner. -/
noncomputable def nullSeamEvolveLift (r : ℝ) : SeamArenaLift → SeamArenaLift :=
  fun y => (y.1, (nullSeamEvolve r (y.1.1, y.2)).2)

@[simp] lemma nullSeamEvolveLift_fst (r : ℝ) (y : SeamArenaLift) :
    (nullSeamEvolveLift r y).1 = y.1 := rfl

/-- The lifted pointer component is the unlifted one at `θ₁`. -/
lemma nullSeamEvolveLift_snd (r : ℝ) (y : SeamArenaLift) :
    (nullSeamEvolveLift r y).2 = (nullSeamEvolve r (y.1.1, y.2)).2 := rfl

/-- The reindexing onto the unlifted arena. -/
lemma continuous_seamReindex :
    Continuous fun y : SeamArenaLift => ((y.1.1, y.2) : CircleFibre × Pointer 2) :=
  (continuous_fst.comp continuous_fst).prodMk continuous_snd

/-! ### Continuity and invariance -/

/-- The lifted propagator is continuous. -/
theorem continuous_nullSeamEvolveLift (r : ℝ) : Continuous (nullSeamEvolveLift r) :=
  continuous_fst.prodMk
    (continuous_snd.comp ((continuous_nullSeamEvolve r).comp continuous_seamReindex))

/-- The even-dimensional arena's invariant measure: Haar on `T²`, Fubini–Study on `ℂℙ²`.
Unlike the `S¹ × ℂℙ²` version this arena *is* even-dimensional, so the name carries no
parity defect — though the symplectic form itself is still not constructed (§2a). -/
noncomputable def nullSeamLiftMeasure (q₀ : Pointer 2) : Measure SeamArenaLift :=
  ((volume : Measure CircleFibre).prod (volume : Measure CircleFibre)).prod
    (fubiniStudyMeasure q₀)

instance (q₀ : Pointer 2) : IsProbabilityMeasure (nullSeamLiftMeasure q₀) := by
  unfold nullSeamLiftMeasure
  infer_instance

/-- **Measure invariance** — a skew product over the whole register torus: both register
coordinates are conserved, and every slice acts by an FS-preserving unitary. -/
theorem nullSeamEvolveLift_measurePreserving (r : ℝ) (q₀ : Pointer 2) :
    MeasurePreserving (nullSeamEvolveLift r)
      (nullSeamLiftMeasure q₀) (nullSeamLiftMeasure q₀) := by
  have hm : Measurable (Function.uncurry
      (fun (y : CircleFibre × CircleFibre) (q : Pointer 2) =>
        (nullSeamEvolve r (y.1, q)).2)) :=
    (continuous_snd.comp
      ((continuous_nullSeamEvolve r).comp continuous_seamReindex)).measurable
  exact MeasurePreserving.skew_product
    (MeasurePreserving.id ((volume : Measure CircleFibre).prod volume)) hm
    (Filter.Eventually.of_forall fun θ =>
      fubiniStudyMeasure_smul_invariant (nullSeamUU r θ.1) q₀)

/-! ### Records, seam, and exact Born -/

/-- Records in the open first cell, exactly — inherited pointwise. -/
theorem nullSeamLift_landing_neg (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (y : CircleFibre × CircleFibre) (hy : nullSeamSign r y.1 < 0) :
    (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 0 :=
  nullSeam_landing_neg r hr0 hr1 y.1 hy

/-- Records in the open second cell, exactly. -/
theorem nullSeamLift_landing_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (y : CircleFibre × CircleFibre) (hy : 0 < nullSeamSign r y.1) :
    (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 1 :=
  nullSeam_landing_pos r hr0 hr1 y.1 hy

/-- The lifted outcome set is a cylinder over the unlifted one. -/
lemma nullSeamLift_outcome_cylinder (r : ℝ) (j : Fin 2) :
    {y : CircleFibre × CircleFibre |
        (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) j}
      = {θ : CircleFibre |
          (nullSeamEvolve r (θ, readyState)).2 ∈ recordRegion (K := 2) j} ×ˢ Set.univ := by
  ext y
  constructor
  · intro h; exact ⟨h, Set.mem_univ _⟩
  · rintro ⟨h, -⟩; exact h

/-- ★ **The seam is still null** — now `(two points) × T¹`. -/
theorem nullSeamLift_seam_null (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure (CircleFibre × CircleFibre))
        {y | nullSeamSign r y.1 = 0} = 0 := by
  have hset : {y : CircleFibre × CircleFibre | nullSeamSign r y.1 = 0}
      = {θ : CircleFibre | nullSeamSign r θ = 0} ×ˢ (Set.univ : Set CircleFibre) := by
    ext y
    exact ⟨fun h => ⟨h, Set.mem_univ _⟩, fun h => h.1⟩
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, nullSeam_seam_null r hr0 hr1, zero_mul]

/-- ★ **Exact Born, first outcome**, on the even-dimensional register. -/
theorem nullSeamLift_born_left (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure (CircleFibre × CircleFibre))
        {y | (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 0}
      = ENNReal.ofReal r := by
  rw [nullSeamLift_outcome_cylinder r 0, Measure.volume_eq_prod, Measure.prod_prod, measure_univ,
    mul_one, nullSeam_born_left r hr0 hr1]

/-- ★ **Exact Born, second outcome**. -/
theorem nullSeamLift_born_right (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (volume : Measure (CircleFibre × CircleFibre))
        {y | (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 1}
      = ENNReal.ofReal (1 - r) := by
  rw [nullSeamLift_outcome_cylinder r 1, Measure.volume_eq_prod, Measure.prod_prod, measure_univ,
    mul_one, nullSeam_born_right r hr0 hr1]

/-! ### ★★ The third horn, on an even-dimensional arena -/

/-- **The third horn, parity obstruction removed.** Same construction, same prices; the
arena is now `T² × ℂℙ²`, real dimension 6, a product of Kähler factors. What is *not*
claimed: the symplectic form itself (§2a-scoped, `MATHLIB-GAPS.md` A4). -/
structure NullSeamLiftClosure (r : ℝ) : Prop where
  /-- Continuous on the whole even-dimensional arena. -/
  continuity : Continuous (nullSeamEvolveLift r)
  /-- The product measure is invariant. -/
  invariant : ∀ q₀ : Pointer 2,
    MeasurePreserving (nullSeamEvolveLift r) (nullSeamLiftMeasure q₀) (nullSeamLiftMeasure q₀)
  /-- Correct record in the open first cell. -/
  landing_left : ∀ y : CircleFibre × CircleFibre, nullSeamSign r y.1 < 0 →
    (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 0
  /-- Correct record in the open second cell. -/
  landing_right : ∀ y : CircleFibre × CircleFibre, 0 < nullSeamSign r y.1 →
    (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 1
  /-- The seam is null. -/
  seam_null : (volume : Measure (CircleFibre × CircleFibre)) {y | nullSeamSign r y.1 = 0} = 0
  /-- Exact Born, first outcome. -/
  born_left : (volume : Measure (CircleFibre × CircleFibre))
      {y | (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 0}
    = ENNReal.ofReal r
  /-- Exact Born, second outcome. -/
  born_right : (volume : Measure (CircleFibre × CircleFibre))
      {y | (nullSeamEvolveLift r (y, readyState)).2 ∈ recordRegion (K := 2) 1}
    = ENNReal.ofReal (1 - r)

/-- ★★ **The lifted third horn exists**, for every cell split. -/
theorem nullSeamLiftClosure (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    NullSeamLiftClosure r where
  continuity := continuous_nullSeamEvolveLift r
  invariant := nullSeamEvolveLift_measurePreserving r
  landing_left := nullSeamLift_landing_neg r hr0 hr1
  landing_right := nullSeamLift_landing_pos r hr0 hr1
  seam_null := nullSeamLift_seam_null r hr0 hr1
  born_left := nullSeamLift_born_left r hr0 hr1
  born_right := nullSeamLift_born_right r hr0 hr1

end CSD.RecordLayer
