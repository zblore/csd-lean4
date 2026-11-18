/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DetunedExchange
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive

/-!
# The rays near a ray have positive Fubini–Study measure

**Category:** 7-SigmaLayer. BACKLOG #438, third brick (Task 2 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (2)).

`RecordLayer/UnifiedRayRadar.lean` gives the radar counts from every ray `P` turned by a
unitary within a radius of the identity. One ray has Fubini–Study measure zero. Here: the
set of turned rays does not.

* `turnedRays`, `self_mem_turnedRays`, `turnedRays_mono`;
* ★★★ `fsMeasure_turnedRays_pos` — for any reference point of the measure, any ray `q` and
  any `r > 0`, the rays `q` turned by a unitary `W` with `‖W − 1‖ < r` have positive
  Fubini–Study measure. The measure is the image of Haar measure on the unitaries under the
  orbit map; the unitaries that carry the reference point into the set contain an open ball
  about one of them; Haar measure is positive on open sets.

## Honest scope

⚠️ **Positive, with no value.** No lower bound in terms of `r` and the dimension is given.

⚠️ **The set is not shown measurable or open.** The statement is about the measure of the
set as it stands (the outer measure). A measurable set of positive measure inside the
compatible region still has to be exhibited for a `HistoryPreparation`; the compatible
region itself is measurable (`RecordLayer/UnifiedRecordHistoryBridge.lean`) and contains the
set once the family is instantiated.

⚠️ **In the carrier's own projective space.** The transport to the arena's base by the
labelling of the basis, the product with the box of pointer angles, and the preparation are
not here.

References: `specs/BACKLOG.md` #438; `specs/unified-record-spacetime-plan.md` (UO-25, UD-213,
UD-214, UD-215); `RecordLayer/UnifiedRayRadar.lean` (`penta_radar_lorentz_near_ray`);
`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean` (`fsMeasure`, `orbitMap`,
`orbit_map_measurable`); `Mathlib/LinearAlgebra/Projectivization/UnitaryTransitive.lean`;
`LF4/TypicalityForcing.lean` (`fsMeasure_pos_of_isOpen`); `CV/DetunedExchange.lean`
(`arenaKick_eq_smul'`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization Topology

namespace CSD.RecordLayer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The rays near `q`**: `q` turned by a unitary within `r` of the identity in the
operator norm. -/
def turnedRays (q : GenArena ι) (r : ℝ) : Set (GenArena ι) :=
  {x | ∃ W : Matrix.unitaryGroup ι ℂ, ‖W.val - 1‖ < r ∧ x = arenaKick W q}

omit [Nonempty ι] in
theorem self_mem_turnedRays (q : GenArena ι) {r : ℝ} (hr : 0 < r) : q ∈ turnedRays q r :=
  ⟨1, by simpa using hr, by rw [arenaKick_eq_smul', one_smul]⟩

omit [Nonempty ι] in
theorem turnedRays_mono (q : GenArena ι) {r r' : ℝ} (h : r ≤ r') :
    turnedRays q r ⊆ turnedRays q r' := fun _ ⟨W, hW, hx⟩ => ⟨W, hW.trans_le h, hx⟩

/-- ★★★ **The rays near a ray have positive Fubini–Study measure**, for any reference point
of the measure: the Fubini–Study measure is the image of Haar measure on the unitaries under
the orbit map, the unitaries that carry the reference point into `turnedRays q r` contain an
open ball, and Haar measure is positive on open sets. -/
theorem fsMeasure_turnedRays_pos (p₀ q : GenArena ι) {r : ℝ} (hr : 0 < r) :
    0 < fsMeasure p₀ (turnedRays q r) := by
  obtain ⟨V, hV⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup ι ℂ) p₀ q
  have hVn : ‖V.val‖ ≤ 1 := (CStarRing.norm_of_mem_unitary V.property).le
  have hopen : IsOpen {U : Matrix.unitaryGroup ι ℂ | ‖U.val - V.val‖ < r} :=
    isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  have hne : {U : Matrix.unitaryGroup ι ℂ | ‖U.val - V.val‖ < r}.Nonempty :=
    ⟨V, by simpa using hr⟩
  have hsub : {U : Matrix.unitaryGroup ι ℂ | ‖U.val - V.val‖ < r}
      ⊆ orbitMap p₀ ⁻¹' turnedRays q r := by
    intro U hU
    refine ⟨U * V⁻¹, ?_, ?_⟩
    · have h1 : V.val * star V.val = 1 := Matrix.mem_unitaryGroup_iff.1 V.property
      have h2 : (U * V⁻¹).val = U.val * star V.val := rfl
      have e : (U * V⁻¹).val - 1 = (U.val - V.val) * star V.val := by
        rw [h2, sub_mul, h1]
      rw [e]
      refine lt_of_le_of_lt ((norm_mul_le _ _).trans ?_) hU
      rw [norm_star]
      exact mul_le_of_le_one_right (norm_nonneg _) hVn
    · show orbitMap p₀ U = arenaKick (U * V⁻¹) q
      rw [arenaKick_eq_smul', ← hV, smul_smul, inv_mul_cancel_right, orbitMap]
  calc 0 < unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | ‖U.val - V.val‖ < r} :=
        hopen.measure_pos unitaryHaarProb hne
    _ ≤ unitaryHaarProb (orbitMap p₀ ⁻¹' turnedRays q r) := measure_mono hsub
    _ ≤ fsMeasure p₀ (turnedRays q r) :=
        Measure.le_map_apply (orbit_map_measurable p₀).aemeasurable _

end CSD.RecordLayer

end
