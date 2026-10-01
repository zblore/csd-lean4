import CsdLean4.RecordLayer.Measurement
import CsdLean4.RecordLayer.DrivenTwoTime

open MeasureTheory Set CSD.RecordLayer CSD.SigmaLayer CSD.LF2

namespace RecordReview

def zeroMeasurement : Measurement 1 := ⟨⟨fun _ => 0, fun _ => le_rfl⟩, 0⟩

-- Nonnegativity alone permits no record at any point, even on the unit fibre.
example (ξ : ℝ) : zeroMeasurement.outcome ξ = none := by
  apply (fibreOutcome_eq_none_iff _ _).2
  intro i
  simp [zeroMeasurement, cdfCell, loSum]

example (ξ : ℝ) : zeroMeasurement.record ξ = none := by
  have h : zeroMeasurement.outcome ξ = none := by
    apply (fibreOutcome_eq_none_iff _ _).2
    intro i
    simp [zeroMeasurement, cdfCell, loSum]
  rw [Measurement.record, h]
  rfl

noncomputable def halfMeasurement : Measurement 1 := ⟨⟨fun _ => 1 / 2, fun _ => by norm_num⟩, 0⟩

-- A nonempty but subnormalized context also misses part of the unit fibre.
example : halfMeasurement.outcome (3 / 4) = none := by
  apply (fibreOutcome_eq_none_iff _ _).2
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  norm_num [halfMeasurement, cdfCell, loSum]

def oneMeasurement : Measurement 1 := ⟨⟨fun _ => 1, fun _ => by norm_num⟩, 0⟩

example : oneMeasurement.prob 0 = 1 := by
  rw [oneMeasurement.prob_eq_rate (by simp [oneMeasurement]) 0]
  norm_num [oneMeasurement]

example : ∀ᵐ ξ ∂fibreTypicality, ∃ i,
    oneMeasurement.record ξ = some ⟨oneMeasurement.context, i, oneMeasurement.time⟩ :=
  oneMeasurement.ae_record_of_sum_eq_one (by simp [oneMeasurement])

-- A normalized readout still has the half-open endpoint convention on the real line.
example : oneMeasurement.outcome 0 = some 0 := by
  apply (fibreOutcome_eq_some_iff _ oneMeasurement.context.rate_nonneg _ _).2
  norm_num [oneMeasurement, cdfCell, loSum]

example : oneMeasurement.outcome 1 = none := by
  apply (fibreOutcome_eq_none_iff _ _).2
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  norm_num [oneMeasurement, cdfCell, loSum]

-- The old P5 event interface does not encode time evolution.
example {n : ℕ} (c : FibreContext n) (i : Fin n) (s t : OnticTime) :
    (fibreRecordSemantics n).event ⟨c, i, s⟩ =
      (fibreRecordSemantics n).event ⟨c, i, t⟩ := rfl

-- Concrete nonzero state in dimension two, with an impossible first outcome.
-- This exercises the newly covered branch, for every measurable drive and second context.
example (b : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
    {Φ : CSD.LF4.CPN 2 → CSD.LF4.CPN 2} (hΦ : Measurable Φ)
    (c : ContextField 2) (j : Fin 2) :
    rotatedMixedTwoPrep b (rankOneDensity (b 0) (b.orthonormal.1 0))
        (drivenJointRecordSector (basinIndex (basisContext b)) (baseLift Φ)
          (basinIndex c) 1 j) = 0 := by
  rw [driven_mixed_two_time_born b _ hΦ c 1 j, born_quadratic]
  rw [b.orthonormal.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
  simp

-- A constant rate field is permitted: generic ContextField does not impose basis rates.
def constantContext : ContextField 2 where
  rate _ i := if i = 0 then 1 else 0
  measurable_rate _ := measurable_const
  nonneg _ _ := by split <;> norm_num
  sum_one _ := by simp

example (p q : CSD.LF4.CPN 2) : constantContext.rate p 0 = constantContext.rate q 0 := rfl

-- Standard basis inhabits the basis parameter of the zero-outcome probe.
example : Nonempty (OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) :=
  ⟨EuclideanSpace.basisFun (Fin 2) ℂ⟩

#print axioms CSD.RecordLayer.Measurement.prob_eq_rate
#print axioms CSD.RecordLayer.Measurement.ae_record_of_sum_eq_one
#print axioms CSD.RecordLayer.driven_mixed_two_time_born
end RecordReview
