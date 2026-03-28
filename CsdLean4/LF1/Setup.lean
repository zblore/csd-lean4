import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

namespace CSD
namespace LF1

/-- Ambient ontic data for LF1. -/
structure OnticSetup (Sigma : Type*) [MeasurableSpace Sigma] [Nonempty Sigma] where
  μL : MeasureTheory.FiniteMeasure Sigma
  Φ  : Sigma → Sigma
  hΦ_pres : MeasureTheory.MeasurePreserving Φ (μL : Measure Sigma) (μL : Measure Sigma)
  Ω0 : Set Sigma
  hΩ0_meas : MeasurableSet Ω0
  hΩ0_nonzero : (μL : Measure Sigma) Ω0 ≠ 0

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

@[simp] lemma measurable_Φ : Measurable S.Φ := S.hΦ_pres.measurable

end OnticSetup

end LF1
end CSD
