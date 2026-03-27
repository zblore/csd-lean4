import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory Set

namespace CSD
namespace LF1

/-- Ambient ontic data for LF1. -/
structure OnticSetup (Σ : Type*) [MeasurableSpace Σ] where
  μL : MeasureTheory.FiniteMeasure Σ
  Φ  : Σ → Σ
  hΦ_pres : MeasureTheory.MeasurePreserving Φ (μL : Measure Σ) (μL : Measure Σ)
  Ω0 : Set Σ
  hΩ0_meas : MeasurableSet Ω0
  hΩ0_nonzero : (μL : Measure Σ) Ω0 ≠ 0

namespace OnticSetup

variable {Σ : Type*} [MeasurableSpace Σ] (S : OnticSetup Σ)

@[simp] lemma measurable_Φ : Measurable S.Φ :=
  S.hΦ_pres.measurable

end OnticSetup

end LF1
end CSD
