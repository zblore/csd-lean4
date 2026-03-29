import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

namespace CSD
namespace LF1

/-- Ambient ontic data for LF1.

`Sigma` is an abstract measurable space standing in for the ontic phase space.  It is
**not** required to be `ℝ^{2n}` or a symplectic manifold; the physical grounding
(Liouville measure from a symplectic form, flow from Hamilton's equations) is encoded
as hypotheses rather than derived from first principles.  LF2 and later papers are
expected to instantiate `Sigma` with a concrete mechanical phase space.
-/
structure OnticSetup (Sigma : Type*) [MeasurableSpace Sigma] [Nonempty Sigma] where
  /-- The Liouville measure on the ontic phase space.
      Assumed finite; in concrete settings this is the restriction of Lebesgue measure
      (or the symplectic volume form) to a bounded region of phase space. -/
  μL : MeasureTheory.FiniteMeasure Sigma
  /-- The deterministic ontic flow.
      In concrete settings this is the time-`t` map of Hamilton's equations. -/
  Φ  : Sigma → Sigma
  /-- Liouville's theorem: the flow `Φ` preserves the Liouville measure `μL`.
      Assumed as a hypothesis; derivable from the symplectic structure in concrete cases. -/
  hΦ_pres : MeasureTheory.MeasurePreserving Φ (μL : Measure Sigma) (μL : Measure Sigma)
  /-- The preparation region: the measurable subset of phase space consistent with the
      experimental preparation procedure. -/
  Ω0 : Set Sigma
  /-- The preparation region is measurable. -/
  hΩ0_meas : MeasurableSet Ω0
  /-- The preparation region has nonzero Liouville measure, so normalisation is well-defined. -/
  hΩ0_nonzero : (μL : Measure Sigma) Ω0 ≠ 0

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

@[simp] lemma measurable_Φ : Measurable S.Φ := S.hΦ_pres.measurable

end OnticSetup

end LF1
end CSD
