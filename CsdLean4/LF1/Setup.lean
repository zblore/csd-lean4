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

## Physical inputs vs. proof-used assumptions

Not every field is used directly inside LF1 proofs.  The fields split into two roles:

**Used directly in LF1 proofs:**
- `μL`       — appears in every measure-theoretic computation.
- `Φ`        — its measurability (`measurable_Φ`, derived from `hΦ_pres`) is used to
               pull back outcome regions.
- `Ω0`, `hΩ0_meas`, `hΩ0_nonzero` — define and normalise the conditional preparation
               measure.

**Declared as structural ontic input; not exercised inside LF1 proofs:**
- `hΦ_pres`  — Liouville's theorem (Φ preserves μL).  Carried here because it is the
               correct physical model and is required by LF2 and later layers.  Within
               LF1, only `hΦ_pres.measurable` is extracted (see `measurable_Φ` below);
               the full measure-preservation content is never invoked.

Readers comparing with the manuscript should note that Liouville preservation does **not**
appear as a hypothesis in any LF1 proof step.  It is declared structural CSD input so
that every `OnticSetup` is a physically admissible model, and so that `measurable_Φ` can
be derived uniformly from it rather than postulated separately.
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
      Assumed as a hypothesis; derivable from the symplectic structure in concrete cases.
      Note: within LF1 only measurability of `Φ` (extracted via `measurable_Φ`) is used
      in proofs. The full measure-preservation property is carried here for correctness of
      the ontic model and will be exercised in LF2 and later layers. -/
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

/-- Measurability of the deterministic flow.

This is the **only** property of `Φ` that LF1 proofs use directly.  It is derived from
`hΦ_pres` (Liouville preservation implies measurability) so that `OnticSetup` need not
carry measurability as a separate field.  The full content of `hΦ_pres` — that `Φ`
actually preserves `μL` — is not invoked anywhere in LF1. -/
@[simp] lemma measurable_Φ : Measurable S.Φ := S.hΦ_pres.measurable

end OnticSetup

end LF1
end CSD
