import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

namespace CSD
namespace LF1

/-- Ambient ontic data for LF1.

`SigmaSpace` is an abstract measurable space standing in for the ontic phase space.  It is
**not** required to be `ℝ^{2n}` or a symplectic manifold; the physical grounding
(Liouville measure from a symplectic form, flow from Hamilton's equations) is encoded
as hypotheses rather than derived from first principles.  LF2 and later papers are
expected to instantiate `SigmaSpace` with a concrete mechanical phase space.

## Physical inputs vs. proof-used assumptions

Not every field is used directly inside LF1 proofs. The fields split into two
roles.

**Used directly in LF1 proofs:**
- `μL`       : appears in every measure-theoretic computation.
- `Φ`        : its measurability (`measurable_Φ`, derived from `hΦ_pres`) is
               used to pull back outcome regions.
- `Ω0`, `hΩ0_meas`, `hΩ0_nonzero` : define and normalise the conditional
               preparation measure.

**Declared as structural ontic input; not exercised inside any current proof
(LF1, LF2, or LF3):**
- `hΦ_pres`  : Liouville's theorem (Φ preserves μL). Carried because it is the
               correct physical model: the class of `OnticSetup`s CSD cares
               about is µ_L-preserving flows, not arbitrary measurable maps.
               Inside LF1, only `hΦ_pres.measurable` is extracted via
               `measurable_Φ`; the full measure-preservation content is never
               invoked.

Readers comparing with the manuscript should note that Liouville preservation
does **not** appear as a hypothesis in any LF1, LF2, or LF3 proof step. It is
declared structural CSD input so that every `OnticSetup` is a physically
admissible model, and so that `measurable_Φ` can be derived uniformly from it
rather than postulated separately.

**Honest disclosure.** The LF1 proof is therefore strictly more general than the
physical reading suggests: it works for any measurable Φ, not only µ_L-preserving
ones. The preservation content becomes load-bearing only when a future LF4
instantiation derives µ_L from a symplectic / Kähler volume form on a concrete
Σ, at which point `hΦ_pres` ceases to be a stipulation and becomes a theorem.
Until then `hΦ_pres` is structural payload that buys nothing the current proofs
use, and the corpus carries it for physical admissibility rather than for
mathematical content. This connects to D1 (the preparation-measure origin
problem in Paper A's framing): µ_L is asserted, the flow is asserted to
preserve it, and neither is derived in v1.00.
-/
structure OnticSetup (SigmaSpace : Type*) [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace] where
  /-- The Liouville measure on the ontic phase space.
      Assumed finite; in concrete settings this is the restriction of Lebesgue measure
      (or the symplectic volume form) to a bounded region of phase space. -/
  μL : MeasureTheory.FiniteMeasure SigmaSpace
  /-- The deterministic ontic flow.
      In concrete settings this is the time-`t` map of Hamilton's equations. -/
  Φ  : SigmaSpace → SigmaSpace
  /-- Liouville's theorem: the flow `Φ` preserves the Liouville measure `μL`.
      Assumed as a hypothesis; derivable from a symplectic / Kähler structure in
      a concrete LF4 instantiation. Within LF1, LF2, and LF3 only measurability
      of `Φ` (extracted via `measurable_Φ`) is consumed in proofs; the full
      measure-preservation content is currently structural payload, carried for
      physical admissibility of the ontic model. It becomes load-bearing only
      when LF4 derives `μL` from a concrete volume form. -/
  hΦ_pres : MeasureTheory.MeasurePreserving Φ (μL : Measure SigmaSpace) (μL : Measure SigmaSpace)
  /-- The preparation region: the measurable subset of phase space consistent with the
      experimental preparation procedure. -/
  Ω0 : Set SigmaSpace
  /-- The preparation region is measurable. -/
  hΩ0_meas : MeasurableSet Ω0
  /-- The preparation region has nonzero Liouville measure, so normalisation is well-defined. -/
  hΩ0_nonzero : (μL : Measure SigmaSpace) Ω0 ≠ 0

namespace OnticSetup

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace] (S : OnticSetup SigmaSpace)

/-- Measurability of the deterministic flow.

This is the **only** property of `Φ` consumed by LF1, LF2, and LF3 proofs. It
is derived from `hΦ_pres` (Liouville preservation implies measurability) so
that `OnticSetup` need not carry measurability as a separate field. The full
content of `hΦ_pres`, that `Φ` actually preserves `μL`, is not invoked
anywhere in the current corpus. See the `OnticSetup` docstring for the honest
disclosure on this. -/
@[simp] lemma measurable_Φ : Measurable S.Φ := S.hΦ_pres.measurable

end OnticSetup

end LF1
end CSD
