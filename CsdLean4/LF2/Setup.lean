import CsdLean4.LF1.Setup
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# LF2 Setup: Sector data

Extends the LF1 `OnticSetup` with:

- a measurable projection `π : Σ → P` onto an abstract epistemic measurable
  space (standing in for `CP^{N-1}`);
- a group `G` acting measurably on both `Σ` and `P`;
- the compatibility hypotheses (`μL`-invariance of the ontic action and
  `G`-equivariance of `π`) that drive the LF2 measure bridge.

The projective space is left abstract — no `Projectivization`, no Fubini–Study
measure construction. Concrete instantiation is LF3+'s job. The reference
measure `μFS` is not a field of `SectorData`; it enters downstream theorems as
an explicit argument, keeping `SectorData` `μFS`-agnostic.
-/

open MeasureTheory Set

namespace CSD
namespace LF2

/-- LF2 sector data. Groups the LF1 ontic setup together with the epistemic
    projection `π` and a `G`-action satisfying `μL`-invariance and
    `π`-equivariance. -/
structure SectorData
    (Sigma P G : Type*)
    [MeasurableSpace Sigma] [Nonempty Sigma]
    [MeasurableSpace P]
    [Group G] where
  /-- Underlying LF1 ontic data (Σ, μL, Φ, Ω0, plus their measurability /
      nonzero-volume / measure-preservation hypotheses). -/
  toOntic      : CSD.LF1.OnticSetup Sigma
  /-- The epistemic projection from ontic state space to the abstract
      projective target. -/
  π            : Sigma → P
  /-- Measurability of the projection. -/
  measurable_π : Measurable π
  /-- The lifted `G`-action on `Σ`, as a family of measurable equivalences. -/
  onticAction  : G → Sigma ≃ᵐ Sigma
  /-- The `G`-action on `P`, as a family of measurable equivalences. -/
  epAction     : G → P ≃ᵐ P
  /-- Liouville invariance: each `onticAction g` preserves `μL`. -/
  hμL_inv      : ∀ g, MeasurePreserving (onticAction g)
                        (toOntic.μL : Measure Sigma)
                        (toOntic.μL : Measure Sigma)
  /-- Equivariance: `π` intertwines the ontic and epistemic actions. -/
  hπ_equiv     : ∀ g x, π (onticAction g x) = epAction g (π x)

namespace SectorData

variable {Sigma P G : Type*}
  [MeasurableSpace Sigma] [Nonempty Sigma]
  [MeasurableSpace P]
  [Group G]
  (D : SectorData Sigma P G)

/-- Convenience re-export of the ontic Liouville measure as a `Measure`. -/
abbrev μL : Measure Sigma := (D.toOntic.μL : Measure Sigma)

end SectorData

end LF2
end CSD
