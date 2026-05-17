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
measure construction. Concrete instantiation is LF4+'s job. The reference
measure `μFS` is not a field of `SectorData`; it enters downstream theorems as
an explicit argument, keeping `SectorData` `μFS`-agnostic.
-/

open MeasureTheory Set

namespace CSD
namespace LF2

/-- LF2 sector data. Groups the LF1 ontic setup together with the epistemic
    projection `π` and a `G`-action satisfying `μL`-invariance and
    `π`-equivariance.

    **A5 structural data, not a derivation.** Both `π : SigmaSpace → P` and the
    group `G` are taken as structural inputs. Nothing in `SectorData` constrains
    `π` to project onto the quantum-effective sector specifically: any
    measurable map with the two coherence conditions
    (`μL`-invariance of the ontic action, `π`-equivariance) qualifies.
    Similarly, `G` is any group acting measurably on both spaces with the two
    coherence conditions. The natural reading is `G = SU(N)` acting on `Σ` via
    the lift of its action on `CP^{N-1}`, with `π` the standard projection,
    but no field forces this.

    This labelling carries A5 in Paper B's framing: the physical motivation
    for the quantum-effective sector assumption is a load-bearing external
    input to the corpus, not derived in v1.00. Concrete instantiation
    (`P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))`,
    `G := Matrix.specialUnitaryGroup (Fin N) ℂ`, plus the explicit `π`) is
    deferred to LF4-todo §8. -/
structure SectorData
    (SigmaSpace P G : Type*)
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    [MeasurableSpace P]
    [Group G] where
  /-- Underlying LF1 ontic data (Σ, μL, Φ, Ω0, plus their measurability /
      nonzero-volume / measure-preservation hypotheses). -/
  toOntic      : CSD.LF1.OnticSetup SigmaSpace
  /-- The epistemic projection from ontic state space to the abstract
      projective target. -/
  π            : SigmaSpace → P
  /-- Measurability of the projection. -/
  measurable_π : Measurable π
  /-- The lifted `G`-action on `Σ`, as a family of measurable equivalences. -/
  onticAction     : G → SigmaSpace ≃ᵐ SigmaSpace
  /-- The `G`-action on `P`, as a family of measurable equivalences. -/
  epAction        : G → P ≃ᵐ P
  /-- Identity element of `G` acts as the identity on `Σ`. -/
  onticAction_one : onticAction 1 = MeasurableEquiv.refl SigmaSpace
  /-- Left-action composition on `Σ`: `(g * h) · x = g · (h · x)`.  Recall
      `(e.trans f) x = f (e x)`, so the right-hand side below applies `h` first
      and then `g`, matching the left-action convention. -/
  onticAction_mul : ∀ g h : G,
                      onticAction (g * h) = (onticAction h).trans (onticAction g)
  /-- Identity element of `G` acts as the identity on `P`. -/
  epAction_one    : epAction 1 = MeasurableEquiv.refl P
  /-- Left-action composition on `P`. -/
  epAction_mul    : ∀ g h : G,
                      epAction (g * h) = (epAction h).trans (epAction g)
  /-- Liouville invariance: each `onticAction g` preserves `μL`. -/
  hμL_inv         : ∀ g, MeasurePreserving (onticAction g)
                           (toOntic.μL : Measure SigmaSpace)
                           (toOntic.μL : Measure SigmaSpace)
  /-- Equivariance: `π` intertwines the ontic and epistemic actions. -/
  hπ_equiv        : ∀ g x, π (onticAction g x) = epAction g (π x)

namespace SectorData

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  (D : SectorData SigmaSpace P G)

/-- Convenience re-export of the ontic Liouville measure as a `Measure`. -/
abbrev μL : Measure SigmaSpace := (D.toOntic.μL : Measure SigmaSpace)

end SectorData

end LF2
end CSD
