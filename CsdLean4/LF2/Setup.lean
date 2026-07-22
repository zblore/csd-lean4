/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF1.Setup
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# LF2 Setup: Sector data

**Category:** 3-Local (LF2 `SectorData`: LF1 `OnticSetup` plus projective target, projection, and group action).

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

@[expose] public section

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
    deferred to LF4-todo §8.

    **MulAction-based encoding.** The `G`-action is encoded via Mathlib's
    `MulAction G _` typeclasses on both `SigmaSpace` and `P`, with transitivity
    encoded by `MulAction.IsPretransitive G P` (the Mathlib-idiomatic spelling
    of "any two points in `P` are related by some group element"). This replaces
    the earlier `onticAction : G → _ ≃ᵐ _` field encoding plus the four
    `_one` / `_mul` coherence fields and the `epAction_transitive` field: the
    group-action laws follow from the `MulAction` typeclass, and transitivity
    from `IsPretransitive`. Measurability of each action is supplied as
    structure fields (`measurable_smul_σ`, `measurable_smul_P`). -/
structure SectorData
    (SigmaSpace P G : Type*)
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    [MeasurableSpace P]
    [Group G]
    [MulAction G SigmaSpace] [MulAction G P]
    [MulAction.IsPretransitive G P] where
  /-- Underlying LF1 ontic data (Σ, μL, Φ, Ω0, plus their measurability /
      nonzero-volume / measure-preservation hypotheses). -/
  toOntic      : CSD.LF1.OnticSetup SigmaSpace
  /-- The epistemic projection from ontic state space to the abstract
      projective target. -/
  π            : SigmaSpace → P
  /-- Measurability of the projection. -/
  measurable_π : Measurable π
  /-- Measurability of each ontic action map `g • · : SigmaSpace → SigmaSpace`. -/
  measurable_smul_σ : ∀ g : G, Measurable ((g • ·) : SigmaSpace → SigmaSpace)
  /-- Measurability of each epistemic action map `g • · : P → P`. -/
  measurable_smul_P : ∀ g : G, Measurable ((g • ·) : P → P)
  /-- Liouville invariance: each ontic action `g • ·` preserves `μL`. -/
  hμL_inv         : ∀ g : G, MeasurePreserving ((g • ·) : SigmaSpace → SigmaSpace)
                           (toOntic.μL : Measure SigmaSpace)
                           (toOntic.μL : Measure SigmaSpace)
  /-- Equivariance: `π` intertwines the ontic and epistemic actions. -/
  hπ_equiv        : ∀ (g : G) (x : SigmaSpace), π (g • x) = g • π x

namespace SectorData

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]
  (D : SectorData SigmaSpace P G)

/-- Convenience re-export of the ontic Liouville measure as a `Measure`. -/
abbrev μL : Measure SigmaSpace := (D.toOntic.μL : Measure SigmaSpace)

end SectorData

end LF2
end CSD
