/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.NoBroadcasting

/-!
# Empirical/CSD: No-broadcasting (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/NoBroadcasting.lean`).

Pairs with `Empirical/QM/NoBroadcasting.lean` (Barnum-Caves-Fuchs-Jozsa-Schumacher
1996). The QM file states the pure-marginal core as a matrix theorem: a bipartite PSD
operator `ρ` whose first-factor marginal is a pure state `|ψ⟩⟨ψ|` is confined to that
pure sector, `(|ψ⟩⟨ψ| ⊗ I)·ρ·(|ψ⟩⟨ψ| ⊗ I) = ρ`. No CSD ontology in the proof.

This file states the **CSD volume-ratio reading**: the same confinement applied to a
CSD-realised bipartite state. The would-be broadcaster's joint ontic state, having the
pure `ψ`-sector as its system marginal, has no support outside that one-dimensional
sector, so there is no room for an independent second copy. This is the structural
squeeze behind "broadcasting a pure state would clone it" carried into the CSD substrate.

## Polarity (transport, not negative-existential)

Like `Uncertainty` and unlike `NoCloning`, this is a positive-content transport: every
bundle satisfies the confinement identity, by direct appeal to the QM-side theorem.

## LF4 obligations carried

The bundle's load-bearing content is the **realisability of the bipartite density
operator `ρ` (and its pure marginal) through the CSD ontic substrate** — the
state/operator correspondence family (LF4-todo §14): the Hilbert-side `ρ` arises as a
CSD object on `Σ` whose system-marginal reduction is the pure `ψ`-sector. Pre-LF4 the
ontic realisation is implicit in the bundle's existence; post-LF4 it follows from the
concrete `SectorData` instantiation. See `BRIDGE-OBLIGATIONS.md` and `PLACEHOLDERS.md §7`
(the bundle's fields are Hilbert-side; the ontic correspondence is prose-only).

## Source

Barnum, Caves, Fuchs, Jozsa, Schumacher 1996, *Phys. Rev. Lett.* **76**, 2818.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace CSDBridge
namespace NoBroadcasting

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**
Fields are Hilbert-side; the state/operator-correspondence claim is prose-only.

**CSD no-broadcasting bundle.** Structural carrier for a bipartite PSD operator `ρ`
with a pure first-factor marginal `|ψ⟩⟨ψ|`, packaged in a `SectorData D` context.
Extends `CSDBridge.Context D` (the LF2-level discharge data) and adds the Hilbert-side
state structure. The fields match the argument list of
`Empirical.QM.NoBroadcasting.pure_marginal_confinement` exactly, so the reduction in
`csd_no_broadcasting` is mechanical.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDNoBroadcastingBundle`, callers implicitly assert that `ρ`
arises as a CSD bipartite state on the substrate of `D`, with its system-marginal
reduction realising the pure `ψ`-sector.

**Status: load-bearing, externally supplied, undischarged.** LF4-todo §14. -/
structure CSDNoBroadcastingBundle
    (D : CSD.LF2.SectorData SigmaSpace P G) (N n : ℕ)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The pure system state whose marginal confines `ρ`. -/
  ψ      : EuclideanSpace ℂ (Fin N)
  hψ     : ‖ψ‖ = 1
  /-- The bipartite density operator of the prospective broadcaster. -/
  ρ      : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ
  hρ     : ρ.PosSemidef
  /-- The first-factor marginal is the pure state `|ψ⟩⟨ψ|`. -/
  hmarg  : Matrix.traceRight ρ = CSD.LF2.outerProduct ψ

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's Hilbert-side fields and calls
the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No-broadcasting in the CSD reading.** For any CSD no-broadcasting bundle on a
`SectorData D`, the joint state is confined to the pure `ψ`-sector:
`(|ψ⟩⟨ψ| ⊗ I)·ρ·(|ψ⟩⟨ψ| ⊗ I) = ρ`. Reduces to the QM-side
`Empirical.QM.NoBroadcasting.pure_marginal_confinement` by direct field extraction.

**Experimental verification:** the impossibility underlies the security of
prepare-and-measure QKD; the marginal-confinement core is checked in any
state-tomography reconstruction of a broadcasting attempt. -/
theorem csd_no_broadcasting
    {D : CSD.LF2.SectorData SigmaSpace P G} {N n : ℕ}
    (b : CSDNoBroadcastingBundle D N n) :
    (CSD.LF2.outerProduct b.ψ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * b.ρ
        * (CSD.LF2.outerProduct b.ψ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = b.ρ :=
  CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement b.ψ b.hψ b.ρ b.hρ b.hmarg

end NoBroadcasting
end CSDBridge
end Empirical
end CSD
