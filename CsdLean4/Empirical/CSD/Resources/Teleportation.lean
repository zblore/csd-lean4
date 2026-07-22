/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Resources.Teleportation

/-!
# Empirical/CSD: Quantum teleportation (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Resources/Teleportation.lean`).

Pairs with `Empirical/QM/Resources/Teleportation.lean` (Bennett et al. 1993). The QM
file proves the branch-conditional identity: for each two-bit Bell-measurement outcome,
Bob's Pauli correction `{I, Z, X, ZX}` returns the input qubit `|ψ⟩` exactly. No CSD
ontology in the proof.

This file states the **CSD reading**: the teleportation protocol, run through the CSD
substrate, recovers the input state in every measurement branch. The shared entangled
resource and the Bell measurement are CSD objects; the four corrections are CSD-realised
unitaries; per branch, the corrected output coincides with the input.

## Polarity (transport, not negative-existential)

A positive-content transport: the bundle's branch identities hold by direct appeal to
the QM-side theorem. (As on the QM side, this is the *branch-conditional* layer; the
measurement-collapse step and the no-signalling marginal need the LF5 measurement-update
notion, documented in the QM file.)

## LF4 obligations carried

The bundle's load-bearing content is the **realisability of the input state, the shared
entangled pair, and the four Pauli corrections through the CSD ontic substrate** (state
realisability LF4-todo §14 + correction-unitary realisability LF4-todo §13). Pre-LF4 the
ontic realisation is implicit in the bundle's existence; post-LF4 it follows from the
concrete `SectorData` instantiation. See `BRIDGE-OBLIGATIONS.md` and `PLACEHOLDERS.md §7`.

## Source

Bennett, Brassard, Crépeau, Jozsa, Peres, Wootters 1993, *Phys. Rev. Lett.* **70**, 1895.
-/

open Matrix

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Teleportation

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**
Fields are Hilbert-side; the state/correction-correspondence claim is prose-only.

**CSD teleportation bundle.** Structural carrier for the input-qubit amplitudes `α, β`
of a teleportation run, packaged in a `SectorData D` context. Extends
`CSDBridge.Context D`; the branch identities are supplied by the QM-side theorem applied
to `α, β`.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDTeleportationBundle`, callers implicitly assert that the
input qubit, the shared `|Φ⁺⟩` resource, and the four Pauli corrections are realised
through the CSD substrate of `D`.

**Status: load-bearing, externally supplied, undischarged.** LF4-todo §14 (states) + §13
(corrections). -/
structure CSDTeleportationBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The input-qubit amplitudes. -/
  α  : ℂ
  β  : ℂ

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's amplitudes and calls the QM-side
theorem.** See `PLACEHOLDERS.md §7`.

**Teleportation recovers the input in the CSD reading.** For any CSD teleportation
bundle on a `SectorData D`, each Bell-measurement branch's Pauli correction returns the
input qubit `|ψ⟩ = α|0⟩ + β|1⟩` exactly. Reduces to the QM-side
`Empirical.QM.Teleportation.teleportation_branch_recovers_input` by direct field
extraction.

**Experimental verification:** Bouwmeester et al. 1997, *Nature* **390**, 575
(photonic); Riebe et al. 2004, Barrett et al. 2004 (trapped ions). -/
theorem csd_teleportation_branch_recovers_input
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (b : CSDTeleportationBundle D) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (CSD.Empirical.QM.Teleportation.bobPhiPlus b.α b.β)
      = CSD.Empirical.QM.Teleportation.teleInput b.α b.β ∧
    (Matrix.toEuclideanLin CSD.Empirical.QM.Teleportation.teleZ)
        (CSD.Empirical.QM.Teleportation.bobPhiMinus b.α b.β)
      = CSD.Empirical.QM.Teleportation.teleInput b.α b.β ∧
    (Matrix.toEuclideanLin CSD.Empirical.QM.Teleportation.teleX)
        (CSD.Empirical.QM.Teleportation.bobPsiPlus b.α b.β)
      = CSD.Empirical.QM.Teleportation.teleInput b.α b.β ∧
    (Matrix.toEuclideanLin CSD.Empirical.QM.Teleportation.teleZX)
        (CSD.Empirical.QM.Teleportation.bobPsiMinus b.α b.β)
      = CSD.Empirical.QM.Teleportation.teleInput b.α b.β :=
  CSD.Empirical.QM.Teleportation.teleportation_branch_recovers_input b.α b.β

end Teleportation
end CSDBridge
end Empirical
end CSD
