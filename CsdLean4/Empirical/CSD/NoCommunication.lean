/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.NoCommunication

/-!
# Empirical/CSD: No-communication / no-signalling (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/NoCommunication.lean`).

Pairs with `Empirical/QM/NoCommunication.lean` (Ghirardi-Rimini-Weber 1980; Eberhard
1978). The QM file states the marginal form as a matrix theorem: a local unitary
`U ⊗ I` on Alice's factor leaves every Bob-side expectation `⟨ψ, (I ⊗ Q) ψ⟩` invariant.
No CSD ontology in the proof.

This file states the **CSD volume-ratio reading**: Alice's local CSD operation cannot
shift Bob's measured statistics. Bob's outcome frequencies are volume ratios on `Σ`
that are invariant under any Alice-side unitary realised through the substrate, so no
information is transmitted by Alice's choice of local operation.

## Polarity (transport, not negative-existential)

A positive-content transport: every bundle satisfies the Bob-expectation invariance,
by direct appeal to the QM-side theorem.

## LF4 obligations carried

The bundle's load-bearing content is the **realisability of Alice's local unitary
`U ⊗ I` as a measure-preserving π-equivariant flow on the substrate (LF4-todo §13) and
of Bob's observable `Q` as a CSD observable (LF4-todo §14)**. Pre-LF4 the ontic
realisation is implicit in the bundle's existence; post-LF4 it follows from the concrete
`SectorData` instantiation. See `BRIDGE-OBLIGATIONS.md` and `PLACEHOLDERS.md §7` (the
bundle's fields are Hilbert-side; the ontic correspondence is prose-only).

## Source

Ghirardi-Rimini-Weber 1980, *Lett. Nuovo Cimento* **27**, 293; Eberhard 1978.
-/

open Matrix ComplexConjugate
open scoped Kronecker

namespace CSD
namespace Empirical
namespace CSDBridge
namespace NoCommunication

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**
Fields are Hilbert-side; the operation/observable-correspondence claim is prose-only.

**CSD no-communication bundle.** Structural carrier for a unitary Alice-side operation
`U`, a Bob-side observable `Q`, and a bipartite state `ψ`, packaged in a `SectorData D`
context. Extends `CSDBridge.Context D` and adds the Hilbert-side structure. The fields
match the argument list of `Empirical.QM.NoCommunication.bob_expectation_invariant`
exactly, so the reduction in `csd_no_communication` is mechanical.

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDNoCommunicationBundle`, callers implicitly assert that `U`
arises as a measure-preserving π-equivariant flow on Alice's factor of the substrate,
and `Q` as a CSD observable on Bob's factor.

**Status: load-bearing, externally supplied, undischarged.** LF4-todo §13 (operation) +
§14 (observable). -/
structure CSDNoCommunicationBundle
    (D : CSD.LF2.SectorData SigmaSpace P G) (m n : ℕ)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- Alice's local unitary. -/
  U   : Matrix (Fin m) (Fin m) ℂ
  /-- `U` is unitary. -/
  hU  : Uᴴ * U = 1
  /-- Bob's observable. -/
  Q   : Matrix (Fin n) (Fin n) ℂ
  /-- The bipartite state. -/
  ψ   : EuclideanSpace ℂ (Fin m × Fin n)

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's Hilbert-side fields and calls
the QM-side theorem.** See `PLACEHOLDERS.md §7`.

**No-communication in the CSD reading.** For any CSD no-communication bundle on a
`SectorData D`, Bob's measured expectation of `Q` is invariant under Alice's local
unitary: conjugating the state by `U ⊗ I` leaves `Re⟨ψ, (I ⊗ Q) ψ⟩` unchanged. Reduces
to the QM-side `Empirical.QM.NoCommunication.bob_expectation_invariant` by direct field
extraction.

**Experimental verification:** every loophole-free Bell test checks no-signalling as a
consistency condition (Hensen 2015, Giustina 2015, Shalm 2015). -/
theorem csd_no_communication
    {D : CSD.LF2.SectorData SigmaSpace P G} {m n : ℕ}
    (b : CSDNoCommunicationBundle D m n) :
    (inner ℂ (Matrix.toEuclideanLin (CSD.Empirical.QM.NoCommunication.aliceOp b.U) b.ψ)
        (Matrix.toEuclideanLin (CSD.Empirical.QM.NoCommunication.bobOp b.Q)
          (Matrix.toEuclideanLin (CSD.Empirical.QM.NoCommunication.aliceOp b.U) b.ψ))).re
      = (inner ℂ b.ψ
          (Matrix.toEuclideanLin (CSD.Empirical.QM.NoCommunication.bobOp b.Q) b.ψ)).re :=
  CSD.Empirical.QM.NoCommunication.bob_expectation_invariant b.U b.Q b.hU b.ψ

end NoCommunication
end CSDBridge
end Empirical
end CSD
