/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Empirical.QM.Gates.SingleQubit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/CSD: Single-qubit gates (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Gates/SingleQubit.lean`).

Pairs with `Empirical/QM/Gates/SingleQubit.lean` (Hadamard, Phase S,
Phase T). The QM file states the gate matrices and their identities
(`H * H = 1`, `S² = Z`, `T² = S`) as pure linear-algebra theorems
on `Matrix (Fin 2) (Fin 2) ℂ`.

This file states the **CSD volume-ratio reading**: for each of the
three gates, the existence of a `CSDUnitaryBundle` whose carried
unitary equals the gate's Hilbert-space action. Pre-LF4 the bundle
is hypothesis-supplied; post-LF4 it is discharged via LF4-todo §13.2.

## Polarity (positive-existence-conditional-on-LF4)

For each gate, the CSD-side claim is the **existence** of a
`CSDUnitaryBundle D 1 (EuclideanSpace ℂ (Fin 2))` whose `U` agrees
with the gate's projective action. This is a new polarity in the
architecture (the four Tranche 0 companions used negative-existential
or positive-frequency forms).

The bundle's existence asserts the LF4-§13.2 obligation: the
Hilbert-space unitary arises as the projective-action lift of a
measure-preserving π-equivariant flow on Σ.

## What's in this file

- Three `gate_realisable_for` statements (Hadamard, Phase S, Phase T)
  expressing the LF4-§13.2 obligation per gate as a Prop.
- Three identity-transport lemmas showing the QM-side identities
  (`H * H = 1`, `S² = Z`, `T² = S`) lift through any bundle.

No theorems with empirical content beyond what the QM-side file
already establishes; this file is a structural interpretation layer.

## LF4 obligations carried

All three gates carry the same LF4-§13.2 obligation: the gate's
Hilbert-space unitary is the projective-action lift of a
measure-preserving π-equivariant flow on Σ.

**Status: DISCHARGED 2026-07-19** on the concrete `cpSectorData`
(`Gates/SingleQubitDischarge.lean`: `hadamard_/phaseS_/phaseT_realisable_cpSector`),
modulo A5 (the posited sector). Each gate's action is a genuine `CSDUnitaryBundle`
whose `U_isometry` is derived from the gate lying in `U(2)`. Honest scope: the bundle
type carries `U` + `U_isometry` + a `Context`, not a Σ-flow (`PLACEHOLDERS.md §7`), so
the Σ-flow-lift prose reading is the open D1 gap, not established here.
LF4-todo §13.2.

See `BRIDGE-OBLIGATIONS.md` §2.6 for the canonical ledger row.

## Honest reading

The CSD-side gate readings do not establish realisability by an
independent ontic-level construction. They assert the realisability
as a structural commitment carried by the `CSDUnitaryBundle`
existence claim. Post-LF4, the bundle becomes constructible from
the concrete Kähler `SectorData` via LF4-todo §13.2's discharge.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates
namespace SingleQubit

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for the Hadamard gate. The QM-side
`CSD.Empirical.QM.Gates.qmH` matrix admits a `CSDUnitaryBundle D 1 _`
realisation under the Kähler `SectorData D`.

**Status: claim-shaped, undischarged.** This is a `Prop` definition,
not a theorem. Pre-LF4 there is no construction of any `D` for which
`hadamard_realisable_for D` holds; the claim is recorded as an
LF4-§13.2 obligation. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def hadamard_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 1 (EuclideanSpace ℂ (Fin 2)),
    ∀ v : EuclideanSpace ℂ (Fin 2),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmH) v

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for the Phase S gate. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def phaseS_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 1 (EuclideanSpace ℂ (Fin 2)),
    ∀ v : EuclideanSpace ℂ (Fin 2),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmS) v

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for the Phase T gate. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def phaseT_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 1 (EuclideanSpace ℂ (Fin 2)),
    ∀ v : EuclideanSpace ℂ (Fin 2),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmT) v

/-! ## Identity-transport lemmas (re-exports of QM-side identities)

The QM-side identities `H * H = 1`, `S² = Z`, `T² = S` hold
identically in the matrix algebra and need no transport for their
statement. We re-export them here in the CSD namespace for symmetry
with the four Tranche 0 retrofit companions' re-export pattern. -/

/-- **Hadamard is involutive (re-export).** `H * H = 1` from the
QM-side. -/
theorem csd_qmH_mul_self :
    CSD.Empirical.QM.Gates.qmH * CSD.Empirical.QM.Gates.qmH = 1 :=
  CSD.Empirical.QM.Gates.qmH_mul_self

/-- **Phase S squared equals Z (re-export).** -/
theorem csd_qmS_sq :
    CSD.Empirical.QM.Gates.qmS * CSD.Empirical.QM.Gates.qmS
      = CSD.Empirical.QM.Gates.qmZ :=
  CSD.Empirical.QM.Gates.qmS_sq

/-- **Phase T squared equals S (re-export).** -/
theorem csd_qmT_sq :
    CSD.Empirical.QM.Gates.qmT * CSD.Empirical.QM.Gates.qmT
      = CSD.Empirical.QM.Gates.qmS :=
  CSD.Empirical.QM.Gates.qmT_sq

end SingleQubit
end Gates
end CSDBridge
end Empirical
end CSD
