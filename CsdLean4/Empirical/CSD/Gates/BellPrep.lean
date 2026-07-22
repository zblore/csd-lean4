/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Gates.Framework
public import CsdLean4.Empirical.CSD.Gates.SingleQubit
public import CsdLean4.Empirical.CSD.Gates.TwoQubit
public import CsdLean4.Empirical.QM.Gates.BellPrep

/-!
# Empirical/CSD: Bell-state preparation circuit (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Gates/BellPrep.lean`).

Tests the `CSDUnitaryBundle.comp` composition pattern: a Hadamard
bundle on qubit 0 composes with a CNOT bundle on qubits (0, 1) to
yield a CSD bundle for the full Bell-state preparation circuit.

## What this file shows

Given two CSD unitary bundles `b_H : CSDUnitaryBundle D 2 H_4` (the
Hadamard ⊗ Identity bundle on the 2-qubit space) and
`b_CNOT : CSDUnitaryBundle D 2 H_4` (the CNOT bundle), their
composition `b_CNOT.comp b_H` is a CSD bundle for the Bell-state
preparation circuit `CNOT ∘ (H ⊗ I)`.

## LF4 obligations

Same per-gate LF4-todo §13.2 obligations as the individual gates.
The composition does not add a new obligation — it inherits the
two underlying gates' obligations via `CSDUnitaryBundle.comp`.

## Honest reading

This file tests the composition lemma `CSDUnitaryBundle.comp` from
`Empirical/CSD/Gates/Framework.lean`. The Hilbert-side identity
`(CNOT ∘ (H ⊗ I)) |00⟩ = |Φ⁺⟩` is established (or, in this commit,
declared but deferred) on the QM side and not re-derived here. The
CSD-side content is the bundle-composition structure plus the
existence-conditional-on-LF4 commitment that the resulting bundle's
`U` is ontic-realisable.
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates
namespace BellPrep

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **PLACEHOLDER (Prop definition, not proved).**

Bell-state preparation circuit realisability: there exist CSD
unitary bundles for the Hadamard-on-qubit-0 operation `H ⊗ I` and
for `CNOT`, whose `U` fields agree with the QM-side gate matrices.
The bundle composition `b_CNOT.comp b_HI` then realises the
Bell-state preparation circuit.

**Status: DISCHARGED 2026-07-19** on the concrete `cpSectorData`
(`Gates/BellPrepDischarge.lean`: `bell_prep_realisable_cpSector`), modulo A5.
Both bundle existences (`H ⊗ I` and `CNOT`) are supplied with `U` the gate action
and `U_isometry` derived from `U(4)` membership. This is the ninth and last of the
gate realisability Props to be discharged. Honest scope (`PLACEHOLDERS.md §7`): the
bundle type carries `U` + `U_isometry` + a `Context`, not a Σ-flow, so this
discharges the Prop *as typed*, not the Σ-flow-lift prose (the open D1 gap). See
`PLACEHOLDERS.md §1` for the canonical ledger.

The earlier formulation `∃ b_HI b_CNOT, True` was a vacuous Prop
(satisfied by any two bundles); rewritten 2026-05-22 to constrain
both bundles' `U` to the QM-side matrices, making the Prop
non-vacuous. -/
def bell_prep_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ (b_HI b_CNOT : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4))),
    (∀ v, b_HI.U v
        = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmH_tensor_I) v) ∧
    (∀ v, b_CNOT.U v
        = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmCNOT) v)

/-- **Composition instance.** Given two `CSDUnitaryBundle`s on
the same context + qubit count, their `comp` is well-defined. Just
re-exports `CSDUnitaryBundle.comp` for the Bell-prep use case;
guarantees the composition is mechanical. -/
noncomputable def bell_prep_compose
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (b_HI b_CNOT : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4))) :
    CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4)) :=
  b_CNOT.comp b_HI

/-! ## QM-side re-exports -/

/-- **TRANSPORT-ONLY: re-export of the QM-side factorisation handle.**
Definitional unfold; see `PLACEHOLDERS.md §3`. -/
theorem csd_qmBellPrep_factorisation :
    CSD.Empirical.QM.Gates.qmBellPrepCircuit
      = CSD.Empirical.QM.Gates.qmCNOT * CSD.Empirical.QM.Gates.qmH_tensor_I :=
  CSD.Empirical.QM.Gates.qmBellPrep_factorisation

/-- **TRANSPORT-ONLY: re-export of the QM-side Bell-prep headline
identity.** `(CNOT ∘ (H ⊗ I)) |00⟩ = |Φ⁺⟩`; proof body in
`Empirical/QM/Gates/BellPrep.lean`. -/
theorem csd_qmBellPrep_yields_phiplus :
    (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmBellPrepCircuit)
        CSD.Empirical.QM.Gates.qmKet00
      = CSD.Empirical.QM.Gates.qmKetPhiPlus :=
  CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus

end BellPrep
end Gates
end CSDBridge
end Empirical
end CSD
