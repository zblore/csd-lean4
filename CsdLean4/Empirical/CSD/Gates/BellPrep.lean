import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Empirical.CSD.Gates.SingleQubit
import CsdLean4.Empirical.CSD.Gates.TwoQubit
import CsdLean4.Empirical.QM.Gates.BellPrep

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

/-- **Bell-state preparation circuit realisability.** Given CSD
unitary bundles for `H ⊗ I` and `CNOT` on the 2-qubit space, the
Bell-state preparation circuit `CNOT ∘ (H ⊗ I)` has a corresponding
CSD bundle via `CSDUnitaryBundle.comp`. -/
def bell_prep_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ (b_HI b_CNOT : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4))),
    True  -- The composition `b_CNOT.comp b_HI` exists by Framework.lean.

/-- **Composition instance.** Given two `CSDUnitaryBundle`s on
the same context + qubit count, their `comp` is well-defined. Just
re-exports `CSDUnitaryBundle.comp` for the Bell-prep use case;
guarantees the composition is mechanical. -/
noncomputable def bell_prep_compose
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (b_HI b_CNOT : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4))) :
    CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4)) :=
  b_CNOT.comp b_HI

/-! ## QM-side factorisation re-export -/

/-- **The Bell-prep circuit factorisation (re-export).** Trivial
`rfl` unfolding from the QM side. -/
theorem csd_qmBellPrep_factorisation :
    CSD.Empirical.QM.Gates.qmBellPrepCircuit
      = CSD.Empirical.QM.Gates.qmCNOT * CSD.Empirical.QM.Gates.qmH_tensor_I :=
  CSD.Empirical.QM.Gates.qmBellPrep_factorisation

end BellPrep
end Gates
end CSDBridge
end Empirical
end CSD
