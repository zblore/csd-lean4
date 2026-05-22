import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Empirical.QM.Gates.TwoQubit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/CSD: Two-qubit gates (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Gates/TwoQubit.lean`).

Three CSD realisability claims, one per gate, plus identity-transport
re-exports. Same template as `Empirical/CSD/Gates/SingleQubit.lean`,
specialised to `N = 2` (Hilbert space `EuclideanSpace ℂ (Fin 4)`).

## LF4 obligations

LF4-todo §13.2 (per gate; same as single-qubit gates, instantiated
at `N = 2`). See `BRIDGE-OBLIGATIONS.md` §2.6.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates
namespace TwoQubit

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for CNOT. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def cnot_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4)),
    ∀ v : EuclideanSpace ℂ (Fin 4),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmCNOT) v

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for SWAP. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def swap_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4)),
    ∀ v : EuclideanSpace ℂ (Fin 4),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmSWAP) v

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for CZ. See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def cz_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 2 (EuclideanSpace ℂ (Fin 4)),
    ∀ v : EuclideanSpace ℂ (Fin 4),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmCZ) v

/-! ## Identity-transport re-exports -/

/-- **CNOT is involutive (re-export).** -/
theorem csd_qmCNOT_mul_self :
    CSD.Empirical.QM.Gates.qmCNOT * CSD.Empirical.QM.Gates.qmCNOT = 1 :=
  CSD.Empirical.QM.Gates.qmCNOT_mul_self

/-- **SWAP is involutive (re-export).** -/
theorem csd_qmSWAP_mul_self :
    CSD.Empirical.QM.Gates.qmSWAP * CSD.Empirical.QM.Gates.qmSWAP = 1 :=
  CSD.Empirical.QM.Gates.qmSWAP_mul_self

/-- **CZ is involutive (re-export).** -/
theorem csd_qmCZ_mul_self :
    CSD.Empirical.QM.Gates.qmCZ * CSD.Empirical.QM.Gates.qmCZ = 1 :=
  CSD.Empirical.QM.Gates.qmCZ_mul_self

end TwoQubit
end Gates
end CSDBridge
end Empirical
end CSD
