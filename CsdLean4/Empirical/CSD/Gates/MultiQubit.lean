import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Empirical.QM.Gates.MultiQubit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/CSD: Multi-qubit gates (CSD-side reading)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Gates/MultiQubit.lean`).

Two CSD realisability claims (Toffoli, Fredkin) on the 3-qubit
space, plus identity-transport re-exports. Same template as
`Empirical/CSD/Gates/{SingleQubit,TwoQubit}.lean`, specialised to
`N = 3` (Hilbert space `EuclideanSpace ℂ (Fin 8)`).

## LF4 obligations

LF4-todo §13.2 per gate. **DISCHARGED 2026-07-19** on `cpSectorData`
(`Gates/MultiQubitDischarge.lean`: `toffoli_/fredkin_realisable_cpSector`), modulo A5;
`U_isometry` derived from the gate ∈ `U(8)`. Honest scope (`PLACEHOLDERS.md §7`): the
bundle type carries no Σ-flow, so this discharges the Prop as-typed, not the
Σ-flow-lift prose (open D1 gap). See `BRIDGE-OBLIGATIONS.md` §2.6, `PLACEHOLDERS.md §1`.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates
namespace MultiQubit

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for Toffoli (CCNOT). See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def toffoli_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 3 (EuclideanSpace ℂ (Fin 8)),
    ∀ v : EuclideanSpace ℂ (Fin 8),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmToffoli) v

/-- **PLACEHOLDER (Prop definition, not proved).**
CSD realisability for Fredkin (CSWAP). See `PLACEHOLDERS.md`. -/
-- TODO(LF4 §13.2): construct a witness bundle for the Kähler `SectorData`.
def fredkin_realisable_for
    (D : CSD.LF2.SectorData SigmaSpace P G) : Prop :=
  ∃ b : CSDUnitaryBundle D 3 (EuclideanSpace ℂ (Fin 8)),
    ∀ v : EuclideanSpace ℂ (Fin 8),
      b.U v = (Matrix.toEuclideanLin CSD.Empirical.QM.Gates.qmFredkin) v

/-! ## Identity-transport re-exports -/

/-- **Toffoli is involutive (re-export).** -/
theorem csd_qmToffoli_mul_self :
    CSD.Empirical.QM.Gates.qmToffoli * CSD.Empirical.QM.Gates.qmToffoli = 1 :=
  CSD.Empirical.QM.Gates.qmToffoli_mul_self

/-- **Fredkin is involutive (re-export).** -/
theorem csd_qmFredkin_mul_self :
    CSD.Empirical.QM.Gates.qmFredkin * CSD.Empirical.QM.Gates.qmFredkin = 1 :=
  CSD.Empirical.QM.Gates.qmFredkin_mul_self

end MultiQubit
end Gates
end CSDBridge
end Empirical
end CSD
