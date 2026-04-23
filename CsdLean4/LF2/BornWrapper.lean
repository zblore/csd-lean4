import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Order

/-!
# LF2 Born-Weight Wrapper

Spec §5. Packages the finite-dimensional probability assignment using
concrete matrix-based `Effect`/`DensityOperator` structures, an imported
`busch_effect_gleason` axiom, and (downstream phases) a proved Born quadratic
form for rank-1 outcomes on pure preparations.

This file is built incrementally; see the companion plan at
`specs/LF2-plan.md` §2.4.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ}

/-- **Effect on an N-dimensional complex Hilbert space.** A Hermitian matrix
    with `0 ≤ E` and `E ≤ I` (both expressed via `PosSemidef`). -/
structure Effect (N : ℕ) where
  /-- Underlying matrix. -/
  M           : Matrix (Fin N) (Fin N) ℂ
  /-- `E` is Hermitian. -/
  isHermitian : M.IsHermitian
  /-- `0 ≤ E`. -/
  nonneg      : M.PosSemidef
  /-- `E ≤ I`, i.e. `I - E` is PSD. -/
  le_one      : (1 - M).PosSemidef

/-- **Density operator on an N-dimensional complex Hilbert space.** A Hermitian
    PSD matrix with trace 1. -/
structure DensityOperator (N : ℕ) where
  /-- Underlying matrix. -/
  M           : Matrix (Fin N) (Fin N) ℂ
  /-- `ρ` is Hermitian. -/
  isHermitian : M.IsHermitian
  /-- `0 ≤ ρ`. -/
  nonneg      : M.PosSemidef
  /-- `Tr(ρ) = 1`. -/
  trace_one   : M.trace = 1

/-- **Trace-form pairing.** `Tr(ρ · E)` as a real number. The trace of a
    product of Hermitian matrices is real (self-adjoint), so taking the real
    part is not an approximation — it is an extraction. -/
noncomputable def traceForm (ρ : DensityOperator N) (E : Effect N) : ℝ :=
  RCLike.re ((ρ.M * E.M).trace)

end LF2
end CSD
