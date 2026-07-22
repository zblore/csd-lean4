/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# LF2: reduced density operators via partial trace

**Category:** 3-Local.

An index-parametric density-operator structure `DensityOperatorIx ι` (Hermitian,
PSD, trace one, on `Matrix ι ι ℂ`) and its **reduced density operator**
`DensityOperatorIx.reduced : DensityOperatorIx (m × n) → DensityOperatorIx m`,
obtained by tracing out the second tensor factor
(`CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean`).

This is the object the no-communication theorem in reduced-density form (E3b) and
no-broadcasting (E2) consume: "Bob's reduced state" of a bipartite density
operator. The three reduced-operator structure fields discharge directly from the
partial-trace API:

- `isHermitian` ← `Matrix.IsHermitian.traceRight`,
- `nonneg`      ← `Matrix.PosSemidef.traceRight`,
- `trace_one`   ← `Matrix.trace_traceRight` + the original `trace_one`.

**Why a new structure** (index-parametric `ι`, vs LF2's `Fin N`-indexed
`DensityOperator`): partial trace lives natively on a product index `m × n`, so a
`Fin N`-only structure would force a `Fin (m*n) ≃ Fin m × Fin n` reindex through
every call. `DensityOperatorIx ι` is the more natural object and avoids that
friction (decision recorded 2026-06-01, `specs/partial-trace-plan.md`). The two
structures agree under `finProdFinEquiv` should a bridge ever be needed.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

/-- **Index-parametric density operator.** A Hermitian, positive-semidefinite,
trace-one matrix on an arbitrary finite index `ι`. Generalises the `Fin N`-indexed
`DensityOperator` so that partial traces (which land on a sub-index) stay inside
the structure. -/
structure DensityOperatorIx (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Underlying matrix. -/
  M           : Matrix ι ι ℂ
  /-- `ρ` is Hermitian. -/
  isHermitian : M.IsHermitian
  /-- `0 ≤ ρ`. -/
  nonneg      : M.PosSemidef
  /-- `Tr(ρ) = 1`. -/
  trace_one   : M.trace = 1

namespace DensityOperatorIx

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Reduced density operator (Bob's state).** Trace out the second tensor factor
`n` of a bipartite density operator on `m × n`, leaving a density operator on `m`.
All three fields discharge from the partial-trace API. -/
noncomputable def reduced (ρ : DensityOperatorIx (m × n)) : DensityOperatorIx m where
  M           := Matrix.traceRight ρ.M
  isHermitian := ρ.isHermitian.traceRight
  nonneg      := ρ.nonneg.traceRight
  trace_one   := by rw [Matrix.trace_traceRight]; exact ρ.trace_one

/-- **Reduced density operator (Alice's state).** Trace out the first factor `m`,
leaving a density operator on `n`. -/
noncomputable def reducedLeft (ρ : DensityOperatorIx (m × n)) : DensityOperatorIx n where
  M           := Matrix.traceLeft ρ.M
  isHermitian := ρ.isHermitian.traceLeft
  nonneg      := ρ.nonneg.traceLeft
  trace_one   := by rw [Matrix.trace_traceLeft]; exact ρ.trace_one

@[simp]
theorem reduced_M (ρ : DensityOperatorIx (m × n)) :
    (reduced ρ).M = Matrix.traceRight ρ.M := rfl

@[simp]
theorem reducedLeft_M (ρ : DensityOperatorIx (m × n)) :
    (reducedLeft ρ).M = Matrix.traceLeft ρ.M := rfl

end DensityOperatorIx
end LF2
end CSD
