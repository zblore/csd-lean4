/-
Copyright (c) 2026 CSD contributors. All rights reserved.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

/-!
# W4: the finite-dimensional obstruction to exact canonical commutation

For finite complex matrices the trace of a commutator vanishes,
`trace (Q * P - P * Q) = 0`, because `trace (Q * P) = trace (P * Q)`. A scalar
multiple of the identity has trace `c * card`, which is nonzero exactly when
`c * card ≠ 0`. Hence no pair of finite matrices satisfies the exact canonical
commutation relation `Q * P - P * Q = c • 1` when `c * card ≠ 0`. The physical
CCR `[Q, P] = i ℏ · 1` is the instance `c = i ℏ`, nonzero for `ℏ ≠ 0` and
`card > 0`.

## CSD reading

Finite operational sectors cannot contain exact continuum canonical commutation
structure. The infinite-dimensional Hilbert space of continuous-variable quantum
mechanics is the ideal completion of a family of finite operational sectors;
position and momentum are approximate, coarse-grained, limiting observables in a
finite regime, not primitive finite-sector observables. The trace obstruction is
the precise sense in which exact `[Q, P] = i ℏ` is unavailable at finite `N`.

## Honest scope (load-bearing)

W4 proves **only** that exact continuum canonical commutation cannot be
represented in finite dimension. It does **not** derive continuous-variable
quantum mechanics, does **not** construct finite position/momentum
approximations, and does **not** claim CSD has derived CV-QM. It is the
obstruction result that motivates the finite-sector reading, nothing more.

## Category

Cat-1: the trace lemmas are CSD-free general facts about finite complex
matrices. The CSD interpretation lives only in this docstring.

## Main results

- `trace_commutator_eq_zero` : `trace (Q * P - P * Q) = 0`.
- `trace_scalar_identity` : `trace (c • 1) = c * Fintype.card n`.
- `no_exact_finite_ccr` : `c * card ≠ 0 → Q * P - P * Q ≠ c • 1` (the headline).
- `no_exact_finite_ccr_ihbar` : the physics corollary at `c = i ℏ`.

## Mathlib lemmas used

`Matrix.trace_sub`, `Matrix.trace_mul_comm`, `Matrix.trace_smul`,
`Matrix.trace_one`.
-/

namespace CSD.CV

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The trace of a finite-matrix commutator vanishes: `trace (Q P - P Q) = 0`,
since `trace (Q P) = trace (P Q)` (`Matrix.trace_mul_comm`). -/
theorem trace_commutator_eq_zero (Q P : Matrix n n ℂ) :
    Matrix.trace (Q * P - P * Q) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The trace of a scalar multiple of the identity: `trace (c • 1) = c * card`.
Uses `Matrix.trace_smul` and `Matrix.trace_one` (with `Fintype.card n` cast into
`ℂ`); the `•` on `ℂ` collapses to multiplication via `smul_eq_mul`. -/
theorem trace_scalar_identity (c : ℂ) :
    Matrix.trace (c • (1 : Matrix n n ℂ)) = c * (Fintype.card n : ℂ) := by
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]

/-- **The finite-dimensional CCR obstruction.** For finite complex matrices, no
`Q, P` satisfy the exact canonical commutation relation `Q P - P Q = c • 1`
whenever `c * card ≠ 0`. Proof by contradiction: taking traces of both sides,
the left side is `0` (`trace_commutator_eq_zero`) while the right side is
`c * card` (`trace_scalar_identity`), contradicting `hc`.

The hypothesis is satisfiable (e.g. `c = 1`, `card ≥ 1`) and the conclusion is a
genuine inequality, so this is non-vacuous. -/
theorem no_exact_finite_ccr (Q P : Matrix n n ℂ) {c : ℂ}
    (hc : c * (Fintype.card n : ℂ) ≠ 0) :
    Q * P - P * Q ≠ c • (1 : Matrix n n ℂ) := by
  intro heq
  apply hc
  rw [← trace_scalar_identity (n := n) c, ← heq, trace_commutator_eq_zero]

/-- **The physics corollary.** No finite complex matrices `Q, P` satisfy the
exact physical CCR `[Q, P] = i ℏ · 1` when `ℏ ≠ 0` and the dimension is nonzero.
Instance of `no_exact_finite_ccr` at `c = i ℏ`; `hc` follows from `Complex.I ≠ 0`,
`hhbar`, and `hN` by `mul_ne_zero`. -/
theorem no_exact_finite_ccr_ihbar (Q P : Matrix n n ℂ) {hbar : ℂ}
    (hhbar : hbar ≠ 0) (hN : (Fintype.card n : ℂ) ≠ 0) :
    Q * P - P * Q ≠ (Complex.I * hbar) • (1 : Matrix n n ℂ) :=
  no_exact_finite_ccr Q P
    (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hhbar) hN)

end CSD.CV
