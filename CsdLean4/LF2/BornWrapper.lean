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

namespace Effect

/-- The identity effect `I`. Represents the trivial always-true measurement
    outcome. -/
noncomputable def one : Effect N where
  M           := 1
  isHermitian := Matrix.isHermitian_one
  nonneg      := Matrix.PosSemidef.one
  le_one      := by simpa [sub_self] using (Matrix.PosSemidef.zero (n := Fin N) (R := ℂ))

/-- The zero effect. Represents the trivial always-false measurement outcome. -/
noncomputable def zero : Effect N where
  M           := 0
  isHermitian := Matrix.isHermitian_zero
  nonneg      := Matrix.PosSemidef.zero
  le_one      := by simpa [sub_zero] using (Matrix.PosSemidef.one (n := Fin N) (R := ℂ))

/-- **Conditional sum of effects.** If `E`, `F` are effects and `E + F ≤ I`,
    their sum is again an effect. Hermitian-ness and PSD of the sum are
    automatic (Hermitian matrices are closed under addition, PSD matrices
    form a convex cone); only `le_one` is a genuine precondition — hence its
    role as an explicit hypothesis. -/
noncomputable def add (E F : Effect N)
    (hLe : (1 - (E.M + F.M)).PosSemidef) : Effect N where
  M           := E.M + F.M
  isHermitian := E.isHermitian.add F.isHermitian
  nonneg      := E.nonneg.add F.nonneg
  le_one      := hLe

end Effect

/-- **Operational consistency package (spec Definition 5.1).** An assignment of
    probabilities to effects satisfying: non-negativity, boundedness by 1,
    total-one on the identity, and finite additivity when the sum remains
    below `I`. Unitary covariance (spec clause 3) is omitted from this minimal
    structure and may be added if the Busch axiom's precise statement
    requires it in a future refinement. -/
structure OperationalPackage (N : ℕ) where
  /-- Probability assignment. -/
  p          : Effect N → ℝ
  /-- `0 ≤ p(E)`. -/
  nonneg     : ∀ E, 0 ≤ p E
  /-- `p(E) ≤ 1`. -/
  le_one     : ∀ E, p E ≤ 1
  /-- `p(I) = 1`. -/
  total_one  : p Effect.one = 1
  /-- Finite additivity: if `E + F ≤ I` then `p(E + F) = p(E) + p(F)`. -/
  additivity : ∀ E F : Effect N, ∀ (hLe : (1 - (E.M + F.M)).PosSemidef),
                 p (Effect.add E F hLe) = p E + p F

/-- **Imported Busch effect-Gleason theorem (spec §5.2, §7.4).** Under the
    effect-additive operational consistency package of Definition 5.1 and
    dimension `N ≥ 2`, there is a unique density operator `ρ` such that
    `p(E) = Tr(ρ · E)` for every effect `E`.

    This is the load-bearing external input of the Born-weight wrapper and is
    not present in Mathlib. LF2 imports it axiomatically rather than
    rederiving it, per the explicit spec directive in §7.4. -/
axiom busch_effect_gleason
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E

/-- **Born-form assignment (spec §5.4 wrapper).** Thin wrapper exposing the
    Busch axiom under an `LF2`-namespaced name. -/
theorem born_form_of_package
    {N : ℕ} (hN : 2 ≤ N) (OP : OperationalPackage N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E :=
  busch_effect_gleason hN OP

end LF2
end CSD
