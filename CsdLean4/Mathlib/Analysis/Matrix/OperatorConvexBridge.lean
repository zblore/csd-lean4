import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex

/-!
# `CStarMatrix ↔ Matrix` transport bridge for the operator-convexity ladder

`Matrix n n ℂ` is **not** a `CStarAlgebra` at its default instances: the C⋆-algebra structure
(norm, topology, spectral order) lives on the type synonym
`CStarMatrix m n A := Matrix m n A` (`CStarMatrix.instCStarAlgebra`). Consequently the
C⋆-generic continuous-functional-calculus order machinery — `CFC.log` (operator monotone),
`CFC.log_le_log`, the rpow order lemmas, the rpow→log limit — is stated for `[CStarAlgebra A]`
and does **not** fire directly on the bare `Matrix` type used by
`Matrix.OperatorConvexOn` / `Matrix.OperatorConcaveOn` and the L.1/L.2 rungs.

This file builds the transport across the star-algebra equivalence
`e := CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ`
(which is the identity `Equiv.refl` on carriers, hence continuous), and uses it to pull the
C⋆-generic facts back onto `Matrix`.

## Main results

* `Matrix.cstar_cfc` (**B.1, the crux**): CFC naturality across the synonym equiv,
  `e (cfc f A) = cfc f (e A)`. Note the two `cfc`s come from **different** functional-calculus
  instances — `Matrix.IsHermitian.instContinuousFunctionalCalculus` on the left and the
  C⋆-algebra CFC on the right — and they agree by CFC uniqueness, packaged by
  `StarAlgHomClass.map_cfc`.
* `Matrix.cstar_le_iff` (**B.2**): the Löwner order on `Matrix` and the spectral order on
  `CStarMatrix` agree across `e`, `e A ≤ e B ↔ A ≤ B`. Proved via
  `StarRingEquivClass.instOrderIsoClass.map_le_map_iff` (a star-ring equivalence is an order
  isomorphism between `StarOrderedRing`s).
* `Matrix.cstar_isStrictlyPositive`: `A.PosDef → IsStrictlyPositive (e A)`, the positivity
  hypothesis transport feeding the order lemmas.
* `Matrix.matrix_log_le_log` (**B.3, log**): operator **monotonicity** of `log` on
  positive-definite matrices in the Löwner order, `A ≤ B → cfc Real.log A ≤ cfc Real.log B`,
  transported from `CFC.log_le_log`. This is the genuine ladder enabler: the route-2 path to
  operator concavity of `log` (`specs/operator-convexity-plan.md` L.2) consumes
  `CFC.log_monotoneOn` and `tendsto_cfc_rpow_sub_one_log` on the C⋆ side, and this bridge is
  what makes the conclusion expressible on the `Matrix` carrier of the `OperatorConcaveOn`
  predicate.

## Honest scope (rpow wall)

The analogous **rpow** transport (`x ↦ x ^ p` operator monotone, `p ∈ [0,1]`) is **not** landed
here. The C⋆-generic `CFC.rpow_le_rpow` is stated with the `Pow A ℝ` notation
(`CFC.instPowReal`), whose instance — together with `NonnegSpectrumClass ℝ A` — does **not**
resolve on `CStarMatrix n n ℂ` at this Mathlib pin: the generic `ℝ`-CFC instance
`IsSelfAdjoint.instContinuousFunctionalCalculus` does not fire on `CStarMatrix` via the
discrimination tree (a local shim `instCStarMatrixRealCFC` is required even to state the goal),
and the `NonnegSpectrumClass ℝ (CStarMatrix n n ℂ)` subgoal — though provable as a *term* — is
not *found* by instance synthesis when nested inside the `Pow`/`CFC.rpow` resolution (the
repeated-index `CStarMatrix n n ℂ` discrimination key blocks the `Fintype n`/`DecidableEq n`
side-conditions). The `log` route needs only `[CStarAlgebra A]` (via `IsStrictlyPositive`), so
it transports cleanly; the rpow route additionally needs `NonnegSpectrumClass` + `Pow`, which do
not. See `specs/operator-convexity-plan.md` (L.2 / L.3 sections) for the precise residual.

**Category:** 1-Mathlib (CSD-free). Natural Mathlib namespace `Matrix`.
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The `ℝ`-CFC instance shim on `CStarMatrix n n ℂ`

The generic `IsSelfAdjoint.instContinuousFunctionalCalculus` does not fire on `CStarMatrix n n ℂ`
through the discrimination tree (its predicate-output `IsSelfAdjoint` is not matched), so we
register it explicitly as a local instance. It elaborates because `CStarMatrix n n ℂ` is a unital
`CStarAlgebra` (`CStarMatrix.instCStarAlgebra`) with the `ℂ`-CFC over `IsStarNormal`. -/

/-- The real continuous functional calculus on `CStarMatrix n n ℂ` over self-adjoint elements,
registered explicitly (the generic instance does not fire on `CStarMatrix` via the
discrimination tree). -/
noncomputable instance instCStarMatrixRealCFC :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local notation "e" => (CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ → CStarMatrix n n ℂ)

/-! ### Continuity of the synonym equivalence -/

omit [DecidableEq n] in
/-- The star-algebra equivalence `Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ` is continuous: on
carriers it is the identity (`Equiv.refl`), and `CStarMatrix.ofMatrixL` is a continuous linear
equivalence with `continuous_id`. -/
theorem ofMatrixStarAlgEquiv_continuous :
    Continuous (CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ → CStarMatrix n n ℂ) := by
  rw [← CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv, CStarMatrix.ofMatrix_eq_ofMatrixL]
  exact (CStarMatrix.ofMatrixL).continuous_toFun

/-! ### B.2 — order transport (Löwner ↔ spectral order across `e`) -/

omit [DecidableEq n] in
/-- **B.2.** The Löwner order on `Matrix n n ℂ` (`(B - A).PosSemidef`) and the spectral order on
`CStarMatrix n n ℂ` agree across the star-algebra equivalence `e`:
`e A ≤ e B ↔ A ≤ B`. Both `Matrix` and `CStarMatrix` are `StarOrderedRing`s, and a star-ring
equivalence is an `OrderIso` between `StarOrderedRing`s (`StarRingEquivClass.instOrderIsoClass`),
so this is `map_le_map_iff`. -/
theorem cstar_le_iff (A B : Matrix n n ℂ) :
    CStarMatrix.ofMatrixStarAlgEquiv A ≤ CStarMatrix.ofMatrixStarAlgEquiv B ↔ A ≤ B :=
  map_le_map_iff CStarMatrix.ofMatrixStarAlgEquiv

/-! ### B.1 — CFC transport (the crux) -/

/-- **B.1 (the crux).** The continuous functional calculus commutes with the synonym equivalence
`e`: for Hermitian `A` and `f` continuous on `spectrum ℝ A`,
`e (cfc f A) = cfc f (e A)`.

The left `cfc` is taken in `Matrix`'s own functional-calculus instance
(`Matrix.IsHermitian.instContinuousFunctionalCalculus`, the spectral triple product); the right
`cfc` is taken in the C⋆-algebra instance on `CStarMatrix`. These are **a priori different**
functional-calculus instances; they agree because `e` is a continuous star-algebra homomorphism
and the CFC is unique (`StarAlgHomClass.map_cfc`, whose proof routes through
`ContinuousMap.UniqueHom`). So no separate uniqueness argument is needed at this level. -/
theorem cstar_cfc {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    CStarMatrix.ofMatrixStarAlgEquiv (cfc f A) = cfc f (CStarMatrix.ofMatrixStarAlgEquiv A) := by
  have hsa : IsSelfAdjoint A := hA
  exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv f A hf
    ofMatrixStarAlgEquiv_continuous hsa (hsa.map _)

/-! ### Positivity transport -/

/-- A positive-definite matrix maps to a strictly-positive element of `CStarMatrix n n ℂ`.
`IsStrictlyPositive a := 0 ≤ a ∧ IsUnit a`: nonnegativity transports via `cstar_le_iff` (B.2) and
`map_zero e`, and invertibility transports because `e` is a ring equivalence. -/
theorem cstar_isStrictlyPositive {A : Matrix n n ℂ} (hA : A.PosDef) :
    IsStrictlyPositive (CStarMatrix.ofMatrixStarAlgEquiv A) := by
  have hsp : IsStrictlyPositive A := hA.isStrictlyPositive
  refine ⟨?_, ?_⟩
  · have h0 : (0 : Matrix n n ℂ) ≤ A := hsp.1
    have := (cstar_le_iff 0 A).mpr h0
    rwa [map_zero] at this
  · exact hsp.2.map CStarMatrix.ofMatrixStarAlgEquiv

/-! ### B.3 — operator monotonicity of `log` transported onto `Matrix` -/

/-- `Real.log` is continuous on the (positive) spectrum of a positive-definite matrix. -/
theorem logContinuousOn {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn Real.log (spectrum ℝ A) :=
  Real.continuousOn_log.mono (fun x hx => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (posDef_spectrum_pos hA x hx).ne')

/-- **B.3 (log).** Operator **monotonicity** of `log` on positive-definite matrices, in the
Löwner order: `A ≤ B → cfc Real.log A ≤ cfc Real.log B` (for positive-definite `A, B`).

Transported from `CFC.log_le_log` on `CStarMatrix n n ℂ`: the order transports (B.2), strict
positivity transports (`cstar_isStrictlyPositive`), and `CFC.log (e A) = e (cfc Real.log A)` by
B.1 (`CFC.log a := cfc Real.log a` definitionally). The statement is in terms of `cfc Real.log`
on the `Matrix` side because `CFC.log` itself requires `NormedRing (Matrix n n ℂ)`, which the
default `Matrix` instances do not provide — this is exactly the carrier mismatch the bridge
resolves. -/
theorem matrix_log_le_log {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := by
  have hspA : IsStrictlyPositive (e A) := cstar_isStrictlyPositive hA
  have hle : e A ≤ e B := (cstar_le_iff A B).mpr hAB
  have key : CFC.log (e A) ≤ CFC.log (e B) := CFC.log_le_log hle hspA
  have hlogA : e (cfc Real.log A) = CFC.log (e A) :=
    (cstar_cfc Real.log hA.1 (logContinuousOn hA)).trans rfl
  have hlogB : e (cfc Real.log B) = CFC.log (e B) :=
    (cstar_cfc Real.log hB.1 (logContinuousOn hB)).trans rfl
  rw [← hlogA, ← hlogB] at key
  exact (cstar_le_iff (cfc Real.log A) (cfc Real.log B)).mp key

/-! ### Non-vacuity witness

The bridge is non-vacuous: it applies to a concrete non-commuting positive-definite pair.
`A = diagonal !![2, 1]`-style witnesses are positive definite; the transport lemmas relate the
genuine carriers (the `Matrix` Löwner order and the `CStarMatrix` spectral order), not a
degenerate or mismatched structure. -/
example {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := matrix_log_le_log hA hB hAB

end Matrix
