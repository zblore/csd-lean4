/- MG-3 probe round 2 (2026-08-22, specs/mathlib-gaps-plan.md). Round-1 findings at this pin:
CStarAlgebra/PartialOrder/StarOrderedRing on `CStarMatrix n n ℂ` all RESOLVE (round-1 "errors"
on P1/P2 were noncomputable-compilation noise); the ℝ-CFC over IsSelfAdjoint still does NOT
fire (the recorded discrimination-tree failure stands), and NonnegSpectrumClass / Pow ℝ≥0 /
monotone_nnrpow / log_le_log all fail downstream of that single root. THIS round: register the
bridge's one-line shim locally and see whether the whole cascade un-dams.
Run: `lake env lean scratch_mg3_probe.lean`. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped ComplexOrder NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Round-1 confirmations, compile-safe this time:
noncomputable example : CStarAlgebra (CStarMatrix n n ℂ) := inferInstance
noncomputable example : PartialOrder (CStarMatrix n n ℂ) := inferInstance
example : StarOrderedRing (CStarMatrix n n ℂ) := inferInstance

-- THE SHIM (the bridge's instCStarMatrixRealCFC, registered locally):
noncomputable instance shimRealCFC :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- SHIM 2 (round 3): the generic NonnegSpectrumClass provider, registered explicitly
instance shimNonnegSpectrum : NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

-- P4': NonnegSpectrumClass, with both shims present
example : NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) := inferInstance

-- P5': the ℝ≥0-Pow instance, with the shim present
noncomputable example (A : CStarMatrix n n ℂ) : CStarMatrix n n ℂ := A ^ (2⁻¹ : ℝ≥0)

-- P6': the generic operator-monotonicity of rpow applies to matrices, with the shim
example {p : ℝ≥0} (hp : p ∈ Set.Icc 0 1) :
    Monotone (fun A : CStarMatrix n n ℂ => A ^ p) :=
  CFC.monotone_nnrpow hp

-- P7': sqrt operator monotone
example : Monotone (CFC.sqrt : CStarMatrix n n ℂ → CStarMatrix n n ℂ) :=
  CFC.monotone_sqrt

-- P8': unital ℝ-rpow elaborates
noncomputable example (A : CStarMatrix n n ℂ) : CStarMatrix n n ℂ := CFC.rpow A (2⁻¹ : ℝ)

-- P9': log monotonicity applies
example (A B : CStarMatrix n n ℂ) (hA : IsStrictlyPositive A) (hAB : A ≤ B) :
    CFC.log A ≤ CFC.log B :=
  CFC.log_le_log hAB hA

-- P10: unital monotone_rpow (ℝ exponent) applies on CStarMatrix
example {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    Monotone (fun A : CStarMatrix n n ℂ => A ^ p) :=
  CFC.monotone_rpow hp

section MatrixSide
-- P11: does the ℝ≥0-CFC fire on BARE Matrix (for the rpow transport's LHS)?
open scoped MatrixOrder

example : ContinuousFunctionalCalculus ℝ≥0 (Matrix n n ℂ) (fun A => 0 ≤ A) := inferInstance

-- P12: bare-Matrix ℝ≥0 power elaborates
noncomputable example (A : Matrix n n ℂ) : Matrix n n ℂ := A ^ (2⁻¹ : ℝ≥0)

end MatrixSide
