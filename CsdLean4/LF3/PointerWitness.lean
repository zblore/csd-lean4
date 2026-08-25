/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Setup
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# A witness for the system-apparatus interface

**Category:** 3-CSD. Closes the unpopulated-interface finding recorded against ledger row CL-008
(2026-08-24).

`LF3_main_theorem` takes an `S : SystemApparatusSetup K_A K_B H_SA`, and until now **no term of that
type existed anywhere in the corpus** — every occurrence was a hypothesis binder. That is the same
defect class as `RecordLayer.DeIsolationInteraction` before `Q12-a`: an interface whose antecedent
is never shown to be satisfiable.

★★ `spinSystemApparatusSetup` is the witness, built from the corpus's own concrete spin layer rather
than from anything new.

## ⚠️ Why not the degenerate one

`proj .plus = 1`, `proj .minus = 0` satisfies **every** field of `BinaryPointerProjectors` —
self-adjoint, idempotent, orthogonal, complete — and would populate the interface while proving
nothing: it describes a pointer that always reads `+`. The witness here is the genuine two-outcome
one, `Π^±(a) = (1 ± σ·a)/2`, whose two projectors are both rank one.

## What was already available, and what was missing

`spinProj` and three of the four field obligations were already proved in `LF3/Setup.lean`
(`spinProj_isHermitian`, `spinProj_idem`, `spinProj_complete`). Only **orthogonality** was missing,
and it falls straight out of `pauliDot_sq`: `Π⁺Π⁻ = (1 − (σ·a)²)/4 = 0`. Lifting matrices to
operators is `Matrix.toEuclideanCLM`, a *star*-algebra equivalence, so each field transports by the
structure map it corresponds to — `map_mul` for idempotence and orthogonality, `map_add`/`map_one`
for completeness, and `map_star` for self-adjointness.

## ⚠️ What this does and does not establish

It establishes that `SystemApparatusSetup` is **inhabited**, so `LF3_main_theorem` is not vacuous on
that argument. It does **not** change what the bundle contributes: as CL-008's trace records, the
singlet content of `LF3_main_theorem` rides entirely on `ctx : MeasurementContext`, and `S` enters
only the two pointer-completeness conjuncts, which are its own axioms echoed back.

Reference: `specs/VALIDATION-LEDGER.md` (CL-008, S3 2026-08-24);
`specs/q12-fibre-mechanism-scoping.md` (`W3`, the same defect class); `specs/future-work.md`.
-/

@[expose] public section

namespace CSD
namespace LF3

/-- **The two spin projectors are mutually orthogonal**, the one field obligation
`LF3/Setup.lean` had not already discharged.

`Π⁺Π⁻ = (1 + σ·a)(1 − σ·a)/4 = (1 − (σ·a)²)/4`, and `pauliDot_sq` makes the square the identity. -/
theorem spinProj_orthogonal (a : DetectorSetting) :
    spinProj .plus a * spinProj .minus a = 0 := by
  unfold spinProj
  simp only [Sign.val_plus, Sign.val_minus, Complex.ofReal_one, Complex.ofReal_neg,
    neg_smul, one_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hprod :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliDot a) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + -pauliDot a) = 0 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_neg, pauliDot_sq]
    module
  rw [hprod, smul_zero]

/-- ★★ **A genuine binary pointer algebra**: the spin projectors `Π^±(a) = (1 ± σ·a)/2`, lifted from
matrices to operators on `EuclideanSpace ℂ (Fin 2)`.

Both projectors are rank one, so this is a real two-outcome pointer and not the degenerate
`(1, 0)` reading that would satisfy the fields vacuously. -/
noncomputable def spinPointerProjectors (a : DetectorSetting) :
    BinaryPointerProjectors (EuclideanSpace ℂ (Fin 2)) where
  proj s := Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a)
  selfAdjoint s x y := by
    have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a))
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a) := by
      rw [← map_star]
      congr 1
      exact spinProj_isHermitian s a
    have hadj : ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a))
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a) := hstar
    calc inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a) x) y
        = inner ℂ (ContinuousLinearMap.adjoint
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a)) x) y := by rw [hadj]
      _ = inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (spinProj s a) y) :=
          ContinuousLinearMap.adjoint_inner_left _ y x
  idem s := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, spinProj_idem]
  orthogonal := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, spinProj_orthogonal, map_zero]
  complete := by
    rw [← map_add, spinProj_complete, map_one]

/-- ★★ **The system-apparatus interface is inhabited.**

Two independent detector settings, one per wing, each carrying its own genuine two-outcome pointer
algebra. This is what `LF3_main_theorem`'s `S` argument was missing.

⚠️ Inhabitation only. See the module docstring for what the bundle does *not* contribute. -/
noncomputable def spinSystemApparatusSetup (a b : DetectorSetting) :
    SystemApparatusSetup (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
      (EuclideanSpace ℂ (Fin 2 × Fin 2)) where
  ptrA := spinPointerProjectors a
  ptrB := spinPointerProjectors b

end LF3
end CSD
