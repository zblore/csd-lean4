/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.MovingFibreWitness
public import CsdLean4.RecordLayer.ShearWitness
public import CsdLean4.Mathlib.Dynamics.LyapunovExponent

/-!
# The Lyapunov exponents of the fibre witnesses

**Category:** 7-SigmaLayer.
BACKLOG #148 (out of ~~#101~~(a)); the criterion #19 records.

The corpus has two maps of the fibre `T²` that stand in for a de-isolation dynamics, and this
file puts them on the two sides of one line.

* The **hyperbolic witness** `catStroke` (`MovingFibreWitness.lean`) lifts to the plane as the
  linear map `catR = [[2,1],[1,1]]` (`catStroke_coe`); its derivative is `catR` at every point,
  and `catR` stretches every direction off the stable line at rate `2 log φ`
  (`Mathlib/Dynamics/LyapunovExponent.lean`).
* The **constructed de-isolation witness** `shearEvolve` (`ShearWitness.lean`) acts on each fibre
  by `pshift`, a translation of the first coordinate (`shearEvolve_snd`); the isolated fibre flow
  `kFlow` is a translation too. A translation lifts to `v ↦ v + c` (`pshift_coe`, `kFlow_coe`),
  whose derivative is the identity: Lyapunov exponent `0` in every direction.

★★★ `fibre_witnesses_lyapunov` states the pair. **The constructed de-isolation flow is not
chaotic; the hyperbolic one is; which map nature uses is BACKLOG #19**, and this file gives that
row a measurable criterion: *the de-isolation flow has a positive Lyapunov exponent on the fibre*.

## Honest scope

* The exponents are those of the **lifts' derivatives**, which are constant for both witnesses;
  no manifold tangent bundle on `T²` is used (Mathlib has none for `AddCircle` products), and
  nothing is claimed about the base `ℂℙ^{N−1}` flow.
* `shearEvolve` is a translation *fibrewise*; the amount depends on the selector coordinate of the
  base, so the full map on `Xsel × T²` is a shear in the base–fibre sense. Its fibre derivative is
  still the identity, which is the statement here.
* Nothing here is a prediction, and nothing here decides #19.

References: `specs/BACKLOG.md` #148, #19, ~~#101~~; `Mathlib/Dynamics/LyapunovExponent.lean`;
`SigmaLayer/MovingFibreWitness.lean`; `RecordLayer/ShearWitness.lean`; `LF4/KahlerFlow.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4

/-! ### The hyperbolic witness lifts to `catR` -/

/-- The hyperbolic stroke is `catR` read modulo `ℤ²`. -/
theorem catStroke_coe (x y : ℝ) :
    catStroke ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((catR (x, y)).1 : AddCircle (1 : ℝ)), ((catR (x, y)).2 : AddCircle (1 : ℝ))) :=
  cat_coe x y

/-- The derivative of the lift of the hyperbolic stroke is `catR` at every point. -/
theorem fderiv_catR (v : ℝ × ℝ) : fderiv ℝ catR v = catR := catR.fderiv

/-! ### The translations lift to `v ↦ v + c` -/

/-- A translation of the plane. -/
def transR (c : ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ := fun v => v + c

/-- The derivative of a translation is the identity. -/
theorem fderiv_transR (c v : ℝ × ℝ) :
    fderiv ℝ (transR c) v = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  unfold transR
  rw [fderiv_add_const, fderiv_fun_id]

/-- The shear witness acts on each fibre by `pshift`. -/
theorem shearEvolve_snd {Xsel : Type*} {K : ℕ} (idx : Xsel → Fin K)
    (s t : OnticTime) (x : Xsel × KTorus) :
    (RecordLayer.shearEvolve idx s t x).2
      = RecordLayer.pshift ((RecordLayer.elapsed t - RecordLayer.elapsed s)
          * RecordLayer.shearAmt K (idx x.1)) x.2 := rfl

/-- `pshift a` is the translation by `(a, 0)` read modulo `ℤ²`. -/
theorem pshift_coe (a x y : ℝ) :
    RecordLayer.pshift a ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((transR (a, 0) (x, y)).1 : AddCircle (1 : ℝ)),
          ((transR (a, 0) (x, y)).2 : AddCircle (1 : ℝ))) := by
  simp [RecordLayer.pshift, transR]

/-- The isolated fibre flow `kFlow` is the translation by `(a, b)` read modulo `ℤ²`. -/
theorem kFlow_coe {N : ℕ} (a b x y : ℝ) (q : CPN N) :
    (kFlow ((a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ)))
        (q, ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ))))).2
      = (((transR (a, b) (x, y)).1 : AddCircle (1 : ℝ)),
          ((transR (a, b) (x, y)).2 : AddCircle (1 : ℝ))) := by
  simp [kFlow, transR, add_comm]

/-! ### The two sides of the line -/

/-- ★★ The derivative of the hyperbolic witness's lift has exponent `2 log φ` in every direction
off the stable line. -/
theorem catR_fderiv_hasLyapunovExponent (v : ℝ × ℝ) {w : ℝ × ℝ} (hw : ellUR w ≠ 0) :
    HasLyapunovExponent (fderiv ℝ catR v) w (2 * Real.log φ) := by
  rw [fderiv_catR]
  exact hasLyapunovExponent_catR hw

/-- ★★ The derivative of a translation's lift has exponent `0` in every direction. -/
theorem transR_fderiv_hasLyapunovExponent (c v w : ℝ × ℝ) :
    HasLyapunovExponent (fderiv ℝ (transR c) v) w 0 := by
  rw [fderiv_transR]
  exact hasLyapunovExponent_id w

/-- ★★★ **The two fibre witnesses sit on the two sides of the line.** The hyperbolic stroke's lift
stretches every direction off the stable line at rate `2 log φ`; the constructed de-isolation
witness's fibre action and the isolated fibre flow are translations, whose lifts stretch nothing.
Which map nature uses is BACKLOG #19. -/
theorem fibre_witnesses_lyapunov :
    (∀ v w : ℝ × ℝ, ellUR w ≠ 0 → HasLyapunovExponent (fderiv ℝ catR v) w (2 * Real.log φ))
      ∧ (∀ c v w : ℝ × ℝ, HasLyapunovExponent (fderiv ℝ (transR c) v) w 0) :=
  ⟨fun v _ hw => catR_fderiv_hasLyapunovExponent v hw, transR_fderiv_hasLyapunovExponent⟩

/-- The exponent `2 log φ` is positive: the hyperbolic witness genuinely stretches. -/
theorem two_mul_log_goldenRatio_pos : 0 < 2 * Real.log φ :=
  mul_pos two_pos (Real.log_pos one_lt_goldenRatio)

end CSD.SigmaLayer

end
