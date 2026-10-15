/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreTwoShears
public import CsdLean4.Mathlib.Dynamics.ClassicalOtoc

/-!
# The classical OTOC of the fibre witnesses

**Category:** 7-SigmaLayer.
BACKLOG #149 (out of ~~#101~~(b)); the last classical chaos signature on the fibre witness.

~~#147~~ (mixing), ~~#148~~ (Lyapunov exponents) and ~~#153~~ (two transverse shears) put the
corpus's two fibre maps on the two sides of one line. This file adds the third textbook
signature, the **classical out-of-time-order correlator** `{x ∘ Φⁿ, p}`
(`classicalOtoc`, `Mathlib/Dynamics/ClassicalOtoc.lean`), evaluated on the lifts' derivatives
exactly as `FibreLyapunov.lean` evaluates the exponents.

* The **hyperbolic witness** `catStroke` lifts to `catR` with derivative `catR` everywhere
  (`fderiv_catR`), so its classical OTOC at step `n` is **exactly `F_{2n+1}`**
  (★ `classicalOtoc_catStroke_lift`), growing at rate `2 log φ` — the Lyapunov exponent
  (★★ `tendsto_log_classicalOtoc_catStroke_lift`); the squared bracket grows at `4 log φ`.
* The **constructed de-isolation witness** `shearEvolve` acts on each fibre by `pshift`, and the
  isolated fibre flow `kFlow` is a translation too; their lifts are `transR c` with derivative the
  identity (`fderiv_transR`), so the classical OTOC is `1` at every step
  (★ `classicalOtoc_transR_lift`), rate `0`.
* The **two shear factors** of the stroke (~~#153~~) each have classical OTOC `1` at every step
  (`classicalOtoc_shearXR_lift`, `classicalOtoc_shearYR_lift`): the exponential growth is produced
  by composing them.

★★★ `fibre_witnesses_otoc` states the package: on the fibre, the corpus's constructed de-isolation
and the isolated flow do not scramble, the hyperbolic witness scrambles at the Lyapunov rate, and
the three classical signatures (mixing, exponent, OTOC) now agree on which side each map sits.

## Honest scope

* **Classical, on the lifts' derivatives.** No phase-space average is taken: for linear maps the
  bracket is constant in the phase point (`poissonBracket_pow_fst_snd`), and every derivative here
  is constant. Nothing is said about the base `ℂℙ^{N−1}` flow.
* **Not the quantum OTOC.** The corpus's `QuantumChaos.otoc` is a commutator norm on finite
  unitaries; its exponential regime up to the Ehrenfest time needs a quantised fibre dynamics
  (Hannay–Berry), which the corpus does not have — the row records this as **L–XL, unpriced until
  an object exists**. The corpus's kicked-diagonal quantum family is at most linear
  (`otoc_interactingU_le`, `CV/ChaosBounds.lean`), on the non-scrambling side of this line.
* Nothing here is a prediction, and nothing here decides #19: which map nature uses is that row.

References: `specs/BACKLOG.md` #149, #19, ~~#148~~, ~~#153~~; `Mathlib/Dynamics/ClassicalOtoc.lean`
(`classicalOtoc`, `classicalOtoc_catR`, `tendsto_log_classicalOtoc_catR`, `cat_classicalOtoc`);
`SigmaLayer/FibreLyapunov.lean` (`fderiv_catR`, `fderiv_transR`, `transR`,
`fibre_witnesses_lyapunov`); `SigmaLayer/FibreTwoShears.lean` (`fibre_two_shears`);
`Incubator/QuantumChaos/Otoc.lean` (`QuantumChaos.otoc`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

/-! ### The hyperbolic witness scrambles at the Lyapunov rate -/

/-- ★ The classical OTOC of the hyperbolic stroke's lift at step `n` is exactly `F_{2n+1}`. -/
theorem classicalOtoc_catStroke_lift (v : ℝ × ℝ) (n : ℕ) :
    classicalOtoc (fderiv ℝ catR v) n = Nat.fib (2 * n + 1) := by
  rw [fderiv_catR, classicalOtoc_catR]

/-- ★★ The hyperbolic stroke's classical OTOC grows at rate `2 log φ`, its Lyapunov exponent. -/
theorem tendsto_log_classicalOtoc_catStroke_lift (v : ℝ × ℝ) :
    Tendsto (fun n : ℕ => Real.log (classicalOtoc (fderiv ℝ catR v) n) / n) atTop
      (𝓝 (2 * Real.log φ)) := by
  rw [fderiv_catR]
  exact tendsto_log_classicalOtoc_catR

/-- The squared bracket of the hyperbolic stroke grows at `4 log φ`, twice the exponent. -/
theorem tendsto_log_classicalOtoc_sq_catStroke_lift (v : ℝ × ℝ) :
    Tendsto (fun n : ℕ => Real.log ((classicalOtoc (fderiv ℝ catR v) n) ^ 2) / n) atTop
      (𝓝 (4 * Real.log φ)) := by
  rw [fderiv_catR]
  exact tendsto_log_classicalOtoc_sq_catR

/-! ### The translations and the shear factors do not -/

/-- ★ The lift of a translation — the fibre action of `shearEvolve`, and `kFlow` — has classical
OTOC `1` at every step. -/
theorem classicalOtoc_transR_lift (c v : ℝ × ℝ) (n : ℕ) :
    classicalOtoc (fderiv ℝ (transR c) v) n = 1 := by
  rw [fderiv_transR, classicalOtoc_id]

/-- The translations' classical OTOC has growth rate `0`. -/
theorem tendsto_log_classicalOtoc_transR_lift (c v : ℝ × ℝ) :
    Tendsto (fun n : ℕ => Real.log (classicalOtoc (fderiv ℝ (transR c) v) n) / n) atTop
      (𝓝 0) := by
  rw [fderiv_transR]
  exact tendsto_log_classicalOtoc_id

/-- The horizontal shear factor of the stroke has classical OTOC `1` at every step. -/
theorem classicalOtoc_shearXR_lift (v : ℝ × ℝ) (n : ℕ) :
    classicalOtoc (fderiv ℝ shearXR v) n = 1 := by
  rw [shearXR.fderiv, classicalOtoc_shearXR]

/-- The vertical shear factor of the stroke has classical OTOC `1` at every step. -/
theorem classicalOtoc_shearYR_lift (v : ℝ × ℝ) (n : ℕ) :
    classicalOtoc (fderiv ℝ shearYR v) n = 1 := by
  rw [shearYR.fderiv, classicalOtoc_shearYR]

/-! ### ★★★ The package -/

/-- ★★★ **The classical OTOC puts the fibre witnesses on the two sides of the line, in agreement
with mixing and the Lyapunov exponents.** The hyperbolic stroke's bracket is exactly `F_{2n+1}`
and grows at the Lyapunov rate `2 log φ`; the constructed de-isolation's fibre action and the
isolated fibre flow have bracket `1` at every step, rate `0`; and so does each of the two shears
whose composition the stroke is. Which map nature uses is BACKLOG #19. -/
theorem fibre_witnesses_otoc :
    (∀ v : ℝ × ℝ, ∀ n : ℕ, classicalOtoc (fderiv ℝ catR v) n = Nat.fib (2 * n + 1))
      ∧ (∀ v : ℝ × ℝ,
          Tendsto (fun n : ℕ => Real.log (classicalOtoc (fderiv ℝ catR v) n) / n) atTop
            (𝓝 (2 * Real.log φ)))
      ∧ (∀ c v : ℝ × ℝ, ∀ n : ℕ, classicalOtoc (fderiv ℝ (transR c) v) n = 1)
      ∧ (∀ c v : ℝ × ℝ,
          Tendsto (fun n : ℕ => Real.log (classicalOtoc (fderiv ℝ (transR c) v) n) / n) atTop
            (𝓝 0))
      ∧ (∀ v : ℝ × ℝ, ∀ n : ℕ, classicalOtoc (fderiv ℝ shearXR v) n = 1)
      ∧ (∀ v : ℝ × ℝ, ∀ n : ℕ, classicalOtoc (fderiv ℝ shearYR v) n = 1) :=
  ⟨classicalOtoc_catStroke_lift, tendsto_log_classicalOtoc_catStroke_lift,
    classicalOtoc_transR_lift, tendsto_log_classicalOtoc_transR_lift,
    classicalOtoc_shearXR_lift, classicalOtoc_shearYR_lift⟩

end CSD.SigmaLayer

end
