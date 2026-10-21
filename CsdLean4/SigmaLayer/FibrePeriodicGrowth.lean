/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreAffineShears
public import CsdLean4.Mathlib.Dynamics.CatMapPeriodicPoints

/-!
# Returns of fibre configurations grow at the Lyapunov exponent

**Category:** 7-SigmaLayer.
BACKLOG #176 (out of #19 and #150): the counting reading of #19's criterion.

~~#148~~ gave Posit 1's discharge one measurable criterion — *the de-isolation flow has a positive
Lyapunov exponent on the fibre* — read off the derivative of the lift. This file gives the same
criterion a second, **counting** reading on the hyperbolic witness: the number of fibre
configurations that return to themselves after `t` strokes is `L₂ₜ − 2`, and it grows at exactly the
stretching rate,

  `(1/t) log #{x ∈ T² : catStroke^[t] x = x} → 2 log φ`

(`CatMapPeriodicPoints.lean`, ★★★ `card_fixedPoints_cat_iterate`, ★★ `tendsto_log_card_fixedPoints_cat`).
Hyperbolicity of the fibre dynamics is therefore visible in how many records return, not only in
how fast nearby lifts separate — the cat-stroke instance of *topological entropy = Lyapunov exponent*.
Both readings give the same number, and both are **classical statements about the ontic fibre**; no
quantisation of the fibre enters (BACKLOG #150's correction of 2026-10-21).

* ★★★ `fibre_periodic_growth` — the package: the count, its growth rate, and the Lyapunov exponent
  of the lift, all `2 log φ`.

## Honest scope

* ⚠️ **Narrows the reading, does not decide #19.** This is what the hyperbolic witness does; nothing
  here says nature's de-isolation is the cat stroke or in its conjugacy class (~~#175~~).
* Only the cat stroke; `shearEvolve`, the constructed witness, is a translation of the fibre and has
  every configuration fixed only at the trivial strokes — its periodic structure is #19's other side.

References: `specs/BACKLOG.md` #176, #19, #150, ~~#148~~, ~~#175~~; `specs/POSITS.md` Posit 1;
`Mathlib/Dynamics/CatMapPeriodicPoints.lean`, `SigmaLayer/FibreLyapunov.lean`
(`catR_fderiv_hasLyapunovExponent`), `SigmaLayer/MovingFibreWitness.lean` (`catStroke`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4

/-- The fixed points of the hyperbolic stroke on the fibre are counted by `L₂ₜ − 2`. -/
theorem card_fixedPoints_catStroke (s : ℕ) :
    Nat.card {x : KTorus // catStroke^[s + 1] x = x} = (lucasEven (s + 1) - 2).natAbs :=
  card_fixedPoints_cat_iterate s

/-- The returns of fibre configurations grow at `2 log φ`. -/
theorem tendsto_log_card_fixedPoints_catStroke :
    Tendsto (fun s : ℕ => Real.log (Nat.card {x : KTorus // catStroke^[s + 1] x = x}) / ((s : ℝ) + 1))
      atTop (𝓝 (2 * Real.log φ)) :=
  tendsto_log_card_fixedPoints_cat

/-- ★★★ **Returns of fibre configurations grow at the Lyapunov exponent.** Under the hyperbolic
stroke, `L₂ₜ − 2` fibre configurations return after `t` strokes, the count grows at `2 log φ`, and
`2 log φ` is the Lyapunov exponent of the lift off the stable line (~~#148~~): #19's criterion read
by counting returns agrees with its reading by stretching. -/
theorem fibre_periodic_growth :
    (∀ s : ℕ, Nat.card {x : KTorus // catStroke^[s + 1] x = x} = (lucasEven (s + 1) - 2).natAbs)
      ∧ Tendsto (fun s : ℕ => Real.log (Nat.card {x : KTorus // catStroke^[s + 1] x = x})
          / ((s : ℝ) + 1)) atTop (𝓝 (2 * Real.log φ))
      ∧ (∀ v w : ℝ × ℝ, ellUR w ≠ 0 →
          HasLyapunovExponent (fderiv ℝ catR v) w (2 * Real.log φ)) :=
  ⟨card_fixedPoints_catStroke, tendsto_log_card_fixedPoints_catStroke,
    fun v _ hw => catR_fderiv_hasLyapunovExponent v hw⟩

end CSD.SigmaLayer

end
