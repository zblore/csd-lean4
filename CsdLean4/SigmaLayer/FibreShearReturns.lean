/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreReturnCriterion
public import CsdLean4.Mathlib.Dynamics.ShearReturns

/-!
# The records-side picture of the parabolic case: each shear returns its torsion circles

**Category:** 7-SigmaLayer.
BACKLOG #181 (out of #19, ~~#153~~, ~~#177~~).

~~#153~~ factored the hyperbolic stroke into two transverse coordinate-reading shears, each of
Lyapunov exponent `0`, and said the stretching comes from their transversality. This file says the
same thing in return terms, which is #19's record-side vocabulary (~~#177~~):

* under `t` strokes of a **single** shear, exactly the configurations whose *read* coordinate is
  `t`-torsion return — all of them, whatever the shifted coordinate — so the return set is a union
  of `t` circles, infinite at every stroke, and the shear has no return growth at any rate;
* under `t` strokes of the **composite**, the hyperbolic stroke, finitely many configurations return
  and their number grows at `2 log φ` (~~#176~~, ~~#177~~).

**The transversality of the pair is what makes returns finite.** A parabolic de-isolation would make
return, at stroke `t`, precisely the configurations rational in the read coordinate with denominator
dividing `t`.

* ★★★ `fibre_shear_returns` — the package.

## Honest scope

* ⚠️ Says what each corpus witness returns; does not decide #19.
* The two shears here are `MeasureTheory.shearX`/`shearY`, the factors of `catStroke`
  (`catStroke_eq_two_shears`); the constructed de-isolation's fibre action `pshift a` is a
  translation, covered by `not_hasReturnGrowth_pshift` (~~#177~~).

References: `specs/BACKLOG.md` #181, #19, ~~#153~~, ~~#177~~; `Mathlib/Dynamics/ShearReturns.lean`,
`SigmaLayer/FibreTwoShears.lean` (`catStroke_eq_two_shears`), `SigmaLayer/FibreReturnCriterion.lean`
(`catStroke_hasReturnGrowth`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4 RecordLayer

/-- ★★★ **Each shear returns its torsion circles; their composite returns finitely many points.**
A point returns under `t` horizontal (vertical) shears iff its second (first) coordinate is
`t`-torsion; the return sets are infinite at every stroke and neither shear has return growth; the
composite `catStroke` has return growth `2 log φ`. -/
theorem fibre_shear_returns :
    (∀ (t : ℕ) (p : KTorus), shearX^[t] p = p ↔ t • p.2 = 0)
      ∧ (∀ (t : ℕ) (p : KTorus), shearY^[t] p = p ↔ t • p.1 = 0)
      ∧ (∀ t : ℕ, Infinite {p : KTorus // shearX^[t] p = p})
      ∧ (∀ t : ℕ, Infinite {p : KTorus // shearY^[t] p = p})
      ∧ (∀ h : ℝ, ¬ HasReturnGrowth shearX h)
      ∧ (∀ h : ℝ, ¬ HasReturnGrowth shearY h)
      ∧ catStroke = shearX ∘ shearY
      ∧ HasReturnGrowth catStroke (2 * Real.log φ) :=
  ⟨shearX_iterate_fixed_iff, shearY_iterate_fixed_iff, infinite_fixedPoints_shearX_iterate,
    infinite_fixedPoints_shearY_iterate, not_hasReturnGrowth_shearX, not_hasReturnGrowth_shearY,
    cat_eq_shearX_comp_shearY, catStroke_hasReturnGrowth⟩

end CSD.SigmaLayer

end
