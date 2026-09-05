/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Bargmann
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology

/-!
# Continuity of the Bargmann invariant on projective space

**Category:** 1-Mathlib (CSD-free; upstream candidate alongside `Projectivization/Topology.lean`).

The Bargmann invariant `Δ(p, q, r)` is continuous as a function of the three *rays*. The
`Projectivization/Bargmann.lean` module carried no continuity at all before this one, and the
omission was load-bearing: `LF4/BargmannSelection.lean` closes the W3 unitary-branch selection given
a hypothesis `hcont` that the Bargmann observable is continuous along the flow, and without
continuity of `Δ` itself that hypothesis could only ever be assumed, never discharged.

## ⚠️ Why the obvious route does not work

`bargmann p q r` is *defined* as `bargmannVec p.rep q.rep r.rep`, so one is tempted to prove
continuity by composing with `Projectivization.rep`. **That fails, and not for a technical reason:**
`rep` is defined by choice and is **not continuous** — it picks a representative with no coherence
between nearby rays. Any proof that appears to go through `rep` is wrong.

The correct route is the quotient. `mk'` is an **open** quotient map
(`isOpenQuotientMap_mk'`), open quotient maps are closed under products
(`IsOpenQuotientMap.prodMap`), and a map out of a quotient is continuous exactly when its lift is.
The lift here is `bargmannVec`, which is visibly continuous away from zero.

## What is proved

★★ `continuous_bargmann` — `Δ : ℙ × ℙ × ℙ → ℂ` is continuous, jointly in all three rays.

★ `continuous_bargmannVec_nonzero` — the lift, continuous on the nonzero locus. Separated out
because it is the only analytic content: a quotient of continuous functions with a denominator that
cannot vanish off zero.

## References

`Projectivization/Bargmann.lean` (`bargmann`, `bargmannVec`, `bargmann_mk`);
`Projectivization/Topology.lean` (`isOpenQuotientMap_mk'`, the `ℙ` topology);
`LF4/BargmannSelection.lean` (`projectedFlow_unitary_of_bargmann_continuous` — the consumer, whose
`hcont` this makes dischargeable); `specs/POSITS.md` (Posit 6, whose discharge condition this moves
from a bespoke datum toward plain continuity of the flow).
-/

@[expose] public section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- ★ **The lift is continuous off zero.** `bargmannVec` is a quotient of continuous functions
whose denominator `‖u‖²‖v‖²‖w‖²` cannot vanish when all three arguments are nonzero. -/
theorem continuous_bargmannVec_nonzero :
    Continuous
      (fun x : {v : E // v ≠ 0} × {v : E // v ≠ 0} × {v : E // v ≠ 0} =>
        bargmannVec (x.1 : E) (x.2.1 : E) (x.2.2 : E)) := by
  unfold bargmannVec
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have h1 : ‖(x.1 : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.1.2
    have h2 : ‖(x.2.1 : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2.1.2
    have h3 : ‖(x.2.2 : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2.2.2
    positivity

/-- ★★ **The Bargmann invariant is continuous on projective space**, jointly in all three rays.

Proved through the quotient, *not* through `Projectivization.rep` — `rep` is choice-defined and not
continuous, so the direct route is unavailable. `mk'` is an open quotient map, open quotient maps
are closed under products, and continuity out of a quotient is continuity of the lift. -/
theorem continuous_bargmann :
    Continuous (fun x : (ℙ ℂ E) × (ℙ ℂ E) × (ℙ ℂ E) => bargmann x.1 x.2.1 x.2.2) := by
  have hq : IsOpenQuotientMap
      (Prod.map (mk' ℂ (V := E)) (Prod.map (mk' ℂ (V := E)) (mk' ℂ (V := E)))) :=
    (isOpenQuotientMap_mk' (K := ℂ) (V := E)).prodMap
      ((isOpenQuotientMap_mk' (K := ℂ) (V := E)).prodMap
        (isOpenQuotientMap_mk' (K := ℂ) (V := E)))
  rw [hq.isQuotientMap.continuous_iff]
  refine continuous_bargmannVec_nonzero.congr fun x => ?_
  exact (bargmann_mk x.1.2 x.2.1.2 x.2.2.2).symm

end Projectivization
