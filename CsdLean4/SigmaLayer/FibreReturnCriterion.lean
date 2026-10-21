/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibrePeriodicGrowth
public import CsdLean4.Mathlib.Dynamics.ReturnCriterion

/-!
# #19's criterion in record terms: which fibre configurations come back

**Category:** 7-SigmaLayer.
BACKLOG #177 (out of #19 and ~~#176~~): the derivative-free form of Posit 1's discharge criterion.

~~#148~~ gave #19 a criterion through the derivative of a lift — *the de-isolation flow has a positive
Lyapunov exponent on the fibre*. ~~#176~~ showed the hyperbolic witness's periodic-return count grows
at the same rate. This file states the criterion as `HasReturnGrowth f h` with `h > 0`
(`ReturnCriterion.lean`): at every stroke count finitely many but at least one fibre configuration
returns, and the count grows at rate `h`. It mentions no lift, no tangent vector and no direction,
only which configurations come back — a statement about records.

* ★★★ `catStroke_hasReturnGrowth` — the hyperbolic witness has return growth `2 log φ > 0`;
* `pshift_eq_add` — the constructed de-isolation's fibre action is a translation of the fibre;
* ★★ `not_hasReturnGrowth_pshift` — **no fibre translation has return growth**, for any amount
  and any rate: its return set at every stroke is all of the fibre or empty;
* ★★★ `fibre_return_criterion` — the package: the witness `shearEvolve` acts on the fibre, over any
  interval and at any base point, by a `pshift` (`shearEvolve_snd`), which fails the criterion, while
  the hyperbolic stroke meets it.

## Honest scope

* ⚠️ **Narrows the statement, does not decide #19.** It says which side each corpus witness falls
  on under a criterion that needs no derivative; which map nature uses stays #19.
* The failure of the translation is by the first clause (finite and nonempty) at the very first
  stroke, so no exponent is computed for it; this is sharper than ~~#148~~'s "exponent `0`", which
  needed the lift.

References: `specs/BACKLOG.md` #177, #19, ~~#176~~, ~~#148~~; `specs/POSITS.md` Posit 1;
`Mathlib/Dynamics/ReturnCriterion.lean`, `SigmaLayer/FibreLyapunov.lean` (`shearEvolve_snd`),
`RecordLayer/ShearWitness.lean` (`pshift`, `shearEvolve`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4 RecordLayer

/-- The circle is infinite. -/
theorem infinite_addCircle_one : Infinite (AddCircle (1 : ℝ)) := by
  have : Infinite (Set.Ioc (0 : ℝ) (0 + 1)) := Set.Ioc.infinite (by norm_num)
  exact (AddCircle.equivIoc (1 : ℝ) 0).infinite_iff.2 this

instance : Infinite KTorus := by
  have := infinite_addCircle_one
  infer_instance

/-- ★★★ The hyperbolic witness has return growth `2 log φ`. -/
theorem catStroke_hasReturnGrowth : HasReturnGrowth catStroke (2 * Real.log φ) :=
  cat_hasReturnGrowth

/-- The constructed de-isolation's fibre action is a translation of the fibre. -/
theorem pshift_eq_add (a : ℝ) : pshift a = fun x : KTorus => x + ((a : AddCircle (1 : ℝ)), 0) := by
  funext x
  simp only [pshift]
  ext <;> simp

/-- ★★ **No fibre translation has return growth**, for any amount and any rate. -/
theorem not_hasReturnGrowth_pshift (a : ℝ) (h : ℝ) : ¬ HasReturnGrowth (pshift a) h := by
  rw [pshift_eq_add]
  exact not_hasReturnGrowth_add_right _ h

/-- ★★★ **#19's criterion in record terms.** The hyperbolic stroke has return growth `2 log φ > 0`;
the constructed de-isolation acts on the fibre, over any interval and at any base point, by a
translation `pshift a`, and no translation has return growth at any rate. -/
theorem fibre_return_criterion {Xsel : Type*} {K : ℕ} (idx : Xsel → Fin K) (s t : OnticTime) :
    HasReturnGrowth catStroke (2 * Real.log φ)
      ∧ 0 < 2 * Real.log φ
      ∧ (∀ x : Xsel × KTorus,
          (shearEvolve idx s t x).2 = pshift ((elapsed t - elapsed s) * shearAmt K (idx x.1)) x.2)
      ∧ (∀ (a h : ℝ), ¬ HasReturnGrowth (pshift a) h) :=
  ⟨catStroke_hasReturnGrowth, two_mul_log_goldenRatio_pos, shearEvolve_snd idx s t,
    not_hasReturnGrowth_pshift⟩

end CSD.SigmaLayer

end
