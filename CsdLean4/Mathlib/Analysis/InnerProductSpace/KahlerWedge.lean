/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed
public import CsdLean4.Mathlib.Analysis.Normed.Module.Alternating.Wedge

/-!
# `ω ∧ ω` on the flat tangent model, and its closedness

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free).

The consumer of
[`Normed/Module/Alternating/Wedge.lean`](../Normed/Module/Alternating/Wedge.lean), and the
reason that file was written. `Kahler.fundamentalFormAlt` is the fundamental 2-form
`ω u v = im ⟪u,v⟫` as a continuous alternating map (`KahlerClosed.lean`). Until now the
*square* of that form was not a term one could write down in Lean at all: Mathlib's
exterior product is `AlternatingMap`-only, and its continuous analogue did not exist
(MATHLIB-ABSENT(ContinuousAlternatingMap.domCoprod)).

* ★ `Kahler.fundamentalFormSq` — `ω ∧ ω`, reindexed from `Fin 2 ⊕ Fin 2` to `Fin 4`
  along `finSumFinEquiv` so that it lands in the `Fin n`-indexed world the rest of
  Mathlib's differential-form API lives in;
* ★ `Kahler.extDeriv_fundamentalFormSq` — `d(ω ∧ ω) = 0` on the flat model. It is a
  constant form, so this is `extDeriv_const`; the content is that there is now an object
  to apply it to.

## Honest scope

⚠️ **This is the flat model, and it is one power.** What is delivered is that `ω ∧ ω`
exists as a continuous alternating 4-form on `E` and is closed. What is NOT delivered,
and must not be read into it:

* **no identification with a volume**. The top-power identity `ω^(N-1)/(N-1)! = μ_FS` is
  a statement on the quotient manifold `ℂℙ^(N-1)`, and making that space a manifold in
  Mathlib's sense is step (0) of the staged plan, probed and recorded in
  `specs/BACKLOG.md` (XL). Nothing here compares `ω ∧ ω` to any measure;
* **no general power `ω^(∧k)`**. Iterating needs a recursion on the index type; this file
  writes the `k = 2` case by hand;
* **no claim about `ℂℙ²`**. `ω ∧ ω` is a 4-form on the ambient `E`. When `E` is
  2-complex-dimensional it is top-degree *on the flat model*, which is a statement about
  `E`, not about the projective quotient.

The honest summary is the one the gap row now carries: a top-power identity has gone from
*unsayable* to *sayable*, and this module is the witness that it has.

References: `MATHLIB-GAPS.md` (Kahler / symplectic manifold API, step (1));
`specs/BACKLOG.md` (XL, "Manifold exterior calculus");
`CsdLean4/Mathlib/Analysis/InnerProductSpace/KahlerClosed.lean`
(`fundamentalFormAlt`, `extDeriv_const`).
-/

@[expose] public section

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- ★ **`ω ∧ ω`**: the exterior square of the fundamental 2-form, as a continuous
alternating 4-form on the flat model `E`.

The wedge is taken with the codomains paired by multiplication
(`ContinuousLinearMap.mul ℝ ℝ`, the real-valued case of
`ContinuousAlternatingMap.wedge`), then reindexed `Fin 2 ⊕ Fin 2 ≃ Fin 4`. -/
noncomputable def fundamentalFormSq : E [⋀^Fin 4]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.domDomCongr finSumFinEquiv
    (ContinuousAlternatingMap.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (fundamentalFormAlt : E [⋀^Fin 2]→L[ℝ] ℝ) fundamentalFormAlt)

/-- `ω ∧ ω` evaluated at four vectors is the reindexed wedge — the definitional
unfolding, recorded so consumers need not unfold `domDomCongr` by hand. -/
theorem fundamentalFormSq_apply (v : Fin 4 → E) :
    fundamentalFormSq v =
      ContinuousAlternatingMap.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (fundamentalFormAlt : E [⋀^Fin 2]→L[ℝ] ℝ) fundamentalFormAlt
        (fun i => v (finSumFinEquiv i)) :=
  rfl

/-- ★ **`d(ω ∧ ω) = 0`** on the flat tangent model.

`ω ∧ ω` is a constant differential form, so this is `extDeriv_const`. The content is not
the proof — it is that the *statement* can now be made: before
`ContinuousAlternatingMap.wedge` there was no term `ω ∧ ω` to differentiate. -/
theorem extDeriv_fundamentalFormSq :
    extDeriv (fun _ : E => (fundamentalFormSq : E [⋀^Fin 4]→L[ℝ] ℝ)) = 0 :=
  extDeriv_const _

/-- `d(ω ∧ ω) = 0`, pointwise form. -/
theorem extDeriv_fundamentalFormSq_apply (x : E) :
    extDeriv (fun _ : E => (fundamentalFormSq : E [⋀^Fin 4]→L[ℝ] ℝ)) x = 0 :=
  extDeriv_const_apply _ x

end Kahler
