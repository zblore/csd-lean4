/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreAffineShears
public import CsdLean4.SigmaLayer.FibreReturnCriterion
public import CsdLean4.Mathlib.Dynamics.ReturnCriterionConj

/-!
# The base-read offsets are invisible to the return criterion too

**Category:** 7-SigmaLayer.
BACKLOG #182 (out of #19, ~~#175~~, ~~#177~~).

~~#175~~ showed that two transverse coordinate-reading shears with base-read offsets `g₁, g₂` compose
to the affine cat map `affineCat (g₁ + g₂, g₂)`, conjugate to the cat stroke by a translation of the
fibre, and that the offsets are invisible to the *Lyapunov* reading of #19's criterion. ~~#177~~
replaced that reading by a derivative-free one: which fibre configurations come back, and how many.
This file carries ~~#175~~ across: return growth is conjugation-invariant
(`HasReturnGrowth.conj`), so for every pair of offsets the offset shears have **the same return
count as the cat stroke at every stroke** and return growth `2 log φ`, and at no other rate.

**What the base says at the base point changes *which* configurations return, never *how many*.**

* `hasReturnGrowth_shearXOff_comp_shearYOff`, `returnCount_shearXOff_comp_shearYOff`;
* ★★★ `fibre_affine_returns` — the package.

## Honest scope

* ⚠️ Narrows, does not decide: the whole affine class of candidate fibre maps passes #19's return
  criterion at one rate; which class nature uses is #19.
* The offsets are real numbers, pointwise in the base, as in ~~#175~~; no base dependence is modelled.

References: `specs/BACKLOG.md` #182, #19, ~~#175~~, ~~#177~~; `SigmaLayer/FibreAffineShears.lean`
(`shearXOff`, `shearYOff`, `shearXOff_comp_shearYOff`, `fibre_affine_shears`),
`SigmaLayer/FibreReturnCriterion.lean` (`catStroke_hasReturnGrowth`),
`Mathlib/Dynamics/ReturnCriterionConj.lean` (`HasReturnGrowth.conj`, `affineCat_hasReturnGrowth`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4 RecordLayer

/-- Two offset shears have return growth `2 log φ`, whatever the offsets. -/
theorem hasReturnGrowth_shearXOff_comp_shearYOff (g₁ g₂ : ℝ) :
    HasReturnGrowth (shearXOff g₁ ∘ shearYOff g₂) (2 * Real.log φ) := by
  rw [shearXOff_comp_shearYOff]
  exact MeasureTheory.affineCat_hasReturnGrowth _

/-- Two offset shears have the cat stroke's return count at every stroke. -/
theorem returnCount_shearXOff_comp_shearYOff (g₁ g₂ : ℝ) (t : ℕ) :
    returnCount (shearXOff g₁ ∘ shearYOff g₂) t = returnCount catStroke t := by
  rw [shearXOff_comp_shearYOff]
  exact MeasureTheory.returnCount_affineCat _ t

/-- ★★★ **The base-read offsets are invisible to the return criterion**: for every pair of offsets
the two transverse shears have return growth `2 log φ`, the cat stroke's return count at every
stroke, and return growth at no other rate. Which conjugacy class nature uses is BACKLOG #19. -/
theorem fibre_affine_returns (g₁ g₂ : ℝ) :
    HasReturnGrowth (shearXOff g₁ ∘ shearYOff g₂) (2 * Real.log φ)
      ∧ (∀ t : ℕ, returnCount (shearXOff g₁ ∘ shearYOff g₂) t = returnCount catStroke t)
      ∧ (∀ h : ℝ, HasReturnGrowth (shearXOff g₁ ∘ shearYOff g₂) h → h = 2 * Real.log φ) :=
  ⟨hasReturnGrowth_shearXOff_comp_shearYOff g₁ g₂, returnCount_shearXOff_comp_shearYOff g₁ g₂,
    fun _ H => H.unique (hasReturnGrowth_shearXOff_comp_shearYOff g₁ g₂)⟩

end CSD.SigmaLayer

end
