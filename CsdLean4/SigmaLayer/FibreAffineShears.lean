/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreTwoShears
public import CsdLean4.Mathlib.Dynamics.CatMapAffine

/-!
# Two transverse shears with base-read offsets are the cat stroke up to a translation

**Category:** 7-SigmaLayer.
BACKLOG #175 (out of #19 and ~~#153~~): the narrowing brick for Posit 1's discharge.

~~#153~~ said what a hyperbolic de-isolation must do to the fibre: shear **both** coordinates, each
reading the other (`catStroke_eq_two_shears`), where the constructed witness `shearEvolve` shears
one coordinate by a **base-read** amount. The natural class that does both is two transverse
coordinate-reading shears each carrying a base-read offset `g₁, g₂` (whatever the base says at that
base point):

  `shearXOff g₁ ∘ shearYOff g₂ = affineCat (g₁ + g₂, g₂)`,

an **affine cat map** `x ↦ A x + c`. `CatMapAffine.lean` shows every affine cat map is conjugate to
the cat map by a translation of the fibre, so it is strongly mixing and its lift stretches at
`2 log φ` — **the base-read offsets are invisible to #19's criterion** (*the de-isolation flow has a
positive Lyapunov exponent on the fibre*). What decides the criterion is the transverse pair, not
what the base says; the choice #19 is about is between conjugacy classes of fibre maps.

* `shearXOff`, `shearYOff` — the two coordinate-reading shears with an offset; at offset `0` they
  are `MeasureTheory.shearX`, `shearY` (`shearXOff_zero`, `shearYOff_zero`);
* ★★ `shearXOff_comp_shearYOff` — **two offset shears are the affine cat map** `affineCat (g₁+g₂, g₂)`;
* ★★★ `mixing_shearXOff_comp_shearYOff`, `ergodic_shearXOff_comp_shearYOff`,
  `measurePreserving_shearXOff_comp_shearYOff` — **strongly mixing, for every pair of offsets**;
* `shearXOff_comp_shearYOff_coe`, ★ `lift_fderiv_hasLyapunovExponent` — the lift's derivative is
  `catR`, exponent `2 log φ` off the stable line, offsets or not;
* ★★★ `fibre_affine_shears` — the package, read against #19.

## Honest scope

* ⚠️ **Narrows, does not decide.** One whole conjugacy class of candidate fibre maps — the affine
  cat maps, i.e. two transverse coordinate-reading shears with any base-read offsets — is shown to be
  dynamically the cat stroke. Which class nature uses stays #19; nothing here says the de-isolation
  is of this class.
* The offsets `g₁, g₂` are real numbers, read as "what the base says at this base point"; the
  statement is pointwise in the base, as `fibre_two_shears` is. No base dependence is modelled.
* The cat matrix only, as in the whole line.

References: `specs/BACKLOG.md` #175, #19, ~~#153~~, ~~#147~~, ~~#148~~; `specs/POSITS.md` Posit 1,
Posit 10; `SigmaLayer/FibreTwoShears.lean` (`qshift`, `catStroke_eq_two_shears`,
`fibre_two_shears`); `Mathlib/Dynamics/CatMapAffine.lean` (`affineCat`, `affineCat_mixing`,
`affineCatR_fderiv_hasLyapunovExponent`); `RecordLayer/ShearWitness.lean` (`pshift`);
`RecordLayer/CircleFibre.lean` (`rep`, `coe_rep`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4 RecordLayer

/-! ### The two shears with offsets -/

/-- Shift the first fibre coordinate by the second plus an offset `g`. -/
noncomputable def shearXOff (g : ℝ) (x : KTorus) : KTorus := pshift (rep x.2 + g) x

/-- Shift the second fibre coordinate by the first plus an offset `g`. -/
noncomputable def shearYOff (g : ℝ) (x : KTorus) : KTorus := qshift (rep x.1 + g) x

theorem shearXOff_apply (g : ℝ) (x : KTorus) :
    shearXOff g x = (x.1 + x.2 + (g : AddCircle (1 : ℝ)), x.2) := by
  simp only [shearXOff, pshift, AddCircle.coe_add, coe_rep, add_assoc]

theorem shearYOff_apply (g : ℝ) (x : KTorus) :
    shearYOff g x = (x.1, x.2 + x.1 + (g : AddCircle (1 : ℝ))) := by
  simp only [shearYOff, qshift, AddCircle.coe_add, coe_rep, add_assoc]

theorem shearXOff_zero : shearXOff 0 = MeasureTheory.shearX := by
  funext x
  rw [shearXOff_apply]
  simp [MeasureTheory.shearX]

theorem shearYOff_zero : shearYOff 0 = MeasureTheory.shearY := by
  funext x
  rw [shearYOff_apply]
  simp [MeasureTheory.shearY, add_comm]

/-- ★★ **Two transverse coordinate-reading shears with offsets are the affine cat map**
`x ↦ A x + (g₁ + g₂, g₂)`. -/
theorem shearXOff_comp_shearYOff (g₁ g₂ : ℝ) :
    shearXOff g₁ ∘ shearYOff g₂
      = MeasureTheory.affineCat (((g₁ + g₂ : ℝ) : AddCircle (1 : ℝ)), (g₂ : AddCircle (1 : ℝ))) := by
  funext x
  rw [Function.comp_apply, shearXOff_apply, shearYOff_apply, MeasureTheory.affineCat_apply]
  refine Prod.ext ?_ ?_ <;> simp only [MeasureTheory.cat, Prod.fst_add, Prod.snd_add,
    AddCircle.coe_add] <;> abel

/-! ### Mixing and the exponent, for every pair of offsets -/

/-- ★★★ **Two offset shears are strongly mixing**, whatever the offsets. -/
theorem mixing_shearXOff_comp_shearYOff (g₁ g₂ : ℝ) :
    Mixing (shearXOff g₁ ∘ shearYOff g₂) (volume : Measure KTorus) := by
  rw [shearXOff_comp_shearYOff]
  exact MeasureTheory.affineCat_mixing _

theorem ergodic_shearXOff_comp_shearYOff (g₁ g₂ : ℝ) :
    Ergodic (shearXOff g₁ ∘ shearYOff g₂) (volume : Measure KTorus) :=
  (mixing_shearXOff_comp_shearYOff g₁ g₂).ergodic

theorem measurePreserving_shearXOff_comp_shearYOff (g₁ g₂ : ℝ) :
    MeasurePreserving (shearXOff g₁ ∘ shearYOff g₂) (volume : Measure KTorus)
      (volume : Measure KTorus) :=
  (mixing_shearXOff_comp_shearYOff g₁ g₂).toMeasurePreserving

/-- The offset shears descend from the lift `affineCatR (g₁ + g₂, g₂)`. -/
theorem shearXOff_comp_shearYOff_coe (g₁ g₂ x y : ℝ) :
    (shearXOff g₁ ∘ shearYOff g₂) ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((MeasureTheory.affineCatR (g₁ + g₂, g₂) (x, y)).1 : AddCircle (1 : ℝ)),
          ((MeasureTheory.affineCatR (g₁ + g₂, g₂) (x, y)).2 : AddCircle (1 : ℝ))) := by
  rw [shearXOff_comp_shearYOff, MeasureTheory.affineCat_coe]

/-- ★ The lift's derivative has exponent `2 log φ` off the stable line: the offsets do not enter. -/
theorem lift_fderiv_hasLyapunovExponent (g₁ g₂ : ℝ) (v : ℝ × ℝ) {w : ℝ × ℝ} (hw : ellUR w ≠ 0) :
    HasLyapunovExponent (fderiv ℝ (MeasureTheory.affineCatR (g₁ + g₂, g₂)) v) w
      (2 * Real.log φ) :=
  MeasureTheory.affineCatR_fderiv_hasLyapunovExponent _ v hw

/-! ### The package -/

/-- ★★★ **Two transverse coordinate-reading shears with base-read offsets are the cat stroke up to a
translation of the fibre**: they compose to the affine cat map `A x + (g₁ + g₂, g₂)`, which is
strongly mixing and whose lift stretches at `2 log φ` off the stable line, for every pair of
offsets. Read against #19's criterion: the base-read offsets are invisible to it; what decides it
is the transverse pair. Which conjugacy class nature uses is BACKLOG #19. -/
theorem fibre_affine_shears (g₁ g₂ : ℝ) :
    shearXOff g₁ ∘ shearYOff g₂
        = MeasureTheory.affineCat (((g₁ + g₂ : ℝ) : AddCircle (1 : ℝ)), (g₂ : AddCircle (1 : ℝ)))
      ∧ Mixing (shearXOff g₁ ∘ shearYOff g₂) (volume : Measure KTorus)
      ∧ (∀ v w : ℝ × ℝ, ellUR w ≠ 0 →
          HasLyapunovExponent (fderiv ℝ (MeasureTheory.affineCatR (g₁ + g₂, g₂)) v) w
            (2 * Real.log φ)) :=
  ⟨shearXOff_comp_shearYOff g₁ g₂, mixing_shearXOff_comp_shearYOff g₁ g₂,
    fun v _ hw => lift_fderiv_hasLyapunovExponent g₁ g₂ v hw⟩

end CSD.SigmaLayer

end
