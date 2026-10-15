/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreLyapunov
public import CsdLean4.Mathlib.Dynamics.CatMapShears
public import CsdLean4.Mathlib.Geometry.Manifold.TranslationAtlasForm

/-!
# The fibre carries both record coordinates: hyperbolicity needs the second coordinate sheared

**Category:** 7-SigmaLayer.
BACKLOG #153 (out of #19 and ~~#148~~); the structural reading of Posit 10 in its I3 form.

~~#148~~ put the corpus's two fibre maps on the two sides of one line: the hyperbolic witness
`catStroke` stretches at `2 log φ`, the constructed de-isolation witness `shearEvolve` stretches
nothing (`fibre_witnesses_lyapunov`). This file says **why**, in terms of what each map does to the
two coordinates of the fibre `T² = KTorus`.

* The constructed de-isolation moves **one** fibre coordinate by an amount read off the **base**:
  `(shearEvolve idx s t x).2 = pshift (amount of the selector) x.2` (`shearEvolve_snd`), and the
  second fibre coordinate is untouched (★ `shearEvolve_snd_snd`). It is a `pshift`-type map.
* The hyperbolic stroke is **two transverse** `pshift`-type maps, each reading the *other* fibre
  coordinate: ★★ `catStroke_eq_two_shears`, `catStroke = (shift the first coordinate by the second)
  ∘ (shift the second coordinate by the first)` — `shearX_eq_pshift`, `shearY_eq_qshift`, where
  `qshift` is the transverse partner of `pshift` (`measurePreserving_qshift`).
* No single `pshift`-type map is the hyperbolic stroke (★ `catStroke_ne_pshift_type`): the
  stroke moves the second coordinate (`catStroke_snd_ne`), and a `pshift`-type map never does.
* **Neither shear stretches on its own.** Each factor's lift has Lyapunov exponent `0` in every
  direction (`shearXR_fderiv_hasLyapunovExponent`, `shearYR_fderiv_hasLyapunovExponent`) while
  the composition has exponent `2 log φ` (`catR_fderiv_hasLyapunovExponent`). The stretching is
  produced by the transversality of the two shears, not by either of them. Both factors preserve
  the torus area form (`areaForm_shearXR`, `areaForm_shearYR`): the factoring is symplectic.

★★★ `fibre_two_shears` states the package. Read against #19's criterion (*the de-isolation flow
has a positive Lyapunov exponent on the fibre*): a de-isolation that shears the fibre along `q`
alone, by any base-read amount, has exponent `0` — so a de-isolation that could discharge R-019's
map identification **must act on the second fibre coordinate too**, reading the first. That second
coordinate is the one Posit 10 (I3, author's decision of 2026-10-10) says carries record content.

## Honest scope

* ⚠️ **Structure, not derivation.** This says what a hyperbolic de-isolation would have to do to
  the fibre; it does not say that nature's does it, and nothing here decides #19 or R-019.
* The row that priced this file said each shear factor "carries the same flux obstruction as the
  corpus's shear". That wording does not apply and is corrected here: the shear factors are
  **linear toral automorphisms**, not time-one maps of vector fields on `T²` (the plane flow
  `(x, y) ↦ (x, y + t x)` descends only at integer `t`), so the flux obstruction for translation
  fields (`not_isHamiltonianVectorField_torusStrokeField`, `LF4/ArenaStrokeFlux.lean`) is about a
  different kind of map. What *is* true and proved of the factors is that they are symplectic
  (area-preserving) and Haar-preserving.
* The exponents are those of the lifts' derivatives, constant for every map here, as in
  `FibreLyapunov.lean`; no tangent bundle on `T²` is used.
* `pshift`-type is read literally: a map `x ↦ pshift (g x) x` for some real-valued `g`. The
  `shearEvolve` fibre action is of that type with `g` reading the base; `shearX` is of that type
  with `g = rep ∘ Prod.snd`.

References: `specs/BACKLOG.md` #153, #19, ~~#148~~; `specs/POSITS.md` Posit 10;
`Mathlib/Dynamics/CatMapShears.lean` (`shearX`, `shearY`, `cat_eq_shearX_comp_shearY`,
`hasLyapunovExponent_shearXR`, `cat_two_shears`); `SigmaLayer/FibreLyapunov.lean`
(`fibre_witnesses_lyapunov`, `shearEvolve_snd`); `RecordLayer/ShearWitness.lean` (`pshift`,
`shearEvolve`); `RecordLayer/CircleFibre.lean` (`rep`, `coe_rep`);
`Mathlib/Geometry/Manifold/TranslationAtlasForm.lean` (`TorusForm.areaForm`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped goldenRatio

namespace CSD.SigmaLayer

open LF4 RecordLayer

/-! ### The transverse partner of `pshift` -/

/-- Translate the **second** fibre coordinate by `a`: the transverse partner of `pshift`. -/
noncomputable def qshift (a : ℝ) (x : KTorus) : KTorus := (x.1, x.2 + (a : AddCircle (1 : ℝ)))

@[simp] theorem qshift_fst (a : ℝ) (x : KTorus) : (qshift a x).1 = x.1 := rfl

/-- A `pshift`-type map never moves the second coordinate. -/
@[simp] theorem pshift_snd (a : ℝ) (x : KTorus) : (pshift a x).2 = x.2 := rfl

/-- Translating the second coordinate preserves Haar measure on the fibre. -/
theorem measurePreserving_qshift (a : ℝ) :
    MeasurePreserving (qshift a) (volume : Measure KTorus) volume := by
  have he : qshift a
      = fun x : KTorus => (((0 : AddCircle (1 : ℝ)), (a : AddCircle (1 : ℝ))) + x) := by
    funext x
    simp [qshift, Prod.ext_iff, add_comm]
  rw [he]
  exact measurePreserving_add_left _ _

/-! ### The two shears are coordinate-reading shifts -/

/-- The horizontal shear shifts the first coordinate by the second. -/
theorem shearX_eq_pshift (x : KTorus) : MeasureTheory.shearX x = pshift (rep x.2) x := by
  simp [MeasureTheory.shearX, pshift, coe_rep]

/-- The vertical shear shifts the second coordinate by the first. -/
theorem shearY_eq_qshift (x : KTorus) : MeasureTheory.shearY x = qshift (rep x.1) x := by
  simp [MeasureTheory.shearY, qshift, coe_rep, add_comm]

/-- ★★ **The hyperbolic stroke is two transverse coordinate-reading shifts**: the second coordinate
shifted by the first, then the first shifted by the (new) second. -/
theorem catStroke_eq_two_shears :
    catStroke
      = (fun x : KTorus => pshift (rep x.2) x) ∘ (fun x : KTorus => qshift (rep x.1) x) := by
  funext x
  show MeasureTheory.cat x = pshift (rep (qshift (rep x.1) x).2) (qshift (rep x.1) x)
  rw [cat_eq_shearX_comp_shearY, Function.comp_apply, shearY_eq_qshift, shearX_eq_pshift]

/-! ### One shear against two -/

/-- ★ **The constructed de-isolation leaves the second fibre coordinate untouched.** Together with
`shearEvolve_snd` (the first coordinate is shifted by a base-read amount) this says the witness is
a single `pshift`-type map of the fibre. -/
theorem shearEvolve_snd_snd {Xsel : Type*} {K : ℕ} (idx : Xsel → Fin K) (s t : OnticTime)
    (x : Xsel × KTorus) :
    (shearEvolve idx s t x).2.2 = x.2.2 := rfl

/-- The hyperbolic stroke moves the second coordinate of `(1/2, 0)`. -/
theorem catStroke_snd_ne : ∃ x : KTorus, (catStroke x).2 ≠ x.2 := by
  refine ⟨(((1 / 2 : ℝ) : AddCircle (1 : ℝ)), 0), ?_⟩
  show ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) + 0 ≠ 0
  rw [add_zero]
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [zsmul_eq_mul, mul_one] at hn
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- ★ **No single `pshift`-type map is the hyperbolic stroke**, whatever its amount reads. -/
theorem catStroke_ne_pshift_type (g : KTorus → ℝ) :
    catStroke ≠ fun x : KTorus => pshift (g x) x := by
  intro h
  obtain ⟨x, hx⟩ := catStroke_snd_ne
  exact hx (congrArg (fun f : KTorus → KTorus => (f x).2) h)

/-! ### Neither shear stretches; the composition does -/

/-- The lift of the horizontal shear has exponent `0` in every direction. -/
theorem shearXR_fderiv_hasLyapunovExponent (v w : ℝ × ℝ) :
    HasLyapunovExponent (fderiv ℝ shearXR v) w 0 := by
  rw [shearXR.fderiv]
  exact hasLyapunovExponent_shearXR w

/-- The lift of the vertical shear has exponent `0` in every direction. -/
theorem shearYR_fderiv_hasLyapunovExponent (v w : ℝ × ℝ) :
    HasLyapunovExponent (fderiv ℝ shearYR v) w 0 := by
  rw [shearYR.fderiv]
  exact hasLyapunovExponent_shearYR w

/-- The horizontal shear's lift preserves the torus area form. -/
theorem areaForm_shearXR (u v : ℝ × ℝ) :
    TorusForm.areaForm ![shearXR u, shearXR v] = TorusForm.areaForm ![u, v] := by
  simp only [TorusForm.areaForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    TorusForm.area]
  exact shearXR_area u v

/-- The vertical shear's lift preserves the torus area form. -/
theorem areaForm_shearYR (u v : ℝ × ℝ) :
    TorusForm.areaForm ![shearYR u, shearYR v] = TorusForm.areaForm ![u, v] := by
  simp only [TorusForm.areaForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    TorusForm.area]
  exact shearYR_area u v

/-! ### ★★★ The package -/

/-- ★★★ **The fibre carries both record coordinates: hyperbolicity needs the second coordinate
sheared.** The hyperbolic stroke is two transverse coordinate-reading shifts of the fibre and is
not any single `pshift`-type map; the constructed de-isolation is a single `pshift`-type map whose
amount reads the base and whose second fibre coordinate is untouched; each shear's lift has
Lyapunov exponent `0` in every direction while their composition has exponent `2 log φ` off the
stable line. A de-isolation that shears along `q` alone cannot meet #19's criterion. -/
theorem fibre_two_shears {Xsel : Type*} {K : ℕ} (idx : Xsel → Fin K) (s t : OnticTime) :
    catStroke
        = (fun x : KTorus => pshift (rep x.2) x) ∘ (fun x : KTorus => qshift (rep x.1) x)
      ∧ (∀ g : KTorus → ℝ, catStroke ≠ fun x : KTorus => pshift (g x) x)
      ∧ (∀ x : Xsel × KTorus,
          (shearEvolve idx s t x).2
              = pshift ((elapsed t - elapsed s) * shearAmt K (idx x.1)) x.2
            ∧ (shearEvolve idx s t x).2.2 = x.2.2)
      ∧ (∀ v w : ℝ × ℝ, HasLyapunovExponent (fderiv ℝ shearXR v) w 0)
      ∧ (∀ v w : ℝ × ℝ, HasLyapunovExponent (fderiv ℝ shearYR v) w 0)
      ∧ (∀ v w : ℝ × ℝ, ellUR w ≠ 0 →
          HasLyapunovExponent (fderiv ℝ catR v) w (2 * Real.log φ)) :=
  ⟨catStroke_eq_two_shears, catStroke_ne_pshift_type,
    fun x => ⟨shearEvolve_snd idx s t x, shearEvolve_snd_snd idx s t x⟩,
    shearXR_fderiv_hasLyapunovExponent, shearYR_fderiv_hasLyapunovExponent,
    fun v _ hw => catR_fderiv_hasLyapunovExponent v hw⟩

end CSD.SigmaLayer

end
