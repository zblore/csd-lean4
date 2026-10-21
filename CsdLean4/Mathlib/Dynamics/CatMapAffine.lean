/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapStrongMixing
public import CsdLean4.Mathlib.Dynamics.LyapunovExponent

/-!
# Affine cat maps are translation-conjugate to the cat map

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #175 (out of #19 and #153).

For `c ∈ T²` the **affine cat map** `p ↦ A p + c`, `A = [[2, 1], [1, 1]]`, is conjugate to the cat
map by a translation: `A − I = [[1, 1], [1, 0]]` has determinant `−1`, so it is invertible over `ℤ`
and `b := (−c₂, c₂ − c₁)` solves `b − A b = c`, whence `A p + c = b + A (p − b)`
(★★ `affineCat_eq_conj`). Strong mixing is invariant under conjugation by a measure-preserving
measurable equivalence (★★ `Mixing.conj_measurableEquiv`, a preimage computation), so every affine
cat map is strongly mixing (★★★ `affineCat_mixing`) and ergodic, and its lift to the plane has the
same derivative `catR` as the cat map's, hence the same Lyapunov exponent `2 log φ` off the stable
line.

* ★★ `Mixing.conj_measurableEquiv` — **strong mixing transports along a measure-preserving
  measurable equivalence**: `Mixing f μ → Mixing (e ∘ f ∘ e.symm) μ`;
* `MeasureTheory.affineCat`, `affineCatShift` — the affine map and its conjugating translation;
* ★★ `MeasureTheory.affineCat_eq_conj` — `affineCat c = τ_b ∘ cat ∘ τ_{−b}`;
* ★★★ `MeasureTheory.affineCat_mixing`, `affineCat_ergodic`, `measurePreserving_affineCat`;
* `MeasureTheory.affineCatR`, `fderiv_affineCatR`, ★ `affineCatR_fderiv_hasLyapunovExponent`,
  `affineCat_coe` — the lift to the plane, its constant derivative `catR`, the exponent, and the
  descent to the torus.

## Honest scope

* The concrete matrix only, as in the rest of the cat-map line. For a general hyperbolic
  `A ∈ SL₂(ℤ)` the same statement needs `det (A − I) = 2 − tr A ≠ 0`, which holds whenever `A` is
  hyperbolic (`|tr A| > 2`), but `A − I` is then invertible over `ℤ` only when `|2 − tr A| = 1`,
  i.e. `tr A = 3` or `tr A = 1`; otherwise the conjugacy exists over `ℚ` (finitely many torsion
  classes) and is not attempted here.
* `Mixing.conj_measurableEquiv` is stated for a measurable equivalence; conjugation by a merely
  measure-preserving bijection with measurable inverse is the same proof.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8 (affine
maps of the torus); `Mathlib/Dynamics/CatMapWitness.lean` (`cat`, `cat_add`, `catHom`),
`CatMapStrongMixing.lean` (`Mixing`, `cat_mixing`), `LyapunovExponent.lean` (`catR`, `ellUR`,
`hasLyapunovExponent_catR`); `specs/BACKLOG.md` #175, #19, #153, #147, #148.
-/

@[expose] public section

open MeasureTheory Filter Topology Function
open scoped goldenRatio

/-! ### Strong mixing is invariant under conjugation -/

/-- ★★ **Strong mixing transports along a measure-preserving measurable equivalence.** -/
theorem Mixing.conj_measurableEquiv {α : Type*} [MeasurableSpace α] {f : α → α} {μ : Measure α}
    (h : Mixing f μ) (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) :
    Mixing (⇑e ∘ f ∘ ⇑e.symm) μ where
  toMeasurePreserving := he.comp (h.toMeasurePreserving.comp (MeasurePreserving.symm e he))
  tendsto_measure_preimage_iterate_inter s t hs ht := by
    have hsemi : Semiconj e f (⇑e ∘ f ∘ ⇑e.symm) := fun x => by simp
    have hiter : ∀ n : ℕ, (⇑e ∘ f ∘ ⇑e.symm)^[n] = ⇑e ∘ f^[n] ∘ ⇑e.symm := by
      intro n
      funext x
      have hx := (hsemi.iterate_right n) (e.symm x)
      simp only [MeasurableEquiv.apply_symm_apply] at hx
      exact hx.symm
    have key : ∀ n : ℕ, μ ((⇑e ∘ f ∘ ⇑e.symm)^[n] ⁻¹' s ∩ t)
        = μ (f^[n] ⁻¹' (⇑e ⁻¹' s) ∩ ⇑e ⁻¹' t) := by
      intro n
      have ht' : t = ⇑e.symm ⁻¹' (⇑e ⁻¹' t) := by
        ext x
        simp
      rw [hiter n, Set.preimage_comp, Set.preimage_comp]
      conv_lhs => rw [ht']
      rw [← Set.preimage_inter, (MeasurePreserving.symm e he).measure_preimage_equiv]
    simp_rw [key]
    have := h.tendsto_measure_preimage_iterate_inter (e.measurable hs) (e.measurable ht)
    rwa [he.measure_preimage_equiv, he.measure_preimage_equiv] at this

namespace MeasureTheory

/-! ### The affine cat map -/

/-- **The affine cat map** `p ↦ A p + c`. -/
noncomputable def affineCat (c : Torus2) : Torus2 → Torus2 := fun p => cat p + c

/-- The translation conjugating `affineCat c` to `cat`: `b = (−c₂, c₂ − c₁)` solves
`b − A b = c`, since `(A − I)⁻¹ = [[0, 1], [1, −1]]` over `ℤ`. -/
noncomputable def affineCatShift (c : Torus2) : Torus2 := (-c.2, c.2 - c.1)

theorem affineCat_apply (c p : Torus2) : affineCat c p = cat p + c := rfl

/-- `b − A b = c` for `b = affineCatShift c`. -/
theorem affineCatShift_sub_cat (c : Torus2) : affineCatShift c - cat (affineCatShift c) = c := by
  refine Prod.ext ?_ ?_ <;> simp only [affineCatShift, cat, Prod.fst_sub, Prod.snd_sub] <;> abel

/-- ★★ **The affine cat map is translation-conjugate to the cat map**:
`affineCat c = τ_b ∘ cat ∘ τ_{−b}` with `b = affineCatShift c`. -/
theorem affineCat_eq_conj (c : Torus2) :
    affineCat c
      = ⇑(MeasurableEquiv.addLeft (affineCatShift c)) ∘ cat
          ∘ ⇑(MeasurableEquiv.addLeft (affineCatShift c)).symm := by
  funext p
  have hb := affineCatShift_sub_cat c
  simp only [Function.comp, MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft,
    affineCat_apply]
  have hsub : cat (p - affineCatShift c) = cat p - cat (affineCatShift c) :=
    map_sub catHom p (affineCatShift c)
  rw [← sub_eq_neg_add, hsub]
  conv_lhs => rw [← hb]
  abel

/-- ★★★ **Every affine cat map is strongly mixing.** -/
theorem affineCat_mixing (c : Torus2) : Mixing (affineCat c) (volume : Measure Torus2) := by
  rw [affineCat_eq_conj]
  exact cat_mixing.conj_measurableEquiv _ (measurePreserving_add_left volume _)

theorem affineCat_ergodic (c : Torus2) : Ergodic (affineCat c) (volume : Measure Torus2) :=
  (affineCat_mixing c).ergodic

theorem measurePreserving_affineCat (c : Torus2) :
    MeasurePreserving (affineCat c) (volume : Measure Torus2) (volume : Measure Torus2) :=
  (affineCat_mixing c).toMeasurePreserving

/-! ### The lift to the plane and its Lyapunov exponent -/

/-- The lift of `affineCat` to the plane. -/
noncomputable def affineCatR (c : ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ := fun v => catR v + c

theorem fderiv_affineCatR (c v : ℝ × ℝ) : fderiv ℝ (affineCatR c) v = catR :=
  (catR.hasFDerivAt.add_const c).fderiv

/-- ★ The lift's derivative has exponent `2 log φ` in every direction off the stable line — the
offset does not enter. -/
theorem affineCatR_fderiv_hasLyapunovExponent (c v : ℝ × ℝ) {w : ℝ × ℝ} (hw : ellUR w ≠ 0) :
    HasLyapunovExponent (fderiv ℝ (affineCatR c) v) w (2 * Real.log φ) := by
  rw [fderiv_affineCatR]
  exact hasLyapunovExponent_catR hw

/-- The affine cat map descends from its lift. -/
theorem affineCat_coe (a b x y : ℝ) :
    affineCat ((a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ)))
        ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((affineCatR (a, b) (x, y)).1 : AddCircle (1 : ℝ)),
          ((affineCatR (a, b) (x, y)).2 : AddCircle (1 : ℝ))) := by
  rw [affineCat_apply, cat_coe, affineCatR]
  simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, AddCircle.coe_add]

end MeasureTheory

end
