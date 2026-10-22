/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.ReturnCriterion
public import CsdLean4.Mathlib.Dynamics.CatMapAffine

/-!
# Return growth is invariant under conjugation; the affine cat maps have it

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #182 (out of #19, #175, #177).

For a bijection `e : α ≃ β` and `f : α → α`, `(e ∘ f ∘ e.symm)^[t] = e ∘ f^[t] ∘ e.symm`, so `e`
restricts to a bijection between the `t`-return sets of `f` and of its conjugate. Hence the return
counts agree at every `t`, and `HasReturnGrowth` (#177) transports along `e` in both directions.
Applied to the translation conjugacy `affineCat c = τ_b ∘ cat ∘ τ_{−b}` (#175), every affine cat map
has the cat map's return count `L₂ₜ − 2` (#176) at every `t ≥ 1` and return growth `2 log φ`.

* `iterate_conj`, `iterate_conj_apply` — the iterates of a conjugate;
* `fixedPointsEquivConj` — `e` as a bijection of return sets; `returnCount_conj`;
* ★★ `HasReturnGrowth.conj`, `hasReturnGrowth_conj_iff` — **return growth is conjugation-invariant**;
* `HasReturnGrowth.unique` — a map has return growth at most at one rate;
* `MeasureTheory.affineCat_eq_conj_equiv`, `returnCount_affineCat`,
  `card_fixedPoints_affineCat_iterate`;
* ★★★ `MeasureTheory.affineCat_hasReturnGrowth` — **every affine cat map has return growth
  `2 log φ`**.

## Honest scope

* Conjugation by a bijection only; a semiconjugacy (a surjection `e` with `e ∘ f = g ∘ e`) carries
  return sets forward but not their cardinalities, and no such statement is made.
* The concrete cat matrix only, through #175's conjugacy; for a general hyperbolic `B ∈ GL₂(ℤ)` the
  affine class `p ↦ B p + c` is conjugate to `toral B` by a translation whenever `B − I` is invertible
  over `ℤ`, which the scope note of `CatMapAffine.lean` discusses and which is not attempted here.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8, §3.2;
`Mathlib/Dynamics/ReturnCriterion.lean` (#177, `HasReturnGrowth`, `cat_hasReturnGrowth`),
`Mathlib/Dynamics/CatMapAffine.lean` (#175, `affineCat_eq_conj`),
`Mathlib/Dynamics/CatMapPeriodicPoints.lean` (#176, `card_fixedPoints_cat_iterate`);
`specs/BACKLOG.md` #182, #19, #175, #177.
-/

@[expose] public section

open Filter Topology Function
open scoped goldenRatio

/-! ### Iterates and return sets of a conjugate -/

section Conj

variable {α β : Type*}

theorem iterate_conj (e : α ≃ β) (f : α → α) (t : ℕ) :
    (⇑e ∘ f ∘ ⇑e.symm)^[t] = ⇑e ∘ f^[t] ∘ ⇑e.symm := by
  induction t with
  | zero => funext y; simp
  | succ k ih =>
      funext y
      rw [iterate_succ_apply', ih]
      simp only [comp_apply, Equiv.symm_apply_apply]
      rw [iterate_succ_apply']

theorem iterate_conj_apply (e : α ≃ β) (f : α → α) (t : ℕ) (y : β) :
    (⇑e ∘ f ∘ ⇑e.symm)^[t] y = e (f^[t] (e.symm y)) := by
  rw [iterate_conj]
  rfl

/-- `e` restricts to a bijection between the `t`-return sets of `f` and of its conjugate. -/
def fixedPointsEquivConj (e : α ≃ β) (f : α → α) (t : ℕ) :
    {x : α // f^[t] x = x} ≃ {y : β // (⇑e ∘ f ∘ ⇑e.symm)^[t] y = y} where
  toFun x := ⟨e x.1, by rw [iterate_conj_apply, e.symm_apply_apply, x.2]⟩
  invFun y := ⟨e.symm y.1, by
    have hy := y.2
    rw [iterate_conj_apply] at hy
    exact e.eq_symm_apply.2 hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

theorem returnCount_conj (e : α ≃ β) (f : α → α) (t : ℕ) :
    returnCount (⇑e ∘ f ∘ ⇑e.symm) t = returnCount f t :=
  (Nat.card_congr (fixedPointsEquivConj e f t)).symm

/-! ### Return growth transports -/

/-- ★★ **Return growth is invariant under conjugation by a bijection.** -/
theorem HasReturnGrowth.conj {f : α → α} {h : ℝ} (H : HasReturnGrowth f h) (e : α ≃ β) :
    HasReturnGrowth (⇑e ∘ f ∘ ⇑e.symm) h where
  finite t := by
    have := H.finite t
    exact Finite.of_equiv _ (fixedPointsEquivConj e f (t + 1))
  nonempty t := (fixedPointsEquivConj e f (t + 1)).nonempty_congr.1 (H.nonempty t)
  tendsto := by simpa only [returnCount_conj] using H.tendsto

theorem symm_conj_conj (e : α ≃ β) (f : α → α) :
    ⇑e.symm ∘ (⇑e ∘ f ∘ ⇑e.symm) ∘ ⇑e.symm.symm = f := by
  funext x
  simp

theorem hasReturnGrowth_conj_iff (e : α ≃ β) (f : α → α) (h : ℝ) :
    HasReturnGrowth (⇑e ∘ f ∘ ⇑e.symm) h ↔ HasReturnGrowth f h :=
  ⟨fun H => by simpa only [symm_conj_conj] using H.conj e.symm, fun H => H.conj e⟩

/-- A map has return growth at most at one rate. -/
theorem HasReturnGrowth.unique {f : α → α} {h h' : ℝ} (H : HasReturnGrowth f h)
    (H' : HasReturnGrowth f h') : h = h' :=
  tendsto_nhds_unique H.tendsto H'.tendsto

end Conj

/-! ### The affine cat maps -/

namespace MeasureTheory

/-- #175's conjugacy, read through the underlying `Equiv`. -/
theorem affineCat_eq_conj_equiv (c : Torus2) :
    affineCat c
      = ⇑(MeasurableEquiv.addLeft (affineCatShift c)).toEquiv ∘ cat
          ∘ ⇑(MeasurableEquiv.addLeft (affineCatShift c)).toEquiv.symm := by
  rw [MeasurableEquiv.coe_toEquiv, MeasurableEquiv.coe_toEquiv_symm]
  exact affineCat_eq_conj c

/-- The affine cat map has the cat map's return count at every `t`. -/
theorem returnCount_affineCat (c : Torus2) (t : ℕ) :
    returnCount (affineCat c) t = returnCount cat t := by
  rw [affineCat_eq_conj_equiv]
  exact returnCount_conj _ cat t

/-- `#Fix((affineCat c)^[t]) = L₂ₜ − 2`, as for the cat map (#176). -/
theorem card_fixedPoints_affineCat_iterate (c : Torus2) (s : ℕ) :
    Nat.card {p : Torus2 // (affineCat c)^[s + 1] p = p} = (lucasEven (s + 1) - 2).natAbs := by
  have h := returnCount_affineCat c (s + 1)
  unfold returnCount at h
  rw [h]
  exact card_fixedPoints_cat_iterate s

/-- ★★★ **Every affine cat map has return growth `2 log φ`**: the base-read offset of #175 is
invisible to the return criterion, stroke by stroke. -/
theorem affineCat_hasReturnGrowth (c : Torus2) :
    HasReturnGrowth (affineCat c) (2 * Real.log φ) := by
  rw [affineCat_eq_conj_equiv]
  exact cat_hasReturnGrowth.conj _

end MeasureTheory

end
