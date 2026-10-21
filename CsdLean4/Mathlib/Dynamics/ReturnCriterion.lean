/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapPeriodicPoints

/-!
# The return criterion: growth of the periodic-point count, with no derivative

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #177 (out of #19 and #176).

A self-map `f` of a type **has return growth `h`** when, for every `t ≥ 1`, the set of points with
`f^[t] x = x` is finite and nonempty, and `(1/t) log #{x | f^[t] x = x} → h`. For a hyperbolic
toral automorphism this `h` is the topological entropy and equals the Lyapunov exponent; the
definition itself mentions neither a lift, a derivative nor a direction, only which points come back.

* `returnCount f t := Nat.card {x // f^[t] x = x}`, `HasReturnGrowth f h`;
* `iterate_add_right` — `(· + c)^[t] = (· + t • c)` in an additive monoid;
* `add_right_eq_self_iff` — a translation of an additive group fixes a point iff it is trivial;
* ★★ `not_hasReturnGrowth_add_right` — **no translation of an infinite additive group has return
  growth**: its return set at every `t` is infinite or empty;
* ★★★ `cat_hasReturnGrowth` — **the cat map has return growth `2 log φ`** (#176).

## Honest scope

* `HasReturnGrowth` asks for a limit; a `limsup` version would cover maps whose counts oscillate,
  and is not needed for either example.
* Translations are the only non-example proved; a general toral automorphism with an eigenvalue on
  the unit circle (e.g. a shear, #153) also has return sets that are infinite at some `t`, and is not
  treated.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §3.2
(periodic points and topological entropy); `Mathlib/Dynamics/CatMapPeriodicPoints.lean` (#176);
`specs/BACKLOG.md` #177, #19, #176, #148.
-/

@[expose] public section

open Filter Topology Function
open scoped goldenRatio

/-! ### The criterion -/

/-- The number of points returning after `t` steps (`0` if infinitely many, by `Nat.card`'s
convention; `HasReturnGrowth` rules that case out). -/
noncomputable def returnCount {α : Type*} (f : α → α) (t : ℕ) : ℕ := Nat.card {x : α // f^[t] x = x}

/-- **`f` has return growth `h`**: at every `t ≥ 1` finitely many but at least one point returns, and
the count grows at rate `h`. -/
structure HasReturnGrowth {α : Type*} (f : α → α) (h : ℝ) : Prop where
  finite : ∀ t : ℕ, Finite {x : α // f^[t + 1] x = x}
  nonempty : ∀ t : ℕ, Nonempty {x : α // f^[t + 1] x = x}
  tendsto : Tendsto (fun t : ℕ => Real.log (returnCount f (t + 1)) / ((t : ℝ) + 1)) atTop (𝓝 h)

/-! ### Translations fail it -/

theorem iterate_add_right {M : Type*} [AddCommMonoid M] (c : M) (t : ℕ) :
    (fun x : M => x + c)^[t] = fun x => x + t • c := by
  induction t with
  | zero => funext x; simp
  | succ k ih =>
      funext x
      rw [iterate_succ_apply', ih]
      simp only [succ_nsmul, add_assoc]

/-- A translation fixes a point iff it is the trivial translation. -/
theorem add_right_eq_self_iff {G : Type*} [AddGroup G] (c x : G) : x + c = x ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun y => -x + y) h
    simpa using this
  · rintro rfl
    simp

/-- ★★ **No translation of an infinite additive group has return growth**: at every `t` its return
set is all of the group (`t • c = 0`) or empty. -/
theorem not_hasReturnGrowth_add_right {G : Type*} [AddCommGroup G] [Infinite G] (c : G) (h : ℝ) :
    ¬ HasReturnGrowth (fun x : G => x + c) h := by
  intro H
  have hfin := H.finite 0
  have hne := H.nonempty 0
  rw [iterate_add_right] at hfin hne
  by_cases hc : (0 + 1 : ℕ) • c = 0
  · -- every point returns: the return set is the whole infinite group
    have hall : ∀ x : G, x + (0 + 1 : ℕ) • c = x := fun x => by rw [hc, add_zero]
    have : Infinite {x : G // x + (0 + 1 : ℕ) • c = x} :=
      Infinite.of_injective (fun x : G => (⟨x, hall x⟩ : {x : G // x + (0 + 1 : ℕ) • c = x}))
        fun a b hab => congrArg Subtype.val hab
    exact not_finite {x : G // x + (0 + 1 : ℕ) • c = x}
  · -- no point returns
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact hc ((add_right_eq_self_iff _ x).1 hx)

/-! ### The cat map has it -/

/-- ★★★ **The cat map has return growth `2 log φ`**: `#Fix(cat^[t]) = L₂ₜ − 2 ≥ 1` is finite and
positive at every `t ≥ 1`, and grows at the Lyapunov exponent (#176). -/
theorem cat_hasReturnGrowth : HasReturnGrowth MeasureTheory.cat (2 * Real.log φ) where
  finite t := by
    have h : Nat.card {p : MeasureTheory.Torus2 // MeasureTheory.cat^[t + 1] p = p} ≠ 0 := by
      rw [MeasureTheory.card_fixedPoints_cat_iterate]
      have := MeasureTheory.three_le_lucasEven_succ t
      omega
    exact Nat.finite_of_card_ne_zero h
  nonempty t := by
    have h : Nat.card {p : MeasureTheory.Torus2 // MeasureTheory.cat^[t + 1] p = p} ≠ 0 := by
      rw [MeasureTheory.card_fixedPoints_cat_iterate]
      have := MeasureTheory.three_le_lucasEven_succ t
      omega
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h Nat.card_of_isEmpty
  tendsto := MeasureTheory.tendsto_log_card_fixedPoints_cat

end
