/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# A homotopy obstruction for maps that collapse a section

**Category:** 1-Mathlib (CSD-free).

A self-map joined to the identity by a flow is homotopic to the identity, and
homotopy is a coarse invariant: it cannot tell apart maps that differ only by a
deformation. This module packages the cheapest useful consequence.

Suppose a space `A` retracts onto `X`, meaning there are continuous `g : X → A`
and `f : A → X` with `f ∘ g = id`. If a self-map `σ : A → A` **collapses that
section**, meaning `f ∘ σ ∘ g` is constant, then `σ` cannot be homotopic to the
identity unless `X` is contractible. Contrapositively, one non-contractible
retract is enough to obstruct.

* ★ `not_homotopic_id_of_section_collapsed` — the obstruction.
* `not_isFlowTimeOne_of_section_collapsed` — the form used downstream: no
  jointly continuous family joining the identity to `σ` exists.

## Why this is here

It is the engine of the relocation-generation obstruction
(`RecordLayer/RelocationObstruction.lean`). Exchanging two identical factors of a
product arena collapses the section that embeds a circle into the *first* of
them, because after the exchange that coordinate reads the *second* factor,
which the section held constant. The circle is not contractible
(`Mathlib/Topology/Homotopy/CircleFundamentalGroup.lean`), so the exchange is
not homotopic to the identity, so it is not the time-one map of any flow.

Stating it this way keeps the argument basepoint-free. The usual route runs
through `π₁` and has to conjugate by the path the basepoint traces under the
homotopy; nothing of the sort is needed here.

## References

`Mathlib/Topology/Homotopy/Contractible.lean`
(`contractible_iff_id_nullhomotopic`); `specs/future-work.md`.
-/

@[expose] public section

open ContinuousMap

/-- ★ **The obstruction.** If `X` is not contractible, `g` is a section of `f`,
and `σ` collapses that section to a constant, then `σ` is not homotopic to the
identity.

The proof is one composition: homotoping `σ` to the identity carries the
constant map `f ∘ σ ∘ g` to `f ∘ g = id`, exhibiting `id` as nullhomotopic. -/
theorem not_homotopic_id_of_section_collapsed
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (hX : ¬ ContractibleSpace X)
    (g : C(X, A)) (f : C(A, X)) (σ : C(A, A))
    (hfg : f.comp g = ContinuousMap.id X)
    (hconst : ∃ x, f.comp (σ.comp g) = ContinuousMap.const X x) :
    ¬ Homotopic σ (ContinuousMap.id A) := by
  intro h
  obtain ⟨x, hx⟩ := hconst
  apply hX
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨x, ?_⟩
  have hstep : Homotopic (f.comp (σ.comp g)) (f.comp ((ContinuousMap.id A).comp g)) :=
    .comp (.refl f) (.comp h (.refl g))
  rw [hx, ContinuousMap.id_comp, hfg] at hstep
  exact hstep.symm

/-- **No flow realises `σ` at time one.** A jointly continuous family joining the
identity to `σ` is a homotopy, so the obstruction applies. This is the form the
dynamical statements consume: being the time-one map of a flow is strictly
stronger than being homotopic to the identity, so obstructing the weaker
property obstructs the stronger one. -/
theorem not_isFlowTimeOne_of_section_collapsed
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (hX : ¬ ContractibleSpace X)
    (g : C(X, A)) (f : C(A, X)) (σ : C(A, A))
    (hfg : f.comp g = ContinuousMap.id X)
    (hconst : ∃ x, f.comp (σ.comp g) = ContinuousMap.const X x) :
    ¬ ∃ φ : C(unitInterval × A, A),
        (∀ a, φ (0, a) = σ a) ∧ (∀ a, φ (1, a) = a) := by
  rintro ⟨φ, h0, h1⟩
  refine not_homotopic_id_of_section_collapsed hX g f σ hfg hconst ⟨?_⟩
  exact { toContinuousMap := φ, map_zero_left := h0, map_one_left := h1 }
