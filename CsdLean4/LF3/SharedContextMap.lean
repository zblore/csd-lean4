/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.ContextMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# LF3/SharedContextMap: outcome maps on ONE shared state space

**Category:** 3-Local (the shared-domain context interface).

`ContextIndexedOutcomeMaps` gives each context its **own** state space
`Domain ctx`. That is the wrong shape for the C1 Bell analysis, which fixes a
single ontic state space `SigmaSpace` and asks what a family of context-indexed outcome
maps on it can do. This module supplies that shape.

* `SharedContextOutcomeMaps SigmaSpace` — one common `SigmaSpace`, an outcome map per context.
  The state type does **not** depend on the context.
* `MeasurableSharedContextOutcomeMaps` — each `F C : SigmaSpace → Sign × Sign` is
  measurable. This is the **only** measurability assumed anywhere in the C1
  chain: the four setting-local responses of a `GlobalCHSHAssignment` are
  *derived* measurable from it and compatibility, never assumed. See
  `LF6/C1BellConsistency.lean`.

`Sign` carries the discrete (`⊤`) σ-algebra, the canonical choice for a finite
type and the one that makes "measurable outcome map" mean what it should.

## References

`LF3/ContextMap.lean` (`MeasurementContext`, `GlobalCHSHAssignment`);
`LF6/C1BellConsistency.lean` (the no-go this feeds);
`specs/c1-correction-plan.md` §3 D1.
-/

@[expose] public section

namespace CSD.LF3

/-- The discrete σ-algebra on `Sign`: every subset is measurable. -/
instance : MeasurableSpace Sign := ⊤

/-- Singletons are measurable in the discrete σ-algebra — the companion instance the
level-set arguments of `LF6/C1BellConsistency.lean` consume. -/
instance : MeasurableSingletonClass Sign := ⟨fun _ => trivial⟩

/-- Every function out of `Sign` is measurable, `Sign` being discrete. -/
lemma measurable_of_sign {α : Type*} [MeasurableSpace α] (f : Sign → α) :
    Measurable f := fun _ _ => trivial

/-- **Outcome maps on one shared state space.** Every context reads the *same*
`SigmaSpace`; only the outcome map varies. This is the C1 shape: a fixed ontic state
space, with the context selecting how it is read. -/
structure SharedContextOutcomeMaps (SigmaSpace : Type*) where
  /-- The context-indexed joint outcome map on the shared state space. -/
  F : MeasurementContext → SigmaSpace → Sign × Sign

/-- Each context's outcome map is measurable. -/
def MeasurableSharedContextOutcomeMaps {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]
    (S : SharedContextOutcomeMaps SigmaSpace) : Prop :=
  ∀ C, Measurable (S.F C)

namespace SharedContextOutcomeMaps

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] (S : SharedContextOutcomeMaps SigmaSpace)

/-- The A-wing component of the joint outcome. -/
def wingA (C : MeasurementContext) (l : SigmaSpace) : Sign := (S.F C l).1

/-- The B-wing component of the joint outcome. -/
def wingB (C : MeasurementContext) (l : SigmaSpace) : Sign := (S.F C l).2

/-- The A-wing component is measurable, **derived** from measurability of the
joint map. -/
lemma measurable_wingA (hS : MeasurableSharedContextOutcomeMaps S)
    (C : MeasurementContext) : Measurable (S.wingA C) :=
  measurable_fst.comp (hS C)

/-- The B-wing component is measurable, **derived**. -/
lemma measurable_wingB (hS : MeasurableSharedContextOutcomeMaps S)
    (C : MeasurementContext) : Measurable (S.wingB C) :=
  measurable_snd.comp (hS C)

/-- The real-valued A-wing response, measurable. -/
lemma measurable_wingA_val (hS : MeasurableSharedContextOutcomeMaps S)
    (C : MeasurementContext) : Measurable (fun l => ((S.wingA C l).val : ℝ)) := by
  exact (measurable_of_sign (fun s : Sign => (s.val : ℝ))).comp (S.measurable_wingA hS C)

/-- The real-valued B-wing response, measurable. -/
lemma measurable_wingB_val (hS : MeasurableSharedContextOutcomeMaps S)
    (C : MeasurementContext) : Measurable (fun l => ((S.wingB C l).val : ℝ)) := by
  exact (measurable_of_sign (fun s : Sign => (s.val : ℝ))).comp (S.measurable_wingB hS C)

end SharedContextOutcomeMaps

/-- Sign values are `±1`. -/
lemma sign_val_eq_one_or (s : Sign) : (s.val : ℝ) = 1 ∨ (s.val : ℝ) = -1 := by
  cases s <;> simp [Sign.val]

end CSD.LF3
