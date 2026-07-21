import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpace
import CsdLean4.SigmaLayer.ConstraintSurface

/-!
# FND/ConstraintDynamics: deterministic, measure-preserving ontic dynamics

**Category:** 7-SigmaLayer (the Choice A ontological layer).

`ConstraintDynamics Sigma` is the canonical FND core (postulates P2, P3, P4): a finite Liouville
reference measure `muL` on the ontic state space, together with a deterministic real-parameter flow
that forms a one-parameter group and preserves `muL`. This is the group-law refinement of the existing
`LF1.OnticSetup` (single map, no group law) and `LF4.KahlerOnticSetup` (time flow, no group law); the
adapters into those live in `FND/IsolationPreparation.lean` and `FND/ChoiceASector.lean`.

## Anti-circularity

`ConstraintDynamics` carries NO Born weight, NO frequency claim, NO Fubini-Study equality, NO unitary
projected dynamics, NO Schrödinger equation. It is deterministic dynamics and a reference measure only.
The projective sector `pi` is a separate structure (`ChoiceASector`); all quantum content is a theorem
target or a named bridge assumption, never a field here.
-/

open MeasureTheory

namespace CSD.SigmaLayer

universe u

/-- **Deterministic, measure-preserving ontic dynamics (postulates P2, P3, P4).** A finite Liouville
reference measure `muL`, a deterministic flow forming a one-parameter group (`flow_zero`, `flow_add`),
each time-`t` map measurable and preserving `muL`. No quantum content. -/
structure ConstraintDynamics (Sigma : Type u) [MeasurableSpace Sigma] where
  /-- P2: the finite Liouville reference measure. -/
  muL : FiniteMeasure Sigma
  /-- P3: the deterministic ontic flow. -/
  flow : OnticTime → Sigma → Sigma
  /-- Each time-`t` map is measurable. -/
  measurable_flow : ∀ t, Measurable (flow t)
  /-- The flow at time `0` is the identity (one-parameter group identity). -/
  flow_zero : ∀ x, flow 0 x = x
  /-- The flow composes additively in time (one-parameter group law). -/
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)
  /-- P4: each time-`t` map preserves the Liouville measure (Liouville's theorem). -/
  flow_preserves : ∀ t,
    MeasurePreserving (flow t) (muL : Measure Sigma) (muL : Measure Sigma)

/-- **The trivial (identity-flow) dynamics** with a given finite reference measure. The isolated
evolution is the identity; useful when the physical content of a model is a de-isolation interaction
(`DeisolationModel`) rather than a nontrivial isolated flow. -/
def trivialDynamics {Sigma : Type u} [MeasurableSpace Sigma] (μ : FiniteMeasure Sigma) :
    ConstraintDynamics Sigma where
  muL := μ
  flow := fun _ => id
  measurable_flow := fun _ => measurable_id
  flow_zero := fun _ => rfl
  flow_add := fun _ _ _ => rfl
  flow_preserves := fun _ => MeasurePreserving.id _

namespace ConstraintDynamics

variable {Sigma : Type u} [MeasurableSpace Sigma] (D : ConstraintDynamics Sigma)

/-- Reversing the flow undoes it on the left: `flow (-t) (flow t x) = x`. Derived from the group law,
so reversibility is not a separate postulate. -/
theorem flow_neg_left (t : OnticTime) (x : Sigma) : D.flow (-t) (D.flow t x) = x := by
  rw [← D.flow_add, neg_add_cancel, D.flow_zero]

/-- Reversing the flow undoes it on the right: `flow t (flow (-t) x) = x`. -/
theorem flow_neg_right (t : OnticTime) (x : Sigma) : D.flow t (D.flow (-t) x) = x := by
  rw [← D.flow_add, add_neg_cancel, D.flow_zero]

/-- Each time-`t` flow map is a bijection, with inverse `flow (-t)` (derived from the real-flow group
laws, not postulated separately). -/
theorem flow_bijective (t : OnticTime) : Function.Bijective (D.flow t) :=
  ⟨Function.LeftInverse.injective (D.flow_neg_left t),
    fun x => ⟨D.flow (-t) x, D.flow_neg_right t x⟩⟩

/-- `flow (-t)` is the two-sided inverse of `flow t`. -/
theorem flow_neg_leftInverse (t : OnticTime) :
    Function.LeftInverse (D.flow (-t)) (D.flow t) := D.flow_neg_left t

/-- `flow (-t)` is a right inverse of `flow t`. -/
theorem flow_neg_rightInverse (t : OnticTime) :
    Function.RightInverse (D.flow (-t)) (D.flow t) := D.flow_neg_right t

end ConstraintDynamics

end CSD.SigmaLayer
