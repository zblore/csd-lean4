/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Data.Real.Basic

/-!
# SigmaLayer/ConstraintSurface: ontic time and the concrete constrained state space

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

This module fixes the ontic time parameter and offers an optional concrete representation of a
constrained ontic state space. The generic foundations stay polymorphic over an abstract `Sigma`; the
`ConstraintSurface` construction here is for concrete models only. We do not claim that every abstract
`Sigma` has been derived from explicit constraints.

See `SigmaLayer/Adapters.lean` for the postulate ledger (P1 to P9, B1 to B7, T1 to T15) governing the whole
SigmaLayer layer, and `SigmaLayer/ConstraintDynamics.lean` for the deterministic dynamics.
-/

namespace CSD.SigmaLayer

universe u

/-- Ontic time is a real parameter (the flow parameter of the deterministic ontic dynamics). -/
abbrev OnticTime := ℝ

/-- A constraint on a raw configuration type is a predicate selecting admissible configurations. -/
abbrev Constraint (Raw : Type u) := Raw → Prop

/-- **The constrained ontic state space (concrete models only).** The subtype of raw configurations
satisfying every constraint in the given family. This is the explicit representation of postulate P1
"there exists a measurable ontic constraint surface" for concrete models; the generic theory keeps
`Sigma` abstract. -/
def ConstraintSurface (Raw : Type u) (constraints : Set (Constraint Raw)) :=
  {x : Raw // ∀ C ∈ constraints, C x}

end CSD.SigmaLayer
