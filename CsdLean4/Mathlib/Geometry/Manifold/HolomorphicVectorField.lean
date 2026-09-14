/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianFlowVolume

/-!
# Holomorphic vector fields and holomorphic maps, for an atlas complex structure

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kähler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

`HamiltonianVectorField.lean` defines a Kähler manifold in the atlas sense (`IsKahler β J J₀`: `J`
is the model's `J₀` through every chart, so the atlas is holomorphic). The two notions that go
with it are stated here in the same sense:

* `DifferentialForm.IsHolomorphicVectorField J₀ X` — **a holomorphic vector field**: in every
  chart, the field read in the chart (`chartField`) is differentiable with `J₀`-linear derivative
  (its components in holomorphic charts are holomorphic functions; equivalently `L_X J = 0`);
* `DifferentialForm.IsHolomorphicMap J g` — **a holomorphic map**: differentiable, with
  `J`-linear manifold derivative at every point (`dg ∘ J = J ∘ dg`);
* ★ `IsAlmostKahler.metric_mfderiv_eq` — **a symplectic holomorphic map is an isometry of the
  compatible metric** `g = β (J ·, ·)`: it preserves `β` and commutes with `J`, so it preserves
  `g`. This is the "holomorphic + symplectic = Killing" half of the Kähler triangle.

## Honest scope

⚠️ **Atlas sense, no Lie derivative.** `IsHolomorphicVectorField` quantifies over every chart; that
the condition transports between holomorphic charts (the second derivative of a holomorphic
transition is `ℂ`-bilinear) is not proved here, and `L_X J` is not built. Consumers prove the
condition in every chart directly.

⚠️ **Self models only**, inherited from `ExteriorDerivative.lean`.

References: `Geometry/Manifold/HamiltonianVectorField.lean` (`IsKahler`, `IsAlmostKahler.metric`);
`Geometry/Manifold/IntegralCurve/FlowContinuity.lean` (`chartField`);
`Geometry/Manifold/Instances/ProjectiveSpaceSchrodingerHolomorphic.lean` (the `ℂℙⁿ` instance);
`specs/BACKLOG.md` (#30); `specs/future-work.md` (KG-3).
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology Set
open scoped Manifold Bundle Topology ContDiff

namespace DifferentialForm

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

/-- **A holomorphic vector field for the atlas complex structure `J₀`**: in every chart, the field
read in the chart is differentiable and its derivative commutes with `J₀`. On a Kähler manifold in
the atlas sense (`IsKahler β J J₀`) this is the usual notion: the components of `X` in
holomorphic charts are holomorphic functions, equivalently `L_X J = 0`. -/
def IsHolomorphicVectorField (J₀ : E →L[ℝ] E) (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) : Prop :=
  ∀ x₀ : M, ∀ w ∈ (chartAt E x₀).target,
    DifferentiableAt ℝ (chartField X x₀) w ∧
      ∀ v : E, fderiv ℝ (chartField X x₀) w (J₀ v) = J₀ (fderiv ℝ (chartField X x₀) w v)

/-- **A holomorphic map for an almost complex structure `J`**: differentiable, with `J`-linear
manifold derivative at every point. -/
def IsHolomorphicMap
    (J : ∀ x : M, TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x) (g : M → M) : Prop :=
  MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) g ∧
    ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x (J x v) = J (g x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v)

end Defs

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {β : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin 2) ℝ}
  {J : ∀ x : M, TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x}

namespace IsAlmostKahler

/-- ★ **A symplectic holomorphic map is an isometry of the compatible metric**: if `g` preserves
`β` and commutes with `J`, it preserves `g_β = β (J ·, ·)`. -/
theorem metric_mfderiv_eq (h : IsAlmostKahler β J) {g : M → M}
    (hg : IsHolomorphicMap J g)
    (hβ : ∀ (x : M) (u v : TangentSpace 𝓘(ℝ, E) x),
      β (g x) ![mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x u, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v] = β x ![u, v])
    (x : M) (u v : TangentSpace 𝓘(ℝ, E) x) :
    h.metric (g x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v)
      = h.metric x u v := by
  unfold IsAlmostKahler.metric
  rw [← hg.2 x u, hβ]

end IsAlmostKahler

end Metric

end DifferentialForm

end
