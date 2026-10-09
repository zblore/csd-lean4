/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.LinearPMapConj
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# A bounded symmetric perturbation keeps self-adjointness and the domain

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #64(ii), the second of the three pieces that row records itself as waiting on.

★★★ `IsSelfAdjoint.addCLM` — **`T + V` is self-adjoint on `dom T` when `T` is self-adjoint and `V`
is a bounded symmetric operator**: the bounded case of Kato–Rellich, which is what gives `H₀ + V`
for a bounded real potential. Behind it:

* `LinearPMap.addCLM` — the sum, with domain **exactly** `dom T` (Mathlib's `+` on `LinearPMap`
  intersects domains, so `T + V.toPMap ⊤` has domain `dom T ⊓ ⊤`, which is equal to `dom T` but not
  syntactically it; a perturbation statement wants the domain unchanged on the nose);
* ★★★ `LinearPMap.adjoint_addCLM` — **the adjoint is perturbed the same way**,
  `(T + V)† = T† + V`, which is the general statement and does not need `T` self-adjoint;
* ★★ `LinearPMap.addCLM_adjointDomain` — **the adjoint's domain does not move at all**, and this
  needs only *boundedness* of `V`, not symmetry: `x ↦ ⟪y, V x⟫` is continuous for every `y`, so it
  cannot affect whether `x ↦ ⟪y, T x⟫` is.

## Why the domain is the whole content

Symmetry of `T + V` is three lines and says nothing: the issue with an unbounded operator is always
*maximality* — that the adjoint has no larger domain. `addCLM_adjointDomain` is where that is
settled, and it is settled by continuity of a bounded functional rather than by any estimate. This
is exactly why the bounded case is elementary and the Kato–Rellich theorem proper (a perturbation
that is merely relatively bounded, with relative bound `< 1`) is not: there the domain argument needs
the resolvent and a Neumann series, and nothing here covers it.

## Honest scope

⚠️ **Bounded, not relatively bounded.** `V` is a `ContinuousLinearMap`. The Kato–Rellich theorem for
`T`-bounded perturbations with relative bound `< 1` — the version that covers Coulomb potentials — is
a different theorem and is **not** proved here.

⚠️ **No semiboundedness, no form sums.** Nothing about `KLMN`/quadratic forms, which is how
potentials that are not operator-bounded are handled.

⚠️ **Symmetric is taken as the hypothesis**, in the form `LinearMap.IsSymmetric`, rather than
`IsSelfAdjoint` for a `ContinuousLinearMap`: they agree for a bounded operator on a complete space,
and the symmetric form is what a consumer actually discharges.

References: [`LinearPMapConj.lean`](LinearPMapConj.lean) (#64(i), the unitary conjugation),
[`MultiplicationOperator.lean`](MultiplicationOperator.lean) (`mulCLM`, the bounded multiplication
operators this is for), `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean` (`adjoint`),
`Mathlib/Analysis/InnerProductSpace/Symmetric.lean` (`LinearMap.IsSymmetric`);
`specs/BACKLOG.md` #64.
-/

@[expose] public section

open scoped ComplexConjugate LinearPMap

noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The perturbed operator -/

/-- **`T + V`** for a bounded `V`, with domain exactly `dom T`. -/
def addCLM (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E where
  domain := T.domain
  toFun := T.toFun + (V : E →ₗ[𝕜] E).comp T.domain.subtype

@[simp]
theorem addCLM_domain (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : (T.addCLM V).domain = T.domain := rfl

theorem addCLM_apply (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) (x : T.domain) :
    T.addCLM V x = T x + V (x : E) := rfl

/-- The perturbation does not move the domain, so density is inherited. -/
theorem dense_addCLM_domain (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E)
    (hT : Dense (T.domain : Set E)) : Dense ((T.addCLM V).domain : Set E) := hT

/-! ### The adjoint's domain does not move

This is the content, and it needs only that `V` is bounded. -/

/-- The functional a bounded perturbation adds is continuous outright. -/
theorem continuous_inner_apply_clm (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) (y : E) :
    Continuous fun x : T.domain => (inner 𝕜 y (V (x : E)) : 𝕜) :=
  (innerSL 𝕜 y).continuous.comp (V.continuous.comp continuous_subtype_val)

/-- ★★ **The adjoint's domain is unchanged by a bounded perturbation.** -/
theorem addCLM_adjointDomain (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    (T.addCLM V).adjointDomain = T.adjointDomain := by
  refine Submodule.ext fun y => ?_
  have hsplit : ∀ x : T.domain,
      (inner 𝕜 y (T.addCLM V x) : 𝕜) = inner 𝕜 y (T x) + inner 𝕜 y (V (x : E)) := by
    intro x
    rw [addCLM_apply, inner_add_right]
  constructor
  · intro hy
    have hcont : Continuous fun x : T.domain => (inner 𝕜 y (T.addCLM V x) : 𝕜) := hy
    have hfun : (fun x : T.domain => (inner 𝕜 y (T x) : 𝕜))
        = (fun x : T.domain => (inner 𝕜 y (T.addCLM V x) : 𝕜))
          - fun x : T.domain => (inner 𝕜 y (V (x : E)) : 𝕜) := by
      funext x
      simp only [Pi.sub_apply, hsplit x]
      ring
    show Continuous fun x : T.domain => (inner 𝕜 y (T x) : 𝕜)
    rw [hfun]
    exact hcont.sub (continuous_inner_apply_clm T V y)
  · intro hy
    have hcont : Continuous fun x : T.domain => (inner 𝕜 y (T x) : 𝕜) := hy
    show Continuous fun x : T.domain => (inner 𝕜 y (T.addCLM V x) : 𝕜)
    simp only [hsplit]
    exact hcont.add (continuous_inner_apply_clm T V y)

variable [CompleteSpace E]

/-- ★★★ **The adjoint is perturbed the same way**: `(T + V)† = T† + V`, for any bounded symmetric
`V` and any densely defined `T`. Self-adjointness of `T` is not needed. -/
theorem adjoint_addCLM (T : E →ₗ.[𝕜] E) (V : E →L[𝕜] E)
    (hV : LinearMap.IsSymmetric (V : E →ₗ[𝕜] E)) (hT : Dense (T.domain : Set E)) :
    (T.addCLM V)† = (T†).addCLM V := by
  refine LinearPMap.ext ?_ ?_
  · show (T.addCLM V).adjointDomain = T.adjointDomain
    exact addCLM_adjointDomain T V
  · intro w hf hg
    have hg' : w ∈ (T†).domain := hg
    show (T.addCLM V)† ⟨w, hf⟩ = T† ⟨w, hg'⟩ + V w
    refine LinearPMap.adjoint_apply_eq (T := T.addCLM V) hT ⟨w, hf⟩ ?_
    intro x
    rw [inner_add_left]
    have h1 : (inner 𝕜 (T† ⟨w, hg'⟩) (x : E) : 𝕜)
        = inner 𝕜 w (T ⟨(x : E), x.2⟩) :=
      LinearPMap.adjoint_isFormalAdjoint hT ⟨w, hg'⟩ ⟨(x : E), x.2⟩
    have h2 : (inner 𝕜 (V w) (x : E) : 𝕜) = inner 𝕜 w (V (x : E)) := hV.apply_clm w (x : E)
    rw [h1, h2, ← inner_add_right]
    rfl

/-- ★★★ **A bounded symmetric perturbation preserves self-adjointness**, on the same domain: the
bounded case of Kato–Rellich, and what gives `H₀ + V` for a bounded real potential. -/
theorem _root_.IsSelfAdjoint.addCLM {T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T) (V : E →L[𝕜] E)
    (hV : LinearMap.IsSymmetric (V : E →ₗ[𝕜] E)) : IsSelfAdjoint (T.addCLM V) := by
  rw [LinearPMap.isSelfAdjoint_def,
    LinearPMap.adjoint_addCLM T V hV hT.dense_domain]
  rw [LinearPMap.isSelfAdjoint_def] at hT
  rw [hT]

end LinearPMap

end

end
