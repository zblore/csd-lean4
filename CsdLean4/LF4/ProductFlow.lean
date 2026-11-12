/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PointerStep
public import CsdLean4.LF4.CrossCoupledFlow

/-!
# Two symplectic arenas side by side: the flow of a sum of energies

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #372 — the generic half of the first brick of
milestone M6 of the author's programme "From `Σ` to physical spacetime": a clock on its own
carrier beside a messenger.

`LF4/PointerStep.lean` adds one pointer torus to a compact symplectic arena.
`LF4/CrossCoupledFlow.lean` joins two particular arenas with a coupling between them. This module
is the uncoupled case for any two compact symplectic arenas `S` and `S'`: on `S × S'` with the
form `π₁^* α + π₂^* β`, the energy `H(a) + K(b)` has the Hamiltonian vector field `(X_H, Y_K)`,
and its flow is the product of the two flows.

* `prodEnergy`, `prodEnergy_eq`, `contMDiff_prodEnergy`;
* ★ `isHamiltonianVectorField_prodEnergy` — `ι_{(X, Y)} (π₁^* α + π₂^* β) = d(H ∘ π₁ + K ∘ π₂)`;
* ★★★ `hamiltonianFlow_prodEnergy` — **the flow of `H(a) + K(b)` is `(Φ_H^t a, Φ_K^t b)`**;
* ★★ `measurePreserving_hamiltonianFlow_prodEnergy` — if the two flows preserve `μ` and `ν`, the
  joint flow preserves `μ ⊗ ν`.

## Exact scope

* **No coupling.** The energy is a sum of a function of the first factor and a function of the
  second. Neither factor's motion depends on the other's state.
* **Compact factors.** Existence and uniqueness of the flows use compactness (`integralFlow`).
  The factors are Hausdorff `C^∞` manifolds modelled on finite-dimensional spaces.
* **The measure is conditional** on each flow being measurable and preserving its own measure,
  for s-finite measures. The top-form measure of the product form is not identified with `μ ⊗ ν`.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-16,
UD-103); `LF4/PointerStep.lean` (`hamiltonianFlow_stepEnergy`, the one-torus step, whose proof
this follows); `LF4/CrossCoupledFlow.lean` (`IsHamiltonianVectorField.prodForm_fst`,
`IsHamiltonianVectorField.prodForm_snd`, `hamiltonianFlow_crossEnergy`: the coupled case);
`Mathlib/Geometry/Manifold/ProductForm.lean` (`prodForm`, `IsSymplectic.prodForm`);
`Mathlib/Geometry/Manifold/IntegralCurve/GlobalFlow.lean` (`integralFlow`,
`integralFlow_eq_of_isMIntegralCurve`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S S' : Type*} [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℝ, E) ∞ S]
  [TopologicalSpace S'] [ChartedSpace F S'] [IsManifold 𝓘(ℝ, F) ∞ S']

/-- **The energy of two arenas side by side**: `H(a) + K(b)`. -/
def prodEnergy (H : S → ℝ) (K : S' → ℝ) (p : S × S') : ℝ := H p.1 + K p.2

omit [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℝ, E) ∞ S] [TopologicalSpace S']
  [ChartedSpace F S'] [IsManifold 𝓘(ℝ, F) ∞ S'] in
theorem prodEnergy_eq (H : S → ℝ) (K : S' → ℝ) :
    prodEnergy H K = (fun p : S × S' => H p.1) + fun p : S × S' => K p.2 :=
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ S] [IsManifold 𝓘(ℝ, F) ∞ S'] in
/-- The energy of two arenas side by side is `C^∞`. -/
theorem contMDiff_prodEnergy {H : S → ℝ} {K : S' → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hK : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ K) :
    ContMDiff 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ) ∞ (prodEnergy H K) := by
  rw [prodEnergy_eq]
  exact (hH.comp (Prod.contMDiff_fst_self (E := E) (F := F) (M := S) (N := S'))).add
    (hK.comp (Prod.contMDiff_snd_self (E := E) (F := F) (M := S) (N := S')))

variable {α : DifferentialForm 𝓘(ℝ, E) S ∞ (Fin 2) ℝ}
  {β : DifferentialForm 𝓘(ℝ, F) S' ∞ (Fin 2) ℝ}

/-- ★ **The field of a sum of energies on a product** is the pair of the two fields:
`ι_{(X, Y)} (π₁^* α + π₂^* β) = d(H ∘ π₁ + K ∘ π₂)`. -/
theorem isHamiltonianVectorField_prodEnergy {X : ∀ s : S, TangentSpace 𝓘(ℝ, E) s}
    {Y : ∀ s : S', TangentSpace 𝓘(ℝ, F) s} {H : S → ℝ} {K : S' → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hK : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ K)
    (hX : IsHamiltonianVectorField (fun s => α s) X H)
    (hY : IsHamiltonianVectorField (fun s => β s) Y K) :
    IsHamiltonianVectorField (fun p => prodForm α β p)
      (fun p : S × S' => (((X p.1 : E), (Y p.2 : F)) : TangentSpace 𝓘(ℝ, E × F) p))
      (prodEnergy H K) := by
  have hHd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H := fun x => (hH x).mdifferentiableAt (by simp)
  have hKd : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, ℝ) K := fun x => (hK x).mdifferentiableAt (by simp)
  have hL := IsHamiltonianVectorField.prodForm_fst β hHd hX
  have hO := IsHamiltonianVectorField.prodForm_snd α hKd hY
  have hdiffL : ∀ p : S × S', MDifferentiableAt 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ)
      (fun p : S × S' => H p.1) p := fun p =>
    ((hH.comp (Prod.contMDiff_fst_self (E := E) (F := F) (M := S) (N := S')))
      p).mdifferentiableAt (by simp)
  have hdiffO : ∀ p : S × S', MDifferentiableAt 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ)
      (fun p : S × S' => K p.2) p := fun p =>
    ((hK.comp (Prod.contMDiff_snd_self (E := E) (F := F) (M := S) (N := S')))
      p).mdifferentiableAt (by simp)
  have hfield : (fun p : S × S' =>
        (((X p.1 : E), (Y p.2 : F)) : TangentSpace 𝓘(ℝ, E × F) p))
      = fun p : S × S' =>
        (((X p.1 : E), (0 : F)) : TangentSpace 𝓘(ℝ, E × F) p)
          + (((0 : E), (Y p.2 : F)) : TangentSpace 𝓘(ℝ, E × F) p) := by
    funext p
    show (((X p.1 : E), (Y p.2 : F)) : E × F)
      = (((X p.1 : E), (0 : F)) : E × F) + (((0 : E), (Y p.2 : F)) : E × F)
    exact Prod.ext (add_zero (X p.1 : E)).symm (zero_add (Y p.2 : F)).symm
  rw [hfield, prodEnergy_eq]
  exact hL.add hO hdiffL hdiffO

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompactSpace S] [T2Space S]
  [CompactSpace S'] [T2Space S']

/-- ★★★ **Two arenas side by side move side by side.** On compact symplectic arenas `S` and
`S'`, the Hamiltonian flow of `H(a) + K(b)` for the form `π₁^* α + π₂^* β` moves `a` by the flow
of `H` and `b` by the flow of `K`. -/
theorem hamiltonianFlow_prodEnergy (hα : α.IsSymplectic) (hβ : β.IsSymplectic) {H : S → ℝ}
    {K : S' → ℝ} (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hK : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ K)
    (t : ℝ) (a : S) (b : S') :
    (hα.prodForm hβ).hamiltonianFlow (contMDiff_prodEnergy hH hK) t (a, b)
      = (hα.hamiltonianFlow hH t a, hβ.hamiltonianFlow hK t b) := by
  have hXH := hα.hamiltonianVectorField_isHamiltonianVectorField H
  have hYK := hβ.hamiltonianVectorField_isHamiltonianVectorField K
  have hΦ : IsMIntegralCurve (fun u : ℝ => hα.hamiltonianFlow hH u a)
      (hα.hamiltonianVectorField H) := isMIntegralCurve_integralFlow _ a
  have hΨ : IsMIntegralCurve (fun u : ℝ => hβ.hamiltonianFlow hK u b)
      (hβ.hamiltonianVectorField K) := isMIntegralCurve_integralFlow _ b
  have hγ : IsMIntegralCurve
      (fun r : ℝ => ((hα.hamiltonianFlow hH r a, hβ.hamiltonianFlow hK r b) : S × S'))
      ((hα.prodForm hβ).hamiltonianVectorField (prodEnergy H K)) := by
    rw [← (isHamiltonianVectorField_prodEnergy (α := α) (β := β) hH hK hXH
      hYK).eq_isSymplectic_hamiltonianVectorField (hα.prodForm hβ)]
    intro r
    refine ((hΦ r).prodMk_self (hΨ r)).congr_deriv ?_
    exact ContinuousLinearMap.ext fun c => Prod.ext rfl rfl
  have h0 : ((hα.hamiltonianFlow hH 0 a, hβ.hamiltonianFlow hK 0 b) : S × S') = (a, b) :=
    Prod.ext (integralFlow_zero (hα.contMDiff_hamiltonianVectorField_tangent hH) a)
      (integralFlow_zero (hβ.contMDiff_hamiltonianVectorField_tangent hK) b)
  have h := integralFlow_eq_of_isMIntegralCurve
    ((hα.prodForm hβ).contMDiff_hamiltonianVectorField_tangent (contMDiff_prodEnergy hH hK))
    hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t]

/-- ★★ **If each flow preserves its measure, the joint flow preserves the product measure.** -/
theorem measurePreserving_hamiltonianFlow_prodEnergy [MeasurableSpace S] [MeasurableSpace S']
    (hα : α.IsSymplectic) (hβ : β.IsSymplectic) {H : S → ℝ} {K : S' → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hK : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ K)
    (μ : Measure S) (ν : Measure S') [SFinite μ] [SFinite ν] (t : ℝ)
    (hμ : MeasurePreserving (hα.hamiltonianFlow hH t) μ μ)
    (hν : MeasurePreserving (hβ.hamiltonianFlow hK t) ν ν) :
    MeasurePreserving ((hα.prodForm hβ).hamiltonianFlow (contMDiff_prodEnergy hH hK) t)
      (μ.prod ν) (μ.prod ν) := by
  have e : (hα.prodForm hβ).hamiltonianFlow (contMDiff_prodEnergy hH hK) t
      = Prod.map (hα.hamiltonianFlow hH t) (hβ.hamiltonianFlow hK t) :=
    funext fun p => hamiltonianFlow_prodEnergy hα hβ hH hK t p.1 p.2
  rw [e]
  exact hμ.prod hν

end Prod

end LF4
end CSD

end
