/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.EchoVolume

/-!
# Adding a pointer torus to a symplectic arena

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #368 — the author's programme "From `Σ` to
physical spacetime", the arena M6 needs; Remainder (a) of #367. The author's choice of route: a
tower of pointer tori, in place of a third arena built by hand.

`ArenaCoupledFlow.lean` generated the flow of a ray coupled to one torus, and
`EchoCoupledFlow.lean` did it again for two. Both are one construction: take a symplectic arena
`S`, an energy `H` on it and one more function `G`, and couple a torus to `G`. This module does
that construction once, for any compact symplectic manifold `S`, so that each further pointer is
an application of it.

**The step.** `stepForm β` is the form `β ⊕ dψ₁ ∧ dψ₂` on `S × T²`, symplectic when `β` is
(`stepForm_isSymplectic`). `stepEnergy H G` is the energy

  `(s, ψ) ↦ H(s) + G(s) g(ψ₂)`.

If `X_H` and `X_G` are the Hamiltonian vector fields of `H` and `G` on `S`, the field

  `(X_H + g(ψ₂) X_G, (G g'(ψ₂), 0))`

is the Hamiltonian vector field of `stepEnergy H G` on `S × T²`
(`isHamiltonianVectorField_step`, from `isHamiltonianVectorField_stepLift` and
`isHamiltonianVectorField_stepTerm`).

**The flow is a skew product over the conserved angle.** For a compact `S`:

  `Φ_t(s, ψ) = (φ_t^{H + g(ψ₂) G}(s), (ψ₁ + g'(ψ₂) ∫₀ᵗ G(φ_u^{H + g(ψ₂) G}(s)) du, ψ₂))`,

where `φ^{H + c G}` is the Hamiltonian flow on `S` of the energy `H + c G`
(`hamiltonianFlow_stepEnergy`). With the new torus's conserved angle held, the base moves by the
base's own flow with `c G` added to its energy, the new pointer's moving angle advances by
`g'(ψ₂)` times the accumulated `G` along that orbit, and `ψ₂` is fixed. The proof is the one of
the two earlier modules: the right-hand side is an integral curve of the field above, and
integral curves on a compact manifold are unique. The slice is
`hamiltonianFlow_stepEnergy_fst`. If every base flow of `H + c G` preserves a measure `μ`, the
flow with one more torus preserves `μ ⊗ vol_{T²}` (`map_hamiltonianFlow_stepEnergy`).

**The instances.** `echoForm = stepForm arenaForm` (`echoForm_eq_stepForm`) and
`twoCoupledEnergy` is a `stepEnergy` (`twoCoupledEnergy_eq_stepEnergy`), so the two-torus arena
is the step applied to the one-torus arena. The three-torus arena is the step applied to the
two-torus arena (`LF4/TriCoupledFlow.lean`).

## Exact scope

* **One step, for any base.** The theorem adds one torus. A family of `n` tori is `n`
  applications, each with its own statement. No arena indexed by `n` is defined.
* **Compact base.** Existence and uniqueness of the flow use compactness
  (`integralFlow`). The base must be a `C^∞` manifold modelled on a finite-dimensional space.
* **The coupling's form is assumed**: a function of the base times a function of the new torus's
  second angle. The moving angle `ψ₁` does not enter the energy, so `ψ₂` is conserved and the
  pointer does not act back on its own rate.
* **The measure is conditional.** `map_hamiltonianFlow_stepEnergy` shows the flow preserves
  `μ ⊗ vol_{T²}` when every base flow of `H + c G` preserves `μ`. That hypothesis is supplied at
  each level. The top-form measure of `stepForm β` is not identified with the product measure.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-13,
UA-15, UD-95); `LF4/ArenaCoupledFlow.lean` (`torusPotential`, `hamiltonianFlow_coupledEnergy`:
the one-torus case); `LF4/EchoCoupledFlow.lean` (`hamiltonianFlow_twoCoupledEnergy`: the
two-torus case, whose proof this generalises);
`Mathlib/Geometry/Manifold/ProductForm.lean` (`prodForm`, `IsSymplectic.prodForm`,
`prodSum_pair`); `Mathlib/Geometry/Manifold/IntegralCurve/GlobalFlow.lean` (`integralFlow`,
`integralFlow_eq_of_isMIntegralCurve`);
`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean` (`IsHamiltonianVectorField`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℝ, E) ∞ S]
  {g : ℝ → ℝ}

/-! ### The form and the energy -/

/-- **The form of the arena with one more torus**: `β ⊕ dψ₁ ∧ dψ₂` on `S × T²`. -/
noncomputable def stepForm (β : DifferentialForm 𝓘(ℝ, E) S ∞ (Fin 2) ℝ) :
    DifferentialForm 𝓘(ℝ, E × (ℝ × ℝ)) (S × KTorus) ∞ (Fin 2) ℝ :=
  prodForm β (AddCircle.torusAreaForm (T := 1) (T' := 1))

/-- ★ **The arena with one more torus is symplectic.** -/
theorem stepForm_isSymplectic {β : DifferentialForm 𝓘(ℝ, E) S ∞ (Fin 2) ℝ}
    (hβ : β.IsSymplectic) : (stepForm β).IsSymplectic :=
  hβ.prodForm AddCircle.torusAreaForm_isSymplectic

/-- **The energy with one more torus coupled to `G`**: `H(s) + G(s) g(ψ₂)`. -/
noncomputable def stepEnergy (H G : S → ℝ) (hg : Function.Periodic g 1) (p : S × KTorus) : ℝ :=
  H p.1 + G p.1 * torusPotential hg p.2

omit [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℝ, E) ∞ S] in
theorem stepEnergy_eq (H G : S → ℝ) (hg : Function.Periodic g 1) :
    stepEnergy H G hg
      = (fun p : S × KTorus => H p.1) + fun p : S × KTorus => G p.1 * torusPotential hg p.2 :=
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ S] in
/-- The coupled term `G(s) g(ψ₂)` is `C^∞`. -/
theorem contMDiff_stepTerm {G : S → ℝ} (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : S × KTorus => G p.1 * torusPotential hg p.2) :=
  (hG.comp (Prod.contMDiff_fst_self (E := E) (F := ℝ × ℝ) (M := S) (N := KTorus))).mul
    ((contMDiff_torusPotential hg hcg).comp
      (Prod.contMDiff_snd_self (E := E) (F := ℝ × ℝ) (M := S) (N := KTorus)))

omit [IsManifold 𝓘(ℝ, E) ∞ S] in
/-- The step energy is `C^∞`. -/
theorem contMDiff_stepEnergy {H G : S → ℝ} (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G) (hg : Function.Periodic g 1)
    (hcg : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞ (stepEnergy H G hg) := by
  rw [stepEnergy_eq]
  exact (hH.comp (Prod.contMDiff_fst_self (E := E) (F := ℝ × ℝ) (M := S) (N := KTorus))).add
    (contMDiff_stepTerm hG hg hcg)

omit [IsManifold 𝓘(ℝ, E) ∞ S] in
/-- The base energy with `c G` added is `C^∞`. -/
theorem contMDiff_add_const_smul {H G : S → ℝ} (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G) (c : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (H + c • G) := by
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun s : S => H s + c * G s) :=
    hH.add (contMDiff_const.mul hG)
  exact h

/-! ### The Hamiltonian vector field -/

variable {β : DifferentialForm 𝓘(ℝ, E) S ∞ (Fin 2) ℝ}

/-- ★ **A Hamiltonian vector field on the base lifts to the arena with one more torus**: if
`ι_X β = dH` then `ι_{(X, 0)} (stepForm β) = d(H ∘ π₁)`. -/
theorem isHamiltonianVectorField_stepLift {X : ∀ s : S, TangentSpace 𝓘(ℝ, E) s} {H : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H)
    (hX : IsHamiltonianVectorField (fun s => β s) X H) :
    IsHamiltonianVectorField (fun p => stepForm β p)
      (fun p : S × KTorus => ((X p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p))
      (fun p => H p.1) := by
  intro p v
  have hv := hX p.1 (v : E × (ℝ × ℝ)).1
  have hz : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : E × (ℝ × ℝ)).2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h1 : (stepForm β p) ![((X p.1 : E), (0 : ℝ × ℝ)), v]
      = toFlat (β p.1) ![(X p.1 : E), (v : E × (ℝ × ℝ)).1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : E × (ℝ × ℝ)).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (β p.1)) TorusForm.areaForm
      ((X p.1 : E), (0 : ℝ × ℝ)) (v : E × (ℝ × ℝ))
  have hd : HasMFDerivAt 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ) (fun p : S × KTorus => H p.1) p
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H p.1).comp (ContinuousLinearMap.fst ℝ E (ℝ × ℝ))) :=
    ((hH p.1).mdifferentiableAt (by simp)).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := E) (F := ℝ × ℝ) p)
  have h2 : mfderiv 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ) (fun p : S × KTorus => H p.1) p v
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H p.1 (v : E × (ℝ × ℝ)).1 := by
    rw [hd.mfderiv]
    rfl
  refine h1.trans ?_
  rw [hz, add_zero]
  exact hv.trans h2.symm

/-- ★ **The coupled term**: `ι_X (stepForm β) = d(G g(ψ₂))` for
`X = (g(ψ₂) X_G, (G g'(ψ₂), 0))`. -/
theorem isHamiltonianVectorField_stepTerm {XG : ∀ s : S, TangentSpace 𝓘(ℝ, E) s} {G : S → ℝ}
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hXG : IsHamiltonianVectorField (fun s => β s) XG G) (hg : Function.Periodic g 1)
    (hd : Differentiable ℝ g) :
    IsHamiltonianVectorField (fun p => stepForm β p)
      (fun p : S × KTorus =>
        (((torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p))
      (fun p => G p.1 * torusPotential hg p.2) := by
  intro p v
  have ha := ((hG p.1).mdifferentiableAt (by simp)).hasMFDerivAt.comp p
    (Prod.hasMFDerivAt_fst_self (E := E) (F := ℝ × ℝ) p)
  have hb := (hasMFDerivAt_torusPotential hg hd p.2).comp p
    (Prod.hasMFDerivAt_snd_self (E := E) (F := ℝ × ℝ) p)
  have hprod : HasMFDerivAt 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ)
      (fun q : S × KTorus => G q.1 * torusPotential hg q.2) p _ := ha.mul hb
  beta_reduce
  rw [hprod.mfderiv]
  have hX := hXG p.1 (v : E × (ℝ × ℝ)).1
  have h1 : (stepForm β p)
      ![(((torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p), v]
      = toFlat (β p.1) ![(torusPotential hg p.2 • XG p.1 : E), (v : E × (ℝ × ℝ)).1]
        + TorusForm.areaForm
          ![((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ), (v : E × (ℝ × ℝ)).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (β p.1)) TorusForm.areaForm _ _
  rw [h1]
  have h3 : toFlat (β p.1) ![(torusPotential hg p.2 • XG p.1 : E), (v : E × (ℝ × ℝ)).1]
      = torusPotential hg p.2 * toFlat (β p.1) ![(XG p.1 : E), (v : E × (ℝ × ℝ)).1] :=
    apply_smul_left (fun s : S => β s) p.1 _ _ _
  have h4 : toFlat (β p.1) ![(XG p.1 : E), (v : E × (ℝ × ℝ)).1]
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G p.1 (v : E × (ℝ × ℝ)).1 := hX
  rw [h3, h4, TorusForm.areaForm_apply]
  set D : ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G p.1 (v : E × (ℝ × ℝ)).1 with hD
  show torusPotential hg p.2 * D
      + (G p.1 * hg.deriv_periodic.lift p.2.2 * (v : E × (ℝ × ℝ)).2.2
        - 0 * (v : E × (ℝ × ℝ)).2.1)
    = G p.1 * ((v : E × (ℝ × ℝ)).2.2 * hg.deriv_periodic.lift p.2.2)
      + torusPotential hg p.2 * D
  ring

/-- ★★ **`ι_X (stepForm β) = d(stepEnergy H G)`** for
`X = (X_H + g(ψ₂) X_G, (G g'(ψ₂), 0))`. -/
theorem isHamiltonianVectorField_step {XH XG : ∀ s : S, TangentSpace 𝓘(ℝ, E) s} {H G : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hXH : IsHamiltonianVectorField (fun s => β s) XH H)
    (hXG : IsHamiltonianVectorField (fun s => β s) XG G) (hg : Function.Periodic g 1)
    (hcg : ContDiff ℝ ∞ g) :
    IsHamiltonianVectorField (fun p => stepForm β p)
      (fun p : S × KTorus =>
        (((XH p.1 + torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p))
      (stepEnergy H G hg) := by
  have hL := isHamiltonianVectorField_stepLift (β := β) hH hXH
  have hO := isHamiltonianVectorField_stepTerm (β := β) hG hXG hg (hcg.differentiable (by simp))
  have hdiffL : ∀ p : S × KTorus, MDifferentiableAt 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ)
      (fun p : S × KTorus => H p.1) p := fun p =>
    ((hH.comp (Prod.contMDiff_fst_self (E := E) (F := ℝ × ℝ) (M := S) (N := KTorus)))
      p).mdifferentiableAt (by simp)
  have hdiffO : ∀ p : S × KTorus, MDifferentiableAt 𝓘(ℝ, E × (ℝ × ℝ)) 𝓘(ℝ, ℝ)
      (fun p : S × KTorus => G p.1 * torusPotential hg p.2) p := fun p =>
    (contMDiff_stepTerm hG hg hcg p).mdifferentiableAt (by simp)
  have hfield : (fun p : S × KTorus =>
        (((XH p.1 + torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p))
      = fun p : S × KTorus =>
        ((XH p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p)
          + (((torusPotential hg p.2 • XG p.1 : E),
            ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
            TangentSpace 𝓘(ℝ, E × (ℝ × ℝ)) p) := by
    funext p
    show (((XH p.1 + torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) : E × (ℝ × ℝ))
      = ((XH p.1 : E), (0 : ℝ × ℝ))
        + ((torusPotential hg p.2 • XG p.1 : E),
          ((G p.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ))
    simp only [Prod.mk_add_mk, zero_add]
    rfl
  rw [hfield, stepEnergy_eq]
  exact hL.add hO hdiffL hdiffO

/-! ### The flow is a skew product over the conserved angle -/

variable [FiniteDimensional ℝ E] [CompactSpace S] [T2Space S]

/-- ★★★ **The Hamiltonian flow with one more torus, in terms of the base's flows.** On a compact
symplectic arena `S`, the flow of `H(s) + G(s) g(ψ₂)` for `stepForm β` moves the base by the
base's Hamiltonian flow of `H + g(ψ₂) G`, advances `ψ₁` by `g'(ψ₂)` times the accumulated `G`
along that orbit, and fixes `ψ₂`. -/
theorem hamiltonianFlow_stepEnergy (hβ : β.IsSymplectic) {H G : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (s : S) (ψ : KTorus) :
    (stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t (s, ψ)
      = (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG (hg.lift ψ.2)) t s,
          (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..t,
              G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG (hg.lift ψ.2)) u s) : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)) := by
  obtain ⟨b₀, hb₀⟩ := QuotientAddGroup.mk_surjective ψ.1
  set c : ℝ := hg.lift ψ.2 with hc
  have hHd : ∀ x : S, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H x := fun x =>
    (hH x).mdifferentiableAt (by simp)
  have hGd : ∀ x : S, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G x := fun x =>
    (hG x).mdifferentiableAt (by simp)
  have hcGd : ∀ x : S, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (c • G) x := fun x =>
    have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun s : S => c * G s) := contMDiff_const.mul hG
    (h x).mdifferentiableAt (by simp)
  have hXH := hβ.hamiltonianVectorField_isHamiltonianVectorField H
  have hXG := hβ.hamiltonianVectorField_isHamiltonianVectorField G
  -- the base field of `H + c G`
  have hbase : (fun x : S => hβ.hamiltonianVectorField H x + c • hβ.hamiltonianVectorField G x)
      = hβ.hamiltonianVectorField (H + c • G) :=
    (hXH.add (hXG.smul c hGd) hHd hcGd).eq_isSymplectic_hamiltonianVectorField hβ
  -- the base orbit
  have hΦ : IsMIntegralCurve
      (fun u : ℝ => hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s)
      (hβ.hamiltonianVectorField (H + c • G)) :=
    isMIntegralCurve_integralFlow _ s
  rw [← hbase] at hΦ
  have hΦc : Continuous fun u : ℝ =>
      hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s :=
    continuous_iff_continuousAt.2 fun u => (hΦ u).continuousAt
  have hGc : Continuous fun u : ℝ =>
      G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s) :=
    hG.continuous.comp hΦc
  have hacc : ∀ r : ℝ, HasDerivAt
      (fun r : ℝ => ∫ u in (0 : ℝ)..r,
        G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s))
      (G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) r s)) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 r)
      (hGc.stronglyMeasurableAtFilter volume _) hGc.continuousAt
  -- the closed-form curve
  have hγ : IsMIntegralCurve
      (fun r : ℝ => ((hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) r s,
        ((((b₀ + hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..r,
          G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s) : ℝ) :
          AddCircle (1 : ℝ))), ψ.2)) : S × KTorus))
      ((stepForm_isSymplectic hβ).hamiltonianVectorField (stepEnergy H G hg)) := by
    rw [← (isHamiltonianVectorField_step (β := β) hH hG hXH hXG hg
      hcg).eq_isSymplectic_hamiltonianVectorField (stepForm_isSymplectic hβ)]
    intro r
    have hS := hΦ r
    have hψ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun r : ℝ => (((b₀ + hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..r,
          G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s) : ℝ) :
          AddCircle (1 : ℝ)))) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (hg.deriv_periodic.lift ψ.2
          * G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) r s))) :=
      AddCircle.hasMFDerivAt_coe_comp (((hacc r).const_mul _).const_add b₀)
    have hψ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => ψ.2) r
        (0 : TangentSpace 𝓘(ℝ, ℝ) r →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) ψ.2) :=
      hasMFDerivAt_const ψ.2 r
    have h := hS.prodMk_self (hψ₁.prodMk_self hψ₂)
    refine h.congr_deriv ?_
    refine ContinuousLinearMap.ext fun a => Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · show ((1 : ℝ →L[ℝ] ℝ) a) • (hg.deriv_periodic.lift ψ.2
          * G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) r s))
        = ((1 : ℝ →L[ℝ] ℝ) a) • (G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) r s)
          * hg.deriv_periodic.lift ψ.2)
      rw [mul_comm]
    · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) a) • (0 : ℝ)
      rw [smul_zero]
  have h0 : ((hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) 0 s,
      ((((b₀ + hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..(0 : ℝ),
        G (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) u s) : ℝ) :
        AddCircle (1 : ℝ))), ψ.2)) : S × KTorus) = (s, ψ) := by
    rw [intervalIntegral.integral_same, mul_zero, add_zero, hb₀]
    exact Prod.ext (integralFlow_zero (hβ.contMDiff_hamiltonianVectorField_tangent
      (contMDiff_add_const_smul hH hG c)) s) rfl
  have h := integralFlow_eq_of_isMIntegralCurve
    ((stepForm_isSymplectic hβ).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_stepEnergy hH hG hg hcg)) hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t, AddCircle.coe_add, hb₀]

omit [CompactSpace S] [T2Space S] in
/-- The Hamiltonian flow depends on the energy only, not on the proof of its smoothness. -/
theorem hamiltonianFlow_congr [CompactSpace S] [T2Space S] (hβ : β.IsSymplectic) {H H' : S → ℝ}
    (h : H = H') (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hH' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H') :
    hβ.hamiltonianFlow hH = hβ.hamiltonianFlow hH' := by
  subst h
  rfl

/-- ★★ **The slice.** With the new torus's conserved angle held, the base moves by the base's
flow of `H + g(ψ₂) G`. -/
theorem hamiltonianFlow_stepEnergy_fst (hβ : β.IsSymplectic) {H G : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (s : S) (ψ : KTorus) :
    ((stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t (s, ψ)).1
      = hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG (hg.lift ψ.2)) t s := by
  rw [hamiltonianFlow_stepEnergy hβ hH hG hg hcg t s ψ]

/-! ### The preserved measure -/

/-- ★★★ **If every base flow preserves `μ`, the flow with one more torus preserves
`μ ⊗ vol_{T²}`.** Over each conserved angle the base moves by a base flow, which preserves `μ`,
and the new moving angle is translated by an amount that does not depend on it. -/
theorem map_hamiltonianFlow_stepEnergy [MeasurableSpace S] [BorelSpace S]
    (hβ : β.IsSymplectic) {H G : S → ℝ} (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G) (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g)
    (μ : Measure S) [SFinite μ] (t : ℝ)
    (hμ : ∀ c : ℝ,
      Measure.map (hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG c) t) μ = μ) :
    Measure.map
        ((stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t)
        (μ.prod (volume : Measure KTorus))
      = μ.prod (volume : Measure KTorus) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : S × KTorus → S × KTorus, Φ
      = (stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t :=
    ⟨_, rfl⟩
  rw [← hΦ]
  have hΦm : Measurable Φ := by
    rw [hΦ]
    exact ((stepForm_isSymplectic hβ).continuous_hamiltonianFlow _ t).measurable
  have hd : Measurable (Function.uncurry fun (σ : S) (b : AddCircle (1 : ℝ)) =>
      (Φ (σ, ((0 : AddCircle (1 : ℝ)), b))).2.1) :=
    (measurable_fst.comp (measurable_snd.comp hΦm)).comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hT := measurePreserving_addShear μ (volume : Measure (AddCircle (1 : ℝ))) hd
  have h1 : MeasurePreserving (fun w : KTorus × S => (w.1, (Φ (w.2, w.1)).1))
      ((volume : Measure KTorus).prod μ) ((volume : Measure KTorus).prod μ) := by
    refine MeasurePreserving.skew_product (μc := μ) (μd := μ)
      (g := fun (ψ : KTorus) (σ : S) => (Φ (σ, ψ)).1)
      (MeasurePreserving.id (volume : Measure KTorus)) ?_ (ae_of_all _ fun ψ => ?_)
    · exact (measurable_fst.comp hΦm).comp (measurable_snd.prodMk measurable_fst)
    · have hs : (fun σ : S => (Φ (σ, ψ)).1)
          = hβ.hamiltonianFlow (contMDiff_add_const_smul hH hG (hg.lift ψ.2)) t := by
        funext σ
        rw [hΦ]
        exact hamiltonianFlow_stepEnergy_fst hβ hH hG hg hcg t σ ψ
      rw [hs]
      exact hμ _
  have hG' : MeasurePreserving (fun z : S × KTorus => ((Φ z).1, z.2))
      (μ.prod (volume : Measure KTorus)) (μ.prod (volume : Measure KTorus)) :=
    Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)
  have hcomp : Φ
      = (fun z : S × KTorus => ((Φ z).1, z.2))
        ∘ (fun z : S × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) =>
          (z.1, (z.2.1 + (Φ (z.1, ((0 : AddCircle (1 : ℝ)), z.2.2))).2.1, z.2.2))) := by
    funext z
    obtain ⟨σ, ψ₁, ψ₂⟩ := z
    simp only [hΦ, Function.comp_apply, hamiltonianFlow_stepEnergy hβ hH hG hg hcg, zero_add]
  rw [hcomp]
  exact (hG'.comp hT).map_eq

end Step

/-! ### The two-torus arena is one step over the one-torus arena -/

section Echo

variable {N : ℕ} {f g : ℝ → ℝ}

/-- The echo arena's form is the step over the arena's form. -/
theorem echoForm_eq_stepForm (N : ℕ) : echoForm N = stepForm (arenaForm N) := rfl

/-- The two-torus energy is the step over the one-torus energy, coupled to `−2⟨B_B⟩` read on the
ray. -/
theorem twoCoupledEnergy_eq_stepEnergy (A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) :
    twoCoupledEnergy A BA BB hf hg
      = stepEnergy (coupledEnergy A BA hf)
          (fun p : KSigma (N + 1) => schrodingerHamiltonian BB p.1) hg :=
  rfl

end Echo

end LF4
end CSD

end
