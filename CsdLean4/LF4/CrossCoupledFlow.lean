/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.EchoCoupledFlow

/-!
# The Hamiltonian flow of a ray coupled to a torus in another factor

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #225, the generic half (residue of #212).

`EchoCoupledFlow.lean` generated the flow of a ray coupled to two tori on `ℂℙᴺ × T² × T²`. The
coupled clock and echo of #212 adds a second arena `ℂℙᴹ × T²` whose ray is coupled, through a
periodic potential, to the **first torus of the first factor**:

  `𝓗(p) = 𝓗_echo(x, θ, ψ) + [−2⟨A_c⟩(y) − 2⟨B_{c,A}⟩(y) f_c(θ₂) − 2⟨B_{c,B}⟩(y) h(χ₂)]`

on `(ℂℙᴺ × T² × T²) × (ℂℙᴹ × T²)`. The term `−2⟨B_{c,A}⟩(y) f_c(θ₂)` pairs a ray in one product
factor with a torus angle in the other, which the factorwise lemmas of `ArenaCoupledFlow.lean` and
`EchoCoupledFlow.lean` (ray and tori in one product) do not reach; its field is computed here by
pairing the product form factor by factor, three levels deep.

* `IsHamiltonianVectorField.prodForm_fst`, `IsHamiltonianVectorField.prodForm_snd` — **a Hamiltonian
  vector field on either factor lifts to `π₁^* α + π₂^* β`** (the general form of
  `isHamiltonianVectorField_fstLift`);
* `CrossSigma`, `crossForm`, ★ `crossForm_isSymplectic` — **`(ℂℙᴺ × T² × T²) × (ℂℙᴹ × T²)` is a
  symplectic manifold**;
* `crossView`, `contMDiff_crossView` — the second ray, the first factor's first torus and the second
  torus, arranged as an echo arena; `crossEnergy` — the echo's two-torus energy plus the second ray's
  read on the cross view; `crossCouplingTerm`, `crossEnergy_eq`, `contMDiff_crossEnergy`, `crossField`;
* ★★ `isHamiltonianVectorField_crossCouplingTerm` — **the cross term's field**: `f_c(θ₂) X_{B_{c,A}}` on the
  second ray and `(−2⟨B_{c,A}⟩(y) f_c'(θ₂), 0)` on the first factor's first torus;
  ★★ `isHamiltonianVectorField_cross`, `crossField_eq_hamiltonianVectorField` — **`ι_X ω = d𝓗` on
  the cross arena**;
* `crossCurve`, ★★ `isMIntegralCurve_crossCurve`; ★★★ `hamiltonianFlow_crossEnergy` — **the flow in
  closed form**: each ray by the Schrödinger unitary of its angle-dependent matrix, the first
  factor's `θ₁` advanced by **its own ray's accumulation plus the second ray's**, `ψ₁` and `χ₁` by
  their rays', the three second angles fixed.

References: `specs/BACKLOG.md` #225, #212, #202, #195; `LF4/EchoCoupledFlow.lean` (the two-torus case,
reused on both factors), `LF4/ArenaCoupledFlow.lean`, `LF4/ArenaSymplectic.lean`,
`Mathlib/Geometry/Manifold/ProductForm.lean` (`IsSymplectic.prodForm`, `prodSum_pair`),
`Mathlib/Geometry/Manifold/IntegralCurve/GlobalFlow.lean`.
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

/-! ### Lifting Hamiltonian vector fields to a product -/

section ProdLift

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace M'] [ChartedSpace F M']
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ M']

namespace DifferentialForm.IsHamiltonianVectorField

/-- **A Hamiltonian vector field on the first factor lifts to the product**: if `ι_X α = dH` then
`ι_{(X, 0)} (π₁^* α + π₂^* β) = d(H ∘ π₁)`. -/
theorem prodForm_fst {α : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin 2) ℝ}
    (β : DifferentialForm 𝓘(ℝ, F) M' ∞ (Fin 2) ℝ) {X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x}
    {H : M → ℝ} (hH : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H)
    (hX : IsHamiltonianVectorField (fun x => α x) X H) :
    IsHamiltonianVectorField (fun p => prodForm α β p)
      (fun p : M × M' => (((X p.1 : E), (0 : F)) : TangentSpace 𝓘(ℝ, E × F) p))
      (fun p => H p.1) := by
  intro p v
  have hv := hX p.1 (v : E × F).1
  have hz : toFlat (β p.2) ![(0 : F), (v : E × F).2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h1 : (prodForm α β p) ![(((X p.1 : E), (0 : F)) : TangentSpace 𝓘(ℝ, E × F) p), v]
      = toFlat (α p.1) ![(X p.1 : E), (v : E × F).1] + toFlat (β p.2) ![(0 : F), (v : E × F).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (α p.1)) (toFlat (β p.2)) ((X p.1 : E), (0 : F))
      (v : E × F)
  have hd : HasMFDerivAt 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ) (fun p : M × M' => H p.1) p
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H p.1).comp (ContinuousLinearMap.fst ℝ E F)) :=
    (hH p.1).hasMFDerivAt.comp p (Prod.hasMFDerivAt_fst_self (E := E) (F := F) p)
  have h2 : mfderiv 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ) (fun p : M × M' => H p.1) p v
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H p.1 (v : E × F).1 := by
    rw [hd.mfderiv]
    rfl
  refine h1.trans ?_
  rw [hz, add_zero]
  exact hv.trans h2.symm

/-- **A Hamiltonian vector field on the second factor lifts to the product**: if `ι_Y β = dK` then
`ι_{(0, Y)} (π₁^* α + π₂^* β) = d(K ∘ π₂)`. -/
theorem prodForm_snd (α : DifferentialForm 𝓘(ℝ, E) M ∞ (Fin 2) ℝ)
    {β : DifferentialForm 𝓘(ℝ, F) M' ∞ (Fin 2) ℝ} {Y : ∀ y : M', TangentSpace 𝓘(ℝ, F) y}
    {K : M' → ℝ} (hK : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, ℝ) K)
    (hY : IsHamiltonianVectorField (fun y => β y) Y K) :
    IsHamiltonianVectorField (fun p => prodForm α β p)
      (fun p : M × M' => (((0 : E), (Y p.2 : F)) : TangentSpace 𝓘(ℝ, E × F) p))
      (fun p => K p.2) := by
  intro p v
  have hv := hY p.2 (v : E × F).2
  have hz : toFlat (α p.1) ![(0 : E), (v : E × F).1] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h1 : (prodForm α β p) ![(((0 : E), (Y p.2 : F)) : TangentSpace 𝓘(ℝ, E × F) p), v]
      = toFlat (α p.1) ![(0 : E), (v : E × F).1] + toFlat (β p.2) ![(Y p.2 : F), (v : E × F).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (α p.1)) (toFlat (β p.2)) ((0 : E), (Y p.2 : F))
      (v : E × F)
  have hd : HasMFDerivAt 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ) (fun p : M × M' => K p.2) p
      ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) K p.2).comp (ContinuousLinearMap.snd ℝ E F)) :=
    (hK p.2).hasMFDerivAt.comp p (Prod.hasMFDerivAt_snd_self (E := E) (F := F) p)
  have h2 : mfderiv 𝓘(ℝ, E × F) 𝓘(ℝ, ℝ) (fun p : M × M' => K p.2) p v
      = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) K p.2 (v : E × F).2 := by
    rw [hd.mfderiv]
    rfl
  refine h1.trans ?_
  rw [hz, zero_add]
  exact hv.trans h2.symm

end DifferentialForm.IsHamiltonianVectorField

end ProdLift

namespace CSD
namespace LF4

variable {N M : ℕ}

/-! ### The cross arena and its symplectic form -/

/-- The cross arena's normed model: the echo arena's model times the arena's. -/
abbrev CrossModel (N M : ℕ) : Type := EchoModel N × ArenaModel M

/-- **The cross arena** `(ℂℙᴺ × T² × T²) × (ℂℙᴹ × T²)`: an echo arena and a second arena. -/
abbrev CrossSigma (N M : ℕ) : Type := EchoSigma N × KSigma (M + 1)

theorem crossSigma_isManifold (N M : ℕ) : IsManifold 𝓘(ℝ, CrossModel N M) ω (CrossSigma N M) :=
  inferInstance

/-- **The cross arena's symplectic form** `echoForm ⊕ arenaForm`. -/
noncomputable def crossForm (N M : ℕ) :
    DifferentialForm 𝓘(ℝ, CrossModel N M) (CrossSigma N M) ∞ (Fin 2) ℝ :=
  prodForm (echoForm N) (arenaForm M)

theorem crossForm_apply (N M : ℕ) (p : CrossSigma N M) :
    crossForm N M p
      = ContinuousAlternatingMap.prodSum (toFlat (echoForm N p.1)) (toFlat (arenaForm M p.2)) := rfl

/-- ★ **`(ℂℙᴺ × T² × T²) × (ℂℙᴹ × T²)` is a symplectic manifold.** -/
theorem crossForm_isSymplectic (N M : ℕ) : (crossForm N M).IsSymplectic :=
  (echoForm_isSymplectic N).prodForm (arenaForm_isSymplectic M)

/-! ### The view of the second ray -/

/-- **The cross view**: the second ray, the echo arena's first torus, and the second torus, arranged
as an echo arena. The second ray's energy is read here, so its first torus is the echo's. -/
def crossView (p : CrossSigma N M) : EchoSigma M := ((p.2.1, p.1.1.2), p.2.2)

theorem contMDiff_crossView :
    ContMDiff 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, EchoModel M) ∞ (crossView (N := N) (M := M)) := by
  have hsnd := Prod.contMDiff_snd_self (n := ∞) (E := EchoModel N) (F := ArenaModel M)
    (M := EchoSigma N) (N := KSigma (M + 1))
  have hfst := Prod.contMDiff_fst_self (n := ∞) (E := EchoModel N) (F := ArenaModel M)
    (M := EchoSigma N) (N := KSigma (M + 1))
  have hray := (Prod.contMDiff_fst_self (n := ∞) (E := Fin M → ℂ) (F := ℝ × ℝ)
    (M := CPN (M + 1)) (N := KTorus)).comp hsnd
  have htor := (Prod.contMDiff_snd_self (n := ∞) (E := Fin M → ℂ) (F := ℝ × ℝ)
    (M := CPN (M + 1)) (N := KTorus)).comp hsnd
  have hθ := ((Prod.contMDiff_snd_self (n := ∞) (E := Fin N → ℂ) (F := ℝ × ℝ)
    (M := CPN (N + 1)) (N := KTorus)).comp (Prod.contMDiff_fst_self (n := ∞) (E := ArenaModel N)
      (F := ℝ × ℝ) (M := KSigma (N + 1)) (N := KTorus))).comp hfst
  exact (hray.prodMk_self hθ).prodMk_self htor

/-! ### The cross energy and its field -/

section Energy

variable {f g fc h : ℝ → ℝ} (A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
  (Ac BcA BcB : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)

/-- **The cross energy**: the two-torus energy of the echo arena plus the two-torus energy of the
second ray read on the cross view,
`−2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂) − 2⟨A_c⟩(y) − 2⟨B_{c,A}⟩(y) f_c(θ₂) − 2⟨B_{c,B}⟩(y) h(χ₂)`.
The term `−2⟨B_{c,A}⟩(y) f_c(θ₂)` couples the second ray to the echo arena's first torus. -/
noncomputable def crossEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hfc : Function.Periodic fc 1) (hh : Function.Periodic h 1) (p : CrossSigma N M) : ℝ :=
  twoCoupledEnergy A BA BB hf hg p.1 + twoCoupledEnergy Ac BcA BcB hfc hh (crossView p)

/-- **The cross term** `−2⟨B_{c,A}⟩(y) f_c(θ₂)`: the second ray coupled to the echo arena's first
torus. -/
noncomputable def crossCouplingTerm (hfc : Function.Periodic fc 1) (p : CrossSigma N M) : ℝ :=
  schrodingerHamiltonian BcA p.2.1 * torusPotential hfc p.1.1.2

/-- The cross energy as the echo energy on the first factor, a one-torus energy on the second, and
the cross term. -/
theorem crossEnergy_eq (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hfc : Function.Periodic fc 1) (hh : Function.Periodic h 1) :
    crossEnergy A BA BB Ac BcA BcB hf hg hfc hh
      = (fun p : CrossSigma N M => twoCoupledEnergy A BA BB hf hg p.1)
        + (fun p : CrossSigma N M => coupledEnergy Ac BcB hh p.2) + crossCouplingTerm BcA hfc := by
  funext p
  show twoCoupledEnergy A BA BB hf hg p.1 + (schrodingerHamiltonian Ac p.2.1
      + schrodingerHamiltonian BcA p.2.1 * torusPotential hfc p.1.1.2
      + schrodingerHamiltonian BcB p.2.1 * torusPotential hh p.2.2)
    = twoCoupledEnergy A BA BB hf hg p.1 + (schrodingerHamiltonian Ac p.2.1
      + schrodingerHamiltonian BcB p.2.1 * torusPotential hh p.2.2)
      + schrodingerHamiltonian BcA p.2.1 * torusPotential hfc p.1.1.2
  ring

/-- The cross energy is `C^∞` on the cross arena. -/
theorem contMDiff_crossEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hfc : Function.Periodic fc 1) (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hcfc : ContDiff ℝ ∞ fc) (hch : ContDiff ℝ ∞ h) :
    ContMDiff 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ) ∞ (crossEnergy A BA BB Ac BcA BcB hf hg hfc hh) :=
  ((contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg).comp
    (Prod.contMDiff_fst_self (E := EchoModel N) (F := ArenaModel M) (M := EchoSigma N)
      (N := KSigma (M + 1)))).add
    ((contMDiff_twoCoupledEnergy Ac BcA BcB hfc hh hcfc hch).comp contMDiff_crossView)

/-- The cross term is `C^∞` on the cross arena. -/
theorem contMDiff_crossCouplingTerm (hfc : Function.Periodic fc 1) (hcfc : ContDiff ℝ ∞ fc) :
    ContMDiff 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ) ∞ (crossCouplingTerm (N := N) BcA hfc) := by
  have hsnd := Prod.contMDiff_snd_self (n := ∞) (E := EchoModel N) (F := ArenaModel M)
    (M := EchoSigma N) (N := KSigma (M + 1))
  have hfst := Prod.contMDiff_fst_self (n := ∞) (E := EchoModel N) (F := ArenaModel M)
    (M := EchoSigma N) (N := KSigma (M + 1))
  have hray := (Prod.contMDiff_fst_self (n := ∞) (E := Fin M → ℂ) (F := ℝ × ℝ)
    (M := CPN (M + 1)) (N := KTorus)).comp hsnd
  have hθ := ((Prod.contMDiff_snd_self (n := ∞) (E := Fin N → ℂ) (F := ℝ × ℝ)
    (M := CPN (N + 1)) (N := KTorus)).comp (Prod.contMDiff_fst_self (n := ∞) (E := ArenaModel N)
      (F := ℝ × ℝ) (M := KSigma (N + 1)) (N := KTorus))).comp hfst
  exact ((contMDiff_schrodingerHamiltonian (m := ∞) BcA).comp hray).mul
    ((contMDiff_torusPotential hfc hcfc).comp hθ)

/-- **The cross field**: on the echo arena, the two-torus field with `θ₁` also driven by the second
ray (`−2⟨B_{c,A}⟩(y) f_c'(θ₂)`); on the second arena, the one-torus field of `A_c + h(χ₂) B_{c,B}`
plus `f_c(θ₂) X_{B_{c,A}}` on the ray. -/
noncomputable def crossField (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hfc : Function.Periodic fc 1) (hh : Function.Periodic h 1) (p : CrossSigma N M) :
    TangentSpace 𝓘(ℝ, CrossModel N M) p :=
  (((((schrodingerField A p.1.1.1 + torusPotential hf p.1.1.2 • schrodingerField BA p.1.1.1
          + torusPotential hg p.1.2 • schrodingerField BB p.1.1.1,
        ((schrodingerHamiltonian BA p.1.1.1 * hf.deriv_periodic.lift p.1.1.2.2
          + schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
      ((schrodingerHamiltonian BB p.1.1.1 * hg.deriv_periodic.lift p.1.2.2, 0) : ℝ × ℝ)),
    (schrodingerField Ac p.2.1 + torusPotential hh p.2.2 • schrodingerField BcB p.2.1
        + torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1,
      ((schrodingerHamiltonian BcB p.2.1 * hh.deriv_periodic.lift p.2.2.2, 0) : ℝ × ℝ))) :
    CrossModel N M) : TangentSpace 𝓘(ℝ, CrossModel N M) p)

/-- ★★ **The cross term's field**: `ι_X ω = d(−2⟨B_{c,A}⟩(y) f_c(θ₂))` on the cross arena for
`X = (((0, (−2⟨B_{c,A}⟩(y) f_c'(θ₂), 0)), 0), (f_c(θ₂) X_{B_{c,A}}, 0))` — a ray in the second factor
paired with a torus angle in the first. -/
theorem isHamiltonianVectorField_crossCouplingTerm {BcA : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    (hBcA : BcA.IsHermitian) (hfc : Function.Periodic fc 1) (hd : Differentiable ℝ fc) :
    IsHamiltonianVectorField (fun p => crossForm N M p)
      (fun p : CrossSigma N M =>
        (((((0 : Fin N → ℂ),
              ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
            (0 : ℝ × ℝ)),
          (torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (0 : ℝ × ℝ))) :
          TangentSpace 𝓘(ℝ, CrossModel N M) p))
      (crossCouplingTerm BcA hfc) := by
  intro p v
  have hsnd : HasMFDerivAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, Fin M → ℂ)
      (fun q : CrossSigma N M => q.2.1) p
      ((ContinuousLinearMap.fst ℝ (Fin M → ℂ) (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ (EchoModel N) (ArenaModel M))) :=
    (Prod.hasMFDerivAt_fst_self (E := Fin M → ℂ) (F := ℝ × ℝ) p.2).comp p
      (Prod.hasMFDerivAt_snd_self (E := EchoModel N) (F := ArenaModel M) p)
  have htor : HasMFDerivAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ × ℝ)
      (fun q : CrossSigma N M => q.1.1.2) p
      (((ContinuousLinearMap.snd ℝ (Fin N → ℂ) (ℝ × ℝ)).comp
        (ContinuousLinearMap.fst ℝ (ArenaModel N) (ℝ × ℝ))).comp
          (ContinuousLinearMap.fst ℝ (EchoModel N) (ArenaModel M))) :=
    ((Prod.hasMFDerivAt_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) p.1.1).comp p.1
      (Prod.hasMFDerivAt_fst_self (E := ArenaModel N) (F := ℝ × ℝ) p.1)).comp p
        (Prod.hasMFDerivAt_fst_self (E := EchoModel N) (F := ArenaModel M) p)
  have ha := (mdifferentiableAt_schrodingerHamiltonian BcA p.2.1).hasMFDerivAt.comp p hsnd
  have hb := (hasMFDerivAt_torusPotential hfc hd p.1.1.2).comp p htor
  have hprod : HasMFDerivAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ) (crossCouplingTerm BcA hfc) p _ := ha.mul hb
  rw [hprod.mfderiv]
  have hX := schrodingerField_isHamiltonianVectorField hBcA p.2.1 (v : CrossModel N M).2.1
  have h1 : (crossForm N M p)
      ![(((((0 : Fin N → ℂ),
              ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
            (0 : ℝ × ℝ)),
          (torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (0 : ℝ × ℝ))) :
          TangentSpace 𝓘(ℝ, CrossModel N M) p), v]
      = toFlat (echoForm N p.1)
          ![(((0 : Fin N → ℂ),
              ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
            (0 : ℝ × ℝ)), (v : CrossModel N M).1]
        + toFlat (arenaForm M p.2)
          ![(torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (0 : ℝ × ℝ)),
            (v : CrossModel N M).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (echoForm N p.1)) (toFlat (arenaForm M p.2)) _ _
  have h2 : toFlat (echoForm N p.1)
      ![(((0 : Fin N → ℂ),
          ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
        (0 : ℝ × ℝ)), (v : CrossModel N M).1]
      = toFlat (arenaForm N p.1.1)
          ![((0 : Fin N → ℂ),
            ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
            (v : CrossModel N M).1.1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : CrossModel N M).1.2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (arenaForm N p.1.1)) TorusForm.areaForm _ _
  have h3 : toFlat (arenaForm N p.1.1)
      ![((0 : Fin N → ℂ),
        ((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ)),
        (v : CrossModel N M).1.1]
      = toFlat (fsForm (n := N) p.1.1.1) ![(0 : Fin N → ℂ), (v : CrossModel N M).1.1.1]
        + TorusForm.areaForm
          ![((schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2, 0) : ℝ × ℝ),
            (v : CrossModel N M).1.1.2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := N) p.1.1.1)) TorusForm.areaForm _ _
  have h4 : toFlat (arenaForm M p.2)
      ![(torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (0 : ℝ × ℝ)),
        (v : CrossModel N M).2]
      = toFlat (fsForm (n := M) p.2.1)
          ![torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (v : CrossModel N M).2.1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : CrossModel N M).2.2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := M) p.2.1)) TorusForm.areaForm _ _
  have hz1 : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : CrossModel N M).1.2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have hz2 : toFlat (fsForm (n := N) p.1.1.1) ![(0 : Fin N → ℂ), (v : CrossModel N M).1.1.1] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have hz3 : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : CrossModel N M).2.2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h5 : toFlat (fsForm (n := M) p.2.1)
      ![torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1, (v : CrossModel N M).2.1]
      = torusPotential hfc p.1.1.2 * toFlat (fsForm (n := M) p.2.1)
          ![schrodingerField BcA p.2.1, (v : CrossModel N M).2.1] :=
    apply_smul_left (fun x : CPN (M + 1) => fsForm (n := M) x) p.2.1 _ _ _
  have h6 : toFlat (fsForm (n := M) p.2.1) ![schrodingerField BcA p.2.1, (v : CrossModel N M).2.1]
      = mfderiv 𝓘(ℝ, Fin M → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian BcA) p.2.1
          (v : CrossModel N M).2.1 :=
    hX
  rw [h1, h2, h3, h4, hz1, hz2, hz3, h5, h6, TorusForm.areaForm_apply]
  set D : ℝ := mfderiv 𝓘(ℝ, Fin M → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian BcA) p.2.1
    (v : CrossModel N M).2.1 with hD
  show 0 + (schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2
        * (v : CrossModel N M).1.1.2.2 - 0 * (v : CrossModel N M).1.1.2.1) + 0
      + (torusPotential hfc p.1.1.2 * D + 0)
    = schrodingerHamiltonian BcA p.2.1
        * ((v : CrossModel N M).1.1.2.2 * hfc.deriv_periodic.lift p.1.1.2.2)
      + torusPotential hfc p.1.1.2 * D
  ring

/-- ★★ **`ι_X ω = d𝓗` on the cross arena for the cross energy**: the echo arena's two-torus field
lifted from the first factor, the second arena's one-torus field lifted from the second, and the
cross term's field. -/
theorem isHamiltonianVectorField_cross {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    {Ac BcA BcB : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hAc : Ac.IsHermitian) (hBcA : BcA.IsHermitian) (hBcB : BcB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hfc : Function.Periodic fc 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcfc : ContDiff ℝ ∞ fc) (hch : ContDiff ℝ ∞ h) :
    IsHamiltonianVectorField (fun p => crossForm N M p)
      (crossField A BA BB Ac BcA BcB hf hg hfc hh) (crossEnergy A BA BB Ac BcA BcB hf hg hfc hh) := by
  have hmE : MDifferentiable 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) (twoCoupledEnergy A BA BB hf hg) :=
    fun p => (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg p).mdifferentiableAt (by simp)
  have hmC : MDifferentiable 𝓘(ℝ, ArenaModel M) 𝓘(ℝ, ℝ) (coupledEnergy Ac BcB hh) :=
    fun p => (contMDiff_coupledEnergy Ac BcB hh hch p).mdifferentiableAt (by simp)
  have hE := (isHamiltonianVectorField_twoCoupled hA hBA hBB hf hg hc hcg).prodForm_fst
    (arenaForm M) hmE
  have hC := (isHamiltonianVectorField_coupled hAc hBcB hh
    (hch.differentiable (by simp))).prodForm_snd (echoForm N) hmC
  have hX := isHamiltonianVectorField_crossCouplingTerm (N := N) hBcA hfc (hcfc.differentiable (by simp))
  have hdE : ∀ p : CrossSigma N M, MDifferentiableAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ)
      (fun p : CrossSigma N M => twoCoupledEnergy A BA BB hf hg p.1) p := fun p =>
    (((contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg).comp
      (Prod.contMDiff_fst_self (E := EchoModel N) (F := ArenaModel M) (M := EchoSigma N)
        (N := KSigma (M + 1)))) p).mdifferentiableAt (by simp)
  have hdC : ∀ p : CrossSigma N M, MDifferentiableAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ)
      (fun p : CrossSigma N M => coupledEnergy Ac BcB hh p.2) p := fun p =>
    (((contMDiff_coupledEnergy Ac BcB hh hch).comp
      (Prod.contMDiff_snd_self (E := EchoModel N) (F := ArenaModel M) (M := EchoSigma N)
        (N := KSigma (M + 1)))) p).mdifferentiableAt (by simp)
  have hdEC : ∀ p : CrossSigma N M, MDifferentiableAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ)
      ((fun p : CrossSigma N M => twoCoupledEnergy A BA BB hf hg p.1)
        + fun p : CrossSigma N M => coupledEnergy Ac BcB hh p.2) p := fun p =>
    (hdE p).add (hdC p)
  have hdX : ∀ p : CrossSigma N M, MDifferentiableAt 𝓘(ℝ, CrossModel N M) 𝓘(ℝ, ℝ)
      (crossCouplingTerm BcA hfc) p := fun p => (contMDiff_crossCouplingTerm BcA hfc hcfc p).mdifferentiableAt
        (by simp)
  have hsum := (hE.add hC hdE hdC).add hX hdEC hdX
  rw [crossEnergy_eq]
  intro p v
  refine Eq.trans ?_ (hsum p v)
  congr 2
  refine Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ ?_))
    (Prod.ext ?_ (Prod.ext ?_ ?_))
  · show schrodingerField A p.1.1.1 + torusPotential hf p.1.1.2 • schrodingerField BA p.1.1.1
        + torusPotential hg p.1.2 • schrodingerField BB p.1.1.1
      = schrodingerField A p.1.1.1 + torusPotential hf p.1.1.2 • schrodingerField BA p.1.1.1
        + torusPotential hg p.1.2 • schrodingerField BB p.1.1.1 + 0 + 0
    rw [add_zero, add_zero]
  · show schrodingerHamiltonian BA p.1.1.1 * hf.deriv_periodic.lift p.1.1.2.2
        + schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2
      = schrodingerHamiltonian BA p.1.1.1 * hf.deriv_periodic.lift p.1.1.2.2 + 0
        + schrodingerHamiltonian BcA p.2.1 * hfc.deriv_periodic.lift p.1.1.2.2
    rw [add_zero]
  · show (0 : ℝ) = 0 + 0 + 0
    simp
  · show schrodingerHamiltonian BB p.1.1.1 * hg.deriv_periodic.lift p.1.2.2
      = schrodingerHamiltonian BB p.1.1.1 * hg.deriv_periodic.lift p.1.2.2 + 0 + 0
    rw [add_zero, add_zero]
  · show (0 : ℝ) = 0 + 0 + 0
    simp
  · show schrodingerField Ac p.2.1 + torusPotential hh p.2.2 • schrodingerField BcB p.2.1
        + torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1
      = 0 + (schrodingerField Ac p.2.1 + torusPotential hh p.2.2 • schrodingerField BcB p.2.1)
        + torusPotential hfc p.1.1.2 • schrodingerField BcA p.2.1
    rw [zero_add]
  · show schrodingerHamiltonian BcB p.2.1 * hh.deriv_periodic.lift p.2.2.2
      = 0 + schrodingerHamiltonian BcB p.2.1 * hh.deriv_periodic.lift p.2.2.2 + 0
    rw [zero_add, add_zero]
  · show (0 : ℝ) = 0 + 0 + 0
    simp

/-- **`X_𝓗 = crossField`** (uniqueness for the symplectic `crossForm`). -/
theorem crossField_eq_hamiltonianVectorField {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    {Ac BcA BcB : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hAc : Ac.IsHermitian) (hBcA : BcA.IsHermitian) (hBcB : BcB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hfc : Function.Periodic fc 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcfc : ContDiff ℝ ∞ fc) (hch : ContDiff ℝ ∞ h) :
    crossField A BA BB Ac BcA BcB hf hg hfc hh
      = (crossForm_isSymplectic N M).hamiltonianVectorField
          (crossEnergy A BA BB Ac BcA BcB hf hg hfc hh) :=
  (isHamiltonianVectorField_cross hA hBA hBB hAc hBcA hBcB hf hg hfc hh hc hcg hcfc
    hch).eq_isSymplectic_hamiltonianVectorField (crossForm_isSymplectic N M)

/-! ### The flow in closed form -/

variable {A BA BB Ac BcA BcB}

/-- **The closed-form curve**: on the echo arena, the two-angle orbit of `A + f(φ) B_A + g(ψ) B_B`,
`θ₁ = a₀ + f'(φ) ∫ (−2⟨B_A⟩) + f_c'(φ) ∫ (−2⟨B_{c,A}⟩)` (the echo's and the second ray's
accumulations), `ψ₁ = b₀ + g'(ψ) ∫ (−2⟨B_B⟩)`; on the second arena, the two-angle orbit of
`A_c + f_c(φ) B_{c,A} + h(χ) B_{c,B}` and `χ₁ = c₀ + h'(χ) ∫ (−2⟨B_{c,B}⟩)`; the angles `φ, ψ, χ`
fixed. -/
noncomputable def crossCurve (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hAc : Ac.IsHermitian) (hBcA : BcA.IsHermitian) (hBcB : BcB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hfc : Function.Periodic fc 1)
    (hh : Function.Periodic h 1) (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (b₀ : ℝ)
    (ψ : AddCircle (1 : ℝ)) (y : CPN (M + 1)) (c₀ : ℝ) (χ : AddCircle (1 : ℝ)) (t : ℝ) :
    CrossSigma N M :=
  (((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x,
      (((a₀ + (hf.deriv_periodic.lift φ * twoAccumA hA hBA hBB hf hg φ ψ x t
          + hfc.deriv_periodic.lift φ * twoAccumA hAc hBcA hBcB hfc hh φ χ y t) : ℝ) :
        AddCircle (1 : ℝ)), φ)),
    (((b₀ + hg.deriv_periodic.lift ψ * twoAccumB hA hBA hBB hf hg φ ψ x t : ℝ) :
      AddCircle (1 : ℝ)), ψ)),
   (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y,
    (((c₀ + hh.deriv_periodic.lift χ * twoAccumB hAc hBcA hBcB hfc hh φ χ y t : ℝ) :
      AddCircle (1 : ℝ)), χ)))

/-- ★★ **The closed-form curve is an integral curve of the cross field.** -/
theorem isMIntegralCurve_crossCurve (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hAc : Ac.IsHermitian) (hBcA : BcA.IsHermitian) (hBcB : BcB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hfc : Function.Periodic fc 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcfc : ContDiff ℝ ∞ fc) (hch : ContDiff ℝ ∞ h) (x : CPN (N + 1)) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (b₀ : ℝ) (ψ : AddCircle (1 : ℝ)) (y : CPN (M + 1)) (c₀ : ℝ)
    (χ : AddCircle (1 : ℝ)) :
    IsMIntegralCurve (crossCurve hA hBA hBB hAc hBcA hBcB hf hg hfc hh x a₀ φ b₀ ψ y c₀ χ)
      ((crossForm_isSymplectic N M).hamiltonianVectorField
        (crossEnergy A BA BB Ac BcA BcB hf hg hfc hh)) := by
  rw [← crossField_eq_hamiltonianVectorField hA hBA hBB hAc hBcA hBcB hf hg hfc hh hc hcg hcfc hch]
  intro t
  have hrayE := isMIntegralCurve_schrodingerUnitary_smul
    (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) x t
  have hrayC := isMIntegralCurve_schrodingerUnitary_smul
    (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) y t
  have hθ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => (((a₀ + (hf.deriv_periodic.lift φ * twoAccumA hA hBA hBB hf hg φ ψ x u
          + hfc.deriv_periodic.lift φ * twoAccumA hAc hBcA hBcB hfc hh φ χ y u) : ℝ) :
        AddCircle (1 : ℝ)))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift φ * schrodingerHamiltonian BA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)
        + hfc.deriv_periodic.lift φ * schrodingerHamiltonian BcA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t
            • y))) :=
    AddCircle.hasMFDerivAt_coe_comp
      ((((hasDerivAt_twoAccumA hA hBA hBB hf hg φ ψ x t).const_mul _).add
        ((hasDerivAt_twoAccumA hAc hBcA hBcB hfc hh φ χ y t).const_mul _)).const_add a₀)
  have hθ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => φ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) φ) :=
    hasMFDerivAt_const φ t
  have hψ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => (((b₀ + hg.deriv_periodic.lift ψ * twoAccumB hA hBA hBB hf hg φ ψ x u : ℝ) :
        AddCircle (1 : ℝ)))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hg.deriv_periodic.lift ψ * schrodingerHamiltonian BB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x))) :=
    AddCircle.hasMFDerivAt_coe_comp
      (((hasDerivAt_twoAccumB hA hBA hBB hf hg φ ψ x t).const_mul _).const_add b₀)
  have hψ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => ψ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) ψ) :=
    hasMFDerivAt_const ψ t
  have hχ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => (((c₀ + hh.deriv_periodic.lift χ * twoAccumB hAc hBcA hBcB hfc hh φ χ y u : ℝ) :
        AddCircle (1 : ℝ)))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hh.deriv_periodic.lift χ * schrodingerHamiltonian BcB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t
          • y))) :=
    AddCircle.hasMFDerivAt_coe_comp
      (((hasDerivAt_twoAccumB hAc hBcA hBcB hfc hh φ χ y t).const_mul _).const_add c₀)
  have hχ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => χ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) χ) :=
    hasMFDerivAt_const χ t
  rw [schrodingerField_twoCoupledMatrix hA hBA hBB] at hrayE
  rw [schrodingerField_twoCoupledMatrix hAc hBcA hBcB] at hrayC
  have hd := ((hrayE.prodMk_self (hθ₁.prodMk_self hθ₂)).prodMk_self
    (hψ₁.prodMk_self hψ₂)).prodMk_self (hrayC.prodMk_self (hχ₁.prodMk_self hχ₂))
  refine hd.congr_deriv ?_
  refine ContinuousLinearMap.ext fun s => Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
    (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hf.deriv_periodic.lift φ * schrodingerHamiltonian BA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)
        + hfc.deriv_periodic.lift φ * schrodingerHamiltonian BcA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t
            • y))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian BA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)
            * hf.deriv_periodic.lift φ
        + schrodingerHamiltonian BcA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t
            • y) * hfc.deriv_periodic.lift φ)
    ring
  · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) s) • (0 : ℝ)
    rw [smul_zero]
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hg.deriv_periodic.lift ψ * schrodingerHamiltonian BB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian BB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)
          * hg.deriv_periodic.lift ψ)
    rw [mul_comm]
  · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) s) • (0 : ℝ)
    rw [smul_zero]
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerField Ac
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y)
        + hfc.lift φ • schrodingerField BcA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y)
        + hh.lift χ • schrodingerField BcB
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerField Ac
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y)
        + hh.lift χ • schrodingerField BcB
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y)
        + hfc.lift φ • schrodingerField BcA
          (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y))
    rw [add_right_comm (schrodingerField Ac _)]
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hh.deriv_periodic.lift χ * schrodingerHamiltonian BcB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian BcB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh φ χ) t • y)
          * hh.deriv_periodic.lift χ)
    rw [mul_comm]
  · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) s) • (0 : ℝ)
    rw [smul_zero]

/-- ★★★ **The Hamiltonian flow of the cross energy in closed form.** On the echo arena: the
Schrödinger unitary of `A + f(θ₂) B_A + g(ψ₂) B_B` on the ray, `θ₁` advanced by
`f'(θ₂) ∫ (−2⟨B_A⟩) + f_c'(θ₂) ∫ (−2⟨B_{c,A}⟩)` — **the echo's own accumulation plus the second
ray's** — and `ψ₁` by `g'(ψ₂) ∫ (−2⟨B_B⟩)`; on the second arena, the Schrödinger unitary of
`A_c + f_c(θ₂) B_{c,A} + h(χ₂) B_{c,B}` and `χ₁` advanced by `h'(χ₂) ∫ (−2⟨B_{c,B}⟩)`; the three
second angles fixed. -/
theorem hamiltonianFlow_crossEnergy (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hAc : Ac.IsHermitian) (hBcA : BcA.IsHermitian) (hBcB : BcB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hfc : Function.Periodic fc 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcfc : ContDiff ℝ ∞ fc) (hch : ContDiff ℝ ∞ h) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus)
    (y : CPN (M + 1)) (χ : KTorus) :
    (crossForm_isSymplectic N M).hamiltonianFlow
        (contMDiff_crossEnergy A BA BB Ac BcA BcB hf hg hfc hh hc hcg hcfc hch) t
        (((x, θ), ψ), (y, χ))
      = (((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) t • x,
            (θ.1 + ((hf.deriv_periodic.lift θ.2 * twoAccumA hA hBA hBB hf hg θ.2 ψ.2 x t
                + hfc.deriv_periodic.lift θ.2 * twoAccumA hAc hBcA hBcB hfc hh θ.2 χ.2 y t : ℝ) :
              AddCircle (1 : ℝ)), θ.2)),
          (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * twoAccumB hA hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)),
         (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh θ.2 χ.2) t
            • y,
          (χ.1 + ((hh.deriv_periodic.lift χ.2 * twoAccumB hAc hBcA hBcB hfc hh θ.2 χ.2 y t : ℝ) :
            AddCircle (1 : ℝ)), χ.2))) := by
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk_surjective θ.1
  obtain ⟨b₀, hb₀⟩ := QuotientAddGroup.mk_surjective ψ.1
  obtain ⟨c₀, hc₀⟩ := QuotientAddGroup.mk_surjective χ.1
  have hγ := isMIntegralCurve_crossCurve hA hBA hBB hAc hBcA hBcB hf hg hfc hh hc hcg hcfc hch x a₀
    θ.2 b₀ ψ.2 y c₀ χ.2
  have h0 : crossCurve hA hBA hBB hAc hBcA hBcB hf hg hfc hh x a₀ θ.2 b₀ ψ.2 y c₀ χ.2 0
      = (((x, θ), ψ), (y, χ)) := by
    unfold crossCurve
    rw [(Matrix.expNegITH_unitary_group (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2)).2,
      (Matrix.expNegITH_unitary_group
        (twoCoupledMatrix_isHermitian hAc hBcA hBcB hfc hh θ.2 χ.2)).2, one_smul, one_smul,
      twoAccumA_zero, twoAccumA_zero, twoAccumB_zero, twoAccumB_zero, mul_zero, mul_zero, mul_zero,
      mul_zero, add_zero, add_zero, add_zero, add_zero, ha₀, hb₀, hc₀]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((crossForm_isSymplectic N M).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_crossEnergy A BA BB Ac BcA BcB hf hg hfc hh hc hcg hcfc hch)) hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t]
  unfold crossCurve
  simp only [← ha₀, ← hb₀, ← hc₀, AddCircle.coe_add]

end Energy

end LF4
end CSD

end
