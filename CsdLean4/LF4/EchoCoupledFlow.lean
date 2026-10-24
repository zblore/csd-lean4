/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaCoupledFlow

/-!
# The Hamiltonian flow of a ray coupled to two tori

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #202, the generation half (out of #39).

`ArenaCoupledFlow.lean` generated the flow of `−2⟨A⟩ − 2⟨B⟩ f(θ₂)` on `ℂℙᴺ × T²`. The echo of #199
has a pointer at each station, so its arena is `ℂℙᴺ × T² × T²` and its energy couples the ray to
both tori:

  `𝓗(x, θ, ψ) = −2⟨A⟩(x) − 2⟨B_A⟩(x) f(θ₂) − 2⟨B_B⟩(x) g(ψ₂)`.

The symplectic form is the product `arenaForm ⊕ dψ₁ ∧ dψ₂` (`IsSymplectic.prodForm` run once more),
and the Hamiltonian vector field is the lift of the one-torus field from the first factor plus one
more coupled term for the outer torus. The flow is again a skew product over the two conserved angles,
in closed form, by uniqueness of integral curves on the compact arena.

* `EchoSigma`, `echoForm`, ★ `echoForm_isSymplectic` — **`ℂℙᴺ × T² × T²` is a symplectic manifold**;
* `twoCoupledEnergy`, `contMDiff_twoCoupledEnergy`, `twoCoupledField`;
* ★ `isHamiltonianVectorField_fstLift` — **a Hamiltonian vector field on the arena lifts to the
  product with the outer torus** (the general form of `isHamiltonianVectorField_sectorEnergy`);
  ★ `isHamiltonianVectorField_outerTerm` — the coupled term for the outer torus; ★★
  `isHamiltonianVectorField_twoCoupled`, `twoCoupledField_eq_hamiltonianVectorField` — **`ι_X ω = d𝓗`
  on `ℂℙᴺ × T² × T²`**;
* `twoCoupledMatrix`, `twoAccumA`, `twoAccumB`, `twoCoupledCurve`, ★★ `isMIntegralCurve_twoCoupledCurve`;
  ★★★ `hamiltonianFlow_twoCoupledEnergy` — **the flow in closed form**: the Schrödinger unitary of
  `A + f(θ₂) B_A + g(ψ₂) B_B` on the ray, `θ₁` advanced by `f'(θ₂) ∫ (−2⟨B_A⟩)`, `ψ₁` by
  `g'(ψ₂) ∫ (−2⟨B_B⟩)`, both second angles fixed.

References: `specs/BACKLOG.md` #202, #199, #195, #39; `LF4/ArenaCoupledFlow.lean` (the one-torus
case, every lemma of which is reused), `LF4/ArenaSymplectic.lean`, `Mathlib/Geometry/Manifold/ProductForm.lean`
(`IsSymplectic.prodForm`, `prodSum_pair`), `Mathlib/Geometry/Manifold/IntegralCurve/GlobalFlow.lean`.
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The echo arena and its symplectic form -/

/-- The echo arena's normed model: the arena's model times the model of one more torus. -/
abbrev EchoModel (N : ℕ) : Type := ArenaModel N × (ℝ × ℝ)

/-- The echo arena `ℂℙᴺ × T² × T²`. -/
abbrev EchoSigma (N : ℕ) : Type := KSigma (N + 1) × KTorus

theorem echoSigma_isManifold (N : ℕ) : IsManifold 𝓘(ℝ, EchoModel N) ω (EchoSigma N) :=
  inferInstance

/-- **The echo arena's symplectic form** `arenaForm ⊕ dψ₁ ∧ dψ₂`. -/
noncomputable def echoForm (N : ℕ) : DifferentialForm 𝓘(ℝ, EchoModel N) (EchoSigma N) ∞ (Fin 2) ℝ :=
  prodForm (arenaForm N) (AddCircle.torusAreaForm (T := 1) (T' := 1))

theorem echoForm_apply (N : ℕ) (p : EchoSigma N) :
    echoForm N p
      = ContinuousAlternatingMap.prodSum (toFlat (arenaForm N p.1)) TorusForm.areaForm := rfl

/-- ★ **`ℂℙᴺ × T² × T²` is a symplectic manifold.** -/
theorem echoForm_isSymplectic (N : ℕ) : (echoForm N).IsSymplectic :=
  (arenaForm_isSymplectic N).prodForm AddCircle.torusAreaForm_isSymplectic

/-! ### Lifting a Hamiltonian vector field from the arena to the product -/

/-- ★ **A Hamiltonian vector field on the arena lifts to the product with the outer torus**: if
`ι_X arenaForm = dH` then `ι_{(X, 0)} echoForm = d(H ∘ π₁)`. -/
theorem isHamiltonianVectorField_fstLift {X : ∀ p : KSigma (N + 1), TangentSpace 𝓘(ℝ, ArenaModel N) p}
    {H : KSigma (N + 1) → ℝ} (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H)
    (hX : IsHamiltonianVectorField (fun p => arenaForm N p) X H) :
    IsHamiltonianVectorField (fun p => echoForm N p)
      (fun p : EchoSigma N => ((X p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, EchoModel N) p))
      (fun p => H p.1) := by
  intro p v
  have hv := hX p.1 (v : EchoModel N).1
  have hz : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : EchoModel N).2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h1 : (echoForm N p) ![((X p.1 : ArenaModel N), (0 : ℝ × ℝ)), v]
      = toFlat (arenaForm N p.1) ![(X p.1 : ArenaModel N), (v : EchoModel N).1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : EchoModel N).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (arenaForm N p.1)) TorusForm.areaForm
      ((X p.1 : ArenaModel N), (0 : ℝ × ℝ)) (v : EchoModel N)
  have hd : HasMFDerivAt 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) (fun p : EchoSigma N => H p.1) p
      ((mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p.1).comp
        (ContinuousLinearMap.fst ℝ (ArenaModel N) (ℝ × ℝ))) :=
    ((hH p.1).mdifferentiableAt (by simp)).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := ArenaModel N) (F := ℝ × ℝ) p)
  have h2 : mfderiv 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) (fun p : EchoSigma N => H p.1) p v
      = mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) H p.1 (v : EchoModel N).1 := by
    rw [hd.mfderiv]
    rfl
  refine h1.trans ?_
  rw [hz, add_zero]
  exact hv.trans h2.symm

/-! ### The two-torus energy and its field -/

section Energy

variable {f g : ℝ → ℝ} (A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **The two-torus energy** `−2⟨A⟩ − 2⟨B_A⟩ f(θ₂) − 2⟨B_B⟩ g(ψ₂)`. -/
noncomputable def twoCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (p : EchoSigma N) :
    ℝ :=
  coupledEnergy A BA hf p.1 + schrodingerHamiltonian BB p.1.1 * torusPotential hg p.2

theorem twoCoupledEnergy_eq (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) :
    twoCoupledEnergy A BA BB hf hg
      = (fun p : EchoSigma N => coupledEnergy A BA hf p.1)
        + fun p : EchoSigma N => schrodingerHamiltonian BB p.1.1 * torusPotential hg p.2 := rfl

/-- The outer coupled term `−2⟨B_B⟩ g(ψ₂)` is `C^∞` on the echo arena. -/
theorem contMDiff_outerTerm (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) ∞
      (fun p : EchoSigma N => schrodingerHamiltonian BB p.1.1 * torusPotential hg p.2) :=
  ((contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) BB)).comp
    (Prod.contMDiff_fst_self (E := ArenaModel N) (F := ℝ × ℝ) (M := KSigma (N + 1))
      (N := KTorus))).mul
    ((contMDiff_torusPotential hg hcg).comp
      (Prod.contMDiff_snd_self (E := ArenaModel N) (F := ℝ × ℝ) (M := KSigma (N + 1))
        (N := KTorus)))

/-- The two-torus energy is `C^∞` on the echo arena. -/
theorem contMDiff_twoCoupledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ) ∞ (twoCoupledEnergy A BA BB hf hg) := by
  rw [twoCoupledEnergy_eq]
  exact ((contMDiff_coupledEnergy A BA hf hc).comp
    (Prod.contMDiff_fst_self (E := ArenaModel N) (F := ℝ × ℝ) (M := KSigma (N + 1))
      (N := KTorus))).add (contMDiff_outerTerm BB hg hcg)

/-- **The two-torus field**: the one-torus coupled field on the arena factor plus `g(ψ₂) X_{B_B}`
on the ray, and `(−2⟨B_B⟩ g'(ψ₂), 0)` on the outer torus. -/
noncomputable def twoCoupledField (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (p : EchoSigma N) :
    TangentSpace 𝓘(ℝ, EchoModel N) p :=
  (((schrodingerField A p.1.1 + torusPotential hf p.1.2 • schrodingerField BA p.1.1
        + torusPotential hg p.2 • schrodingerField BB p.1.1,
      ((schrodingerHamiltonian BA p.1.1 * hf.deriv_periodic.lift p.1.2.2, 0) : ℝ × ℝ)),
    ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
    TangentSpace 𝓘(ℝ, EchoModel N) p)

/-- ★ **The outer coupled term**: `ι_X ω = d(−2⟨B_B⟩ g(ψ₂))` on the echo arena for
`X = ((g(ψ₂) X_{B_B}, 0), (−2⟨B_B⟩ g'(ψ₂), 0))`. -/
theorem isHamiltonianVectorField_outerTerm {BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hBB : BB.IsHermitian) (hg : Function.Periodic g 1) (hd : Differentiable ℝ g) :
    IsHamiltonianVectorField (fun p => echoForm N p)
      (fun p : EchoSigma N =>
        ((((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)) : ArenaModel N),
          ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, EchoModel N) p))
      (fun p => schrodingerHamiltonian BB p.1.1 * torusPotential hg p.2) := by
  intro p v
  have hfst : HasMFDerivAt 𝓘(ℝ, EchoModel N) 𝓘(ℝ, Fin N → ℂ)
      (fun q : EchoSigma N => q.1.1) p
      ((ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ)).comp
        (ContinuousLinearMap.fst ℝ (ArenaModel N) (ℝ × ℝ))) :=
    (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p.1).comp p
      (Prod.hasMFDerivAt_fst_self (E := ArenaModel N) (F := ℝ × ℝ) p)
  have ha := (mdifferentiableAt_schrodingerHamiltonian BB p.1.1).hasMFDerivAt.comp p hfst
  have hb := (hasMFDerivAt_torusPotential hg hd p.2).comp p
    (Prod.hasMFDerivAt_snd_self (E := ArenaModel N) (F := ℝ × ℝ) p)
  have hprod : HasMFDerivAt 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ)
      (fun q : EchoSigma N => schrodingerHamiltonian BB q.1.1 * torusPotential hg q.2) p _ :=
    ha.mul hb
  beta_reduce
  rw [hprod.mfderiv]
  have hX := schrodingerField_isHamiltonianVectorField hBB p.1.1 (v : EchoModel N).1.1
  have h1 : (echoForm N p)
      ![((((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)) : ArenaModel N),
          ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, EchoModel N) p), v]
      = toFlat (arenaForm N p.1)
          ![((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)) : ArenaModel N),
            (v : EchoModel N).1]
        + TorusForm.areaForm
          ![((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ),
            (v : EchoModel N).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (arenaForm N p.1)) TorusForm.areaForm _ _
  rw [h1]
  have h2 : toFlat (arenaForm N p.1)
      ![((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)) : ArenaModel N),
        (v : EchoModel N).1]
      = toFlat (fsForm (n := N) p.1.1)
          ![torusPotential hg p.2 • schrodingerField BB p.1.1, (v : EchoModel N).1.1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : EchoModel N).1.2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := N) p.1.1)) TorusForm.areaForm _ _
  have hz : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : EchoModel N).1.2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h3 : toFlat (fsForm (n := N) p.1.1)
      ![torusPotential hg p.2 • schrodingerField BB p.1.1, (v : EchoModel N).1.1]
      = torusPotential hg p.2 * toFlat (fsForm (n := N) p.1.1)
          ![schrodingerField BB p.1.1, (v : EchoModel N).1.1] :=
    apply_smul_left (fun x : CPN (N + 1) => fsForm (n := N) x) p.1.1 _ _ _
  have h4 : toFlat (fsForm (n := N) p.1.1) ![schrodingerField BB p.1.1, (v : EchoModel N).1.1]
      = mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian BB) p.1.1 (v : EchoModel N).1.1 :=
    hX
  rw [h2, hz, add_zero, h3, h4, TorusForm.areaForm_apply]
  set D : ℝ := mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian BB) p.1.1
    (v : EchoModel N).1.1 with hD
  show torusPotential hg p.2 * D
      + (schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2 * (v : EchoModel N).2.2
        - 0 * (v : EchoModel N).2.1)
    = schrodingerHamiltonian BB p.1.1 * ((v : EchoModel N).2.2 * hg.deriv_periodic.lift p.2.2)
      + torusPotential hg p.2 * D
  ring

/-- ★★ **`ι_X ω = d𝓗` on `ℂℙᴺ × T² × T²` for the two-torus energy.** -/
theorem isHamiltonianVectorField_twoCoupled {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    IsHamiltonianVectorField (fun p => echoForm N p) (twoCoupledField A BA BB hf hg)
      (twoCoupledEnergy A BA BB hf hg) := by
  have hL := isHamiltonianVectorField_fstLift (contMDiff_coupledEnergy A BA hf hc)
    (isHamiltonianVectorField_coupled hA hBA hf (hc.differentiable (by simp)))
  have hO := isHamiltonianVectorField_outerTerm hBB hg (hcg.differentiable (by simp))
  have hdiffL : ∀ p : EchoSigma N, MDifferentiableAt 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ)
      (fun p : EchoSigma N => coupledEnergy A BA hf p.1) p := fun p =>
    (((contMDiff_coupledEnergy A BA hf hc).comp
      (Prod.contMDiff_fst_self (E := ArenaModel N) (F := ℝ × ℝ) (M := KSigma (N + 1))
        (N := KTorus))) p).mdifferentiableAt (by simp)
  have hdiffO : ∀ p : EchoSigma N, MDifferentiableAt 𝓘(ℝ, EchoModel N) 𝓘(ℝ, ℝ)
      (fun p : EchoSigma N => schrodingerHamiltonian BB p.1.1 * torusPotential hg p.2) p :=
    fun p => (contMDiff_outerTerm BB hg hcg p).mdifferentiableAt (by simp)
  have hfield : twoCoupledField A BA BB hf hg = fun p : EchoSigma N =>
      ((coupledField A BA hf p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, EchoModel N) p)
        + ((((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)) : ArenaModel N),
          ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, EchoModel N) p) := by
    funext p
    show (((schrodingerField A p.1.1 + torusPotential hf p.1.2 • schrodingerField BA p.1.1
          + torusPotential hg p.2 • schrodingerField BB p.1.1,
        ((schrodingerHamiltonian BA p.1.1 * hf.deriv_periodic.lift p.1.2.2, 0) : ℝ × ℝ)),
      ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) : EchoModel N)
      = ((schrodingerField A p.1.1 + torusPotential hf p.1.2 • schrodingerField BA p.1.1,
          ((schrodingerHamiltonian BA p.1.1 * hf.deriv_periodic.lift p.1.2.2, 0) : ℝ × ℝ)),
          (0 : ℝ × ℝ))
        + ((torusPotential hg p.2 • schrodingerField BB p.1.1, (0 : ℝ × ℝ)),
          ((schrodingerHamiltonian BB p.1.1 * hg.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ))
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  rw [hfield, twoCoupledEnergy_eq]
  exact hL.add hO hdiffL hdiffO

/-- **`X_𝓗 = twoCoupledField`** (uniqueness for the symplectic `echoForm`). -/
theorem twoCoupledField_eq_hamiltonianVectorField {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    twoCoupledField A BA BB hf hg
      = (echoForm_isSymplectic N).hamiltonianVectorField (twoCoupledEnergy A BA BB hf hg) :=
  (isHamiltonianVectorField_twoCoupled hA hBA hBB hf hg hc hcg).eq_isSymplectic_hamiltonianVectorField
    (echoForm_isSymplectic N)

/-! ### The flow in closed form -/

/-- The state-dependent matrix at angles `(φ, ψ)`: `A + f(φ) B_A + g(ψ) B_B`. -/
noncomputable def twoCoupledMatrix (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (φ ψ : AddCircle (1 : ℝ)) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  coupledMatrix A BA hf φ + ((hg.lift ψ : ℝ) : ℂ) • BB

theorem twoCoupledMatrix_isHermitian {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ)) :
    (twoCoupledMatrix A BA BB hf hg φ ψ).IsHermitian :=
  isHermitian_add_real_smul (coupledMatrix_isHermitian hA hBA hf φ) hBB _

variable {A BA BB}

/-- The Schrödinger field of the two-angle matrix is the combination of the three fields. -/
theorem schrodingerField_twoCoupledMatrix (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (φ ψ : AddCircle (1 : ℝ)) (y : CPN (N + 1)) :
    schrodingerField (twoCoupledMatrix A BA BB hf hg φ ψ) y
      = schrodingerField A y + hf.lift φ • schrodingerField BA y
        + hg.lift ψ • schrodingerField BB y := by
  rw [twoCoupledMatrix, schrodingerField_add_real_smul (coupledMatrix_isHermitian hA hBA hf φ) hBB,
    schrodingerField_coupledMatrix hA hBA]

/-- The two-angle Schrödinger orbit from `x`, as a continuous curve. -/
theorem continuous_twoCoupledOrbit (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) :
    Continuous fun s : ℝ =>
      Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s • x := by
  have hU : Continuous fun s : ℝ =>
      Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s :=
    continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun s =>
      (Matrix.schrodingerUnitary_hasDerivAt (twoCoupledMatrix A BA BB hf hg φ ψ)
        (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s).continuousAt)
  exact hU.smul continuous_const

theorem continuous_schrodingerHamiltonian_twoCoupledOrbit (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) :
    Continuous fun s : ℝ => schrodingerHamiltonian C
      (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s • x) := by
  have h := (continuous_schrodingerHamiltonian C).comp
    (continuous_twoCoupledOrbit hA hBA hBB hf hg φ ψ x)
  simpa only [Function.comp_def] using h

/-- **The accumulated `−2⟨B_A⟩`** along the two-angle orbit. -/
noncomputable def twoAccumA (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, schrodingerHamiltonian BA
    (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s • x)

/-- **The accumulated `−2⟨B_B⟩`** along the two-angle orbit. -/
noncomputable def twoAccumB (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, schrodingerHamiltonian BB
    (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) s • x)

theorem twoAccumA_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) : twoAccumA hA hBA hBB hf hg φ ψ x 0 = 0 :=
  intervalIntegral.integral_same

theorem twoAccumB_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) : twoAccumB hA hBA hBB hf hg φ ψ x 0 = 0 :=
  intervalIntegral.integral_same

theorem hasDerivAt_twoAccumA (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) (t : ℝ) :
    HasDerivAt (fun t => twoAccumA hA hBA hBB hf hg φ ψ x t)
      (schrodingerHamiltonian BA
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)) t := by
  unfold twoAccumA
  have hc := continuous_schrodingerHamiltonian_twoCoupledOrbit BA hA hBA hBB hf hg φ ψ x
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt

theorem hasDerivAt_twoAccumB (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ))
    (x : CPN (N + 1)) (t : ℝ) :
    HasDerivAt (fun t => twoAccumB hA hBA hBB hf hg φ ψ x t)
      (schrodingerHamiltonian BB
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)) t := by
  unfold twoAccumB
  have hc := continuous_schrodingerHamiltonian_twoCoupledOrbit BB hA hBA hBB hf hg φ ψ x
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt

/-- **The closed-form curve**: the two-angle orbit, `θ₁ = a₀ + f'(φ) ∫ (−2⟨B_A⟩)`, `θ₂ = φ`,
`ψ₁ = b₀ + g'(ψ) ∫ (−2⟨B_B⟩)`, `ψ₂ = ψ`. -/
noncomputable def twoCoupledCurve (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (x : CPN (N + 1)) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (b₀ : ℝ) (ψ : AddCircle (1 : ℝ)) (t : ℝ) : EchoSigma N :=
  ((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x,
    (((a₀ + hf.deriv_periodic.lift φ * twoAccumA hA hBA hBB hf hg φ ψ x t : ℝ) :
      AddCircle (1 : ℝ)), φ)),
   (((b₀ + hg.deriv_periodic.lift ψ * twoAccumB hA hBA hBB hf hg φ ψ x t : ℝ) :
      AddCircle (1 : ℝ)), ψ))

/-- ★★ **The closed-form curve is an integral curve of the two-torus field.** -/
theorem isMIntegralCurve_twoCoupledCurve (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ))
    (b₀ : ℝ) (ψ : AddCircle (1 : ℝ)) :
    IsMIntegralCurve (twoCoupledCurve hA hBA hBB hf hg x a₀ φ b₀ ψ)
      ((echoForm_isSymplectic N).hamiltonianVectorField (twoCoupledEnergy A BA BB hf hg)) := by
  rw [← twoCoupledField_eq_hamiltonianVectorField hA hBA hBB hf hg hc hcg]
  intro t
  have hray := isMIntegralCurve_schrodingerUnitary_smul
    (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) x t
  have hθ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => (((a₀ + hf.deriv_periodic.lift φ * twoAccumA hA hBA hBB hf hg φ ψ x u : ℝ) :
        AddCircle (1 : ℝ)))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift φ * schrodingerHamiltonian BA
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x))) :=
    AddCircle.hasMFDerivAt_coe_comp
      (((hasDerivAt_twoAccumA hA hBA hBB hf hg φ ψ x t).const_mul _).const_add a₀)
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
  rw [schrodingerField_twoCoupledMatrix hA hBA hBB] at hray
  have h := (hray.prodMk_self (hθ₁.prodMk_self hθ₂)).prodMk_self (hψ₁.prodMk_self hψ₂)
  refine h.congr_deriv ?_
  refine ContinuousLinearMap.ext fun s => Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ ?_)
  · rfl
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hf.deriv_periodic.lift φ * schrodingerHamiltonian BA
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian BA
        (Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ) t • x)
          * hf.deriv_periodic.lift φ)
    rw [mul_comm]
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

/-- ★★★ **The Hamiltonian flow of the two-torus energy in closed form**: the Schrödinger unitary of
`A + f(θ₂) B_A + g(ψ₂) B_B` on the ray, `θ₁` advanced by `f'(θ₂) ∫ (−2⟨B_A⟩)`, `ψ₁` by
`g'(ψ₂) ∫ (−2⟨B_B⟩)`, both second angles fixed — a skew product over the two conserved angles. -/
theorem hamiltonianFlow_twoCoupledEnergy (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus) :
    (echoForm_isSymplectic N).hamiltonianFlow (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg) t
        ((x, θ), ψ)
      = ((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) t • x,
          (θ.1 + ((hf.deriv_periodic.lift θ.2 * twoAccumA hA hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), θ.2)),
         (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * twoAccumB hA hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)) := by
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk_surjective θ.1
  obtain ⟨b₀, hb₀⟩ := QuotientAddGroup.mk_surjective ψ.1
  have hγ := isMIntegralCurve_twoCoupledCurve hA hBA hBB hf hg hc hcg x a₀ θ.2 b₀ ψ.2
  have h0 : twoCoupledCurve hA hBA hBB hf hg x a₀ θ.2 b₀ ψ.2 0 = ((x, θ), ψ) := by
    unfold twoCoupledCurve
    rw [(Matrix.expNegITH_unitary_group (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2)).2,
      one_smul, twoAccumA_zero, twoAccumB_zero, mul_zero, mul_zero, add_zero, add_zero, ha₀, hb₀]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((echoForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg)) hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t]
  unfold twoCoupledCurve
  rw [AddCircle.coe_add, AddCircle.coe_add, ha₀, hb₀]

end Energy

end LF4
end CSD

end
