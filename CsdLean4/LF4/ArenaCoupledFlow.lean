/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaSymplectic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.AddCirclePeriodicLift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# A sector energy coupled to a torus angle: the Hamiltonian flow on the arena

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 3-Local (the corpus's arena, assembled from Category-1 pieces). BACKLOG #195.

`ArenaSymplectic.lean` handles energies of one factor: a sector energy's flow is the sector's flow
with the torus fixed. This module handles the first energy **coupling the two factors**,

  `𝓗(x, θ) = −2⟨A⟩(x) − 2⟨B⟩(x) · f(θ₂)`,   `A, B` Hermitian, `f` smooth of period `1`,

the arena form being `π₁^* ω_FS + π₂^* (dθ₁ ∧ dθ₂)`. Hamilton's equations split as the row says:
at fixed `θ₂` the ray sees the **state-dependent** Hermitian matrix `A + f(θ₂) B`, so it runs that
Schrödinger unitary; `θ₂` is conserved (`𝓗` does not depend on `θ₁`); and `θ₁` moves at the rate
`−2⟨B⟩(x) f'(θ₂)` — only while `⟨B⟩` is nonzero on the orbit. The flow is a skew product, in closed
form.

* `expectation_add`, `expectation_real_smul`, `schrodingerHamiltonian_add`,
  `schrodingerHamiltonian_real_smul`, ★ `schrodingerField_add_real_smul` — **the Schrödinger field
  is linear in the matrix**, by uniqueness of Hamiltonian vector fields for the symplectic
  Fubini–Study form;
* `torusPotential`, ★ `isHamiltonianVectorField_torusPotential` — **the Hamiltonian vector field
  of `f(θ₂)` for the area form is `(f'(θ₂), 0)`**, from the periodic-lift calculus of
  `AddCirclePeriodicLift.lean`;
* `coupledEnergy`, `coupledField`, ★★ `isHamiltonianVectorField_coupled` — **`ι_X ω = d𝓗` on the
  arena for the coupled energy**, with `X = (X_A + f(θ₂) X_B, (−2⟨B⟩ f'(θ₂), 0))`; this is the
  coupled product field the row was stuck on, obtained from the product rule for `mfderiv` and the
  factorwise pairing `prodSum_pair`; `coupledField_eq_hamiltonianVectorField`;
* `coupledMatrix`, `coupledAccum`, `coupledCurve`, ★★ `isMIntegralCurve_coupledCurve` — **the
  closed-form curve is an integral curve**: the detuned Schrödinger orbit, `θ₁` advanced by
  `f'(θ₂) ∫₀ᵗ (−2⟨B⟩)` along it, `θ₂` fixed;
* ★★★ `hamiltonianFlow_coupledEnergy` — **the Hamiltonian flow of the coupled energy in closed
  form**, by uniqueness of integral curves on the compact arena;
* ★ `arenaVolume_map_coupledFlow` — Liouville for it, read off the explicit map.

## Honest scope

* The sector is `ℂℙᴺ` with Mathlib's `Fin (N+1)` index; the record layer's field arenas reach it
  through the index bridge (`CV/ArenaIndexBridge.lean`), which is where #194's flow is identified
  with this one (`RecordLayer/ActivatedHamiltonian.lean`).
* The normalisation is the corpus's: with this Fubini–Study form the Schrödinger unitary of `H` is
  the flow of `−2⟨H⟩` (`hamiltonianFlow_schrodingerHamiltonian`), so the coupled term carries the
  same `−2`, and the pointer rate is `−2⟨B⟩ f'(θ₂)`. No other normalisation is claimed.
* `f` is `C^∞` where the flow is taken (the Hamiltonian must be smooth for the flow machinery);
  `C^1` suffices for the vector-field identity.

References: `LF4/ArenaSymplectic.lean` (`arenaForm`, `sectorEnergy`,
`isHamiltonianVectorField_sectorEnergy`, `hamiltonianFlow_sectorEnergy`);
`Geometry/Manifold/Instances/ProjectiveSpaceSchrodingerFlow.lean` (`schrodingerField`,
`schrodingerField_isHamiltonianVectorField`, `isMIntegralCurve_schrodingerUnitary_smul`);
`Geometry/Manifold/Instances/AddCirclePeriodicLift.lean`; `Geometry/Manifold/ProductForm.lean`
(`prodSum_pair`); `Geometry/Manifold/IntegralCurve/GlobalFlow.lean`
(`integralFlow_eq_of_isMIntegralCurve`); `specs/BACKLOG.md` #195, #194.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### Linearity of the Schrödinger Hamiltonian and field in the matrix -/

theorem expectation_add (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : CPN (N + 1)) :
    expectation (A + B) p = expectation A p + expectation B p := by
  unfold expectation
  rw [map_add, LinearMap.add_apply, inner_add_right, Complex.add_re, add_div]

theorem expectation_real_smul (c : ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : CPN (N + 1)) :
    expectation ((c : ℂ) • A) p = c * expectation A p := by
  unfold expectation
  rw [map_smul, LinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul, mul_div_assoc]

theorem schrodingerHamiltonian_add (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    schrodingerHamiltonian (A + B)
      = schrodingerHamiltonian (n := N) A + schrodingerHamiltonian B := by
  funext p
  simp only [schrodingerHamiltonian, Pi.add_apply, expectation_add]
  ring

theorem schrodingerHamiltonian_real_smul (c : ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    schrodingerHamiltonian ((c : ℂ) • A) = c • schrodingerHamiltonian (n := N) A := by
  funext p
  simp only [schrodingerHamiltonian, Pi.smul_apply, expectation_real_smul, smul_eq_mul]
  ring

theorem mdifferentiableAt_schrodingerHamiltonian (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (x : CPN (N + 1)) :
    MDifferentiableAt 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian A) x :=
  (contMDiff_schrodingerHamiltonian (m := ∞) A x).mdifferentiableAt (by simp)

theorem isHermitian_add_real_smul {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ) : (A + (c : ℂ) • B).IsHermitian :=
  hA.add (hB.smul (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal])))

/-- ★ **The Schrödinger field is linear in the matrix**: the field of `A + c B` is the combination
of the fields, by uniqueness of Hamiltonian vector fields for the symplectic `fsForm`. -/
theorem schrodingerField_add_real_smul {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ) (x : CPN (N + 1)) :
    schrodingerField (A + (c : ℂ) • B) x = schrodingerField A x + c • schrodingerField B x := by
  have h1 := schrodingerField_isHamiltonianVectorField (isHermitian_add_real_smul hA hB c)
  have h2 : IsHamiltonianVectorField (fun y : CPN (N + 1) => fsForm (n := N) y)
      (fun y => schrodingerField A y + c • schrodingerField B y)
      (schrodingerHamiltonian (A + (c : ℂ) • B)) := by
    rw [schrodingerHamiltonian_add, schrodingerHamiltonian_real_smul]
    exact (schrodingerField_isHamiltonianVectorField hA).add
      ((schrodingerField_isHamiltonianVectorField hB).smul c
        (mdifferentiableAt_schrodingerHamiltonian B))
      (mdifferentiableAt_schrodingerHamiltonian A)
      (fun y => (mdifferentiableAt_schrodingerHamiltonian B y).const_smul c)
  exact h1.eq_of_nondegenerate h2 x ((fsForm_isSymplectic N).nondegenerate x)

/-! ### The torus potential `f(θ₂)` and its Hamiltonian vector field -/

variable {f : ℝ → ℝ}

/-- The second torus angle read through a periodic potential. -/
def torusPotential (hf : Function.Periodic f 1) (θ : KTorus) : ℝ := hf.lift θ.2

theorem hasMFDerivAt_torusPotential (hf : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (θ : KTorus) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (torusPotential hf) θ
      (((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift θ.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) :=
  (hf.hasMFDerivAt_lift hd θ.2).comp θ
    (Prod.hasMFDerivAt_snd_self (E := ℝ) (F := ℝ) (M := AddCircle (1 : ℝ))
      (N := AddCircle (1 : ℝ)) θ)

theorem contMDiff_torusPotential (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (torusPotential hf) :=
  (hf.contMDiff_lift hc).comp
    (Prod.contMDiff_snd_self (E := ℝ) (F := ℝ) (M := AddCircle (1 : ℝ)) (N := AddCircle (1 : ℝ)))

/-- ★ **The Hamiltonian vector field of `f(θ₂)` for the area form `dθ₁ ∧ dθ₂` is `(f'(θ₂), 0)`.** -/
theorem isHamiltonianVectorField_torusPotential (hf : Function.Periodic f 1)
    (hd : Differentiable ℝ f) :
    IsHamiltonianVectorField (fun θ : KTorus => AddCircle.torusAreaForm (T := 1) (T' := 1) θ)
      (fun θ => ((hf.deriv_periodic.lift θ.2, 0) : TangentSpace 𝓘(ℝ, ℝ × ℝ) θ))
      (torusPotential hf) := by
  intro θ v
  rw [(hasMFDerivAt_torusPotential hf hd θ).mfderiv]
  show TorusForm.areaForm ![((hf.deriv_periodic.lift θ.2, 0) : ℝ × ℝ), (v : ℝ × ℝ)]
    = (v : ℝ × ℝ).2 * hf.deriv_periodic.lift θ.2
  rw [TorusForm.areaForm_apply]
  show TorusForm.area ((hf.deriv_periodic.lift θ.2, 0) : ℝ × ℝ) (v : ℝ × ℝ)
    = (v : ℝ × ℝ).2 * hf.deriv_periodic.lift θ.2
  unfold TorusForm.area
  ring

/-! ### The coupled energy and its Hamiltonian vector field -/

variable (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **The coupled energy** `−2⟨A⟩(x) − 2⟨B⟩(x) f(θ₂)` on the arena. -/
def coupledEnergy (hf : Function.Periodic f 1) (p : KSigma (N + 1)) : ℝ :=
  schrodingerHamiltonian A p.1 + schrodingerHamiltonian B p.1 * torusPotential hf p.2

theorem coupledEnergy_eq (hf : Function.Periodic f 1) :
    coupledEnergy A B hf
      = sectorEnergy (schrodingerHamiltonian A)
        + fun p : KSigma (N + 1) => schrodingerHamiltonian B p.1 * torusPotential hf p.2 :=
  rfl

theorem contMDiff_torusPotential_snd (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ (fun p : KSigma (N + 1) => torusPotential hf p.2) :=
  (contMDiff_torusPotential hf hc).comp
    (Prod.contMDiff_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) (M := CPN (N + 1)) (N := KTorus))

/-- The coupled energy is `C^∞` on the arena. -/
theorem contMDiff_coupledEnergy (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ (coupledEnergy A B hf) := by
  rw [coupledEnergy_eq]
  exact (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) A)).add
    ((contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) B)).mul
      (contMDiff_torusPotential_snd (N := N) hf hc))

/-- **The coupled field** `(X_A + f(θ₂) X_B, (−2⟨B⟩ f'(θ₂), 0))`. -/
def coupledField (hf : Function.Periodic f 1) (p : KSigma (N + 1)) :
    TangentSpace 𝓘(ℝ, ArenaModel N) p :=
  ((schrodingerField A p.1 + torusPotential hf p.2 • schrodingerField B p.1,
    ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
    TangentSpace 𝓘(ℝ, ArenaModel N) p)

/-- The coupled term alone: `ι_X ω = d (−2⟨B⟩ · f(θ₂))` on the arena for
`X = (f(θ₂) X_B, (−2⟨B⟩ f'(θ₂), 0))`. -/
theorem isHamiltonianVectorField_coupledTerm {B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hB : B.IsHermitian) (hf : Function.Periodic f 1) (hd : Differentiable ℝ f) :
    IsHamiltonianVectorField (fun p => arenaForm N p)
      (fun p : KSigma (N + 1) =>
        ((torusPotential hf p.2 • schrodingerField B p.1,
          ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, ArenaModel N) p))
      (fun p => schrodingerHamiltonian B p.1 * torusPotential hf p.2) := by
  intro p v
  have ha : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian B q.1) p
      ((mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1).comp
        (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (mdifferentiableAt_schrodingerHamiltonian B p.1).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have hb : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => torusPotential hf q.2) p
      ((((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift p.2.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (hasMFDerivAt_torusPotential hf hd p.2).comp p
      (Prod.hasMFDerivAt_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have hprod : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian B q.1 * torusPotential hf q.2) p _ :=
    ha.mul hb
  beta_reduce
  rw [hprod.mfderiv]
  have hX := schrodingerField_isHamiltonianVectorField hB p.1 (v : ArenaModel N).1
  have h1 : (arenaForm N p) ![((torusPotential hf p.2 • schrodingerField B p.1,
      ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
        TangentSpace 𝓘(ℝ, ArenaModel N) p), v]
      = toFlat (fsForm (n := N) p.1)
          ![torusPotential hf p.2 • schrodingerField B p.1, (v : ArenaModel N).1]
        + TorusForm.areaForm
          ![((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ),
            (v : ArenaModel N).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm _ _
  rw [h1]
  have h2 : toFlat (fsForm (n := N) p.1)
      ![torusPotential hf p.2 • schrodingerField B p.1, (v : ArenaModel N).1]
      = torusPotential hf p.2 * toFlat (fsForm (n := N) p.1)
          ![schrodingerField B p.1, (v : ArenaModel N).1] :=
    apply_smul_left (fun x : CPN (N + 1) => fsForm (n := N) x) p.1 _ _ _
  rw [h2]
  have h3 : toFlat (fsForm (n := N) p.1) ![schrodingerField B p.1, (v : ArenaModel N).1]
      = mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1 (v : ArenaModel N).1 := hX
  rw [h3, TorusForm.areaForm_apply]
  set D : ℝ := mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1 (v : ArenaModel N).1
    with hD
  show torusPotential hf p.2 * D
      + (schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2 * (v : ArenaModel N).2.2
        - 0 * (v : ArenaModel N).2.1)
    = schrodingerHamiltonian B p.1 * ((v : ArenaModel N).2.2 * hf.deriv_periodic.lift p.2.2)
      + torusPotential hf p.2 * D
  ring

/-- ★★ **`ι_X ω = d𝓗` on the arena for the coupled energy.** The coupled product field the row was
stuck on: the sector energy's field with the torus fixed, plus the coupled term's field. -/
theorem isHamiltonianVectorField_coupled {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (hd : Differentiable ℝ f) :
    IsHamiltonianVectorField (fun p => arenaForm N p) (coupledField A B hf)
      (coupledEnergy A B hf) := by
  have hS := isHamiltonianVectorField_sectorEnergy (contMDiff_schrodingerHamiltonian A)
    (schrodingerField_isHamiltonianVectorField hA)
  have hC := isHamiltonianVectorField_coupledTerm hB hf hd
  have hdiffS : ∀ p : KSigma (N + 1), MDifferentiableAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (sectorEnergy (schrodingerHamiltonian A)) p := fun p =>
    (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) A) p).mdifferentiableAt
      (by simp)
  have hdiffC : ∀ p : KSigma (N + 1), MDifferentiableAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun p : KSigma (N + 1) => schrodingerHamiltonian B p.1 * torusPotential hf p.2) p := by
    intro p
    have ha : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
        (fun q : KSigma (N + 1) => schrodingerHamiltonian B q.1) p
        ((mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1).comp
          (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
      (mdifferentiableAt_schrodingerHamiltonian B p.1).hasMFDerivAt.comp p
        (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
    have hb : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
        (fun q : KSigma (N + 1) => torusPotential hf q.2) p
        ((((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift p.2.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
      (hasMFDerivAt_torusPotential hf hd p.2).comp p
        (Prod.hasMFDerivAt_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
    exact (ha.mul hb).mdifferentiableAt
  have hfield : coupledField A B hf = fun p : KSigma (N + 1) =>
      ((schrodingerField A p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, ArenaModel N) p)
        + ((torusPotential hf p.2 • schrodingerField B p.1,
          ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, ArenaModel N) p) := by
    funext p
    show ((schrodingerField A p.1 + torusPotential hf p.2 • schrodingerField B p.1,
      ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ)) : ArenaModel N)
      = (schrodingerField A p.1, (0 : ℝ × ℝ))
        + (torusPotential hf p.2 • schrodingerField B p.1,
          ((schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2, 0) : ℝ × ℝ))
    rw [Prod.mk_add_mk, zero_add]
    rfl
  rw [hfield, coupledEnergy_eq]
  exact hS.add hC hdiffS hdiffC

/-- **`X_𝓗 = coupledField`**: the Hamiltonian vector field of the coupled energy is the coupled
field (uniqueness for the symplectic `arenaForm`). -/
theorem coupledField_eq_hamiltonianVectorField {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (hd : Differentiable ℝ f) :
    coupledField A B hf
      = (arenaForm_isSymplectic N).hamiltonianVectorField (coupledEnergy A B hf) :=
  (isHamiltonianVectorField_coupled hA hB hf hd).eq_isSymplectic_hamiltonianVectorField
    (arenaForm_isSymplectic N)

/-! ### The flow in closed form -/

/-- The state-dependent matrix at angle `φ`: `A + f(φ) B`. -/
def coupledMatrix (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  A + ((hf.lift φ : ℝ) : ℂ) • B

theorem coupledMatrix_isHermitian {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) : (coupledMatrix A B hf φ).IsHermitian :=
  isHermitian_add_real_smul hA hB _

variable {A B}

/-- The Schrödinger field of the state-dependent matrix is the combination of the fields. -/
theorem schrodingerField_coupledMatrix (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (y : CPN (N + 1)) :
    schrodingerField (coupledMatrix A B hf φ) y
      = schrodingerField A y + hf.lift φ • schrodingerField B y :=
  schrodingerField_add_real_smul hA hB _ y

/-- The detuned Schrödinger orbit from `x` at angle `φ`, as a continuous curve. -/
theorem continuous_coupledOrbit (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) :
    Continuous fun s : ℝ =>
      Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) s • x := by
  have hU : Continuous fun s : ℝ => Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) s :=
    continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun s =>
      (Matrix.schrodingerUnitary_hasDerivAt (coupledMatrix A B hf φ)
        (coupledMatrix_isHermitian hA hB hf φ) s).continuousAt)
  exact hU.smul continuous_const

/-- The integrand `−2⟨B⟩` along the orbit is continuous. -/
theorem continuous_schrodingerHamiltonian_coupledOrbit (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) :
    Continuous fun s : ℝ => schrodingerHamiltonian B
      (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) s • x) := by
  have h := (continuous_schrodingerHamiltonian B).comp (continuous_coupledOrbit hA hB hf φ x)
  simpa only [Function.comp_def] using h

/-- **The accumulated `−2⟨B⟩`** along the detuned orbit. -/
def coupledAccum (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, schrodingerHamiltonian B
    (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) s • x)

theorem coupledAccum_zero (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) : coupledAccum hA hB hf φ x 0 = 0 :=
  intervalIntegral.integral_same

theorem hasDerivAt_coupledAccum (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) (t : ℝ) :
    HasDerivAt (fun t => coupledAccum hA hB hf φ x t)
      (schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x)) t := by
  unfold coupledAccum
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_schrodingerHamiltonian_coupledOrbit hA hB hf φ x).intervalIntegrable 0 t)
    ((continuous_schrodingerHamiltonian_coupledOrbit hA hB hf φ x).stronglyMeasurableAtFilter
      volume _)
    (continuous_schrodingerHamiltonian_coupledOrbit hA hB hf φ x).continuousAt

/-- **The closed-form curve**: the detuned orbit, `θ₁ = a₀ + f'(φ) ∫₀ᵗ (−2⟨B⟩)`, `θ₂ = φ`. -/
def coupledCurve (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) : KSigma (N + 1) :=
  (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x,
    (((a₀ + hf.deriv_periodic.lift φ * coupledAccum hA hB hf φ x t : ℝ) : AddCircle (1 : ℝ)), φ))

/-- ★★ **The closed-form curve is an integral curve of the coupled field.** -/
theorem isMIntegralCurve_coupledCurve (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hd : Differentiable ℝ f) (x : CPN (N + 1)) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) :
    IsMIntegralCurve (coupledCurve hA hB hf x a₀ φ)
      ((arenaForm_isSymplectic N).hamiltonianVectorField (coupledEnergy A B hf)) := by
  rw [← coupledField_eq_hamiltonianVectorField hA hB hf hd]
  intro t
  have hray := isMIntegralCurve_schrodingerUnitary_smul (coupledMatrix_isHermitian hA hB hf φ) x t
  have hθ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => (((a₀ + hf.deriv_periodic.lift φ * coupledAccum hA hB hf φ x u : ℝ) :
        AddCircle (1 : ℝ)))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift φ * schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x))) :=
    AddCircle.hasMFDerivAt_coe_comp
      (((hasDerivAt_coupledAccum hA hB hf φ x t).const_mul _).const_add a₀)
  have hθ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => φ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) φ) :=
    hasMFDerivAt_const φ t
  rw [schrodingerField_coupledMatrix hA hB] at hray
  have h := hray.prodMk_self (hθ₁.prodMk_self hθ₂)
  refine h.congr_deriv ?_
  refine ContinuousLinearMap.ext fun s => Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hf.deriv_periodic.lift φ * schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x)
          * hf.deriv_periodic.lift φ)
    rw [mul_comm]
  · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) s) • (0 : ℝ)
    rw [smul_zero]

/-- ★★★ **The Hamiltonian flow of the coupled energy in closed form.** At `(x, θ)` the flow for
time `t` is the Schrödinger unitary of `A + f(θ₂) B` on the sector, the angle `θ₁` advanced by
`f'(θ₂) ∫₀ᵗ (−2⟨B⟩)` along that orbit, and `θ₂` unchanged — a skew product over the conserved
angle, by uniqueness of integral curves on the compact arena. -/
theorem hamiltonianFlow_coupledEnergy (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : CPN (N + 1)) (θ : KTorus) :
    (arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A B hf hc) t (x, θ)
      = (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf θ.2) t • x,
          (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), θ.2)) := by
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk_surjective θ.1
  have hγ := isMIntegralCurve_coupledCurve hA hB hf (hc.differentiable (by simp)) x a₀ θ.2
  have h0 : coupledCurve hA hB hf x a₀ θ.2 0 = (x, θ) := by
    unfold coupledCurve
    rw [(Matrix.expNegITH_unitary_group (coupledMatrix_isHermitian hA hB hf θ.2)).2, one_smul,
      coupledAccum_zero, mul_zero, add_zero, ha₀]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_coupledEnergy A B hf hc)) hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t]
  unfold coupledCurve
  rw [AddCircle.coe_add, ha₀]

/-- ★ **Liouville for the coupled flow**, read off the explicit map. -/
theorem arenaVolume_map_coupledFlow (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measure.map (fun p : KSigma (N + 1) =>
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf p.2.2) t • p.1,
          (p.2.1 + ((hf.deriv_periodic.lift p.2.2 * coupledAccum hA hB hf p.2.2 p.1 t : ℝ) :
            AddCircle (1 : ℝ)), p.2.2)))
      (arenaVolume N) = arenaVolume N := by
  have h : (fun p : KSigma (N + 1) =>
      (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf p.2.2) t • p.1,
        (p.2.1 + ((hf.deriv_periodic.lift p.2.2 * coupledAccum hA hB hf p.2.2 p.1 t : ℝ) :
          AddCircle (1 : ℝ)), p.2.2)))
      = (arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A B hf hc) t :=
    funext fun p => (hamiltonianFlow_coupledEnergy hA hB hf hc t p.1 p.2).symm
  rw [h]
  exact arenaVolume_map_hamiltonianFlow (contMDiff_coupledEnergy A B hf hc) t

end LF4
end CSD

end
