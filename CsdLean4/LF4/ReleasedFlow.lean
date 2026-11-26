/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ControlledStep
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUnitaryCurve
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonBracket
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelSector

/-!
# A carrier released by a pointer's angle: the flow, where the released observable vanishes

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #437 (obligation UO-26, the mechanism of
UA-22; obligation UO-24; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md`
§9.4; route (α) of the task plans).

`LF4/ControlledStep.lean` names the base's flow of the energy

  `−2⟨A⟩ − 2 f(θ₂)⟨B⟩ + c · b(θ₁) · (−2⟨C⟩)`

and solves it only for `c = 0`. Here it is solved for every `c`, at the points where
`⟨C⟩ = 0`, when `C` commutes with `A` and `B`. There `⟨C⟩` stays `0`, so the pointer's
conserved angle `θ₂` stays conserved; the ray is moved by the earlier unitary of
`A + f(θ₂) B` **times** the unitary of `C` run with the clock `c ∫₀ᵗ b(θ₁(u)) du`; and the
pointer's moving angle `θ₁` advances exactly as it did without the term.

So a carrier whose only motion is through `C` is at rest while the window `b` of the
pointer's angle is shut, and moves as a free carrier, with its whole weight, once the
pointer has turned into the window.

* `hasMFDerivAt_torusWindow`, `releaseField`, `isHamiltonianVectorField_releaseTerm`,
  ★ `isHamiltonianVectorField_controlObs` — the field of `b(θ₁) · (−2⟨C⟩)`;
* ★★ `isHamiltonianVectorField_released` — the field of the whole energy;
* `schrodingerUnitary_val`, `mul_schrodingerUnitary_of_commute`,
  `schrodingerUnitary_mul_comm_of_commute`, `continuous_schrodingerUnitary`,
  ★ `hasDerivAt_schrodingerUnitary_mul_clock` — two commuting one-parameter groups, the
  second run with any differentiable clock;
* `schrodingerHamiltonian_mul_smul_of_commute`, `schrodingerHamiltonian_mul_smul_self`;
* `releasedAngle`, `releasedClock`, `releasedCurve`, `hasDerivAt_releasedClock`,
  ★★ `isMIntegralCurve_releasedCurve`;
* ★★★ `hamiltonianFlow_released` — **the flow in closed form at a point where `⟨C⟩ = 0`**.

## Honest scope

⚠️ **Only where `⟨C⟩ = 0`.** Elsewhere the pointer's conserved angle moves at the rate
`c (−2⟨C⟩) b'(θ₁)` and no closed form is given. The points where `⟨C⟩ = 0` are a closed set
with empty interior in general.

⚠️ **`C` commutes with `A` and `B`** by hypothesis. That is the case of a carrier that no
other term of the energy acts on. No such carrier is put in here: the matrices are any
three.

⚠️ **One pointer.** This is the base's flow of `LF4/ControlledStep.lean`, with the constant
`c` in place of the next pointer's profile at its conserved angle. The step with that
pointer added is `hamiltonianFlow_controlledEnergy`; the two are not composed here.

⚠️ **No record is read.** No readout, no threshold, no detector. That the pointer turns
into the window is not shown.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #437, #440; `specs/unified-record-spacetime-plan.md` (UA-20,
UA-22, UO-24, UO-26, UD-233, UD-270, UD-271; §9.4);
`specs/unified-records-spacetime-task-plans.md` (§9, route (α)); `LF4/ControlledStep.lean`
(`torusWindow`, `controlObs`, `hamiltonianFlow_controlledEnergy`);
`LF4/ArenaCoupledFlow.lean` (`coupledEnergy`, `coupledField`,
`isHamiltonianVectorField_coupled`, `coupledAccum`, `hamiltonianFlow_coupledEnergy`);
`Geometry/Manifold/Instances/ProjectiveSpaceUnitaryCurve.lean`
(`hasMFDerivAt_unitaryCurve_smul`);
`Geometry/Manifold/Instances/ProjectiveSpacePoissonBracket.lean`
(`expectation_conserved_iff_commute`); `Analysis/Matrix/DuhamelSector.lean`
(`Matrix.mul_exp_smul_eq_of_commute`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

/-! ### Two commuting one-parameter groups -/

section Groups

variable {N : ℕ}

/-- The matrix of `exp(-itH)`. -/
theorem schrodingerUnitary_val {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (t : ℝ) :
    (Matrix.schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ)
      = NormedSpace.exp (t • ((-Complex.I) • H)) := by
  show NormedSpace.exp (Matrix.schrodingerGen H t) = _
  rw [Matrix.schrodingerGen_eq_real_smul]

/-- A matrix that commutes with `H` commutes with `exp(-itH)`. -/
theorem mul_schrodingerUnitary_of_commute {Q H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (h : Q * H = H * Q) (t : ℝ) :
    Q * (Matrix.schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ)
      = (Matrix.schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ) * Q := by
  rw [schrodingerUnitary_val]
  exact Matrix.mul_exp_smul_eq_of_commute (by rw [mul_smul_comm, smul_mul_assoc, h]) t

/-- The unitary groups of two commuting Hermitian matrices commute. -/
theorem schrodingerUnitary_mul_comm_of_commute {M C : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.IsHermitian) (hC : C.IsHermitian) (h : C * M = M * C) (s τ : ℝ) :
    Matrix.schrodingerUnitary hM s * Matrix.schrodingerUnitary hC τ
      = Matrix.schrodingerUnitary hC τ * Matrix.schrodingerUnitary hM s := by
  refine Subtype.ext ?_
  show (Matrix.schrodingerUnitary hM s : Matrix (Fin N) (Fin N) ℂ)
      * (Matrix.schrodingerUnitary hC τ : Matrix (Fin N) (Fin N) ℂ)
    = (Matrix.schrodingerUnitary hC τ : Matrix (Fin N) (Fin N) ℂ)
      * (Matrix.schrodingerUnitary hM s : Matrix (Fin N) (Fin N) ℂ)
  have hCa := mul_schrodingerUnitary_of_commute hM h s
  exact mul_schrodingerUnitary_of_commute hC hCa.symm τ

/-- `t ↦ exp(-itH)` is continuous in the unitary group. -/
theorem continuous_schrodingerUnitary {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    Continuous fun t : ℝ => Matrix.schrodingerUnitary hH t :=
  continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun s =>
    (Matrix.schrodingerUnitary_hasDerivAt H hH s).continuousAt)

/-- ★ **Two commuting groups, the second run with a clock.** For commuting Hermitian `M`, `C`
and a clock `κ` with derivative `r` at `t`, the matrix of `exp(-itM) exp(-iκ(t)C)` has the
derivative `(-i (M + r C))` times itself at `t`. -/
theorem hasDerivAt_schrodingerUnitary_mul_clock {M C : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.IsHermitian) (hC : C.IsHermitian) (hCM : C * M = M * C) {κ : ℝ → ℝ} {r t : ℝ}
    (hκ : HasDerivAt κ r t) :
    HasDerivAt
      (fun s : ℝ => ((Matrix.schrodingerUnitary hM s * Matrix.schrodingerUnitary hC (κ s) :
        Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
      (((-Complex.I) • (M + (r : ℂ) • C))
        * ((Matrix.schrodingerUnitary hM t * Matrix.schrodingerUnitary hC (κ t) :
          Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) t := by
  have h1 := Matrix.schrodingerUnitary_hasDerivAt M hM t
  have h2 := HasDerivAt.scomp t (Matrix.schrodingerUnitary_hasDerivAt C hC (κ t)) hκ
  have h := h1.mul h2
  have hMa := mul_schrodingerUnitary_of_commute hM (rfl : M * M = M * M) t
  have hCa := mul_schrodingerUnitary_of_commute hM hCM t
  have hCd := mul_schrodingerUnitary_of_commute hC (rfl : C * C = C * C) (κ t)
  have e1 : (Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ) * M
        * (Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ)
      = M * ((Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ)
        * (Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [← hMa, mul_assoc]
  have e2 : (Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ)
        * ((Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ) * C)
      = C * ((Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ)
        * (Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [← hCd, ← mul_assoc, ← hCa, mul_assoc]
  refine h.congr_deriv ?_
  show (Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ) * ((-Complex.I) • M)
        * (Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ)
      + (Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ)
        * (r • ((Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ)
          * ((-Complex.I) • C)))
    = ((-Complex.I) • (M + (r : ℂ) • C))
      * ((Matrix.schrodingerUnitary hM t : Matrix (Fin N) (Fin N) ℂ)
        * (Matrix.schrodingerUnitary hC (κ t) : Matrix (Fin N) (Fin N) ℂ))
  rw [← Complex.coe_smul r]
  simp only [mul_smul_comm, smul_mul_assoc, smul_add, add_mul]
  rw [e1, e2]
  module

end Groups

/-! ### The field of the released term -/

section Field

variable {N : ℕ} {f b : ℝ → ℝ}

theorem hasMFDerivAt_torusWindow (hb : Function.Periodic b 1) (hd : Differentiable ℝ b)
    (θ : KTorus) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (torusWindow hb) θ
      (((1 : ℝ →L[ℝ] ℝ).smulRight (hb.deriv_periodic.lift θ.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) :=
  (hb.hasMFDerivAt_lift hd θ.1).comp θ
    (Prod.hasMFDerivAt_fst_self (E := ℝ) (F := ℝ) (M := AddCircle (1 : ℝ))
      (N := AddCircle (1 : ℝ)) θ)

variable (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **The field of the released term** `b(θ₁) · (−2⟨C⟩)`: `(b(θ₁) X_C, (0, 2⟨C⟩ b'(θ₁)))`. -/
def releaseField (hb : Function.Periodic b 1) (p : KSigma (N + 1)) :
    TangentSpace 𝓘(ℝ, ArenaModel N) p :=
  ((torusWindow hb p.2 • schrodingerField C p.1,
    ((0, -(schrodingerHamiltonian C p.1 * hb.deriv_periodic.lift p.2.1)) : ℝ × ℝ)) :
    TangentSpace 𝓘(ℝ, ArenaModel N) p)

variable {C}

/-- `ι_X ω = d (−2⟨C⟩ · b(θ₁))` on the arena for the field of the released term. -/
theorem isHamiltonianVectorField_releaseTerm (hC : C.IsHermitian)
    (hb : Function.Periodic b 1) (hd : Differentiable ℝ b) :
    IsHamiltonianVectorField (fun p => arenaForm N p)
      (fun p : KSigma (N + 1) =>
        ((torusWindow hb p.2 • schrodingerField C p.1,
          ((0, -(schrodingerHamiltonian C p.1 * hb.deriv_periodic.lift p.2.1)) : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, ArenaModel N) p))
      (fun p => schrodingerHamiltonian C p.1 * torusWindow hb p.2) := by
  intro p v
  have ha : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian C q.1) p
      ((mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian C) p.1).comp
        (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (mdifferentiableAt_schrodingerHamiltonian C p.1).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have hbw : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => torusWindow hb q.2) p
      ((((1 : ℝ →L[ℝ] ℝ).smulRight (hb.deriv_periodic.lift p.2.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (hasMFDerivAt_torusWindow hb hd p.2).comp p
      (Prod.hasMFDerivAt_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have hprod : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian C q.1 * torusWindow hb q.2) p _ :=
    ha.mul hbw
  beta_reduce
  rw [hprod.mfderiv]
  have hX := schrodingerField_isHamiltonianVectorField hC p.1 (v : ArenaModel N).1
  have h1 : (arenaForm N p) ![((torusWindow hb p.2 • schrodingerField C p.1,
      ((0, -(schrodingerHamiltonian C p.1 * hb.deriv_periodic.lift p.2.1)) : ℝ × ℝ)) :
        TangentSpace 𝓘(ℝ, ArenaModel N) p), v]
      = toFlat (fsForm (n := N) p.1)
          ![torusWindow hb p.2 • schrodingerField C p.1, (v : ArenaModel N).1]
        + TorusForm.areaForm
          ![((0, -(schrodingerHamiltonian C p.1 * hb.deriv_periodic.lift p.2.1)) : ℝ × ℝ),
            (v : ArenaModel N).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm _ _
  rw [h1]
  have h2 : toFlat (fsForm (n := N) p.1)
      ![torusWindow hb p.2 • schrodingerField C p.1, (v : ArenaModel N).1]
      = torusWindow hb p.2 * toFlat (fsForm (n := N) p.1)
          ![schrodingerField C p.1, (v : ArenaModel N).1] :=
    apply_smul_left (fun x : CPN (N + 1) => fsForm (n := N) x) p.1 _ _ _
  rw [h2]
  have h3 : toFlat (fsForm (n := N) p.1) ![schrodingerField C p.1, (v : ArenaModel N).1]
      = mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian C) p.1 (v : ArenaModel N).1 := hX
  rw [h3, TorusForm.areaForm_apply]
  set D : ℝ := mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian C) p.1 (v : ArenaModel N).1
    with hD
  show torusWindow hb p.2 * D
      + (0 * (v : ArenaModel N).2.2
        - -(schrodingerHamiltonian C p.1 * hb.deriv_periodic.lift p.2.1) * (v : ArenaModel N).2.1)
    = schrodingerHamiltonian C p.1 * ((v : ArenaModel N).2.1 * hb.deriv_periodic.lift p.2.1)
      + torusWindow hb p.2 * D
  ring

/-- ★ **The field of the controlled observable** `b(θ₁) · (−2⟨C⟩)`. -/
theorem isHamiltonianVectorField_controlObs (hC : C.IsHermitian) (hb : Function.Periodic b 1)
    (hd : Differentiable ℝ b) :
    IsHamiltonianVectorField (fun p => arenaForm N p) (releaseField C hb)
      (controlObs C hb) := by
  have e : controlObs C hb
      = fun p : KSigma (N + 1) => schrodingerHamiltonian C p.1 * torusWindow hb p.2 := by
    funext p
    exact mul_comm _ _
  rw [e]
  exact isHamiltonianVectorField_releaseTerm hC hb hd

/-- ★★ **`ι_X ω = d𝓗` for the energy with the released term**, for every constant `c`. -/
theorem isHamiltonianVectorField_released {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcb : ContDiff ℝ ∞ b) (c : ℝ) :
    IsHamiltonianVectorField (fun p => arenaForm N p)
      (fun p : KSigma (N + 1) => coupledField A B hf p + c • releaseField C hb p)
      (coupledEnergy A B hf + c • controlObs C hb) := by
  have hdH : ∀ p : KSigma (N + 1), MDifferentiableAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (coupledEnergy A B hf) p := fun p =>
    (contMDiff_coupledEnergy A B hf hc p).mdifferentiableAt (by simp)
  have hdG : ∀ p : KSigma (N + 1), MDifferentiableAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (controlObs C hb) p := fun p =>
    (contMDiff_controlObs C hb hcb p).mdifferentiableAt (by simp)
  exact (isHamiltonianVectorField_coupled hA hB hf (hc.differentiable (by simp))).add
    ((isHamiltonianVectorField_controlObs hC hb (hcb.differentiable (by simp))).smul c hdG)
    hdH (fun p => (hdG p).const_smul c)

end Field

/-! ### What a commuting unitary does to an expectation -/

section Invariance

variable {N : ℕ}

/-- `⟨B⟩` does not see a unitary of a commuting `C` applied after another unitary. -/
theorem schrodingerHamiltonian_mul_smul_of_commute
    {M B C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hM : M.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hCM : C * M = M * C) (hBC : B * C = C * B) (s τ : ℝ)
    (x : CPN (N + 1)) :
    schrodingerHamiltonian B
        ((Matrix.schrodingerUnitary hM s * Matrix.schrodingerUnitary hC τ) • x)
      = schrodingerHamiltonian B (Matrix.schrodingerUnitary hM s • x) := by
  rw [schrodingerUnitary_mul_comm_of_commute hM hC hCM, mul_smul]
  unfold schrodingerHamiltonian
  rw [(expectation_conserved_iff_commute hB hC).2 hBC]

/-- `⟨C⟩` is conserved by its own unitary and by that of a commuting `M`. -/
theorem schrodingerHamiltonian_mul_smul_self {M C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hM : M.IsHermitian) (hC : C.IsHermitian) (hCM : C * M = M * C) (s τ : ℝ)
    (x : CPN (N + 1)) :
    schrodingerHamiltonian C
        ((Matrix.schrodingerUnitary hM s * Matrix.schrodingerUnitary hC τ) • x)
      = schrodingerHamiltonian C x := by
  rw [mul_smul]
  unfold schrodingerHamiltonian
  rw [(expectation_conserved_iff_commute hC hM).2 hCM, expectation_schrodingerUnitary_smul hC]

end Invariance

/-! ### The closed-form curve -/

section Curve

variable {N : ℕ} {f b : ℝ → ℝ} {A B C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

/-- The pointer's moving angle along the run, as a real number: it is not changed by the
released term. -/
def releasedAngle (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (u : ℝ) : ℝ :=
  a₀ + hf.deriv_periodic.lift φ * coupledAccum hA hB hf φ x u

theorem hasDerivAt_releasedAngle (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (releasedAngle hA hB hf x a₀ φ)
      (hf.deriv_periodic.lift φ * schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x)) t :=
  ((hasDerivAt_coupledAccum hA hB hf φ x t).const_mul _).const_add a₀

theorem continuous_releasedAngle (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) :
    Continuous (releasedAngle hA hB hf x a₀ φ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_releasedAngle hA hB hf x a₀ φ t).continuousAt

/-- **The clock of the released carrier**: `c ∫₀ᵗ b(θ₁(u)) du`. -/
def releasedClock (hA : A.IsHermitian) (hB : B.IsHermitian) (hf : Function.Periodic f 1)
    (b : ℝ → ℝ) (c : ℝ) (x : CPN (N + 1)) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) : ℝ :=
  c * ∫ u in (0 : ℝ)..t, b (releasedAngle hA hB hf x a₀ φ u)

theorem hasDerivAt_releasedClock (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hbc : Continuous b) (c : ℝ) (x : CPN (N + 1)) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (releasedClock hA hB hf b c x a₀ φ)
      (c * b (releasedAngle hA hB hf x a₀ φ t)) t := by
  have hcont : Continuous fun u : ℝ => b (releasedAngle hA hB hf x a₀ φ u) :=
    hbc.comp (continuous_releasedAngle hA hB hf x a₀ φ)
  exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    (hcont.stronglyMeasurableAtFilter volume _) hcont.continuousAt).const_mul c

/-- **The closed-form curve**: the ray moved by `exp(-itM) exp(-iκ(t)C)`, `M = A + f(φ) B`,
`κ` the released clock; `θ₁` as without the term; `θ₂ = φ`. -/
def releasedCurve (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hf : Function.Periodic f 1) (b : ℝ → ℝ) (c : ℝ) (x : CPN (N + 1)) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) : KSigma (N + 1) :=
  ((Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t
      * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x,
    (((releasedAngle hA hB hf x a₀ φ t : ℝ) : AddCircle (1 : ℝ)), φ))

/-- `C` commutes with `A + f(φ) B` when it commutes with `A` and `B`. -/
theorem mul_coupledMatrix_of_commute (hCA : C * A = A * C) (hCB : C * B = B * C)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) :
    C * coupledMatrix A B hf φ = coupledMatrix A B hf φ * C := by
  unfold coupledMatrix
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hCA, hCB]

/-- ★★ **The closed-form curve is an integral curve of the field**, from a point where
`⟨C⟩ = 0`, when `C` commutes with `A` and `B`. -/
theorem isMIntegralCurve_releasedCurve (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hCA : C * A = A * C) (hCB : C * B = B * C)
    (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcb : ContDiff ℝ ∞ b) (c : ℝ) {x : CPN (N + 1)} (hx : schrodingerHamiltonian C x = 0)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) :
    IsMIntegralCurve (releasedCurve hA hB hC hf b c x a₀ φ)
      ((arenaForm_isSymplectic N).hamiltonianVectorField
        (coupledEnergy A B hf + c • controlObs C hb)) := by
  rw [← (isHamiltonianVectorField_released hA hB hC hf hb hc hcb
    c).eq_isSymplectic_hamiltonianVectorField (arenaForm_isSymplectic N)]
  intro t
  have hM := coupledMatrix_isHermitian hA hB hf φ
  have hCM := mul_coupledMatrix_of_commute hCA hCB hf φ
  have hκ := hasDerivAt_releasedClock hA hB hf hcb.continuous c x a₀ φ t
  have hWc : Continuous fun s : ℝ =>
      Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) s
        * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ s) :=
    (continuous_schrodingerUnitary hM).mul ((continuous_schrodingerUnitary hC).comp
      (continuous_iff_continuousAt.2 fun s =>
        (hasDerivAt_releasedClock hA hB hf hcb.continuous c x a₀ φ s).continuousAt))
  have hray := hasMFDerivAt_unitaryCurve_smul hWc
    (hasDerivAt_schrodingerUnitary_mul_clock hM hC hCM hκ) x
  rw [schrodingerField_add_real_smul hM hC, schrodingerField_coupledMatrix hA hB] at hray
  have hθ₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun u : ℝ => ((releasedAngle hA hB hf x a₀ φ u : ℝ) : AddCircle (1 : ℝ))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift φ * schrodingerHamiltonian B
        (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf φ) t • x))) :=
    AddCircle.hasMFDerivAt_coe_comp (hasDerivAt_releasedAngle hA hB hf x a₀ φ t)
  have hθ₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => φ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) φ) :=
    hasMFDerivAt_const φ t
  have hBray := schrodingerHamiltonian_mul_smul_of_commute hM hB hC hCM hCB.symm t
    (releasedClock hA hB hf b c x a₀ φ t) x
  have hCray := (schrodingerHamiltonian_mul_smul_self hM hC hCM t
    (releasedClock hA hB hf b c x a₀ φ t) x).trans hx
  have h := hray.prodMk_self (hθ₁.prodMk_self hθ₂)
  refine h.congr_deriv ?_
  refine ContinuousLinearMap.ext fun s => Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((1 : ℝ →L[ℝ] ℝ) s) •
        (schrodingerField A ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          + hf.lift φ • schrodingerField B ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          + (c * b (releasedAngle hA hB hf x a₀ φ t)) • schrodingerField C
            ((Matrix.schrodingerUnitary hM t
              * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x))
      = ((1 : ℝ →L[ℝ] ℝ) s) •
        (schrodingerField A ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          + hf.lift φ • schrodingerField B ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          + c • (hb.lift ((releasedAngle hA hB hf x a₀ φ t : ℝ) : AddCircle (1 : ℝ))
            • schrodingerField C ((Matrix.schrodingerUnitary hM t
              * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)))
    rw [hb.lift_coe, smul_smul]
  · show ((1 : ℝ →L[ℝ] ℝ) s) • (hf.deriv_periodic.lift φ * schrodingerHamiltonian B
        (Matrix.schrodingerUnitary hM t • x))
      = ((1 : ℝ →L[ℝ] ℝ) s) • (schrodingerHamiltonian B
          ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          * hf.deriv_periodic.lift φ + c • (0 : ℝ))
    rw [hBray, smul_zero, add_zero, mul_comm]
  · show (0 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) s) • ((0 : ℝ) + c •
        -(schrodingerHamiltonian C ((Matrix.schrodingerUnitary hM t
            * Matrix.schrodingerUnitary hC (releasedClock hA hB hf b c x a₀ φ t)) • x)
          * hb.deriv_periodic.lift ((releasedAngle hA hB hf x a₀ φ t : ℝ) : AddCircle (1 : ℝ))))
    rw [hCray, zero_mul, neg_zero, smul_zero, add_zero, smul_zero]

/-- ★★★ **The flow with a released term, in closed form where `⟨C⟩ = 0`.** `C` commutes with
`A` and `B`, and `⟨C⟩ = 0` at `x`. For every constant `c`, the Hamiltonian flow of
`−2⟨A⟩ − 2 f(θ₂)⟨B⟩ + c b(θ₁)(−2⟨C⟩)` moves the ray by `exp(-itM) exp(-iκ(t)C)` with
`M = A + f(θ₂) B` and the clock `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`, advances `θ₁` by
`f'(θ₂) ∫₀ᵗ (−2⟨B⟩)` along the orbit of `M` alone, and fixes `θ₂`. -/
theorem hamiltonianFlow_released (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hCA : C * A = A * C) (hCB : C * B = B * C)
    (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcb : ContDiff ℝ ∞ b) (c : ℝ) {x : CPN (N + 1)} (hx : schrodingerHamiltonian C x = 0)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul (contMDiff_coupledEnergy A B hf hc)
          (contMDiff_controlObs C hb hcb) c) t (x, ((a₀ : AddCircle (1 : ℝ)), φ))
      = releasedCurve hA hB hC hf b c x a₀ φ t := by
  have hγ := isMIntegralCurve_releasedCurve hA hB hC hCA hCB hf hb hc hcb c hx a₀ φ
  have h0 : releasedCurve hA hB hC hf b c x a₀ φ 0 = (x, ((a₀ : AddCircle (1 : ℝ)), φ)) := by
    unfold releasedCurve releasedClock releasedAngle
    rw [intervalIntegral.integral_same, mul_zero,
      (Matrix.expNegITH_unitary_group (coupledMatrix_isHermitian hA hB hf φ)).2,
      (Matrix.expNegITH_unitary_group hC).2, one_mul, one_smul, coupledAccum_zero, mul_zero,
      add_zero]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_add_const_smul (contMDiff_coupledEnergy A B hf hc)
        (contMDiff_controlObs C hb hcb) c)) hγ h0
  rw [IsSymplectic.hamiltonianFlow, ← congrFun h t]

end Curve

end LF4
end CSD

end
