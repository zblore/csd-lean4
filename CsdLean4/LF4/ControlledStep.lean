/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PointerStep
public import CsdLean4.LF4.ArenaVolume

/-!
# A pointer that reads an earlier pointer: the controlled step

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #440, second brick (Task 5 of the author's
plan "Unified records, quantum measurement and emergent spacetime" of 2026-11-18, workstream
R; obligations UO-24 and UO-25, item (5); the term of UA-20).

On every arena built before this one no pointer's moving angle is in the energy, so nothing
depends on what a pointer displays (`LF4/PentaPointerInert.lean`). UA-20 admits a step whose
observable is `b(θ₁) · K`: a smooth window `b` of an earlier pointer's **moving** angle `θ₁`
times a function `K` of the ray. This module defines that step over the one-pointer arena
and solves its flow.

* `torusWindow`, `contMDiff_torusWindow` — a profile of the first angle of a torus;
* `controlObs`, `contMDiff_controlObs` — the observable `b(θ₁) · (−2⟨C⟩)`;
* `controlledEnergy`, `contMDiff_controlledEnergy` — the energy
  `−2⟨A⟩ − 2 f(θ₂)⟨B⟩ + g(ψ₂) b(θ₁) (−2⟨C⟩)`;
* ★★ `hamiltonianFlow_controlledEnergy` — the flow as a skew product over the new pointer's
  conserved angle;
* `coupledEnergy_add_zero_smul`;
* ★★★ `hamiltonianFlow_controlledEnergy_of_lift_eq_zero` — **on a fibre where `g(ψ₂) = 0`
  the first apparatus runs as if alone, and the second pointer's displacement is
  `g'(ψ₂) ∫₀ᵗ b(θ₁(u)) (−2⟨C⟩(u)) du` along it**;
* ★★★ `controlled_pointer_fixed_of_window_eq_zero` — **the second pointer does not move
  while the window of the first pointer's angle is shut**;
* ★★ `map_hamiltonianFlow_controlledEnergy` — the flow preserves `μ_FS ⊗ vol ⊗ vol`.

## Honest scope

⚠️ **A term of a new kind (UA-20).** The first pointer's moving angle is in the energy. Off
the fibres where `g(ψ₂) = 0` its conserved angle `θ₂` is not conserved, and no closed form
is given there: `hamiltonianFlow_controlledEnergy` names the base's flow and does not solve
it.

⚠️ **One-way on the fibres `g(ψ₂) = 0`, which are a null set of the second pointer's
angles.** The explicit statements are on those fibres.

⚠️ **A smooth window, not the displaying arc.** `b` is smooth, so "the first pointer
displays" is a window on its angle and not the indicator of the arc.

⚠️ **No record is read here.** No ticks, no thresholds, no history. That the second pointer
ticks only after the first has displayed is not shown.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #440, ~~#368~~, ~~#374~~;
`specs/unified-record-spacetime-plan.md` (UA-13, UA-20, UO-24, UO-25, UD-227, UD-233);
`specs/unified-records-spacetime-task-plans.md` (§3); `LF4/PointerStep.lean` (`stepEnergy`,
`hamiltonianFlow_stepEnergy`, `map_hamiltonianFlow_stepEnergy`, `hamiltonianFlow_congr`);
`LF4/ArenaCoupledFlow.lean` (`coupledEnergy`, `hamiltonianFlow_coupledEnergy`,
`coupledAccum`); `LF4/ArenaVolume.lean` (`kMuL_map_hamiltonianFlow`);
`LF4/PentaPointerInert.lean` (`fiveCoupledFlow_shiftPenta`); `specs/future-work.md`.
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

section Controlled

variable {N : ℕ} {f g b : ℝ → ℝ}

/-- **The first torus angle read through a periodic profile.** -/
noncomputable def torusWindow (hb : Function.Periodic b 1) (θ : KTorus) : ℝ := hb.lift θ.1

theorem contMDiff_torusWindow (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ b) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (torusWindow hb) :=
  (hb.contMDiff_lift hc).comp
    (Prod.contMDiff_fst_self (E := ℝ) (F := ℝ) (M := AddCircle (1 : ℝ)) (N := AddCircle (1 : ℝ)))

variable (A B C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **The observable of the controlled step**: the window of the first pointer's moving
angle times `−2⟨C⟩`. -/
noncomputable def controlObs (hb : Function.Periodic b 1) (x : KSigma (N + 1)) : ℝ :=
  torusWindow hb x.2 * schrodingerHamiltonian C x.1

theorem contMDiff_controlObs (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ b) :
    ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ (controlObs C hb) :=
  ((contMDiff_torusWindow hb hc).comp
    (Prod.contMDiff_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) (M := CPN (N + 1))
      (N := KTorus))).mul
    (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (m := ∞) C))

/-- **The energy of the controlled step**: the one-pointer energy plus the new pointer's
profile times the controlled observable. -/
noncomputable def controlledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hb : Function.Periodic b 1) : KSigma (N + 1) × KTorus → ℝ :=
  stepEnergy (coupledEnergy A B hf) (controlObs C hb) hg

theorem contMDiff_controlledEnergy (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcb : ContDiff ℝ ∞ b) :
    ContMDiff 𝓘(ℝ, ArenaModel N × (ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞ (controlledEnergy A B C hf hg hb) :=
  contMDiff_stepEnergy (contMDiff_coupledEnergy A B hf hc) (contMDiff_controlObs C hb hcb) hg hcg

/-- ★★ **The flow of the controlled step is a skew product over the new pointer's conserved
angle.** The arena with the first pointer moves by its own Hamiltonian flow of the energy
`−2⟨A⟩ − 2 f(θ₂)⟨B⟩ + g(ψ₂) b(θ₁)(−2⟨C⟩)`, the new pointer's moving angle advances by
`g'(ψ₂)` times the accumulated `b(θ₁)(−2⟨C⟩)` along that orbit, and `ψ₂` is fixed. -/
theorem hamiltonianFlow_controlledEnergy (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hcb : ContDiff ℝ ∞ b) (t : ℝ) (s : KSigma (N + 1)) (ψ : KTorus) :
    (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) t (s, ψ)
      = ((arenaForm_isSymplectic N).hamiltonianFlow
            (contMDiff_add_const_smul (contMDiff_coupledEnergy A B hf hc)
              (contMDiff_controlObs C hb hcb) (hg.lift ψ.2)) t s,
          (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..t,
              controlObs C hb ((arenaForm_isSymplectic N).hamiltonianFlow
                (contMDiff_add_const_smul (contMDiff_coupledEnergy A B hf hc)
                  (contMDiff_controlObs C hb hcb) (hg.lift ψ.2)) u s) : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)) :=
  hamiltonianFlow_stepEnergy (arenaForm_isSymplectic N) (contMDiff_coupledEnergy A B hf hc)
    (contMDiff_controlObs C hb hcb) hg hcg t s ψ

/-- With the new pointer's profile at zero the base energy is the one-pointer energy. -/
theorem coupledEnergy_add_zero_smul (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) :
    coupledEnergy A B hf + (0 : ℝ) • controlObs C hb = coupledEnergy A B hf := by
  rw [zero_smul, add_zero]

variable {A B}

/-- ★★★ **On a fibre where the new pointer's profile vanishes, the first apparatus runs as if
alone and the second pointer reads the window of the first.** The ray moves by the
Schrödinger unitary of `A + f(θ₂) B`, the first pointer by `f'(θ₂)` times the accumulated
`−2⟨B⟩`, and the second pointer by `g'(ψ₂) ∫₀ᵗ b(θ₁(u)) (−2⟨C⟩(u)) du` along that run. -/
theorem hamiltonianFlow_controlledEnergy_of_lift_eq_zero (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hcb : ContDiff ℝ ∞ b) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus) (h0 : hg.lift ψ.2 = 0) :
    (stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) t ((x, θ), ψ)
      = ((Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf θ.2) t • x,
            (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x t : ℝ) :
              AddCircle (1 : ℝ)), θ.2)),
          (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * ∫ u in (0 : ℝ)..t,
              hb.lift (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
                AddCircle (1 : ℝ)))
              * schrodingerHamiltonian C
                (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf θ.2) u • x) : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)) := by
  have hbase : ∀ u : ℝ, (arenaForm_isSymplectic N).hamiltonianFlow
      (contMDiff_add_const_smul (contMDiff_coupledEnergy A B hf hc)
        (contMDiff_controlObs C hb hcb) (hg.lift ψ.2)) u (x, θ)
      = (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf θ.2) u • x,
          (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
            AddCircle (1 : ℝ)), θ.2)) := fun u => by
    rw [← hamiltonianFlow_coupledEnergy hA hB hf hc u x θ]
    exact congrFun (congrFun (hamiltonianFlow_congr (arenaForm_isSymplectic N)
      (by rw [h0]; exact coupledEnergy_add_zero_smul A B C hf hb) _
      (contMDiff_coupledEnergy A B hf hc)) u) (x, θ)
  rw [hamiltonianFlow_controlledEnergy A B C hf hg hb hc hcg hcb t (x, θ) ψ, hbase t]
  simp only [hbase]
  rfl

/-- ★★★ **The second pointer does not move while the window of the first is shut.** On a
fibre where `g(ψ₂) = 0`: if the window `b` vanishes at the first pointer's angle at every
flow time between `0` and `t`, the second pointer is at `t` where it started. -/
theorem controlled_pointer_fixed_of_window_eq_zero (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hcb : ContDiff ℝ ∞ b) (t : ℝ)
    (x : CPN (N + 1)) (θ ψ : KTorus) (h0 : hg.lift ψ.2 = 0)
    (hshut : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      hb.lift (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
        AddCircle (1 : ℝ))) = 0) :
    ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
        (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) t ((x, θ), ψ)).2 = ψ := by
  rw [hamiltonianFlow_controlledEnergy_of_lift_eq_zero C hA hB hf hg hb hc hcg hcb t x θ ψ h0]
  have hint : ∫ u in (0 : ℝ)..t,
      hb.lift (θ.1 + ((hf.deriv_periodic.lift θ.2 * coupledAccum hA hB hf θ.2 x u : ℝ) :
          AddCircle (1 : ℝ)))
        * schrodingerHamiltonian C
          (Matrix.schrodingerUnitary (coupledMatrix_isHermitian hA hB hf θ.2) u • x) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
      simp only [hshut u hu, zero_mul]]
    exact intervalIntegral.integral_zero
  simp only [hint, mul_zero, AddCircle.coe_zero, add_zero]

variable (A B)

set_option synthInstance.maxSize 1024 in
/-- ★★ **The flow of the controlled step preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`.** The
arena with the first pointer is moved by Hamiltonian flows of smooth energies, each of which
preserves `μ_FS ⊗ vol_{T²}`; the step adds the new torus. -/
theorem map_hamiltonianFlow_controlledEnergy (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hcb : ContDiff ℝ ∞ b) (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map
        ((stepForm_isSymplectic (arenaForm_isSymplectic N)).hamiltonianFlow
          (contMDiff_controlledEnergy A B C hf hg hb hc hcg hcb) t)
        ((kMuL p₀).prod (volume : Measure KTorus))
      = (kMuL p₀).prod (volume : Measure KTorus) :=
  map_hamiltonianFlow_stepEnergy (arenaForm_isSymplectic N) (contMDiff_coupledEnergy A B hf hc)
    (contMDiff_controlObs C hb hcb) hg hcg (kMuL p₀) t fun _ =>
      kMuL_map_hamiltonianFlow N p₀ _ t

end Controlled

end LF4
end CSD
