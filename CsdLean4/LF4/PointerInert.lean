/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PointerStep

/-!
# A pointer's moving angle is a cyclic coordinate: the flow commutes with turning it

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #374 — the generic half of an obstruction under
obligations UO-14 (b), UO-16 and UO-24 of the author's programme "From `Σ` to physical
spacetime".

`LF4/PointerStep.lean` adds a pointer torus to a compact symplectic arena with the energy
`H(s) + G(s) g(ψ₂)`. The moving angle `ψ₁` does not enter that energy. So turning the pointer by
any angle `c` at the start turns it by `c` at every later time and changes nothing else.

* `shiftMoving` — turn the new torus's moving angle by `c`;
* ★★★ `hamiltonianFlow_stepEnergy_shiftMoving` — **the flow of the step energy commutes with
  `shiftMoving c`**;
* ★ `hamiltonianFlow_stepEnergy_shiftMoving_fst` — the base at time `t` is the same for every
  starting position of the pointer.

## Exact scope

* **A consequence of the energy's form**, which is assumed (UA-13, UA-15): the coupling is a
  function of the base times a function of the conserved angle. Nothing is said for an energy in
  which the moving angle appears (UO-24).
* **One step.** For a tower of pointer tori the statement is applied at each level, with the
  lower levels as the base.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-13,
UA-15, UO-14, UO-16, UO-24, UD-106); `LF4/PointerStep.lean` (`stepEnergy`,
`hamiltonianFlow_stepEnergy`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

section Inert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℝ, E) ∞ S]
  {g : ℝ → ℝ} {β : DifferentialForm 𝓘(ℝ, E) S ∞ (Fin 2) ℝ}

/-- Turn the new torus's moving angle by `c`, leaving the base and the conserved angle. -/
def shiftMoving (c : AddCircle (1 : ℝ)) (p : S × KTorus) : S × KTorus :=
  (p.1, (p.2.1 + c, p.2.2))

variable [FiniteDimensional ℝ E] [CompactSpace S] [T2Space S]

/-- ★★★ **The flow commutes with turning the pointer.** For the energy `H(s) + G(s) g(ψ₂)`,
starting the new pointer `c` further round leaves it `c` further round at every time, and leaves
the base and the conserved angle as they were. -/
theorem hamiltonianFlow_stepEnergy_shiftMoving (hβ : β.IsSymplectic) {H G : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (c : AddCircle (1 : ℝ))
    (p : S × KTorus) :
    (stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t
        (shiftMoving c p)
      = shiftMoving c
        ((stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t p) := by
  obtain ⟨s, ψ⟩ := p
  rw [hamiltonianFlow_stepEnergy hβ hH hG hg hcg t s ψ]
  simp only [shiftMoving]
  rw [hamiltonianFlow_stepEnergy hβ hH hG hg hcg t s (ψ.1 + c, ψ.2)]
  simp only [add_right_comm]

/-- ★ **The base does not see where the pointer is.** -/
theorem hamiltonianFlow_stepEnergy_shiftMoving_fst (hβ : β.IsSymplectic) {H G : S → ℝ}
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ H) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G)
    (hg : Function.Periodic g 1) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (c : AddCircle (1 : ℝ))
    (p : S × KTorus) :
    ((stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t
        (shiftMoving c p)).1
      = ((stepForm_isSymplectic hβ).hamiltonianFlow (contMDiff_stepEnergy hH hG hg hcg) t p).1 := by
  rw [hamiltonianFlow_stepEnergy_shiftMoving hβ hH hG hg hcg t c p]
  rfl

end Inert

end LF4
end CSD

end
