/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.PerturbedGenerator
public import CsdLean4.Mathlib.Analysis.Semigroup.PhaseGenerator

/-!
# The interacting Schrödinger equation on the domain of the free Hamiltonian

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #129 (out of ~~#64(iii)~~).

`SchrodingerGroup.schrodinger` is the interacting propagator `U(t) = e^{−it(H₀ + V)}` for a bounded
potential, built as the Dyson series around the free group — a mild solution. `PhaseGenerator.lean`
has the free Schrödinger equation on the domain of `H₀` (`hasDerivAt_fourierGroup_freePositionOp`),
and `PerturbedGenerator.lean` has the abstract theorem that a bounded perturbation's mild solution
is classical on the generator's domain. This file puts the two together.

* ★ `hasGeneratorAt_freeGroup`: a vector `ψ = 𝓕⁻¹ f` of the domain of `H₀` is in the domain of the
  generator of the free group, with value `−i H₀ ψ` — the free equation at `t = 0`, read as a right
  derivative.
* ★★★ `hasDerivAt_schrodinger`: **the interacting Schrödinger equation**, `d/dt U(t)ψ =
  −i U(t)(H₀ψ + Vψ)` at every `t > 0`, for every such `ψ`; `hasDerivAt_schrodinger_addCLM` writes
  the right-hand side with the operator `H₀ + V` of `FreeHamiltonian.lean` (`freePositionOp.addCLM
  (potential VL)`); `hasDerivWithinAt_schrodinger_zero` is the same at `t = 0`.
* ★★ `hasGeneratorAt_freeGroup_schrodinger`: **the orbit `U(t)ψ` stays in the domain of the free
  generator**, with `−i H₀ (U(t)ψ) = −i U(t)(H₀ + V)ψ + i V U(t)ψ`, so the equation also reads
  `i ∂ₜ U(t)ψ = (H₀ + V)(U(t)ψ)` with `H₀` acting on the orbit (★★★ `schrodinger_classical`).

## Honest scope

* **The domain of `H₀` enters as a hypothesis on the initial vector**, in the form
  `PhaseGenerator.lean` uses: `ψ = 𝓕⁻¹ f` with `f` in the momentum domain and the membership of
  `ψ` in `freePositionOp.domain` supplied. The *orbit* is shown to lie in the domain of the free
  **generator** (the right derivative of the free orbit exists), which is the semigroup-theoretic
  domain. That this coincides with the concretely described `freePositionOp.domain` — the converse
  of `phaseGroup_mem_mulDomain`, "a right-differentiable free orbit has `κ·f ∈ L²`", a Fatou
  argument — is not proved here and is recorded as a separate row. Until it is, "`U(t)ψ ∈ dom H₀`"
  is a statement about the generator, not about the multiplication domain.
* **The potential is the bounded multiplier `potential VL`** for `VL ∈ L^∞`, as in `schrodinger`
  itself. The self-adjoint `schrodingerOp` of `FreeHamiltonian.lean` takes a real `V` through
  `mulCLM`; identifying the two operators is a `coeFn` statement about `potential` that this file
  does not make, so the equation is stated with `potential VL` and the `addCLM` form uses it too.
* One dimension, `κ = freeSymbol`, as in `FreeHamiltonian.lean`.

References: Engel–Nagel III.1, Pazy Thm 3.1.1; `PerturbedGenerator.lean` (`hasDerivAt_perturbed`,
`hasGeneratorAt_of_perturbed`, `perturbed_classical`), `PhaseGenerator.lean`
(`hasDerivAt_fourierGroup_freePositionOp`, `phaseGroup_mem_mulDomain`), `SchrodingerGroup.lean`
(`schrodinger`, `isContractionSemigroup_fourierGroup`), `FreeHamiltonian.lean` (`freePositionOp`,
`schrodingerOp`); `specs/BACKLOG.md` #129, ~~#64~~.
-/

@[expose] public section

open scoped Topology ENNReal
open MeasureTheory Filter Set ContractionSemigroup HeatSemigroup

namespace SchrodingerGroup

/-! ### The free generator on the domain of `H₀` -/

/-- ★ **A vector of the domain of `H₀` is in the domain of the free group's generator**, with value
`−i H₀ ψ`: the free Schrödinger equation at `t = 0`, read as a right derivative. -/
theorem hasGeneratorAt_freeGroup (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) :
    HasGeneratorAt
      (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1)
      (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)))
      ((-Complex.I) • freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩) := by
  have hd := hasDerivAt_fourierGroup_freePositionOp f h 0
  rw [fourierGroup_zero, one_apply_eq_self] at hd
  rw [hasGeneratorAt_iff_hasDerivWithinAt (by simp [fourierGroup_zero])]
  refine hd.hasDerivWithinAt.congr ?_ ?_
  · intro s hs
    have hs' : (0 : ℝ) ≤ s := hs
    simp [hs']
  · simp

/-! ### The interacting equation -/

/-- ★★★ **The interacting Schrödinger equation on the domain of `H₀`**: for a bounded potential and
every `ψ = 𝓕⁻¹ f` with `f` in the momentum domain, `d/dt U(t)ψ = −i U(t)(H₀ψ + Vψ)` at every
`t > 0`. -/
theorem hasDerivAt_schrodinger (VL : Lp ℂ ∞ (volume : Measure ℝ)) (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt
      (fun s => schrodinger (measurable_freeSymbol (E := ℝ)) VL s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      ((-Complex.I) • schrodinger (measurable_freeSymbol (E := ℝ)) VL t
        (freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩
          + potential VL (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))) t := by
  have hd := hasDerivAt_perturbed (-(Complex.I • potential VL))
    (isContractionSemigroup_fourierGroup (measurable_freeSymbol (E := ℝ)))
    (hasGeneratorAt_freeGroup f h) ht
  refine hd.congr_deriv ?_
  rw [schrodinger, ← ContinuousLinearMap.map_smul]
  congr 1
  simp [smul_add]

/-- The same equation with the right-hand side written through the operator `H₀ + V` of
`FreeHamiltonian.lean`. -/
theorem hasDerivAt_schrodinger_addCLM (VL : Lp ℂ ∞ (volume : Measure ℝ))
    (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt
      (fun s => schrodinger (measurable_freeSymbol (E := ℝ)) VL s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      ((-Complex.I) • schrodinger (measurable_freeSymbol (E := ℝ)) VL t
        ((freePositionOp.addCLM (potential VL))
          ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩)) t :=
  hasDerivAt_schrodinger VL f h ht

/-- The equation at `t = 0`, within `[0, ∞)`: the derivative is `−i (H₀ψ + Vψ)`. -/
theorem hasDerivWithinAt_schrodinger_zero (VL : Lp ℂ ∞ (volume : Measure ℝ))
    (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) :
    HasDerivWithinAt
      (fun s => schrodinger (measurable_freeSymbol (E := ℝ)) VL s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      ((-Complex.I) • (freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩
          + potential VL (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)))))
      (Ici 0) 0 := by
  have hd := hasDerivWithinAt_perturbed_zero (-(Complex.I • potential VL))
    (isContractionSemigroup_fourierGroup (measurable_freeSymbol (E := ℝ)))
    (hasGeneratorAt_freeGroup f h)
  refine hd.congr_deriv ?_
  simp [smul_add]

/-! ### The orbit stays in the domain of the free generator -/

/-- ★★ **The orbit `U(t)ψ` stays in the domain of the free generator**, with
`−i H₀(U(t)ψ) = −i U(t)(H₀ψ + Vψ) + i V (U(t)ψ)`. -/
theorem hasGeneratorAt_freeGroup_schrodinger (VL : Lp ℂ ∞ (volume : Measure ℝ))
    (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    HasGeneratorAt
      (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1)
      (schrodinger (measurable_freeSymbol (E := ℝ)) VL t
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      (schrodinger (measurable_freeSymbol (E := ℝ)) VL t
          ((-Complex.I) • freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩
            + (-(Complex.I • potential VL)) (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
        - (-(Complex.I • potential VL)) (schrodinger (measurable_freeSymbol (E := ℝ)) VL t
            (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))) :=
  hasGeneratorAt_of_perturbed (-(Complex.I • potential VL))
    (isContractionSemigroup_fourierGroup (measurable_freeSymbol (E := ℝ)))
    (hasGeneratorAt_freeGroup f h) ht

/-- ★★★ **The classical equation along the orbit**: at every `t > 0`, `U(t)ψ` lies in the domain of
the free generator with a named value `w` (that is, `w = −i H₀ (U(t)ψ)` in generator form), and
`d/dt U(t)ψ = w − i V (U(t)ψ)` — i.e. `i ∂ₜ U(t)ψ = (H₀ + V)(U(t)ψ)` with `H₀` acting on the orbit. -/
theorem schrodinger_classical (VL : Lp ℂ ∞ (volume : Measure ℝ)) (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) {t : ℝ}
    (ht : 0 < t) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
      HasGeneratorAt
        (fun t : ℝ => if 0 ≤ t then fourierGroup (measurable_freeSymbol (E := ℝ)) t else 1)
        (schrodinger (measurable_freeSymbol (E := ℝ)) VL t
          (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)))) w
      ∧ HasDerivAt
        (fun s => schrodinger (measurable_freeSymbol (E := ℝ)) VL s
          (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
        (w - Complex.I • potential VL (schrodinger (measurable_freeSymbol (E := ℝ)) VL t
          (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))) t := by
  obtain ⟨w, hw, hd⟩ := perturbed_classical (-(Complex.I • potential VL))
    (isContractionSemigroup_fourierGroup (measurable_freeSymbol (E := ℝ)))
    (hasGeneratorAt_freeGroup f h) ht
  refine ⟨w, hw, hd.congr_deriv ?_⟩
  rw [schrodinger]
  simp [sub_eq_add_neg]

end SchrodingerGroup

end
