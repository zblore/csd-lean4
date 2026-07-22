/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.SternGerlachVolume

/-!
# Empirical/CSD: Malus's law (spin-1/2) as a derived Kähler-volume frequency

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag).

The **parametric generalisation** of `Empirical/CSD/SternGerlachVolume.lean`:
the operational spin-1/2 Malus law `P(+ | θ, |+z⟩) = cos²(θ/2)` realised as a
derived Fubini–Study volume frequency on the ontic `Σ = ℂℙ¹`, carving-free and
Gleason-free.

## Construction

For a measurement axis at polar angle `θ` from the `+z` preparation axis, the
`+`-eigenstate is `ψ_θ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩`, so the Born amplitude is
`⟨e₀, ψ_θ⟩ = cos(θ/2)` and the Born weight `‖⟨e₀, ψ_θ⟩‖² = cos²(θ/2)`. The volume
capstone `LF4.qubit_born_frequency_convergence_uncond` then gives, for i.i.d.
Fubini–Study trials, that the empirical frequency of the moment-sublevel outcome
region cut by `[ψ_θ]` converges almost surely to `cos²(θ/2)`, with `volume = Born`
*computed* via the Duistermaat–Heckman theorem `fs_moment_pushforward_uniform`
(no carving, no `busch_effect_gleason`).

## Specialisations

`csd_malus_law` subsumes the two Stern-Gerlach values of
`SternGerlachVolume.lean`:

- `θ = 0`     ⟹  `cos²(0) = 1`        (`P(+z | +z) = 1`);
- `θ = π/2`   ⟹  `cos²(π/4) = 1/2`    (the canonical `50/50` split).

## What is and is not claimed

**Derived (Lean-checked, carving-free, Gleason-free).** The limit value
`cos²(θ/2)` is the genuine Fubini–Study volume of the moment-sublevel region,
foundational triple only.

**Not claimed (still LF4-todo §14).** Identifying the moment-sublevel region with
the physical "the spin-`θ` `+` detector fired" outcome is the §14 observable
correspondence, undischarged pre-LF5. This file derives the Born *number* as a
Kähler volume; it does not provide the operator → measurable-Σ-function dictionary.

## Experimental verification

- Malus 1809 (optical, classical analogue); the spin-1/2 `cos²(θ/2)` form is the
  canonical sequential Stern-Gerlach prediction (Stern, Gerlach 1922; standard
  QM textbooks, e.g. Sakurai 1985).
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace MalusVolume

/-! ### The `θ`-rotated single-qubit state -/

/-- The spin-`θ` `+`-eigenstate `cos(θ/2)|0⟩ + sin(θ/2)|1⟩`, with
`⟨e₀, malusVec θ⟩ = cos(θ/2)`. -/
noncomputable def malusVec (θ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((Real.cos (θ / 2) : ℝ) : ℂ)
    + EuclideanSpace.single 1 ((Real.sin (θ / 2) : ℝ) : ℂ)

lemma malusVec_ofLp_zero (θ : ℝ) :
    (malusVec θ).ofLp 0 = ((Real.cos (θ / 2) : ℝ) : ℂ) := by
  simp [malusVec, EuclideanSpace.single]

lemma malusVec_ofLp_one (θ : ℝ) :
    (malusVec θ).ofLp 1 = ((Real.sin (θ / 2) : ℝ) : ℂ) := by
  simp [malusVec, EuclideanSpace.single]

lemma malusVec_norm (θ : ℝ) : ‖malusVec θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, malusVec_ofLp_zero, malusVec_ofLp_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

lemma malusVec_ne_zero (θ : ℝ) : malusVec θ ≠ 0 := by
  intro h
  have hz : ‖malusVec θ‖ = 0 := by rw [h, norm_zero]
  rw [malusVec_norm] at hz
  exact one_ne_zero hz

/-! ### Malus's law as a derived volume frequency -/

/-- **CSD Malus's law as a derived Kähler-volume frequency.**
For i.i.d. trials drawing microstates from the Fubini–Study typicality measure on
`Σ = ℂℙ¹`, the empirical frequency of the moment-sublevel outcome region cut by
the spin-`θ` `+`-eigenstate `[malusVec θ]` converges almost surely to `cos²(θ/2)`
— the operational spin-1/2 Malus law.

The limit is `‖⟨e₀, malusVec θ⟩‖² = ‖cos(θ/2)‖² = cos²(θ/2)`, with `volume = Born`
*derived* from the moment map (no carving), foundational triple only (no
`busch_effect_gleason`). Specialises to `1` at `θ = 0` and `1/2` at `θ = π/2`.
The identification of the region with the physical spin-`θ` outcome is
LF4-todo §14. -/
theorem csd_malus_law
    (θ : ℝ) (p₀ : CPN 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                momentMap (Projectivization.mk ℂ (malusVec θ) (malusVec_ne_zero θ)) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ (malusVec θ) (malusVec_ne_zero θ)) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (Real.cos (θ / 2) ^ 2)) := by
  have h := qubit_born_frequency_convergence_uncond p₀ (malusVec θ)
    (malusVec_ne_zero θ) (malusVec_norm θ) X hX hlaw hindep
  have hv : ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (malusVec θ)‖ ^ 2
      = Real.cos (θ / 2) ^ 2 := by
    rw [SternGerlachVolume.normSq_inner_single_zero, malusVec_ofLp_zero,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rwa [hv] at h

end MalusVolume
end CSDBridge
end Empirical
end CSD
