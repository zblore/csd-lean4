import CsdLean4.LF4.MomentUniform
import CsdLean4.LF4.SingleQubitKahler

/-!
# Empirical/CSD: Stern-Gerlach Born values as derived Kähler-volume frequencies

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag).

This file is the **carving-free, Gleason-free** CSD-ontic reading of the
single-qubit Stern-Gerlach Born values. It sits strictly above the other two
Stern-Gerlach statements in the corpus:

1. `Empirical/CSD/SternGerlach.lean` (`csd_sg_*`): a *transport tag* — the Born
   numbers `1`, `0`, `1/2` are restated from the QM side; the CSD content is a
   prose realisability claim on the bundle. The numbers are **not** derived.
2. `LF4/SingleQubitKahler.lean` (`sg_frequency_convergence`): a genuine LF3-chain
   frequency-convergence capstone, but its outcome region is a `fibreArc`
   **carved by construction** to volume `sgBorn s a` (Tier-2). The number is
   realised, not derived from independent geometry.
3. **this file**: the outcome region is the genuine **moment-map sublevel set**
   on the ontic `Σ = ℂℙ¹`, whose Fubini–Study volume is *computed* (via the
   `N = 2` Duistermaat–Heckman fact `fs_moment_pushforward_uniform`, now a
   theorem) to equal the Born weight `‖⟨e₀, ψ⟩‖²`. So `volume = Born` is
   **derived**, not posited by carving, and the chain cites **only the
   foundational triple** (no `busch_effect_gleason`,
   no `invariant_measure_uniqueness`).

## What is and is not claimed

**Derived (Lean-checked, carving-free, Gleason-free).** For i.i.d. trials drawing
microstates from the Fubini–Study typicality measure on `Σ = ℂℙ¹`, the empirical
frequency of the moment-sublevel outcome region cut by `[ψ]` converges almost
surely to `‖⟨e₀, ψ⟩‖²`. Instantiating:

- `ψ = |+z⟩ = e₀`  ⟹  frequency → `1`   (`csd_sg_volume_certain`);
- `ψ` balanced (`⟨e₀,ψ⟩ = 1/√2`)  ⟹  frequency → `1/2`  (`csd_sg_volume_half`).

These are exactly the Stern-Gerlach predictions `P(+z | +z) = 1` and the canonical
`50/50` split (`|⟨+z|+x⟩|² = 1/2`).

**Not claimed (still LF4-todo §14).** Identifying the moment-sublevel region with
the physical "the `+z` (resp. `+x`) detector fired" measurement outcome is the
§14 observable correspondence, undischarged pre-LF5. This file derives the Born
*numbers* as Kähler volumes; it does not provide the operator → measurable-Σ-
function dictionary. The carved capstone (2) carries the same boundary.

## Experimental verification

- Stern, Gerlach 1922: *Z. Phys.* **9**, 349.
- Phipps, Taylor 1927: *Phys. Rev.* **29**, 309.
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace SternGerlachVolume

/-! ### The Born value as a first-coordinate amplitude -/

/-- For the fixed measurement outcome `e₀`, the Born amplitude squared is just the
zeroth-coordinate squared norm: `‖⟨e₀, ψ⟩‖² = ‖ψ₀‖²`. This is the value the
moment-volume frequency capstone lands on. -/
lemma normSq_inner_single_zero (ψ : EuclideanSpace ℂ (Fin 2)) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp 0‖ ^ 2 := by
  have h : (inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ : ℂ) = ψ.ofLp 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    simp [EuclideanSpace.single, Pi.star_apply]
  rw [h]

/-! ### A balanced single-qubit state (the `1/2` witness) -/

/-- The balanced unit vector `(1/√2)|0⟩ + (1/√2)|1⟩`, with `⟨e₀, balVec⟩ = 1/√2`.
Realises the canonical Stern-Gerlach `50/50` split. -/
noncomputable def balVec : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    + EuclideanSpace.single 1 (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

lemma balVec_ofLp_zero : balVec.ofLp 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [balVec, EuclideanSpace.single]

lemma balVec_ofLp_one : balVec.ofLp 1 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [balVec, EuclideanSpace.single]

lemma balVec_norm : ‖balVec‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, balVec_ofLp_zero, balVec_ofLp_one,
    Complex.norm_of_nonneg (show (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ by positivity)]
  rw [show (Real.sqrt 2)⁻¹ ^ 2 + (Real.sqrt 2)⁻¹ ^ 2 = 1 by
        rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      Real.sqrt_one]

lemma balVec_ne_zero : balVec ≠ 0 := by
  intro h
  have hz : ‖balVec‖ = 0 := by rw [h, norm_zero]
  rw [balVec_norm] at hz
  exact one_ne_zero hz

/-! ### The Stern-Gerlach Born values as derived volume frequencies -/

/-- **CSD Stern-Gerlach certainty as a derived Kähler-volume frequency.**
For i.i.d. trials drawing microstates from the Fubini–Study typicality measure on
`Σ = ℂℙ¹`, the empirical frequency of the moment-sublevel outcome region cut by
the `|+z⟩` ray converges almost surely to `1` — the `P(+z | +z) = 1` Born value.

The limit is `‖⟨e₀, e₀⟩‖² = 1`, with `volume = Born` *derived* from the moment
map (no carving), foundational triple only (no `busch_effect_gleason`). The
identification of the region with the physical `+z` outcome is LF4-todo §14. -/
theorem csd_sg_volume_certain
    (p₀ : CPN 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                momentMap (Projectivization.mk ℂ zPlusVec zPlusVec_ne_zero) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ zPlusVec zPlusVec_ne_zero) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (1 : ℝ)) := by
  have h := qubit_born_frequency_convergence_uncond p₀ zPlusVec
    zPlusVec_ne_zero zPlusVec_norm X hX hlaw hindep
  have hv : ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) zPlusVec‖ ^ 2 = 1 := by
    rw [normSq_inner_single_zero]
    simp [zPlusVec, EuclideanSpace.single]
  rwa [hv] at h

/-- **CSD Stern-Gerlach `50/50` split as a derived Kähler-volume frequency.**
For i.i.d. trials drawing microstates from the Fubini–Study typicality measure on
`Σ = ℂℙ¹`, the empirical frequency of the moment-sublevel outcome region cut by
the balanced ray `[balVec]` converges almost surely to `1/2` — the canonical
Stern-Gerlach split `|⟨+z | +x⟩|² = 1/2`.

The limit is `‖⟨e₀, balVec⟩‖² = ‖1/√2‖² = 1/2`, with `volume = Born` *derived*
from the moment map (no carving), foundational triple only (no
`busch_effect_gleason`). The identification of the region with the physical `+x`
outcome is LF4-todo §14. -/
theorem csd_sg_volume_half
    (p₀ : CPN 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                momentMap (Projectivization.mk ℂ balVec balVec_ne_zero) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤
                    momentMap (Projectivization.mk ℂ balVec balVec_ne_zero) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop (nhds (1 / 2 : ℝ)) := by
  have h := qubit_born_frequency_convergence_uncond p₀ balVec
    balVec_ne_zero balVec_norm X hX hlaw hindep
  have hv : ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) balVec‖ ^ 2 = 1 / 2 := by
    rw [normSq_inner_single_zero, balVec_ofLp_zero,
        Complex.norm_of_nonneg (show (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ by positivity),
        inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rwa [hv] at h

end SternGerlachVolume
end CSDBridge
end Empirical
end CSD
