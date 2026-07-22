/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.BornRegionUncond

/-!
# Empirical/CSD: GHZ three-qubit joint probabilities as derived Kähler-volume frequencies

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag, and **not** conditional on any preparation bundle).

The three-qubit (N = 8) surfacing of `LF4.born_frequency_convergence_N_uncond`
(the hpos-free form, since the 2026-06-11 migration) for the **GHZ state**
`(|000⟩ + |111⟩)/√2`, in the spirit of `Empirical/CSD/BellVolume.lean`.

## The genericity obstruction (resolved 2026-06-11)

The GHZ state is a **stabiliser state**: in every Pauli basis it is *sparse* (the
iconic all-`X` Mermin measurement gives four zero amplitudes). It is therefore a
**boundary point** of the probability simplex in those bases, and violates the
genericity hypothesis `hpos` (`∀ j, 0 < ‖⟨eⱼ,ψ⟩‖²`) of the conditional engine
`born_frequency_convergence_N`, which needs an interior point. That obstruction
was the historical reason this file's capstone carried `Φ ∈ (0, π)`; it is
**resolved** by the hpos-free engine (`LF4/BornRegionUncond.lean`,
`born_frequency_convergence_N_uncond`): zero-amplitude outcomes have FS-null
cells and frequencies converging to `0`, so the capstone now covers **every**
angle-sum `Φ`, the Mermin boundary values `Φ = 0, π` included.

The measured family is the **xy-plane product basis** at angle-sum
`Φ = φ₁+φ₂+φ₃`. There the eight joint amplitudes are
`(1/4)(1 + s₁s₂s₃ e^{-iΦ})` (up to a global phase, taken real here:
`cos(Φ/2)/2` on the four even-parity outcomes, `i·sin(Φ/2)/2` on the four odd),
with squared moduli

```
P_even = cos²(Φ/2)/4 = (1 + cos Φ)/8     P_odd = sin²(Φ/2)/4 = (1 − cos Φ)/8,
```

strictly positive iff `Φ ∈ (0, π)` (`ghzVec_hpos`, retained as the
interior-point fact). The three-point correlation is
`∑ s₁s₂s₃ · P_s = cos Φ` (`ghz_volume_correlation`).

The iconic Mermin values are the boundary points: `Φ = 0` gives `⟨XXX⟩ = +1`,
`Φ = π` gives `⟨XYY⟩ = ⟨YXY⟩ = ⟨YYX⟩ = −1` (the GHZ all-or-nothing
contradiction). At these sparse `cos Φ = ±1` points four of the eight cells are
FS-null; the capstone reaches them with the four surviving weights `1/4` and the
four null weights `0`.

## What is and is not claimed

**Derived (carving-free, Gleason-free, unconditional).** For **every** `Φ`, the
eight Born weights are the genuine Fubini–Study volumes of the barycentric moment
regions on `ℂℙ⁷`, and i.i.d. FS trials have frequencies converging a.s. to them.
No `busch_effect_gleason`, no carving, no preparation bundle, no genericity.

**Not claimed.** (i) The closed-form amplitudes are the physics input (cf. LF3
`cAmp`); identifying `ghzVec Φ` with the abstract GHZ state in the `Φ`-basis is
the amplitude identity, supplied by construction. (ii) Region → physical-outcome
labelling is LF4-todo §14.

## Experimental verification

- Greenberger, Horne, Zeilinger 1989; Mermin 1990: *Phys. Rev. Lett.* **65**,
  3373; Pan et al. 2000: *Nature* **403**, 515.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace GHZVolume

/-! ### Helpers -/

/-- Eight-term expansion of a sum over `Fin 8` (no `Fin.sum_univ_eight` in Mathlib). -/
lemma sum_univ_eight {M : Type*} [AddCommMonoid M] (f : Fin 8 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- `‖⟨eᵢ, ψ⟩‖² = ‖ψᵢ‖²` on `ℂℙ⁷`. -/
lemma normSq_inner_single (ψ : EuclideanSpace ℂ (Fin 8)) (i : Fin 8) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- `‖↑r‖² = r²`. -/
lemma realNormSq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `‖↑r · i‖² = r²`. -/
lemma imagNormSq (r : ℝ) : ‖((r : ℝ) : ℂ) * Complex.I‖ ^ 2 = r ^ 2 := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The GHZ amplitude vector on `ℂℙ⁷` (generic xy-plane basis) -/

/-- The GHZ state's eight joint amplitudes in the generic `Φ`-angle xy-plane
product basis, up to a global phase: `cos(Φ/2)/2` on the four even-parity outcomes
`{0,3,5,6}`, `i·sin(Φ/2)/2` on the four odd-parity outcomes `{1,2,4,7}`. -/
noncomputable def ghzVec (Φ : ℝ) : EuclideanSpace ℂ (Fin 8) :=
  EuclideanSpace.single 0 ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ)
    + EuclideanSpace.single 1 (((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I)
    + EuclideanSpace.single 2 (((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I)
    + EuclideanSpace.single 3 ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ)
    + EuclideanSpace.single 4 (((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I)
    + EuclideanSpace.single 5 ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ)
    + EuclideanSpace.single 6 ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ)
    + EuclideanSpace.single 7 (((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I)

lemma ghzVec_ofLp_zero (Φ : ℝ) :
    (ghzVec Φ).ofLp 0 = ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ) := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_one (Φ : ℝ) :
    (ghzVec Φ).ofLp 1 = ((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_two (Φ : ℝ) :
    (ghzVec Φ).ofLp 2 = ((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_three (Φ : ℝ) :
    (ghzVec Φ).ofLp 3 = ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ) := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_four (Φ : ℝ) :
    (ghzVec Φ).ofLp 4 = ((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_five (Φ : ℝ) :
    (ghzVec Φ).ofLp 5 = ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ) := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_six (Φ : ℝ) :
    (ghzVec Φ).ofLp 6 = ((Real.cos (Φ / 2) / 2 : ℝ) : ℂ) := by
  simp [ghzVec, EuclideanSpace.single]

lemma ghzVec_ofLp_seven (Φ : ℝ) :
    (ghzVec Φ).ofLp 7 = ((Real.sin (Φ / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  simp [ghzVec, EuclideanSpace.single]

/-! ### The eight Born weights -/

lemma born_value_zero (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.cos (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_zero, realNormSq]; ring

lemma born_value_one (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.sin (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_one, imagNormSq]; ring

lemma born_value_two (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 2 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.sin (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_two, imagNormSq]; ring

lemma born_value_three (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 3 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.cos (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_three, realNormSq]; ring

lemma born_value_four (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 4 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.sin (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_four, imagNormSq]; ring

lemma born_value_five (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 5 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.cos (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_five, realNormSq]; ring

lemma born_value_six (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 6 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.cos (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_six, realNormSq]; ring

lemma born_value_seven (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 7 (1 : ℂ)) (ghzVec Φ)‖ ^ 2 = Real.sin (Φ / 2) ^ 2 / 4 := by
  rw [normSq_inner_single, ghzVec_ofLp_seven, imagNormSq]; ring

/-! ### Norm, non-vanishing, genericity -/

lemma ghzVec_norm (Φ : ℝ) : ‖ghzVec Φ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  rw [sum_univ_eight (fun i => ‖(ghzVec Φ).ofLp i‖ ^ 2),
    ghzVec_ofLp_zero, ghzVec_ofLp_one, ghzVec_ofLp_two, ghzVec_ofLp_three,
    ghzVec_ofLp_four, ghzVec_ofLp_five, ghzVec_ofLp_six, ghzVec_ofLp_seven,
    realNormSq, imagNormSq]
  linear_combination Real.sin_sq_add_cos_sq (Φ / 2)

lemma ghzVec_ne_zero (Φ : ℝ) : ghzVec Φ ≠ 0 := by
  intro h
  have hz : ‖ghzVec Φ‖ = 0 := by rw [h, norm_zero]
  rw [ghzVec_norm] at hz
  exact one_ne_zero hz

/-- Genericity: for `Φ ∈ (0, π)` all eight Born weights are strictly positive
(`sin(Φ/2), cos(Φ/2) > 0`), so the conditional `born_frequency_convergence_N`
applies. No longer consumed by the capstone (it routes through the hpos-free
`born_frequency_convergence_N_uncond`); retained as the interior-point fact. -/
lemma ghzVec_hpos (Φ : ℝ) (hΦ : 0 < Φ ∧ Φ < Real.pi) :
    ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) (ghzVec Φ)‖ ^ 2 := by
  have hs : 0 < Real.sin (Φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hΦ.1]) (by linarith [hΦ.2, Real.pi_pos])
  have hc : 0 < Real.cos (Φ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hΦ.1, Real.pi_pos], by linarith [hΦ.2]⟩
  have hs2 := pow_pos hs 2
  have hc2 := pow_pos hc 2
  intro j
  fin_cases j
  · show 0 < ‖inner ℂ (EuclideanSpace.single (0 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_zero]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (1 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_one]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (2 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_two]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (3 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_three]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (4 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_four]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (5 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_five]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (6 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_six]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (7 : Fin 8) (1 : ℂ)) (ghzVec Φ)‖ ^ 2
    rw [born_value_seven]; linarith

/-! ### The GHZ volume-frequency capstone -/

/-- **CSD GHZ joint frequencies as derived Kähler-volume convergence.** For
**every** angle-sum `Φ` and i.i.d. trials drawing microstates from the Fubini–Study
typicality measure on the ontic `Σ = ℂℙ⁷`, the empirical frequencies of the eight
barycentric Born outcome regions converge, on a single almost-sure event, to the
GHZ joint Born weights `‖⟨eᵢ, ghzVec Φ⟩‖²`.

Carving-free, Gleason-free, unconditional — no `busch_effect_gleason`, no carved
regions, no preparation bundle, and (since the 2026-06-11 hpos migration) **no
angle restriction**: the iconic Mermin values `Φ = 0, π` are covered — their four
sparse outcomes' cells are FS-null with frequencies converging to `0` (see module
docstring). The amplitude values are the physics input; the
`volume = Born number` step is derived. -/
theorem ghz_born_frequency_volume
    (Φ : ℝ) (p₀ : CPN 8)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 8) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 8,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (ghzVec Φ) (ghzVec_ne_zero Φ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 8,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion (ghzVec Φ) (ghzVec_ne_zero Φ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (ghzVec Φ)‖ ^ 2)) :=
  born_frequency_convergence_N_uncond (M := 7) p₀ (ghzVec Φ) (ghzVec_ne_zero Φ)
    (ghzVec_norm Φ) X hX hlaw hindep

/-- **Recovered GHZ three-point correlation.** The parity-signed sum of the eight
volume-derived Born weights is `cos Φ`, the GHZ correlation
`⟨σ_{n₁} σ_{n₂} σ_{n₃}⟩ = cos(φ₁+φ₂+φ₃)`. Its boundary values `Φ = 0 ↦ +1`
(`⟨XXX⟩`) and `Φ = π ↦ −1` (`⟨XYY⟩`) are the Mermin all-or-nothing data. -/
theorem ghz_volume_correlation (Φ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 2 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      + ‖inner ℂ (EuclideanSpace.single 3 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 4 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      + ‖inner ℂ (EuclideanSpace.single 5 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      + ‖inner ℂ (EuclideanSpace.single 6 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 7 (1 : ℂ)) (ghzVec Φ)‖ ^ 2
      = Real.cos Φ := by
  rw [born_value_zero, born_value_one, born_value_two, born_value_three,
    born_value_four, born_value_five, born_value_six, born_value_seven]
  have hc : Real.cos Φ = 2 * Real.cos (Φ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (Φ / 2); rwa [show 2 * (Φ / 2) = Φ by ring] at h
  have h2 := Real.sin_sq_add_cos_sq (Φ / 2)
  linarith

end GHZVolume
end CSDBridge
end Empirical
end CSD
