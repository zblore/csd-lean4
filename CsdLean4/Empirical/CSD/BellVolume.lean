import CsdLean4.LF4.BornRegionUncond

/-!
# Empirical/CSD: Bell singlet joint probabilities as derived Kähler-volume frequencies

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag, and **not** conditional on the undischarged
`PureSingletPreparation` bundle).

The two-qubit (N = 4) surfacing of the general-`N` Born-from-Kähler-volume
capstone `LF4.born_frequency_convergence_N_uncond` (the hpos-free form, since the
2026-06-11 migration) for the **Bell singlet**. Where
`Empirical/CSD/Bell.lean`'s `bell_singlet_frequency_convergence*` are conditional
on the undischarged `PureSingletPreparation` bundle (LF4-todo §2/§3/§7) and where
`LF4/SingletObservables.lean` works with sector regions **carved** to volume
`P_st` (Tier-2), this file lands the singlet's four joint-outcome probabilities as
genuine **Fubini–Study volumes** on the ontic `Σ = ℂℙ³`, derived via the
Duistermaat–Heckman theorem, carving-free and Gleason-free, and unconditional.

## Construction

For detectors at relative angle `θ` (so `a · b = cos θ`), the singlet's four joint
spin amplitudes in the product measurement eigenbasis `{u_z^s ⊗ u_θ^t}` are, in
closed form,

```
⟨u_z^+ ⊗ u_θ^+, singlet⟩ = sin(θ/2)/√2     ⟨u_z^+ ⊗ u_θ^-, singlet⟩ =  cos(θ/2)/√2
⟨u_z^- ⊗ u_θ^+, singlet⟩ = -cos(θ/2)/√2    ⟨u_z^- ⊗ u_θ^-, singlet⟩ =  sin(θ/2)/√2
```

`bellSingletVec θ` is the vector of these amplitudes on `Fin 4 ↔ (s,t)`. Its four
computational-basis Born weights are the singlet joint probabilities

```
P_{++} = P_{--} = sin²(θ/2)/2 = (1 − cos θ)/4
P_{+-} = P_{-+} = cos²(θ/2)/2 = (1 + cos θ)/4,
```

and `∑ st·P_st = −cos θ` recovers the singlet correlation `⟨σ_a σ_b⟩ = −a·b`
(`bell_singlet_volume_correlation`).

## What is and is not claimed

**Derived (Lean-checked, carving-free, Gleason-free, unconditional).** The four
Born weights are the genuine Fubini–Study volumes of the barycentric moment
regions on `ℂℙ³` (`born_frequency_convergence_N_uncond` via
`fs_born_volume_ratio_N_uncond`), and i.i.d. Fubini–Study trials have outcome
frequencies converging a.s. to them — at **every** relative angle `θ`, the
aligned / anti-aligned boundary values `θ = 0, π` included (hpos-free since the
2026-06-11 migration onto `LF4/BornRegionUncond.lean`; the vanishing-amplitude
outcomes' cells are FS-null). No `busch_effect_gleason`, no carving, no
`PureSingletPreparation` bundle.

**Not claimed.** (i) The closed-form amplitudes above are the physics input (the
known singlet inner products, defined directly — cf. LF3's `cAmp`); identifying
`bellSingletVec θ` with the abstract singlet measured at relative angle `θ` is the
LF4-todo §3 amplitude identity, here supplied by construction rather than derived
from an abstract singlet object. (ii) The moment-region → physical-detector-outcome
labelling is LF4-todo §14. The genuine, derived content is `volume = Born number`.

## Experimental verification

- Bell 1964: *Physics* **1**, 195; Aspect, Grangier, Roger 1982:
  *Phys. Rev. Lett.* **49**, 91; loophole-free: Hensen 2015, Giustina 2015,
  Shalm 2015.
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace BellVolume

/-! ### Reusable amplitude helpers -/

/-- `‖⟨eᵢ, ψ⟩‖² = ‖ψᵢ‖²` on `ℂℙ³` (the fixed-outcome Born amplitude is the `i`-th
coordinate squared norm). -/
private lemma normSq_inner_single (ψ : EuclideanSpace ℂ (Fin 4)) (i : Fin 4) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 := by
  have h : inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ = ψ.ofLp i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_four]
    fin_cases i <;> simp [EuclideanSpace.single, Pi.star_apply]
  rw [h]

/-- `‖↑(r/√2)‖² = r²/2`. -/
private lemma normSq_ofReal_div_sqrt2 (r : ℝ) :
    ‖((r / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = r ^ 2 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-! ### The singlet amplitude vector on `ℂℙ³` -/

/-- The singlet's four joint amplitudes in the `(z, θ)` product measurement
eigenbasis, as a vector on `Fin 4 ↔ (s,t)`. -/
noncomputable def bellSingletVec (θ : ℝ) : EuclideanSpace ℂ (Fin 4) :=
  EuclideanSpace.single 0 ((Real.sin (θ / 2) / Real.sqrt 2 : ℝ) : ℂ)
    + EuclideanSpace.single 1 ((Real.cos (θ / 2) / Real.sqrt 2 : ℝ) : ℂ)
    + EuclideanSpace.single 2 (((-Real.cos (θ / 2)) / Real.sqrt 2 : ℝ) : ℂ)
    + EuclideanSpace.single 3 ((Real.sin (θ / 2) / Real.sqrt 2 : ℝ) : ℂ)

lemma bellSingletVec_ofLp_zero (θ : ℝ) :
    (bellSingletVec θ).ofLp 0 = ((Real.sin (θ / 2) / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [bellSingletVec, EuclideanSpace.single]

lemma bellSingletVec_ofLp_one (θ : ℝ) :
    (bellSingletVec θ).ofLp 1 = ((Real.cos (θ / 2) / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [bellSingletVec, EuclideanSpace.single]

lemma bellSingletVec_ofLp_two (θ : ℝ) :
    (bellSingletVec θ).ofLp 2 = (((-Real.cos (θ / 2)) / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [bellSingletVec, EuclideanSpace.single]

lemma bellSingletVec_ofLp_three (θ : ℝ) :
    (bellSingletVec θ).ofLp 3 = ((Real.sin (θ / 2) / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [bellSingletVec, EuclideanSpace.single]

/-! ### The four Born weights (component form) -/

/-- `P_{++}` Born weight: `sin²(θ/2)/2`. -/
lemma born_value_zero (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = Real.sin (θ / 2) ^ 2 / 2 := by
  rw [normSq_inner_single, bellSingletVec_ofLp_zero, normSq_ofReal_div_sqrt2]

/-- `P_{+-}` Born weight: `cos²(θ/2)/2`. -/
lemma born_value_one (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = Real.cos (θ / 2) ^ 2 / 2 := by
  rw [normSq_inner_single, bellSingletVec_ofLp_one, normSq_ofReal_div_sqrt2]

/-- `P_{-+}` Born weight: `cos²(θ/2)/2`. -/
lemma born_value_two (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 2 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = Real.cos (θ / 2) ^ 2 / 2 := by
  rw [normSq_inner_single, bellSingletVec_ofLp_two, normSq_ofReal_div_sqrt2]
  ring

/-- `P_{--}` Born weight: `sin²(θ/2)/2`. -/
lemma born_value_three (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 3 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = Real.sin (θ / 2) ^ 2 / 2 := by
  rw [normSq_inner_single, bellSingletVec_ofLp_three, normSq_ofReal_div_sqrt2]

/-! ### The `P_st = (1 ∓ cos θ)/4` closed forms (recognisable singlet kernel) -/

private lemma sin_half_sq (θ : ℝ) : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at h
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  linarith

private lemma cos_half_sq (θ : ℝ) : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- `P_{++} = P_{--} = (1 − cos θ)/4`. -/
lemma born_value_pst_minus (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = (1 - Real.cos θ) / 4 := by
  rw [born_value_zero, sin_half_sq]; ring

/-- `P_{+-} = P_{-+} = (1 + cos θ)/4`. -/
lemma born_value_pst_plus (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = (1 + Real.cos θ) / 4 := by
  rw [born_value_one, cos_half_sq]; ring

/-! ### Norm, non-vanishing, genericity -/

lemma bellSingletVec_norm (θ : ℝ) : ‖bellSingletVec θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  simp only [Fin.sum_univ_four, bellSingletVec_ofLp_zero, bellSingletVec_ofLp_one,
    bellSingletVec_ofLp_two, bellSingletVec_ofLp_three, normSq_ofReal_div_sqrt2]
  linear_combination Real.sin_sq_add_cos_sq (θ / 2)

lemma bellSingletVec_ne_zero (θ : ℝ) : bellSingletVec θ ≠ 0 := by
  intro h
  have hz : ‖bellSingletVec θ‖ = 0 := by rw [h, norm_zero]
  rw [bellSingletVec_norm] at hz
  exact one_ne_zero hz

/-- Genericity: for `θ ∈ (0, π)` all four Born weights are strictly positive
(`sin(θ/2), cos(θ/2) > 0`), so the conditional `born_frequency_convergence_N`
applies. No longer consumed by the capstone (it routes through the hpos-free
`born_frequency_convergence_N_uncond`); retained as the interior-point fact. -/
lemma bellSingletVec_hpos (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi) :
    ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) (bellSingletVec θ)‖ ^ 2 := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hs2 := pow_pos hs 2
  have hc2 := pow_pos hc 2
  intro j
  fin_cases j
  · show 0 < ‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
    rw [born_value_zero]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
    rw [born_value_one]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (2 : Fin 4) (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
    rw [born_value_two]; linarith
  · show 0 < ‖inner ℂ (EuclideanSpace.single (3 : Fin 4) (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
    rw [born_value_three]; linarith

/-! ### The Bell singlet volume-frequency capstone -/

/-- **CSD Bell singlet joint frequencies as derived Kähler-volume convergence.**
For detectors at **any** relative angle `θ` and i.i.d. trials drawing microstates
from the Fubini–Study typicality measure on the ontic `Σ = ℂℙ³`, the empirical
frequencies of the four barycentric Born outcome regions converge, on a single
almost-sure event, to the singlet joint Born weights `‖⟨eᵢ, bellSingletVec θ⟩‖²`
(equal to `(1 ∓ cos θ)/4`, see `born_value_pst_minus/plus`).

Carving-free, Gleason-free, **unconditional** — no `busch_effect_gleason`, no
carved sector regions, no `PureSingletPreparation` bundle, and (since the
2026-06-11 hpos migration) **no angle restriction**: the aligned / anti-aligned
boundary values `θ = 0, π`, where two of the four amplitudes vanish, are covered
— their cells are FS-null and their frequencies converge to `0`. The genuine
upgrade over `Empirical/CSD/Bell.lean`'s bundle-conditional capstones and over
`LF4/SingletObservables.lean`'s carved sector identities. The amplitude values
are the physics input; the `volume = Born number` step is derived. -/
theorem bell_singlet_born_frequency_volume
    (θ : ℝ) (p₀ : CPN 4)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (bellSingletVec θ) (bellSingletVec_ne_zero θ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion (bellSingletVec θ) (bellSingletVec_ne_zero θ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (bellSingletVec θ)‖ ^ 2)) :=
  born_frequency_convergence_N_uncond (M := 3) p₀ (bellSingletVec θ)
    (bellSingletVec_ne_zero θ) (bellSingletVec_norm θ) X hX hlaw hindep

/-- **Recovered singlet correlation.** The signed sum of the four volume-derived
Born weights is `−cos θ = −a·b`, the singlet two-point correlation
`⟨σ_a ⊗ σ_b⟩`. Ties the volume capstone to the Bell/CHSH content. -/
theorem bell_singlet_volume_correlation (θ : ℝ) :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      - ‖inner ℂ (EuclideanSpace.single 2 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      + ‖inner ℂ (EuclideanSpace.single 3 (1 : ℂ)) (bellSingletVec θ)‖ ^ 2
      = - Real.cos θ := by
  rw [born_value_zero, born_value_one, born_value_two, born_value_three]
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at h
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  linarith

end BellVolume
end CSDBridge
end Empirical
end CSD
