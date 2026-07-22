/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.BornFrequencyN
import CsdLean4.Empirical.QM.Hardy

/-!
# Empirical/CSD: Hardy's probability as a derived Kähler-volume frequency

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag, and **not** conditional on any preparation bundle).

The two-qubit (N = 4) surfacing of `LF4.born_frequency_convergence_N` for the
**Hardy state** at the golden-ratio maximum, in the spirit of
`Empirical/CSD/BellVolume.lean` and `Empirical/CSD/GHZVolume.lean`.

## What this adds over the QM layer

`Empirical/QM/Hardy.lean` closes the Hardy *paradox*: no LHV distribution
satisfies the four Hardy constraints (`no_lhv_hardy`), QM realises them
(`exists_hardy_realisation_max`), and the maximal Hardy probability is the
closed-form `(5√5 − 11)/2 ≈ 9.017 %` (`hardyMax_probability_eq`). That number is
an *inner-product* Born value. This file **derives the same number as a genuine
Fubini–Study typicality volume** on the ontic `Σ = ℂℙ³`: carving-free,
Gleason-free, unconditional.

## The interior-point property (no boundary obstruction)

Unlike the GHZ state — a stabiliser state that is sparse in its Mermin bases and
therefore a *boundary* point of the probability simplex (`GHZVolume.lean`) — the
golden-ratio Hardy state

```
|ψ_max⟩ ∝ |00⟩ + √φ |01⟩ + √φ |10⟩ − φ² |11⟩       (φ = (1+√5)/2)
```

has **all four** computational-basis amplitudes nonzero. Its Born weights

```
P_00 = 1/(5φ+3) = (5√5−11)/2,   P_01 = P_10 = φ/(5φ+3),   P_11 = φ⁴/(5φ+3),
```

are all strictly positive, so the Hardy state is an *interior* point of the
3-simplex and the genericity hypothesis `hpos` of `born_frequency_convergence_N`
holds outright — no `Φ ∈ (0,π)` carve-out is needed, the full Hardy instance is
covered. `P_00` is exactly the Hardy probability the experiment measures.

## What is and is not claimed

**Derived (carving-free, Gleason-free, unconditional).** The four Born weights
are the genuine Fubini–Study volumes of the barycentric moment regions on `ℂℙ³`,
and i.i.d. FS trials have frequencies converging a.s. to them. In particular the
Hardy probability `(5√5 − 11)/2` is a Kähler volume. No `busch_effect_gleason`,
no carving, no preparation bundle.

**Not claimed.** (i) The closed-form amplitudes are the physics input (cf. LF3
`cAmp`, `BellVolume`); identifying `hardyVolVec` with the abstract Hardy state in
the computational basis is the amplitude identity, supplied by construction —
the amplitudes here are exactly those of `QM/Hardy.lean`'s `hardyMaxVec`,
normalised. (ii) Region → physical-outcome labelling is LF4-todo §14. The LHV
impossibility itself lives in `QM/Hardy.lean`.

## Experimental verification

- Hardy 1993: *Phys. Rev. Lett.* **71**, 1665; Lundeen, Steinberg 2009:
  *Phys. Rev. Lett.* **102**, 020404 (weak-measurement confirmation).
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization
open CSD.Empirical.Hardy.HardyQMMax

namespace CSD
namespace Empirical
namespace CSDBridge
namespace HardyVolume

/-! ### Helpers (file-local, mirroring `GHZVolume.lean`) -/

/-- `‖⟨eᵢ, ψ⟩‖² = ‖ψᵢ‖²` on `ℂℙ³`. -/
private lemma normSq_inner_single (ψ : EuclideanSpace ℂ (Fin 4)) (i : Fin 4) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- `‖↑r‖² = r²`. -/
private lemma realNormSq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The normalising constant `nrm = √(5φ+3)` -/

/-- `5φ + 3 > 0` (the squared norm of the golden-ratio Hardy state). -/
private lemma denom_pos : (0 : ℝ) < 5 * phi + 3 := by nlinarith [phi_pos]

/-- The normalisation `nrm = √(5φ+3) = ‖ψ_max‖`. -/
noncomputable def nrm : ℝ := Real.sqrt (5 * phi + 3)

private lemma nrm_pos : 0 < nrm := Real.sqrt_pos.mpr denom_pos

private lemma nrm_sq : nrm ^ 2 = 5 * phi + 3 := Real.sq_sqrt denom_pos.le

/-! ### The normalised golden-ratio Hardy state on `ℂℙ³` -/

/-- The golden-ratio Hardy state, normalised onto `Fin 4 ↔ (Fin 2 × Fin 2)`:
amplitudes `(1, √φ, √φ, −φ²)/√(5φ+3)`. These are exactly the amplitudes of
`QM/Hardy.lean`'s `hardyMaxVec`, divided by `‖ψ_max‖ = √(5φ+3)`. -/
noncomputable def hardyVolVec : EuclideanSpace ℂ (Fin 4) :=
  EuclideanSpace.single 0 ((1 / nrm : ℝ) : ℂ)
    + EuclideanSpace.single 1 ((sqrtPhi / nrm : ℝ) : ℂ)
    + EuclideanSpace.single 2 ((sqrtPhi / nrm : ℝ) : ℂ)
    + EuclideanSpace.single 3 ((-(phi ^ 2) / nrm : ℝ) : ℂ)

lemma hardyVolVec_ofLp_zero : (hardyVolVec).ofLp 0 = ((1 / nrm : ℝ) : ℂ) := by
  simp [hardyVolVec, EuclideanSpace.single]

lemma hardyVolVec_ofLp_one : (hardyVolVec).ofLp 1 = ((sqrtPhi / nrm : ℝ) : ℂ) := by
  simp [hardyVolVec, EuclideanSpace.single]

lemma hardyVolVec_ofLp_two : (hardyVolVec).ofLp 2 = ((sqrtPhi / nrm : ℝ) : ℂ) := by
  simp [hardyVolVec, EuclideanSpace.single]

lemma hardyVolVec_ofLp_three : (hardyVolVec).ofLp 3 = ((-(phi ^ 2) / nrm : ℝ) : ℂ) := by
  simp [hardyVolVec, EuclideanSpace.single]

/-! ### The four Born weights -/

lemma born_value_zero :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) hardyVolVec‖ ^ 2 = 1 / (5 * phi + 3) := by
  rw [normSq_inner_single, hardyVolVec_ofLp_zero, realNormSq, div_pow, one_pow, nrm_sq]

lemma born_value_one :
    ‖inner ℂ (EuclideanSpace.single 1 (1 : ℂ)) hardyVolVec‖ ^ 2 = phi / (5 * phi + 3) := by
  rw [normSq_inner_single, hardyVolVec_ofLp_one, realNormSq, div_pow, sqrtPhi_sq, nrm_sq]

lemma born_value_two :
    ‖inner ℂ (EuclideanSpace.single 2 (1 : ℂ)) hardyVolVec‖ ^ 2 = phi / (5 * phi + 3) := by
  rw [normSq_inner_single, hardyVolVec_ofLp_two, realNormSq, div_pow, sqrtPhi_sq, nrm_sq]

lemma born_value_three :
    ‖inner ℂ (EuclideanSpace.single 3 (1 : ℂ)) hardyVolVec‖ ^ 2
      = (phi ^ 2) ^ 2 / (5 * phi + 3) := by
  rw [normSq_inner_single, hardyVolVec_ofLp_three, realNormSq, div_pow, neg_sq, nrm_sq]

/-! ### Norm, non-vanishing, genericity -/

lemma hardyVolVec_norm : ‖hardyVolVec‖ = 1 := by
  have hne : (5 * phi + 3 : ℝ) ≠ 0 := ne_of_gt denom_pos
  rw [EuclideanSpace.norm_eq, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  rw [Fin.sum_univ_four,
    ← normSq_inner_single hardyVolVec 0, ← normSq_inner_single hardyVolVec 1,
    ← normSq_inner_single hardyVolVec 2, ← normSq_inner_single hardyVolVec 3,
    born_value_zero, born_value_one, born_value_two, born_value_three,
    show (1 : ℝ) / (5 * phi + 3) + phi / (5 * phi + 3) + phi / (5 * phi + 3)
        + (phi ^ 2) ^ 2 / (5 * phi + 3)
        = (1 + phi + phi + (phi ^ 2) ^ 2) / (5 * phi + 3) from by ring,
    div_eq_iff hne]
  linear_combination (phi ^ 2 + phi + 2) * phi_sq

lemma hardyVolVec_ne_zero : hardyVolVec ≠ 0 := by
  intro h
  have hz : ‖hardyVolVec‖ = 0 := by rw [h, norm_zero]
  rw [hardyVolVec_norm] at hz
  exact one_ne_zero hz

/-- Genericity: all four Born weights are strictly positive (the Hardy state is an
interior point of the 3-simplex), so `born_frequency_convergence_N` applies with no
boundary carve-out. -/
lemma hardyVolVec_hpos :
    ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) hardyVolVec‖ ^ 2 := by
  have hden : (0 : ℝ) < 5 * phi + 3 := denom_pos
  intro j
  fin_cases j
  · show 0 < ‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) hardyVolVec‖ ^ 2
    rw [born_value_zero]; exact div_pos one_pos hden
  · show 0 < ‖inner ℂ (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) hardyVolVec‖ ^ 2
    rw [born_value_one]; exact div_pos phi_pos hden
  · show 0 < ‖inner ℂ (EuclideanSpace.single (2 : Fin 4) (1 : ℂ)) hardyVolVec‖ ^ 2
    rw [born_value_two]; exact div_pos phi_pos hden
  · show 0 < ‖inner ℂ (EuclideanSpace.single (3 : Fin 4) (1 : ℂ)) hardyVolVec‖ ^ 2
    rw [born_value_three]; exact div_pos (pow_pos (pow_pos phi_pos 2) 2) hden

/-! ### The Hardy volume-frequency capstone -/

/-- **Hardy's maximal probability as a derived Kähler volume.** The `|00⟩`
computational-basis Born weight of the golden-ratio Hardy state — the quantity the
Hardy experiment measures — equals the closed-form maximum `(5√5 − 11)/2 ≈
9.017 %`, here obtained as a genuine Fubini–Study typicality volume on the ontic
`Σ = ℂℙ³` (via `born_value_zero` + `QM/Hardy.lean`'s `hardyMax_value`). -/
theorem hardy_max_volume_probability :
    ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) hardyVolVec‖ ^ 2
      = (5 * Real.sqrt 5 - 11) / 2 := by
  rw [born_value_zero]; exact hardyMax_value

/-- **CSD Hardy joint frequencies as derived Kähler-volume convergence.** For
i.i.d. trials drawing microstates from the Fubini–Study typicality measure on the
ontic `Σ = ℂℙ³`, the empirical frequencies of the four barycentric Born outcome
regions converge, on a single almost-sure event, to the golden-ratio Hardy state's
joint Born weights `‖⟨eᵢ, hardyVolVec⟩‖²` — the `i = 0` coordinate of which is
Hardy's maximal probability `(5√5 − 11)/2` (`hardy_max_volume_probability`).

Carving-free, Gleason-free, unconditional — no `busch_effect_gleason`, no carved
regions, no preparation bundle. The amplitude values are the physics input; the
`volume = Born number` step is derived. -/
theorem hardy_max_born_frequency_volume
    (p₀ : CPN 4)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion hardyVolVec hardyVolVec_ne_zero i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion hardyVolVec hardyVolVec_ne_zero i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) hardyVolVec‖ ^ 2)) :=
  born_frequency_convergence_N (M := 3) p₀ hardyVolVec hardyVolVec_ne_zero
    hardyVolVec_norm hardyVolVec_hpos X hX hlaw hindep

end HardyVolume
end CSDBridge
end Empirical
end CSD
