/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.ContextVolume
public import CsdLean4.LF4.TrialWitness

/-!
# Empirical/CSD: qubit observable variance as a product of Fubini–Study volumes

**Category:** 3-Local (CSD-ontic layer; genuine volume composition, not a
transport tag).

The CSD volume-ratio twin of `Empirical/QM/Uncertainty.lean`'s
`robertson_uncertainty`. The QM-validity file gives the Robertson inequality
`Var_ψ(A)·Var_ψ(B) ≥ ¼|⟨ψ,[A,B]ψ⟩|²` as pure inner-product geometry, with no
ontic reading of the variance itself. This file supplies the missing twin: for a
`±1`-valued qubit observable, the **variance is a product of two Fubini–Study
typicality volumes** on the ontic `Σ = ℂℙ¹`.

## The reading

A `±1`-valued qubit observable `O` measured in an orthonormal context
`B : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))` has two outcomes,
with Born weights `p₊ = ‖⟨B 0, ψ⟩‖²`, `p₋ = ‖⟨B 1, ψ⟩‖²`. By
`ContextVolume.context_born_frequency_volume` (M = 1) these are genuine
Fubini–Study typicality volumes on `Σ = ℂℙ¹`, derived (carving-free,
Gleason-free) from the Kähler moment map; and `p₊ + p₋ = 1` by Parseval. The
variance of a `±1` observable is

  `Var = ⟨O²⟩ − ⟨O⟩² = 1 − (p₊ − p₋)² = 4·p₊·p₋`

(`⟨O²⟩ = 1` because `O² = I`, `⟨O⟩ = p₊ − p₋`). So **the spread is the product
of the two ontic typicality volumes** `4·vol₊·vol₋` — the CSD volume-ratio
account of "uncertainty / spread" for a single qubit observable.

`varFromVolume p := 4·p·(1−p)` is this variance as a function of the `+` volume.
`variance_eq_four_vol_product` is the headline `Var = 4·vol₊·vol₋`;
`varFromVolume_eq_centered_moment` exhibits the `⟨O²⟩ − ⟨O⟩²` reading
`varFromVolume p = 1 − (p − (1−p))²`. `uncertainty_volume_frequency` is the
frequency capstone: the variance computed from the empirical finite-sample
frequencies (`4·freq₊(m)·freq₋(m)`) converges almost surely to the volume-product
variance, so the spread is *grounded in ontic typicality volumes*, not assumed.

## What is and is not claimed

**Derived (Lean-checked, carving-free, Gleason-free).** The `±` Born weights are
Fubini–Study typicality volumes on `Σ = ℂℙ¹` (composing the qubit Born-volume
engine `ContextVolume.context_born_frequency_volume` at M = 1), and the variance
is their product `4·vol₊·vol₋`. Foundational triple only (no
`busch_effect_gleason`).

**Not re-proved here.** The Robertson *inequality*
`Var(A)·Var(B) ≥ ¼|⟨[A,B]⟩|²` itself stays at the QM-validity layer
(`Empirical/QM/Uncertainty.lean`, `robertson_uncertainty`); it is an
inner-product Cauchy–Schwarz fact, not a volume identity. This file grounds the
two single-observable variances entering that inequality as FS-volume products;
substituting them into `robertson_uncertainty` reads the bound as an inequality
between products of FS typicality volumes, with no new volume content needed.

**Realisation not derivation (Tier-2).** As with the rest of the `*Volume`
series, `Φ = id` in the underlying `SectorData`; the FS regions are carved in the
rotated frame `B.repr ψ`. The identification of the moment regions with the
physical "the `+` detector fired" outcome is LF4-todo §14.

## Source

Robertson 1929, *Phys. Rev.* **34**, 163 (the QM-layer inequality). The
variance-as-volume-product reading is the CSD-ontic surfacing of the qubit
Born-volume engine (`LF4.born_frequency_convergence_N` / the moment-map cluster).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace UncertaintyVolume

/-! ### The variance-from-volume function and its algebra -/

/-- The variance of a `±1`-valued qubit observable as a function of its `+`
outcome Fubini–Study volume `p`: `varFromVolume p := 4·p·(1−p)`. -/
def varFromVolume (p : ℝ) : ℝ := 4 * p * (1 - p)

/-- **The `⟨O²⟩ − ⟨O⟩²` reading.** For a `±1`-valued observable with `+` weight
`p` (so `−` weight `1 − p`), the variance `varFromVolume p` equals
`1 − (p − (1 − p))²`: the second-moment minus mean-squared form, with
`⟨O²⟩ = 1` (since `O² = I`) and `⟨O⟩ = p − (1 − p) = p₊ − p₋`. -/
lemma varFromVolume_eq_centered_moment (p : ℝ) :
    varFromVolume p = 1 - (p - (1 - p)) ^ 2 := by
  unfold varFromVolume; ring

/-- **Variance as a product of two typicality volumes.** Given two
Fubini–Study volumes `vol₊`, `vol₋` summing to one (the two outcome Born weights
of a `±1` qubit observable, normalised by Parseval), the variance
`varFromVolume vol₊` equals their product `4·vol₊·vol₋`. This is the CSD
volume-ratio account of observable spread: `Var = 4·vol₊·vol₋`. -/
theorem variance_eq_four_vol_product (volp volm : ℝ) (h : volp + volm = 1) :
    varFromVolume volp = 4 * volp * volm := by
  have hm : volm = 1 - volp := by linarith
  subst hm
  unfold varFromVolume; ring

/-! ### The two qubit Born weights are FS volumes summing to one (Parseval) -/

/-- The two qubit context Born weights `‖⟨B 0, ψ⟩‖²`, `‖⟨B 1, ψ⟩‖²` sum to one
for a unit preparation (squared-norm Parseval over the orthonormal basis,
`OrthonormalBasis.sum_sq_norm_inner_right`). These are the two Fubini–Study
typicality volumes whose product is the variance. -/
lemma context_vol_sum_two
    (B : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    ‖inner ℂ (B 0) ψ‖ ^ 2 + ‖inner ℂ (B 1) ψ‖ ^ 2 = 1 := by
  have h := B.sum_sq_norm_inner_right ψ
  rw [Fin.sum_univ_two, hψ, one_pow] at h
  exact h

/-- **Born-tied headline: variance = product of the two FS Born volumes.** For a
`±1` qubit observable measured in context `B` on a unit preparation `ψ`, the
variance `varFromVolume (‖⟨B 0, ψ⟩‖²)` equals the product of the two outcome
Fubini–Study typicality volumes `4·‖⟨B 0, ψ⟩‖²·‖⟨B 1, ψ⟩‖²`. Composes
`variance_eq_four_vol_product` with the Parseval normalisation
`context_vol_sum_two`. -/
theorem born_variance_eq_vol_product
    (B : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    varFromVolume (‖inner ℂ (B 0) ψ‖ ^ 2)
      = 4 * ‖inner ℂ (B 0) ψ‖ ^ 2 * ‖inner ℂ (B 1) ψ‖ ^ 2 :=
  variance_eq_four_vol_product _ _ (context_vol_sum_two B ψ hψ)

/-! ### The variance-as-volume-product frequency capstone -/

/-- **CSD uncertainty as a product of derived Kähler-volume frequencies.** For
i.i.d. trials drawing microstates from the Fubini–Study typicality measure on the
ontic `Σ = ℂℙ¹`, the variance of a `±1` qubit observable computed from the
empirical finite-sample frequencies `4·freq₊(m)·freq₋(m)` converges almost surely
to the volume-product variance `varFromVolume (‖⟨B 0, ψ⟩‖²) = 4·vol₊·vol₋`.

So the observable spread is **grounded in ontic typicality volumes** on
`Σ = ℂℙ¹`, not assumed: each outcome frequency converges to a Fubini–Study
typicality volume (`ContextVolume.context_born_frequency_volume`, M = 1,
carving-free and Gleason-free), and their `4·(·)·(·)` product converges to the
variance by continuity of multiplication. Foundational triple only (no
`busch_effect_gleason`); the Robertson inequality itself stays at the QM-validity
layer (`Empirical/QM/Uncertainty.lean`). -/
theorem uncertainty_volume_frequency
    (p₀ : CPN 2)
    (B : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 2,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (B.repr ψ)
                (ContextVolume.repr_ne_zero (M := 1) B ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          4 * (((∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion (B.repr ψ)
                      (ContextVolume.repr_ne_zero (M := 1) B ψ hψ) 0)
                    (fun _ => (1 : ℝ)) ω) / (m : ℝ))
              * ((∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion (B.repr ψ)
                      (ContextVolume.repr_ne_zero (M := 1) B ψ hψ) 1)
                    (fun _ => (1 : ℝ)) ω) / (m : ℝ))))
        atTop
        (nhds (varFromVolume (‖inner ℂ (B 0) ψ‖ ^ 2))) := by
  have h := ContextVolume.context_born_frequency_volume (M := 1) p₀ B ψ hψ X hX hlaw hindep
  filter_upwards [h] with ω hω
  have hmul := ((hω 0).mul (hω 1)).const_mul (4 : ℝ)
  have hval : (4 : ℝ) * (‖inner ℂ (B 0) ψ‖ ^ 2 * ‖inner ℂ (B 1) ψ‖ ^ 2)
      = varFromVolume (‖inner ℂ (B 0) ψ‖ ^ 2) := by
    rw [variance_eq_four_vol_product _ _ (context_vol_sum_two B ψ hψ)]; ring
  rw [hval] at hmul
  exact hmul

/-- `uncertainty_volume_frequency` on the canonical i.i.d. Fubini–Study process
(`fsTrialMeasure` / `fsTrial`), so the hypothesis set is Lean-inhabited, not
merely classically satisfiable. The region family is the rotated-basis cell
`bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ)`. -/
theorem uncertainty_volume_frequency_canonical
    (p₀ : CPN 2)
    (B : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          4 * (((∑ k ∈ Finset.range m,
                  Set.indicator ((fsTrial 2 k) ⁻¹' bornRegion (B.repr ψ)
                      (ContextVolume.repr_ne_zero (M := 1) B ψ hψ) 0)
                    (fun _ => (1 : ℝ)) ω) / (m : ℝ))
              * ((∑ k ∈ Finset.range m,
                  Set.indicator ((fsTrial 2 k) ⁻¹' bornRegion (B.repr ψ)
                      (ContextVolume.repr_ne_zero (M := 1) B ψ hψ) 1)
                    (fun _ => (1 : ℝ)) ω) / (m : ℝ))))
        atTop
        (nhds (varFromVolume (‖inner ℂ (B 0) ψ‖ ^ 2))) :=
  uncertainty_volume_frequency p₀ B ψ hψ
    (fsTrial 2) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (B.repr ψ) (ContextVolume.repr_ne_zero (M := 1) B ψ hψ))
      (bornRegion_measurable_uncond (B.repr ψ) (ContextVolume.repr_ne_zero (M := 1) B ψ hψ)))

end UncertaintyVolume
end CSDBridge
end Empirical
end CSD
