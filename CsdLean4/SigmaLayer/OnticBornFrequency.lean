/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.MeasureBridge
public import CsdLean4.LF4.BornRegionDisjoint
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF1.GeneralFrequency

/-!
# SigmaLayer/OnticBornFrequency: Born as an ontic typicality volume (connectivity, G1)

**Category:** 7-SigmaLayer (grounding the Born frequency in the ontic typicality).

The general-`N` Born-frequency capstone `LF4/BornFrequencyN.lean` samples the **projective** measure
`μ_FS` on `ℂℙⁿ⁻¹` directly (`hlaw : map Xₙ = fubiniStudyMeasure`). That is the *epistemic* law, and
stating it as the trial hypothesis leaves the trials floating free of the ontic substrate. This file
puts the sampling where it belongs — on the **ontic** floor — and derives the epistemic content:

**Ontic vs epistemic.**
* **Ontic (the floor — the *only* thing assumed):** the space `Σ`, the deterministic dynamics `D`, and
  its **typicality measure `μ_L = D.muL`** (`ConstraintDynamics.muL`). Trials sample `μ_L` — repeated
  preparations under ontic ignorance of the microstate (Paper D). That `Σ, μ_L` exist and that trials
  are i.i.d.-`μ_L` is **SO-1**: the floor, not a derivation (deriving it from a single flow's
  time-ergodicity is deliberately *not* the CSD route; typicality is repeated-preparation ignorance).
* **Epistemic (everything here is *derived*, not assumed):** the outcome regions `Ωᵢ = bornRegion ψ i`
  on the projective base `ℂℙⁿ⁻¹`, the projective law `μ_FS = π_* μ_L` (the measure bridge
  `HasFubiniStudyPushforward`), and the Born weight.

Results:
* `onticBornVolume_eq` — **Born = the ontic typicality volume.** For any projective sector whose `π`
  pushes `μ_L` to `μ_FS`, the `μ_L`-measure of the ontic preimage of the epistemic outcome region is
  exactly the Born weight `‖⟨eᵢ, ψ⟩‖²` (via the pushforward + `bornRegion_fs_measure_uncond`). The
  epistemic Born number is a *theorem about the ontic typicality*, not a posited projective measure.
* `born_frequency_from_ontic_sampling` — **the Born frequency from ontic sampling.** For i.i.d. trials
  that sample the **ontic** `μ_L` (not `μ_FS`), the frequency of trials whose ontic microstate lands in
  the preimage of `Ωᵢ` converges a.s. to `‖⟨eᵢ, ψ⟩‖²`. The projective/epistemic law is never assumed —
  it is derived from the ontic sampling by the measure bridge.

So the *only* hypothesis is ontic (`hlaw : map Xₙ = D.muL`, the floor's typicality); `μ_FS` and Born are
consequences. This is the general, sector-level ontic grounding that `unified_born_frequency` provides
only for the concrete `productDynamics` witness. Foundational-triple, no `sorry`.

## References
`SigmaLayer/MeasureBridge.lean` (`HasFubiniStudyPushforward`, `productSector_hasFubiniStudyPushforward`);
`LF4/BornRegionUncond.lean` (`bornRegion_fs_measure_uncond`, `bornRegion_measurable_uncond`);
`LF1/GeneralFrequency.lean` (`freq_tendsto_of_iid`, the law-agnostic strong law);
`SigmaLayer/UnifiedFlowedRecords.lean` (`unified_born_frequency`, the product-model instance);
`specs/connectivity-manifest.md` (L5, the sampling caveat this addresses).
-/

@[expose] public section

open MeasureTheory
open CSD.LF4

namespace CSD.SigmaLayer

variable {M : ℕ} {Sigma : Type*} [MeasurableSpace Sigma] {D : ConstraintDynamics Sigma}
  (Q : ProjectiveSector (M + 1) D) (p₀ : CPN (M + 1))

/-- **Born = the ontic typicality volume.** If the sector's projection `π` pushes the ontic typicality
`μ_L = D.muL` forward to `μ_FS` (the measure bridge), then the `μ_L`-measure of the **ontic** preimage
`π⁻¹(Ωᵢ)` of the **epistemic** outcome region `Ωᵢ = bornRegion ψ i` is exactly the Born weight
`‖⟨eᵢ, ψ⟩‖²`. The Born number is a theorem about the ontic typicality, derived via the pushforward and
`bornRegion_fs_measure_uncond` — no projective measure is posited. -/
theorem onticBornVolume_eq (hpush : HasFubiniStudyPushforward Q p₀)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin (M + 1)) :
    ((D.muL : Measure Sigma) (Q.pi ⁻¹' bornRegion ψ hψ0 i)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  unfold HasFubiniStudyPushforward at hpush
  rw [← Measure.map_apply Q.measurable_pi (bornRegion_measurable_uncond ψ hψ0 i), hpush]
  exact bornRegion_fs_measure_uncond p₀ ψ hψ0 hψ i

/-- **The Born frequency from ontic sampling.** For i.i.d. trials that sample the **ontic** typicality
`μ_L = D.muL` (the floor — repeated preparations under ontic ignorance), the frequency of trials whose
microstate lands in the ontic preimage `π⁻¹(Ωᵢ)` of the epistemic outcome region converges almost
surely to the Born weight `‖⟨eᵢ, ψ⟩‖²`. The projective law `μ_FS` and the Born number are **derived**
from the ontic sampling by the measure bridge (`onticBornVolume_eq`); the only hypothesis is ontic. -/
theorem born_frequency_from_ontic_sampling (hpush : HasFubiniStudyPushforward Q p₀)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → Sigma) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (D.muL : Measure Sigma))
    (hindep : Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
      (fun n => Set.indicator ((X n) ⁻¹' (Q.pi ⁻¹' bornRegion ψ hψ0 i)) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, Filter.Tendsto
      (fun m : ℕ => (∑ k ∈ Finset.range m,
        Set.indicator ((X k) ⁻¹' (Q.pi ⁻¹' bornRegion ψ hψ0 i)) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
      Filter.atTop (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  have hmeas : MeasurableSet (Q.pi ⁻¹' bornRegion ψ hψ0 i) :=
    (bornRegion_measurable_uncond ψ hψ0 i).preimage Q.measurable_pi
  have h := CSD.LF1.freq_tendsto_of_iid hX hlaw hmeas hindep
  rwa [onticBornVolume_eq Q p₀ hpush ψ hψ0 hψ i] at h

/-- **Non-vacuity: the ontic Born-volume identity on the concrete product model.** The `hpush`
hypothesis is not idle — it is discharged by the *proved* pushforward `productSector_hasFubiniStudyPushforward`.
On the product model `Σ = KSigma`, the ontic typicality `μ_L = (productDynamics H hH p₀).muL` of the
preimage of the Born region is exactly the Born weight. -/
theorem productModel_onticBornVolume (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    (hH : H.IsHermitian) (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin (M + 1)) :
    (((productDynamics H hH p₀).muL : Measure (CSD.LF4.KSigma (M + 1)))
        ((productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 :=
  onticBornVolume_eq (productSector H hH p₀) p₀
    (productSector_hasFubiniStudyPushforward H hH p₀) ψ hψ0 hψ i

end CSD.SigmaLayer
