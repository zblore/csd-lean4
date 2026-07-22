/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.BornFS
import CsdLean4.LF1.GeneralFrequency

/-!
# LF4: Busch-free empirical chain for the qubit Born weight (volume route)

**Category:** 3-Local (Busch-free empirical chain for the qubit Born weight (volume route)).

This integrates the moment-map / volume derivation of the Born weight into the
LF1 empirical chain, giving a frequency-convergence capstone that routes through
the **Fubini–Study volume** rather than through `busch_effect_gleason`.

The existing LF3 chain capstones land on the Born weight via the operational
package and `pure_state_born_weights_of_certainty`, hence cite
`busch_effect_gleason`. Here, for the qubit, the limiting frequency is identified
with the Born weight `‖⟨e₀,ψ⟩‖²` via `fs_born_volume_ratio_qubit` — the genuine
Fubini–Study volume of the moment sublevel set on the ontic Kähler `Σ = ℂℙ¹`. So
this capstone cites **only the foundational triple** plus the explicit
`h_uniform` hypothesis (the `N=2` Duistermaat–Heckman fact; the plan-B discharge
target — see `specs/carve-out-plan.md`). No `busch_effect_gleason`.

This realises the CSD thesis end to end for the qubit: deterministic
repeated-trial typicality (LF1) + "Born = Fubini–Study volume ratio" (the moment
map) ⟹ empirical frequencies converge almost surely to the Born weight, with the
Born value derived from the Kähler volume, not imported via Gleason/Busch.

**Honest scope.** Conditional on `h_uniform` (classically true, dischargeable;
plan B). The outcome region is the moment sublevel set, special to `N=2`'s
1-dimensional polytope.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **Busch-free qubit Born frequency convergence.** For i.i.d. trials `X` drawn
from the Fubini–Study measure on `ℂℙ¹`, the empirical frequency of the moment
sublevel outcome `{p | momentMap p 0 ≤ momentMap [ψ] 0}` converges almost surely
to the Born weight `‖⟨e₀, ψ⟩‖²`, provided the `N=2` Duistermaat–Heckman
hypothesis `h_uniform`. Cites only the foundational triple + `h_uniform`; no
`busch_effect_gleason`. -/
theorem qubit_born_frequency_convergence
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (h_uniform : Measure.map (fun p => momentMap p 0) (fubiniStudyMeasure p₀)
        = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2)) := by
  have hO : MeasurableSet
      {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0} :=
    (momentMap_measurable 0) measurableSet_Iic
  have hlim : (fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0}).toReal
      = ‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2 := by
    rw [fs_born_volume_ratio_qubit p₀ ψ hψ0 hψ h_uniform, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hfreq := LF1.freq_tendsto_of_iid hX hlaw hO hindep
  rwa [hlim] at hfreq

end LF4
end CSD
