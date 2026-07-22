/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF5.Capstone
import CsdLean4.LF4.TrialWitness

/-!
# LF5: the measurement-flow capstone on the canonical i.i.d. FS trial witness

**Category:** 3-Local (LF5 measurement-dynamics layer, trial-witness tranche).

`measurement_flow_born_frequency` (LF5-E) quantifies over an abstract i.i.d.
trial bundle `(Ω, Pr, X, hX, hlaw, hindep)` on the dilated sector
`ℂℙ^{N·N−1}`. This module discharges that bundle with the canonical
coordinate process of `CsdLean4/LF4/TrialWitness.lean`
(`fsTrialMeasure p₀ = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀)`,
`fsTrial (M + 1) n = (· n)`): the canonical capstone quantifies only over the
measurement context `(hN, e)`, the preparation `(ψ, hψ)`, the dilated state
`(ψ', hψ'eq, hψ'0)`, and the reference point `p₀`. The five-conjunct
conclusion is verbatim that of `measurement_flow_born_frequency` with
`Pr := fsTrialMeasure p₀` and `X := fsTrial (M + 1)`.

## Honest scope

As in `TrialWitness.lean`: this is the measure-theoretic existence of the
i.i.d. sampling law, turning the LF5-E hypothesis set from classically
satisfiable into Lean-inhabited. The physical reading of repeated preparation
as i.i.d. FS-typical draws on the dilated sector remains the LF1 typicality
posit (A5, here on `Σ'`); the canonical process does not derive it.
Foundational-triple-only, Gleason-free.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

/-- **The LF5-E capstone on the canonical i.i.d. FS trial witness.** All five
conjuncts of `measurement_flow_born_frequency`, with the trial bundle
discharged by the canonical process: only the measurement context, the
preparation, the dilated state, and the FS reference point remain as
hypotheses. -/
theorem measurement_flow_born_frequency_canonical
    {N M : ℕ} [NeZero N] (hN : 1 < N)
    (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1)) :
    -- (1) the measurement dynamics is genuine: Φ_vN ≠ id
    measurementFlow N e ≠ id
    -- (2) and physically admissible: FS measure-preserving (the Liouville /
    -- hΦ_pres content)
    ∧ MeasurePreserving (measurementFlow N e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) and context-fixed: the SAME flow realises the dilation for EVERY
    -- preparation
    ∧ (∀ (φ : EuclideanSpace ℂ (Fin N)) (hφ : φ ≠ 0),
        measurementFlow N e
            (Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
                (Matrix.toEuclideanLin (embedGround N) φ))
              (piLpCongrLeft_embedGround_ne_zero e φ hφ))
          = Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
                (Matrix.toEuclideanLin (vnDilationV N) φ))
              (piLpCongrLeft_vnDilationV_ne_zero e φ hφ))
    -- (4) pointer-i committed FS volume = Born weight, every unit ψ
    ∧ (∀ i : Fin N,
        ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2
          = ∑ n : Fin N,
              (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, i)))).toReal)
    -- (5) the empirical capstone: a.s. pointer-block frequencies → Born, on
    -- the canonical i.i.d. FS trial process
    ∧ ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin N,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin N,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((fsTrial (M + 1) k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  measurement_flow_born_frequency hN e ψ hψ ψ' hψ'eq hψ'0 p₀
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end LF5
end CSD
