import CsdLean4.LF4.NonTrivialSetup
import CsdLean4.LF4.POVMVolume

/-!
# HY-5: routing the general-`N` Born frequencies through a deterministic Σ-flow

The general-`N` Born-frequency capstones (`born_frequency_convergence_N`,
`povm_born_frequency_volume`) run the strong law over i.i.d. trials sampled from
the bare Fubini–Study measure on `ℂℙ^{N-1}` — the abstract SLLN engine, with no
deterministic evolution. This is the Born-side analogue of the gap the W-series
`sigmaFlow` fix closed on the Schrödinger side (a provenance audit found the
Schrödinger chain consumed only the induced ray map, never the Σ-substrate flow).

This module closes it on the Born side: the trials are **evolved by the sector's
own deterministic flow** before their outcome block is scored. Concretely, for the
`unitaryFlowSetup (M+1) U p₀` sector (`Σ = ℂℙ^{N-1}`, `flow t = (U t • ·)`, a
genuine `Φ ≠ id` for e.g. `U = rotU`, cf. `rotationSetup_projectedFlow_ne_id`),
the empirical frequencies of the flow-image Born region converge a.s. to the Born
weights. The flow's Liouville-preservation `flow_preserves_volume` (= the
`U(N)`-invariance of `μ_FS`) is **load-bearing**: it pins the law of the evolved
trials `Φ_t ∘ X` back to `μ_FS`, so the deterministic evolution does not spoil the
typicality frequencies. The sector's `flow`/`flow_preserves_volume` fields are now
consumed by the Born capstone, not just the abstract measure.

## Deliverables

* `unitaryFlowSetup_born_frequency_evolved` — the general-`N` Born frequencies of
  trials evolved by the sector flow → `‖⟨eᵢ, ψ⟩‖²`;
* `povm_born_frequency_volume_evolved` — the POVM analogue → `P.weight ψ i`.

## Honest scope

This routes the Born capstone through the sector's deterministic flow, making
`flow_preserves_volume` load-bearing (the Born-side sigmaFlow fix). It does NOT
derive the Born weights from the flow, and the trials are still an i.i.d. sampling
posit before evolution — the weights-from-dynamics problem (A5→D1, FND-1) is
untouched. Foundational-triple-only / Gleason-free (reuses
`born_frequency_convergence_N`; nothing re-proved).
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization Kronecker

namespace CSD
namespace LF4

open CSD.LF2

/-- **General-`N` Born frequencies of trials EVOLVED by the sector's deterministic
flow.** For any `unitaryFlowSetup (M+1) U p₀` and time `t`, i.i.d. trials sampled
from its `liouvilleMeasure` and then evolved by the sector's own flow
`Φ_t = (unitaryFlowSetup …).flow t` have empirical frequencies of the Born region
converging a.s. to the Born weights `‖⟨eᵢ, ψ⟩‖²`. The flow's Liouville-preservation
(`flow_preserves_volume`, i.e. `U(N)`-invariance of `μ_FS`) pins the law of the
evolved trials back to `μ_FS` — this is where the substrate flow becomes
load-bearing on the Born side. -/
theorem unitaryFlowSetup_born_frequency_evolved {M : ℕ}
    (U : ℝ → Matrix.unitaryGroup (Fin (M + 1)) ℂ) (p₀ : CPN (M + 1)) (t : ℝ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (unitaryFlowSetup (M + 1) U p₀).liouvilleMeasure)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator
          (((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X n) ⁻¹' bornRegion ψ hψ0 i)
          (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                (((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X k) ⁻¹' bornRegion ψ hψ0 i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  -- The sector's flow preserves its Liouville measure, so it pins the evolved law.
  have hmp := (unitaryFlowSetup (M + 1) U p₀).flow_preserves_volume t
  have hlaw' : ∀ n, Measure.map ((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X n) Pr
      = fubiniStudyMeasure p₀ := fun n =>
    calc Measure.map ((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X n) Pr
        = Measure.map ((unitaryFlowSetup (M + 1) U p₀).flow t) (Measure.map (X n) Pr) :=
          (Measure.map_map hmp.measurable (hX n)).symm
      _ = Measure.map ((unitaryFlowSetup (M + 1) U p₀).flow t)
            ((unitaryFlowSetup (M + 1) U p₀).liouvilleMeasure) := congrArg _ (hlaw n)
      _ = fubiniStudyMeasure p₀ := hmp.map_eq
  exact born_frequency_convergence_N p₀ ψ hψ0 hψ hpos
    (fun n => (unitaryFlowSetup (M + 1) U p₀).flow t ∘ X n)
    (fun n => hmp.measurable.comp (hX n)) hlaw' hindep

/-- **POVM Born frequencies of trials EVOLVED by the sector's deterministic flow.**
The `povm_born_frequency_volume` capstone on trials evolved by the sector flow
`Φ_t`: the empirical frequencies of the pointer blocks converge a.s. to the POVM
weights `P.weight ψ i`. Same block-sum reduction as `povm_born_frequency_volume`,
now on the flow-evolved trials via `unitaryFlowSetup_born_frequency_evolved`. -/
theorem povm_born_frequency_volume_evolved {M : ℕ} {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (e : (Fin N × ι) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (hpos : ∀ j : Fin (M + 1), 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ'‖ ^ 2)
    (U : ℝ → Matrix.unitaryGroup (Fin (M + 1)) ℂ) (p₀ : CPN (M + 1)) (t : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (unitaryFlowSetup (M + 1) U p₀).liouvilleMeasure)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator
          (((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X n) ⁻¹' bornRegion ψ' hψ'0 j)
          (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : ι,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator
                  (((unitaryFlowSetup (M + 1) U p₀).flow t ∘ X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (P.weight ψ i)) := by
  filter_upwards [unitaryFlowSetup_born_frequency_evolved U p₀ t ψ' hψ'0 hnorm hpos X hX hlaw hindep]
    with ω hω
  intro i
  have hlim := tendsto_finset_sum (Finset.univ : Finset (Fin N))
    (fun n (_ : n ∈ Finset.univ) => hω (e (n, i)))
  rwa [show (∑ n : Fin N, ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2)
        = P.weight ψ i from by
      rw [povm_born_eq_block_sum P D ψ i, hψ'eq]
      exact Finset.sum_congr rfl (fun n _ => piLpCongrLeft_inner_single_sq e _ (n, i))] at hlim

end LF4
end CSD
