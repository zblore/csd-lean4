/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF5.FlowBornFrequency

/-!
# LF5: the measurement-flow Born-frequency capstone (LF5-E)

**Category:** 3-Local (LF5 measurement-dynamics layer).

This is **LF5-E** of `specs/lf5-plan.md`: the LF5 capstone, the layer's named
headline `measurement_flow_born_frequency`. Every conjunct is an existing
LF5-B/C/D theorem; this module's content is the single named chain statement
plus the honest documentation of what the layer does and does not deliver.

## The chain in one breath

A deterministic, Fubini–Study-measure-preserving von Neumann de-isolation flow
`Φ_vN = measurementFlow N e ≠ id` on the dilated ontic
`Σ' = ℂℙ^{N·N−1}` carries every embedded preparation ray `[ψ ⊗ a₀]` to the
dilated ray `[Vψ]` (`V = U_vN ∘ (· ⊗ a₀)`, the dynamically-realised Naimark
dilation); the pointer-`i` outcome is the context-fixed apparatus block
(`blockProj N i`, the index block `{(n, i) : n}` through `e`); its committed
Fubini–Study typicality volume is the Born weight `‖⟨eᵢ, ψ⟩‖²`; and i.i.d.
FS-typical trials on the dilated sector have pointer-block empirical
frequencies converging almost surely to it — for **every** unit preparation
`ψ`, vanishing dilated amplitudes included (the unconditional engine, LF5-D).

## The de-isolation reading (carve-out-plan §6)

The apparatus de-isolates a region of `Σ`; the outcome is fixed by the joint
microstate (deterministic — a Laplacian observer with access to the isolated
degrees of freedom would predict it with certainty); the apparent randomness
is epistemic, via typicality over the isolated DOF (the same
ignorance-of-microstate that carries LF1 frequencies to ontic volume, with the
FS measure as the A5 typicality law). The measurement *dynamics* is now
exercised (`Φ_vN ≠ id`, conjunct (1)), closing the single-system projective
tier of the D1 debt ("`Φ = id` in every concrete instance").

## Context-fixedness made precise

The flow and the pointer-block structure depend only on the measurement
context (the apparatus basis / the adder coupling `vnUnitary N` and the block
index `{(n, i) : n}`), never on the preparation — conjunct (3) is quantified
over **every** nonzero `φ`. The volume-*realising* regions
(`bornRegion ψ' hψ'0`) are the FS-volume engine's moment-subdivision cells at
the dilated state: preparation-dependent as a realisation mechanism, with
their measures **forced** by the Kähler geometry (the audited unconditional
engine `bornRegion_fs_measure_uncond`), not cut to fit; the partition of cells
into pointer blocks is the fixed index block `{(n, i)}`, `ψ`-independent.

## The ContextMap connection

`LF3/ContextMap.lean` keeps the per-context state space and outcome map
abstract and definitional: `ContextIndexedOutcomeMaps` carries
`Domain : MeasurementContext → Type*` and
`F : (ctx) → Domain ctx → Sign × Sign` as bare fields (and
`MeasurementContext` is Bell-two-wing-shaped — detector settings on two
wings). LF5 realises the single-system analogue of that context slot
*dynamically* rather than definitionally: the context is the fixed vN coupling
plus the apparatus block structure; the per-context state space is the dilated
ontic `Σ' = ℂℙ^{N·N−1}`; the outcome statistics are the pointer-block
frequencies. The *definitional per-microstate outcome map*
(microstate ↦ pointer value) is now **discharged** in `LF5/PointerOutcome.lean`
(LF5-F): the `bornRegion` pairwise-disjointness fact (owed since the Z⊗Z
degenerate-witness commit `aeece86`) is `CSD.LF4.bornRegion_pairwiseDisjoint`,
the outcome function is `vnPointerOutcome` (deterministic, total off an FS-null
set, measurable fibres), and `measurement_flow_outcome_frequency` upgrades this
capstone's conjunct (5) from outcome statistics (a sum of cell frequencies) to a
single union event per pointer. The five-conjunct text here is kept as the
statistics-form headline; the outcome-function upgrade is the standalone
conjunct-(5) theorem in `PointerOutcome.lean`.

## Honest non-goals (per `specs/lf5-plan.md` §0)

- The Born = FS-volume identity is **derived** one layer down (the moment-map /
  Duistermaat–Heckman cluster, `fs_born_volume_ratio_N` /
  `born_frequency_convergence_N`: the FS volume of a pure-geometry region equals
  `‖⟨eᵢ,ψ⟩‖²`, Gleason-free, no Born put in) and **imported** here (via
  `povm_born_eq_dilated_volume_uncond` / `bornRegion_fs_measure_uncond`). This
  module re-proves nothing about the number and takes Born as no primitive; its
  increment is the measurement **dynamics** (`Φ_vN ≠ id`).
- What **is** posited is not Born but **A5**: that the (apparatus-enlarged)
  sector's typicality law is the Fubini–Study measure (i.i.d. trials with law
  `fubiniStudyMeasure`). Born = volume is a theorem; FS-as-the-typicality-measure
  is the sector posit, not derived from the flow (it reduces to D1).
- Entangled / non-local de-isolation is deferred: Bell forces a non-local
  de-isolation map, given the corpus CHSH `= 2√2`. Single-system projective
  tier only.

Reference: `specs/lf5-plan.md` (LF5-E); `specs/carve-out-plan.md` §6.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

/-- **The LF5 capstone: the von Neumann measurement flow, its de-isolation
dynamics, and the Born frequencies it commits.** For the context-fixed von
Neumann coupling `e` and every unit preparation `ψ` (no genericity):

1. the measurement dynamics is genuine, `Φ_vN ≠ id`
   (`measurementFlow_ne_id`);
2. it is physically admissible: FS-measure-preserving — the Liouville /
   `hΦ_pres` content (`measurementFlow_measurePreserving`);
3. it is context-fixed: the **same** flow realises the Naimark dilation for
   **every** nonzero preparation `φ`, carrying `[φ ⊗ a₀]` to `[Vφ]`
   (`measurementFlow_realises_dilation`, quantified over the preparation);
4. the pointer-`i` committed FS volume — the sum over the context-fixed block
   `{(n, i) : n}` of the dilated Born-region volumes at the post-flow state —
   equals the Born weight `‖⟨eᵢ, ψ⟩‖²` (`vnDilation_pointer_volume`);
5. the empirical capstone: i.i.d. FS-typical trials on the dilated
   `ℂℙ^{N·N−1}` (the A5 typicality posit over the isolated DOF) have, almost
   surely, every pointer-block frequency converging to the Born weight
   (`vnDilation_pointer_frequency`).

Pure assembly of the LF5-B/C/D theorems — no new mathematical content; the
honest-scope ledger is the module docstring. -/
theorem measurement_flow_born_frequency
    {N M : ℕ} [NeZero N] (hN : 1 < N)
    (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
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
    -- (5) the empirical capstone: a.s. pointer-block frequencies → Born
    ∧ ∀ᵐ ω ∂ Pr, ∀ i : Fin N,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin N,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  ⟨measurementFlow_ne_id hN e,
   measurementFlow_measurePreserving e p₀,
   fun φ hφ => measurementFlow_realises_dilation e φ hφ,
   fun i => vnDilation_pointer_volume ψ hψ e p₀ ψ' hψ'eq hψ'0 i,
   vnDilation_pointer_frequency ψ hψ e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep⟩

end LF5
end CSD
