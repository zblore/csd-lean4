import CsdLean4.LF5.DilationFromFlow
import CsdLean4.LF4.BornRegionUncond

/-!
# LF5: pointer frequencies of the de-isolation flow → Born (LF5-D)

**Category:** 3-Local (LF5 measurement-dynamics layer).

This is **LF5-D** of `specs/lf5-plan.md`: the empirical capstone of the
de-isolation reading. The LF5-C tranche realised the Naimark dilation isometry
dynamically — `V = U_vN ∘ (· ⊗ a₀)` (embed in the apparatus ground state, evolve
by the von Neumann coupling), with pointer outcomes the **context-fixed
apparatus blocks** `blockProj N i`, not regions carved to Born values. This
module closes the loop onto the FS-volume engine: for **every** unit
preparation `ψ`, the pointer-`i` committed Fubini–Study volume on the dilated
`ℂℙ^{N²−1}` equals the Born weight `‖⟨eᵢ, ψ⟩‖²`
(`vnDilation_pointer_volume`), and i.i.d. FS-typical trials on the dilated
sector have pointer-`i` block frequencies converging almost surely to that Born
weight (`vnDilation_pointer_frequency`).

## How the LF5-C obstruction was resolved

The post-flow state `Vψ` has **zero amplitude on every off-diagonal cell**
(`vnDilationV_mulVec`), so the `hpos` genericity of the audited POVM volume
theorems (P.3b/P.4) is unsatisfiable at `ψ' = piLpCongrLeft e (Vψ)` for
`N ≥ 2` — the obstruction recorded in `DilationFromFlow.lean`. The resolution
is **not** a carving and **not** a system-side reduction: the FS-volume engine
itself was upgraded to unconditional (`CsdLean4/LF4/BornRegionUncond.lean`) via
the per-cell dichotomy — positive-weight cells by the closed-simplex subset
argument, zero-weight cells by the det-0 null image + the joint Dirichlet law.
The regions below are the **same** ψ'-indexed moment-subdivision cells as the
audited engine, now evaluated at the non-generic `Vψ`; the off-diagonal cells
genuinely collapse to FS-null sets contributing `0` to each pointer block.

## Honest scope

The Born = FS-volume identity is **derived** one layer down — the moment-map /
Duistermaat–Heckman cluster (`fs_born_volume_ratio_N`,
`born_frequency_convergence_N`) computes the FS volume of a pure-geometry region
and out comes `‖⟨eᵢ,ψ⟩‖²`, with no Born put in, Gleason-free. This module
**imports** that identity (via `bornRegion_fs_measure_uncond`); it does not
re-prove it, and it does not take Born as a primitive. The increment here is the
*dynamically realised* dilation (`vnNaimark`, LF5-C) wired into that engine
without genericity — the measurement **dynamics** (`Φ ≠ id`), not the number.
What **is** posited is not Born but **A5**: that the sector's typicality law is
the Fubini–Study measure (i.i.d. trials with law `fubiniStudyMeasure`). Born =
volume is a theorem; FS-as-the-typicality-measure is the sector posit, still
undischarged (it reduces to D1, the dynamical sector origin). LF5-E wires the context-fixed pointer reading +
capstone; entangled / non-local de-isolation is deferred
(`specs/lf5-plan.md` §0).

Reference: `specs/lf5-plan.md` (LF5-D).
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

variable {N : ℕ} [NeZero N]

/-- The von Neumann Naimark dilation's isometry is the de-isolation matrix
`V = U_vN ∘ (· ⊗ a₀)` (definitional unfolding). Not consumed by the proofs
below — they rely on this defeq silently (iota-reduction of the structure
projection); this lemma certifies the seam explicitly. -/
lemma vnNaimark_V : (vnNaimark N).V = vnDilationV N := rfl

/-- **The dilated post-flow state of a unit preparation is unit:** the reindex
`piLpCongrLeft e` is an isometry and `V` is norm-preserving
(`vnDilationV_norm_map`). Discharges the `hnorm` hypothesis of the
unconditional engine for every unit `ψ`. -/
theorem piLpCongrLeft_vnDilationV_norm {m : ℕ} (e : Fin N × Fin N ≃ Fin m)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (vnDilationV N) ψ)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, vnDilationV_norm_map]
  exact hψ

/-- **Pointer-`i` committed FS volume = Born weight, every unit `ψ`.** The sum,
over the context-fixed pointer-`i` block `{(n, i) : n}`, of the Fubini–Study
volumes of the dilated Born regions at the post-flow state
`ψ' = piLpCongrLeft e (Vψ)` equals the Born weight `‖⟨eᵢ, ψ⟩‖²` — with **no
genericity hypothesis** (the off-diagonal cells of the block are FS-null and
contribute `0`). Instantiates `povm_born_eq_dilated_volume_uncond` at the
dynamically realised dilation `vnNaimark` and reads the POVM weight through
`basisPOVM_weight`. -/
theorem vnDilation_pointer_volume {M : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (e : (Fin N × Fin N) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0) (i : Fin N) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2
      = ∑ n : Fin N,
          (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, i)))).toReal := by
  subst hψ'eq
  have hnorm := piLpCongrLeft_vnDilationV_norm e ψ hψ
  have h := povm_born_eq_dilated_volume_uncond (basisPOVM N) (vnNaimark N) ψ i e p₀ hnorm
  rw [basisPOVM_weight ψ i] at h
  exact h

/-- **The LF5-D capstone: pointer-block frequencies of the de-isolation flow
converge to the Born weight, every unit `ψ`.** For i.i.d. FS-typical trials on
the dilated `ℂℙ^{N²−1}` (the A5 posit on the enlarged sector), almost surely
**every** pointer outcome `i` has its context-fixed block frequency (the sum
over the block `{(n, i) : n}` of per-cell empirical frequencies) converging to
`‖⟨eᵢ, ψ⟩‖²` — no genericity, vanishing (off-diagonal) dilated amplitudes
included. Instantiates `povm_born_frequency_volume_uncond` at `vnNaimark` and
lands the limit on the Born quadratic form via `basisPOVM_weight`. -/
theorem vnDilation_pointer_frequency {M : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (e : (Fin N × Fin N) ≃ Fin (M + 1))
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
    ∀ᵐ ω ∂ Pr, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  have hnorm : ‖ψ'‖ = 1 := by
    rw [hψ'eq]; exact piLpCongrLeft_vnDilationV_norm e ψ hψ
  filter_upwards [povm_born_frequency_volume_uncond (basisPOVM N) (vnNaimark N) ψ e ψ'
      hψ'eq hψ'0 hnorm p₀ X hX hlaw hindep] with ω hω i
  have h := hω i
  rwa [basisPOVM_weight ψ i] at h

end LF5
end CSD
