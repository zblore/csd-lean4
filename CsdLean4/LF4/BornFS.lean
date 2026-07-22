/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.MomentMap
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# LF4 Tranche M slice 2 (option C): Born = Fubini–Study volume ratio on Σ (qubit)

This completes the on-`Σ` statement of "Born = volume ratio" for the qubit
(`N = 2`), modulo the single explicit analytic hypothesis identified in slice 2:
the `0`-coordinate of the moment map pushes the genuine Fubini–Study measure to
the uniform measure on `[0,1]`.

```
fs_born_volume_ratio_qubit :
  (Φ₀∗ fubiniStudyMeasure = uniform[0,1]) →
    fubiniStudyMeasure {p | momentMap p 0 ≤ momentMap [ψ] 0} = ‖⟨e₀, ψ⟩‖².
```

The outcome region is the **sublevel set** `{p | momentMap p 0 ≤ momentMap [ψ] 0}`
— the rays whose outcome-`0` moment value is at most the preparation's. For
`N = 2` the moment polytope is the segment `[0,1]`, so this sublevel set is the
pullback of `[0, b₀(ψ)]` and its FS measure is its length `b₀(ψ) = ‖⟨e₀,ψ⟩‖²`.
The region is geometric (a moment sublevel set), the measure is the genuine
`fubiniStudyMeasure` on the ontic Kähler `Σ = ℂℙ¹`, and the equality to the Born
weight is a theorem — no carving, no `busch_effect_gleason`.

**Honest scope.** The hypothesis `h_uniform` is the `N = 2` Duistermaat–Heckman /
Dirichlet fact ("`|U₀₀|²` is `Uniform[0,1]` for Haar `U(2)`"), the discharge
target of plan B (`specs/carve-out-plan.md` Tranche M slice 2). Stated as an
explicit hypothesis, the theorem stays axiom-clean (the project's
load-bearing-hypothesis pattern) and names the precise remaining gap. The
sublevel-set form is special to `N = 2` (the 1-dimensional polytope); general `N`
uses the barycentric regions of `BornVolume.lean` with the full
`Φ∗μ_FS = uniform_Δ` pushforward.

**Category:** 1-Mathlib adjacent; kept in `CSD.LF4` for the carve-out programme.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **`momentMap · i` is measurable.** `momentMap` is defined via the
representative `rep`, but it is scale-invariant, so it descends from the
measurable function `v ↦ ‖vᵢ‖²/‖v‖²` on the nonzero subtype. Routed through the
§12 characterisation `measurable_iff_measurable_comp_mk'`. -/
theorem momentMap_measurable (i : Fin N) :
    Measurable (fun p : CPN N => momentMap p i) := by
  borelize (EuclideanSpace ℂ (Fin N))
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcomp : (fun p : CPN N => momentMap p i) ∘ (Projectivization.mk' ℂ)
      = fun w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 } =>
          ‖(w : EuclideanSpace ℂ (Fin N)) i‖ ^ 2 / ‖(w : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    funext w
    show momentMap (Projectivization.mk ℂ (w : EuclideanSpace ℂ (Fin N)) w.2) i = _
    rw [momentMap_mk]
  rw [hcomp]
  have hden : ∀ w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 },
      ‖(w : EuclideanSpace ℂ (Fin N))‖ ^ 2 ≠ 0 :=
    fun w => pow_ne_zero 2 (norm_ne_zero_iff.mpr w.2)
  refine Measurable.div ?_ ?_
  · exact ((((EuclideanSpace.proj i).continuous).comp continuous_subtype_val).norm.pow 2).measurable
  · exact ((continuous_subtype_val.norm).pow 2).measurable

/-- **Headline (option C): the Born weight is a Fubini–Study volume ratio on `ℂℙ¹`.**
For a unit qubit preparation `ψ`, modulo the `N = 2` Duistermaat–Heckman
hypothesis (`Φ₀∗ fubiniStudyMeasure = uniform[0,1]`), the FS measure of the
moment sublevel set at `[ψ]` equals the Born weight `‖⟨e₀, ψ⟩‖²`. -/
theorem fs_born_volume_ratio_qubit
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (h_uniform : Measure.map (fun p => momentMap p 0) (fubiniStudyMeasure p₀)
        = (volume : Measure ℝ).restrict (Set.Icc 0 1)) :
    fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0}
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2) := by
  set s := momentMap (Projectivization.mk ℂ ψ hψ0) 0 with hs
  have hs0 : 0 ≤ s := momentMap_nonneg _ _
  have hs1 : s ≤ 1 := momentMap_le_one _ _
  have hset : {p : CPN 2 | momentMap p 0 ≤ s} = (fun p => momentMap p 0) ⁻¹' Set.Iic s := rfl
  rw [hset, ← Measure.map_apply (momentMap_measurable 0) measurableSet_Iic, h_uniform,
      Measure.restrict_apply measurableSet_Iic]
  have hinter : Set.Iic s ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hxs, hx0, _⟩ => ⟨hx0, hxs⟩, fun ⟨hx0, hxs⟩ => ⟨hxs, hx0, hxs.trans hs1⟩⟩
  rw [hinter, Real.volume_Icc, sub_zero, hs, momentMap_mk_eq_inner_sq ψ hψ0 hψ 0]

end LF4
end CSD
