/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# LF1 General frequency theorem (law-agnostic)

**Category:** 3-Local.

The law-agnostic core of `LF1_main_theorem_ae`. For i.i.d. `Σ`-valued trials
`X : ℕ → Ω → Σ` with a *common law* `μp` (any probability measure), the empirical
frequency of a measurable outcome region `O ⊆ Σ` converges almost surely to the
ontic weight `(μp O).toReal`.

The preparation enters **only** as the probability measure `μp`. The
`Ω₀`-conditional preparation (`OnticSetup.prepMeasure`) is one instance; a
**posited fibre measure** `μ_[ψ]` for a pure-state preparation is another. This is
the formal counterpart of the ambient/fibre split: ambient `μL`-conditionals for
mixed states, fibre measures for pure states (Paper A / Σ0, revised). `μ_[ψ]` is
posited ontic structure, so no disintegration machinery is needed here — it enters
downstream simply as a probability measure pushing to a Dirac on `[ψ]`.

The proof is the same strong-law wrapper used in `Convergence.lean`, with
`S.prepMeasure` replaced by the abstract `μp`.
-/

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace LF1

/-- **General repeated-trial frequency theorem.** I.i.d. trials with common law
`μp` make the empirical frequency of a measurable outcome region `O` converge
almost surely to `(μp O).toReal`. -/
theorem freq_tendsto_of_iid
    {SigmaSpace Ω : Type*} [MeasurableSpace SigmaSpace] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    {μp : Measure SigmaSpace} (hlaw : ∀ n, Measure.map (X n) P = μp)
    {O : Set SigmaSpace} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g P)
          (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P,
      Tendsto
        (fun N : ℕ =>
          (∑ i ∈ Finset.range N,
              Set.indicator (X i ⁻¹' O) (fun _ => (1 : ℝ)) ω) / (N : ℝ))
        atTop
        (nhds (μp O).toReal) := by
  -- Integrability of the (bounded) indicator on trial 0.
  have hint : Integrable (Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).mono
      ((measurable_const.indicator (hO.preimage (hX 0))).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        by_cases hω : ω ∈ X 0 ⁻¹' O
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω])
  -- Identical distribution: each indicator factors as `(indicator O 1) ∘ X n`,
  -- and all `X n` share the law `μp`.
  have hident : ∀ n,
      IdentDistrib (Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ)))
        (Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ))) P P := fun n => by
    have hfact : ∀ m,
        Set.indicator (X m ⁻¹' O) (fun _ => (1 : ℝ))
          = (Set.indicator O (fun _ => (1 : ℝ))) ∘ X m := fun m => by
      funext ω
      simp only [Function.comp]
      by_cases hω : X m ω ∈ O
      · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hω), Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h)),
            Set.indicator_of_notMem hω]
    have hXident : IdentDistrib (X n) (X 0) P P :=
      ⟨(hX n).aemeasurable, (hX 0).aemeasurable, by rw [hlaw n, hlaw 0]⟩
    rw [hfact n, hfact 0]
    exact hXident.comp (measurable_const.indicator hO)
  -- Strong law: empirical mean → ∫ (indicator on trial 0).
  have hSLLN :=
    strong_law_ae_real
      (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ)))
      hint hindep hident
  -- The mean is `(μp O).toReal`.
  have hmean :
      ∫ ω, Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ)) ω ∂ P = (μp O).toReal := by
    have h1 :
        ∫ ω, Set.indicator (X 0 ⁻¹' O) (fun _ => (1 : ℝ)) ω ∂ P
          = (P (X 0 ⁻¹' O)).toReal := by
      rw [integral_indicator (hO.preimage (hX 0)), setIntegral_const, smul_eq_mul, mul_one]
      simp [Measure.real]
    rw [h1, ← Measure.map_apply (hX 0) hO, hlaw 0]
  filter_upwards [hSLLN] with ω hω
  rwa [hmean] at hω

end LF1
end CSD
