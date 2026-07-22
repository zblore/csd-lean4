/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF1.GeneralFrequency

/-!
# LF4: general-`N` Busch-free Born frequency convergence over a partition

**Category:** 3-Local (general-`N` Busch-free Born frequency convergence over a partition).

The qubit capstone `qubit_born_frequency_convergence` is single-outcome. This is
its general-`N`, joint-outcome form: for a finite family of measurable outcome
regions whose ontic measures are the Born weights, the empirical frequencies
converge **jointly** (a single almost-sure event) to those weights.

This simultaneously closes the bookkeeping deferred in `specs/LF4-todo.md` §9
(the finite-partition joint a.e. convergence that LF1 sketched as
"apply once per element and intersect the full-measure sets"): the proof is
exactly that, `freq_tendsto_of_iid` per index intersected via `ae_all_iff`.

The "Born = ontic measure" content enters **only** through the hypothesis
`hborn : ∀ i, (μ (region i)).toReal = b i`. For the qubit this is discharged by
`fs_born_volume_ratio_qubit` (the genuine Fubini–Study volume of the moment
sublevel set), modulo `h_uniform`; for general `N` it awaits the `(N-1)`-dim
barycentric volume ratio + the full Duistermaat–Heckman pushforward
`Φ∗μ_FS = uniform_Δ`. Either way the capstone is **Busch-free** — it cites only
the foundational triple, never `busch_effect_gleason`.

So the general statement is: deterministic repeated-trial typicality (LF1) +
"Born = ontic volume" (the hypothesis, derived from the Kähler geometry per
`BornVolume`/`BornFS`) ⟹ empirical frequencies converge jointly to the Born
weights, with the Born values supplied by the volume route, not Gleason/Busch.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace LF4

/-- **General-`N` Busch-free joint Born frequency convergence.** For i.i.d. trials
`X` with common law `μ` and a finite family of measurable outcome regions
`region i` whose ontic measures are the Born weights `b i`
(`hborn : (μ (region i)).toReal = b i`), the empirical frequencies of all outcomes
converge — on a single full-measure event — to their Born weights. Cites only the
foundational triple; no `busch_effect_gleason`. Closes `LF4-todo` §9. -/
theorem born_frequency_convergence_partition
    {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] {μ : Measure SigmaSpace}
    {ι : Type*} [Countable ι]
    (region : ι → Set SigmaSpace) (hmeas : ∀ i, MeasurableSet (region i))
    (b : ι → ℝ) (hborn : ∀ i, (μ (region i)).toReal = b i)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → SigmaSpace) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = μ)
    (hindep : ∀ i,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' region i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i,
      Tendsto
        (fun M : ℕ =>
          (∑ k ∈ Finset.range M,
              Set.indicator ((X k) ⁻¹' region i) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (b i)) := by
  rw [ae_all_iff]
  intro i
  have hfreq := LF1.freq_tendsto_of_iid hX hlaw (hmeas i) (hindep i)
  rwa [hborn i] at hfreq

end LF4
end CSD
