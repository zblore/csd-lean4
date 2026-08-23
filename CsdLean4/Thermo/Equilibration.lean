/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.ReducedSecondMoment
public import CsdLean4.Mathlib.Dynamics.CorrelationDecay

/-!
# E4: equilibration of time-averaged reduced states, as a conditional theorem

The equilibration arc's fourth item (`specs/equilibration-arc-plan.md` E4). It spends the generic
engine `CsdLean4/Mathlib/Dynamics/CorrelationDecay.lean` on the observables E1 built.

## ⚠️ This is a conditional, and the antecedent is the whole content

Both theorems below have the shape

  *if* the flow preserves `μ_FS`, *and* its correlations for this observable decay with a
  summable envelope, *then* the time averages converge to the Fubini–Study average.

**Neither hypothesis is proved, exhibited, or claimed to hold for any Σ.** Nothing in the corpus
proves that any dynamics mixes, and nothing here changes that. What E4 buys is a *reformulation*:
equilibration stops being a dephasing story and becomes an ergodic-theoretic statement whose one
hypothesis is explicit, quantitative, and checkable in principle. Producing an actual witness for
the antecedent is E5's separate job, and until that exists these theorems are conditionals with
an unpopulated antecedent — which is exactly why the hypothesis is named in the signature rather
than folded into a definition.

## What is proved

* ★★ `blockPop_timeAverage_tendsto` — time-averaged **subsystem populations** converge in `L²` to
  `d_B/N` (`= 1/d_A`, the maximally-mixed value, by `fs_blockPop_mean`);
* ★★ `hsDeviationNormSq_timeAverage_tendsto` — the time-averaged **Hilbert–Schmidt deviation**
  `‖ρ_A − I_A/d_A‖₂²` converges in `L²` to the Lubkin–Page value `(d_A+d_B)/(N+1) − 1/d_A`
  that E1 computed (`fs_hsDeviationNormSq`). This is E4 composed with E1.

## ⚠️ Honest scope

* **Discrete time.** `Φ` is a single map and `Φ^[t]` its iterates; a continuous Σ-flow enters by
  sampling at a fixed timestep. The continuous-time statement is not proved.
* **`L²` convergence**, from a second-moment bound. Almost-everywhere convergence is what
  pointwise Birkhoff would give and is not available (`MATHLIB-GAPS.md`).
* The flow is a hypothesis, not a construction: no Σ-dynamics is built here, and in particular
  the `D1` dynamics residue is untouched. `μ_FS`-preservation is likewise assumed, not derived.
* H-TENSOR is inherited from E1: the bipartition travels as the explicit `e` in every signature.

Reference: `specs/equilibration-arc-plan.md` (E4, and E5 for the non-vacuity requirement);
`MATHLIB-GAPS.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators

namespace CSD.Thermo

open CSD.LF4

variable {N dA dB : ℕ} [NeZero N]

/-- ★★ **Time-averaged subsystem populations equilibrate — conditionally.**

If `Φ` preserves the Fubini–Study measure and the population's correlations decay with a summable
envelope `ε`, then the Birkhoff averages of `(ρ_A)_{aa}` converge in `L²` to `d_B/N`, which
`fs_blockPop_mean` identifies as the maximally-mixed value `1/d_A`.

The correlation hypothesis is stated at **one lag**, which is the form a physical estimate
produces; `HasCorrelationDecay.of_measurePreserving` turns it into the two-index form the engine
consumes. -/
theorem blockPop_timeAverage_tendsto (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ}
    (hΦ : MeasurePreserving Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    (hlag : ∀ u : ℕ,
      |(∫ p, blockPop e p a * blockPop e (Φ^[u] p) a ∂(fubiniStudyMeasure p₀))
        - (∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀)) ^ 2| ≤ ε u)
    (hsum : Summable ε) :
    Filter.Tendsto
      (fun T : ℕ => ∫ p, (birkhoffAverage ℝ Φ (fun q => blockPop e q a) T p - (dB : ℝ) / N) ^ 2
        ∂(fubiniStudyMeasure p₀))
      Filter.atTop (nhds 0) := by
  have hf : Measurable (fun q : CPN N => blockPop e q a) := blockPop_measurable e a
  have hdec := MeasureTheory.HasCorrelationDecay.of_measurePreserving hΦ hf hlag
  have hmean : ∀ t : ℕ, ∫ p, blockPop e (Φ^[t] p) a ∂(fubiniStudyMeasure p₀)
      = ∫ q, blockPop e q a ∂(fubiniStudyMeasure p₀) := fun t =>
    MeasureTheory.integral_iterate_of_measurePreserving hΦ hf.aestronglyMeasurable t
  have h := MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq hΦ.measurable hf
    zero_le_one (fun p => abs_blockPop_le_one e p a) hmean hdec hsum
  rwa [fs_blockPop_mean p₀ e a] at h

/-- ★★ **E4 composed with E1.** Under the same two hypotheses, the time-averaged Hilbert–Schmidt
deviation of the reduced state from maximally mixed converges in `L²` to the Lubkin–Page value
`(d_A + d_B)/(N + 1) − 1/d_A` proved in `fs_hsDeviationNormSq`.

For a large environment that value is `O(1/d_A · d_A/d_B)`-small, so the conditional reads: a
`μ_FS`-preserving flow with decaying correlations spends almost all of its time with the
subsystem near maximally mixed. Again — *conditional*; see the header. -/
theorem hsDeviationNormSq_timeAverage_tendsto (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ}
    (hΦ : MeasurePreserving Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀))
    (hlag : ∀ u : ℕ,
      |(∫ p, hsDeviationNormSq e p * hsDeviationNormSq e (Φ^[u] p) ∂(fubiniStudyMeasure p₀))
        - (∫ q, hsDeviationNormSq e q ∂(fubiniStudyMeasure p₀)) ^ 2| ≤ ε u)
    (hsum : Summable ε) :
    Filter.Tendsto
      (fun T : ℕ => ∫ p, (birkhoffAverage ℝ Φ (fun q => hsDeviationNormSq e q) T p
          - (((dA : ℝ) + (dB : ℝ)) / ((N : ℝ) + 1) - ((dA : ℝ))⁻¹)) ^ 2
        ∂(fubiniStudyMeasure p₀))
      Filter.atTop (nhds 0) := by
  have hf : Measurable (fun q : CPN N => hsDeviationNormSq e q) := hsDeviationNormSq_measurable e
  have hC : (0 : ℝ) ≤ (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by positivity
  have hbd : ∀ p : CPN N, |hsDeviationNormSq e p| ≤ (dA : ℝ) ^ 2 * (1 + (dB : ℝ) ^ 2) := by
    intro p
    rw [abs_of_nonneg (hsDeviationNormSq_nonneg e p)]
    exact hsDeviationNormSq_le e p
  have hdec := MeasureTheory.HasCorrelationDecay.of_measurePreserving hΦ hf hlag
  have hmean : ∀ t : ℕ, ∫ p, hsDeviationNormSq e (Φ^[t] p) ∂(fubiniStudyMeasure p₀)
      = ∫ q, hsDeviationNormSq e q ∂(fubiniStudyMeasure p₀) := fun t =>
    MeasureTheory.integral_iterate_of_measurePreserving hΦ hf.aestronglyMeasurable t
  have h := MeasureTheory.tendsto_integral_birkhoffAverage_sub_sq hΦ.measurable hf hC hbd
    hmean hdec hsum
  rwa [fs_hsDeviationNormSq p₀ e] at h

end CSD.Thermo
