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

/-! ### ⚠️ E5's sharpness check: when the antecedent is *empty* -/

/-- ⚠️ **No periodic flow satisfies E4's antecedent for a nontrivial subsystem.**

If `Φ^[k] = id` and `d_A ≥ 2`, then `HasCorrelationDecay` for the population observable is
**false** for every summable envelope. So `blockPop_timeAverage_tendsto`, applied to a periodic
Σ-flow, is a conditional whose antecedent cannot be met.

The proof is Q24 arithmetic against the periodic no-go. A periodic map forces `⟨x²⟩ = ⟨x⟩²`
(`HasCorrelationDecay.integral_mul_self_eq_of_periodic`), whereas `fs_blockPop_sq` and
`fs_blockPop_mean` give `⟨x²⟩ = (d_B²+d_B)/(N(N+1))` and `⟨x⟩ = d_B/N`. Those agree exactly when
`N = d_B`, i.e. when `d_A = 1` — no subsystem at all.

**Why this matters for the arc.** A unitary acting on `ℂℙ^{N-1}` generates a relatively compact
group, so its correlations are almost periodic and cannot decay either. That general statement is
**not yet proved**, but it is no longer hand-waving — two of its three pieces are theorems:

* `MeasureTheory.HasCorrelationDecay.integral_mul_self_eq_of_recurrent` reduces it to a single
  property `hrec`: the correlation must return near its lag-zero value at arbitrarily large lags;
* `exists_le_pow_mem_of_compactSpace` supplies the recurrence of `U ^ n` itself — the powers of a
  unitary return to *every* neighbourhood of `1`, at arbitrarily large exponents, since
  `Matrix.unitaryGroup` is a compact topological group.

What remains is exactly one analytic bridge: a **uniform** estimate
`|f (V • p) - f p| ≤ c · √(dev V)` with `dev` continuous and vanishing at `V = 1`, transferring
the group recurrence to the correlation. (Uniform, because `FirstCountableTopology` does not
synthesize for `Matrix.unitaryGroup`, so `continuous_of_dominated` is unavailable.) That estimate
is a queued BACKLOG item, not a claim made here.

Either way the honest reading is that E4's antecedent is **not** populated by finite-dimensional
unitary Σ-dynamics, and a genuine witness needs a non-atomic space with a genuinely mixing map —
which is what `CsdLean4/Mathlib/Dynamics/CorrelationDecayWitness.lean` supplies for the engine. -/
theorem not_hasCorrelationDecay_blockPop_of_periodic
    (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) (hdA : 2 ≤ dA)
    {Φ : CPN N → CPN N} {ε : ℕ → ℝ} {k : ℕ} (hk : 0 < k) (hper : Φ^[k] = id)
    (hsum : Summable ε) :
    ¬ MeasureTheory.HasCorrelationDecay (fubiniStudyMeasure p₀) Φ
        (fun q => blockPop e q a) ε := by
  intro hdec
  have hvar := hdec.integral_mul_self_eq_of_periodic hk hper hsum
  have hsq : ∫ p, blockPop e p a * blockPop e p a ∂(fubiniStudyMeasure p₀)
      = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) := by
    rw [integral_congr_ae (ae_of_all _ (fun p => (pow_two (blockPop e p a)).symm))]
    exact fs_blockPop_sq p₀ e a
  rw [hsq, fs_blockPop_mean p₀ e a] at hvar
  -- arithmetic: the two Q24 values agree only when `N = d_B`, i.e. `d_A = 1`
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNmul := card_eq_mul_of_tensorEquiv e
  have hdBn : dB ≠ 0 := by rintro rfl; exact hN0 (by simpa using hNmul)
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hdBne : (dB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdBn
  have hN1ne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hNR : (N : ℝ) = (dA : ℝ) * (dB : ℝ) := by exact_mod_cast hNmul
  have hcross : ((dB : ℝ) ^ 2 + (dB : ℝ)) * (N : ℝ) ^ 2
      = (dB : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) := by
    have e1 : ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1))
        * ((N : ℝ) * ((N : ℝ) + 1)) * (N : ℝ) ^ 2
        = ((dB : ℝ) ^ 2 + (dB : ℝ)) * (N : ℝ) ^ 2 := by field_simp
    have e2 : ((dB : ℝ) / (N : ℝ)) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) * (N : ℝ) ^ 2
        = (dB : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) + 1)) := by field_simp
    rw [← e1, ← e2, hvar]
  have hfac : (N : ℝ) * (dB : ℝ) * ((N : ℝ) - (dB : ℝ)) = 0 := by linear_combination hcross
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hNne h'
    · exact hdBne h'
  · have hNd : (N : ℝ) = (dB : ℝ) := by linarith [sub_eq_zero.mp h]
    have hdA1 : (dA : ℝ) = 1 := by
      have hmul : (dA : ℝ) * (dB : ℝ) = 1 * (dB : ℝ) := by rw [one_mul, ← hNR, hNd]
      exact mul_right_cancel₀ hdBne hmul
    have h2 : (2 : ℝ) ≤ (dA : ℝ) := by exact_mod_cast hdA
    linarith

end CSD.Thermo
