/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Crypto.E91KeyRate
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Empirical/QM: E91 finite-sample (finite-key) concentration

**Category:** 3-Local (QM-validity content, no CSD ontology).

The asymptotic key rate `E91.e91_key_rate_pos_of_chsh` takes the *true* CHSH
value `S` as given. A real device-independent QKD run does not see `S`; it
**estimates** it from `n` finite rounds. This module supplies the missing
finite-sample bridge: the empirical CHSH estimator `Ŝₙ` concentrates around the
true `S` exponentially in `n`, so the probability of failing to certify a
genuine violation decays like `exp(−n ε² / (2c))`.

## Model (minimal and honest)

A run is a sequence of per-round CHSH statistics `Y : ℕ → Ω → ℝ`. Each round's
statistic is

* **bounded**: `Y i ω ∈ [a, b]` almost surely (`a ≤ b`); the width `b − a` is the
  range of the per-round CHSH correlator combination (modelling choice — e.g. the
  standard randomized-setting unbiased per-round estimator lands in a fixed
  bounded interval). The Hoeffding constant is `c = ((b − a)/2)²`;
* **unbiased**: `μ[Y i] = S` (the true CHSH value);
* **independent**: `iIndepFun Y μ` (the per-round independence is a modelling
  hypothesis, exactly the i.i.d.-rounds assumption; it is what the sub-Gaussian
  `add`/sum API consumes — the same independence idiom LF1 threads).

`Ŝₙ = (∑_{i<n} Yᵢ) / n` is the empirical CHSH estimator (`empiricalCHSH`).

## What this delivers

* `e91_chsh_concentration` — **the headline**: a genuine Hoeffding tail,
  `μ.real {ω | Ŝₙ ω ≤ S − ε} ≤ exp(−n ε² / (2·((b−a)/2)²))`, proved through
  Mathlib's sub-Gaussian pipeline (Hoeffding's lemma
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` per round, summed with
  `measure_sum_range_ge_le_of_iIndepFun`, the Chernoff `measure_ge_le` tail). The
  exponent genuinely decays in `n` (linear in `n`, constant `c = ((b−a)/2)² > 0`
  whenever `a < b`).
* `e91_finite_key_confidence` — **the bridge**: for a true violation
  `2 < S ≤ 2√2`, (1) the asymptotic rate is positive
  (`e91_key_rate_pos_of_chsh`), (2) the failure-to-certify probability
  `μ.real {ω | Ŝₙ ω ≤ 2}` is `≤ exp(−n (S−2)²/(2·((b−a)/2)²))`, and (3) the
  estimator certifies (`2 < Ŝₙ`) with probability `≥ 1 − exp(−n (S−2)²/…)`. The
  failure probability is exponentially small in the number of rounds.

## Honest scope

This is finite-**sample** confidence: Hoeffding concentration of the CHSH
estimator. It is **not** a composable finite-key security proof. A full
finite-key analysis (Renner smooth min-entropy, the leftover-hash / privacy-
amplification accounting, the entropy-accumulation theorem) needs infrastructure
Mathlib does not have (MATHLIB-ABSENT(file:Mathlib/InformationTheory/QuantumKeyDistribution)); none of it is claimed here. The per-round independence and
boundedness are explicit modelling hypotheses (not derived). QM-validity
inner-product layer; no CSD ontology. Foundational triple only (no `busch`).

## Source

Hoeffding 1963; Pironio et al. 2009 (DIQKD finite-key); Tomamichel–Lim–
Gisin–Renner 2012 (composable finite-key, *not* formalised here).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CSD
namespace Empirical
namespace QM
namespace E91

section FiniteKey

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The empirical CHSH estimator over `n` rounds: the sample mean of the
per-round CHSH statistics `Y`, `Ŝₙ(ω) = (∑_{i<n} Yᵢ ω) / n`. -/
noncomputable def empiricalCHSH (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)

/-- **E91 finite-sample CHSH concentration (Hoeffding tail).** For `n` bounded
(`Y i ∈ [a,b]` a.s.), unbiased (`μ[Y i] = S`), independent (`iIndepFun Y μ`)
per-round CHSH statistics, the empirical estimator `Ŝₙ` deviates below the true
value `S` by `ε ≥ 0` with exponentially small probability:

`μ.real {ω | Ŝₙ ω ≤ S − ε} ≤ exp(−n ε² / (2·((b−a)/2)²))`.

The Hoeffding constant is `c = ((b−a)/2)²` (the per-round sub-Gaussian
parameter). The exponent is linear in `n` and strictly negative for `ε > 0`,
`a < b`, so the bound genuinely decays. Proved by Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, per round, on the centered
variable `S − Y i`) + the i.i.d. sub-Gaussian Hoeffding sum
(`measure_sum_range_ge_le_of_iIndepFun`, which is the Chernoff `measure_ge_le`
tail of the summed sub-Gaussian). -/
theorem e91_chsh_concentration [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {S a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≤ b)
    (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[Y i] = S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | empiricalCHSH Y n ω ≤ S - ε}
      ≤ Real.exp (-(n : ℝ) * ε ^ 2 / (2 * ((b - a) / 2) ^ 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- centered per-round variables  X i ω = S − Y i ω
  set X : ℕ → Ω → ℝ := fun i => (fun y : ℝ => S - y) ∘ Y i with hXdef
  have hXapp : ∀ i ω, X i ω = S - Y i ω := fun _ _ => rfl
  -- independence of the centered variables
  have hXindep : iIndepFun X μ :=
    hindep.comp (fun _ => fun y : ℝ => S - y) (fun _ => measurable_const.sub measurable_id)
  -- common per-round sub-Gaussian (Hoeffding) parameter
  set cG : ℝ≥0 := (‖(S - a) - (S - b)‖₊ / 2) ^ 2 with hcGdef
  have hsub : ∀ i, HasSubgaussianMGF (X i) cG μ := by
    intro i
    have hb' : ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (S - b) (S - a) := by
      filter_upwards [hbound i] with ω hω
      exact ⟨by simp only [hXapp]; linarith [hω.2], by simp only [hXapp]; linarith [hω.1]⟩
    have hint : Integrable (Y i) μ :=
      Integrable.of_mem_Icc a b (hmeas i).aemeasurable (hbound i)
    have hc0 : μ[X i] = 0 := by
      simp only [hXapp]
      rw [integral_sub (integrable_const S) hint, integral_const, hmean i]
      simp
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((measurable_const.sub (hmeas i)).aemeasurable) hb' hc0
  -- Hoeffding tail for the centered sum at threshold (n·ε)
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hXindep (c := cG)
    (n := n) (fun i _ => hsub i) (ε := (n : ℝ) * ε) (by positivity)
  -- identify the deviation event with the centered-sum tail event
  have hset : {ω | empiricalCHSH Y n ω ≤ S - ε}
      = {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, empiricalCHSH, hXapp]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      div_le_iff₀ hnpos]
    constructor <;> intro h <;> nlinarith [h]
  -- the Hoeffding constant, coerced to ℝ
  have hcG : ((cG : ℝ≥0) : ℝ) = ((b - a) / 2) ^ 2 := by
    rw [hcGdef]
    push_cast
    rw [Real.norm_eq_abs, show S - a - (S - b) = b - a by ring,
      abs_of_nonneg (by linarith)]
  -- exponent bookkeeping:  −(nε)²/(2 n c) = −n ε²/(2 c)
  have harg : -((n : ℝ) * ε) ^ 2 / (2 * (n : ℝ) * ((b - a) / 2) ^ 2)
      = -(n : ℝ) * ε ^ 2 / (2 * ((b - a) / 2) ^ 2) := by
    rw [show -((n : ℝ) * ε) ^ 2 = (n : ℝ) * (-(n : ℝ) * ε ^ 2) by ring,
      show 2 * (n : ℝ) * ((b - a) / 2) ^ 2 = (n : ℝ) * (2 * ((b - a) / 2) ^ 2) by ring,
      mul_div_mul_left _ _ (ne_of_gt hnpos)]
  calc μ.real {ω | empiricalCHSH Y n ω ≤ S - ε}
      = μ.real {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, X i ω} := by rw [hset]
    _ ≤ Real.exp (-((n : ℝ) * ε) ^ 2 / (2 * (n : ℝ) * (cG : ℝ))) := key
    _ = Real.exp (-(n : ℝ) * ε ^ 2 / (2 * ((b - a) / 2) ^ 2)) := by
        rw [hcG]; exact congrArg Real.exp harg

/-- **E91 finite-key confidence (the bridge).** For a *true* CHSH violation
`2 < S ≤ 2√2` certified by independent, bounded, unbiased per-round statistics:

1. the asymptotic DI secret-key rate is strictly positive
   (`e91_key_rate_pos_of_chsh`);
2. the **failure-to-certify** probability — the empirical estimator landing at or
   below the classical ceiling `2` — is exponentially small in `n`,
   `μ.real {ω | Ŝₙ ω ≤ 2} ≤ exp(−n (S−2)² / (2·((b−a)/2)²))`;
3. equivalently, the estimator **certifies** (`2 < Ŝₙ`) with probability
   `≥ 1 − exp(−n (S−2)² / (2·((b−a)/2)²))`.

This is the finite-round content: the asymptotic positive key rate plus a
finite-sample confidence that the estimate witnesses the violation. It is **not**
composable finite-key security (no smooth min-entropy / leftover hashing); see
the module docstring. -/
theorem e91_finite_key_confidence [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {S a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≤ b)
    (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[Y i] = S)
    (hS : 2 < S) (hS' : S ≤ 2 * Real.sqrt 2) :
    0 < e91KeyRate S
      ∧ μ.real {ω | empiricalCHSH Y n ω ≤ 2}
          ≤ Real.exp (-(n : ℝ) * (S - 2) ^ 2 / (2 * ((b - a) / 2) ^ 2))
      ∧ 1 - Real.exp (-(n : ℝ) * (S - 2) ^ 2 / (2 * ((b - a) / 2) ^ 2))
          ≤ μ.real {ω | 2 < empiricalCHSH Y n ω} := by
  -- (2) failure-to-certify is the deviation event at ε = S − 2
  have hconc := e91_chsh_concentration hn hab hmeas hindep hbound hmean
    (ε := S - 2) (by linarith)
  rw [show S - (S - 2) = (2 : ℝ) by ring] at hconc
  -- (1) asymptotic positivity, (2) failure bound, (3) certification bound
  refine ⟨e91_key_rate_pos_of_chsh hS hS', hconc, ?_⟩
  -- (3) complement: certification probability ≥ 1 − failure bound
  have hŜmeas : Measurable (empiricalCHSH Y n) := by
    unfold empiricalCHSH
    exact (Finset.measurable_sum _ (fun i _ => hmeas i)).div measurable_const
  have hms : MeasurableSet {ω | empiricalCHSH Y n ω ≤ 2} :=
    measurableSet_le hŜmeas measurable_const
  have hcompl : {ω | 2 < empiricalCHSH Y n ω} = {ω | empiricalCHSH Y n ω ≤ 2}ᶜ := by
    ext ω; simp [not_le]
  rw [hcompl, measureReal_compl hms, probReal_univ]
  linarith [hconc]

end FiniteKey

end E91
end QM
end Empirical
end CSD
