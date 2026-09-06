/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.IIDCoordinateProcess

/-!
# The canonical i.i.d. trial process, over an arbitrary law

**Category:** 1-Mathlib (CSD-free upstream candidate).

`LF4/TrialWitness.lean` built the canonical i.i.d. process for the Fubini–Study law on `ℂℙ^{N−1}`
(`fsTrialSpace` / `fsTrialMeasure` / `fsTrial`, with its law and independence lemmas). Nothing in
that construction is specific to either the space or the measure: it is `Measure.infinitePi` of a
constant family, evaluation as the trial, and the standard independence of coordinates.

The fibred arena needs the same thing for `epistemicMeasure` on `KSigma N`, which is the second
consumer — so by CONVENTIONS §9 (rule of two) the construction is extracted here rather than copied.

## What is provided

For any measurable space `X` and probability measure `μ`:

* `iidSpace X` — the trial space `ℕ → X`;
* `iidMeasure μ` — the i.i.d. law, `Measure.infinitePi (fun _ => μ)`;
* `iidTrial X n` — the `n`-th trial (evaluation), with `iidTrial_measurable`;
* `iidTrial_law` — each trial has law `μ`, the `hlaw` hypothesis of the frequency theorems;
* `iidTrial_iIndepFun` and `iidTrial_pairwise_indepFun_indicator` — the `hindep` hypothesis.

Those five are exactly the inputs `born_frequency_convergence_partition` asks for, so any frequency
theorem stated over an arbitrary law can be instantiated on the canonical process by supplying them.

⚠️ **`LF4/TrialWitness.lean`'s `fsTrial*` block is now a fold candidate**: it is this construction at
`μ := fubiniStudyMeasure p₀`. It is left in place because it has live consumers whose statements name
it, and re-pointing them is churn without benefit; the duplication is recorded here rather than left
for someone to rediscover.

## References

`LF4/TrialWitness.lean` (`fsTrialSpace`, `fsTrialMeasure`, `fsTrial`, and the twins of every lemma
below); `LF4/BornFrequencyPartition.lean` (`born_frequency_convergence_partition`, whose hypotheses
these supply); `RecordLayer/BasinFrequency.lean` (the second consumer); `CONVENTIONS.md` §9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- The canonical trial space: one draw per natural number. -/
abbrev iidSpace (X : Type*) : Type _ := ℕ → X

/-- The canonical i.i.d. law with marginal `μ`. -/
noncomputable def iidMeasure (μ : Measure X) : Measure (iidSpace X) :=
  Measure.infinitePi (fun _ : ℕ => μ)

instance instIsProbabilityMeasureIidMeasure (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (iidMeasure μ) := by
  rw [iidMeasure]; infer_instance

/-- The `n`-th canonical trial. -/
def iidTrial (X : Type*) (n : ℕ) : iidSpace X → X := fun ω => ω n

/-- Each canonical trial is measurable — the `hX` hypothesis. -/
theorem iidTrial_measurable (n : ℕ) : Measurable (iidTrial X n) :=
  measurable_pi_apply n

/-- Each canonical trial has law `μ` — the `hlaw` hypothesis. -/
theorem iidTrial_law (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure.map (iidTrial X n) (iidMeasure μ) = μ :=
  Measure.infinitePi_map_eval (fun _ : ℕ => μ) n

/-- The canonical trials are jointly independent. -/
theorem iidTrial_iIndepFun (μ : Measure X) [IsProbabilityMeasure μ] :
    iIndepFun (iidTrial X) (iidMeasure μ) :=
  iIndepFun_eval_infinitePi μ

/-- Indicators of a fixed event across trials are pairwise independent — the `hindep` hypothesis of
the frequency theorems, in the shape they ask for. -/
theorem iidTrial_pairwise_indepFun_indicator (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) :
    ∀ i, Pairwise
      (Function.onFun (fun f g : iidSpace X → ℝ => IndepFun f g (iidMeasure μ))
        (fun n => Set.indicator ((iidTrial X n) ⁻¹' S i) (fun _ => (1 : ℝ)))) :=
  (iidTrial_iIndepFun μ).pairwise_indepFun_indicator_preimage S hS

end MeasureTheory
