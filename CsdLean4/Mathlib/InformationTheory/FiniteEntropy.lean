/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.InformationTheory.KlDivArrow

/-!
# Shannon entropy on a finite type, and the H-theorem in entropy form

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #110, the residue
#109 named.

Mathlib has the Kullback–Leibler divergence but **no Shannon entropy of a measure** — not for a finite
type, not anywhere. #109 proved the arrow of time in its divergence form, which is the general one;
this file supplies the identity that turns it into the textbook statement, and the two classical
consequences.

## What is proved

* `measureEntropy μ = ∑ x, negMulLog (μ.real {x})` — Shannon entropy of a measure on a finite type;
* ★★ `withDensity_uniformOn_univ` — **the density of a measure against the uniform law is
  `card · μ{x}`**, which is the Radon–Nikodym computation the identity needs and the only real work
  here. It holds for **any** measure on a finite type, not only a probability measure, and so do
  `absolutelyContinuous_uniformOn_univ` and ★★ `llr_uniformOn_univ_ae` — hence the log-likelihood
  ratio against the uniform law is `log (card · μ{x})` almost everywhere;
* ★★★ `integral_llr_uniformOn_univ` and ★★★ `klDiv_uniformOn_univ` — **the identity**:
  `klDiv μ uniform = ENNReal.ofReal (log card − measureEntropy μ)`. The vanishing of the two
  correction terms is what makes it clean: both measures are probability measures;
* ★★ `measureEntropy_le_log_card` — **the maximum-entropy theorem**, from Gibbs' inequality, and
  ★ `measureEntropy_uniformOn_univ` — the uniform law attains it, so the bound is tight;
* ★★★ `monotone_measureEntropy_compIterate` — **the H-theorem in entropy form**: under a Markov kernel
  that fixes the uniform law, Shannon entropy is **non-decreasing**, monotonically along the whole
  trajectory. This is the classical statement, and it is #109's divergence form composed with the
  identity above.

## Honest scope

⚠️ **The uniform reference is not optional.** Entropy increases along a kernel that fixes the
*uniform* law; a kernel with some other stationary law moves entropy either way, and what is monotone
then is the divergence from that law (#109), not the entropy. The two statements coincide only here.

⚠️ **Finite type only.** `measureEntropy` sums over `Fintype.card α` point masses. Differential
entropy, countable types with infinite entropy, and the conditional and joint entropies are all
untouched.

⚠️ **No convergence, and no rate.** Monotone is not strictly increasing, and nothing says the entropy
reaches `log card`: a kernel can be the identity.

References: T. Cover, J. Thomas, *Elements of Information Theory*, 2nd ed., Thm 2.6.4 (maximum
entropy) and §4.4 (the H-theorem for a doubly stochastic chain);
`Mathlib.InformationTheory.KullbackLeibler.Basic` (`klDiv`, `llr`,
`integral_llr_add_sub_measure_univ_nonneg` = Gibbs), `Mathlib.Probability.UniformOn`;
`KlDivArrow.lean` (#109's Cat-1 half).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace InformationTheory

theorem card_ne_zero_ennreal (α : Type*) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ≥0∞) ≠ 0 := by
  simp [Fintype.card_ne_zero]

theorem card_ne_zero_real (α : Type*) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ) ≠ 0 := by
  simp [Fintype.card_ne_zero]

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Shannon entropy** of a measure on a finite type: `−∑ p log p` over the point masses. -/
noncomputable def measureEntropy [Fintype α] (μ : Measure α) : ℝ :=
  ∑ x, Real.negMulLog (μ.real {x})

section Finite

variable [Fintype α] [Nonempty α]

instance isProbabilityMeasure_uniformOn_univ :
    IsProbabilityMeasure (uniformOn (univ : Set α)) :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

omit [Nonempty α] in
theorem uniformOn_univ_singleton (x : α) :
    uniformOn (univ : Set α) {x} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, one_div]

omit [Nonempty α] in
theorem measureReal_uniformOn_univ_singleton (x : α) :
    (uniformOn (univ : Set α)).real {x} = (Fintype.card α : ℝ)⁻¹ := by
  rw [Measure.real, uniformOn_univ_singleton]
  simp

omit [Nonempty α] in
/-- Every measure on a finite type is the sum of its point masses, restricted. -/
theorem measure_eq_sum_restrict_singleton (μ : Measure α) (s : Set α) :
    μ s = ∑ x, (μ.restrict s) {x} := by
  rw [← Measure.restrict_apply_univ, ← lintegral_one, lintegral_fintype]
  simp

omit [Nonempty α] in
theorem sum_measureReal_singleton (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ x, μ.real {x} = 1 := by
  have h := integral_fintype (μ := μ) (f := fun _ : α => (1 : ℝ)) Integrable.of_finite
  simp

/-! ### The density against the uniform law -/

/-- ★★ **The density of a law against the uniform law is `card · μ{x}`.** This is the Radon–Nikodym
computation the entropy identity runs on, and the only real work in this file. -/
theorem withDensity_uniformOn_univ (μ : Measure α) :
    (uniformOn (univ : Set α)).withDensity (fun x => (Fintype.card α : ℝ≥0∞) * μ {x}) = μ := by
  ext s hs
  rw [withDensity_apply _ hs, lintegral_fintype, measure_eq_sum_restrict_singleton μ s]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measure.restrict_apply (measurableSet_singleton x),
    Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ s
  · rw [Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hx), uniformOn_univ_singleton,
      mul_comm (Fintype.card α : ℝ≥0∞) (μ {x}), mul_assoc,
      ENNReal.mul_inv_cancel (card_ne_zero_ennreal α) (ENNReal.natCast_ne_top _), mul_one]
  · rw [Set.singleton_inter_eq_empty.2 hx]
    simp

theorem absolutelyContinuous_uniformOn_univ (μ : Measure α) :
    μ ≪ uniformOn (univ : Set α) := by
  rw [← withDensity_uniformOn_univ μ]
  exact withDensity_absolutelyContinuous _ _

/-- ★★ **So the log-likelihood ratio against the uniform law is `log (card · μ{x})`**, almost
everywhere. -/
theorem llr_uniformOn_univ_ae (μ : Measure α) :
    llr μ (uniformOn (univ : Set α)) =ᵐ[μ]
      fun x => Real.log ((Fintype.card α : ℝ) * μ.real {x}) := by
  have hrn := Measure.rnDeriv_withDensity (uniformOn (univ : Set α))
    (f := fun x => (Fintype.card α : ℝ≥0∞) * μ {x}) Measurable.of_discrete
  rw [withDensity_uniformOn_univ μ] at hrn
  filter_upwards [hrn.filter_mono (absolutelyContinuous_uniformOn_univ μ).ae_le] with x hx
  rw [llr, hx, ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real]

/-! ### The identity, and the two classical consequences -/

/-- ★★★ **The entropy identity, in integral form.** -/
theorem integral_llr_uniformOn_univ (μ : Measure α) [IsProbabilityMeasure μ] :
    ∫ x, llr μ (uniformOn (univ : Set α)) x ∂μ
      = Real.log (Fintype.card α) - measureEntropy μ := by
  have hterm : ∀ x : α, μ.real {x} * Real.log ((Fintype.card α : ℝ) * μ.real {x})
      = μ.real {x} * Real.log (Fintype.card α) - Real.negMulLog (μ.real {x}) := by
    intro x
    rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := ({x} : Set α))) with h | h
    · rw [← h, Real.negMulLog]
      simp
    · rw [Real.log_mul (card_ne_zero_real α) (ne_of_gt h), Real.negMulLog]
      ring
  rw [integral_congr_ae (llr_uniformOn_univ_ae μ),
    integral_fintype (Integrable.of_finite (μ := μ))]
  simp only [smul_eq_mul, hterm, measureEntropy]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_measureReal_singleton μ, one_mul]

/-- ★★★ **The identity**: the divergence from the uniform law is `log card − entropy`. The two
correction terms in `klDiv`'s definition vanish because both measures are probability measures. -/
theorem klDiv_uniformOn_univ (μ : Measure α) [IsProbabilityMeasure μ] :
    klDiv μ (uniformOn (univ : Set α))
      = ENNReal.ofReal (Real.log (Fintype.card α) - measureEntropy μ) := by
  rw [klDiv_of_ac_of_integrable (absolutelyContinuous_uniformOn_univ μ) Integrable.of_finite,
    integral_llr_uniformOn_univ μ]
  simp

/-- ★★ **The maximum-entropy theorem**: no law on a finite type has entropy above `log card`. This is
Gibbs' inequality read through the identity. -/
theorem measureEntropy_le_log_card (μ : Measure α) [IsProbabilityMeasure μ] :
    measureEntropy μ ≤ Real.log (Fintype.card α) := by
  have h := integral_llr_add_sub_measure_univ_nonneg
    (absolutelyContinuous_uniformOn_univ μ) (Integrable.of_finite (μ := μ))
  rw [integral_llr_uniformOn_univ μ] at h
  simp only [probReal_univ] at h
  linarith

/-- ★ **And the uniform law attains it**, so the bound is tight. -/
theorem measureEntropy_uniformOn_univ :
    measureEntropy (uniformOn (univ : Set α)) = Real.log (Fintype.card α) := by
  rw [measureEntropy]
  simp only [measureReal_uniformOn_univ_singleton, Real.negMulLog, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  field_simp

/-! ### The H-theorem in entropy form -/

/-- ★★★ **The H-theorem in entropy form.** Under a Markov kernel that fixes the uniform law, Shannon
entropy is non-decreasing, monotonically along the whole trajectory.

This is the classical statement, and it is #109's divergence form (`antitone_klDiv_compIterate`)
composed with the identity: `klDiv · uniform` and `measureEntropy` move in opposite directions, and
the maximum-entropy bound is what licenses stripping `ENNReal.ofReal`. -/
theorem monotone_measureEntropy_compIterate (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α α) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ uniformOn (univ : Set α) = uniformOn (univ : Set α)) :
    Monotone fun n : ℕ => measureEntropy (μ.compIterate κ n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h1 := antitone_klDiv_compIterate (μ := μ) κ hκ (Nat.le_succ n)
  simp only [klDiv_uniformOn_univ] at h1
  rw [ENNReal.ofReal_le_ofReal_iff
    (by linarith [measureEntropy_le_log_card (μ.compIterate κ n)])] at h1
  linarith

end Finite

end InformationTheory

end
