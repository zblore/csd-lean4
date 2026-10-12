/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.InformationTheory.FiniteEntropy

/-!
# The divergence from the uniform law is at most its chi-squared distance

**Category:** 1-Mathlib (CSD-free).
BACKLOG #130's first half.

Mathlib has the Kullback-Leibler divergence and no comparison inequality for it. The one a rate
argument reaches for is the chi-squared bound: `klDiv` is at most the chi-squared distance, which is
quadratic in the deviation and therefore converts an `L²` estimate into a divergence estimate.
Against the uniform law on a finite type with `n` points the chi-squared distance is
`n · ∑ (p x − 1/n)²`, and that is the form proved here.

* ★★★ `log_card_sub_measureEntropy_le_chiSq` — the real-valued inequality
  `log n − H(μ) ≤ n · ∑ (μ{x} − 1/n)²`;
* ★★★ `klDiv_uniformOn_univ_le_chiSq` — the same read through `klDiv_uniformOn_univ`, which is the
  statement a consumer uses.

## How it goes

Both sides are the *same* sum, compared pointwise. Writing `p x` for `μ.real {x}`:

* the left side is `∑ p x · log (n · p x)`, because `∑ p x = 1` turns `log n` into `∑ p x · log n`
  and the `p x = 0` terms contribute nothing to either half;
* `log t ≤ t − 1` (`Real.log_le_sub_one_of_pos`) at `t = n · p x`, multiplied by `p x ≥ 0`, gives
  `p x · log (n · p x) ≤ p x · (n · p x − 1)` — the only analysis in the file;
* and `∑ p x · (n · p x − 1) = n · ∑ p x² − 1` is *equal* to `n · ∑ (p x − 1/n)²`, again by
  `∑ p x = 1`. So the inequality is tight exactly where `log t = t − 1`, at `p x = 1/n`.

## Honest scope

⚠️ **Uniform reference only.** The general bound `klDiv μ ν ≤ ∑ (μ{x} − ν{x})²/ν{x}` needs the
Radon-Nikodym derivative of `μ` against an arbitrary `ν`, which `FiniteEntropy.lean` computes only
for the uniform law (`withDensity_uniformOn_univ`). A consumer whose reference is uniform *as a
theorem* can use this; one whose reference is merely believed uniform has to carry that as a
hypothesis.

⚠️ **Finite type only**, and both measures are probability measures: `klDiv`'s correction terms are
dropped by `klDiv_uniformOn_univ`, which assumes it.

⚠️ **It is an inequality, not an equivalence.** The chi-squared distance can be arbitrarily larger
than the divergence, so a chi-squared bound that fails to tend to zero says nothing about `klDiv`.

## References

T. Cover, J. Thomas, *Elements of Information Theory*, 2nd ed., §11.6 (the chi-squared comparison);
`FiniteEntropy.lean` (`measureEntropy`, `klDiv_uniformOn_univ`, `sum_measureReal_singleton`);
`Mathlib.Analysis.SpecialFunctions.Log.Basic` (`Real.log_le_sub_one_of_pos`);
`specs/future-work.md`; `specs/BACKLOG.md` #130, #118.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]

/-- ★★★ **The entropy defect is at most the chi-squared distance from the uniform law.**

`log n − H(μ) ≤ n · ∑ (μ{x} − 1/n)²`, where `n` is the cardinality. Both sides are the same sum
read two ways, compared pointwise by `log t ≤ t − 1`. -/
theorem log_card_sub_measureEntropy_le_chiSq (μ : Measure α) [IsProbabilityMeasure μ] :
    Real.log (Fintype.card α) - measureEntropy μ
      ≤ (Fintype.card α : ℝ) * ∑ x, (μ.real {x} - (Fintype.card α : ℝ)⁻¹) ^ 2 := by
  set n : ℝ := (Fintype.card α : ℝ) with hndef
  have hn0 : (0 : ℝ) < n := by
    rw [hndef]
    exact_mod_cast Fintype.card_pos
  have hp : ∀ x : α, 0 ≤ μ.real {x} := fun _ => measureReal_nonneg
  have hs1 : ∑ x, μ.real {x} = 1 := sum_measureReal_singleton μ
  -- the left-hand side as one sum over the points
  have hL : Real.log n - measureEntropy μ
      = ∑ x, μ.real {x} * Real.log (μ.real {x} * n) := by
    have hterm : ∀ x : α, μ.real {x} * Real.log (μ.real {x} * n)
        = μ.real {x} * Real.log n - Real.negMulLog (μ.real {x}) := by
      intro x
      rcases eq_or_lt_of_le (hp x) with h | h
      · rw [← h, Real.negMulLog]
        simp
      · rw [Real.log_mul (ne_of_gt h) (ne_of_gt hn0), Real.negMulLog]
        ring
    rw [measureEntropy]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs1, one_mul]
  -- `log t ≤ t - 1`, the only analysis here
  have hpt : ∀ x : α, μ.real {x} * Real.log (μ.real {x} * n)
      ≤ μ.real {x} * (μ.real {x} * n - 1) := by
    intro x
    rcases eq_or_lt_of_le (hp x) with h | h
    · rw [← h]
      simp
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (mul_pos h hn0)) (hp x)
  -- and the right-hand side is the same sum, by `∑ p = 1`
  have hcardn : ((Finset.univ : Finset α).card : ℝ) = n := by
    rw [Finset.card_univ, hndef]
  have hR : n * ∑ x, (μ.real {x} - n⁻¹) ^ 2
      = ∑ x, μ.real {x} * (μ.real {x} * n - 1) := by
    have hexp : ∀ x : α, (μ.real {x} - n⁻¹) ^ 2
        = μ.real {x} ^ 2 - 2 * n⁻¹ * μ.real {x} + n⁻¹ ^ 2 := fun _ => by ring
    have hterm : ∀ x : α, μ.real {x} * (μ.real {x} * n - 1)
        = n * μ.real {x} ^ 2 - μ.real {x} := fun _ => by ring
    simp only [hexp, hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcardn, hs1]
    field_simp
    ring
  calc Real.log n - measureEntropy μ
      = ∑ x, μ.real {x} * Real.log (μ.real {x} * n) := hL
    _ ≤ ∑ x, μ.real {x} * (μ.real {x} * n - 1) := Finset.sum_le_sum fun x _ => hpt x
    _ = n * ∑ x, (μ.real {x} - n⁻¹) ^ 2 := hR.symm

/-- ★★★ **The chi-squared bound on the divergence from the uniform law.** This is the form a rate
argument consumes: an `L²` estimate on the point masses bounds `klDiv`, at the cost of one factor of
the cardinality. -/
theorem klDiv_uniformOn_univ_le_chiSq (μ : Measure α) [IsProbabilityMeasure μ] :
    klDiv μ (uniformOn (univ : Set α))
      ≤ ENNReal.ofReal ((Fintype.card α : ℝ) * ∑ x, (μ.real {x} - (Fintype.card α : ℝ)⁻¹) ^ 2) := by
  rw [klDiv_uniformOn_univ μ]
  exact ENNReal.ofReal_le_ofReal (log_card_sub_measureEntropy_le_chiSq μ)

end InformationTheory

end
