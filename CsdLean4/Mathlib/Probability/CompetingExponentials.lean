/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Competing exponential clocks: the first to fire wins in proportion to its rate

**Category:** 1-Mathlib. No CSD content: this is the classical competing-risks computation for
independent exponential waiting times.

It is the engine for the record layer's **order-free** Born partition
(`specs/q12-fibre-mechanism-scoping.md`, brick `Q12-b`). The partition already in the corpus
(`RecordLayer/BornFibrePartition.cdfCell`) stacks intervals in index order, which reproduces Born
but imposes an arbitrary **outcome order**; `record-layer-plan.md` §3b asks instead for the
symmetric noisy-argmax / race form, in which no index is privileged.

## The two one-dimensional facts

* `expMeasure_Ioi` — the survival function: `P(T > t) = e^{-rt}` for `t ≥ 0`.
* `lintegral_exp_neg_expMeasure` — the rescaling identity
  `∫ e^{-St} d(Exp r) = r/(r+S)`. Proved *without* evaluating an improper integral: the integrand
  times the `Exp r` density is a constant multiple of the `Exp (r+S)` density, whose total mass is
  one (`lintegral_exponentialPDF_eq_one`).

## The race

* `raceCell i` — the readings on which clock `i` fires strictly first. No index order, no
  cumulative sums, no privileged outcome.
* `raceCell_pairwiseDisjoint` — the partition content; needs no hypothesis on the rates.
* ★★ `measure_raceCell` — clock `i` wins with probability `bᵢ / Σⱼ bⱼ`, and
  ★★ `measure_raceCell_of_sum_eq_one` — hence exactly `bᵢ` for a probability vector of rates.

## ⚠️ Scope, and two findings worth carrying

Nothing here is a new physical claim. The Born numbers this feeds are already proved for the
ordered partition (`RecordLayer.volume_bornCell`); what the race buys is that the *construction*
privileges no outcome.

Two things the build turned up, both recorded in `specs/q12-fibre-mechanism-scoping.md`:

* **The race does not fit the corpus's record-layer interface.** `RecordLayer.DeIsolationInteraction`
  takes `pointer : ℝ → Fin n` — a **one-dimensional** fibre — whereas the race needs `Fin (n+1) → ℝ`.
  That is not an accident of this construction: `record-layer-plan.md` §3b states the minimal fibre
  dimension is `n − 1`. So the existing interface is *committed to the ordered CDF construction*,
  and admitting the symmetric race would require generalising it. `Q12-a`'s witness
  (`cdfDeIsolationInteraction`) remains the only instance.
* **Strictly positive rates only.** An exponential clock needs `r > 0`, so `measure_raceCell`
  applies to states with every amplitude nonzero. A zero amplitude means a clock that never fires,
  which is the right physics but is outside `expMeasure`'s domain.

Reference: `specs/q12-fibre-mechanism-scoping.md`; `specs/record-layer-plan.md` §3b–§3c;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace ProbabilityTheory

/-- **The survival function of an exponential clock**: `P(T > t) = e^{-rt}` for `t ≥ 0`. -/
lemma expMeasure_Ioi {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    expMeasure r (Ioi t) = ENNReal.ofReal (exp (-(r * t))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic t) = ENNReal.ofReal (1 - exp (-(r * t))) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr t, if_pos ht]
  have hle : exp (-(r * t)) ≤ 1 := by
    rw [exp_le_one_iff]
    nlinarith
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

/-- **The rescaling identity** `∫ e^{-St} d(Exp r) = r/(r+S)`.

No improper integral is evaluated: `e^{-St}` times the `Exp r` density is exactly `r/(r+S)` times
the `Exp (r+S)` density, and that density integrates to one. -/
lemma lintegral_exp_neg_expMeasure {r S : ℝ} (hr : 0 < r) (hS : 0 ≤ S) :
    ∫⁻ t, ENNReal.ofReal (exp (-(S * t))) ∂(expMeasure r)
      = ENNReal.ofReal (r / (r + S)) := by
  have hrS : 0 < r + S := by linarith
  have hmeasPDF : ∀ q : ℝ, Measurable (exponentialPDF q) := fun q =>
    (measurable_exponentialPDFReal q).ennreal_ofReal
  have hdens : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [hdens, lintegral_withDensity_eq_lintegral_mul _ (hmeasPDF r)
    (Measurable.ennreal_ofReal (by fun_prop))]
  have hpt : ∀ t : ℝ, (exponentialPDF r * fun t => ENNReal.ofReal (exp (-(S * t)))) t
      = ENNReal.ofReal (r / (r + S)) * exponentialPDF (r + S) t := by
    intro t
    simp only [Pi.mul_apply]
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_assoc, ← exp_add, show -(r * t) + -(S * t) = -((r + S) * t) by ring]
      field_simp
    · rw [exponentialPDF_of_neg (lt_of_not_ge ht), exponentialPDF_of_neg (lt_of_not_ge ht),
        zero_mul, mul_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (hmeasPDF (r + S)), lintegral_exponentialPDF_eq_one hrS, mul_one]

/-- The exponential measure lives on `[0, ∞)`. -/
lemma expMeasure_ae_nonneg {r : ℝ} (hr : 0 < r) : ∀ᵐ t ∂(expMeasure r), 0 ≤ t := by
  have hprob := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic 0) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr 0, if_pos le_rfl]
    norm_num
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) hIic
  simp only [mem_ofPred_eq, not_le] at ht
  exact le_of_lt ht

/-! ### The race -/

variable {n : ℕ}

/-- **The race cell**: the clock readings on which clock `i` fires first.

Note what is *absent*: no index order, no cumulative sums, no privileged outcome. Relabelling the
clocks permutes the cells, which is exactly the symmetry `record-layer-plan.md` §3b asks for and
which `cdfCell` does not have. -/
def raceCell (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) := {ξ | ∀ j, j ≠ i → ξ i < ξ j}

lemma measurableSet_raceCell (i : Fin (n + 1)) : MeasurableSet (raceCell i) := by
  have : raceCell i = ⋂ j ∈ {j : Fin (n + 1) | j ≠ i}, {ξ : Fin (n + 1) → ℝ | ξ i < ξ j} := by
    ext ξ; simp [raceCell]
  rw [this]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))

/-- ★★ **The first clock to fire wins in proportion to its rate.**

For independent exponential clocks with rates `b`, clock `i` fires first with probability
`bᵢ / Σⱼ bⱼ`. Feeding a probability vector of rates (`Σ b = 1`) this is `bᵢ` on the nose — the
order-free Born partition.

The proof splits coordinate `i` off the product (`measurePreserving_piFinSuccAbove`), reads the
remaining clocks' survival as a *box* (`Measure.pi_pi` on `Set.pi univ (fun _ => Ioi t)`), and
integrates the resulting `e^{-St}` against clock `i` by `lintegral_exp_neg_expMeasure`. -/
theorem measure_raceCell (b : Fin (n + 1) → ℝ) (hb : ∀ j, 0 < b j) (i : Fin (n + 1)) :
    Measure.pi (fun j => expMeasure (b j)) (raceCell i)
      = ENNReal.ofReal (b i / ∑ j, b j) := by
  classical
  have : ∀ j : Fin (n + 1), IsProbabilityMeasure (expMeasure (b j)) :=
    fun j => isProbabilityMeasure_expMeasure (hb j)
  set S : ℝ := ∑ j : Fin n, b (i.succAbove j) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hb _).le)
  have hsum : ∑ j, b j = b i + S := Fin.sum_univ_succAbove b i
  -- the winning set, transported through the split
  set W : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j, p.1 < p.2 j} with hW
  have hWmeas : MeasurableSet W := by
    have : W = ⋂ j, {p : ℝ × (Fin n → ℝ) | p.1 < p.2 j} := by ext p; simp [hW]
    rw [this]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd))
  have hpre : raceCell i = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' W := by
    ext ξ
    simp only [raceCell, Set.mem_preimage, Set.mem_ofPred_eq, hW]
    show (∀ j, j ≠ i → ξ i < ξ j) ↔ ∀ j : Fin n, ξ i < ξ (i.succAbove j)
    refine ⟨fun h j => h _ (Fin.succAbove_ne i j), fun h j hj => ?_⟩
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    exact h k
  have hmp := measurePreserving_piFinSuccAbove (fun j => expMeasure (b j)) i
  have hnull : NullMeasurableSet W
      ((expMeasure (b i)).prod (Measure.pi fun j : Fin n => expMeasure (b (i.succAbove j)))) :=
    hWmeas.nullMeasurableSet
  rw [hpre, hmp.measure_preimage hnull, Measure.prod_apply hWmeas]
  -- the slice at `t` is a box, so `pi_pi` applies
  have hslice : ∀ t : ℝ, 0 ≤ t →
      Measure.pi (fun j : Fin n => expMeasure (b (i.succAbove j))) (Prod.mk t ⁻¹' W)
        = ENNReal.ofReal (exp (-(S * t))) := by
    intro t ht
    have hbox : (Prod.mk t ⁻¹' W) = Set.pi univ (fun _ : Fin n => Ioi t) := by
      ext ζ; simp [hW, Set.mem_pi]
    have hprod : ∏ j : Fin n, expMeasure (b (i.succAbove j)) (Ioi t)
        = ∏ j : Fin n, ENNReal.ofReal (exp (-(b (i.succAbove j) * t))) :=
      Finset.prod_congr rfl (fun j _ => expMeasure_Ioi (hb _) ht)
    rw [hbox, Measure.pi_pi, hprod,
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (exp_pos _).le)]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [lintegral_congr_ae ((expMeasure_ae_nonneg (hb i)).mono hslice),
    lintegral_exp_neg_expMeasure (hb i) hSnn, hsum]

/-- The race cells are pairwise disjoint: two clocks cannot both be strictly first. This is the
partition content, and it needs no hypothesis on the rates at all. -/
lemma raceCell_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint (raceCell (n := n))) := by
  intro i j hij
  refine Set.disjoint_left.mpr (fun ξ hi hj => ?_)
  exact absurd (hi j (Ne.symm hij)) (not_lt.mpr (hj i hij).le)

/-- ★★ **The order-free Born partition.** For a rate vector that is already a probability vector,
clock `i` wins with probability exactly `bᵢ`.

Compare `RecordLayer.volume_bornCell`, which gets the same numbers from `cdfCell` — but by stacking
intervals in index order. Here no index is privileged: `raceCell` is defined by "fires strictly
first", and relabelling the clocks just permutes the cells. -/
theorem measure_raceCell_of_sum_eq_one (b : Fin (n + 1) → ℝ) (hb : ∀ j, 0 < b j)
    (hsum : ∑ j, b j = 1) (i : Fin (n + 1)) :
    Measure.pi (fun j => expMeasure (b j)) (raceCell i) = ENNReal.ofReal (b i) := by
  rw [measure_raceCell b hb i, hsum, div_one]

end ProbabilityTheory
