/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Bell
public import CsdLean4.Mathlib.Probability.ChainedBell
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Colbeck–Renner on the singlet: no parameter-independent extension sharpens the outcome

**Category:** 3-Local (QM-validity). BACKLOG #23, the Lean form of expert row D
(`specs/colbeck-renner-note.md`).

**Glossary:** https://glossary.constraintsurfacedynamics.com/colbeck-renner/
Plain-language, CSD-role and formal statements of the Colbeck-Renner theorem, with this module as
the Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

Colbeck and Renner (2011) argue that no extension of quantum theory has improved predictive
power. An **extension** supplies extra information `ξ`, distributed by a measure `μ` that is the
same for every choice of settings, and predicts outcomes through a law `q ξ`. Their premise
bundles two assumptions, and this module keeps them apart, because which one a programme denies is
exactly the question a referee asks:

* **parameter independence** — each `q ξ` is no-signalling, so a wing's marginal depends on that
  wing's setting alone. Here: the hypotheses `hA` and `hB`;
* **measurement independence** — one `μ` serves every pair of settings. Here: `μ` is fixed before
  the settings are chosen, and `hmix` uses the same `μ` throughout.

The mathematics is the chained walk of `Mathlib/Probability/ChainedBell.lean` instantiated at the
singlet. Detector settings sit around a great circle in steps of `π − π/(2n+1)`, so every link of
the alternating walk `A 0, B 0, A 1, …, A n, B n` is nearly perfectly anticorrelated while the walk
closes on a link that is *exactly* correlated. Chained uniformity then pins Alice's marginal at the
first setting to `1/2` up to `π²/(8(2n+1))`, for **every component** of the extension and not only
for the quantum average.

* `circleSetting`, ★ `dotR_circleSetting` — settings on a great circle, with the singlet's
  correlation as the cosine of the angle between them;
* `crAngle`, `crStep`, `crNode`, `crA`, `crB` — the chained settings; ★ `dotR_crA_crB`,
  ★ `dotR_crA_succ_crB`, ★★ `dotR_crA_zero_crB_last` (the closing link is exactly correlated);
* `P_st_sum`, `marginalA_P_st`, `disagree_P_st`, `agree_P_st`, ★ `chainCost_P_st` — the singlet's
  link costs and the walk's total;
* ★★ `bound_le` — the total is at most `π²/(8(2n+1))`, by `1 − cos x ≤ x²/2`;
* ★★★ `integral_abs_marginalA_sub_half_le` — **the quantitative Colbeck–Renner statement**: every
  extension of the singlet's predictions with parameter independence has, in mean over `ξ`, its
  prediction for Alice's outcome within `π²/(8(2n+1))` of the uniform `1/2`;
* ★★★ `no_improved_predictive_power` — **the limit form**: for every accuracy `δ > 0` there are
  settings at which no such extension beats `1/2` by more than `δ`. Conditioning on `ξ` buys
  nothing, which is Colbeck–Renner for this state;
* ★ `exists_signalling_of_sharp` — the contrapositive: an extension that does sharpen the outcome
  has a component that signals.

## Where CSD stands, and what this does not say

⚠️ **CSD denies parameter independence, and that denial is a theorem elsewhere**
(`CSD.LF6.no_product_partition_realises_singlet`, `LF6/ForcedContextuality.lean`): no product
partition of any probability space reproduces the singlet correlations, so a `Σ`-level model of the
singlet cannot have each wing's response depend on its own setting alone. The hypotheses `hA`, `hB`
of the theorems below therefore fail for the programme's own model, which is why the conclusion does
not apply to it. Measurement independence, the other half of Colbeck–Renner's bundled premise, the
corpus **keeps** and says so where it is used (`LF3/OperationalNoSignalling.lean`). Nothing here
says CSD escapes a no-go by fiat; it says which premise the escape uses, and that the escape is
inherited from Bell rather than independent of it.

⚠️ **Not the general-state theorem.** Colbeck–Renner extend from maximally entangled states to all
states by an embedding argument. That step is not formalised. What is proved is their statement for
the singlet, which is where the chained-Bell machinery does its work.

⚠️ **"Improved predictive power" is formalised as sharpening the outcome marginal** of a single
measurement, in mean over the extension variable. The full conditional distribution, and the
sharper almost-everywhere form, are not claimed.

⚠️ Ideal projective measurements on the LF3 singlet kernel (`P_st`), which is where the settings and
the correlation `−a·b` come from. No detector inefficiency, no finite statistics.

References: R. Colbeck, R. Renner, *No extension of quantum theory can have improved predictive
power*, Nat. Commun. 2 (2011) 411; G. C. Ghirardi, R. Romano (2013) and J. Leegwater (2016), the
unbundling of free choice into parameter and measurement independence; S. L. Braunstein,
C. M. Caves, Ann. Phys. 202 (1990) 22; `specs/colbeck-renner-note.md`; `specs/BACKLOG.md` #23;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Real
open scoped BigOperators
open ProbabilityTheory.ChainedBell

namespace CSD
namespace Empirical
namespace QM
namespace ColbeckRenner

open LF3 CSD.Empirical.Bell

/-! ### Settings on a great circle -/

/-- A detector setting on the great circle in the `xy`-plane, at angle `φ`. -/
noncomputable def circleSetting (φ : ℝ) : DetectorSetting :=
  detector3 (Real.cos φ) (Real.sin φ) 0 (by
    have h := Real.sin_sq_add_cos_sq φ
    have h0 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    linarith)

@[simp] theorem circleSetting_vec_zero (φ : ℝ) : (circleSetting φ).vec 0 = Real.cos φ := rfl

@[simp] theorem circleSetting_vec_one (φ : ℝ) : (circleSetting φ).vec 1 = Real.sin φ := rfl

@[simp] theorem circleSetting_vec_two (φ : ℝ) : (circleSetting φ).vec 2 = 0 := rfl

/-- ★ **The singlet's correlation on the circle**: the dot product of two circle settings is the
cosine of the angle between them, so the singlet correlation `−a·b` is `−cos(φ − ψ)`. -/
theorem dotR_circleSetting (φ ψ : ℝ) :
    dotR (circleSetting φ) (circleSetting ψ) = Real.cos (φ - ψ) := by
  rw [dotR, Real.cos_sub]
  simp only [circleSetting_vec_zero, circleSetting_vec_one, circleSetting_vec_two]
  ring

/-! ### The singlet as a two-party outcome law -/

/-- The singlet law is a probability distribution for each pair of settings. -/
theorem P_st_sum (a b : DetectorSetting) : ∑ s : Sign, ∑ t : Sign, P_st a b s t = 1 := by
  rw [Sign.sum_univ (fun s => ∑ t : Sign, P_st a b s t), marginal_a_eq_half, marginal_a_eq_half]
  norm_num

/-- Alice's marginal on the singlet is uniform, whatever the settings. -/
theorem marginalA_P_st (a b : DetectorSetting) (s : Sign) : marginalA P_st a b s = 1 / 2 :=
  marginal_a_eq_half a b s

/-- Bob's marginal on the singlet is uniform, whatever the settings. -/
theorem marginalB_P_st (a b : DetectorSetting) (t : Sign) : marginalB P_st a b t = 1 / 2 :=
  marginal_b_eq_half a b t

/-- The outcome type has exactly the two signs. -/
theorem sign_univ : (Finset.univ : Finset Sign) = {Sign.plus, Sign.minus} := rfl

/-- The two signs are distinct. -/
theorem sign_ne : Sign.minus ≠ Sign.plus := by decide

/-- The probability that the two wings disagree, on the singlet. -/
theorem disagree_P_st (a b : DetectorSetting) :
    disagree P_st Sign.plus Sign.minus a b = (1 + dotR a b) / 2 := by
  rw [disagree, P_st, P_st]
  simp only [Sign.val_plus, Sign.val_minus]
  ring

/-- The probability that the two wings agree, on the singlet. -/
theorem agree_P_st (a b : DetectorSetting) :
    agree P_st Sign.plus Sign.minus a b = (1 - dotR a b) / 2 := by
  rw [agree, P_st, P_st]
  simp only [Sign.val_plus, Sign.val_minus]
  ring

/-! ### The chained settings -/

/-- The angle by which each link of the chain falls short of perfect anticorrelation. -/
noncomputable def crAngle (n : ℕ) : ℝ := π / (2 * n + 1)

/-- The angle between consecutive nodes of the chain. -/
noncomputable def crStep (n : ℕ) : ℝ := π - crAngle n

/-- The angle of the `j`-th node of the chain. -/
noncomputable def crNode (n j : ℕ) : ℝ := (j : ℝ) * crStep n

/-- Alice's `i`-th chained setting: the even nodes. -/
noncomputable def crA (n i : ℕ) : DetectorSetting := circleSetting (crNode n (2 * i))

/-- Bob's `i`-th chained setting: the odd nodes. -/
noncomputable def crB (n i : ℕ) : DetectorSetting := circleSetting (crNode n (2 * i + 1))

theorem two_mul_add_one_pos (n : ℕ) : (0 : ℝ) < 2 * n + 1 := by positivity

/-- ★ The Alice-to-Bob links of the chain are at the step angle. -/
theorem dotR_crA_crB (n i : ℕ) : dotR (crA n i) (crB n i) = Real.cos (crStep n) := by
  rw [crA, crB, dotR_circleSetting]
  have h : crNode n (2 * i) - crNode n (2 * i + 1) = -crStep n := by
    rw [crNode, crNode]
    push_cast
    ring
  rw [h, Real.cos_neg]

/-- ★ The Bob-to-Alice links of the chain are at the step angle too. -/
theorem dotR_crA_succ_crB (n i : ℕ) : dotR (crA n (i + 1)) (crB n i) = Real.cos (crStep n) := by
  rw [crA, crB, dotR_circleSetting]
  have h : crNode n (2 * (i + 1)) - crNode n (2 * i + 1) = crStep n := by
    rw [crNode, crNode]
    push_cast
    ring
  rw [h]

/-- ★★ **The chain closes up exactly.** The `2n + 1` steps of `π − π/(2n+1)` come to `2nπ`, so the
closing link between `crA n 0` and `crB n n` is perfectly correlated and costs nothing. -/
theorem dotR_crA_zero_crB_last (n : ℕ) : dotR (crA n 0) (crB n n) = 1 := by
  rw [crA, crB, dotR_circleSetting]
  have hne : (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt (two_mul_add_one_pos n)
  have h : crNode n (2 * 0) - crNode n (2 * n + 1) = -((n : ℝ) * (2 * π)) := by
    rw [crNode, crNode, crStep, crAngle]
    push_cast
    field_simp
    ring
  rw [h, Real.cos_neg, Real.cos_nat_mul_two_pi]

/-- Each link of the chain costs `(1 − cos(π/(2n+1)))/2` in disagreement. -/
theorem disagree_crStep (n : ℕ) (a b : DetectorSetting) (h : dotR a b = Real.cos (crStep n)) :
    disagree P_st Sign.plus Sign.minus a b = (1 - Real.cos (crAngle n)) / 2 := by
  rw [disagree_P_st, h, crStep, Real.cos_pi_sub]
  ring

/-- ★ **The walk's total cost on the singlet**: `2n + 1` links, each costing
`(1 − cos(π/(2n+1)))/2`. -/
theorem chainCost_P_st (n : ℕ) :
    chainCost P_st Sign.plus Sign.minus (crA n) (crB n) n
      = (2 * n + 1) * ((1 - Real.cos (crAngle n)) / 2) := by
  rw [chainCost,
    Finset.sum_congr rfl (fun i _ => disagree_crStep n _ _ (dotR_crA_crB n i)),
    Finset.sum_congr rfl (fun i _ => disagree_crStep n _ _ (dotR_crA_succ_crB n i)),
    Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range]
  ring

/-- The closing link of the chain is free: the two settings agree exactly. -/
theorem agree_crA_zero_crB_last (n : ℕ) :
    agree P_st Sign.plus Sign.minus (crA n 0) (crB n n) = 0 := by
  rw [agree_P_st, dotR_crA_zero_crB_last]
  ring

/-- ★★ **The chained bound on the singlet** is `π²/(8(2n+1))`: the walk has `2n + 1` links, each
costing `(1 − cos(π/(2n+1)))/2 ≤ π²/(4(2n+1)²)`, and the closing link is free. -/
theorem bound_le (n : ℕ) :
    (chainCost P_st Sign.plus Sign.minus (crA n) (crB n) n
        + agree P_st Sign.plus Sign.minus (crA n 0) (crB n n)) / 2
      ≤ π ^ 2 / (8 * (2 * n + 1)) := by
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := two_mul_add_one_pos n
  have hcos : 1 - crAngle n ^ 2 / 2 ≤ Real.cos (crAngle n) := Real.one_sub_sq_div_two_le_cos
  have hsq : crAngle n ^ 2 = π ^ 2 / (2 * (n : ℝ) + 1) ^ 2 := by
    rw [crAngle, div_pow]
  have hstep : 1 - Real.cos (crAngle n) ≤ π ^ 2 / (2 * (n : ℝ) + 1) ^ 2 / 2 := by
    rw [← hsq]
    linarith
  have hmul : (2 * (n : ℝ) + 1) * (1 - Real.cos (crAngle n))
      ≤ (2 * (n : ℝ) + 1) * (π ^ 2 / (2 * (n : ℝ) + 1) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hstep (le_of_lt hpos)
  have hval : (2 * (n : ℝ) + 1) * (π ^ 2 / (2 * (n : ℝ) + 1) ^ 2 / 2) / 4
      = π ^ 2 / (8 * (2 * (n : ℝ) + 1)) := by
    field_simp
    ring
  rw [chainCost_P_st, agree_crA_zero_crB_last]
  have hgoal : ((2 * (n : ℝ) + 1) * ((1 - Real.cos (crAngle n)) / 2) + 0) / 2
      = (2 * (n : ℝ) + 1) * (1 - Real.cos (crAngle n)) / 4 := by ring
  rw [hgoal, ← hval]
  linarith

/-! ### Extensions of the singlet's predictions -/

section Extension

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
variable {q : Ξ → DetectorSetting → DetectorSetting → Sign → Sign → ℝ}

/-- ★★★ **The quantitative Colbeck–Renner statement for the singlet.** Let an extension supply, for
each value `ξ` of its variable, an outcome law `q ξ` that is no-signalling (`hA`, `hB`: parameter
independence), and let the mixture over one distribution `μ` of `ξ`, the same for all settings
(measurement independence), reproduce the singlet's predictions (`hmix`). Then at the chained
settings the extension's prediction for Alice's outcome is within `π²/(8(2n+1))` of the uniform
`1/2`, in mean over `ξ`. Knowing `ξ` sharpens nothing beyond that. -/
theorem integral_abs_marginalA_sub_half_le
    (hnn : ∀ ξ a b s t, 0 ≤ q ξ a b s t)
    (hsum : ∀ ξ a b, ∑ s : Sign, ∑ t : Sign, q ξ a b s t = 1)
    (hA : ∀ ξ a b b' s, marginalA (q ξ) a b s = marginalA (q ξ) a b' s)
    (hB : ∀ ξ a a' b t, marginalB (q ξ) a b t = marginalB (q ξ) a' b t)
    (hint : ∀ a b s t, Integrable (fun ξ => q ξ a b s t) μ)
    (hmix : ∀ a b s t, ∫ ξ, q ξ a b s t ∂μ = P_st a b s t)
    (n : ℕ) :
    ∫ ξ, |marginalA (q ξ) (crA n 0) (crB n 0) Sign.plus - 1 / 2| ∂μ
      ≤ π ^ 2 / (8 * (2 * n + 1)) :=
  le_trans
    (ProbabilityTheory.ChainedBell.integral_abs_marginalA_sub_half_le sign_univ sign_ne hnn hsum
      hA hB hint hmix (crA n) (crB n) Sign.plus n)
    (bound_le n)

/-- ★★★ **No improved predictive power.** For every accuracy `δ > 0` there are settings at which no
parameter-independent extension of the singlet's predictions gets within `δ` of knowing Alice's
outcome: its prediction is `1/2` up to `δ`, in mean over the extension variable. This is
Colbeck–Renner for the singlet, with the two halves of their free-choice premise separated into the
no-signalling hypotheses and the single shared `μ`. -/
theorem no_improved_predictive_power
    (hnn : ∀ ξ a b s t, 0 ≤ q ξ a b s t)
    (hsum : ∀ ξ a b, ∑ s : Sign, ∑ t : Sign, q ξ a b s t = 1)
    (hA : ∀ ξ a b b' s, marginalA (q ξ) a b s = marginalA (q ξ) a b' s)
    (hB : ∀ ξ a a' b t, marginalB (q ξ) a b t = marginalB (q ξ) a' b t)
    (hint : ∀ a b s t, Integrable (fun ξ => q ξ a b s t) μ)
    (hmix : ∀ a b s t, ∫ ξ, q ξ a b s t ∂μ = P_st a b s t)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ a b : DetectorSetting,
      ∫ ξ, |marginalA (q ξ) a b Sign.plus - 1 / 2| ∂μ < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (π ^ 2 / (8 * δ))
  have h8 : (0 : ℝ) < 8 * δ := by positivity
  have h1 : π ^ 2 < (n : ℝ) * (8 * δ) := by
    have hcancel : π ^ 2 / (8 * δ) * (8 * δ) = π ^ 2 := div_mul_cancel₀ _ (ne_of_gt h8)
    have := mul_lt_mul_of_pos_right hn h8
    rwa [hcancel] at this
  have hden : (0 : ℝ) < 8 * (2 * (n : ℝ) + 1) := by positivity
  have h2 : π ^ 2 < δ * (8 * (2 * (n : ℝ) + 1)) := by nlinarith [h1, hδ, Nat.cast_nonneg (α := ℝ) n]
  refine ⟨crA n 0, crB n 0, lt_of_le_of_lt
    (integral_abs_marginalA_sub_half_le hnn hsum hA hB hint hmix n) ?_⟩
  have hcancel : π ^ 2 / (8 * (2 * (n : ℝ) + 1)) * (8 * (2 * (n : ℝ) + 1)) = π ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  nlinarith [h2, hden, hcancel]

/-- ★ **The contrapositive.** An extension whose components do sharpen Alice's outcome past the
chained bound must have a component that signals: parameter independence is exactly the premise the
bound consumes. -/
theorem exists_signalling_of_sharp
    (hnn : ∀ ξ a b s t, 0 ≤ q ξ a b s t)
    (hsum : ∀ ξ a b, ∑ s : Sign, ∑ t : Sign, q ξ a b s t = 1)
    (hint : ∀ a b s t, Integrable (fun ξ => q ξ a b s t) μ)
    (hmix : ∀ a b s t, ∫ ξ, q ξ a b s t ∂μ = P_st a b s t)
    (n : ℕ)
    (hsharp : π ^ 2 / (8 * (2 * n + 1))
      < ∫ ξ, |marginalA (q ξ) (crA n 0) (crB n 0) Sign.plus - 1 / 2| ∂μ) :
    ¬ ((∀ ξ a b b' s, marginalA (q ξ) a b s = marginalA (q ξ) a b' s) ∧
        ∀ ξ a a' b t, marginalB (q ξ) a b t = marginalB (q ξ) a' b t) := by
  intro h
  exact absurd (integral_abs_marginalA_sub_half_le hnn hsum h.1 h.2 hint hmix n)
    (not_le.mpr hsharp)

end Extension

end ColbeckRenner
end QM
end Empirical
end CSD

end
