/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ReedMuller15Errors
public import CsdLean4.Mathlib.Probability.CodeCapacityThreshold
public import Mathlib.Probability.ConditionalProbability

/-!
# The 15-to-1 distillation bound and its recursion

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #78, part (d) of `R-004`
(`specs/magic-plan.md`, "The split"); closes `R-004`.

The fifteen injections (BACKLOG #66–#67) leave independent `Z`-errors of rate `p` on the encoded
magic state: the error pattern `e ∈ 𝔽₂¹⁵` is distributed by the product measure `patternMeasure ν`
of fifteen copies of a Bernoulli `ν` with `ν {1} = p`. The `X`-checks accept exactly the undetected
patterns (BACKLOG #77), and an accepted pattern is wrong exactly when its weight is odd.

* `patternMeasure_singleton` — `μ {e} = p^{|e|} (1 − p)^{15 − |e|}`;
* `acceptSet`, `wrongSet`; ★ `measure_acceptSet_ge` — **acceptance `≥ (1 − p)^{15}`** (the
  zero pattern is accepted); ★ `measure_wrongSet_le` — **accepted-and-wrong `≤ 35 p³ + 2¹¹ p⁵`**
  (an accepted wrong pattern has odd weight `≥ 3`: exactly `35` of weight `3`, at most `2¹¹` of
  weight `≥ 5`, the counts of BACKLOG #75 transported through the definitional bridge);
* ★★ `distillation_error_le` — **the conditional error of one round**:
  `P(output wrong | accept) ≤ (35 p³ + 2¹¹ p⁵) / (1 − p)^{15}` — Bravyi–Kitaev's `35 p³` at leading
  order; ★ `distillation_error_le_ninety` — for `p ≤ 1/20` the bound is at most `90 p³`;
* `distillIter p k` — the recursion `p ↦ 90 p³`; ★ `distillIter_le`, ★★ `tendsto_distillIter` —
  **below `p ≤ 1/20` the iterated error rate tends to `0`** (as `p (90 p²)^k`, a crude but valid
  envelope of the triple-exponential decay).

## Honest scope

⚠️ The recursion iterates the one-round bound under the standard modelling assumption that the
output errors of one round are again independent `Z`-errors of the bounded rate; the threshold
`p ≤ 1/20` is a convenient sufficient condition, not Bravyi–Kitaev's exact fixed point `≈ 0.141`.
The explicit decoding circuit is BACKLOG #79.

References: S. Bravyi, A. Kitaev, PRA 71 (2005) 022316 §IV; `specs/magic-plan.md`;
`specs/BACKLOG.md` #78; `specs/future-work.md`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantumInfo

namespace ReedMuller15

/-! ### Transport of the counts from `ReedMuller15.lean` -/

theorem wt_eq_weight (e : Fin 15 → Fin 2) : wt e = _root_.ReedMuller15.weight e := by
  unfold wt _root_.ReedMuller15.weight _root_.ReedMuller15.support
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  show e j = 1 ↔ e j ≠ 0
  generalize e j = v
  revert v
  decide

theorem wt_ne_one_of_undetected {e : Fin 15 → Fin 2} (he : syndromeF e = 0) : wt e ≠ 1 := by
  intro h1
  exact _root_.ReedMuller15.syndrome_ne_zero_of_weight_one e (by rw [← wt_eq_weight]; exact h1)
    (by rw [← syndromeF_eq]; exact he)

theorem wt_ne_two_of_undetected {e : Fin 15 → Fin 2} (he : syndromeF e = 0) : wt e ≠ 2 := by
  intro h2
  exact _root_.ReedMuller15.syndrome_ne_zero_of_weight_two e (by rw [← wt_eq_weight]; exact h2)
    (by rw [← syndromeF_eq]; exact he)

/-- Exactly `35` undetected patterns of weight `3` (BACKLOG #75, on `Fin 2` labels). -/
theorem card_undetected_wt_three :
    (univ.filter fun e : Fin 15 → Fin 2 => syndromeF e = 0 ∧ wt e = 3).card = 35 := by
  have h := _root_.ReedMuller15.card_undetected_weight_three
  rw [← Fintype.card_subtype] at h ⊢
  rw [← h]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun e => by
    rw [syndromeF_eq, wt_eq_weight]
    exact Iff.rfl)

/-- `2¹¹` undetected patterns (BACKLOG #75, on `Fin 2` labels). -/
theorem card_undetectedF :
    (univ.filter fun e : Fin 15 → Fin 2 => syndromeF e = 0).card = 2 ^ 11 := by
  have h := _root_.ReedMuller15.card_undetected
  rw [← Fintype.card_subtype] at h ⊢
  rw [← h]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun e => by
    rw [syndromeF_eq]
    exact Iff.rfl)

/-! ### The pattern measure -/

/-- Fifteen independent copies of the single-qubit error law `ν`. -/
noncomputable abbrev patternMeasure (ν : Measure (Fin 2)) : Measure (Fin 15 → Fin 2) :=
  Measure.pi fun _ => ν

variable (ν : Measure (Fin 2)) [IsProbabilityMeasure ν] {p : ℝ}

theorem measure_zero_eq (hp0 : 0 ≤ p) (hν : ν {1} = ENNReal.ofReal p) :
    ν {0} = ENNReal.ofReal (1 - p) := by
  have h : ({0} : Set (Fin 2)) = {1}ᶜ := by
    ext v
    fin_cases v <;> simp
  rw [h, prob_compl_eq_one_sub (measurableSet_singleton 1), hν, ENNReal.ofReal_sub 1 hp0,
    ENNReal.ofReal_one]

/-- `μ {e} = p^{|e|} (1 − p)^{15 − |e|}`. -/
theorem patternMeasure_singleton (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν : ν {1} = ENNReal.ofReal p)
    (e : Fin 15 → Fin 2) :
    patternMeasure ν {e} = ENNReal.ofReal (p ^ wt e * (1 - p) ^ (15 - wt e)) := by
  rw [← Set.univ_pi_singleton e, Measure.pi_pi]
  have hν0 := measure_zero_eq ν hp0 hν
  have h : ∀ i, ν {e i} = if e i = 1 then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
    intro i
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (e i) with h0 | h0 <;> simp [h0, hν, hν0]
  simp_rw [h]
  rw [prod_ite, prod_const, prod_const, ← compl_filter, card_compl, Fintype.card_fin,
    ENNReal.ofReal_mul (pow_nonneg hp0 _), ENNReal.ofReal_pow hp0, ENNReal.ofReal_pow (by linarith)]
  rfl

/-- The accepted patterns: zero syndrome. -/
def acceptSet : Set (Fin 15 → Fin 2) := {e | syndromeF e = 0}

/-- The accepted and wrong patterns: zero syndrome and odd parity. -/
def wrongSet : Set (Fin 15 → Fin 2) := {e | syndromeF e = 0 ∧ parity e = 1}

theorem acceptSet_eq : acceptSet = ↑(univ.filter fun e : Fin 15 → Fin 2 => syndromeF e = 0) := by
  ext e
  simp [acceptSet]

theorem measurableSet_acceptSet : MeasurableSet acceptSet := by
  rw [acceptSet_eq]
  exact Finset.measurableSet _

theorem wt_zero : wt (0 : Fin 15 → Fin 2) = 0 := by
  decide

/-- ★ **Acceptance probability at least `(1 − p)^{15}`**: the zero pattern is accepted. -/
theorem measure_acceptSet_ge (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν : ν {1} = ENNReal.ofReal p) :
    ENNReal.ofReal ((1 - p) ^ 15) ≤ patternMeasure ν acceptSet := by
  have h0 : (0 : Fin 15 → Fin 2) ∈ acceptSet := by
    show syndromeF 0 = 0
    funext i
    rw [syndromeF, bdot_zero_left, Pi.zero_apply]
  calc ENNReal.ofReal ((1 - p) ^ 15) = patternMeasure ν {0} := by
        rw [patternMeasure_singleton ν hp0 hp1 hν, wt_zero, pow_zero, one_mul, Nat.sub_zero]
    _ ≤ patternMeasure ν acceptSet := measure_mono (Set.singleton_subset_iff.mpr h0)

theorem singleton_le_pow_wt (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν : ν {1} = ENNReal.ofReal p)
    (e : Fin 15 → Fin 2) : patternMeasure ν {e} ≤ ENNReal.ofReal (p ^ wt e) := by
  rw [patternMeasure_singleton ν hp0 hp1 hν]
  refine ENNReal.ofReal_le_ofReal ?_
  calc p ^ wt e * (1 - p) ^ (15 - wt e) ≤ p ^ wt e * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith)) (pow_nonneg hp0 _)
    _ = p ^ wt e := mul_one _

/-- ★ **Accepted-and-wrong probability at most `35 p³ + 2¹¹ p⁵`.** -/
theorem measure_wrongSet_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν : ν {1} = ENNReal.ofReal p) :
    patternMeasure ν wrongSet ≤ ENNReal.ofReal (35 * p ^ 3 + 2 ^ 11 * p ^ 5) := by
  set W3 := univ.filter fun e : Fin 15 → Fin 2 => syndromeF e = 0 ∧ wt e = 3 with hW3
  set W5 := univ.filter fun e : Fin 15 → Fin 2 => syndromeF e = 0 ∧ 5 ≤ wt e with hW5
  have hsub : wrongSet ⊆ ↑W3 ∪ ↑W5 := by
    intro e he
    obtain ⟨hs, hpar⟩ := he
    have hodd : Odd (wt e) := (parity_eq_one_iff_odd e).mp hpar
    have h1 := wt_ne_one_of_undetected hs
    have h2 := wt_ne_two_of_undetected hs
    rcases Nat.lt_or_ge (wt e) 5 with hlt | hge
    · left
      obtain ⟨k, hk⟩ := hodd
      simp only [hW3, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨hs, by omega⟩
    · right
      simp only [hW5, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨hs, hge⟩
  have hb3 : patternMeasure ν ↑W3 ≤ ENNReal.ofReal (35 * p ^ 3) := by
    rw [← sum_measure_singleton]
    calc ∑ e ∈ W3, patternMeasure ν {e} ≤ ∑ e ∈ W3, ENNReal.ofReal (p ^ 3) := by
          refine sum_le_sum fun e he => ?_
          have h3 : wt e = 3 := (mem_filter.mp he).2.2
          rw [← h3]
          exact singleton_le_pow_wt ν hp0 hp1 hν e
      _ = ENNReal.ofReal (35 * p ^ 3) := by
          rw [sum_const, card_undetected_wt_three, nsmul_eq_mul,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 35)]
          norm_num
  have hb5 : patternMeasure ν ↑W5 ≤ ENNReal.ofReal (2 ^ 11 * p ^ 5) := by
    rw [← sum_measure_singleton]
    calc ∑ e ∈ W5, patternMeasure ν {e} ≤ ∑ e ∈ W5, ENNReal.ofReal (p ^ 5) := by
          refine sum_le_sum fun e he => ?_
          have h5 : 5 ≤ wt e := (mem_filter.mp he).2.2
          exact (singleton_le_pow_wt ν hp0 hp1 hν e).trans
            (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hp0 hp1 h5))
      _ = W5.card • ENNReal.ofReal (p ^ 5) := sum_const _
      _ ≤ (2 ^ 11 : ℕ) • ENNReal.ofReal (p ^ 5) := by
          refine nsmul_le_nsmul_left zero_le ?_
          rw [← card_undetectedF]
          refine card_le_card fun e he => ?_
          rw [mem_filter] at he ⊢
          exact ⟨he.1, he.2.1⟩
      _ = ENNReal.ofReal (2 ^ 11 * p ^ 5) := by
          rw [nsmul_eq_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2 ^ 11)]
          norm_num
  calc patternMeasure ν wrongSet ≤ patternMeasure ν (↑W3 ∪ ↑W5) := measure_mono hsub
    _ ≤ patternMeasure ν ↑W3 + patternMeasure ν ↑W5 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (35 * p ^ 3) + ENNReal.ofReal (2 ^ 11 * p ^ 5) := add_le_add hb3 hb5
    _ = ENNReal.ofReal (35 * p ^ 3 + 2 ^ 11 * p ^ 5) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-! ### The conditional error of one round -/

theorem acceptSet_inter : acceptSet ∩ {e : Fin 15 → Fin 2 | parity e = 1} = wrongSet := rfl

/-- ★★ **The 15-to-1 distillation bound**: conditional on acceptance, the output is wrong with
probability at most `(35 p³ + 2¹¹ p⁵) / (1 − p)^{15}` — Bravyi–Kitaev's `35 p³` at leading order. -/
theorem distillation_error_le (hp0 : 0 ≤ p) (hp1 : p < 1) (hν : ν {1} = ENNReal.ofReal p) :
    (patternMeasure ν)[|acceptSet] {e | parity e = 1}
      ≤ ENNReal.ofReal ((35 * p ^ 3 + 2 ^ 11 * p ^ 5) / (1 - p) ^ 15) := by
  rw [cond_apply measurableSet_acceptSet, acceptSet_inter,
    ENNReal.ofReal_div_of_pos (pow_pos (by linarith) 15), ENNReal.div_eq_inv_mul]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr (measure_acceptSet_ge ν hp0 hp1.le hν))
    (measure_wrongSet_le ν hp0 hp1.le hν)

/-- For `p ≤ 1/20` the one-round bound is at most `90 p³`. -/
theorem bound_le_ninety (hp0 : 0 ≤ p) (hp : p ≤ 1 / 20) :
    (35 * p ^ 3 + 2 ^ 11 * p ^ 5) / (1 - p) ^ 15 ≤ 90 * p ^ 3 := by
  have h19 : (19 / 20 : ℝ) ^ 15 ≤ (1 - p) ^ 15 := pow_le_pow_left₀ (by norm_num) (by linarith) 15
  have hpos : 0 < (1 - p) ^ 15 := pow_pos (by linarith) 15
  have hnum : (0.46 : ℝ) ≤ (19 / 20 : ℝ) ^ 15 := by norm_num
  have hp2 : p ^ 2 ≤ (1 / 20) ^ 2 := pow_le_pow_left₀ hp0 hp 2
  have h3 : 0 ≤ p ^ 3 := pow_nonneg hp0 3
  rw [div_le_iff₀ hpos]
  have h5 : 2 ^ 11 * p ^ 5 ≤ 2 ^ 11 * ((1 / 20) ^ 2 * p ^ 3) := by
    rw [show p ^ 5 = p ^ 2 * p ^ 3 by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp2 h3) (by norm_num)
  have h6 : 90 * p ^ 3 * 0.46 ≤ 90 * p ^ 3 * (1 - p) ^ 15 :=
    mul_le_mul_of_nonneg_left (hnum.trans h19) (by positivity)
  nlinarith [h5, h6, h3]

/-- ★ **One round for `p ≤ 1/20`**: the conditional error is at most `90 p³`. -/
theorem distillation_error_le_ninety (hp0 : 0 ≤ p) (hp : p ≤ 1 / 20)
    (hν : ν {1} = ENNReal.ofReal p) :
    (patternMeasure ν)[|acceptSet] {e | parity e = 1} ≤ ENNReal.ofReal (90 * p ^ 3) :=
  (distillation_error_le ν hp0 (by linarith) hν).trans
    (ENNReal.ofReal_le_ofReal (bound_le_ninety hp0 hp))

/-! ### The recursion -/

/-- The iterated error rate: `p₀ = p`, `p_{k+1} = 90 p_k³`. -/
def distillIter (p : ℝ) : ℕ → ℝ
  | 0 => p
  | k + 1 => 90 * distillIter p k ^ 3

theorem distillIter_zero (p : ℝ) : distillIter p 0 = p := rfl

theorem distillIter_succ (p : ℝ) (k : ℕ) : distillIter p (k + 1) = 90 * distillIter p k ^ 3 := rfl

/-- ★ For `p ≤ 1/20`: `0 ≤ p_k ≤ p (90 p²)^k` and `p_k ≤ p`. -/
theorem distillIter_le (hp0 : 0 ≤ p) (hp : p ≤ 1 / 20) (k : ℕ) :
    0 ≤ distillIter p k ∧ distillIter p k ≤ p ∧ distillIter p k ≤ p * (90 * p ^ 2) ^ k := by
  induction k with
  | zero => exact ⟨hp0, le_of_eq (distillIter_zero p), by simp [distillIter_zero]⟩
  | succ k ih =>
    obtain ⟨h0, hle, hgeo⟩ := ih
    have hsq : distillIter p k ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ h0 hle 2
    have h90 : 90 * p ^ 2 ≤ 1 := by nlinarith [pow_le_pow_left₀ hp0 hp 2]
    refine ⟨by rw [distillIter_succ]; positivity, ?_, ?_⟩
    · calc distillIter p (k + 1) = 90 * distillIter p k ^ 2 * distillIter p k := by
            rw [distillIter_succ]; ring
        _ ≤ 90 * p ^ 2 * distillIter p k := by gcongr
        _ ≤ 1 * distillIter p k := by gcongr
        _ ≤ p := by rw [one_mul]; exact hle
    · calc distillIter p (k + 1) = 90 * distillIter p k ^ 2 * distillIter p k := by
            rw [distillIter_succ]; ring
        _ ≤ 90 * p ^ 2 * (p * (90 * p ^ 2) ^ k) := by gcongr
        _ = p * (90 * p ^ 2) ^ (k + 1) := by ring

/-- ★★ **The distillation threshold, in the form the chain claims**: below `p ≤ 1/20` the iterated
error rate tends to `0`. -/
theorem tendsto_distillIter (hp0 : 0 ≤ p) (hp : p ≤ 1 / 20) :
    Tendsto (distillIter p) atTop (𝓝 0) := by
  have h90 : 90 * p ^ 2 < 1 := by nlinarith [pow_le_pow_left₀ hp0 hp 2]
  have hlim : Tendsto (fun k : ℕ => p * (90 * p ^ 2) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h90).const_mul p
    rwa [mul_zero] at this
  exact squeeze_zero (fun k => (distillIter_le hp0 hp k).1) (fun k => (distillIter_le hp0 hp k).2.2)
    hlim

end ReedMuller15

end QuantumInfo

end
