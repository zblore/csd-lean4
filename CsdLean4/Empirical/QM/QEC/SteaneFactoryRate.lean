/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneVerifiedAncilla
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The ancilla factory's rejection rate and expected attempts

**Category:** 3-Local (Empirical, QM twin). BACKLOG #267 (residue of ~~#240~~).

~~#240~~'s retrying factory runs at most two attempts of ~~#234~~'s verified-ancilla preparation and
counts both in every fault window; it says nothing about how often an attempt is rejected. Here the
faults are random: each of an attempt's forty-six locations is faulty independently with
probability `p` (`Measure.pi` of Bernoulli measures). Whether an attempt is rejected is the
checker's readout, so given a fault pattern it is a Born probability, `rejProb`; a fault-free
attempt is never rejected (~~#234~~'s `facVec_none_of_not_accepts`), and no attempt is rejected with
probability above `1`.

## The rejection probability

* `rejProb` (the Born weight of the rejected checker words under a fault pattern),
  `rejProb_nonneg`, `norm_sq_eq_re_star_mul_self`, ★ `rejProb_le_one`,
  ★ `rejProb_none` — **a fault-free attempt is never rejected**.

## Random faults

* `faultLaw` (`Ber(true, false, p)` at every location, independent: `Measure.pi`), `faultySet`
  (some location faulty), `card_facLoc` (`46`), `faultySet_subset`;
  ★★ `faultLaw_faultySet_le` — **some location is faulty with probability at most `46 p`** (the
  union bound, a measure statement on `Measure.pi`);
* ★★★ `integral_rejProb_le` — **an attempt is rejected with probability at most `46 p`**.

## Repeated attempts

* ★★ `integral_prod_rejProb` — **`k` independent attempts are all rejected with probability
  `r^k`**, `r` one attempt's rejection probability (Fubini over `Measure.pi`);
  ★★ `integral_prod_rejProb_le` — at most `(46 p)^k`;
* `attemptsMean` (the expected number of attempts of a factory that stops at its first acceptance or
  after `K` attempts: the tail sum `∑_{k<K} P(the first k are rejected)`);
  ★★★ `attemptsMean_le` — **at most `1/(1 − 46 p)` for every cap `K`**, when `46 p < 1`.

## The finding

**The factory almost never retries at low noise**: one attempt is rejected with probability at most
`46 p`, the same order as its own fault budget, and the expected cost of repeat-until-success is
at most `1/(1 − 46 p)` attempts — `1 + O(p)`.

## Honest scope

⚠️ **The fault model is independent Bernoulli locations with one rate `p`**, the faults at a faulty
location being any valid channel (`FacFaults.Valid`) — the channel enters only through
`rejProb ≤ 1`, so the bound is crude: it charges every fault pattern with a full rejection.

⚠️ **`attemptsMean` is the tail-sum formula** `E[N] = ∑_{k<K} P(N > k)` with
`P(N > k) = ∫ ∏_{i<k} rejProb` (the attempts independent); the stopping process itself is not built
as a random variable on a path space.

References: `specs/BACKLOG.md` #267, #240, #234, #239; `Empirical/QM/QEC/SteaneVerifiedAncilla.lean`
(`facVec`, `facVec_none_of_not_accepts`, `sum_facVec_sq`, `FacLoc`, `FacFaults.Valid`, `retryOut`);
Mathlib `ProbabilityTheory.bernoulliMeasure`, `MeasureTheory.measurePreserving_eval`,
`MeasureTheory.integral_fintype_prod_eq_pow`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The rejection probability -/

/-- **The rejection probability of an attempt under the fault pattern `b`**: the Born weight of the
checker words the verification rejects, summed over the fault branches. -/
noncomputable def rejProb {κ : Type} [Fintype κ] (Φ : FacFaults κ) (b : FacLoc → Bool) : ℝ :=
  ∑ s : FacBranch κ, ∑ q : (Fin 7 → Fin 2) × (Fin 7 → Fin 2),
    if Accepts q.1 then 0 else ‖facVec Φ b s q‖ ^ 2

theorem rejProb_nonneg {κ : Type} [Fintype κ] (Φ : FacFaults κ) (b : FacLoc → Bool) :
    0 ≤ rejProb Φ b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _

theorem norm_sq_eq_re_star_mul_self (z : ℂ) : ‖z‖ ^ 2 = (star z * z).re := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- No attempt is rejected with probability above `1`. -/
theorem rejProb_le_one {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid)
    (b : FacLoc → Bool) : rejProb Φ b ≤ 1 := by
  have h1 : ∑ s : FacBranch κ, ∑ q : (Fin 7 → Fin 2) × (Fin 7 → Fin 2),
      ‖facVec Φ b s q‖ ^ 2 = 1 := by
    simp only [norm_sq_eq_re_star_mul_self, ← Complex.re_sum, sum_facVec_sq hΦ b, Complex.one_re]
  rw [← h1]
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun q _ => ?_
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- ★ **A fault-free attempt is never rejected.** -/
theorem rejProb_none {κ : Type} [Fintype κ] (Φ : FacFaults κ) :
    rejProb Φ (fun _ => false) = 0 := by
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun q _ => ?_
  split_ifs with h
  · rfl
  · rw [show q = (q.1, q.2) from rfl, facVec_none_of_not_accepts Φ s h, norm_zero,
      zero_pow two_ne_zero]

/-! ### Random faults -/

/-- **Independent faults of rate `p`**: each of the forty-six locations faulty with probability
`p`. -/
noncomputable def faultLaw (p : I) : Measure (FacLoc → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false p

instance (p : I) : IsProbabilityMeasure (faultLaw p) := by
  unfold faultLaw
  infer_instance

/-- The patterns with some location faulty. -/
def faultySet : Set (FacLoc → Bool) := {b | b ≠ fun _ => false}

theorem card_facLoc : Fintype.card FacLoc = 46 := by
  simp [FacLoc, EncLoc, Fintype.card_sum]

theorem faultySet_subset : faultySet ⊆ ⋃ ℓ : FacLoc, Function.eval ℓ ⁻¹' {true} := by
  intro b hb
  obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.1 hb
  exact Set.mem_iUnion.2 ⟨ℓ, by simpa using hℓ⟩

/-- ★★ **Some location is faulty with probability at most `46 p`**: the union bound on
`Measure.pi`. -/
theorem faultLaw_faultySet_le (p : I) :
    faultLaw p faultySet ≤ 46 * (toNNReal p : ℝ≥0∞) := by
  calc faultLaw p faultySet ≤ faultLaw p (⋃ ℓ : FacLoc, Function.eval ℓ ⁻¹' {true}) :=
        measure_mono faultySet_subset
    _ ≤ ∑ ℓ : FacLoc, faultLaw p (Function.eval ℓ ⁻¹' {true}) := measure_iUnion_fintype_le _ _
    _ = ∑ _ℓ : FacLoc, (toNNReal p : ℝ≥0∞) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [faultLaw, (measurePreserving_eval (fun _ : FacLoc => bernoulliMeasure true false p)
          ℓ).measure_preimage (measurableSet_singleton true).nullMeasurableSet]
        exact bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton true) rfl
          (by simp)
    _ = 46 * (toNNReal p : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, card_facLoc, nsmul_eq_mul]
        norm_num

/-- ★★★ **An attempt is rejected with probability at most `46 p`.** -/
theorem integral_rejProb_le {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (p : I) :
    ∫ b, rejProb Φ b ∂(faultLaw p) ≤ 46 * (p : ℝ) := by
  have hpt : ∀ b, rejProb Φ b ≤ faultySet.indicator (fun _ => (1 : ℝ)) b := by
    intro b
    by_cases hb : b ∈ faultySet
    · rw [Set.indicator_of_mem hb]
      exact rejProb_le_one hΦ b
    · rw [Set.indicator_of_notMem hb]
      have : b = fun _ => false := by
        simpa [faultySet] using hb
      rw [this, rejProb_none]
  calc ∫ b, rejProb Φ b ∂(faultLaw p)
      ≤ ∫ b, faultySet.indicator (fun _ => (1 : ℝ)) b ∂(faultLaw p) :=
        integral_mono (Integrable.of_finite) (Integrable.of_finite) hpt
    _ = (faultLaw p).real faultySet :=
        integral_indicator_one (Set.toFinite _).measurableSet
    _ ≤ 46 * (p : ℝ) := by
        rw [measureReal_def]
        have h := faultLaw_faultySet_le p
        have h46 : (46 * (toNNReal p : ℝ≥0∞)).toReal = 46 * (p : ℝ) := by
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
          simp
        rw [← h46]
        exact ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h

/-! ### Repeated attempts -/

/-- ★★ **`k` independent attempts are all rejected with probability `r^k`**, `r` one attempt's. -/
theorem integral_prod_rejProb {κ : Type} [Fintype κ] (Φ : FacFaults κ) (p : I) (k : ℕ) :
    ∫ B : Fin k → FacLoc → Bool, ∏ i, rejProb Φ (B i) ∂(Measure.pi fun _ => faultLaw p)
      = (∫ b, rejProb Φ b ∂(faultLaw p)) ^ k := by
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin]

/-- ★★ **At most `(46 p)^k`.** -/
theorem integral_prod_rejProb_le {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (p : I)
    (k : ℕ) :
    ∫ B : Fin k → FacLoc → Bool, ∏ i, rejProb Φ (B i) ∂(Measure.pi fun _ => faultLaw p)
      ≤ (46 * (p : ℝ)) ^ k := by
  rw [integral_prod_rejProb]
  exact pow_le_pow_left₀ (integral_nonneg fun b => rejProb_nonneg Φ b) (integral_rejProb_le hΦ p) k

/-- **The expected number of attempts** of a factory that stops at its first acceptance or after `K`
attempts: the tail sum `∑_{k<K} P(the first k attempts are all rejected)`. -/
noncomputable def attemptsMean {κ : Type} [Fintype κ] (Φ : FacFaults κ) (p : I) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∫ B : Fin k → FacLoc → Bool, ∏ i, rejProb Φ (B i) ∂(Measure.pi fun _ => faultLaw p)

/-- ★★★ **At most `1/(1 − 46 p)` attempts on average**, for every cap `K`, when `46 p < 1`. -/
theorem attemptsMean_le {κ : Type} [Fintype κ] {Φ : FacFaults κ} (hΦ : Φ.Valid) (p : I)
    (hp : 46 * (p : ℝ) < 1) (K : ℕ) : attemptsMean Φ p K ≤ 1 / (1 - 46 * (p : ℝ)) := by
  set q := 46 * (p : ℝ) with hq
  have hq0 : 0 ≤ q := by have := p.2.1; positivity
  calc attemptsMean Φ p K ≤ ∑ k ∈ Finset.range K, q ^ k :=
        Finset.sum_le_sum fun k _ => integral_prod_rejProb_le hΦ p k
    _ = (1 - q ^ K) / (1 - q) := by
        rw [geom_sum_eq (by linarith : q ≠ 1), ← neg_sub 1 (q ^ K), ← neg_sub 1 q,
          neg_div_neg_eq]
    _ ≤ 1 / (1 - q) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith [pow_nonneg hq0 K]

end Steane
end QEC
end QM
end Empirical
end CSD

end
