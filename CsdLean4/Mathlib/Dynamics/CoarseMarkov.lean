/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Effective stochasticity: when a coarse-grained deterministic orbit is approximately Markov

**Category:** 1-Mathlib. Nothing here mentions CSD; this is elementary measure theory about
deterministic dynamics and a coarse-graining. BACKLOG #100.

A deterministic map `Φ` on a probability space, observed only through a finite coarse-graining
`C : Ω → X`, produces a *stochastic-looking* process `n ↦ C (Φ^[n] ω)`. This file says when that
process is approximately Markov, and with what error.

## The shape of the statement, and why it is not circular

The hypothesis and the conclusion are about **different objects**:

* `MicroDecoupled μ C Φ ε` is about the **microstate**: conditioning on the whole coarse history up to
  step `n` moves the law of the *microstate at step `n`* by at most `ε`, uniformly over measurable
  sets, compared with conditioning on the present coarse value alone. It is a property of the triple
  `(μ, Φ, C)`;
* the conclusions are about the **coarse process**: its one-step transition probabilities, and its
  path probabilities.

Assuming instead that *the coarse process forgets its history* would be assuming the conclusion. That
is the trap this file is written to avoid, and it is why the hypothesis quantifies over microstate
events rather than coarse ones.

## What is proved

* `condProb` — conditional probability as a real number, scale-invariant in `μ` and `0` on null
  conditions, with `condProb_nonneg` and `condProb_le_one`;
* `coarseAt`, `coarseEvent`, `historyEvent` — the coarse process, its one-step events and its
  cylinder events, the last defined by recursion so the path arguments are inductions;
* ★★ `abs_condProb_coarseEvent_sub_le` — **the one-step Markov error is at most `ε`**: the next coarse
  value's probability given the whole history differs from its probability given the present by at
  most `ε`. The coarse future event is a microstate event pulled back along `Φ^[n]`, which is exactly
  the instance of the hypothesis it needs;
* ★ `measure_historyEvent_toReal_eq_prod` — the **exact** chain rule: a path probability is the
  initial probability times the product of its own conditionals, with no hypothesis beyond
  non-degeneracy;
* ★★★ `abs_measure_historyEvent_sub_markov_le` — **the path probability factorises up to `n · ε`**:
  replacing every history-conditional by the corresponding one-step transition probability costs at
  most `n · ε` in total. This is "approximately Markovian with an explicit error";
* ★ `abs_prod_sub_prod_le_sum` — the elementary product comparison the path bound runs on;
* ★★ `condProb_coarseEvent_succ_of_autonomous` — **non-vacuity**: when the coarse variable is
  autonomous (`C ∘ Φ = T ∘ C`) the transition probabilities are `0`/`1` indicators and the error is
  `0` with no hypothesis at all, so the bounds above are attainable;
* ★★ `cex_not_microDecoupled` — **the hypothesis is load-bearing.** A four-point rotation coarse-grained
  into two cells has `P(C₂ = 1 ∣ C₁ = 0, C₀ = 0) = 1` but `P(C₂ = 1 ∣ C₁ = 0) = 1/2`, so its coarse
  process is **not** Markov and no `ε < 1/2` is available for it. Without this the theorems above
  could have been vacuous.

## Honest scope

⚠️ **The decoupling is a hypothesis, and nothing here supplies it.** No dynamics is shown to satisfy
`MicroDecoupled` with a small `ε`. That is deliberate and is forced: for the finite unitary dynamics
the CSD corpus cares about, mixing is unavailable in principle
(`not_hasCorrelationDecay_blockPop_of_unitary`), so a statement of this kind can only be conditional —
exactly as the corpus's ETH-conditional results are.

⚠️ **It is not the corpus's `HasCorrelationDecay`.** That predicate bounds the two-point correlation
of a single scalar observable; a Markov error is about conditional *laws*. Neither implies the other
and this file does not connect them.

⚠️ **The error is additive in the number of steps and is not claimed uniform in `n`.** `n · ε` is
useless once `n ≳ 1/ε`: this bounds a finite horizon, and no stationary or infinite-horizon Markov
approximation is claimed. Nothing here is an invariant-measure or convergence statement.

⚠️ **The coarse-graining is a parameter.** `C` is arbitrary measurable; no particular coarse-graining
is singled out, and in particular nothing here identifies `C` with any macroscopic or spacetime
projection. Picking `C` is a separate question that this file deliberately leaves open.

⚠️ **No randomness is derived.** The process is a deterministic orbit throughout; what is bounded is
how far its coarse marginals sit from those of a Markov chain. In particular this is **not** a
derivation of the Born rule, and it says nothing about where probabilities come from — only about how
a deterministic orbit can *look* stochastic when observed coarsely.

⚠️ **Non-degeneracy hypotheses are real.** The chain rule and the path bound need the history events
to have non-zero finite measure; on a null history the conditionals are `0` by convention and the
statements are about nothing.

## References

`Mathlib/Dynamics/CorrelationDecay.lean` (the two-point predicate this is *not*);
`specs/BACKLOG.md` #100; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {Ω X : Type*}

/-! ### The coarse process and its events -/

/-- The coarse value after `n` steps. -/
def coarseAt (C : Ω → X) (Φ : Ω → Ω) (n : ℕ) : Ω → X := fun ω => C (Φ^[n] ω)

@[simp] theorem coarseAt_zero (C : Ω → X) (Φ : Ω → Ω) : coarseAt C Φ 0 = C := rfl

/-- The event that the coarse process takes the value `x` after `n` steps. -/
def coarseEvent (C : Ω → X) (Φ : Ω → Ω) (n : ℕ) (x : X) : Set Ω := coarseAt C Φ n ⁻¹' {x}

@[simp] theorem mem_coarseEvent {C : Ω → X} {Φ : Ω → Ω} {n : ℕ} {x : X} {ω : Ω} :
    ω ∈ coarseEvent C Φ n x ↔ C (Φ^[n] ω) = x := Iff.rfl

/-- **A coarse future event is a microstate event pulled back along the flow.** The bridge that lets
a hypothesis about microstates speak about the coarse process. -/
theorem coarseEvent_succ_eq (C : Ω → X) (Φ : Ω → Ω) (n : ℕ) (x : X) :
    coarseEvent C Φ (n + 1) x = (Φ^[n]) ⁻¹' ((C ∘ Φ) ⁻¹' {x}) := by
  ext ω
  simp [coarseEvent, coarseAt, Function.iterate_succ_apply']

/-- The cylinder event that the coarse process follows the history `h` for its first `n + 1` values.
Defined by recursion, so the path arguments below are plain inductions. -/
def historyEvent (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) : ℕ → Set Ω
  | 0 => coarseEvent C Φ 0 (h 0)
  | n + 1 => historyEvent C Φ h n ∩ coarseEvent C Φ (n + 1) (h (n + 1))

@[simp] theorem historyEvent_zero (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) :
    historyEvent C Φ h 0 = coarseEvent C Φ 0 (h 0) := rfl

@[simp] theorem historyEvent_succ (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) (n : ℕ) :
    historyEvent C Φ h (n + 1)
      = historyEvent C Φ h n ∩ coarseEvent C Φ (n + 1) (h (n + 1)) := rfl

theorem historyEvent_subset_coarseEvent (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) :
    ∀ n, historyEvent C Φ h n ⊆ coarseEvent C Φ n (h n)
  | 0 => subset_rfl
  | _ + 1 => Set.inter_subset_right

theorem historyEvent_antitone (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) (n : ℕ) :
    historyEvent C Φ h (n + 1) ⊆ historyEvent C Φ h n := Set.inter_subset_left

variable [MeasurableSpace Ω]

theorem measurableSet_coarseEvent [MeasurableSpace X] [MeasurableSingletonClass X]
    {C : Ω → X} {Φ : Ω → Ω} (hC : Measurable C) (hΦ : Measurable Φ) (n : ℕ) (x : X) :
    MeasurableSet (coarseEvent C Φ n x) :=
  (hC.comp (hΦ.iterate n)) (measurableSet_singleton x)

/-! ### Conditional probability as a real number -/

/-- **The conditional probability of `B` given `H`**, as a real number: `μ (H ∩ B) / μ H`. Invariant
under rescaling `μ`, and `0` when `H` is null or infinite, so no non-degeneracy hypothesis is needed
to *write* it. -/
noncomputable def condProb (μ : Measure Ω) (H B : Set Ω) : ℝ :=
  (μ (H ∩ B)).toReal / (μ H).toReal

theorem condProb_nonneg (μ : Measure Ω) (H B : Set Ω) : 0 ≤ condProb μ H B :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem condProb_le_one (μ : Measure Ω) (H B : Set Ω) (hfin : μ H ≠ ⊤) :
    condProb μ H B ≤ 1 := by
  rcases eq_or_ne (μ H) 0 with h0 | h0
  · simp [condProb, h0]
  · refine div_le_one_of_le₀ ?_ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)

theorem condProb_mem_Icc (μ : Measure Ω) (H B : Set Ω) (hfin : μ H ≠ ⊤) :
    condProb μ H B ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨condProb_nonneg μ H B, condProb_le_one μ H B hfin⟩

/-- On a condition of non-zero finite measure, `condProb` is the ratio it looks like. -/
theorem condProb_mul_eq (μ : Measure Ω) {H : Set Ω} (B : Set Ω) (h0 : μ H ≠ 0) (hfin : μ H ≠ ⊤) :
    condProb μ H B * (μ H).toReal = (μ (H ∩ B)).toReal := by
  rw [condProb, div_mul_cancel₀]
  exact ENNReal.toReal_ne_zero.2 ⟨h0, hfin⟩

/-! ### The decoupling hypothesis -/

/-- **Microscopic decoupling at strength `ε`.** Conditioning on the whole coarse history up to step
`n`, rather than on the present coarse value alone, moves the law of the **microstate at step `n`** by
at most `ε`, uniformly over measurable sets.

⚠️ This is a property of `(μ, Φ, C)` and says nothing directly about the coarse process; assuming the
coarse process forgets its history would be assuming the conclusions below. -/
def MicroDecoupled (μ : Measure Ω) (C : Ω → X) (Φ : Ω → Ω) (ε : ℝ) : Prop :=
  ∀ (h : ℕ → X) (n : ℕ) (B : Set Ω), MeasurableSet B →
    |condProb μ (historyEvent C Φ h n) ((Φ^[n]) ⁻¹' B)
        - condProb μ (coarseEvent C Φ n (h n)) ((Φ^[n]) ⁻¹' B)| ≤ ε

/-- ★★ **The one-step Markov error.** Under microscopic decoupling, the probability that the coarse
process takes the value `z` next differs by at most `ε` between conditioning on the whole history and
conditioning on the present coarse value. The proof is the bridge `coarseEvent_succ_eq`: a coarse
future event *is* a microstate event pulled back along the flow. -/
theorem abs_condProb_coarseEvent_sub_le [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {C : Ω → X} {Φ : Ω → Ω} {ε : ℝ} (hC : Measurable C) (hΦ : Measurable Φ)
    (hdec : MicroDecoupled μ C Φ ε) (h : ℕ → X) (n : ℕ) (z : X) :
    |condProb μ (historyEvent C Φ h n) (coarseEvent C Φ (n + 1) z)
        - condProb μ (coarseEvent C Φ n (h n)) (coarseEvent C Φ (n + 1) z)| ≤ ε := by
  have hB : MeasurableSet ((C ∘ Φ) ⁻¹' {z}) := (hC.comp hΦ) (measurableSet_singleton z)
  simpa [coarseEvent_succ_eq C Φ n z] using hdec h n ((C ∘ Φ) ⁻¹' {z}) hB

/-! ### The exact chain rule -/

/-- ★ **The chain rule for a coarse path probability**, with no hypothesis beyond non-degeneracy of
the prefixes: the path probability is the initial probability times the product of the path's own
history-conditionals. -/
theorem measure_historyEvent_toReal_eq_prod (μ : Measure Ω) (C : Ω → X) (Φ : Ω → Ω) (h : ℕ → X) :
    ∀ n : ℕ, (∀ m, m ≤ n → μ (historyEvent C Φ h m) ≠ 0) →
      (∀ m, m ≤ n → μ (historyEvent C Φ h m) ≠ ⊤) →
      (μ (historyEvent C Φ h n)).toReal
        = (μ (historyEvent C Φ h 0)).toReal
          * ∏ m ∈ Finset.range n,
              condProb μ (historyEvent C Φ h m) (coarseEvent C Φ (m + 1) (h (m + 1)))
  | 0, _, _ => by simp
  | n + 1, h0, hfin => by
      have hrec := measure_historyEvent_toReal_eq_prod μ C Φ h n
        (fun m hm => h0 m (hm.trans (Nat.le_succ n))) (fun m hm => hfin m (hm.trans (Nat.le_succ n)))
      rw [Finset.prod_range_succ, ← mul_assoc, ← hrec,
        mul_comm (μ (historyEvent C Φ h n)).toReal,
        condProb_mul_eq μ _ (h0 n (Nat.le_succ n)) (hfin n (Nat.le_succ n))]
      rfl

/-! ### The path probability factorises, up to `n · ε` -/

/-- ★ **The elementary product comparison**: replacing each factor of a product of numbers in `[0,1]`
costs at most the sum of the changes. -/
theorem abs_prod_sub_prod_le_sum (a b : ℕ → ℝ) :
    ∀ n : ℕ, (∀ m, m < n → a m ∈ Set.Icc (0:ℝ) 1) → (∀ m, m < n → b m ∈ Set.Icc (0:ℝ) 1) →
      |∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m|
        ≤ ∑ m ∈ Finset.range n, |a m - b m|
  | 0, _, _ => by simp
  | n + 1, ha, hb => by
      have ih := abs_prod_sub_prod_le_sum a b n (fun m hm => ha m (hm.trans (Nat.lt_succ_self n)))
        (fun m hm => hb m (hm.trans (Nat.lt_succ_self n)))
      have hprodA : ∏ m ∈ Finset.range n, a m ∈ Set.Icc (0:ℝ) 1 :=
        ⟨Finset.prod_nonneg fun m hm => (ha m (Finset.mem_range.1 hm |>.trans
            (Nat.lt_succ_self n))).1,
          Finset.prod_le_one (fun m hm => (ha m (Finset.mem_range.1 hm |>.trans
            (Nat.lt_succ_self n))).1)
            (fun m hm => (ha m (Finset.mem_range.1 hm |>.trans (Nat.lt_succ_self n))).2)⟩
      have hbn := hb n (Nat.lt_succ_self n)
      have hkey : ∏ m ∈ Finset.range (n + 1), a m - ∏ m ∈ Finset.range (n + 1), b m
          = (∏ m ∈ Finset.range n, a m) * (a n - b n)
            + (∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m) * b n := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        ring
      rw [Finset.sum_range_succ, hkey]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have h1 : |∏ m ∈ Finset.range n, a m| * |a n - b n| ≤ |a n - b n| := by
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rw [abs_of_nonneg hprodA.1]
        exact hprodA.2
      have h2 : |∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m| * |b n|
          ≤ ∑ m ∈ Finset.range n, |a m - b m| := by
        refine le_trans (mul_le_of_le_one_right (abs_nonneg _) ?_) ih
        rw [abs_of_nonneg hbn.1]
        exact hbn.2
      linarith

/-- ★★★ **The coarse path probability factorises up to `n · ε`.** Replacing every
history-conditional by the one-step transition probability from the present coarse value changes the
path probability by at most `n · ε`. This is "the coarse process is approximately Markovian with an
explicit error", for a deterministic orbit and a hypothesis about microstates.

⚠️ Additive in `n`: useless once `n ≳ 1/ε`, and no infinite-horizon statement is implied. -/
theorem abs_measure_historyEvent_sub_markov_le [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C : Ω → X} {Φ : Ω → Ω} {ε : ℝ}
    (hC : Measurable C) (hΦ : Measurable Φ) (hdec : MicroDecoupled μ C Φ ε)
    (h : ℕ → X) (n : ℕ) (h0 : ∀ m, m ≤ n → μ (historyEvent C Φ h m) ≠ 0) :
    |(μ (historyEvent C Φ h n)).toReal
        - (μ (historyEvent C Φ h 0)).toReal
          * ∏ m ∈ Finset.range n,
              condProb μ (coarseEvent C Φ m (h m)) (coarseEvent C Φ (m + 1) (h (m + 1)))|
      ≤ n * ε := by
  have hfin : ∀ m, m ≤ n → μ (historyEvent C Φ h m) ≠ ⊤ := fun m _ => measure_ne_top μ _
  rw [measure_historyEvent_toReal_eq_prod μ C Φ h n h0 hfin, ← mul_sub, abs_mul]
  have hinit : |(μ (historyEvent C Φ h 0)).toReal| ≤ 1 := by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 : μ (historyEvent C Φ h 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) h1
  have hbody :=
    abs_prod_sub_prod_le_sum
      (fun m => condProb μ (historyEvent C Φ h m) (coarseEvent C Φ (m + 1) (h (m + 1))))
      (fun m => condProb μ (coarseEvent C Φ m (h m)) (coarseEvent C Φ (m + 1) (h (m + 1)))) n
      (fun m _ => condProb_mem_Icc μ _ _ (measure_ne_top μ _))
      (fun m _ => condProb_mem_Icc μ _ _ (measure_ne_top μ _))
  have hterms : ∑ m ∈ Finset.range n,
      |condProb μ (historyEvent C Φ h m) (coarseEvent C Φ (m + 1) (h (m + 1)))
        - condProb μ (coarseEvent C Φ m (h m)) (coarseEvent C Φ (m + 1) (h (m + 1)))|
      ≤ n * ε := by
    calc ∑ m ∈ Finset.range n,
        |condProb μ (historyEvent C Φ h m) (coarseEvent C Φ (m + 1) (h (m + 1)))
          - condProb μ (coarseEvent C Φ m (h m)) (coarseEvent C Φ (m + 1) (h (m + 1)))|
        ≤ ∑ _m ∈ Finset.range n, ε :=
          Finset.sum_le_sum fun m _ =>
            abs_condProb_coarseEvent_sub_le hC hΦ hdec h m (h (m + 1))
      _ = n * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  calc |(μ (historyEvent C Φ h 0)).toReal|
        * |∏ m ∈ Finset.range n,
              condProb μ (historyEvent C Φ h m) (coarseEvent C Φ (m + 1) (h (m + 1)))
            - ∏ m ∈ Finset.range n,
              condProb μ (coarseEvent C Φ m (h m)) (coarseEvent C Φ (m + 1) (h (m + 1)))|
      ≤ 1 * (n * ε) := by
        refine mul_le_mul hinit (le_trans hbody hterms) (abs_nonneg _) zero_le_one
    _ = n * ε := one_mul _

/-! ### Non-vacuity: an autonomous coarse variable is exactly Markov -/

/-- ★★ **With an autonomous coarse variable the error is zero, with no hypothesis.** If `C ∘ Φ`
factors through `C` then the next coarse value is determined by the present one, so every conditional
transition probability is the same `0`/`1` indicator however much history is conditioned on. The
bounds above are therefore attainable. -/
theorem condProb_coarseEvent_succ_of_autonomous [DecidableEq X] {μ : Measure Ω} {C : Ω → X}
    {Φ : Ω → Ω} {T : X → X}
    (hT : ∀ ω, C (Φ ω) = T (C ω)) {H : Set Ω} (n : ℕ) (y z : X)
    (hH : H ⊆ coarseEvent C Φ n y) (h0 : μ H ≠ 0) (hfin : μ H ≠ ⊤) :
    condProb μ H (coarseEvent C Φ (n + 1) z) = if z = T y then 1 else 0 := by
  classical
  have hmem : ∀ ω ∈ H, (ω ∈ coarseEvent C Φ (n + 1) z ↔ z = T y) := by
    intro ω hω
    have hy : C (Φ^[n] ω) = y := hH hω
    rw [mem_coarseEvent, Function.iterate_succ_apply', hT, hy]
    exact ⟨fun hzz => hzz.symm, fun hzz => hzz.symm⟩
  by_cases hz : z = T y
  · have hsub : H ∩ coarseEvent C Φ (n + 1) z = H := by
      refine Set.inter_eq_self_of_subset_left fun ω hω => ?_
      exact (hmem ω hω).2 hz
    rw [if_pos hz, condProb, hsub, div_self (ENNReal.toReal_ne_zero.2 ⟨h0, hfin⟩)]
  · have hempty : H ∩ coarseEvent C Φ (n + 1) z = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      exact hz ((hmem ω hω.1).1 hω.2)
    rw [if_neg hz, condProb, hempty, measure_empty]
    simp

/-! ### The hypothesis is load-bearing: a coarse process that is not Markov -/

/-- The four-point rotation. -/
def cexFlow : Fin 4 → Fin 4 := fun n => n + 1

/-- The two-cell coarse-graining of the four-point rotation. -/
def cexCoarse : Fin 4 → Fin 2 := fun n => if n.val < 2 then 0 else 1

theorem cexHistory_eq : historyEvent cexCoarse cexFlow (fun _ => 0) 1 = {(0 : Fin 4)} := by
  ext ω
  fin_cases ω <;> simp [historyEvent, coarseEvent, coarseAt, cexCoarse, cexFlow]

theorem cexPresent_eq :
    coarseEvent cexCoarse cexFlow 1 0 = ({3, 0} : Set (Fin 4)) := by
  ext ω
  fin_cases ω <;> simp [coarseEvent, coarseAt, cexCoarse, cexFlow]

theorem cexFuture_eq :
    coarseEvent cexCoarse cexFlow 2 1 = ({0, 1} : Set (Fin 4)) := by
  ext ω
  fin_cases ω <;> simp [coarseEvent, coarseAt, cexCoarse, cexFlow]

/-- Given the history `C₀ = 0, C₁ = 0`, the next coarse value is `1` with certainty. -/
theorem cex_condProb_history :
    condProb (Measure.count : Measure (Fin 4)) (historyEvent cexCoarse cexFlow (fun _ => 0) 1)
        (coarseEvent cexCoarse cexFlow 2 1) = 1 := by
  rw [cexHistory_eq, cexFuture_eq, condProb,
    show ({(0 : Fin 4)} ∩ ({0, 1} : Set (Fin 4))) = {(0 : Fin 4)} by
      ext ω; fin_cases ω <;> simp,
    Measure.count_singleton]
  simp

/-- Given only the present value `C₁ = 0`, the next coarse value is `1` with probability `1/2`. -/
theorem cex_condProb_present :
    condProb (Measure.count : Measure (Fin 4)) (coarseEvent cexCoarse cexFlow 1 0)
        (coarseEvent cexCoarse cexFlow 2 1) = 1 / 2 := by
  have h1 : (Measure.count : Measure (Fin 4))
      (coarseEvent cexCoarse cexFlow 1 0 ∩ coarseEvent cexCoarse cexFlow 2 1) = 1 := by
    rw [cexPresent_eq, cexFuture_eq,
      show (({3, 0} : Set (Fin 4)) ∩ ({0, 1} : Set (Fin 4))) = {(0 : Fin 4)} by
        ext ω; fin_cases ω <;> simp,
      Measure.count_singleton]
  have h2 : (Measure.count : Measure (Fin 4)) (coarseEvent cexCoarse cexFlow 1 0) = 2 := by
    rw [cexPresent_eq,
      show ({3, 0} : Set (Fin 4)) = (({3, 0} : Finset (Fin 4)) : Set (Fin 4)) by simp,
      Measure.count_apply_finset,
      show (({3, 0} : Finset (Fin 4)).card) = 2 from by decide]
    simp
  rw [condProb, h1, h2]
  simp

/-- ★★ **The hypothesis is load-bearing.** The four-point rotation coarse-grained into two cells has a
coarse process that is *not* Markov — the history changes the next step's probability from `1/2` to
`1` — so no `ε < 1/2` is available for it, and the theorems above are not vacuous. -/
theorem cex_not_microDecoupled {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ MicroDecoupled (Measure.count : Measure (Fin 4)) cexCoarse cexFlow ε := by
  intro hdec
  have h := abs_condProb_coarseEvent_sub_le (μ := (Measure.count : Measure (Fin 4)))
    (C := cexCoarse) (Φ := cexFlow) (measurable_from_top) (measurable_from_top) hdec
    (fun _ => 0) 1 1
  rw [cex_condProb_history, cex_condProb_present] at h
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at h
  linarith

end MeasureTheory

end
