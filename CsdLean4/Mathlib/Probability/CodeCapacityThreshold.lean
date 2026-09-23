/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The code-capacity threshold: independent errors, two or more, and concatenation

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #51 (row 14's
part (c)), the probabilistic core of the code-capacity threshold argument.

A distance-`3` code corrects any single error, so an encoded block fails only when **two or more**
of its `n` qubits are hit. Under independent noise of rate `p` that happens with probability at
most `C(n, 2) p²` (the union bound over pairs). Concatenating the code `k` times replaces `p` by
`c p²` at each level (`c = C(n, 2)`), giving `(c p)^{2^k} / c`, which is below `p` once
`c p ≤ 1` and tends to `0` once `c p < 1`: the **threshold** `p < 1/c`.

* ★ `measure_pi_two_or_more_le` — under the product of `n` copies of a probability measure, the
  patterns with two or more coordinates in a set of measure `≤ q` have measure `≤ C(n, 2) q²`;
* `codeCapacityBound` — the recursion `p ↦ c p²`; `codeCapacityBound_eq` — the closed form
  `(c p)^{2^k} / c`; `codeCapacityBound_le` — below `p` when `c p ≤ 1`;
  ★ `tendsto_codeCapacityBound` — **the threshold**: the bound tends to `0` when `c p < 1`;
* `ConcatPat`, `concatMeasure`, `concatBad` — the error patterns of a `k`-fold concatenated
  `n`-block code under independent noise, with the bad patterns (an error at level `0`; two or
  more bad sub-blocks at level `k + 1`), and ★★ `concatMeasure_concatBad_le` — **the code-capacity
  recursion**: the bad patterns at level `k` have probability at most `codeCapacityBound c p k`.

The quantum half — that a block whose pattern is not bad is restored by the recovery — is the
consumer's (`Empirical/QM/QEC/SteaneThreshold.lean` for the Steane code at level `1`).
References: E. Knill, R. Laflamme, W. Zurek, *Resilient quantum computation*, Science 279 (1998);
D. Aharonov, M. Ben-Or, *Fault-tolerant quantum computation with constant error rate*, SIAM J.
Comput. 38 (2008), §2 (the code-capacity recursion); `specs/BACKLOG.md` #51;
`specs/steane-plan.md`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

section TwoOrMore

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

/-- ★ **Two or more of `n` independent events of probability `≤ q` occur with probability
`≤ C(n, 2) q²`**: under the product of `n` copies of a probability measure `ν`, the patterns with
at least two coordinates satisfying `P` have measure at most `C(n, 2) · q²` when `ν {P} ≤ q`
(the union bound over the pairs of coordinates, each pair cylinder having measure `ν {P}²`). -/
theorem measure_pi_two_or_more_le (ν : Measure α) [IsProbabilityMeasure ν] (P : α → Prop)
    [DecidablePred P] {q : ℝ≥0∞} (hP : ν {a | P a} ≤ q) :
    Measure.pi (fun _ : ι => ν) {x | 2 ≤ (Finset.univ.filter fun i => P (x i)).card}
      ≤ ((Fintype.card ι).choose 2 : ℝ≥0∞) * q ^ 2 := by
  classical
  -- every pattern with two or more hits lies in the cylinder of some pair
  have hsub : {x : ι → α | 2 ≤ (Finset.univ.filter fun i => P (x i)).card}
      ⊆ ⋃ s ∈ Finset.univ.powersetCard 2, {x : ι → α | ∀ i ∈ s, P (x i)} := by
    intro x hx
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (n := 2) hx
    refine mem_iUnion₂.mpr ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hs hi)).2
  -- each pair cylinder has measure `≤ q²`
  have hpair : ∀ s ∈ Finset.univ.powersetCard 2,
      Measure.pi (fun _ : ι => ν) {x : ι → α | ∀ i ∈ s, P (x i)} ≤ q ^ 2 := by
    intro s hs
    obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hs
    have hcyl : {x : ι → α | ∀ i ∈ s, P (x i)}
        = pi univ (fun i => if i ∈ s then {a | P a} else univ) := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_univ_pi]
      constructor
      · intro h i
        split_ifs with hi
        · exact h i hi
        · exact mem_univ _
      · intro h i hi
        have := h i
        rwa [if_pos hi] at this
    rw [hcyl, Measure.pi_pi]
    have hfac : ∀ i, ν (if i ∈ s then {a | P a} else univ) = if i ∈ s then ν {a | P a} else 1 := by
      intro i
      split_ifs <;> simp
    calc ∏ i, ν (if i ∈ s then {a | P a} else univ)
        = ∏ i ∈ Finset.univ ∩ s, ν {a | P a} := by
          rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_ite_mem]
      _ = ν {a | P a} ^ 2 := by rw [Finset.univ_inter, Finset.prod_const, hcard]
      _ ≤ q ^ 2 := pow_le_pow_left' hP 2
  -- the union bound
  calc Measure.pi (fun _ : ι => ν) {x | 2 ≤ (Finset.univ.filter fun i => P (x i)).card}
      ≤ Measure.pi (fun _ : ι => ν)
          (⋃ s ∈ Finset.univ.powersetCard 2, {x : ι → α | ∀ i ∈ s, P (x i)}) :=
        measure_mono hsub
    _ ≤ ∑ s ∈ Finset.univ.powersetCard 2,
          Measure.pi (fun _ : ι => ν) {x : ι → α | ∀ i ∈ s, P (x i)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ Finset.univ.powersetCard 2, q ^ 2 := Finset.sum_le_sum hpair
    _ = ((Fintype.card ι).choose 2 : ℝ≥0∞) * q ^ 2 := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]

end TwoOrMore

section Recursion

/-- The code-capacity recursion: `p ↦ c p²`, iterated `k` times from `p`. -/
def codeCapacityBound (c p : ℝ) : ℕ → ℝ
  | 0 => p
  | k + 1 => c * codeCapacityBound c p k ^ 2

theorem codeCapacityBound_zero (c p : ℝ) : codeCapacityBound c p 0 = p := rfl

theorem codeCapacityBound_succ (c p : ℝ) (k : ℕ) :
    codeCapacityBound c p (k + 1) = c * codeCapacityBound c p k ^ 2 := rfl

theorem codeCapacityBound_nonneg {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (k : ℕ) :
    0 ≤ codeCapacityBound c p k := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [codeCapacityBound_succ]; positivity

/-- **The closed form of the recursion**: `k` levels give `(c p)^{2^k} / c`. -/
theorem codeCapacityBound_eq {c : ℝ} (hc : 0 < c) (p : ℝ) (k : ℕ) :
    codeCapacityBound c p k = (c * p) ^ (2 ^ k) / c := by
  induction k with
  | zero => rw [codeCapacityBound_zero, pow_zero, pow_one, mul_div_cancel_left₀ p hc.ne']
  | succ k ih =>
    rw [codeCapacityBound_succ, ih, show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]
    field_simp

/-- Below the threshold `c p ≤ 1`, every level is at most `p`. -/
theorem codeCapacityBound_le {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (h : c * p ≤ 1) (k : ℕ) :
    codeCapacityBound c p k ≤ p := by
  rw [codeCapacityBound_eq hc]
  calc (c * p) ^ (2 ^ k) / c ≤ (c * p) ^ 1 / c :=
        div_le_div_of_nonneg_right
          (pow_le_pow_of_le_one (by positivity) h Nat.one_le_two_pow) hc.le
    _ = p := by rw [pow_one, mul_div_cancel_left₀ p hc.ne']

/-- ★ **The threshold**: below `p < 1/c` the concatenated failure bound tends to `0`. -/
theorem tendsto_codeCapacityBound {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (h : c * p < 1) :
    Tendsto (codeCapacityBound c p) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h).comp
      (tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id)
  have h2 := h1.div_const c
  rw [zero_div] at h2
  exact h2.congr fun k => (codeCapacityBound_eq hc p k).symm

end Recursion

section Concatenation

/-- Error patterns of a `k`-fold concatenated `n`-block code: level `0` is one qubit (`true` = an
error), level `k + 1` is `n` blocks of level `k`. -/
def ConcatPat (n : ℕ) : ℕ → Type
  | 0 => Bool
  | k + 1 => Fin n → ConcatPat n k

instance instMeasurableSpaceConcatPat (n : ℕ) : ∀ k, MeasurableSpace (ConcatPat n k)
  | 0 => inferInstanceAs (MeasurableSpace Bool)
  | k + 1 => @MeasurableSpace.pi (Fin n) (fun _ => ConcatPat n k) fun _ =>
      instMeasurableSpaceConcatPat n k

/-- The independent noise on `k`-level patterns: `ν` on each qubit, the product across blocks,
bundled with its probability-measure proof (which the next product needs). -/
noncomputable def concatMeasure (n : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] :
    ∀ k, {μ : Measure (ConcatPat n k) // IsProbabilityMeasure μ}
  | 0 => ⟨ν, ‹IsProbabilityMeasure ν›⟩
  | k + 1 =>
    have := (concatMeasure n ν k).2
    ⟨Measure.pi fun _ : Fin n => (concatMeasure n ν k).1,
      inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n => (concatMeasure n ν k).1))⟩

/-- The bad patterns, as a Boolean test: an error at level `0`; two or more bad sub-blocks at
level `k + 1`. -/
def isBad (n : ℕ) : ∀ k, ConcatPat n k → Bool
  | 0 => fun b => b
  | k + 1 => fun x =>
      decide (2 ≤ (Finset.univ.filter fun i : Fin n => isBad n k (x i) = true).card)

/-- The set of bad patterns at level `k`. -/
def concatBad (n : ℕ) (k : ℕ) : Set (ConcatPat n k) := {x | isBad n k x = true}

theorem concatBad_zero (n : ℕ) : concatBad n 0 = {b | b = true} := rfl

theorem concatBad_succ (n : ℕ) (k : ℕ) :
    concatBad n (k + 1)
      = {x : Fin n → ConcatPat n k |
          2 ≤ (Finset.univ.filter fun i => isBad n k (x i) = true).card} := by
  ext x
  show isBad n (k + 1) x = true ↔
    2 ≤ (Finset.univ.filter fun i : Fin n => isBad n k (x i) = true).card
  simp only [isBad, decide_eq_true_eq]

/-- ★★ **The code-capacity recursion on error patterns.** Under independent noise with
per-qubit error probability at most `p`, the bad patterns of the `k`-fold concatenated `n`-block
code have probability at most `codeCapacityBound (C(n, 2)) p k = (C(n, 2) p)^{2^k} / C(n, 2)`. -/
theorem concatMeasure_concatBad_le (n : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}
    (hp : 0 ≤ p) (hν : ν {b | b = true} ≤ ENNReal.ofReal p) :
    ∀ k, (concatMeasure n ν k).1 (concatBad n k)
      ≤ ENNReal.ofReal (codeCapacityBound (n.choose 2) p k)
  | 0 => hν
  | k + 1 => by
    have := (concatMeasure n ν k).2
    have ih := concatMeasure_concatBad_le n ν hp hν k
    have h := measure_pi_two_or_more_le (ι := Fin n) (concatMeasure n ν k).1
      (fun a => isBad n k a = true) ih
    rw [Fintype.card_fin] at h
    have hnn : 0 ≤ codeCapacityBound (n.choose 2) p k :=
      codeCapacityBound_nonneg (Nat.cast_nonneg _) hp k
    rw [concatBad_succ, codeCapacityBound_succ, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_pow hnn, ENNReal.ofReal_natCast]
    exact h

end Concatenation

end
