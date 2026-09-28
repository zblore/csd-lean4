/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.CodeCapacityThreshold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The circuit-level threshold: many locations, one union bound, and the level count

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). BACKLOG #62, its
probabilistic half.

`CodeCapacityThreshold.lean` bounds the failure of **one** encoded block. A computation is a circuit
of many locations, each replaced by a gadget, and it fails when *any* of them fails. This module is
that step: the fault patterns of a circuit of `N` locations whose level-`k` gadgets have `L` fault
locations each, the union bound over the circuit, and the count of levels an accuracy demands.

* `Fintype (ConcatPat n k)` and ★ `card_concatPat` — the level-`k` gadget has `n ^ k` fault
  locations: its pattern space has `2 ^ (n ^ k)` elements. This is the **overhead** of the recursive
  simulation, in the only form this file needs;
* `circuitMeasure N L ν k` — independent faults at every location of every gadget: the product over
  the `N` circuit locations of `concatMeasure L ν k`;
* `circuitBad N L k` — the circuit fails when *some* location's level-`k` gadget is bad;
* ★★ `circuitMeasure_circuitBad_le` — **the circuit-level bound**
  `ℙ[circuit fails] ≤ N · (c p)^{2^k} / c` with `c = C(L, 2)`: the union bound over the locations on
  top of the code-capacity recursion;
* ★ `exists_level_mul_lt` and ★★★ `exists_level_circuitMeasure_lt` — **the threshold at circuit
  level**: below `p < 1/c`, for every circuit size `N` and every accuracy `ε` there is a level `k`
  at which the whole circuit fails with probability less than `ε`;
* ★ `mul_codeCapacityBound_lt_of_log_div_lt` — the quantitative form: any `k` with
  `2^k > log(c ε / N) / log(c p)` will do. The right-hand side is a single logarithm, so the level
  needed grows like `log log (N/ε)` and the overhead `L ^ k` of `card_concatPat` is polylogarithmic;
  the `Nat.ceil` arithmetic of that last sentence is left to the reader and is not claimed here.

## Honest scope

⚠️ **This is the accounting, not the fault tolerance.** What makes a gadget "bad" is an input to
this file, exactly as in `CodeCapacityThreshold.lean`: the consumer must prove that a gadget with at
most one fault does the right thing. For faulty *gates* on the Steane code that consumer is
`Empirical/QM/QEC/SteaneFaultyGate.lean`, at level one and with an ideal recovery. Faults inside the
recovery gadget itself — hence extended rectangles, and with them the Aharonov–Ben-Or simulation
theorem — are not here; `specs/BACKLOG.md` #62 records what is left.

⚠️ The locations of a circuit are indexed by `Fin N` and nothing here says what they *do*: there is
no circuit datatype, no gate set, no time ordering. The union bound needs none of that, and claiming
more would be claiming the simulation theorem.

References: D. Aharonov, M. Ben-Or, *Fault-tolerant quantum computation with constant error rate*,
SIAM J. Comput. 38 (2008), §2; P. Aliferis, D. Gottesman, J. Preskill, *Quantum accuracy threshold
for concatenated distance-3 codes*, Quantum Inf. Comput. 6 (2006); `specs/BACKLOG.md` #62;
`specs/steane-plan.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

section Overhead

/-- The pattern space of a level-`k` gadget is finite. -/
instance instFintypeConcatPat (n : ℕ) : ∀ k, Fintype (ConcatPat n k)
  | 0 => inferInstanceAs (Fintype Bool)
  | k + 1 =>
    have := instFintypeConcatPat n k
    inferInstanceAs (Fintype (Fin n → ConcatPat n k))

/-- ★ **The level-`k` gadget has `n ^ k` fault locations**: its pattern space has `2 ^ (n ^ k)`
elements, each location being faulty or not. This is the overhead of the recursive simulation. -/
theorem card_concatPat (n k : ℕ) : Fintype.card (ConcatPat n k) = 2 ^ n ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show Fintype.card (Fin n → ConcatPat n k) = _
    rw [Fintype.card_fun, ih, Fintype.card_fin, ← pow_mul, ← pow_succ]

end Overhead

section Circuit

/-- Independent faults at every location of every gadget: the product over the `N` locations of a
circuit of the level-`k` gadget noise. -/
noncomputable def circuitMeasure (N L : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] (k : ℕ) :
    Measure (Fin N → ConcatPat L k) :=
  have := (concatMeasure L ν k).2
  Measure.pi fun _ : Fin N => (concatMeasure L ν k).1

/-- The circuit fails when *some* location's gadget is bad. -/
def circuitBad (N L k : ℕ) : Set (Fin N → ConcatPat L k) :=
  {X | ∃ j, isBad L k (X j) = true}

theorem circuitBad_eq_iUnion (N L k : ℕ) :
    circuitBad N L k = ⋃ j : Fin N, {X : Fin N → ConcatPat L k | isBad L k (X j) = true} := by
  ext X
  simp only [circuitBad, mem_ofPred_eq, mem_iUnion]

/-- One location's failure has the level-`k` gadget's probability: a cylinder in one coordinate of
a product of probability measures. -/
theorem circuitMeasure_coord (N L : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] (k : ℕ)
    (j : Fin N) :
    circuitMeasure N L ν k {X : Fin N → ConcatPat L k | isBad L k (X j) = true}
      = (concatMeasure L ν k).1 (concatBad L k) := by
  have := (concatMeasure L ν k).2
  have hcyl : {X : Fin N → ConcatPat L k | isBad L k (X j) = true}
      = pi univ fun i => if i = j then concatBad L k else univ := by
    ext X
    simp only [mem_univ_pi, mem_ofPred_eq]
    constructor
    · intro h i
      split_ifs with hi
      · subst hi
        exact h
      · exact mem_univ _
    · intro h
      have hj := h j
      rwa [if_pos rfl] at hj
  rw [circuitMeasure, hcyl, Measure.pi_pi, Finset.prod_eq_single j]
  · rw [if_pos rfl]
  · intro i _ hi
    rw [if_neg hi, measure_univ]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- ★★ **The circuit-level failure bound.** A circuit of `N` locations, each simulated at level `k`
by a gadget of `L` fault locations under independent faults of rate at most `p`, has some bad gadget
with probability at most `N · (c p)^{2^k} / c`, `c = C(L, 2)`: the code-capacity recursion at each
location, and the union bound over the locations. -/
theorem circuitMeasure_circuitBad_le (N L : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ}
    (hp : 0 ≤ p) (hν : ν {b | b = true} ≤ ENNReal.ofReal p) (k : ℕ) :
    circuitMeasure N L ν k (circuitBad N L k)
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound (L.choose 2) p k) := by
  have := (concatMeasure L ν k).2
  have hloc : ∀ j : Fin N,
      circuitMeasure N L ν k {X : Fin N → ConcatPat L k | isBad L k (X j) = true}
        ≤ ENNReal.ofReal (codeCapacityBound (L.choose 2) p k) := by
    intro j
    rw [circuitMeasure_coord]
    exact concatMeasure_concatBad_le L ν hp hν k
  calc circuitMeasure N L ν k (circuitBad N L k)
      ≤ ∑ j : Fin N,
          circuitMeasure N L ν k {X : Fin N → ConcatPat L k | isBad L k (X j) = true} := by
        rw [circuitBad_eq_iUnion]
        have hb := measure_biUnion_finset_le (μ := circuitMeasure N L ν k)
          (Finset.univ : Finset (Fin N))
          fun j => {X : Fin N → ConcatPat L k | isBad L k (X j) = true}
        simpa using hb
    _ ≤ ∑ _j : Fin N, ENNReal.ofReal (codeCapacityBound (L.choose 2) p k) :=
        Finset.sum_le_sum fun j _ => hloc j
    _ = (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound (L.choose 2) p k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Circuit

section Level

/-- ★ **How many levels an accuracy needs**: any `k` whose `2^k` exceeds
`log(c ε / N) / log(c p)` brings the circuit bound below `ε`. Both logarithms are negative below
the threshold, so the ratio is positive and a *single* logarithm — the level grows like
`log log (N / ε)`. -/
theorem mul_codeCapacityBound_lt_of_log_div_lt {c p ε : ℝ} (hc : 0 < c) (hp : 0 < p)
    (h : c * p < 1) {N : ℕ} (hN : 0 < N) (hε : 0 < ε) {k : ℕ}
    (hk : Real.log (c * ε / N) / Real.log (c * p) < 2 ^ k) :
    (N : ℝ) * codeCapacityBound c p k < ε := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hx : 0 < c * p := by positivity
  have hlogx : Real.log (c * p) < 0 := Real.log_neg hx h
  have htarget : 0 < c * ε / N := by positivity
  -- the log inequality, with the sign flip of multiplying by `log (c p) < 0`
  have hmul : (2 ^ k : ℝ) * Real.log (c * p) < Real.log (c * ε / N) := by
    have := (div_lt_iff_of_neg hlogx).mp hk
    linarith
  have hpow : (c * p) ^ (2 ^ k) < c * ε / N := by
    have hlog : Real.log ((c * p) ^ (2 ^ k)) < Real.log (c * ε / N) := by
      rw [Real.log_pow]
      exact_mod_cast hmul
    exact (Real.log_lt_log_iff (by positivity) htarget).mp hlog
  rw [codeCapacityBound_eq hc]
  calc (N : ℝ) * ((c * p) ^ (2 ^ k) / c) < (N : ℝ) * ((c * ε / N) / c) :=
        mul_lt_mul_of_pos_left (by
          exact div_lt_div_of_pos_right hpow hc) hNpos
    _ = ε := by field_simp

/-- ★ **The threshold, in the form a circuit designer uses**: below `p < 1/c` every accuracy is
reachable at some level, whatever the circuit's size. -/
theorem exists_level_mul_lt {c p ε : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (h : c * p < 1) (N : ℕ)
    (hε : 0 < ε) : ∃ k, (N : ℝ) * codeCapacityBound c p k < ε := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simpa using hε⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlim := tendsto_codeCapacityBound hc hp h
  have hev : ∀ᶠ k in atTop, codeCapacityBound c p k < ε / N :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨k, ?_⟩
  calc (N : ℝ) * codeCapacityBound c p k < (N : ℝ) * (ε / N) :=
        mul_lt_mul_of_pos_left hk hNpos
    _ = ε := by field_simp

/-- ★★★ **The circuit-level threshold theorem, probabilistic form.** Below the threshold
`p < 1/C(L, 2)`, for every circuit size `N` and every accuracy `ε` there is a concatenation level at
which the probability that *any* of the circuit's `N` level-`k` gadgets is bad is less than `ε` —
with the gadgets' fault locations, and hence the overhead, counted by `card_concatPat`. -/
theorem exists_level_circuitMeasure_lt (N L : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    {p ε : ℝ} (hp : 0 ≤ p) (hν : ν {b | b = true} ≤ ENNReal.ofReal p)
    (hL : 0 < L.choose 2) (h : (L.choose 2 : ℝ) * p < 1) (hε : 0 < ε) :
    ∃ k, circuitMeasure N L ν k (circuitBad N L k) < ENNReal.ofReal ε := by
  have hc : (0 : ℝ) < L.choose 2 := Nat.cast_pos.mpr hL
  obtain ⟨k, hk⟩ := exists_level_mul_lt hc hp h N hε
  refine ⟨k, lt_of_le_of_lt (circuitMeasure_circuitBad_le N L ν hp hν k) ?_⟩
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hk

end Level

end
