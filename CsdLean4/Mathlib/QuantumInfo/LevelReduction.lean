/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ExtendedRectangle
public import CsdLean4.Mathlib.Probability.CodeCapacityThreshold

/-!
# Level reduction, and the probabilistic join

**Category:** 1-Mathlib (CSD-free). BACKLOG #97, split out of #62 (d2) — the last of that row's
remainder.

Three things were deliberately left out of #94, #95 and #96, and they are what this file supplies:
the **recursion** (a level-`k` gadget *is* a level-`(k−1)` circuit), the **fault count**, and the
**join** of the deterministic and probabilistic halves into one statement.

The deterministic half is #62 (d1)'s ★★★ `correctedRun_eq_idealRun`; the arithmetic half is #51's
`codeCapacityBound` with ★★ `concatMeasure_concatBad_le`, the code-capacity recursion on error
patterns. Neither is re-proved here. What is new is the lifting, the union bound, and the step from
"the good event has large probability" to "the output is exactly the ideal one with large
probability".

## Level reduction

* ★★★ `isCorrectedStep_correctedRun` — **a corrected circuit is a corrected step one level up**:
  if every gadget of `c` is corrected and `idealRun c` is the gadget the next level wants, then
  `correctedRun c` is a corrected step for it. The `preserves` half comes free from
  `isCodeState_idealRun`, so no extra hypothesis is needed;
* `IsCorrectedAtLevel P k ideal impl` — the recursive simulation: at level `0` a corrected step, and
  at level `k + 1` the corrected run of a circuit whose gadgets are corrected at level `k`;
* ★★★ `isCorrectedStep_of_isCorrectedAtLevel` — **correctness at every level follows from
  correctness at level 0**, by induction on the tower. This is the recursion the threshold theorem
  runs on, and with it ★★★ `correctedRun_eq_idealRun_of_level`: a circuit of level-`k` gadgets
  computes the ideal circuit's output.

## The probabilistic join

* ★★★ `one_sub_le_measure_output_eq` — **the join, with no measurability hypotheses at all**: if the
  output is the ideal one on every pattern that makes no gadget bad, and each gadget is bad with
  probability at most `q`, then the output is ideal with probability at least `1 − N · q`.
  Subadditivity does all the work — `1 ≤ μ s + μ sᶜ` holds for arbitrary sets — so nothing has to be
  shown measurable;
* `ConcatPat`-valued circuit patterns, `circuitMeasure`, and ★ `circuitMeasure_coord`, the
  one-coordinate marginal of the product (which *does* need measurability, supplied by
  ★ `measurableSet_of_concatPat`: every set of patterns is measurable, since the pattern spaces are
  finite with measurable singletons);
* ★★★ `one_sub_le_measure_output_eq_concat` — **the row's statement**: for a circuit of `N` level-`k`
  concatenated gadgets under independent noise of rate at most `p`,

      μ {output = ideal} ≥ 1 − N · (C(n,2) · p)^(2^k) / C(n,2),

  which is `1 − N (cp)^{2^k}/c` with `c = C(n, 2)`. The deterministic input is the hypothesis that a
  pattern making no gadget bad gives the ideal output — exactly what #96's good extended rectangles
  and `isCorrectedStep_of_isCorrectedAtLevel` deliver;
* ★★ `tendsto_one_sub_codeCapacityBound` — and below threshold the bound tends to `1` as the level
  grows, from #51's `tendsto_codeCapacityBound`.

## Honest scope

⚠️ **The deterministic input is a hypothesis, and this file does not discharge it.** `hgood` says a
pattern with no bad gadget yields the ideal output. For a concrete code that is what #96's rectangles
plus the level recursion above give — but **no concrete gadget set is plugged in here**, so nothing
below is a threshold theorem *for the Steane code*. The row's statement is proved with its
deterministic premise named, not assumed away.

⚠️ **"Bad" is a pattern predicate, not a physical fault model.** `isBad` counts two-or-more bad
sub-blocks recursively; nothing here derives it from a circuit's fault locations, and the
correspondence between a gadget's faults and a `ConcatPat` is not constructed. The locality
assumption — that a gadget's failure depends only on its own block's pattern — is built into the
product measure and is a **modelling choice**, visible in the statement as the independence of
`circuitMeasure`.

⚠️ **Independent noise.** `circuitMeasure` is a product across gadgets and across blocks. Correlated
noise is outside everything below, and so is any adversarial or non-Markovian model.

⚠️ **No gate counts and no overhead.** `N` is the number of gadgets, given; nothing bounds the
circuit size needed to simulate a given computation, and no polylogarithmic-overhead claim is made or
implied. That is the part of a threshold theorem this file does not touch.

⚠️ **The constant is `C(n, 2)`, from the two-or-more union bound.** It is not claimed sharp, and no
optimised threshold value follows from it.

⚠️ **Maps, not channels, as in #62 (d1) and #96:** no positivity or trace preservation is imposed
anywhere, so "output" means the value of a map on a matrix.

## References

`Mathlib/QuantumInfo/FaultTolerantComposition.lean` (#62 (d1));
`Mathlib/QuantumInfo/ExtendedRectangle.lean` (#96);
`Mathlib/Probability/CodeCapacityThreshold.lean` (#51, `codeCapacityBound`,
`concatMeasure_concatBad_le`); `specs/BACKLOG.md` #97, #96, #95, #94, #86, #62, #51;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace QuantumInfo

/-! ### Level reduction -/

noncomputable section

variable {m : Type*} [Fintype m]

/-- ★★★ **A corrected circuit is a corrected step one level up.** The hypothesis is only that the
circuit's *ideal* run is the gadget the next level wants; `preserves` then comes free from
`isCodeState_idealRun`. This is the lifting the recursive simulation runs on. -/
theorem isCorrectedStep_correctedRun {P : Matrix m m ℂ} {c : Circuit m}
    {ideal : Matrix m m ℂ → Matrix m m ℂ} (hc : IsCorrectedCircuit P c)
    (hideal : ∀ ρ, IsCodeState P ρ → idealRun c ρ = ideal ρ) :
    IsCorrectedStep P ideal (correctedRun c) where
  recovers ρ hρ := by rw [correctedRun_eq_idealRun hc hρ, hideal ρ hρ]
  preserves ρ hρ := hideal ρ hρ ▸ isCodeState_idealRun hc hρ

/-- **The recursive simulation.** At level `0` a gadget is a corrected step; at level `k + 1` it is
the corrected run of a circuit whose gadgets are corrected at level `k`. -/
def IsCorrectedAtLevel (P : Matrix m m ℂ) :
    ℕ → (Matrix m m ℂ → Matrix m m ℂ) → (Matrix m m ℂ → Matrix m m ℂ) → Prop
  | 0, ideal, impl => IsCorrectedStep P ideal impl
  | k + 1, ideal, impl => ∃ c : Circuit m, impl = correctedRun c
      ∧ (∀ g ∈ c, IsCorrectedAtLevel P k g.1 g.2)
      ∧ ∀ ρ, IsCodeState P ρ → idealRun c ρ = ideal ρ

/-- ★★★ **Correctness at every level follows from correctness at level 0.** The induction over the
tower: each level's circuit is corrected because its gadgets are, and then the level above is a
corrected step by `isCorrectedStep_correctedRun`. -/
theorem isCorrectedStep_of_isCorrectedAtLevel {P : Matrix m m ℂ} :
    ∀ (k : ℕ) (ideal impl : Matrix m m ℂ → Matrix m m ℂ),
      IsCorrectedAtLevel P k ideal impl → IsCorrectedStep P ideal impl
  | 0, _, _, h => h
  | k + 1, ideal, impl, h => by
      obtain ⟨c, hc, hgad, hid⟩ := h
      subst hc
      exact isCorrectedStep_correctedRun
        (fun g hg => isCorrectedStep_of_isCorrectedAtLevel k g.1 g.2 (hgad g hg)) hid

/-- ★★★ **A circuit of level-`k` gadgets computes the ideal circuit's output.** -/
theorem correctedRun_eq_idealRun_of_level {P : Matrix m m ℂ} {c : Circuit m} {k : ℕ}
    (hc : ∀ g ∈ c, IsCorrectedAtLevel P k g.1 g.2) {ρ : Matrix m m ℂ} (hρ : IsCodeState P ρ) :
    correctedRun c ρ = idealRun c ρ :=
  correctedRun_eq_idealRun (fun g hg => isCorrectedStep_of_isCorrectedAtLevel k g.1 g.2 (hc g hg)) hρ

end

/-! ### The join: a large good event gives a correct output -/

/-- ★★★ **The probabilistic join.** If the output is the ideal one whenever no gadget is bad, and each
of the `N` gadgets is bad with probability at most `q`, then the output is ideal with probability at
least `1 − N · q`.

⚠️ No measurability hypotheses: subadditivity gives `1 ≤ μ s + μ sᶜ` for *arbitrary* sets, and
monotonicity does the rest. -/
theorem one_sub_le_measure_output_eq {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (Bad : Fin N → Set Ω) {out : Ω → β} {ideal : β}
    (hgood : ∀ ω, (∀ j, ω ∉ Bad j) → out ω = ideal) {q : ℝ≥0∞} (hq : ∀ j, μ (Bad j) ≤ q) :
    1 - (N : ℝ≥0∞) * q ≤ μ {ω | out ω = ideal} := by
  have hunion : μ (⋃ j, Bad j) ≤ (N : ℝ≥0∞) * q := by
    calc μ (⋃ j, Bad j) ≤ ∑ j, μ (Bad j) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin N, q := Finset.sum_le_sum fun j _ => hq j
      _ = (N : ℝ≥0∞) * q := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsub : (⋃ j, Bad j)ᶜ ⊆ {ω | out ω = ideal} := by
    intro ω hω
    exact hgood ω fun j hj => hω (Set.mem_iUnion.2 ⟨j, hj⟩)
  have hcompl : 1 - μ (⋃ j, Bad j) ≤ μ (⋃ j, Bad j)ᶜ := by
    have h1 : (1 : ℝ≥0∞) ≤ μ (⋃ j, Bad j) + μ (⋃ j, Bad j)ᶜ := by
      have := measure_union_le (μ := μ) (⋃ j, Bad j) (⋃ j, Bad j)ᶜ
      rw [Set.union_compl_self, measure_univ] at this
      exact this
    exact tsub_le_iff_right.2 (by rw [add_comm]; exact h1)
  calc 1 - (N : ℝ≥0∞) * q ≤ 1 - μ (⋃ j, Bad j) := tsub_le_tsub_left hunion 1
    _ ≤ μ (⋃ j, Bad j)ᶜ := hcompl
    _ ≤ μ {ω | out ω = ideal} := measure_mono hsub

/-! ### The concatenated instance -/

instance instFintypeConcatPat (n : ℕ) : ∀ k, Fintype (ConcatPat n k)
  | 0 => inferInstanceAs (Fintype Bool)
  | k + 1 =>
    have := instFintypeConcatPat n k
    inferInstanceAs (Fintype (Fin n → ConcatPat n k))

instance instMeasurableSingletonClassConcatPat (n : ℕ) :
    ∀ k, MeasurableSingletonClass (ConcatPat n k)
  | 0 => inferInstanceAs (MeasurableSingletonClass Bool)
  | k + 1 => by
      have inst := instMeasurableSingletonClassConcatPat n k
      refine ⟨fun f => ?_⟩
      show MeasurableSet ({f} : Set (Fin n → ConcatPat n k))
      have h : MeasurableSet (Set.univ.pi fun i => ({f i} : Set (ConcatPat n k))) :=
        MeasurableSet.univ_pi fun i => measurableSet_singleton (f i)
      have heq : (Set.univ.pi fun i => ({f i} : Set (ConcatPat n k)))
          = ({f} : Set (Fin n → ConcatPat n k)) := by
        apply Set.eq_of_subset_of_subset
        · intro g hg
          exact Set.mem_singleton_iff.2 (funext fun i => hg i (Set.mem_univ i))
        · intro g hg
          have hgf : g = f := Set.mem_singleton_iff.1 hg
          intro i _
          rw [hgf]
          exact rfl
      rwa [heq] at h

/-- ★ **Every set of patterns is measurable**: the pattern spaces are finite and have measurable
singletons. -/
theorem measurableSet_of_concatPat (n k : ℕ) (S : Set (ConcatPat n k)) : MeasurableSet S :=
  (Set.toFinite S).measurableSet

/-- The fault patterns of a circuit of `N` gadgets, each a level-`k` concatenated block. -/
abbrev CircuitPat (N n k : ℕ) : Type := Fin N → ConcatPat n k

/-- Independent noise across the gadgets of the circuit. ⚠️ Independence is a modelling choice, and it
is visible here. -/
noncomputable def circuitMeasure (N n : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] (k : ℕ) :
    Measure (CircuitPat N n k) :=
  Measure.pi fun _ : Fin N => (concatMeasure n ν k).1

instance instIsProbabilityMeasureCircuitMeasure (N n : ℕ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (k : ℕ) : IsProbabilityMeasure (circuitMeasure N n ν k) := by
  have := (concatMeasure n ν k).2
  unfold circuitMeasure
  infer_instance

/-- ★ **The one-coordinate marginal of the circuit's noise** is one gadget's noise. -/
theorem circuitMeasure_coord (N n : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] (k : ℕ)
    (j : Fin N) (S : Set (ConcatPat n k)) :
    circuitMeasure N n ν k {ω | ω j ∈ S} = (concatMeasure n ν k).1 S := by
  classical
  have := (concatMeasure n ν k).2
  have hset : {ω : CircuitPat N n k | ω j ∈ S}
      = Set.univ.pi fun i => if i = j then S else Set.univ := by
    ext ω
    simp only [Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi; simpa using h
      · simp [hi]
    · intro h
      simpa using h j
  rw [circuitMeasure, hset, Measure.pi_pi, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- ★★★ **The threshold statement.** For a circuit of `N` gadgets, each a level-`k` concatenated
block under independent noise of rate at most `p`, the output is **exactly** the ideal one with
probability at least

    1 − N · (C(n,2) · p)^(2^k) / C(n,2),

which is the row's `1 − N (cp)^{2^k}/c`. The deterministic premise `hgood` — a pattern with no bad
gadget gives the ideal output — is what #96's good extended rectangles and
`isCorrectedStep_of_isCorrectedAtLevel` supply for a concrete gadget set; it is **named here, not
assumed away**. -/
theorem one_sub_le_measure_output_eq_concat {β : Type*} {N n k : ℕ} (ν : Measure Bool)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 ≤ p) (hν : ν {b | b = true} ≤ ENNReal.ofReal p)
    {out : CircuitPat N n k → β} {ideal : β}
    (hgood : ∀ ω, (∀ j, isBad n k (ω j) = false) → out ω = ideal) :
    1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound (n.choose 2) p k)
      ≤ circuitMeasure N n ν k {ω | out ω = ideal} := by
  refine one_sub_le_measure_output_eq (circuitMeasure N n ν k)
    (fun j => {ω | ω j ∈ concatBad n k}) (fun ω hω => hgood ω fun j => ?_) (fun j => ?_)
  · have hj := hω j
    simp only [concatBad] at hj
    simpa using hj
  · rw [circuitMeasure_coord N n ν k j (concatBad n k)]
    exact concatMeasure_concatBad_le n ν hp hν k

/-- ★★ **Below threshold the bound tends to `1`.** With `C(n,2) · p < 1`, raising the concatenation
level drives the failure probability to `0`, so the output is ideal with probability tending to `1`.
From #51's `tendsto_codeCapacityBound`; the limit is of the *bound*, not of the measure. -/
theorem tendsto_one_sub_codeCapacityBound {n N : ℕ} {p : ℝ} (hc : 0 < (n.choose 2 : ℝ))
    (hp : 0 ≤ p) (h : (n.choose 2 : ℝ) * p < 1) :
    Filter.Tendsto
      (fun k : ℕ => 1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound (n.choose 2) p k))
      Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto
      (fun k : ℕ => (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound (n.choose 2) p k))
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_codeCapacityBound hc hp h
    have h2 : Filter.Tendsto
        (fun k : ℕ => ENNReal.ofReal (codeCapacityBound (n.choose 2) p k))
        Filter.atTop (nhds 0) := by simpa using ENNReal.tendsto_ofReal h1
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr (by simp))
  have := ENNReal.Tendsto.sub (a := (1 : ℝ≥0∞)) (b := 0) tendsto_const_nhds h0 (by simp)
  simpa using this

end QuantumInfo

end
