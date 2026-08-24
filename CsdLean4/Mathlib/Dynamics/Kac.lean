/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Kac's formula: the mean return time is the reciprocal of the measure

**Category:** 1-Mathlib. No CSD content. Mathlib has Poincaré recurrence (`Conservative`) and
ergodicity but not this, and no return times at all.

★★ `tsum_measure_lt_returnTime` — for an **ergodic** measure-preserving map of a probability space
and any `A` with `μ A ≠ 0`,

> `∑ₙ μ {x ∈ A : n < n_A x} = 1`,

where `n_A x` is the first `n ≥ 1` with `f^[n] x ∈ A`. The left side is the expectation of `n_A`
over `A`, so conditioning on starting in `A` the **mean return time is exactly `1 / μ A`**
(`tsum_measure_lt_returnTime_div`).

## The proof avoids the tower

The textbook proof builds the Kakutani skyscraper and needs the pieces `f^k(Aₙ)` to be disjoint and
to exhaust the space — the awkward part to formalise. This is the telescoping proof instead, which
uses no images at all, only preimages, where measure preservation applies directly.

Write `notYet f A n` for the points whose iterates `0, …, n-1` all miss `A`. Everything turns on one
identity (`measure_notYet_succ`):

> `f ⁻¹' (notYet n)` splits into `A ∩ f ⁻¹' (notYet n)` and `notYet (n+1)`, and measure
> preservation turns its measure back into `μ (notYet n)`.

Telescoping gives `∑_{n<N} μ (A ∩ f ⁻¹' notYet n) + μ (notYet N) = 1`, ergodicity kills the tail
(a.e. point eventually meets `A`), and `inter_lt_returnTime` identifies each summand as
`{x ∈ A : n_A x > n}`.

## ⚠️ `returnTime` is `ℕ∞`-valued, and that is not cosmetic

With a natural-number junk value the bridge lemma is **false**: a point that never returns would
have `n_A = 0`, so `n < n_A` would fail, while it does belong to every `notYet n`. The two sides
disagree exactly on the never-returning set. That set is null here, but the identity is wanted
pointwise, so `⊤` is the honest value.

## What it is for, and what it is not

`specs/q12-fibre-mechanism-scoping.md` `Q12-d` asks for the record layer's first-passage race to
come from dynamics rather than a posited clock law. Kac is the part of that which is
**regime-correct**: it holds for *any* set of positive measure, with no rarity hypothesis — unlike
the hitting-time limit theorems (Galves–Schmitt/Abadi), which need `μ A → 0` and so cannot be
instantiated on a Born partition, whose cells have measures summing to one.

⚠️ So this supplies the **rates** — mean return time to a cell of measure `bᵢ` is `1/bᵢ`, derived
from the dynamics — and **not** the exponential **law**. The law does not follow, and the `Q12-d`
row records why.

Reference: `specs/q12-fibre-mechanism-scoping.md`; `specs/record-layer-plan.md` §3c;
`specs/future-work.md`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory

-- `notYet` and its three characterisation lemmas are pure set theory: they must NOT pull in
-- `[MeasurableSpace α]`, or the unused-section-variable linter fires and CI (`--wfail`) rejects it.
variable {α : Type*} {f : α → α} {A : Set α}

/-! ### The sets that have not met `A` yet -/

/-- **The points that have not met `A` yet**: those whose iterates at times `0, …, n-1` all miss
`A`. Defined by recursion rather than as an intersection, because the recursion is the identity the
whole proof turns on. -/
def notYet (f : α → α) (A : Set α) : ℕ → Set α
  | 0 => univ
  | n + 1 => Aᶜ ∩ f ⁻¹' notYet f A n

@[simp] lemma notYet_zero : notYet f A 0 = univ := rfl

@[simp] lemma notYet_succ (n : ℕ) : notYet f A (n + 1) = Aᶜ ∩ f ⁻¹' notYet f A n := rfl

lemma mem_notYet_iff (n : ℕ) (x : α) : x ∈ notYet f A n ↔ ∀ k < n, f^[k] x ∉ A := by
  induction n generalizing x with
  | zero => simp
  | succ j ih =>
    simp only [notYet_succ, mem_inter_iff, mem_compl_iff, mem_preimage]
    constructor
    · rintro ⟨hx0, hxs⟩ k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hx0
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Function.iterate_succ_apply]
        exact (ih (f x)).mp hxs k' (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), (ih (f x)).mpr (fun k hk => ?_)⟩
      have := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this

variable [MeasurableSpace α] {μ : Measure α}

lemma measurableSet_notYet (hf : Measurable f) (hA : MeasurableSet A) :
    ∀ n, MeasurableSet (notYet f A n)
  | 0 => MeasurableSet.univ
  | n + 1 => hA.compl.inter (hf (measurableSet_notYet hf hA n))

/-! ### The one identity, and the telescope -/

/-- ★★ **The telescoping step.** The preimage of `notYet n` splits into the points of `A` that have
not returned within `n` steps, and `notYet (n+1)`; measure preservation identifies its measure with
`μ (notYet n)`. -/
lemma measure_notYet_succ (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A)
    (hfm : Measurable f) (n : ℕ) :
    μ (notYet f A n) = μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A (n + 1)) := by
  have hmeas := measurableSet_notYet hfm hA n
  have hsplit : f ⁻¹' notYet f A n
      = (A ∩ f ⁻¹' notYet f A n) ∪ (Aᶜ ∩ f ⁻¹' notYet f A n) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  have hdisj : Disjoint (A ∩ f ⁻¹' notYet f A n) (Aᶜ ∩ f ⁻¹' notYet f A n) :=
    Set.disjoint_left.mpr (fun x hx hx' => hx'.1 hx.1)
  have hpre : μ (f ⁻¹' notYet f A n) = μ (notYet f A n) :=
    hf.measure_preimage hmeas.nullMeasurableSet
  calc μ (notYet f A n) = μ (f ⁻¹' notYet f A n) := hpre.symm
    _ = μ ((A ∩ f ⁻¹' notYet f A n) ∪ (Aᶜ ∩ f ⁻¹' notYet f A n)) := by rw [← hsplit]
    _ = μ (A ∩ f ⁻¹' notYet f A n) + μ (Aᶜ ∩ f ⁻¹' notYet f A n) :=
        measure_union hdisj (hA.compl.inter (hfm hmeas))
    _ = μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A (n + 1)) := by rw [notYet_succ]

section Probability

variable [IsProbabilityMeasure μ]

/-- The telescoped partial sums: the mass that has already returned by time `N`, plus the mass that
has not, is everything. -/
lemma sum_measure_inter_notYet (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (hfm : Measurable f) (N : ℕ) :
    ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A N) = 1 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← measure_notYet_succ hf hA hfm k]
    exact ih

/-! ### Ergodicity kills the tail -/

/-- Almost every point eventually meets `A`, so the set that never does is null. -/
lemma measure_iInter_notYet_eq_zero (hf : MeasurePreserving f μ μ)
    (herg : PreErgodic f μ) (hA : MeasurableSet A) (hApos : μ A ≠ 0) (hfm : Measurable f) :
    μ (⋂ n, notYet f A n) = 0 := by
  -- the points meeting `A` infinitely often form a strictly invariant set
  set V : Set α := ⋂ m : ℕ, ⋃ n ∈ {n : ℕ | m ≤ n}, f^[n] ⁻¹' A with hV
  have hVmeas : MeasurableSet V :=
    MeasurableSet.iInter (fun m => MeasurableSet.biUnion (to_countable _)
      (fun n _ => (hfm.iterate n) hA))
  have hVmem : ∀ x, x ∈ V ↔ ∃ᶠ n in atTop, f^[n] x ∈ A := by
    intro x
    simp only [hV, mem_iInter, mem_iUnion, mem_ofPred_eq, mem_preimage, frequently_atTop,
      exists_prop]
  have hVinv : f ⁻¹' V = V := by
    ext x
    simp only [mem_preimage, hVmem, frequently_atTop]
    constructor
    · intro h m
      obtain ⟨n, hn, hmem⟩ := h m
      exact ⟨n + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
    · intro h m
      obtain ⟨n, hn, hmem⟩ := h (m + 1)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact ⟨n', by omega, by rwa [Function.iterate_succ_apply] at hmem⟩
  -- Poincaré recurrence puts almost all of `A` inside `V`, so `V` is not null
  have hcons : Conservative f μ := hf.conservative
  have hAV : A ≤ᵐ[μ] V := by
    filter_upwards [hcons.ae_mem_imp_frequently_image_mem hA.nullMeasurableSet] with x hx hxA
    exact (hVmem x).mpr (hx hxA)
  have hVne : μ V ≠ 0 := by
    intro hzero
    have hle : μ A ≤ μ V := measure_mono_ae hAV
    rw [hzero] at hle
    exact hApos (nonpos_iff_eq_zero.mp hle)
  -- ergodicity then makes it conull
  have hVcompl : μ Vᶜ = 0 := by
    rcases herg.ae_empty_or_univ hVmeas hVinv with h | h
    · exact absurd (measure_congr h |>.trans measure_empty) hVne
    · have : μ V = 1 := by rw [measure_congr h]; exact measure_univ
      rw [prob_compl_eq_one_sub hVmeas, this, tsub_self]
  refine measure_mono_null (fun x hx => ?_) hVcompl
  simp only [mem_iInter] at hx
  simp only [mem_compl_iff, hVmem, frequently_atTop, not_forall, not_exists, not_and]
  refine ⟨0, fun n _ hmem => ?_⟩
  exact (mem_notYet_iff (n + 1) x).mp (hx (n + 1)) n (by omega) hmem

/-! ### The return time, and Kac's formula -/

open Classical in
/-- **The first return time to `A`**, valued in `ℕ∞` with `⊤` for points that never return. The `⊤`
is load-bearing — see the module docstring. -/
noncomputable def returnTime (f : α → α) (A : Set α) (x : α) : ℕ∞ :=
  if h : ∃ n : ℕ, 1 ≤ n ∧ f^[n] x ∈ A then (Nat.find h : ℕ∞) else ⊤

omit [MeasurableSpace α] in
/-- ★ **The bridge.** Starting anywhere, "the first return exceeds `n`" is exactly "the `n` steps
after the first all miss `A`". This is what lets the whole proof avoid mentioning `returnTime`. -/
lemma lt_returnTime_iff (n : ℕ) (x : α) :
    (n : ℕ∞) < returnTime f A x ↔ f x ∈ notYet f A n := by
  classical
  rw [mem_notYet_iff]
  simp only [returnTime]
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    constructor
    · intro hlt k hk
      have h2 := hlt (k + 1) (by omega)
      rw [not_and] at h2
      have h3 := h2 (by omega)
      rwa [Function.iterate_succ_apply] at h3
    · intro hall m hm
      rw [not_and]
      intro _
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact hall m' (by omega)
  · push Not at h
    constructor
    · intro _ k hk
      have h2 := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h2
    · intro _
      simp

omit [MeasurableSpace α] in
lemma inter_lt_returnTime (n : ℕ) :
    A ∩ {x | (n : ℕ∞) < returnTime f A x} = A ∩ f ⁻¹' notYet f A n := by
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, lt_returnTime_iff]

/-- ★★★ **Kac's formula.** For an ergodic measure-preserving map of a probability space and any `A`
of positive measure, the expected first return time to `A`, summed over `A`, is exactly one.

Since `∑ₙ μ {x ∈ A : n_A x > n}` is the expectation of `n_A` restricted to `A`, dividing by `μ A`
gives the mean return time **conditioned on starting in `A`** as `1 / μ A`
(`tsum_measure_lt_returnTime_div`). Small cells are returned to rarely, in exact proportion. -/
theorem tsum_measure_lt_returnTime (hf : MeasurePreserving f μ μ)
    (herg : PreErgodic f μ) (hA : MeasurableSet A) (hApos : μ A ≠ 0) (hfm : Measurable f) :
    ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) = 1 := by
  simp only [inter_lt_returnTime]
  -- the tail vanishes, so the telescoped partial sums converge to one
  have hanti : Antitone (notYet f A) := by
    intro m n hmn x hx
    rw [mem_notYet_iff] at hx ⊢
    exact fun k hk => hx k (by omega)
  have htail : Filter.Tendsto (fun N => μ (notYet f A N)) atTop (nhds 0) := by
    have hmeas : ∀ n, MeasurableSet (notYet f A n) := measurableSet_notYet hfm hA
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [measure_iInter_notYet_eq_zero hf herg hA hApos hfm] at h
    exact h
  have hpart : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n)) atTop
      (nhds (∑' n : ℕ, μ (A ∩ f ⁻¹' notYet f A n))) :=
    ENNReal.tendsto_nat_tsum _
  -- partial sums plus the tail are constantly one, so the tsum is one
  have hsum := hpart.add htail
  have heq : (fun N => ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A N))
      = fun _ : ℕ => (1 : ℝ≥0∞) :=
    funext (fun N => sum_measure_inter_notYet hf hA hfm N)
  rw [heq] at hsum
  simpa using tendsto_nhds_unique hsum tendsto_const_nhds

/-- ★★ **The mean return time is `1 / μ A`.** Kac's formula, normalised by the measure of `A` — the
form the record layer reads: a cell of Born weight `bᵢ` is returned to on average every `1/bᵢ`
steps. -/
theorem tsum_measure_lt_returnTime_div (hf : MeasurePreserving f μ μ)
    (herg : PreErgodic f μ) (hA : MeasurableSet A) (hApos : μ A ≠ 0) (hfm : Measurable f) :
    (∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x})) / μ A = 1 / μ A := by
  rw [tsum_measure_lt_returnTime hf herg hA hApos hfm]

end Probability

end MeasureTheory
