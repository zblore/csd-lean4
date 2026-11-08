/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.LocalStochastic

/-!
# Badness for any family of rectangles

**Category:** 1-Mathlib (CSD-free). BACKLOG #322 (split from #319).

#318 counts bad rectangles along a **chain**, neighbours sharing one recovery. A circuit with gates
on two blocks is not a chain: a `CNOT̄` rectangle shares recoveries with two predecessors and two
successors. This file drops the geometry altogether. The rectangles are taken in **decoding
order** — the order in which an ideal decoder, moved from the end of the circuit towards its start,
meets them, so rectangle `0` is the last in time — and a rectangle's window is truncated by the
windows of the bad rectangles already met. The bound `(A p²)^|T|` then holds for **every** family of
windows, with no hypothesis on how they overlap.

## The family and its badness

* `RectFamily` — **windows `W j` and malignant pairs `M j ⊆` pairs of `W j`**, nothing else;
* `malignantOff` — some pair of a family that misses a set is entirely faulty;
* `claimed` — the union of the windows of the bad rectangles among `0, …, j − 1`;
* ★ `bad` — **rectangle `j` is bad if a faulty malignant pair misses every window already claimed**;
* `trunc`, ★ `bad_eq_true_iff` — equivalently, a faulty malignant pair lies in the **truncated
  window** `W j \ claimed j`; `trunc_eq_of_disjoint` — a window that misses every earlier window is
  never truncated;
* `claimed_mono`, `W_subset_claimed` — a bad rectangle's whole window is claimed from then on.

## The bound

* ★ `disjoint_of_bad` — **witnesses of two bad rectangles are disjoint**: the later one misses the
  earlier one's window;
* ★★★ `measure_forall_bad_le` — **every set `T` of rectangles is entirely bad with probability at
  most `(A p²)^|T|`**, under local stochastic noise of parameter `p` with at most `A` malignant
  pairs per rectangle;
* ★ `measure_bad_le`, ★★ `measure_exists_bad_le` — one rectangle `A p²`; some rectangle of `T`
  `|T| A p²`;
* `reducePat`, `measurable_reducePat`, ★★★ `isLocalStochastic_map_reducePat` — **one level of
  reduction carries parameter `p` to `A p²`**, for any family.

## Every pair malignant

* `ofWindows`, ★ `ofWindows_card_M_le` — every pair of each window malignant, at most `C(w, 2)`
  pairs for windows of at most `w` locations.

## Honest scope

⚠️ **Counting only**, as in #318. That a rectangle with no faulty malignant pair in its truncated
window is correct — in particular that a rectangle whose successor is bad is correct **without its
trailing recovery**, which the truncation removes — is #323 (the exact one-level reduction).

⚠️ **Truncation is by the decoding order.** Which windows are claimed depends on the order in which
the family is indexed; for a circuit the order is a reverse time order, so a rectangle loses the
trailing recoveries it shares with bad successors. The circuit model that fixes the windows and the
order is #323 (serialised) and #332 (two blocks).

⚠️ **Not proved equal to #318's `badSeq`.** For a chain indexed in decoding order the two notions
truncate the same shared recovery, but `RectChain.badSeq` uses an explicit truncated family `M'`
and this file uses the filter of `M` by the claimed windows; no theorem here relates them.

⚠️ **Malignant pairs.** As in #318, three faults that no pair of the family covers are not counted
bad; with every pair of the window (`ofWindows`) the family is a cover.

## References

P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, §§ 5–6 (truncated extended
rectangles, local stochastic noise); `Mathlib/QuantumInfo/LocalStochastic.lean` (#318),
`Mathlib/QuantumInfo/SyndromeDecoder.lean` (#316); `specs/BACKLOG.md` #322, #319, #323, #324, #315;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuantumInfo

variable {ι : Type*}

/-- **A family of extended rectangles over the locations `ι`, in decoding order.** Rectangle `j`
has a window `W j` and a family `M j` of malignant pairs in it. Nothing is assumed about how the
windows overlap. -/
structure RectFamily (ι : Type*) where
  /-- The window of rectangle `j`. -/
  W : ℕ → Finset ι
  /-- The malignant pairs of rectangle `j`. -/
  M : ℕ → Finset (Finset ι)
  card_eq : ∀ j, ∀ s ∈ M j, s.card = 2
  subset_W : ∀ j, ∀ s ∈ M j, s ⊆ W j

namespace RectFamily

/-- **Every pair of each window malignant.** -/
def ofWindows (W : ℕ → Finset ι) : RectFamily ι where
  W := W
  M j := (W j).powersetCard 2
  card_eq _ _ hs := (Finset.mem_powersetCard.1 hs).2
  subset_W _ _ hs := (Finset.mem_powersetCard.1 hs).1

/-- ★ With every pair malignant, a window of at most `w` locations has at most `C(w, 2)` malignant
pairs. -/
theorem ofWindows_card_M_le {W : ℕ → Finset ι} {w : ℕ} (hw : ∀ j, (W j).card ≤ w) (j : ℕ) :
    ((ofWindows W).M j).card ≤ w.choose 2 := by
  simp only [ofWindows, Finset.card_powersetCard]
  exact Nat.choose_le_choose 2 (hw j)

variable [DecidableEq ι] (F : RectFamily ι)

/-- Some pair of `P` that misses `A` is entirely faulty. -/
def malignantOff (P : Finset (Finset ι)) (A : Finset ι) (ω : ι → Bool) : Bool :=
  decide (∃ s ∈ P, Disjoint s A ∧ ∀ i ∈ s, ω i = true)

/-- **The claimed locations before rectangle `j`**: the union of the windows of the bad rectangles
among `0, …, j − 1`. -/
def claimed (ω : ι → Bool) : ℕ → Finset ι
  | 0 => ∅
  | j + 1 =>
    if malignantOff (F.M j) (claimed ω j) ω then claimed ω j ∪ F.W j else claimed ω j

/-- ★ **Badness in decoding order**: rectangle `j` is bad if a faulty malignant pair misses every
window already claimed by a bad rectangle. -/
def bad (ω : ι → Bool) (j : ℕ) : Bool :=
  malignantOff (F.M j) (F.claimed ω j) ω

/-- **The truncated window**: rectangle `j`'s window without the claimed locations. -/
def trunc (ω : ι → Bool) (j : ℕ) : Finset ι :=
  F.W j \ F.claimed ω j

theorem claimed_zero (ω : ι → Bool) : F.claimed ω 0 = ∅ := rfl

theorem claimed_succ (ω : ι → Bool) (j : ℕ) :
    F.claimed ω (j + 1) = if F.bad ω j then F.claimed ω j ∪ F.W j else F.claimed ω j := rfl

theorem claimed_subset_succ (ω : ι → Bool) (j : ℕ) : F.claimed ω j ⊆ F.claimed ω (j + 1) := by
  rw [claimed_succ]
  split_ifs
  · exact Finset.subset_union_left
  · exact subset_rfl

theorem claimed_mono (ω : ι → Bool) {j j' : ℕ} (h : j ≤ j') : F.claimed ω j ⊆ F.claimed ω j' := by
  induction j', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact ih.trans (F.claimed_subset_succ ω k)

/-- A bad rectangle's whole window is claimed from then on. -/
theorem W_subset_claimed {ω : ι → Bool} {j j' : ℕ} (hj : F.bad ω j = true) (h : j < j') :
    F.W j ⊆ F.claimed ω j' := by
  refine subset_trans ?_ (F.claimed_mono ω (Nat.succ_le_of_lt h))
  rw [claimed_succ, ite_eq_left hj]
  exact Finset.subset_union_right

/-- The claimed locations lie in the windows before `j`. -/
theorem claimed_subset_biUnion (ω : ι → Bool) :
    ∀ j, F.claimed ω j ⊆ (Finset.range j).biUnion F.W
  | 0 => by simp [claimed_zero]
  | j + 1 => by
    rw [claimed_succ, Finset.range_add_one, Finset.biUnion_insert]
    have ih := claimed_subset_biUnion ω j
    split_ifs
    · exact Finset.union_subset (ih.trans Finset.subset_union_right) Finset.subset_union_left
    · exact ih.trans Finset.subset_union_right

/-- A window that misses every earlier window is never truncated. -/
theorem trunc_eq_of_disjoint {j : ℕ} (h : ∀ i < j, Disjoint (F.W j) (F.W i)) (ω : ι → Bool) :
    F.trunc ω j = F.W j := by
  refine Finset.sdiff_eq_self_of_disjoint ?_
  refine Finset.disjoint_of_subset_right (F.claimed_subset_biUnion ω j) ?_
  rw [Finset.disjoint_biUnion_right]
  exact fun i hi => h i (Finset.mem_range.1 hi)

/-- ★ **A bad rectangle has a faulty malignant pair in its truncated window**, and conversely. -/
theorem bad_eq_true_iff (ω : ι → Bool) (j : ℕ) :
    F.bad ω j = true ↔ ∃ s ∈ F.M j, s ⊆ F.trunc ω j ∧ ∀ i ∈ s, ω i = true := by
  simp only [bad, malignantOff, trunc, decide_eq_true_eq]
  refine exists_congr fun s => and_congr_right fun hs => and_congr_left fun _ => ?_
  rw [Finset.subset_sdiff]
  exact (and_iff_right (F.subset_W j s hs)).symm

/-- A bad rectangle has a faulty malignant pair missing the claimed locations. -/
theorem exists_witness {ω : ι → Bool} {j : ℕ} (hj : F.bad ω j = true) :
    ∃ s ∈ F.M j, Disjoint s (F.claimed ω j) ∧ ∀ i ∈ s, ω i = true := by
  simpa [bad, malignantOff] using hj

/-- ★ **Witnesses of two bad rectangles are disjoint**: the later one misses the earlier one's
window, which is claimed. -/
theorem disjoint_of_bad {ω : ι → Bool} {j j' : ℕ} (hj : F.bad ω j = true) (h : j < j')
    {s s' : Finset ι} (hs : s ∈ F.M j) (hs' : Disjoint s' (F.claimed ω j')) : Disjoint s s' :=
  (hs'.mono_right ((F.subset_W j s hs).trans (F.W_subset_claimed hj h))).symm

/-- ★★★ **Every set `T` of rectangles is entirely bad with probability at most `(A p²)^|T|`**,
under local stochastic noise of parameter `p` with at most `A` malignant pairs per rectangle, for
any family of windows. The witnesses are pairwise disjoint (`disjoint_of_bad`), so each choice of
one witness per rectangle is `2|T|` faulty locations, and there are at most `A^|T|` choices. -/
theorem measure_forall_bad_le {μ : Measure (ι → Bool)} {p : ℝ≥0∞} (hμ : IsLocalStochastic μ p)
    {A : ℕ} (hA : ∀ j, (F.M j).card ≤ A) (T : Finset ℕ) :
    μ {ω | ∀ j ∈ T, F.bad ω j = true} ≤ ((A : ℝ≥0∞) * p ^ 2) ^ T.card := by
  classical
  -- the choices of one witness per rectangle of `T`, pairwise disjoint
  set Ch := (Fintype.piFinset fun j : T => F.M j).filter
    fun f => ∀ a b : T, a ≠ b → Disjoint (f a) (f b) with hCh
  have hsub : {ω : ι → Bool | ∀ j ∈ T, F.bad ω j = true}
      ⊆ ⋃ f ∈ Ch, {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true} := by
    intro ω hω
    have hw : ∀ j : T, ∃ s ∈ F.M j, Disjoint s (F.claimed ω j) ∧ ∀ i ∈ s, ω i = true :=
      fun j => F.exists_witness (hω j j.2)
    choose f hf hfd hfω using hw
    have hmem : f ∈ Ch := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 hf, fun a b hab => ?_⟩
      rcases lt_or_gt_of_ne (fun h : (a : ℕ) = b => hab (Subtype.ext h)) with h | h
      · exact F.disjoint_of_bad (hω a a.2) h (hf a) (hfd b)
      · exact (F.disjoint_of_bad (hω b b.2) h (hf b) (hfd a)).symm
    refine Set.mem_biUnion (x := f) hmem ?_
    intro i hi
    obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.1 hi
    exact hfω j i hij
  have hcard : ∀ f ∈ Ch, (Finset.univ.biUnion f).card = 2 * T.card := by
    intro f hf
    obtain ⟨hf', hdisj⟩ := Finset.mem_filter.1 hf
    have hf'' := Fintype.mem_piFinset.1 hf'
    rw [Finset.card_biUnion]
    · calc ∑ u : T, (f u).card = ∑ _u : T, 2 :=
            Finset.sum_congr rfl fun j _ => F.card_eq (j : ℕ) (f j) (hf'' j)
        _ = 2 * T.card := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
    · intro j _ j' _ hne
      exact hdisj j j' hne
  have hChcard : (Ch.card : ℝ≥0∞) ≤ (A : ℝ≥0∞) ^ T.card := by
    have hnat : Ch.card ≤ A ^ T.card := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Fintype.card_piFinset]
      calc ∏ j : T, (F.M j).card ≤ ∏ _j : T, A := Finset.prod_le_prod fun j _ => hA j
        _ = A ^ T.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    exact_mod_cast hnat
  calc μ {ω | ∀ j ∈ T, F.bad ω j = true}
      ≤ μ (⋃ f ∈ Ch, {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true}) := measure_mono hsub
    _ ≤ ∑ f ∈ Ch, μ {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _f ∈ Ch, p ^ (2 * T.card) :=
        Finset.sum_le_sum fun f hf => (hμ _).trans_eq (by rw [hcard f hf])
    _ = Ch.card * (p ^ 2) ^ T.card := by rw [Finset.sum_const, nsmul_eq_mul, pow_mul]
    _ ≤ (A : ℝ≥0∞) ^ T.card * (p ^ 2) ^ T.card := by gcongr
    _ = ((A : ℝ≥0∞) * p ^ 2) ^ T.card := (mul_pow _ _ _).symm

/-- ★ **One rectangle is bad with probability at most `A p²`.** -/
theorem measure_bad_le {μ : Measure (ι → Bool)} {p : ℝ≥0∞} (hμ : IsLocalStochastic μ p)
    {A : ℕ} (hA : ∀ j, (F.M j).card ≤ A) (j : ℕ) :
    μ {ω | F.bad ω j = true} ≤ (A : ℝ≥0∞) * p ^ 2 := by
  have h := F.measure_forall_bad_le hμ hA {j}
  rw [Finset.card_singleton, pow_one] at h
  exact (measure_mono fun ω hω => by simpa using hω).trans h

/-- ★★ **Some rectangle of `T` is bad with probability at most `|T| A p²`.** -/
theorem measure_exists_bad_le {μ : Measure (ι → Bool)} {p : ℝ≥0∞} (hμ : IsLocalStochastic μ p)
    {A : ℕ} (hA : ∀ j, (F.M j).card ≤ A) (T : Finset ℕ) :
    μ {ω | ∃ j ∈ T, F.bad ω j = true} ≤ T.card * ((A : ℝ≥0∞) * p ^ 2) := by
  have hset : {ω : ι → Bool | ∃ j ∈ T, F.bad ω j = true}
      = ⋃ j ∈ T, {ω | F.bad ω j = true} := by
    ext ω
    simp
  rw [hset]
  calc μ (⋃ j ∈ T, {ω | F.bad ω j = true})
      ≤ ∑ j ∈ T, μ {ω | F.bad ω j = true} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ T, (A : ℝ≥0∞) * p ^ 2 := Finset.sum_le_sum fun j _ => F.measure_bad_le hμ hA j
    _ = T.card * ((A : ℝ≥0∞) * p ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The badness pattern of the first `N` rectangles**: the fault pattern one level down. -/
def reducePat (N : ℕ) (ω : ι → Bool) : Fin N → Bool := fun j => F.bad ω j

theorem measurable_reducePat [Fintype ι] (N : ℕ) : Measurable (F.reducePat N) :=
  fun _ _ => (Set.toFinite _).measurableSet

/-- ★★★ **One level of reduction carries local stochastic noise of parameter `p` to local stochastic
noise of parameter `A p²`** on the rectangles, for any family of windows. -/
theorem isLocalStochastic_map_reducePat [Fintype ι] {μ : Measure (ι → Bool)} {p : ℝ≥0∞}
    (hμ : IsLocalStochastic μ p) {A : ℕ} (hA : ∀ j, (F.M j).card ≤ A) (N : ℕ) :
    IsLocalStochastic (μ.map (F.reducePat N)) ((A : ℝ≥0∞) * p ^ 2) := by
  intro S
  rw [Measure.map_apply (F.measurable_reducePat N) (Set.toFinite _).measurableSet]
  have h := F.measure_forall_bad_le hμ hA (S.map Fin.valEmbedding)
  rw [Finset.card_map] at h
  refine (measure_mono fun ω hω => ?_).trans h
  intro j hj
  obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hj
  exact hω j' hj'

end RectFamily

end QuantumInfo

end
