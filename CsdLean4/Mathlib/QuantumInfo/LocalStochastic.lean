/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import CsdLean4.Mathlib.Probability.CodeCapacityThreshold

/-!
# Local stochastic noise and its level reduction

**Category:** 1-Mathlib (CSD-free). BACKLOG #318 (split from #314).

The threshold recursion `p_k ≤ A p_{k−1}²` needs a noise model that survives one level of the
reduction. Independent faults do not: once the faulty rectangles of a level are the faulty locations
of the next, two neighbouring rectangles share a recovery, so their badness is correlated. The model
that survives is Aliferis–Gottesman–Preskill's **local stochastic noise** — every set `S` of
locations is entirely faulty with probability at most `p^|S|` — and independent faults are an
instance of it.

## Local stochastic noise

* `IsLocalStochastic μ p`, `IsLocalStochastic.mono`;
* ★★ `isLocalStochastic_pi` — **independent faults of rate `ν{true}` are local stochastic** with
  that parameter (each set's event is a box);
* ★ `IsLocalStochastic.measure_exists_le` — the union bound: some location of `T` faulty has
  probability at most `|T| p`.

## One level of reduction

* `RectChain` — **a chain of extended rectangles over the locations**: rectangle `j` has a full
  window `W j` and a truncated window `W' j` (without the recovery it shares with rectangle
  `j − 1`), with its malignant pairs `M j` and truncated malignant pairs `M' j ⊆ M j`; windows two
  or more apart are disjoint, and a truncated window is disjoint from the window before it;
* `malignant`, ★ `badSeq` — **Aliferis–Gottesman–Preskill's sequential badness**: rectangle `j` is
  bad if a malignant pair of its window is faulty, of its truncated window if rectangle `j − 1` is
  already bad — the shared recovery is counted once;
* `exists_witness` — a bad rectangle has a faulty pair from `M' j` when its predecessor is bad;
* ★★★ `measure_forall_badSeq_le` — **every set `T` of rectangles is entirely bad with probability at
  most `(A p²)^|T|`**: the witnesses of a set of bad rectangles can be chosen pairwise disjoint, so
  each choice is a set of `2|T|` faulty locations, and there are at most `A^|T|` choices;
* `reducePat`, `measurable_reducePat`, ★★★ `isLocalStochastic_map_reducePat` — **one level of
  reduction carries local stochastic noise of parameter `p` to local stochastic noise of parameter
  `A p²`** on the rectangles.

## The recursion and the threshold

* `lsBound`, `lsBound_succ`, ★★ `lsBound_induction` — **`k` reductions give parameter
  `lsBound A p k`**, with `lsBound A p (k + 1) = A · lsBound A p k²`;
* ★★ `ofReal_codeCapacityBound` — `lsBound` is #51's `codeCapacityBound` `(A p)^{2^k} / A`;
* ★★★ `tendsto_lsBound` — **below the threshold `p < 1/A` the parameter tends to `0`**.

## Chains of steps

* `RectChain.ofSteps` — **the overlapping chain of #233**: step `j`'s locations `L j`, its recovery
  `R j ⊆ L j`, rectangle `j`'s window `L j ∪ R (j − 1)`, its truncated window `L j`, every pair of
  each malignant; ★ `RectChain.ofSteps_card_M_le` — at most `C(w, 2)` pairs for windows of at most
  `w` locations.

## Honest scope

⚠️ **Counting only.** Nothing here says that a rectangle with no faulty malignant pair is correct,
or that a bad one is a faulty location one level down; those are #312, #313 and the decoder algebra
(#316, #317). This file proves that the **badness pattern** is local stochastic with the squared
parameter, which is what the recursion consumes.

⚠️ **A chain.** The rectangles form a sequence, neighbours sharing one recovery, as in #233's
machine. Rectangles on several blocks at once (`CNOT̄`) share recoveries with two predecessors; that
geometry is #319's circuit model.

⚠️ **Malignant pairs.** A rectangle is bad when a pair of its window is faulty; three faults that
no pair of the family covers are not counted bad, so the family must be a cover in the sense the
correctness theorem needs. With every pair of the window the family is `C(w, 2)` pairs
(`RectChain.ofSteps`).

## References

P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, §§ 5–6 (local stochastic
noise, the truncation of overlapping extended rectangles);
`Mathlib/QuantumInfo/OverlappingRectangles.lean` (#233), `Mathlib/QuantumInfo/LevelReduction.lean`
(#97), `Mathlib/Probability/CodeCapacityThreshold.lean` (#51); `specs/BACKLOG.md` #314,
#316–#319, #315; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumInfo

variable {ι : Type*}

/-! ### Local stochastic noise -/

/-- **Local stochastic noise of parameter `p`**: every set `S` of locations is entirely faulty with
probability at most `p^|S|`. -/
def IsLocalStochastic (μ : Measure (ι → Bool)) (p : ℝ≥0∞) : Prop :=
  ∀ S : Finset ι, μ {ω | ∀ i ∈ S, ω i = true} ≤ p ^ S.card

theorem IsLocalStochastic.mono {μ : Measure (ι → Bool)} {p q : ℝ≥0∞} (h : IsLocalStochastic μ p)
    (hpq : p ≤ q) : IsLocalStochastic μ q :=
  fun S => (h S).trans (pow_le_pow_left' hpq _)

/-- ★★ **Independent faults are local stochastic**: under the product of one law `ν` on each
location, a set `S` is entirely faulty with probability exactly `ν{true}^|S|`. -/
theorem isLocalStochastic_pi [Fintype ι] [DecidableEq ι] (ν : Measure Bool)
    [IsProbabilityMeasure ν] :
    IsLocalStochastic (Measure.pi fun _ : ι => ν) (ν {b | b = true}) := by
  intro S
  have hset : {ω : ι → Bool | ∀ i ∈ S, ω i = true}
      = Set.univ.pi fun i => if i ∈ S then {b | b = true} else Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    refine ⟨fun h i => ?_, fun h i hi => by simpa [hi] using h i⟩
    by_cases hi : i ∈ S
    · simpa [hi] using h i hi
    · simp [hi]
  rw [hset, Measure.pi_pi]
  simp only [apply_ite (ν ·), measure_univ]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- ★ **The union bound**: some location of `T` is faulty with probability at most `|T| p`. -/
theorem IsLocalStochastic.measure_exists_le {μ : Measure (ι → Bool)} {p : ℝ≥0∞}
    (h : IsLocalStochastic μ p) (T : Finset ι) :
    μ {ω | ∃ i ∈ T, ω i = true} ≤ T.card * p := by
  have hset : {ω : ι → Bool | ∃ i ∈ T, ω i = true}
      = ⋃ i ∈ T, {ω | ∀ j ∈ ({i} : Finset ι), ω j = true} := by
    ext ω
    simp
  rw [hset]
  calc μ (⋃ i ∈ T, {ω | ∀ j ∈ ({i} : Finset ι), ω j = true})
      ≤ ∑ i ∈ T, μ {ω | ∀ j ∈ ({i} : Finset ι), ω j = true} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ T, p := Finset.sum_le_sum fun i _ => by simpa using h {i}
    _ = T.card * p := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### One level of reduction -/

/-- **A chain of extended rectangles over the locations `ι`.** Rectangle `j` has a window `W j` and
a truncated window `W' j` (the window without the recovery it shares with rectangle `j − 1`), and a
family of malignant pairs in each, the truncated family inside the full one. Windows two or more
apart are disjoint, and a truncated window is disjoint from the window before it. -/
structure RectChain (ι : Type*) where
  /-- The window of rectangle `j`. -/
  W : ℕ → Finset ι
  /-- The truncated window of rectangle `j`. -/
  W' : ℕ → Finset ι
  /-- The malignant pairs of rectangle `j`. -/
  M : ℕ → Finset (Finset ι)
  /-- The malignant pairs of the truncated rectangle `j`. -/
  M' : ℕ → Finset (Finset ι)
  card_eq : ∀ j, ∀ s ∈ M j, s.card = 2
  subset_W : ∀ j, ∀ s ∈ M j, s ⊆ W j
  M'_subset : ∀ j, M' j ⊆ M j
  subset_W' : ∀ j, ∀ s ∈ M' j, s ⊆ W' j
  disjoint_far : ∀ j j', j + 2 ≤ j' → Disjoint (W j) (W j')
  disjoint_next : ∀ j, Disjoint (W j) (W' (j + 1))

namespace RectChain

variable (C : RectChain ι)

/-- Some pair of the family is entirely faulty. -/
def malignant (F : Finset (Finset ι)) (ω : ι → Bool) : Bool :=
  decide (∃ s ∈ F, ∀ i ∈ s, ω i = true)

/-- ★ **Sequential badness**: rectangle `j` is bad if a malignant pair of its window is faulty — of
its truncated window if rectangle `j − 1` is already bad, so that the recovery the two share is
counted once. -/
def badSeq (ω : ι → Bool) : ℕ → Bool
  | 0 => malignant (C.M 0) ω
  | j + 1 => if badSeq ω j then malignant (C.M' (j + 1)) ω else malignant (C.M (j + 1)) ω

/-- The family a witness of rectangle `j`'s badness is drawn from, given the set `T` of rectangles
already known bad: the truncated family if `j − 1 ∈ T`. -/
def witFam (T : Finset ℕ) (j : ℕ) : Finset (Finset ι) :=
  if j ≠ 0 ∧ j - 1 ∈ T then C.M' j else C.M j

theorem witFam_subset (T : Finset ℕ) (j : ℕ) : C.witFam T j ⊆ C.M j := by
  unfold witFam
  split_ifs
  · exact C.M'_subset j
  · exact subset_rfl

/-- **A bad rectangle has a faulty witness pair**, from the truncated family when its predecessor is
bad. -/
theorem exists_witness {ω : ι → Bool} {T : Finset ℕ} (hT : ∀ j ∈ T, C.badSeq ω j = true) {j : ℕ}
    (hj : j ∈ T) : ∃ s ∈ C.witFam T j, ∀ i ∈ s, ω i = true := by
  have hb := hT j hj
  unfold witFam
  cases j with
  | zero =>
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    simpa [badSeq, malignant] using hb
  | succ j =>
    simp only [badSeq] at hb
    by_cases hprev : C.badSeq ω j = true
    · rw [ite_eq_left hprev] at hb
      have : ∃ s ∈ C.M' (j + 1), ∀ i ∈ s, ω i = true := by simpa [malignant] using hb
      split_ifs
      · exact this
      · obtain ⟨s, hs, h⟩ := this
        exact ⟨s, C.M'_subset _ hs, h⟩
    · rw [ite_eq_right hprev] at hb
      have hnot : ¬ (j + 1 ≠ 0 ∧ j + 1 - 1 ∈ T) := by
        rintro ⟨-, h⟩
        exact hprev (hT j (by simpa using h))
      rw [ite_eq_right hnot]
      simpa [malignant] using hb

/-- Witnesses drawn from `witFam` for distinct rectangles of `T` are disjoint. -/
theorem disjoint_of_witFam {T : Finset ℕ} {j j' : ℕ} (hj : j ∈ T) (hjj' : j < j')
    {s s' : Finset ι} (hs : s ∈ C.witFam T j) (hs' : s' ∈ C.witFam T j') : Disjoint s s' := by
  have hsW : s ⊆ C.W j := C.subset_W j s (C.witFam_subset T j hs)
  rcases Nat.lt_or_ge (j + 1) j' with h | h
  · exact (C.disjoint_far j j' (by omega)).mono hsW (C.subset_W j' s' (C.witFam_subset T j' hs'))
  · have hj' : j' = j + 1 := by omega
    subst hj'
    have hs'M : s' ∈ C.M' (j + 1) := by
      unfold witFam at hs'
      rwa [ite_eq_left (⟨by omega, by simpa using hj⟩ : j + 1 ≠ 0 ∧ j + 1 - 1 ∈ T)] at hs'
    exact (C.disjoint_next j).mono hsW (C.subset_W' _ s' hs'M)

/-- ★★★ **Every set `T` of rectangles is entirely bad with probability at most `(A p²)^|T|`**, under
local stochastic noise of parameter `p` with at most `A` malignant pairs per rectangle. The
witnesses can be chosen disjoint (`disjoint_of_witFam`), so each choice is `2|T|` faulty locations,
and there are at most `A^|T|` choices. -/
theorem measure_forall_badSeq_le [DecidableEq ι] {μ : Measure (ι → Bool)} {p : ℝ≥0∞}
    (hμ : IsLocalStochastic μ p) {A : ℕ} (hA : ∀ j, (C.M j).card ≤ A) (T : Finset ℕ) :
    μ {ω | ∀ j ∈ T, C.badSeq ω j = true} ≤ ((A : ℝ≥0∞) * p ^ 2) ^ T.card := by
  classical
  -- the choices of one witness per rectangle of `T`
  set Ch := Fintype.piFinset fun j : T => C.witFam T j with hCh
  have hsub : {ω : ι → Bool | ∀ j ∈ T, C.badSeq ω j = true}
      ⊆ ⋃ f ∈ Ch, {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true} := by
    intro ω hω
    have hw : ∀ j : T, ∃ s ∈ C.witFam T j, ∀ i ∈ s, ω i = true :=
      fun j => C.exists_witness hω j.2
    choose f hf hfω using hw
    refine Set.mem_biUnion (x := f) (Fintype.mem_piFinset.2 hf) ?_
    intro i hi
    obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.1 hi
    exact hfω j i hij
  have hcard : ∀ f ∈ Ch, (Finset.univ.biUnion f).card = 2 * T.card := by
    intro f hf
    have hf' := Fintype.mem_piFinset.1 hf
    rw [Finset.card_biUnion]
    · calc ∑ u : T, (f u).card = ∑ _u : T, 2 :=
            Finset.sum_congr rfl fun j _ =>
              C.card_eq (j : ℕ) (f j) (C.witFam_subset T (j : ℕ) (hf' j))
        _ = 2 * T.card := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
    · intro j _ j' _ hne
      rcases lt_or_gt_of_ne (fun h : (j : ℕ) = j' => hne (Subtype.ext h)) with h | h
      · exact C.disjoint_of_witFam j.2 h (hf' j) (hf' j')
      · exact (C.disjoint_of_witFam j'.2 h (hf' j') (hf' j)).symm
  have hChcard : (Ch.card : ℝ≥0∞) ≤ (A : ℝ≥0∞) ^ T.card := by
    rw [hCh, Fintype.card_piFinset]
    have hnat : ∏ j : T, (C.witFam T j).card ≤ A ^ T.card := by
      calc ∏ j : T, (C.witFam T j).card ≤ ∏ _j : T, A :=
            Finset.prod_le_prod fun j _ =>
              (Finset.card_le_card (C.witFam_subset T j)).trans (hA j)
        _ = A ^ T.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    exact_mod_cast hnat
  calc μ {ω | ∀ j ∈ T, C.badSeq ω j = true}
      ≤ μ (⋃ f ∈ Ch, {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true}) := measure_mono hsub
    _ ≤ ∑ f ∈ Ch, μ {ω | ∀ i ∈ Finset.univ.biUnion f, ω i = true} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _f ∈ Ch, p ^ (2 * T.card) :=
        Finset.sum_le_sum fun f hf => (hμ _).trans_eq (by rw [hcard f hf])
    _ = Ch.card * (p ^ 2) ^ T.card := by rw [Finset.sum_const, nsmul_eq_mul, pow_mul]
    _ ≤ (A : ℝ≥0∞) ^ T.card * (p ^ 2) ^ T.card := by gcongr
    _ = ((A : ℝ≥0∞) * p ^ 2) ^ T.card := (mul_pow _ _ _).symm

/-- **The badness pattern of the first `N` rectangles**: the fault pattern one level down. -/
def reducePat (N : ℕ) (ω : ι → Bool) : Fin N → Bool := fun j => C.badSeq ω j

theorem measurable_reducePat [Fintype ι] (N : ℕ) : Measurable (C.reducePat N) :=
  fun _ _ => (Set.toFinite _).measurableSet

/-- ★★★ **One level of reduction carries local stochastic noise of parameter `p` to local stochastic
noise of parameter `A p²`** on the rectangles. -/
theorem isLocalStochastic_map_reducePat [Fintype ι] [DecidableEq ι] {μ : Measure (ι → Bool)}
    {p : ℝ≥0∞}
    (hμ : IsLocalStochastic μ p) {A : ℕ} (hA : ∀ j, (C.M j).card ≤ A) (N : ℕ) :
    IsLocalStochastic (μ.map (C.reducePat N)) ((A : ℝ≥0∞) * p ^ 2) := by
  intro S
  rw [Measure.map_apply (C.measurable_reducePat N) (Set.toFinite _).measurableSet]
  have h := C.measure_forall_badSeq_le hμ hA (S.map Fin.valEmbedding)
  rw [Finset.card_map] at h
  refine (measure_mono fun ω hω => ?_).trans h
  intro j hj
  obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hj
  exact hω j' hj'

end RectChain

/-! ### The recursion and the threshold -/

/-- **The parameter after `k` reductions**: `lsBound A p (k + 1) = A · lsBound A p k²`. -/
def lsBound (A p : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => p
  | k + 1 => A * lsBound A p k ^ 2

theorem lsBound_zero (A p : ℝ≥0∞) : lsBound A p 0 = p := rfl

theorem lsBound_succ (A p : ℝ≥0∞) (k : ℕ) : lsBound A p (k + 1) = A * lsBound A p k ^ 2 := rfl

/-- ★★ **`k` reductions give parameter `lsBound A p k`**: any property of the levels that starts
at `p` and is carried by one reduction from `q` to `A q²` holds at level `k` with
`lsBound A p k`. -/
theorem lsBound_induction {P : ℕ → ℝ≥0∞ → Prop} {A p : ℝ≥0∞} (h0 : P 0 p)
    (hstep : ∀ k q, P k q → P (k + 1) (A * q ^ 2)) : ∀ k, P k (lsBound A p k)
  | 0 => h0
  | k + 1 => hstep k _ (lsBound_induction h0 hstep k)

/-- ★★ **`lsBound` is #51's `codeCapacityBound`**: `(A p)^{2^k} / A`, read in `ℝ≥0∞`. -/
theorem ofReal_codeCapacityBound {A : ℕ} {p : ℝ} (hp : 0 ≤ p) (k : ℕ) :
    ENNReal.ofReal (codeCapacityBound A p k) = lsBound A (ENNReal.ofReal p) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [codeCapacityBound_succ, lsBound_succ, ← ih,
      ENNReal.ofReal_mul (Nat.cast_nonneg A), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (codeCapacityBound_nonneg (Nat.cast_nonneg A) hp k)]

/-- ★★★ **Below the threshold the parameter tends to `0`**: for `A p < 1`, `lsBound A p k → 0`. -/
theorem tendsto_lsBound {A : ℕ} (hA : 0 < A) {p : ℝ} (hp : 0 ≤ p) (h : (A : ℝ) * p < 1) :
    Tendsto (lsBound A (ENNReal.ofReal p)) atTop (𝓝 0) := by
  have h1 := tendsto_codeCapacityBound (c := (A : ℝ)) (by exact_mod_cast hA) hp h
  have h2 := (ENNReal.tendsto_ofReal h1)
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr fun k => ?_
  exact ofReal_codeCapacityBound hp k

/-! ### Chains of steps -/

namespace RectChain

/-- The recovery before step `j`: step `j − 1`'s, none before step `0`. -/
def prevRec (R : ℕ → Finset ι) : ℕ → Finset ι
  | 0 => ∅
  | j + 1 => R j

/-- **The overlapping chain of #233**: step `j`'s locations `L j` (pairwise disjoint), its
recovery's `R j ⊆ L j`; rectangle `j`'s window is `L j ∪ R (j − 1)`, its truncated window `L j`,
and every pair of each is malignant. -/
def ofSteps [DecidableEq ι] (L R : ℕ → Finset ι) (hL : Pairwise fun j j' => Disjoint (L j) (L j'))
    (hR : ∀ j, R j ⊆ L j) : RectChain ι where
  W j := L j ∪ prevRec R j
  W' j := L j
  M j := (L j ∪ prevRec R j).powersetCard 2
  M' j := (L j).powersetCard 2
  card_eq j s hs := (Finset.mem_powersetCard.1 hs).2
  subset_W j s hs := (Finset.mem_powersetCard.1 hs).1
  M'_subset j := Finset.powersetCard_mono Finset.subset_union_left
  subset_W' j s hs := (Finset.mem_powersetCard.1 hs).1
  disjoint_far j j' h := by
    have mem : ∀ k x, x ∈ L k ∪ prevRec R k → ∃ a, (a = k ∨ a + 1 = k) ∧ x ∈ L a := by
      intro k x hx
      cases k with
      | zero => exact ⟨0, Or.inl rfl, by simpa [prevRec] using hx⟩
      | succ k =>
        rcases Finset.mem_union.1 hx with h | h
        · exact ⟨k + 1, Or.inl rfl, h⟩
        · exact ⟨k, Or.inr rfl, hR k (by simpa [prevRec] using h)⟩
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨a, ha, hxa⟩ := mem j x hx
    obtain ⟨b, hb, hxb⟩ := mem j' x hx'
    exact Finset.disjoint_left.1 (hL (show a ≠ b by omega)) hxa hxb
  disjoint_next j := by
    rw [Finset.disjoint_union_left]
    refine ⟨hL (by omega), ?_⟩
    cases j with
    | zero => exact Finset.disjoint_empty_left _
    | succ j => exact (hL (by omega)).mono_left (hR j)

/-- ★ **At most `C(w, 2)` malignant pairs** per rectangle when every window has at most `w`
locations. -/
theorem ofSteps_card_M_le [DecidableEq ι] {L R : ℕ → Finset ι}
    (hL : Pairwise fun j j' => Disjoint (L j) (L j'))
    (hR : ∀ j, R j ⊆ L j) {w : ℕ} (hw : ∀ j, (L j ∪ prevRec R j).card ≤ w) (j : ℕ) :
    ((ofSteps L R hL hR).M j).card ≤ w.choose 2 := by
  show ((L j ∪ prevRec R j).powersetCard 2).card ≤ w.choose 2
  rw [Finset.card_powersetCard]
  exact Nat.choose_le_choose 2 (hw j)

end RectChain

end QuantumInfo

end
