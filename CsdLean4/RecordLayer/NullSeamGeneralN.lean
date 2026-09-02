/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.NullSeamWitness

/-!
# SigmaLayer/NullSeamGeneralN: the third horn at every `N` (D3b)

**Category:** dynamical measurement — the general-`N` null-seam witness
(`specs/BACKLOG.md` D3b; the two-cell witness is `NullSeamWitness.lean`).

## The construction

`N` cells on the register circle, cut at the corpus's own cumulative Born
positions `loSum r i` (`BornFibrePartition.lean`) of a positive weight vector
`r` summing to `1`. Each closed cell is realised as a **closed ball**
`cellArc r i` around the existing cell midpoint `cellMid r i`
(`PointerWeights.lean`), radius `r i / 2`, which hands the cell mass to
`AddCircle.volume_closedBall` with no bespoke measure computation; the open
cell is a `rep`-preimage (`CircleFibre.lean`), so measurability is free.

The landing amplitudes are **plateau tents**
`cellTent r i θ = max 0 (cellGap r − infDist θ (cellArc r i))` with
`cellGap = (min r)/2`: value exactly `cellGap` on the whole closed cell,
decaying outside, vanishing at distance `cellGap`. Off the seam the active
cell's tent dominates strictly (it sits at the plateau, every other tent is
strictly below it, and at most one other tent is nonzero — the separation
estimates); at a seam point the two adjacent tents are **equal** — the kiss.
The record criterion `momentMap > ½` therefore reads: record `i` exactly on
the **open** cell `i`, no record exactly on the `N` seam points.

The propagator's unitary is a single global formula — the rotation by `π/2`
in the plane spanned by the ready direction `f₀` and the (normalised)
amplitude vector `a ⊥ f₀`:

    M(a) = I − f₀f₀ᵀ − aaᵀ + af₀ᵀ − f₀aᵀ,

orthogonal for every unit `a` with `a₀ = 0` (`seamRotation_mem`), with first
column `a` (the landing). Because `M` is a **fixed polynomial in the
amplitudes**, continuity of the propagator reduces to continuity of the
tents — there is no per-boundary gluing of plane rotations, and hence none of
the monodromy trouble a piecewise-rotation design would have at the wrap.

## Relation to the two-cell witness

`NullSeamWitness.lean` stands as the minimal exhibit (its `(f₁,f₂)`-plane
rotation is the `N = 2` kissing-crossing in bespoke form); this module proves
the same closure shape for every `N ≥ 2` and every weight vector: continuity,
measure invariance, exact records off an `N`-point null seam, and **exact**
Born mass `r i` per cell (`nullSeamGeneralClosure`). The scope notes of the
two-cell module apply verbatim: the exactness is at the Dirac-calibrated
ready point (the third horn's price — `posMeasure_noRecord_pointer`), and the
cell split `r` plays the Born-weight role without a preparation in the arena.
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup Metric
open scoped LinearAlgebra.Projectivization

variable {N : ℕ}

/-! ### Cumulative-position extras

`loSum` (`BornFibrePartition.lean`) carries the ordering lemmas
(`loSum_add_le_loSum`, `loSum_add_self_le_one`); the two small identities
below complete the tiling picture. -/

lemma loSum_nonneg (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (i : Fin N) :
    0 ≤ loSum r i :=
  Finset.sum_nonneg fun j _ => (hr j).le

lemma loSum_zero_val {i : Fin N} (r : Fin N → ℝ) (hi : i.val = 0) :
    loSum r i = 0 := by
  rw [loSum,
    Finset.filter_false_of_mem
      (fun j _ => show ¬((j : Fin N).val < i.val) by omega)]
  exact Finset.sum_empty

/-- Consecutive cumulative positions: the cell for `i` ends where the cell
for the next index begins. -/
lemma loSum_succ_val (r : Fin N → ℝ) {i j : Fin N} (hij : j.val = i.val + 1) :
    loSum r j = loSum r i + r i := by
  rw [loSum, loSum, hij]
  rw [show Finset.univ.filter (fun k : Fin N => (k : ℕ) < i.val + 1)
      = insert i (Finset.univ.filter (fun k : Fin N => (k : ℕ) < i.val)) from by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hk)
      · omega
      · omega]
  rw [Finset.sum_insert (by simp)]
  ring

/-- The last cell ends at `1`. -/
lemma loSum_last_add (r : Fin N → ℝ) (hsum : ∑ i, r i = 1) {i : Fin N}
    (hi : i.val + 1 = N) : loSum r i + r i = 1 := by
  rw [← hsum, loSum]
  rw [show Finset.univ.filter (fun k : Fin N => (k : ℕ) < i.val)
      = Finset.univ.erase i from by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    constructor
    · intro hk h
      subst h
      omega
    · intro hk
      have hkN := k.isLt
      rcases Nat.lt_or_ge k.val i.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega : k.val = i.val)) hk]
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-! ### The canonical representative -/

lemma rep_mem (θ : CircleFibre) : rep θ ∈ Set.Ioc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := (AddCircle.equivIoc (1 : ℝ) 0 θ).2
  refine ⟨h1, ?_⟩
  show ((AddCircle.equivIoc (1 : ℝ) 0 θ) : ℝ) ≤ 1
  linarith

/-! ### The tent half-width -/

variable [NeZero N]

/-- The tent half-width: half the smallest cell width. Every tent extends
exactly `cellGap` beyond its cell, so tents of cells that do not share a
boundary never overlap. -/
noncomputable def cellGap (r : Fin N → ℝ) : ℝ :=
  (Finset.univ.inf' Finset.univ_nonempty r) / 2

lemma cellGap_pos (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) : 0 < cellGap r := by
  rw [cellGap]
  have h := (Finset.lt_inf'_iff (Finset.univ_nonempty)).mpr fun i _ => hr i
  linarith

lemma two_cellGap_le (r : Fin N → ℝ) (i : Fin N) : 2 * cellGap r ≤ r i := by
  rw [cellGap]
  have h := Finset.inf'_le r (Finset.mem_univ i)
  linarith

/-! ### Circle lemmas beyond the two-cell toolkit -/

/-- On lifts within a half-period, the circle distance is exact. -/
lemma circle_dist_coe_eq {a b : ℝ} (h : |a - b| ≤ 1 / 2) :
    dist ((a : ℝ) : CircleFibre) ((b : ℝ) : CircleFibre) = |a - b| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [show round (a - b) = 0 from round_eq_zero_iff.mpr
      ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩]
    rw [Int.cast_zero, sub_zero]
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp heq with h2 | h2
    · rw [h2, show round ((1 : ℝ)/2) = 1 from by norm_num [round_eq]]
      norm_num
    · rw [h2]
      rw [show round (-(1/2) : ℝ) = 0 from by norm_num [round_eq]]
      norm_num

/-- The circle distance of two lifts is at least `min |a−b| (1 − |a−b|)`. -/
lemma circle_dist_coe_ge (a b : ℝ) :
    min |a - b| (1 - |a - b|)
      ≤ dist ((a : ℝ) : CircleFibre) ((b : ℝ) : CircleFibre) := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  rcases eq_or_ne (round (a - b)) 0 with h0 | h0
  · rw [h0, Int.cast_zero, sub_zero]
    exact min_le_left _ _
  · have h1 : (1 : ℝ) ≤ |(round (a - b) : ℝ)| := by
      have : (1 : ℤ) ≤ |round (a - b)| := Int.one_le_abs h0
      exact_mod_cast this
    refine le_trans (min_le_right _ _) ?_
    have h4 := abs_sub_abs_le_abs_sub ((round (a - b) : ℝ)) (a - b)
    rw [show |((round (a - b) : ℝ)) - (a - b)| = |a - b - (round (a - b) : ℝ)| from
      abs_sub_comm _ _] at h4
    linarith

/-! ### The cells -/

variable (r : Fin N → ℝ)

/-- Closed cell `i`: the closed ball of radius `r i / 2` around the existing
cell midpoint `cellMid r i` (`PointerWeights.lean`). Equal to the arc image of
its lift interval (`cellArc_eq_image`). -/
noncomputable def cellArc (i : Fin N) : Set CircleFibre :=
  Metric.closedBall (cellMid r i) (r i / 2)

/-- The open cell: the `rep`-preimage of the open CDF interval, so
measurability is definitional (compare `circleCell`). -/
noncomputable def openCell (i : Fin N) : Set CircleFibre :=
  rep ⁻¹' Set.Ioo (loSum r i) (loSum r i + r i)

/-- The seam point at the left end of cell `i`. The `N` of them are the cell
boundaries (the right end of the last cell wraps to the left end of the
first). -/
noncomputable def seamPoint (i : Fin N) : CircleFibre :=
  ((loSum r i : ℝ) : CircleFibre)

variable {r}

omit [NeZero N] in
lemma measurableSet_openCell (i : Fin N) : MeasurableSet (openCell r i) :=
  measurable_rep measurableSet_Ioo

omit [NeZero N] in
/-- The closed cell is the arc image of its lift interval. -/
lemma cellArc_eq_image (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1) (i : Fin N) :
    cellArc r i
      = (fun s : ℝ => (s : CircleFibre)) ''
          Set.Icc (loSum r i) (loSum r i + r i) := by
  have hw1 : r i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
  have hmid : cellMid r i = ((loSum r i + r i / 2 : ℝ) : CircleFibre) := rfl
  ext θ
  constructor
  · intro hθ
    rw [cellArc, hmid, Metric.mem_closedBall] at hθ
    obtain ⟨u, hu, hnorm, -⟩ :=
      exists_norm_lift (θ - ((loSum r i + r i / 2 : ℝ) : CircleFibre))
    have hdist : |u| ≤ r i / 2 := by
      rw [hnorm, ← dist_eq_norm]
      exact hθ
    refine ⟨loSum r i + r i / 2 + u, ⟨?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp hdist).1]
    · linarith [(abs_le.mp hdist).2]
    · show ((loSum r i + r i / 2 + u : ℝ) : CircleFibre) = θ
      rw [AddCircle.coe_add, hu]
      abel
  · rintro ⟨s, hs, rfl⟩
    rw [cellArc, hmid, Metric.mem_closedBall]
    refine (circle_dist_coe_le s (loSum r i + r i / 2)).trans ?_
    rw [abs_le]
    constructor
    · linarith [hs.1]
    · linarith [hs.2]

/-- Every circle point lies in some closed cell (via its canonical
representative, whose CDF interval is found by taking the largest cumulative
position strictly below it). -/
lemma exists_rep_mem_cell (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) :
    ∃ i : Fin N, rep θ ∈ Set.Ioc (loSum r i) (loSum r i + r i) := by
  classical
  set y := rep θ with hy
  have hy0 : 0 < y := (rep_mem θ).1
  have hy1 : y ≤ 1 := (rep_mem θ).2
  -- the candidates: indices whose cumulative position is strictly below y
  set S : Finset (Fin N) := Finset.univ.filter (fun i => loSum r i < y) with hS
  have hS_ne : S.Nonempty := by
    refine ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, ?_⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      rw [loSum_zero_val r rfl]
      exact hy0⟩
  -- take the largest such index (in the Fin order = ℕ order)
  obtain ⟨i, hiS, hmax⟩ := S.exists_max_image (fun i => i.val) hS_ne
  rw [hS, Finset.mem_filter] at hiS
  refine ⟨i, hiS.2, ?_⟩
  by_contra hgt
  push Not at hgt
  -- then the next index is also a candidate, contradicting maximality
  rcases Nat.lt_or_ge (i.val + 1) N with hlt | hge
  · set j : Fin N := ⟨i.val + 1, hlt⟩ with hj
    have hjS : j ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [loSum_succ_val r (show j.val = i.val + 1 from rfl)]
      exact hgt
    have hjval : j.val = i.val + 1 := rfl
    have := hmax j hjS
    omega
  · have hi1 : i.val + 1 = N := by omega
    have := loSum_last_add r hsum hi1
    linarith

omit [NeZero N] in
/-- The open cell sits inside the closed cell. -/
lemma openCell_subset_cellArc (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (i : Fin N) : openCell r i ⊆ cellArc r i := by
  intro θ hθ
  rw [openCell, Set.mem_preimage] at hθ
  rw [cellArc_eq_image hr hsum]
  exact ⟨rep θ, ⟨hθ.1.le, hθ.2.le⟩, coe_rep θ⟩

omit [NeZero N] in
/-- The Born mass of an open cell is exactly its weight (the `Ioo` sibling of
`volume_circleCell`, same measure-preserving route). -/
lemma volume_openCell (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1) (i : Fin N) :
    (volume : Measure CircleFibre) (openCell r i) = ENNReal.ofReal (r i) := by
  have hlo : 0 ≤ loSum r i := loSum_nonneg r hr i
  have hhi : loSum r i + r i ≤ 1 :=
    loSum_add_self_le_one r (fun j => (hr j).le) hsum i
  have hS : MeasurableSet (Subtype.val ⁻¹' Set.Ioo (loSum r i) (loSum r i + r i) :
      Set (Set.Ioc (0:ℝ) ((0:ℝ) + 1))) := measurable_subtype_coe measurableSet_Ioo
  have hpre : openCell r i
      = (AddCircle.equivIoc (1:ℝ) 0) ⁻¹'
        (Subtype.val ⁻¹' Set.Ioo (loSum r i) (loSum r i + r i)) := rfl
  rw [hpre, (AddCircle.measurePreserving_equivIoc (T := (1:ℝ)) (a := 0)).measure_preimage
    hS.nullMeasurableSet,
    Measure.comap_apply _ Subtype.val_injective
      (fun s hs => measurableSet_Ioc.subtype_image hs) _ hS]
  have himg : (Subtype.val '' (Subtype.val ⁻¹' Set.Ioo (loSum r i) (loSum r i + r i) :
      Set (Set.Ioc (0:ℝ) ((0:ℝ) + 1)))) = Set.Ioo (loSum r i) (loSum r i + r i) := by
    rw [Subtype.image_preimage_coe]
    apply Set.inter_eq_self_of_subset_right
    intro x hx
    exact ⟨lt_of_le_of_lt hlo hx.1, by
      rw [zero_add]
      exact le_trans hx.2.le hhi⟩
  rw [himg, Real.volume_Ioo]
  congr 1
  ring

/-! ### The tents -/

variable (r)

/-- The plateau tent of cell `i`: value `cellGap r` on the whole closed cell,
decaying with the distance outside, vanishing at distance `cellGap r`. -/
noncomputable def cellTent (i : Fin N) (θ : CircleFibre) : ℝ :=
  max 0 (cellGap r - infDist θ (cellArc r i))

variable {r}

lemma continuous_cellTent (i : Fin N) : Continuous (cellTent r i) :=
  continuous_const.max (continuous_const.sub (continuous_infDist_pt _))

lemma cellTent_nonneg (i : Fin N) (θ : CircleFibre) : 0 ≤ cellTent r i θ :=
  le_max_left 0 _

lemma cellTent_le (hr : ∀ i, 0 < r i) (i : Fin N) (θ : CircleFibre) :
    cellTent r i θ ≤ cellGap r := by
  rw [cellTent]
  rcases max_cases 0 (cellGap r - infDist θ (cellArc r i)) with ⟨h, hle⟩ | ⟨h, -⟩
  · rw [h]
    exact (cellGap_pos r hr).le
  · rw [h]
    linarith [infDist_nonneg (s := cellArc r i) (x := θ)]

/-- On the closed cell the tent sits at its plateau. -/
lemma cellTent_of_mem (hr : ∀ i, 0 < r i) {i : Fin N} {θ : CircleFibre}
    (hθ : θ ∈ cellArc r i) : cellTent r i θ = cellGap r := by
  rw [cellTent, infDist_zero_of_mem hθ, sub_zero]
  exact max_eq_right (cellGap_pos r hr).le

omit [NeZero N] in
lemma cellArc_nonempty (hr : ∀ i, 0 < r i) (i : Fin N) : (cellArc r i).Nonempty :=
  ⟨cellMid r i, Metric.mem_closedBall_self (by linarith [hr i])⟩

/-- Off the closed cell the tent is strictly below its plateau. -/
lemma cellTent_lt_of_notMem (hr : ∀ i, 0 < r i) {i : Fin N} {θ : CircleFibre}
    (hθ : θ ∉ cellArc r i) : cellTent r i θ < cellGap r := by
  have hpos : 0 < infDist θ (cellArc r i) :=
    (Metric.isClosed_closedBall.notMem_iff_infDist_pos (cellArc_nonempty hr i)).mp hθ
  rw [cellTent]
  rcases max_cases 0 (cellGap r - infDist θ (cellArc r i)) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact cellGap_pos r hr
  · rw [h]
    linarith

/-- Vanishing at distance `cellGap`. -/
lemma cellTent_eq_zero {i : Fin N} {θ : CircleFibre}
    (h : cellGap r ≤ infDist θ (cellArc r i)) : cellTent r i θ = 0 :=
  max_eq_left (by linarith)

/-- Positivity means the cell is within tent reach. -/
lemma infDist_lt_of_cellTent_pos {i : Fin N} {θ : CircleFibre}
    (h : 0 < cellTent r i θ) : infDist θ (cellArc r i) < cellGap r := by
  by_contra hge
  push Not at hge
  rw [cellTent_eq_zero hge] at h
  exact lt_irrefl 0 h

/-! ### Separation: at most one foreign tent is ever within reach -/

/-- Tent-positivity at a lift, resolved into the two approach directions:
if cell `k`'s tent is positive at `coe s`, then `s` is within `cellGap` of
the cell's lift interval either directly or around the wrap. -/
lemma cellTent_pos_branches (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {k : Fin N} {s : ℝ}
    (hpos : 0 < cellTent r k ((s : ℝ) : CircleFibre)) :
    ∃ t, loSum r k ≤ t ∧ t ≤ loSum r k + r k ∧
      (|s - t| < cellGap r ∨ 1 - |s - t| < cellGap r) := by
  have hinf := infDist_lt_of_cellTent_pos hpos
  rw [cellArc_eq_image hr hsum] at hinf
  obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff
    (Set.Nonempty.image _ (Set.nonempty_Icc.mpr (by linarith [hr k])))).mp hinf
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨t, ht.1, ht.2, ?_⟩
  exact min_lt_iff.mp (lt_of_le_of_lt (circle_dist_coe_ge s t) hdy)

omit [NeZero N] in
/-- The open cell meets no other closed cell. -/
lemma openCell_disjoint_cellArc (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {i k : Fin N} (hik : k ≠ i) {θ : CircleFibre} (hθ : θ ∈ openCell r i) :
    θ ∉ cellArc r k := by
  intro hmem
  rw [openCell, Set.mem_preimage] at hθ
  rw [cellArc_eq_image hr hsum] at hmem
  obtain ⟨t, ht, hcoe⟩ := hmem
  set s := rep θ with hs
  have hsc : ((s : ℝ) : CircleFibre) = θ := coe_rep θ
  have hcoe' : ((t : ℝ) : CircleFibre) = θ := hcoe
  -- the two lifts agree on the circle, hence differ by an integer
  have hz : ((t - s : ℝ) : CircleFibre) = 0 := by
    rw [AddCircle.coe_sub, hcoe', hsc, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have hn' : (n : ℝ) = t - s := by
    rw [← hn]
    simp
  -- both lifts live strictly inside one period, so the integer is zero
  have hs0 : 0 < s := lt_of_le_of_lt (loSum_nonneg r hr i) hθ.1
  have hs1 : s < 1 :=
    lt_of_lt_of_le hθ.2 (loSum_add_self_le_one r (fun j => (hr j).le) hsum i)
  have ht0 : 0 ≤ t := le_trans (loSum_nonneg r hr k) ht.1
  have ht1 : t ≤ 1 :=
    le_trans ht.2 (loSum_add_self_le_one r (fun j => (hr j).le) hsum k)
  have hn0 : n = 0 := by
    have h1 : (-1 : ℝ) < (n : ℝ) := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hts : t = s := by
    rw [hn0] at hn'
    push_cast at hn'
    linarith
  -- so `s` lies in both cells' lift intervals — impossible for `k ≠ i`
  subst hts
  rcases Nat.lt_or_ge k.val i.val with hlt | hge
  · have := loSum_add_le_loSum r (fun j => (hr j).le) hlt
    linarith [ht.2, hθ.1]
  · have hgt : i.val < k.val := by
      rcases Nat.lt_or_ge i.val k.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega : k.val = i.val)) hik
    have := loSum_add_le_loSum r (fun j => (hr j).le) hgt
    linarith [ht.1, hθ.2]

/-- Foreign-tent approach bounds, cell to the left of the active one. -/
lemma cellTent_pos_left (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {i k : Fin N} (hki : k.val < i.val) {s : ℝ}
    (hsi : loSum r i < s ∧ s < loSum r i + r i)
    (hpos : 0 < cellTent r k ((s : ℝ) : CircleFibre)) :
    s < loSum r k + r k + cellGap r ∨ loSum r k + 1 - cellGap r < s := by
  obtain ⟨t, ht0, ht1, hbr⟩ := cellTent_pos_branches hr hsum hpos
  have hts : t < s := by
    have := loSum_add_le_loSum r (fun j => (hr j).le) hki
    linarith [hsi.1]
  rw [abs_of_pos (by linarith : (0:ℝ) < s - t)] at hbr
  rcases hbr with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Foreign-tent approach bounds, cell to the right of the active one. -/
lemma cellTent_pos_right (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {i k : Fin N} (hik : i.val < k.val) {s : ℝ}
    (hsi : loSum r i < s ∧ s < loSum r i + r i)
    (hpos : 0 < cellTent r k ((s : ℝ) : CircleFibre)) :
    loSum r k - cellGap r < s ∨ s < loSum r k + r k + cellGap r - 1 := by
  obtain ⟨t, ht0, ht1, hbr⟩ := cellTent_pos_branches hr hsum hpos
  have hts : s < t := by
    have := loSum_add_le_loSum r (fun j => (hr j).le) hik
    linarith [hsi.2]
  rw [abs_of_neg (by linarith : s - t < 0)] at hbr
  rcases hbr with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **At most one foreign tent is within reach** at any point of an open
cell. The twelve position/branch combinations each contradict the cumulative
ordering (`loSum_add_le_loSum`), the one-turn bound
(`loSum_add_self_le_one`), or the width floor (`two_cellGap_le`). -/
lemma cellTent_pair_exclusion (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {i k l : Fin N} (hk : k ≠ i) (hl : l ≠ i) (hkl : k.val < l.val)
    {θ : CircleFibre} (hθ : θ ∈ openCell r i) :
    ¬(0 < cellTent r k θ ∧ 0 < cellTent r l θ) := by
  rintro ⟨hpk, hpl⟩
  set s := rep θ with hs
  have hsc : ((s : ℝ) : CircleFibre) = θ := coe_rep θ
  have hsi : loSum r i < s ∧ s < loSum r i + r i := by
    rw [openCell, Set.mem_preimage] at hθ
    exact ⟨hθ.1, hθ.2⟩
  rw [← hsc] at hpk hpl
  have hnn := fun j => (hr j).le
  have hgap := cellGap_pos r hr
  -- shared cumulative facts
  have hk2 := two_cellGap_le r k
  have hl2 := two_cellGap_le r l
  have hi2 := two_cellGap_le r i
  have hkl' := loSum_add_le_loSum r hnn hkl
  have hione := loSum_add_self_le_one r hnn hsum i
  have hkone := loSum_add_self_le_one r hnn hsum k
  have hlone := loSum_add_self_le_one r hnn hsum l
  have hk0 := loSum_nonneg r hr k
  have hl0 := loSum_nonneg r hr l
  have hi0 := loSum_nonneg r hr i
  rcases Nat.lt_or_ge i.val k.val with hik | hik
  · -- i < k < l : both foreign cells to the right
    have hbk := cellTent_pos_right hr hsum hik hsi hpk
    have hbl := cellTent_pos_right hr hsum (lt_trans hik hkl) hsi hpl
    have hik' := loSum_add_le_loSum r hnn hik
    rcases hbk with hk1 | hk1 <;> rcases hbl with hl1 | hl1
    · linarith
    · linarith
    · linarith
    · linarith
  · have hki : k.val < i.val := by
      rcases Nat.lt_or_ge k.val i.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega : k.val = i.val)) hk
    rcases Nat.lt_or_ge i.val l.val with hil | hil
    · -- k < i < l : one on each side
      have hbk := cellTent_pos_left hr hsum hki hsi hpk
      have hbl := cellTent_pos_right hr hsum hil hsi hpl
      have hki' := loSum_add_le_loSum r hnn hki
      have hil' := loSum_add_le_loSum r hnn hil
      rcases hbk with hk1 | hk1 <;> rcases hbl with hl1 | hl1
      · linarith
      · linarith
      · linarith
      · linarith
    · -- k < l < i : both to the left
      have hli : l.val < i.val := by
        rcases Nat.lt_or_ge l.val i.val with h | h
        · exact h
        · exact absurd (Fin.ext (by omega : l.val = i.val)) hl
      have hbk := cellTent_pos_left hr hsum hki hsi hpk
      have hbl := cellTent_pos_left hr hsum hli hsi hpl
      have hli' := loSum_add_le_loSum r hnn hli
      rcases hbk with hk1 | hk1 <;> rcases hbl with hl1 | hl1
      · linarith
      · linarith
      · linarith
      · linarith

/-! ### The amplitude vector and the record criterion -/

variable (r)

/-- The (unnormalised) landing amplitude vector: zero in the ready slot,
tent `i` in record slot `i.succ`. -/
noncomputable def tentVec (θ : CircleFibre) : EuclideanSpace ℂ (Fin (N + 1)) :=
  WithLp.toLp 2 (fun k => Fin.cases 0 (fun i => ((cellTent r i θ : ℝ) : ℂ)) k)

variable {r}

lemma tentVec_zero (θ : CircleFibre) : tentVec r θ 0 = 0 := rfl

lemma tentVec_succ (θ : CircleFibre) (i : Fin N) :
    tentVec r θ i.succ = ((cellTent r i θ : ℝ) : ℂ) := rfl

/-- Every point sits on some closed cell's plateau. -/
lemma exists_cellTent_plateau (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) : ∃ i, cellTent r i θ = cellGap r := by
  obtain ⟨i, hi⟩ := exists_rep_mem_cell (r := r) hsum θ
  refine ⟨i, cellTent_of_mem hr ?_⟩
  rw [cellArc_eq_image hr hsum]
  exact ⟨rep θ, ⟨hi.1.le, hi.2⟩, coe_rep θ⟩

lemma tentVec_ne_zero (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) : tentVec r θ ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_cellTent_plateau hr hsum θ
  intro h
  have h1 : tentVec r θ i.succ = 0 := by rw [h]; rfl
  rw [tentVec_succ, hi, Complex.ofReal_eq_zero] at h1
  have := cellGap_pos r hr
  linarith

/-- The squared norm of the tent vector is the tent sum of squares. -/
lemma norm_sq_tentVec (θ : CircleFibre) :
    ‖tentVec r θ‖ ^ 2 = ∑ i : Fin N, cellTent r i θ ^ 2 := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _), Fin.sum_univ_succ,
    show ‖tentVec r θ 0‖ ^ 2 = 0 from by rw [tentVec_zero]; simp, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tentVec_succ, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The seam rotation -/

/-- The rotation by `π/2` in the plane spanned by the ready direction `f₀`
and a unit amplitude vector `a ⊥ f₀`, over `ℝ`: first column `a`, first row
`−aᵀ` (off the corner), the record block `I − aaᵀ`. -/
noncomputable def seamRotationR {n : ℕ} (a : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k l =>
    if k = 0 then (if l = 0 then 0 else -(a l))
    else (if l = 0 then a k else (if k = l then 1 else 0) - a k * a l)

section SeamRotation

variable {n : ℕ} (a : Fin (n + 1) → ℝ)

@[simp] lemma seamRotationR_zero_zero : seamRotationR a 0 0 = 0 := by
  rw [seamRotationR, Matrix.of_apply, if_pos rfl, if_pos rfl]

@[simp] lemma seamRotationR_zero_succ (m : Fin n) :
    seamRotationR a 0 m.succ = -(a m.succ) := by
  rw [seamRotationR, Matrix.of_apply, if_pos rfl, if_neg (Fin.succ_ne_zero m)]

@[simp] lemma seamRotationR_succ_zero (k : Fin n) :
    seamRotationR a k.succ 0 = a k.succ := by
  rw [seamRotationR, Matrix.of_apply, if_neg (Fin.succ_ne_zero k), if_pos rfl]

@[simp] lemma seamRotationR_succ_succ (k l : Fin n) :
    seamRotationR a k.succ l.succ
      = (if k = l then (1:ℝ) else 0) - a k.succ * a l.succ := by
  rw [seamRotationR, Matrix.of_apply, if_neg (Fin.succ_ne_zero k),
    if_neg (Fin.succ_ne_zero l)]
  by_cases h : k = l
  · rw [if_pos (show k.succ = l.succ from by rw [h]), if_pos h]
  · rw [if_neg (fun hc => h (Fin.succ_inj.mp hc)), if_neg h]

/-- Orthogonality of the seam rotation, for every unit amplitude vector with
empty ready slot. -/
theorem seamRotationR_orthogonal (h0 : a 0 = 0) (hsum : ∑ k, a k ^ 2 = 1) :
    (seamRotationR a)ᵀ * seamRotationR a = 1 := by
  have hsum' : ∑ j : Fin n, a j.succ ^ 2 = 1 := by
    rw [Fin.sum_univ_succ, h0] at hsum
    simpa using hsum
  ext l m
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨m', rfl⟩
  · -- (0, 0)
    rw [Fin.sum_univ_succ]
    simp only [seamRotationR_zero_zero, seamRotationR_succ_zero]
    rw [show ∑ j : Fin n, a j.succ * a j.succ = ∑ j : Fin n, a j.succ ^ 2 from
      Finset.sum_congr rfl fun j _ => (sq (a j.succ)).symm, hsum',
      Matrix.one_apply_eq]
    ring
  · -- (0, m'.succ)
    rw [Fin.sum_univ_succ]
    simp only [seamRotationR_zero_zero, seamRotationR_zero_succ,
      seamRotationR_succ_zero, seamRotationR_succ_succ]
    rw [show ∑ j : Fin n,
        a j.succ * ((if j = m' then (1:ℝ) else 0) - a j.succ * a m'.succ)
        = ∑ j : Fin n,
            ((if j = m' then a j.succ else 0) - a j.succ ^ 2 * a m'.succ) from
      Finset.sum_congr rfl fun j _ => by
        by_cases hj : j = m'
        · rw [if_pos hj, if_pos hj]
          ring
        · rw [if_neg hj, if_neg hj]
          ring]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_ite_eq' Finset.univ m' (fun j => a j.succ), hsum',
      Matrix.one_apply_ne (Fin.succ_ne_zero m').symm]
    simp
  · -- (l'.succ, 0)
    rw [Fin.sum_univ_succ]
    simp only [seamRotationR_zero_zero, seamRotationR_zero_succ,
      seamRotationR_succ_zero, seamRotationR_succ_succ]
    rw [show ∑ j : Fin n,
        ((if j = l' then (1:ℝ) else 0) - a j.succ * a l'.succ) * a j.succ
        = ∑ j : Fin n,
            ((if j = l' then a j.succ else 0) - a l'.succ * a j.succ ^ 2) from
      Finset.sum_congr rfl fun j _ => by
        by_cases hj : j = l'
        · rw [if_pos hj, if_pos hj]
          ring
        · rw [if_neg hj, if_neg hj]
          ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ l' (fun j => a j.succ), hsum',
      Matrix.one_apply_ne (Fin.succ_ne_zero l')]
    simp
  · -- (l'.succ, m'.succ)
    rw [Fin.sum_univ_succ]
    simp only [seamRotationR_zero_succ, seamRotationR_succ_succ]
    rw [show ∑ j : Fin n,
        ((if j = l' then (1:ℝ) else 0) - a j.succ * a l'.succ)
          * ((if j = m' then (1:ℝ) else 0) - a j.succ * a m'.succ)
        = ∑ j : Fin n,
            ((if j = l' then (if l' = m' then (1:ℝ) else 0) else 0)
              - (if j = l' then a l'.succ * a m'.succ else 0)
              - (if j = m' then a m'.succ * a l'.succ else 0)
              + a j.succ ^ 2 * (a l'.succ * a m'.succ)) from
      Finset.sum_congr rfl fun j _ => by
        by_cases hjl : j = l' <;> by_cases hjm : j = m'
        · subst hjl
          subst hjm
          simp only [if_true]
          ring
        · subst hjl
          simp only [if_true, if_neg hjm]
          ring
        · subst hjm
          simp only [if_true, if_neg hjl]
          ring
        · simp only [if_neg hjl, if_neg hjm]
          ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul,
      Finset.sum_ite_eq' Finset.univ l'
        (fun _ => (if l' = m' then (1:ℝ) else 0)),
      Finset.sum_ite_eq' Finset.univ l' (fun _ => a l'.succ * a m'.succ),
      Finset.sum_ite_eq' Finset.univ m' (fun _ => a m'.succ * a l'.succ),
      hsum']
    simp only [Finset.mem_univ, if_true, one_mul]
    rw [Matrix.one_apply]
    by_cases hlm : l' = m'
    · rw [if_pos hlm, if_pos (show l'.succ = m'.succ from by rw [hlm])]
      subst hlm
      ring
    · rw [if_neg hlm, if_neg (fun h => hlm (Fin.succ_inj.mp h))]
      ring

/-- The seam rotation over `ℂ`: the real matrix, entrywise embedded. -/
noncomputable def seamRotation (a : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (seamRotationR a).map Complex.ofReal

theorem seamRotation_mem (h0 : a 0 = 0) (hsum : ∑ k, a k ^ 2 = 1) :
    seamRotation a ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  have hstar : star (seamRotation a) = (seamRotationR a)ᵀ.map Complex.ofReal := by
    show (seamRotation a)ᴴ = _
    ext k l
    rw [Matrix.conjTranspose_apply, seamRotation, Matrix.map_apply,
      Matrix.map_apply, Matrix.transpose_apply]
    exact Complex.conj_ofReal _
  rw [Matrix.mem_unitaryGroup_iff']
  rw [hstar, seamRotation,
    show ((seamRotationR a)ᵀ.map Complex.ofReal) * ((seamRotationR a).map Complex.ofReal)
      = ((seamRotationR a)ᵀ * seamRotationR a).map Complex.ofReal from
    (Matrix.map_mul (f := Complex.ofRealHom)).symm,
    seamRotationR_orthogonal a h0 hsum]
  exact Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)

/-- The first column of the seam rotation is the amplitude vector. -/
lemma seamRotation_mulVec_single (h0 : a 0 = 0) :
    Matrix.toEuclideanLin (seamRotation a) (EuclideanSpace.single 0 (1 : ℂ))
      = WithLp.toLp 2 (fun k => ((a k : ℝ) : ℂ)) := by
  rw [Matrix.toLpLin_apply]
  apply PiLp.ext
  intro k
  show (seamRotation a *ᵥ WithLp.ofLp (EuclideanSpace.single 0 (1 : ℂ))) k = _
  rw [PiLp.ofLp_single, Matrix.mulVec_single]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
  · show seamRotation a 0 0 * 1 = ((a 0 : ℝ) : ℂ)
    rw [seamRotation, Matrix.map_apply, seamRotationR_zero_zero, h0]
    simp
  · show seamRotation a k'.succ 0 * 1 = ((a k'.succ : ℝ) : ℂ)
    rw [seamRotation, Matrix.map_apply, seamRotationR_succ_zero]
    simp

end SeamRotation

/-! ### The propagator -/

variable (r)

/-- The total tent weight (the amplitude normaliser). -/
noncomputable def tentTotal (θ : CircleFibre) : ℝ :=
  Real.sqrt (∑ j : Fin N, cellTent r j θ ^ 2)

variable {r}

lemma tentTotal_pos (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1) (θ : CircleFibre) :
    0 < tentTotal r θ := by
  rw [tentTotal]
  refine Real.sqrt_pos.mpr ?_
  obtain ⟨i, hi⟩ := exists_cellTent_plateau hr hsum θ
  have hpos : 0 < cellTent r i θ ^ 2 := by
    have := cellGap_pos r hr
    rw [hi]
    positivity
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (f := fun j => cellTent r j θ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

lemma sq_tentTotal (θ : CircleFibre) :
    tentTotal r θ ^ 2 = ∑ j : Fin N, cellTent r j θ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

variable (r)

/-- The normalised landing amplitudes: empty ready slot, `tent/total` in the
record slots. -/
noncomputable def seamAmp (θ : CircleFibre) : Fin (N + 1) → ℝ :=
  fun k => Fin.cases 0 (fun i => cellTent r i θ / tentTotal r θ) k

variable {r}

lemma seamAmp_zero (θ : CircleFibre) : seamAmp r θ 0 = 0 := rfl

lemma seamAmp_succ (θ : CircleFibre) (i : Fin N) :
    seamAmp r θ i.succ = cellTent r i θ / tentTotal r θ := rfl

lemma seamAmp_sq_sum (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) : ∑ k, seamAmp r θ k ^ 2 = 1 := by
  rw [Fin.sum_univ_succ, seamAmp_zero]
  have hT := tentTotal_pos hr hsum θ
  have hSpos : (0:ℝ) < ∑ j : Fin N, cellTent r j θ ^ 2 := by
    rw [← sq_tentTotal]
    positivity
  rw [show ∑ j : Fin N, seamAmp r θ j.succ ^ 2
      = (∑ j : Fin N, cellTent r j θ ^ 2) / tentTotal r θ ^ 2 from by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [seamAmp_succ, div_pow]]
  rw [sq_tentTotal, div_self hSpos.ne']
  ring

/-- The propagator's unitary at register point `θ`. -/
noncomputable def nullSeamGenUU (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) : Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  ⟨seamRotation (seamAmp r θ),
    seamRotation_mem _ (seamAmp_zero θ) (seamAmp_sq_sum hr hsum θ)⟩

/-- **The general-`N` null-seam propagator**: register conserved, pointer
rotated by the seam rotation at the register's amplitudes. -/
noncomputable def nullSeamGenEvolve (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1) :
    CircleFibre × Pointer N → CircleFibre × Pointer N :=
  fun y => (y.1, nullSeamGenUU hr hsum y.1 • y.2)

/-- The amplitude vector is the tent vector, normalised. -/
lemma seamAmp_toLp_smul (θ : CircleFibre) :
    WithLp.toLp 2 (fun k => ((seamAmp r θ k : ℝ) : ℂ))
      = (((tentTotal r θ)⁻¹ : ℝ) : ℂ) • tentVec r θ := by
  apply PiLp.ext
  intro k
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
  · show ((seamAmp r θ 0 : ℝ) : ℂ) = (_ • tentVec r θ) 0
    rw [seamAmp_zero]
    rw [show (((((tentTotal r θ)⁻¹ : ℝ) : ℂ)) • tentVec r θ) 0
        = (((tentTotal r θ)⁻¹ : ℝ) : ℂ) * tentVec r θ 0 from rfl,
      tentVec_zero]
    simp
  · show ((seamAmp r θ k'.succ : ℝ) : ℂ) = (_ • tentVec r θ) k'.succ
    rw [show (((((tentTotal r θ)⁻¹ : ℝ) : ℂ)) • tentVec r θ) k'.succ
        = (((tentTotal r θ)⁻¹ : ℝ) : ℂ) * tentVec r θ k'.succ from rfl,
      seamAmp_succ, tentVec_succ]
    push_cast
    rw [div_eq_inv_mul]

/-- **The landing identity**: the propagator sends the calibrated ready state
to the tent ray. -/
lemma nullSeamGenEvolve_ready (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) :
    (nullSeamGenEvolve hr hsum (θ, readyState)).2
      = Projectivization.mk ℂ (tentVec r θ) (tentVec_ne_zero hr hsum θ) := by
  show nullSeamGenUU hr hsum θ • readyState = _
  rw [readyState, vertexPoint,
    Projectivization.smul_mk_eq_mk_toEuclideanLin _ (single_ne_zero' 0)]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨(((tentTotal r θ)⁻¹ : ℝ) : ℂ), ?_⟩
  show (((tentTotal r θ)⁻¹ : ℝ) : ℂ) • tentVec r θ
      = Matrix.toEuclideanLin (seamRotation (seamAmp r θ))
          (EuclideanSpace.single 0 (1:ℂ))
  rw [seamRotation_mulVec_single _ (seamAmp_zero θ), seamAmp_toLp_smul θ]

/-! ### Records: exactly the open cells -/

/-- The landing moments are the normalised squared tents. -/
lemma momentMap_tentVec (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) (i : Fin N) :
    LF4.momentMap
        (Projectivization.mk ℂ (tentVec r θ) (tentVec_ne_zero hr hsum θ)) i.succ
      = cellTent r i θ ^ 2 / ∑ j : Fin N, cellTent r j θ ^ 2 := by
  rw [LF4.momentMap_mk _ (tentVec_ne_zero hr hsum θ), norm_sq_tentVec]
  congr 1
  rw [tentVec_succ, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The record criterion**: outcome `i` is recorded iff cell `i`'s tent
strictly dominates all the others combined. -/
lemma tentVec_record_iff (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) (i : Fin N) :
    Projectivization.mk ℂ (tentVec r θ) (tentVec_ne_zero hr hsum θ)
        ∈ recordRegion (K := N) i
      ↔ ∑ j ∈ Finset.univ.erase i, cellTent r j θ ^ 2 < cellTent r i θ ^ 2 := by
  have hS : ∑ j : Fin N, cellTent r j θ ^ 2
      = cellTent r i θ ^ 2 + ∑ j ∈ Finset.univ.erase i, cellTent r j θ ^ 2 :=
    (Finset.add_sum_erase Finset.univ (fun j => cellTent r j θ ^ 2)
      (Finset.mem_univ i)).symm
  have hS0 : (0:ℝ) < ∑ j : Fin N, cellTent r j θ ^ 2 := by
    have := tentTotal_pos hr hsum θ
    rw [← sq_tentTotal]
    positivity
  rw [recordRegion, Set.mem_ofPred_eq, momentMap_tentVec hr hsum θ i,
    lt_div_iff₀ hS0]
  constructor
  · intro h
    nlinarith [hS]
  · intro h
    nlinarith [hS]

/-- ★ **Records on the open cells — exactly.** -/
theorem nullSeamGen_landing (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {i : Fin N} {θ : CircleFibre} (hθ : θ ∈ openCell r i) :
    (nullSeamGenEvolve hr hsum (θ, readyState)).2 ∈ recordRegion (K := N) i := by
  rw [nullSeamGenEvolve_ready hr hsum θ, tentVec_record_iff hr hsum θ i]
  have hti : cellTent r i θ = cellGap r :=
    cellTent_of_mem hr (openCell_subset_cellArc hr hsum i hθ)
  have hlt : ∀ k, k ≠ i → cellTent r k θ < cellGap r := fun k hk =>
    cellTent_lt_of_notMem hr (openCell_disjoint_cellArc hr hsum hk hθ)
  have hgap := cellGap_pos r hr
  by_cases hex : ∃ k ∈ Finset.univ.erase i, 0 < cellTent r k θ
  · obtain ⟨k₀, hk₀mem, hk₀⟩ := hex
    have hk₀i : k₀ ≠ i := (Finset.mem_erase.mp hk₀mem).1
    have hzero : ∀ b ∈ Finset.univ.erase i, b ≠ k₀ → cellTent r b θ ^ 2 = 0 := by
      intro b hbmem hbk₀
      have hbi : b ≠ i := (Finset.mem_erase.mp hbmem).1
      have hnot : ¬(0 < cellTent r b θ ∧ 0 < cellTent r k₀ θ) := by
        rcases Nat.lt_or_ge b.val k₀.val with hor | hor
        · exact cellTent_pair_exclusion hr hsum hbi hk₀i hor hθ
        · have hor' : k₀.val < b.val := by
            rcases Nat.lt_or_ge k₀.val b.val with h | h
            · exact h
            · exact absurd (Fin.ext (by omega : b.val = k₀.val)) hbk₀
          intro hpair
          exact cellTent_pair_exclusion hr hsum hk₀i hbi hor' hθ ⟨hpair.2, hpair.1⟩
      have hb0 : cellTent r b θ = 0 := by
        by_contra hne
        exact hnot ⟨lt_of_le_of_ne (cellTent_nonneg (r := r) b θ) (Ne.symm hne), hk₀⟩
      rw [hb0]
      ring
    rw [Finset.sum_eq_single_of_mem k₀ hk₀mem hzero, hti]
    have := hlt k₀ hk₀i
    nlinarith [cellTent_nonneg (r := r) k₀ θ]
  · push Not at hex
    rw [show ∑ j ∈ Finset.univ.erase i, cellTent r j θ ^ 2 = 0 from
      Finset.sum_eq_zero fun j hj => by
        have h1 := hex j hj
        have h2 := cellTent_nonneg (r := r) j θ
        have h3 : cellTent r j θ = 0 := le_antisymm h1 h2
        rw [h3]
        ring]
    rw [hti]
    positivity

/-! ### The seam: the kiss, and no record -/

omit [NeZero N] in
lemma seamPoint_mem_cellArc (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (i : Fin N) : seamPoint r i ∈ cellArc r i := by
  rw [cellArc_eq_image hr hsum]
  exact ⟨loSum r i, ⟨le_refl _, by linarith [hr i]⟩, rfl⟩

omit [NeZero N] in
lemma coe_one_eq_coe_zero : ((1 : ℝ) : CircleFibre) = ((0 : ℝ) : CircleFibre) := by
  have h1 : ((1 : ℝ) : CircleFibre) = 0 := AddCircle.coe_period (1 : ℝ)
  rw [h1]
  simp

omit [NeZero N] in
/-- Every seam point also sits on its left neighbour's plateau — the kiss.
Needs `N ≥ 2` (with a single cell, the seam point's only cell is its own). -/
lemma seamPoint_mem_left (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (hN : 1 < N) (i : Fin N) :
    ∃ i' : Fin N, i' ≠ i ∧ seamPoint r i ∈ cellArc r i' := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · refine ⟨⟨N - 1, by omega⟩, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · rw [cellArc_eq_image hr hsum]
      have hlast : loSum r ⟨N - 1, by omega⟩ + r ⟨N - 1, by omega⟩ = 1 :=
        loSum_last_add r hsum (by simp; omega)
      refine ⟨1, ⟨by linarith [hr ⟨N - 1, by omega⟩], le_of_eq hlast.symm⟩, ?_⟩
      show ((1 : ℝ) : CircleFibre) = seamPoint r i
      rw [seamPoint, loSum_zero_val r h0, coe_one_eq_coe_zero]
  · refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · rw [cellArc_eq_image hr hsum]
      have hsucc : loSum r i
          = loSum r ⟨i.val - 1, by omega⟩ + r ⟨i.val - 1, by omega⟩ :=
        loSum_succ_val r (by simp; omega)
      exact ⟨loSum r i, ⟨by linarith [hr ⟨i.val - 1, by omega⟩], le_of_eq hsucc⟩, rfl⟩

/-- ★ **No record at any seam point, for any outcome** — the kiss: two tents
sit at the plateau, so no tent strictly dominates. -/
theorem nullSeamGen_seam_no_record (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (hN : 1 < N) (i j : Fin N) :
    (nullSeamGenEvolve hr hsum (seamPoint r i, readyState)).2
      ∉ recordRegion (K := N) j := by
  intro hmem
  rw [nullSeamGenEvolve_ready hr hsum _, tentVec_record_iff hr hsum _ j] at hmem
  have hti : cellTent r i (seamPoint r i) = cellGap r :=
    cellTent_of_mem hr (seamPoint_mem_cellArc hr hsum i)
  obtain ⟨i', hi'ne, hi'mem⟩ := seamPoint_mem_left hr hsum hN i
  have hti' : cellTent r i' (seamPoint r i) = cellGap r :=
    cellTent_of_mem hr hi'mem
  obtain ⟨w, hwj, hw⟩ : ∃ w, w ≠ j ∧ cellTent r w (seamPoint r i) = cellGap r := by
    rcases ne_or_eq i j with hij | rfl
    · exact ⟨i, hij, hti⟩
    · exact ⟨i', hi'ne, hti'⟩
  have hge : cellGap r ^ 2
      ≤ ∑ k ∈ Finset.univ.erase j, cellTent r k (seamPoint r i) ^ 2 := by
    rw [← hw]
    exact Finset.single_le_sum
      (f := fun k => cellTent r k (seamPoint r i) ^ 2)
      (fun _ _ => sq_nonneg _)
      (Finset.mem_erase.mpr ⟨hwj, Finset.mem_univ w⟩)
  have hle : cellTent r j (seamPoint r i) ^ 2 ≤ cellGap r ^ 2 := by
    nlinarith [cellTent_nonneg (r := r) j (seamPoint r i),
      cellTent_le hr j (seamPoint r i)]
  linarith

/-! ### The outcome sets are exactly the open cells -/

/-- Every register point is in an open cell or on the seam. -/
lemma openCell_or_seam (hsum : ∑ i, r i = 1)
    (θ : CircleFibre) :
    (∃ i, θ ∈ openCell r i) ∨ (∃ i, θ = seamPoint r i) := by
  obtain ⟨i, hi⟩ := exists_rep_mem_cell (r := r) hsum θ
  rcases lt_or_eq_of_le hi.2 with hlt | heq
  · exact Or.inl ⟨i, show rep θ ∈ Set.Ioo _ _ from ⟨hi.1, hlt⟩⟩
  · right
    have hθ : θ = ((loSum r i + r i : ℝ) : CircleFibre) := by
      rw [← heq]
      exact (coe_rep θ).symm
    rcases Nat.lt_or_ge (i.val + 1) N with hlt2 | hge2
    · refine ⟨⟨i.val + 1, hlt2⟩, ?_⟩
      rw [hθ, seamPoint,
        loSum_succ_val r (show (⟨i.val + 1, hlt2⟩ : Fin N).val = i.val + 1 from rfl)]
    · have hlast : loSum r i + r i = 1 := loSum_last_add r hsum (by omega)
      refine ⟨⟨0, by omega⟩, ?_⟩
      rw [hθ, hlast, seamPoint, loSum_zero_val r rfl, coe_one_eq_coe_zero]

/-- ★ **The outcome set for record `i` is exactly the open cell `i`.** -/
theorem nullSeamGen_outcome (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (hN : 1 < N) (i : Fin N) :
    {θ | (nullSeamGenEvolve hr hsum (θ, readyState)).2 ∈ recordRegion (K := N) i}
      = openCell r i := by
  ext θ
  constructor
  · intro h
    rcases openCell_or_seam hsum θ with ⟨j, hj⟩ | ⟨j, hj⟩
    · rcases ne_or_eq j i with hji | rfl
      · exfalso
        have hrec := nullSeamGen_landing hr hsum hj
        have hdisj := recordRegion_pairwiseDisjoint (K := N) hji.symm
        exact Set.disjoint_left.mp hdisj h hrec
      · exact hj
    · exfalso
      rw [hj] at h
      exact nullSeamGen_seam_no_record hr hsum hN j i h
  · exact fun h => nullSeamGen_landing hr hsum h

/-- ★ **Exact Born, every cell**: the record-`i` outcome set has measure
exactly `r i`. -/
theorem nullSeamGen_born (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (hN : 1 < N) (i : Fin N) :
    (volume : Measure CircleFibre)
        {θ | (nullSeamGenEvolve hr hsum (θ, readyState)).2
          ∈ recordRegion (K := N) i}
      = ENNReal.ofReal (r i) := by
  rw [nullSeamGen_outcome hr hsum hN i]
  exact volume_openCell hr hsum i

omit [NeZero N] in
/-- ★ **The seam is null** — indeed `N` points. -/
theorem nullSeamGen_seam_null :
    (volume : Measure CircleFibre) (Set.range (seamPoint r)) = 0 := by
  rw [Set.range_eq_iUnion]
  refine measure_iUnion_null fun i => ?_
  refine le_zero_iff.mp ?_
  calc (volume : Measure CircleFibre) {seamPoint r i}
      ≤ volume (Metric.closedBall (seamPoint r i) 0) :=
        measure_mono (by
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Metric.mem_closedBall_self le_rfl)
    _ = 0 := by
        rw [AddCircle.volume_closedBall]
        norm_num

/-! ### ★★ Continuity and measure invariance -/

lemma continuous_tentTotal : Continuous (tentTotal r) :=
  Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ => (continuous_cellTent i).pow 2)

lemma continuous_seamAmp (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (k : Fin (N + 1)) : Continuous fun θ => seamAmp r θ k := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
  · show Continuous fun _ : CircleFibre => (0 : ℝ)
    exact continuous_const
  · show Continuous fun θ => cellTent r k' θ / tentTotal r θ
    exact (continuous_cellTent k').div continuous_tentTotal
      (fun θ => (tentTotal_pos hr hsum θ).ne')

/-- Entrywise continuity of the seam rotation over the register. -/
lemma continuous_seamRotation_entry (hr : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    (a b : Fin (N + 1)) :
    Continuous fun θ : CircleFibre => seamRotation (seamAmp r θ) a b := by
  have hamp := continuous_seamAmp hr hsum
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
  · show Continuous fun θ =>
      ((seamRotationR (seamAmp r θ) 0 0 : ℝ) : ℂ)
    simp only [seamRotationR_zero_zero]
    exact continuous_const
  · show Continuous fun θ =>
      ((seamRotationR (seamAmp r θ) 0 b'.succ : ℝ) : ℂ)
    simp only [seamRotationR_zero_succ]
    exact Complex.continuous_ofReal.comp (hamp b'.succ).neg
  · show Continuous fun θ =>
      ((seamRotationR (seamAmp r θ) a'.succ 0 : ℝ) : ℂ)
    simp only [seamRotationR_succ_zero]
    exact Complex.continuous_ofReal.comp (hamp a'.succ)
  · show Continuous fun θ =>
      ((seamRotationR (seamAmp r θ) a'.succ b'.succ : ℝ) : ℂ)
    simp only [seamRotationR_succ_succ]
    exact Complex.continuous_ofReal.comp
      (continuous_const.sub ((hamp a'.succ).mul (hamp b'.succ)))

/-- The pointer component of the propagator is continuous. -/
theorem continuous_nullSeamGenEvolve_snd (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) :
    Continuous fun y : CircleFibre × Pointer N =>
      nullSeamGenUU hr hsum y.1 • y.2 := by
  have hQ : IsOpenQuotientMap
      (Prod.map (id : CircleFibre → CircleFibre)
        (Projectivization.mk' ℂ :
          {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} → Pointer N)) :=
    IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'
  rw [hQ.isQuotientMap.continuous_iff]
  have hvec : Continuous
      fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
        (Matrix.toEuclideanLin (seamRotation (seamAmp r z.1)) z.2.val
          : EuclideanSpace ℂ (Fin (N + 1))) := by
    show Continuous
      fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
        (WithLp.toLp 2
          ((seamRotation (seamAmp r z.1)) *ᵥ (WithLp.ofLp z.2.val))
          : EuclideanSpace ℂ (Fin (N + 1)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · refine continuous_matrix fun a b => ?_
      exact (continuous_seamRotation_entry hr hsum a b).comp continuous_fst
    · exact (PiLp.continuous_ofLp _ _).comp
        (continuous_subtype_val.comp continuous_snd)
  have hkey : ((fun y : CircleFibre × Pointer N => nullSeamGenUU hr hsum y.1 • y.2)
      ∘ (Prod.map id (Projectivization.mk' ℂ)))
      = fun z : CircleFibre × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
          Projectivization.mk' ℂ
            ⟨Matrix.toEuclideanLin (seamRotation (seamAmp r z.1)) z.2.val,
              toEuclideanLin_unitary_apply_ne_zero
                (nullSeamGenUU hr hsum z.1) z.2.2⟩ := by
    funext z
    show nullSeamGenUU hr hsum z.1 • (Projectivization.mk' ℂ z.2) = _
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
    exact Projectivization.smul_mk_eq_mk_toEuclideanLin _ z.2.2
  rw [hkey]
  exact Projectivization.continuous_mk'.comp (hvec.subtype_mk _)

/-- ★★ **The propagator is continuous on the whole arena.** -/
theorem continuous_nullSeamGenEvolve (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) : Continuous (nullSeamGenEvolve hr hsum) :=
  continuous_fst.prodMk (continuous_nullSeamGenEvolve_snd hr hsum)

/-- The arena's invariant measure: Haar on the register, Fubini–Study on the
pointer (the same product as the two-cell witness's `nullSeamMeasure`). -/
noncomputable def nullSeamGenMeasure (q₀ : Pointer N) :
    Measure (CircleFibre × Pointer N) :=
  (volume : Measure CircleFibre).prod (fubiniStudyMeasure q₀)

instance (q₀ : Pointer N) : IsProbabilityMeasure (nullSeamGenMeasure q₀) := by
  unfold nullSeamGenMeasure
  infer_instance

/-- ★★ **Measure invariance** — a skew product: register conserved, every
register slice acts by an FS-preserving unitary. -/
theorem nullSeamGenEvolve_measurePreserving (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) (q₀ : Pointer N) :
    MeasurePreserving (nullSeamGenEvolve hr hsum)
      (nullSeamGenMeasure q₀) (nullSeamGenMeasure q₀) := by
  unfold nullSeamGenEvolve nullSeamGenMeasure
  exact (MeasurePreserving.id (volume : Measure CircleFibre)).skew_product
    (continuous_nullSeamGenEvolve_snd hr hsum).measurable
    (Filter.Eventually.of_forall fun θ =>
      fubiniStudyMeasure_smul_invariant (nullSeamGenUU hr hsum θ) q₀)

/-! ### ★★ The third horn at every `N`, bundled -/

/-- **The general-`N` third horn**: continuous, measure-preserving dynamics on
`S¹ × ℂℙ^N` whose records from the calibrated ready state are exact and
correct off an `N`-point null seam, with **exact** Born mass `r i` per cell.
The price is unchanged from the two-cell witness: Dirac calibration
(`posMeasure_noRecord_pointer` prices the alternative). -/
structure NullSeamGenClosure (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) (hN : 1 < N) : Prop where
  /-- The propagator is continuous on the whole arena. -/
  continuity : Continuous (nullSeamGenEvolve hr hsum)
  /-- Measure invariance at every Fubini–Study base point. -/
  invariant : ∀ q₀ : Pointer N,
    MeasurePreserving (nullSeamGenEvolve hr hsum)
      (nullSeamGenMeasure q₀) (nullSeamGenMeasure q₀)
  /-- Correct record on every open cell — exactly. -/
  landing : ∀ i : Fin N, ∀ θ ∈ openCell r i,
    (nullSeamGenEvolve hr hsum (θ, readyState)).2 ∈ recordRegion (K := N) i
  /-- No record at any seam point, for any outcome — the kiss. -/
  seam_kiss : ∀ i j : Fin N,
    (nullSeamGenEvolve hr hsum (seamPoint r i, readyState)).2
      ∉ recordRegion (K := N) j
  /-- The seam is null. -/
  seam_null : (volume : Measure CircleFibre) (Set.range (seamPoint r)) = 0
  /-- Exact Born, every outcome. -/
  born : ∀ i : Fin N,
    (volume : Measure CircleFibre)
        {θ | (nullSeamGenEvolve hr hsum (θ, readyState)).2
          ∈ recordRegion (K := N) i}
      = ENNReal.ofReal (r i)

/-- ★★ **The third horn exists at every `N ≥ 2` and every weight vector** —
D3b discharged. -/
theorem nullSeamGenClosure (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    (hsum : ∑ i, r i = 1) (hN : 1 < N) :
    NullSeamGenClosure r hr hsum hN where
  continuity := continuous_nullSeamGenEvolve hr hsum
  invariant := nullSeamGenEvolve_measurePreserving hr hsum
  landing := fun _ _ hθ => nullSeamGen_landing hr hsum hθ
  seam_kiss := nullSeamGen_seam_no_record hr hsum hN
  seam_null := nullSeamGen_seam_null
  born := nullSeamGen_born hr hsum hN

/-- The uniform witness: `N` cells of weight `1/N` each — non-vacuity of the
closure at every `N ≥ 2`. -/
theorem nullSeamGenClosure_uniform (hN : 1 < N) :
    NullSeamGenClosure (fun _ : Fin N => (N : ℝ)⁻¹)
      (fun _ => by positivity)
      (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h0 : (N : ℝ) ≠ 0 := by
          exact_mod_cast NeZero.ne N
        field_simp)
      hN :=
  nullSeamGenClosure _ _ _ hN

end CSD.RecordLayer
