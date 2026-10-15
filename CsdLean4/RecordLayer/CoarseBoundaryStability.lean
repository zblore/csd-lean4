/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TwoWingStability
public import CsdLean4.RecordLayer.NullSeamGeneralN

/-!
# Stability that scales with the coarse boundaries

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #138 (out of #131 obligation (2)): the sharpening `TwoWingStability.lean` did not claim.

#103 bounded the microstates a record write relabels by `N · δ`, one boundary band per **fine**
cell, and `TwoWingStability.lean` inherited that bound for the coarse two-wing reading without
improving it. This file proves the bound the coarse reading deserves: **one band per coarse
boundary**, where a coarse boundary is an index `k` whose decoded value differs from that of the
*cyclically* next cell (`IsCoarseBoundary`, `coarseBoundaryCount`).

## The argument

* **Every microstate lies in a basin** (★ `exists_mem_globalBasin`). The rates sum to one, so the
  arcs tile `(0, 1]` exactly, not merely almost everywhere: the `none` value of `fineIndex` and the
  `0` value of `outcomeCode` are never taken. This strengthens `globalBasin_ae_total`.
* **A write of size `δ ≤ 1` moves the representative by `δ`, wrapping at most once**
  (`rep_sigmaShift`): either `rep ↦ rep + δ` or, past the top of the turn, `rep ↦ rep + δ − 1`
  (`rep_add_coe_of_one_lt`, the wrap-around companion of `rep_add_coe`).
* **A coarse relabelling crosses a coarse boundary within `δ`** (★★ `coarseCode_ne_subset`). If
  the microstate sits in cell `i` and the written point in cell `j` with different coarse values,
  then along the cyclic path from `i` to `j` some consecutive pair of cells differs
  (`exists_boundary_between`, a discrete intermediate-value lemma), and the representative lies in
  the last `δ` before that boundary — read cyclically, so the band at a boundary `T` is
  `(T − δ, T] ∪ (T + 1 − δ, 1]` (`cyclicBand`), of epistemic measure at most `δ`
  (★ `measure_cyclicBand_le`).
* Hence ★★★ `measure_coarseCode_ne_le`: the microstates whose coarse reading a write of size
  `δ ≤ 1` changes have epistemic measure at most **`#boundaries · δ`**; uniformly over the horizon
  (★★★ `measure_exists_coarseCode_ne_le`) and under a drift (★★★ `measure_drift_coarseCode_ne_le`).
* `coarseBoundaryCount_le`: the count is at most `N`, so #103's bound is the worst case; and
  ★★ `coarseBoundaryCount_comp_le`: **a decoding that groups adjacent cells into `m` contiguous
  blocks has at most `m` boundaries**, whatever the block values. For the two-wing record this is
  ★★★ `measure_wingCode_ne_le_of_blocks`: a contiguous decoding into the experiment's `m = 4` joint
  outcomes is stable outside a set of measure `4 · δ`, **independent of the Hilbert dimension `N`**.

## Honest scope

* **Writes of at most one turn** (`δ ≤ 1`, `ω · T ≤ 1`). A longer write can wrap several times; the
  bound `#boundaries · δ` is then trivially true for any decoding with a boundary and the
  hypothesis is kept rather than discharged by that remark.
* **Contiguity is a hypothesis on the decoding**, stated as a factorisation `w = v ∘ g` through a
  monotone block map `g : Fin N → Fin m`. The row's worry stands: `LF6.pointerDecode` groups cells
  by the pointer half of an *arbitrary* index equivalence, which need not be contiguous, and for a
  non-contiguous decoding the count can be `N`. Nothing here chooses the equivalence.
* The row's first deliverable, "a write moves a microstate to the next cell or nowhere", is true
  only when the write is shorter than the next cell; the covering lemma above replaces it by the
  statement that holds for every `δ ≤ 1`.
* **The write is the fibre translation `sigmaShift`**, as in #103 and `TwoWingStability.lean`: the
  base and the symplectic partner are fixed; no base motion is composed with this, and this is not
  invariance and contains no mixing claim.

References: `specs/BACKLOG.md` #138, #131 obligation (2), #103;
`RecordLayer/MacrostateStability.lean` (`sigmaShift`, `cellTop`, `edgeBand`, `measure_edgeBand_le`,
`measure_unstableSet_le`), `RecordLayer/TwoWingStability.lean` (`measure_wingCode_ne_le`, the
bound sharpened here), `RecordLayer/TwoWingCoarsening.lean` (`fineIndex`, `wingCode`),
`RecordLayer/CircleFibre.lean` (`rep_add_coe`, `volume_rep_preimage_Ioc`),
`RecordLayer/NullSeamGeneralN.lean` (`loSum_succ_val`, `loSum_last_add`),
`LF6/TwoWingRecord.lean` (`pointerDecode`).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {N : ℕ} {κ : Type*} {Ω₁ Ω₂ : Type*}

/-! ### Every microstate lies in a basin -/

/-- ★ **Every microstate lies in a basin.** The rates sum to one, so the arcs tile the whole turn:
the fine code is never `0`. Strengthens `globalBasin_ae_total`. -/
theorem exists_mem_globalBasin (c : ContextField N) (x : LF4.KSigma N) :
    ∃ i, x ∈ globalBasin c i := by
  classical
  have hsum : ∑ i, c.rate x.1 i = 1 := c.sum_one x.1
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      subst h
      simp at hsum
    · exact h
  have hs0 : 0 < rep x.2.1 := rep_pos _
  have hs1 : rep x.2.1 ≤ 1 := rep_le_one _
  let S := Finset.univ.filter (fun i : Fin N => loSum (c.rate x.1) i < rep x.2.1)
  have h0 : (⟨0, hN⟩ : Fin N) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [loSum_zero_val (c.rate x.1) rfl]
    exact hs0
  obtain ⟨i, hiS, hmax⟩ := S.exists_max_image (fun i : Fin N => (i : ℕ)) ⟨_, h0⟩
  have hi : loSum (c.rate x.1) i < rep x.2.1 := (Finset.mem_filter.1 hiS).2
  refine ⟨i, (mem_globalBasin_iff c i x).2 ⟨hi, ?_⟩⟩
  by_cases hlast : i.val + 1 = N
  · unfold cellTop
    rw [loSum_last_add (c.rate x.1) hsum hlast]
    exact hs1
  · have hlt : i.val + 1 < N := lt_of_le_of_ne i.isLt hlast
    have hj : ¬ loSum (c.rate x.1) ⟨i.val + 1, hlt⟩ < rep x.2.1 := by
      intro hjs
      have := hmax ⟨i.val + 1, hlt⟩ (by simp [S, hjs])
      simp at this
    rw [not_lt, loSum_succ_val (c.rate x.1) (show (⟨i.val + 1, hlt⟩ : Fin N).val = i.val + 1
      from rfl)] at hj
    exact hj

/-- The fine code is never `0`. -/
theorem outcomeCode_ne_zero (c : ContextField N) (x : LF4.KSigma N) : outcomeCode c x ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_mem_globalBasin c x
  rw [(outcomeCode_eq_succ_iff c x i).2 hi]
  exact Fin.succ_ne_zero i

/-- The fine index is never `none`. -/
theorem fineIndex_ne_none (c : ContextField N) (x : LF4.KSigma N) : fineIndex c x ≠ none := by
  intro h
  obtain ⟨i, hi⟩ := exists_mem_globalBasin c x
  exact (fineIndex_eq_none_iff c x).1 h i hi

/-! ### The written representative: forward by `δ`, wrapping at most once -/

/-- **The wrap-around companion of `rep_add_coe`**: when the shifted representative overshoots the
turn by less than one, it drops by exactly `1`. -/
theorem rep_add_coe_of_one_lt {θ : CircleFibre} {δ : ℝ} (h1 : 1 < rep θ + δ)
    (h2 : rep θ + δ ≤ 2) :
    rep (θ + (δ : CircleFibre)) = rep θ + δ - 1 := by
  have hsum : θ + (δ : CircleFibre) = ((rep θ + δ - 1 : ℝ) : CircleFibre) := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, coe_rep, AddCircle.coe_period, sub_zero]
  rw [hsum, rep_coe_of_mem_Ioc ⟨by linarith, by linarith⟩]

/-- **A write of at most one turn moves the representative by `δ`, wrapping at most once.** -/
theorem rep_sigmaShift {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : LF4.KSigma N) :
    (rep x.2.1 + δ ≤ 1 ∧ rep (sigmaShift δ x).2.1 = rep x.2.1 + δ)
      ∨ (1 < rep x.2.1 + δ ∧ rep (sigmaShift δ x).2.1 = rep x.2.1 + δ - 1) := by
  by_cases h : rep x.2.1 + δ ≤ 1
  · exact Or.inl ⟨h, by
      rw [sigmaShift_record]
      exact rep_add_coe ⟨by linarith [rep_pos x.2.1], h⟩⟩
  · have h' : 1 < rep x.2.1 + δ := not_le.mp h
    exact Or.inr ⟨h', by
      rw [sigmaShift_record]
      exact rep_add_coe_of_one_lt h' (by linarith [rep_le_one x.2.1])⟩

/-! ### Cell endpoints -/

/-- The upper endpoint of a cell is non-negative. -/
theorem cellTop_nonneg (c : ContextField N) (k : Fin N) (x : LF4.KSigma N) :
    0 ≤ cellTop c k x :=
  add_nonneg (Finset.sum_nonneg fun j _ => c.nonneg x.1 j) (c.nonneg x.1 k)

/-- Cell tops are monotone in the index. -/
theorem cellTop_mono (c : ContextField N) (x : LF4.KSigma N) {i k : Fin N} (h : i.val ≤ k.val) :
    cellTop c i x ≤ cellTop c k x := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have := loSum_add_le_loSum (c.rate x.1) (c.nonneg x.1) hlt
    unfold cellTop
    linarith [c.nonneg x.1 k]
  · rw [Fin.ext heq]

/-- A cell's top is at most the lower endpoint of every later cell. -/
theorem cellTop_le_loSum_of_lt (c : ContextField N) (x : LF4.KSigma N) {k j : Fin N}
    (h : k.val < j.val) : cellTop c k x ≤ loSum (c.rate x.1) j :=
  loSum_add_le_loSum (c.rate x.1) (c.nonneg x.1) h

/-- The last cell ends at the top of the turn. -/
theorem cellTop_eq_one (c : ContextField N) (x : LF4.KSigma N) {k : Fin N} (h : k.val + 1 = N) :
    cellTop c k x = 1 :=
  loSum_last_add (c.rate x.1) (c.sum_one x.1) h

/-! ### The cyclic successor and the coarse boundaries -/

/-- The cyclic successor of an index: `k + 1`, or `0` after the last. -/
def nextIdx (k : Fin N) : Fin N :=
  if h : k.val + 1 < N then ⟨k.val + 1, h⟩ else ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩

theorem nextIdx_of_lt {k : Fin N} (h : k.val + 1 < N) : nextIdx k = ⟨k.val + 1, h⟩ := by
  unfold nextIdx
  simp [h]

theorem nextIdx_of_last {k : Fin N} (h : k.val + 1 = N) :
    nextIdx k = ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩ := by
  unfold nextIdx
  simp [show ¬ (k.val + 1 < N) by omega]

/-- **A coarse boundary** of a decoding `w`: an index whose value differs from the cyclically next
one. -/
def IsCoarseBoundary (w : Fin N → κ) (k : Fin N) : Prop := w k ≠ w (nextIdx k)

/-- The coarse boundaries of a decoding, as a finite set. -/
def coarseBoundaries (w : Fin N → κ) : Finset (Fin N) :=
  haveI := Classical.decPred (IsCoarseBoundary w)
  Finset.univ.filter (IsCoarseBoundary w)

/-- **The number of coarse boundaries** of a decoding. -/
def coarseBoundaryCount (w : Fin N → κ) : ℕ := (coarseBoundaries w).card

theorem mem_coarseBoundaries {w : Fin N → κ} {k : Fin N} :
    k ∈ coarseBoundaries w ↔ IsCoarseBoundary w k := by
  classical
  simp [coarseBoundaries]

/-- There are at most `N` coarse boundaries: #103's count is the worst case. -/
theorem coarseBoundaryCount_le (w : Fin N → κ) : coarseBoundaryCount w ≤ N := by
  classical
  unfold coarseBoundaryCount coarseBoundaries
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **The discrete intermediate-value lemma**: a sequence that differs between `a` and `b ≥ a`
differs between some consecutive pair in between. -/
theorem exists_ne_succ_of_ne (f : ℕ → κ) {a b : ℕ} (hab : a ≤ b) (h : f a ≠ f b) :
    ∃ k, a ≤ k ∧ k < b ∧ f k ≠ f (k + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd rfl h
  | succ m hm ih =>
      by_cases hfm : f a = f m
      · exact ⟨m, hm, Nat.lt_succ_self m, fun h' => h (hfm.trans h')⟩
      · obtain ⟨k, hk1, hk2, hk3⟩ := ih hfm
        exact ⟨k, hk1, Nat.lt_succ_of_lt hk2, hk3⟩

/-- Between two indices with different values lies a coarse boundary. -/
theorem exists_boundary_between (w : Fin N → κ) {i j : Fin N} (hij : i.val ≤ j.val)
    (h : w i ≠ w j) :
    ∃ k : Fin N, i.val ≤ k.val ∧ k.val < j.val ∧ IsCoarseBoundary w k := by
  classical
  let f : ℕ → κ := fun n => if hn : n < N then w ⟨n, hn⟩ else w i
  have hfi : f i.val = w i := by simp [f, i.isLt]
  have hfj : f j.val = w j := by simp [f, j.isLt]
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_ne_succ_of_ne f hij (by rw [hfi, hfj]; exact h)
  have hkN : k < N := lt_trans hk2 j.isLt
  have hk1N : k + 1 < N := lt_of_le_of_lt hk2 j.isLt
  refine ⟨⟨k, hkN⟩, hk1, hk2, ?_⟩
  unfold IsCoarseBoundary
  rw [nextIdx_of_lt hk1N]
  simpa [f, hkN, hk1N] using hk3

/-! ### The cyclic boundary band -/

/-- The part of a boundary band that wraps past the top of the turn: the representatives within
`δ` of the boundary `T` *through* `1`, i.e. in `(T + 1 − δ, 1]`. -/
def wrapBand (c : ContextField N) (δ : ℝ) (k : Fin N) : Set (LF4.KSigma N) :=
  {x | cellTop c k x + 1 - δ < rep x.2.1}

/-- **The cyclic boundary band** at the top of cell `k`: the representatives within `δ` before the
boundary, read around the circle. -/
def cyclicBand (c : ContextField N) (δ : ℝ) (k : Fin N) : Set (LF4.KSigma N) :=
  edgeBand c δ k ∪ wrapBand c δ k

theorem measurableSet_wrapBand (c : ContextField N) (δ : ℝ) (k : Fin N) :
    MeasurableSet (wrapBand c δ k) :=
  measurableSet_lt (((measurable_cellTop c k).add_const 1).sub_const δ) measurable_repRecord

theorem measurableSet_cyclicBand (c : ContextField N) (δ : ℝ) (k : Fin N) :
    MeasurableSet (cyclicBand c δ k) :=
  (measurableSet_edgeBand c δ k).union (measurableSet_wrapBand c δ k)

/-- A smaller write has a smaller band. -/
theorem cyclicBand_mono (c : ContextField N) {s δ : ℝ} (h : s ≤ δ) (k : Fin N) :
    cyclicBand c s k ⊆ cyclicBand c δ k := by
  rintro x (⟨h1, h2⟩ | h1)
  · exact Or.inl ⟨by linarith, h2⟩
  · exact Or.inr (by simp only [wrapBand, mem_ofPred_eq] at h1 ⊢; linarith)

/-- ★ **The cyclic band is small**: its epistemic measure is at most `δ`, however the band wraps.
The two pieces have measures `min T δ` and `(δ − T)₊`, which sum to `δ`. -/
theorem measure_cyclicBand_le (c : ContextField N) (δ : ℝ) (k : Fin N)
    (p : LF4.CPN N) : epistemicMeasure p (cyclicBand c δ k) ≤ ENNReal.ofReal δ := by
  have hT0 : 0 ≤ loSum (c.rate p) k + c.rate p k :=
    add_nonneg (Finset.sum_nonneg fun j _ => c.nonneg p j) (c.nonneg p k)
  have hT1 : loSum (c.rate p) k + c.rate p k ≤ 1 := c.loSum_le_one p k
  -- the edge slice
  have hE : epistemicMeasure p (edgeBand c δ k)
      = (volume : Measure CircleFibre)
          (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k - δ) (loSum (c.rate p) k + c.rate p k)) := by
    have hmeas := measurableSet_edgeBand c δ k
    rw [epistemicMeasure, Measure.prod_apply hmeas,
      lintegral_dirac' _ (measurable_measure_prodMk_left hmeas)]
    have hslice : Prod.mk p ⁻¹' edgeBand c δ k
        = (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k - δ) (loSum (c.rate p) k + c.rate p k))
          ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
      ext θ
      simp [edgeBand, cellTop, Set.mem_prod]
    rw [hslice, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  -- the wrap slice
  have hW : epistemicMeasure p (wrapBand c δ k)
      = (volume : Measure CircleFibre)
          (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k + 1 - δ) 1) := by
    have hmeas := measurableSet_wrapBand c δ k
    rw [epistemicMeasure, Measure.prod_apply hmeas,
      lintegral_dirac' _ (measurable_measure_prodMk_left hmeas)]
    have hslice : Prod.mk p ⁻¹' wrapBand c δ k
        = (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k + 1 - δ) 1)
          ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
      ext θ
      simp only [wrapBand, cellTop, mem_preimage, mem_ofPred_eq, Set.mem_prod, mem_Ioc, mem_univ,
        and_true]
      exact ⟨fun h => ⟨h, rep_le_one _⟩, fun h => h.1⟩
    rw [hslice, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  -- the edge piece measures `min T δ`
  have hE' : (volume : Measure CircleFibre)
      (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k - δ) (loSum (c.rate p) k + c.rate p k))
        ≤ ENNReal.ofReal (min (loSum (c.rate p) k + c.rate p k) δ) := by
    have hclip : rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k - δ) (loSum (c.rate p) k + c.rate p k)
        = rep ⁻¹' Ioc (max 0 (loSum (c.rate p) k + c.rate p k - δ))
            (loSum (c.rate p) k + c.rate p k) := by
      ext θ
      simp only [mem_preimage, mem_Ioc, max_lt_iff]
      exact ⟨fun h => ⟨⟨rep_pos θ, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    rw [hclip, volume_rep_preimage_Ioc (le_max_left _ _) hT1]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rcases le_total δ (loSum (c.rate p) k + c.rate p k) with h | h
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
    · rw [max_eq_left (by linarith), min_eq_left h]; ring
  -- the wrap piece measures at most `δ − T`
  have hW' : (volume : Measure CircleFibre)
      (rep ⁻¹' Ioc (loSum (c.rate p) k + c.rate p k + 1 - δ) 1)
        ≤ ENNReal.ofReal (δ - (loSum (c.rate p) k + c.rate p k)) := by
    have h := volume_rep_preimage_Ioc_le (loSum (c.rate p) k + c.rate p k + 1 - δ) 1
    rwa [show (1 : ℝ) - (loSum (c.rate p) k + c.rate p k + 1 - δ)
      = δ - (loSum (c.rate p) k + c.rate p k) from by ring] at h
  -- assemble
  calc epistemicMeasure p (cyclicBand c δ k)
      ≤ epistemicMeasure p (edgeBand c δ k) + epistemicMeasure p (wrapBand c δ k) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (min (loSum (c.rate p) k + c.rate p k) δ)
          + ENNReal.ofReal (δ - (loSum (c.rate p) k + c.rate p k)) := by
        rw [hE, hW]; exact add_le_add hE' hW'
    _ = ENNReal.ofReal δ := by
        rcases le_total δ (loSum (c.rate p) k + c.rate p k) with h | h
        · rw [min_eq_right h,
            ENNReal.ofReal_of_nonpos (show δ - (loSum (c.rate p) k + c.rate p k) ≤ 0 by linarith),
            add_zero]
        · rw [min_eq_left h, ← ENNReal.ofReal_add hT0 (by linarith)]
          congr 1
          ring

/-! ### A coarse relabelling crosses a coarse boundary within `δ` -/

/-- **The coarse code** of a microstate under a decoding `u`: the fine index, decoded. The two-wing
code `wingCode` is this with `u = w`. -/
def coarseCode (c : ContextField N) (u : Fin N → κ) (x : LF4.KSigma N) : Option κ :=
  (fineIndex c x).map u

theorem wingCode_eq_coarseCode (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) :
    wingCode c w = coarseCode c w := rfl

theorem coarseCode_eq_some (c : ContextField N) (u : Fin N → κ) {x : LF4.KSigma N} {i : Fin N}
    (hx : x ∈ globalBasin c i) : coarseCode c u x = some (u i) := by
  simp [coarseCode, (fineIndex_eq_some_iff c x i).2 hx]

/-- ★★ **A write that changes the coarse reading puts the microstate in a cyclic band at a coarse
boundary.** Along the cyclic path from the microstate's cell to the written point's cell some
consecutive pair of cells decodes differently, and the representative lies within `δ` before that
boundary, read around the circle. -/
theorem coarseCode_ne_subset (c : ContextField N) (u : Fin N → κ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    {x : LF4.KSigma N | coarseCode c u (sigmaShift δ x) ≠ coarseCode c u x}
      ⊆ ⋃ k ∈ coarseBoundaries u, cyclicBand c δ k := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_mem_globalBasin c x
  obtain ⟨j, hj⟩ := exists_mem_globalBasin c (sigmaShift δ x)
  have hne : u i ≠ u j := by
    intro h
    apply hx
    rw [coarseCode_eq_some c u hj, coarseCode_eq_some c u hi, h]
  have hr : ∀ l, 0 ≤ c.rate x.1 l := c.nonneg x.1
  obtain ⟨hi1, hi2⟩ := (mem_globalBasin_iff c i x).1 hi
  obtain ⟨hj1, hj2⟩ := (mem_globalBasin_iff c j (sigmaShift δ x)).1 hj
  simp only [sigmaShift_fst, cellTop_sigmaShift] at hj1 hj2
  rw [mem_iUnion₂]
  rcases rep_sigmaShift hδ0 hδ1 x with ⟨_, hrep⟩ | ⟨hgt, hrep⟩
  · -- no wrap: the written representative is `rep + δ`, so `j ≥ i`
    rw [hrep] at hj1 hj2
    have hij : i.val ≤ j.val := by
      by_contra hlt
      have hlt' : j.val < i.val := not_le.mp hlt
      have := loSum_add_le_loSum (c.rate x.1) hr hlt'
      unfold cellTop at hj2
      linarith
    obtain ⟨k, hik, hkj, hk⟩ := exists_boundary_between u hij hne
    refine ⟨k, mem_coarseBoundaries.2 hk, Or.inl ⟨?_, ?_⟩⟩
    · have := cellTop_le_loSum_of_lt c x hkj
      linarith
    · linarith [cellTop_mono c x hik]
  · -- wrap: the written representative is `rep + δ − 1`
    rw [hrep] at hj1 hj2
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hlastN : (N - 1) + 1 = N := Nat.sub_add_cancel hN
    by_cases h1 : u i = u ⟨N - 1, Nat.sub_lt hN one_pos⟩
    · by_cases h2 : u ⟨N - 1, Nat.sub_lt hN one_pos⟩ = u ⟨0, hN⟩
      · -- the boundary lies between cell `0` and cell `j`
        have hne0 : u ⟨0, hN⟩ ≠ u j := by rw [← h2, ← h1]; exact hne
        obtain ⟨k, _, hkj, hk⟩ := exists_boundary_between u (Nat.zero_le _) hne0
        refine ⟨k, mem_coarseBoundaries.2 hk, Or.inr ?_⟩
        show cellTop c k x + 1 - δ < rep x.2.1
        have := cellTop_le_loSum_of_lt c x hkj
        linarith
      · -- the boundary is the top of the turn
        refine ⟨⟨N - 1, Nat.sub_lt hN one_pos⟩, mem_coarseBoundaries.2 ?_, Or.inl ⟨?_, ?_⟩⟩
        · show u _ ≠ u (nextIdx _)
          rw [nextIdx_of_last hlastN]
          exact h2
        · rw [cellTop_eq_one c x hlastN]
          linarith
        · rw [cellTop_eq_one c x hlastN]
          exact rep_le_one _
    · -- the boundary lies between cell `i` and the last cell
      have hil : i.val ≤ N - 1 := Nat.le_sub_one_of_lt i.isLt
      obtain ⟨k, hik, _, hk⟩ := exists_boundary_between u hil h1
      refine ⟨k, mem_coarseBoundaries.2 hk, Or.inl ⟨?_, ?_⟩⟩
      · have := cellTop_le_one c k x
        linarith
      · linarith [cellTop_mono c x hik]

/-! ### ★★★ The bounds -/

/-- ★★★ **Stability that scales with the coarse boundaries.** The microstates whose coarse reading a
write of size `δ ≤ 1` changes have epistemic measure at most `#boundaries · δ`. -/
theorem measure_coarseCode_ne_le (c : ContextField N) (u : Fin N → κ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (p : LF4.CPN N) :
    epistemicMeasure p {x | coarseCode c u (sigmaShift δ x) ≠ coarseCode c u x}
      ≤ (coarseBoundaryCount u : ENNReal) * ENNReal.ofReal δ := by
  calc epistemicMeasure p {x | coarseCode c u (sigmaShift δ x) ≠ coarseCode c u x}
      ≤ epistemicMeasure p (⋃ k ∈ coarseBoundaries u, cyclicBand c δ k) :=
        measure_mono (coarseCode_ne_subset c u hδ0 hδ1)
    _ ≤ ∑ k ∈ coarseBoundaries u, epistemicMeasure p (cyclicBand c δ k) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ coarseBoundaries u, ENNReal.ofReal δ :=
        Finset.sum_le_sum fun k _ => measure_cyclicBand_le c δ k p
    _ = (coarseBoundaryCount u : ENNReal) * ENNReal.ofReal δ := by
        simp [Finset.sum_const, nsmul_eq_mul, coarseBoundaryCount]

/-- ★★★ **One exceptional set serves the whole horizon**: a smaller write has a smaller band. -/
theorem measure_exists_coarseCode_ne_le (c : ContextField N) (u : Fin N → κ) {δ : ℝ}
    (hδ1 : δ ≤ 1) (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ s ∈ Icc (0 : ℝ) δ, coarseCode c u (sigmaShift s x) ≠ coarseCode c u x}
      ≤ (coarseBoundaryCount u : ENNReal) * ENNReal.ofReal δ := by
  have hsub : {x : LF4.KSigma N | ∃ s ∈ Icc (0 : ℝ) δ,
      coarseCode c u (sigmaShift s x) ≠ coarseCode c u x}
        ⊆ ⋃ k ∈ coarseBoundaries u, cyclicBand c δ k := by
    intro x hx
    obtain ⟨s, hs, hne⟩ := hx
    have h := coarseCode_ne_subset c u hs.1 (le_trans hs.2 hδ1) hne
    rw [mem_iUnion₂] at h ⊢
    obtain ⟨k, hk, hxk⟩ := h
    exact ⟨k, hk, cyclicBand_mono c hs.2 k hxk⟩
  calc epistemicMeasure p
        {x | ∃ s ∈ Icc (0 : ℝ) δ, coarseCode c u (sigmaShift s x) ≠ coarseCode c u x}
      ≤ epistemicMeasure p (⋃ k ∈ coarseBoundaries u, cyclicBand c δ k) := measure_mono hsub
    _ ≤ ∑ k ∈ coarseBoundaries u, epistemicMeasure p (cyclicBand c δ k) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ coarseBoundaries u, ENNReal.ofReal δ :=
        Finset.sum_le_sum fun k _ => measure_cyclicBand_le c δ k p
    _ = (coarseBoundaryCount u : ENNReal) * ENNReal.ofReal δ := by
        simp [Finset.sum_const, nsmul_eq_mul, coarseBoundaryCount]

/-- ★★★ **Persistence over a horizon, scaling with the coarse boundaries.** Under a drift of the
record coordinate at rate `ω` for a total of at most one turn, the coarse reading survives all of
`[0, T]` outside a set of measure `#boundaries · ω · T`. -/
theorem measure_drift_coarseCode_ne_le (c : ContextField N) (u : Fin N → κ) {ω T : ℝ}
    (hω : 0 ≤ ω) (hωT : ω * T ≤ 1) (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ t ∈ Icc (0 : ℝ) T, coarseCode c u (sigmaShift (ω * t) x) ≠ coarseCode c u x}
      ≤ (coarseBoundaryCount u : ENNReal) * ENNReal.ofReal (ω * T) := by
  refine le_trans (measure_mono ?_) (measure_exists_coarseCode_ne_le c u hωT p)
  intro x hx
  obtain ⟨t, ht, hne⟩ := hx
  exact ⟨ω * t, ⟨mul_nonneg hω ht.1, mul_le_mul_of_nonneg_left ht.2 hω⟩, hne⟩

/-! ### Contiguous decodings have few boundaries -/

/-- Under a monotone block map, the images of the cyclic successors of two distinct boundaries
differ: strictly increasing values between non-wrapping boundaries, and the wrap boundary's
successor image `g 0` lies below every other successor image. -/
theorem nextIdx_image_ne {m : ℕ} {g : Fin N → Fin m} (hg : Monotone g) {k k' : Fin N}
    (hk : g k ≠ g (nextIdx k)) (hk' : g k' ≠ g (nextIdx k')) (hlt : k.val < k'.val) :
    g (nextIdx k) ≠ g (nextIdx k') := by
  have hkN : k.val + 1 < N := lt_of_le_of_lt hlt k'.isLt
  rw [nextIdx_of_lt hkN] at hk ⊢
  have hk_lt : g k < g ⟨k.val + 1, hkN⟩ :=
    lt_of_le_of_ne (hg (Fin.le_iff_val_le_val.2 (Nat.le_succ _))) hk
  by_cases hk'N : k'.val + 1 < N
  · rw [nextIdx_of_lt hk'N] at hk' ⊢
    have h1 : g ⟨k.val + 1, hkN⟩ ≤ g k' := hg (Fin.le_iff_val_le_val.2 hlt)
    have h2 : g k' < g ⟨k'.val + 1, hk'N⟩ :=
      lt_of_le_of_ne (hg (Fin.le_iff_val_le_val.2 (Nat.le_succ _))) hk'
    exact ne_of_lt (lt_of_le_of_lt h1 h2)
  · have hlast : k'.val + 1 = N := by have := k'.isLt; omega
    rw [nextIdx_of_last hlast]
    have h0 : g ⟨0, lt_of_le_of_lt (Nat.zero_le _) k'.isLt⟩ ≤ g k :=
      hg (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
    exact ne_of_gt (lt_of_le_of_lt h0 hk_lt)

/-- ★★ **A decoding that groups adjacent cells into `m` contiguous blocks has at most `m` coarse
boundaries**, whatever values the blocks carry. The successor image is injective on the
boundaries. -/
theorem coarseBoundaryCount_comp_le {m : ℕ} (v : Fin m → κ) (g : Fin N → Fin m)
    (hg : Monotone g) : coarseBoundaryCount (v ∘ g) ≤ m := by
  classical
  have hg_of : ∀ {k : Fin N}, IsCoarseBoundary (v ∘ g) k → g k ≠ g (nextIdx k) :=
    fun hb h => hb (congrArg v h)
  unfold coarseBoundaryCount
  calc (coarseBoundaries (v ∘ g)).card
      ≤ (Finset.univ : Finset (Fin m)).card := by
        refine Finset.card_le_card_of_injOn (fun k => g (nextIdx k))
          (fun _ _ => Finset.mem_univ _) ?_
        intro k hk k' hk' heq
        have hbk := hg_of (mem_coarseBoundaries.1 (Finset.mem_coe.1 hk))
        have hbk' := hg_of (mem_coarseBoundaries.1 (Finset.mem_coe.1 hk'))
        by_contra hne
        rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
        · exact nextIdx_image_ne hg hbk hbk' h heq
        · exact nextIdx_image_ne hg hbk' hbk h heq.symm
    _ = m := by simp

/-- ★★★ **The two-wing record under a contiguous decoding is stable in proportion to its outcome
count, not the Hilbert dimension.** If the decoding groups adjacent cells into `m` blocks, the
microstates whose two-wing reading a write of size `δ ≤ 1` changes have epistemic measure at most
`m · δ`. For the experiment's four joint outcomes, `m = 4`, whatever `N` is. -/
theorem measure_wingCode_ne_le_of_blocks (c : ContextField N) {m : ℕ} (g : Fin N → Fin m)
    (hg : Monotone g) (v : Fin m → Ω₁ × Ω₂) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : LF4.CPN N) :
    epistemicMeasure p {x | wingCode c (v ∘ g) (sigmaShift δ x) ≠ wingCode c (v ∘ g) x}
      ≤ (m : ENNReal) * ENNReal.ofReal δ := by
  rw [wingCode_eq_coarseCode]
  refine le_trans (measure_coarseCode_ne_le c (v ∘ g) hδ0 hδ1 p) ?_
  exact mul_le_mul' (by exact_mod_cast coarseBoundaryCount_comp_le v g hg) le_rfl

/-- ★★★ **Persistence of the two-wing record over a horizon, in proportion to the outcome
count.** -/
theorem measure_drift_wingCode_ne_le_of_blocks (c : ContextField N) {m : ℕ} (g : Fin N → Fin m)
    (hg : Monotone g) (v : Fin m → Ω₁ × Ω₂) {ω T : ℝ} (hω : 0 ≤ ω)
    (hωT : ω * T ≤ 1) (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ t ∈ Icc (0 : ℝ) T,
          wingCode c (v ∘ g) (sigmaShift (ω * t) x) ≠ wingCode c (v ∘ g) x}
      ≤ (m : ENNReal) * ENNReal.ofReal (ω * T) := by
  rw [wingCode_eq_coarseCode]
  refine le_trans (measure_drift_coarseCode_ne_le c (v ∘ g) hω hωT p) ?_
  exact mul_le_mul' (by exact_mod_cast coarseBoundaryCount_comp_le v g hg) le_rfl

end CSD.RecordLayer

end

end
