import CsdLean4.LF4.BornRegionUncond

/-!
# LF4: pairwise disjointness of the Born regions, the per-microstate outcome map

**Category:** 3-Local (LF4 Born-from-Kähler-volume engine, outcome-map tranche).

This is **LF5-F** (engine half) of `specs/lf5-plan.md`: the upgrade of the LF5
layer from outcome *statistics* (sums of cell-indicator frequencies) to a
deterministic per-microstate outcome *function*. The owed fact, named as the
gate in `LF5/Capstone.lean`'s docstring and noted owed since the `aeece86`
degenerate-witness commit, is the **pairwise disjointness of the `bornRegion`
cells** — the moment-subdivision is a genuine partition, so a microstate lands
in at most one cell.

## What is delivered

* **Image-level disjointness, unconditional** (any `b` in the closed free
  simplex `0 ≤ b`, `∑ b ≤ 1`): `replaceMap_image_disjoint_replaceMap`
  (free `i` vs free `j`, `i ≠ j`) and `replaceMap_image_disjoint_apexMap`
  (free `i` vs apex). Division-free coordinate arguments.
* `bornRegion_pairwiseDisjoint` — preimages of disjoint sets are disjoint; the
  Born vector `b = ratioN (momentMap [ψ])` is in the closed free simplex for
  every `ψ ≠ 0` (no norm hypothesis).
* `bornRegion_ae_cover` — the cells cover `ℂℙ^M` up to an FS-null set (unit
  `ψ`): `measure_iUnion` over the disjoint measurable family sums to
  `∑ ‖⟨eᵢ,ψ⟩‖² = ‖ψ‖² = 1`.
* `bornOutcome` — the per-microstate outcome map `CPN (M+1) → Option (Fin (M+1))`
  (`some i` on cell `i`, `none` off the union); `bornOutcome_eq_some_iff`,
  `bornOutcome_preimage_some`, measurability, a.e.-totality
  `bornOutcome_ae_isSome`.
* `indicator_iUnion_disjoint` — the indicator of a disjoint finite union is the
  sum of indicators (a thin wrapper of `Set.indicator_biUnion_apply`).

## Honest scope

The cells are the **same** ψ-indexed moment-subdivision cells as the audited
volume engine; nothing is carved. The disjointness is a genuine geometric fact
of the barycentric subdivision at the closed-simplex point `b`. Born values
enter through `bornRegion_fs_measure_uncond` (the FS-volume = Born engine);
`Φ = id` still (D1). This file makes the partition structure formal; it does not
exercise dynamics.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-! ### Image-level pairwise disjointness (closed free simplex, unconditional) -/

/-- **Free vs free disjointness.** For `b` in the closed free simplex
(`0 ≤ b`, `∑ b ≤ 1`) and `i ≠ j`, the `i`-th and `j`-th vertex-replacement cell
images are disjoint. Division-free: from cell-`i` membership `xⱼ·bᵢ − xᵢ·bⱼ =
tⱼ·bᵢ ≥ 0` and cell-`j` membership `xᵢ·bⱼ − xⱼ·bᵢ = t'ᵢ·bⱼ ≥ 0`, adding forces
`bᵢ = bⱼ = 0`, then `xᵢ = bᵢ·tᵢ = 0` contradicts `xᵢ = t'ᵢ > 0`. -/
theorem replaceMap_image_disjoint_replaceMap (b : Fin M → ℝ) (i j : Fin M)
    (hb0 : ∀ k, 0 ≤ b k) (hij : i ≠ j) :
    Disjoint ((replaceMap b i) '' openSimplexFree) ((replaceMap b j) '' openSimplexFree) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, ⟨htpos, _⟩, rfl⟩ ⟨t', ⟨ht'pos, _⟩, hx⟩
  -- `hx : replaceMap b j t' = replaceMap b i t`; read coordinates `i`, `j`
  have hci : (replaceMap b j t') i = (replaceMap b i t) i := congrFun hx i
  have hcj : (replaceMap b j t') j = (replaceMap b i t) j := congrFun hx j
  rw [replaceMap_apply, replaceMap_apply, if_neg hij, if_pos rfl, add_zero] at hci
  rw [replaceMap_apply, replaceMap_apply, if_pos rfl, if_neg (Ne.symm hij), add_zero] at hcj
  -- the shared point's `i` and `j` coordinates, read both ways
  have hi : b i * t i = b i * t' j + t' i := hci.symm
  have hj : b j * t i + t j = b j * t' j := by linarith [hcj]
  -- `tⱼ·bᵢ + t'ᵢ·bⱼ = 0` (`= bᵢ·hj − bⱼ·hi`), both nonneg ⇒ both zero
  have hsum0 : t j * b i + t' i * b j = 0 := by linear_combination b i * hj - b j * hi
  have hbi0 : b i = 0 := by
    nlinarith [hsum0, hb0 i, mul_nonneg (le_of_lt (htpos j)) (hb0 i),
      mul_nonneg (le_of_lt (ht'pos i)) (hb0 j), htpos j, ht'pos i]
  -- with `bᵢ = 0`: cell-`i` gives `xᵢ = 0`, cell-`j` gives `xᵢ = t'ᵢ > 0`
  rw [hbi0, zero_mul, zero_mul, zero_add] at hi
  exact absurd hi.symm (ne_of_gt (ht'pos i))

/-- **Free vs apex disjointness.** For `b` in the closed free simplex, the
`i`-th vertex-replacement cell image and the apex cell image are disjoint.
Division-free: cell-`i` gives `(1−∑x)·bᵢ − xᵢ·(1−∑b) = (1−∑t)·bᵢ ≥ 0`; apex
gives `xᵢ·(1−∑b) − (1−∑x)·bᵢ = t'ᵢ·(1−∑b) ≥ 0`; adding forces `bᵢ = 0` and
`∑b = 1`, then `xᵢ = bᵢ·tᵢ = 0` contradicts `xᵢ = t'ᵢ > 0`. -/
theorem replaceMap_image_disjoint_apexMap (b : Fin M → ℝ) (i : Fin M)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k ≤ 1) :
    Disjoint ((replaceMap b i) '' openSimplexFree)
      ((fun x => apexLin b x + b) '' openSimplexFree) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, ⟨htpos, htsum⟩, rfl⟩ ⟨t', ⟨ht'pos, ht'sum⟩, hx⟩
  -- `hx : (apexLin b t' + b) = replaceMap b i t`
  -- coordinate formula for the apex point and its `i`-th coordinate
  have happ : ∀ k, (apexLin b t' + b) k = t' k + (1 - ∑ j, t' j) * b k := by
    intro k; rw [Pi.add_apply, apexLin_apply]; ring
  have hci : (apexLin b t' + b) i = (replaceMap b i t) i := congrFun hx i
  rw [happ i, replaceMap_apply, if_pos rfl, add_zero] at hci
  -- `xᵢ` both ways
  have hi : b i * t i = t' i + (1 - ∑ j, t' j) * b i := hci.symm
  -- `∑ x` both ways (free cell): `∑ x = ∑t + tᵢ·(∑b − 1)`
  have hxsum_i : ∑ k, (replaceMap b i t) k = (∑ k, t k) + t i * ((∑ k, b k) - 1) := by
    rw [Finset.sum_congr rfl (fun k _ => replaceMap_apply b i t k)]
    have hcompl : ∑ k, (if k = i then (0 : ℝ) else t k) = (∑ k, t k) - t i := by
      have h1 : ∑ k, ((if k = i then (0 : ℝ) else t k) + (if i = k then t k else 0))
          = ∑ k, t k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hk : k = i
        · subst hk; simp
        · rw [if_neg hk, if_neg (Ne.symm hk), add_zero]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i t,
        if_pos (Finset.mem_univ i)] at h1
      linarith
    rw [Finset.sum_add_distrib, hcompl, ← Finset.sum_mul]
    ring
  -- `∑ x` (apex cell): `∑ x = ∑t' + (1−∑t')·∑b`
  have hxsum_a : ∑ k, (apexLin b t' + b) k = (∑ k, t' k) + (1 - ∑ k, t' k) * (∑ k, b k) := by
    simp_rw [happ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- equate the two readings of `∑ x`
  have hsumeq : ∑ k, (apexLin b t' + b) k = ∑ k, (replaceMap b i t) k :=
    Finset.sum_congr rfl (fun k _ => congrFun hx k)
  have hssum : (∑ k, t k) + t i * ((∑ k, b k) - 1)
      = (∑ k, t' k) + (1 - ∑ k, t' k) * (∑ k, b k) := by
    rw [← hxsum_i, ← hsumeq, hxsum_a]
  -- `(1−∑t)·bᵢ + t'ᵢ·(1−∑b) = 0`, both nonneg ⇒ each zero
  have hsum0 : (1 - ∑ k, t k) * b i + t' i * (1 - ∑ k, b k) = 0 := by
    linear_combination ((∑ k, b k) - 1) * hi - b i * hssum
  have hbi0 : b i = 0 := by
    nlinarith [hsum0, hb0 i, mul_nonneg (le_of_lt (sub_pos.mpr htsum)) (hb0 i),
      mul_nonneg (le_of_lt (ht'pos i)) (sub_nonneg.mpr hbsum), sub_pos.mpr htsum]
  -- with `bᵢ = 0`: cell-`i` gives `xᵢ = 0`, apex gives `xᵢ = t'ᵢ > 0`
  simp only [hbi0, zero_mul, mul_zero, add_zero] at hi
  exact absurd hi.symm (ne_of_gt (ht'pos i))

/-! ### Born vector closed-simplex bounds (any `ψ ≠ 0`, no norm) -/

/-- The free Born vector lies in the closed free simplex: each coordinate is
nonnegative. Holds for **every** `ψ ≠ 0` (the moment ratio is a ratio of
nonnegatives); no norm hypothesis. -/
theorem ratioN_momentMap_nonneg (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (k : Fin M) :
    0 ≤ ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k := by
  rw [ratioN]
  exact div_nonneg (momentMap_nonneg _ _)
    (Finset.sum_nonneg fun j _ => momentMap_nonneg _ j)

/-- The free Born vector's coordinates sum to at most one (the dropped apex
weight is nonnegative). Holds for **every** `ψ ≠ 0`; no norm hypothesis. -/
theorem ratioN_momentMap_sum_le_one (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k ≤ 1 := by
  simp only [ratioN]
  simp_rw [momentMap_sum_eq_one (Projectivization.mk ℂ ψ hψ0), div_one]
  have hsplit : ∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j
      = (∑ k : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc k))
        + momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.last M) := Fin.sum_univ_castSucc _
  rw [momentMap_sum_eq_one] at hsplit
  linarith [momentMap_nonneg (Projectivization.mk ℂ ψ hψ0) (Fin.last M)]

/-! ### Pairwise disjointness of the Born regions -/

/-- **The Born regions are pairwise disjoint, every `ψ ≠ 0`.** Preimages of
disjoint sets are disjoint; the `Fin.lastCases` split dispatches to the two
image-level disjointness lemmas, with the Born vector in the closed free simplex
by `ratioN_momentMap_nonneg` / `ratioN_momentMap_sum_le_one`. No norm or
genericity hypothesis. -/
theorem bornRegion_pairwiseDisjoint (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    Pairwise (Function.onFun Disjoint (bornRegion ψ hψ0)) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => ratioN_momentMap_nonneg ψ hψ0 k
  have hbsum : ∑ k, b k ≤ 1 := ratioN_momentMap_sum_le_one ψ hψ0
  -- image-level disjointness, in both index orders, lifted to preimages
  have free_free : ∀ i j : Fin M, i ≠ j →
      Function.onFun Disjoint (bornRegion ψ hψ0) (Fin.castSucc i) (Fin.castSucc j) := by
    intro i j hij
    simp only [Function.onFun, bornRegion, Fin.lastCases_castSucc]
    exact (replaceMap_image_disjoint_replaceMap b i j hb0 hij).preimage _
  have free_apex : ∀ i : Fin M,
      Function.onFun Disjoint (bornRegion ψ hψ0) (Fin.castSucc i) (Fin.last M) := by
    intro i
    simp only [Function.onFun, bornRegion, Fin.lastCases_castSucc, Fin.lastCases_last]
    exact (replaceMap_image_disjoint_apexMap b i hb0 hbsum).preimage _
  intro a c
  induction a using Fin.lastCases with
  | last =>
    induction c using Fin.lastCases with
    | last => intro hac; exact absurd rfl hac
    | cast j => intro _; exact (free_apex j).symm
  | cast i =>
    induction c using Fin.lastCases with
    | last => intro _; exact free_apex i
    | cast j => intro hac; exact free_free i j (fun h => hac (by rw [h]))

/-! ### a.e. coverage (unit `ψ`) -/

/-- Parseval: `∑ᵢ ‖⟨eᵢ, ψ⟩‖² = ‖ψ‖²`. -/
theorem sum_inner_single_sq (ψ : EuclideanSpace ℂ (Fin (M + 1))) :
    ∑ i, ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The FS measure of the union of the Born regions is `1` (unit `ψ`):
`measure_iUnion` over the disjoint measurable family, summing to
`∑ ‖⟨eᵢ,ψ⟩‖² = ‖ψ‖² = 1`. ENNReal-level form. -/
theorem bornRegion_iUnion_fs_measure (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fubiniStudyMeasure p₀ (⋃ i, bornRegion ψ hψ0 i) = 1 := by
  rw [measure_iUnion (fun i j hij => bornRegion_pairwiseDisjoint ψ hψ0 hij)
      (bornRegion_measurable_uncond ψ hψ0)]
  -- each summand's ENNReal value is `ofReal` of the Born weight (nonneg)
  have hval : ∀ i, fubiniStudyMeasure p₀ (bornRegion ψ hψ0 i)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) := by
    intro i
    have h := bornRegion_fs_measure_uncond p₀ ψ hψ0 hψ i
    rw [← h, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hval]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
      ⟨‖ψ‖ ^ 2, by
        rw [← sum_inner_single_sq ψ]
        exact hasSum_fintype _⟩,
    tsum_fintype, sum_inner_single_sq ψ, hψ, one_pow, ENNReal.ofReal_one]

/-- **a.e. coverage:** the complement of the union of the Born regions is
FS-null (unit `ψ`). The cells partition `ℂℙ^M` up to a null set. -/
theorem bornRegion_ae_cover (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fubiniStudyMeasure p₀ (⋃ i, bornRegion ψ hψ0 i)ᶜ = 0 := by
  rw [measure_compl (MeasurableSet.iUnion (bornRegion_measurable_uncond ψ hψ0))
      (measure_ne_top _ _), bornRegion_iUnion_fs_measure p₀ ψ hψ0 hψ, measure_univ,
    tsub_self]

/-! ### The per-microstate outcome map -/

/-- The discrete (`⊤`) measurable space on `Option (Fin n)` — the codomain of the
outcome map. `Option (Fin n)` is finite, hence the discrete σ-algebra is the only
natural choice and every set is measurable. Mathlib provides `Fin.instMeasurableSpace
:= ⊤` but no `Option` instance; this supplies it locally for the outcome-map
measurability statement. -/
instance instMeasurableSpaceOptionFin (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

instance instMeasurableSingletonClassOptionFin (n : ℕ) :
    MeasurableSingletonClass (Option (Fin n)) :=
  ⟨fun _ => trivial⟩

/-- **The per-microstate Born outcome map.** `some i` on cell `i`, `none` off the
union of cells. Total off an FS-null set (`bornOutcome_ae_isSome`), deterministic
(the cell is unique, `bornRegion_pairwiseDisjoint`). The genuine realisation of
the contextual outcome-map slot: the microstate fixes the outcome. -/
noncomputable def bornOutcome (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    CPN (M + 1) → Option (Fin (M + 1)) :=
  fun p =>
    haveI := Classical.propDecidable (∃ i, p ∈ bornRegion ψ hψ0 i)
    if h : ∃ i, p ∈ bornRegion ψ hψ0 i then some h.choose else none

/-- **The outcome map is `some i` iff the microstate is in cell `i`.** The `←`
direction uses uniqueness (`bornRegion_pairwiseDisjoint`); the `→` direction
uses `h.choose_spec` plus uniqueness to pin the chosen index. -/
theorem bornOutcome_eq_some_iff (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (p : CPN (M + 1)) (i : Fin (M + 1)) :
    bornOutcome ψ hψ0 p = some i ↔ p ∈ bornRegion ψ hψ0 i := by
  unfold bornOutcome
  constructor
  · intro h
    split_ifs at h with hex
    -- only the `∃` branch survives (`none = some i` is auto-discharged)
    -- `h.choose ∈ cell h.choose` and `some h.choose = some i` ⇒ `i = h.choose`
    rw [Option.some.injEq] at h
    have hspec := hex.choose_spec
    rw [h] at hspec
    exact hspec
  · intro hp
    have hex : ∃ j, p ∈ bornRegion ψ hψ0 j := ⟨i, hp⟩
    rw [dif_pos hex, Option.some.injEq]
    -- uniqueness: `p ∈ cell hex.choose ∩ cell i` forces `hex.choose = i`
    by_contra hne
    exact Set.disjoint_left.mp (bornRegion_pairwiseDisjoint ψ hψ0 hne) hex.choose_spec hp

/-- Set-level form: the `some i` fibre of the outcome map is exactly cell `i`. -/
theorem bornOutcome_preimage_some (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (i : Fin (M + 1)) :
    bornOutcome ψ hψ0 ⁻¹' {some i} = bornRegion ψ hψ0 i :=
  Set.ext fun p => by
    rw [Set.mem_preimage, Set.mem_singleton_iff, bornOutcome_eq_some_iff]

/-- The `some i` fibres of the outcome map are measurable (immediate from
`bornOutcome_preimage_some` + `bornRegion_measurable_uncond`). -/
theorem bornOutcome_measurableSet_some (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (i : Fin (M + 1)) :
    MeasurableSet (bornOutcome ψ hψ0 ⁻¹' {some i}) := by
  rw [bornOutcome_preimage_some]
  exact bornRegion_measurable_uncond ψ hψ0 i

/-- **The outcome map is measurable.** The codomain `Option (Fin (M+1))` is a
countable measurable space (`⊤` σ-algebra), so measurability reduces to
measurability of every singleton preimage (`measurable_to_countable'`): the
`some i` fibres are cells (measurable); the `none` fibre is the complement of
the union of cells (measurable). -/
theorem bornOutcome_measurable (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) :
    Measurable (bornOutcome ψ hψ0) := by
  refine measurable_to_countable' (fun o => ?_)
  cases o with
  | none =>
    -- the `none` fibre is the complement of the union of cells
    have hpre : bornOutcome ψ hψ0 ⁻¹' {none} = (⋃ i, bornRegion ψ hψ0 i)ᶜ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · rintro h ⟨i, hi⟩
        rw [← bornOutcome_eq_some_iff] at hi
        rw [hi] at h
        exact absurd h (by simp)
      · intro h
        unfold bornOutcome
        rw [dif_neg]
        rintro ⟨i, hi⟩
        exact h ⟨i, hi⟩
    rw [hpre]
    exact (MeasurableSet.iUnion (bornRegion_measurable_uncond ψ hψ0)).compl
  | some i => exact bornOutcome_measurableSet_some ψ hψ0 i

/-- **a.e. totality:** the outcome map is defined (`isSome`) off an FS-null set
(unit `ψ`). The microstate determines an outcome almost surely. -/
theorem bornOutcome_ae_isSome (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ p ∂ fubiniStudyMeasure p₀, (bornOutcome ψ hψ0 p).isSome := by
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (t := (⋃ i, bornRegion ψ hψ0 i)ᶜ) ?_
    (bornRegion_ae_cover p₀ ψ hψ0 hψ)
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion] at hp ⊢
  push_neg
  -- if `p ∈ cell i` then `bornOutcome = some i` is `isSome`, contradiction
  intro i hpi
  apply hp
  rw [← bornOutcome_eq_some_iff ψ hψ0 p i] at hpi
  rw [hpi]
  rfl

/-! ### Indicator-of-disjoint-union bridge -/

/-- **Indicator of a disjoint finite union = sum of indicators.** Thin wrapper
of `Finset.indicator_biUnion_apply` for a pairwise-disjoint family indexed by a
finset. Feeds the union-event outcome-frequency restatements. -/
theorem indicator_iUnion_disjoint {α ι : Type*} (s : Finset ι) (t : ι → Set α)
    (hdisj : (s : Set ι).PairwiseDisjoint t) (f : α → ℝ) (x : α) :
    Set.indicator (⋃ i ∈ s, t i) f x = ∑ i ∈ s, Set.indicator (t i) f x :=
  Finset.indicator_biUnion_apply s t hdisj x

end LF4
end CSD
