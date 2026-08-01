/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Piecewise measure-preserving maps, and coordinate swaps with a `pi` factor

**Category:** 1-Mathlib (CSD-free upstream candidates).

Three reusable measure lemmas the record layer's swap witness needs, stated with no CSD content:

* `measurePreserving_of_partition` — a map agreeing on each piece of a countable measurable
  partition with a measure-preserving map that fixes that piece (as a preimage) is itself
  measure-preserving. The natural tool for *piecewise-defined* dynamics such as record-triggered
  interactions.
* `Measure.map_eval_pi'` — the pushforward of a finite product of probability measures under a
  coordinate evaluation is that coordinate's measure.
* `measurePreserving_swapSlot` — exchanging an external factor with one coordinate of a `pi` factor
  (all factors carrying the same measure) preserves the product measure. The map
  `(s, a) ↦ (a j, update a j s)` is an involutive measurable map of `α × (ι → α)`, proved
  measure-preserving by conjugating through `piEquivPiSubtypeProd (· = j)`: the `pi` factor splits
  as (slot `j`) × (the rest) and the swap becomes `Prod.swap` on the first two factors.

## Provenance

Staged as upstream Mathlib material; no `CsdLean4`-namespace content.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

/-- **A map defined piecewise on a countable measurable partition is measurable**, when each piece's
map is. Companion to `measurePreserving_of_partition`. -/
theorem measurable_of_partition
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Countable ι]
    {A : ι → Set X} (hAmeas : ∀ k, MeasurableSet (A k)) (hAcover : (⋃ k, A k) = univ)
    {T : X → X} {Tk : ι → X → X} (hTk : ∀ k, Measurable (Tk k))
    (hagree : ∀ k, ∀ x ∈ A k, T x = Tk k x) :
    Measurable T := by
  intro S hS
  have hpre : T ⁻¹' S = ⋃ k, (A k ∩ (Tk k) ⁻¹' S) := by
    ext x
    constructor
    · intro hx
      have hxk : x ∈ ⋃ k, A k := hAcover ▸ Set.mem_univ x
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxk
      refine Set.mem_iUnion.mpr ⟨k, hk, ?_⟩
      show Tk k x ∈ S
      rw [← hagree k x hk]
      exact hx
    · intro hx
      obtain ⟨k, hk, hTx⟩ := Set.mem_iUnion.mp hx
      show T x ∈ S
      rw [hagree k x hk]
      exact hTx
  rw [hpre]
  exact MeasurableSet.iUnion fun k => (hAmeas k).inter (hTk k hS)

/-- **A piecewise measure-preserving map is measure-preserving.** If `{A k}` is a countable
measurable partition, each `T k` preserves `μ` and fixes its own piece as a preimage
(`T k ⁻¹' A k = A k`), and `T` agrees with `T k` on `A k`, then `T` preserves `μ`. -/
theorem measurePreserving_of_partition
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Countable ι]
    {A : ι → Set X} (hAmeas : ∀ k, MeasurableSet (A k))
    (hAdisj : Pairwise (Function.onFun Disjoint A)) (hAcover : (⋃ k, A k) = univ)
    {T : X → X} (hTmeas : Measurable T)
    {Tk : ι → X → X} (hTk : ∀ k, MeasurePreserving (Tk k) μ μ)
    (hagree : ∀ k, ∀ x ∈ A k, T x = Tk k x)
    (hfix : ∀ k, (Tk k) ⁻¹' (A k) = A k) :
    MeasurePreserving T μ μ := by
  refine ⟨hTmeas, ?_⟩
  ext S hS
  rw [Measure.map_apply hTmeas hS]
  -- Decompose both sides over the partition.
  have hdecomp : ∀ (V : Set X), MeasurableSet V → μ V = ∑' k, μ (V ∩ A k) := by
    intro V hV
    calc μ V = μ (⋃ k, V ∩ A k) := by rw [← Set.inter_iUnion, hAcover, Set.inter_univ]
      _ = ∑' k, μ (V ∩ A k) :=
          measure_iUnion (fun i j hij =>
            ((hAdisj hij).mono Set.inter_subset_right Set.inter_subset_right))
            (fun k => hV.inter (hAmeas k))
  rw [hdecomp _ (hTmeas hS), hdecomp _ hS]
  congr 1
  funext k
  -- On the piece `A k`, `T` agrees with `T k`, and `T k` fixes the piece.
  have hpiece : T ⁻¹' S ∩ A k = (Tk k) ⁻¹' (S ∩ A k) := by
    rw [Set.preimage_inter, ← hfix k]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hfix k]
    exact and_congr_left fun hx => by rw [hagree k x hx]
  rw [hpiece, (hTk k).measure_preimage ((hS.inter (hAmeas k)).nullMeasurableSet)]

/-- **Evaluation pushes a finite product of probability measures to its factor.** -/
theorem Measure.map_eval_pi'
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    Measure.map (Function.eval i) (Measure.pi μ) = μ i := by
  ext S hS
  rw [Measure.map_apply (measurable_pi_apply i) hS, Set.eval_preimage, Measure.pi_pi]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Function.update_of_ne hj]) (by simp)]
  simp

/-- The slot-swap map `(s, a) ↦ (a j, update a j s)` on `α × (ι → α)`. An involution. -/
def swapSlot {α : Type*} {ι : Type*} [DecidableEq ι] (j : ι) :
    α × (ι → α) → α × (ι → α) :=
  fun x => (x.2 j, Function.update x.2 j x.1)

theorem swapSlot_involutive {α ι : Type*} [DecidableEq ι] (j : ι) :
    Function.Involutive (swapSlot (α := α) j) := by
  intro x
  simp [swapSlot, Function.update_eq_self]

theorem measurable_swapSlot {α ι : Type*} [MeasurableSpace α] [DecidableEq ι] (j : ι) :
    Measurable (swapSlot (α := α) (ι := ι) j) := by
  refine Measurable.prodMk ((measurable_pi_apply j).comp measurable_snd) ?_
  exact measurable_update'.comp (measurable_snd.prodMk measurable_fst)

/-- Inserting a value back into its removed slot is `Function.update`. -/
theorem Fin.insertNth_removeNth_eq_update {n : ℕ} {α : Type*} (j : Fin (n + 1))
    (a : Fin (n + 1) → α) (s : α) :
    j.insertNth s (fun k => a (j.succAbove k)) = Function.update a j s := by
  have h : (fun k => a (j.succAbove k)) = j.removeNth a := rfl
  rw [h]
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne hij]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk, Fin.insertNth_apply_succAbove]
    simp [Fin.removeNth]

/-- **Swapping an external factor with one `pi` coordinate preserves the product measure**, when
every factor carries the same measure. Stated for `Fin K` (the record layer's index type); proved by
splitting the `pi` factor at the slot with `piFinSuccAbove`, under which the swap becomes
`Prod.swap` on the first two factors. -/
theorem measurePreserving_swapSlot
    {α : Type*} [MeasurableSpace α] {K : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (j : Fin K) :
    MeasurePreserving (swapSlot (α := α) (ι := Fin K) j)
      (μ.prod (Measure.pi fun _ => μ)) (μ.prod (Measure.pi fun _ => μ)) := by
  classical
  match K, j with
  | (n + 1), j =>
    -- Split the `pi` factor at the slot.
    have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j
    have hA := (MeasurePreserving.id μ).prod hsplit
    have hM : MeasurePreserving
        (fun x : α × (α × (Fin n → α)) => (x.2.1, (x.1, x.2.2)))
        (μ.prod (μ.prod (Measure.pi fun _ : Fin n => μ)))
        (μ.prod (μ.prod (Measure.pi fun _ : Fin n => μ))) := by
      have h1 := (measurePreserving_prodAssoc μ μ
        (Measure.pi fun _ : Fin n => μ)).symm
        (MeasurableEquiv.prodAssoc (α := α) (β := α) (γ := (Fin n → α)))
      have h2 := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).prod
        (MeasurePreserving.id (Measure.pi fun _ : Fin n => μ))
      have h3 := measurePreserving_prodAssoc μ μ (Measure.pi fun _ : Fin n => μ)
      have := h3.comp (h2.comp h1)
      convert this using 1
      funext x
      rfl
    have hE := (MeasurePreserving.id μ).prod
      (hsplit.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j))
    have htot := hE.comp (hM.comp hA)
    refine ⟨measurable_swapSlot j, ?_⟩
    have hfun : swapSlot (α := α) (ι := Fin (n + 1)) j
        = (Prod.map (id : α → α)
            ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm)
          ∘ (fun x : α × (α × (Fin n → α)) => (x.2.1, (x.1, x.2.2)))
          ∘ (Prod.map (id : α → α)
              ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j)) := by
      funext x
      obtain ⟨s, a⟩ := x
      show (a j, Function.update a j s) = (a j,
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm
          (s, fun k => a (j.succAbove k)))
      congr 1
      show Function.update a j s
        = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm
            (s, fun k => a (j.succAbove k))
      rw [← Fin.insertNth_removeNth_eq_update j a s]
      rfl
    rw [hfun]
    exact htot.map_eq

end MeasureTheory
