/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.InformationTheory.KlDivArrow
public import CsdLean4.Mathlib.InformationTheory.FiniteEntropy

/-!
# The coarse-grained arrow, for an arbitrary finite coarse-graining

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #18 / `R-019`, brick (a).

#109 proved an H-theorem for one coarse-graining — the record string on `Σ` — and the proof used
nothing about records beyond *measurability into a finite type*. This file is that proof with the
vocabulary abstracted: a probability measure `π` on `α`, a finite `β`, a measurable `q : α → β`, and
a `π`-preserving `F : α → α`.

* `coarseLaw π q = π.map q` — the coarse-grained law;
* `coarseStep`/`coarseKernel` — the **induced macro dynamics**: from a cell `v`, condition `π` on
  that cell, push forward by `F`, and read off the cell. Null cells get `dirac`, so the kernel is
  Markov on the nose (`isMarkovKernel_coarseKernel`);
* ★★★ `comp_coarseLaw` — one step of the macro dynamics is the pushforward along `q ∘ F`;
* ★★★ `comp_coarseLaw_of_measurePreserving` — **invariance of the fine measure makes the coarse law
  stationary.** Nothing is chosen: the reference law the divergence is measured from is the
  coarse-grained law itself;
* ★★★ `antitone_klDiv_coarseLaw` — **the coarse-grained H-theorem.** Along the induced macro
  dynamics, every macro law's relative entropy from the coarse-grained law is non-increasing.
* ★★ `monotone_measureEntropy_coarseLaw` — the entropy form, when the cells carry equal weight.

## What this is and is not

⚠️ **The arrow is for the induced macro chain, not for coarse-graining the fine orbit.** The
statement is that iterating `coarseKernel` decreases divergence from the stationary law. It is *not*
that `klDiv (coarseLaw (π.map F^[n]) q) (coarseLaw π q)` decreases — for a measure-preserving `F`
that quantity is constant, by the data-processing inequality in both directions, and no theorem can
make it decrease. The Markov property is the content of the coarse-graining step, which is why
`coarseStep` is a *definition* here and not a hypothesis.

⚠️ **Monotone is not convergent.** Nothing here says the divergence tends to `0`, and nothing here
depends on the geometry of the cells — the H-theorem holds for *any* finite measurable
coarse-graining, however coarse or lopsided. A rate, and hence relaxation, is where the cell size
enters, and that half of the fibre relaxation H-theorem is open (`RESIDUE(R-019)`).

References: `KlDivArrow.lean` (#109, `klDiv_comp_le_of_stationary`, `Measure.compIterate`),
`FiniteEntropy.lean` (#110), `RecordLayer/MacrostateArrow.lean` (#109's record instance, which this
generalises); `specs/BACKLOG.md` #18, #109, #110; `specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### The coarse-grained law and the induced dynamics -/

/-- The coarse-grained law: the distribution of the cell index. -/
noncomputable def coarseLaw (π : Measure α) (q : α → β) : Measure β := π.map q

theorem coarseLaw_apply (π : Measure α) {q : α → β} (hq : Measurable q) {s : Set β}
    (hs : MeasurableSet s) : coarseLaw π q s = π (q ⁻¹' s) := by
  rw [coarseLaw, Measure.map_apply hq hs]

theorem isProbabilityMeasure_coarseLaw (π : Measure α) [IsProbabilityMeasure π] {q : α → β}
    (hq : Measurable q) : IsProbabilityMeasure (coarseLaw π q) :=
  Measure.isProbabilityMeasure_map (μ := π) hq.aemeasurable

variable [DiscreteMeasurableSpace β]

/-- **One step of the induced macro dynamics.** From cell `v`: condition on that cell, evolve by `F`,
read the cell. A null cell is sent to `dirac v`, which keeps the kernel Markov without affecting any
statement about `coarseLaw`. -/
noncomputable def coarseStep (π : Measure α) (q : α → β) (F : α → α) (v : β) : Measure β :=
  if π (q ⁻¹' {v}) = 0 then Measure.dirac v else (π[|q ⁻¹' {v}]).map (fun x => q (F x))

/-- The induced macro kernel. Measurability is free: the cell type is finite and discrete. -/
noncomputable def coarseKernel (π : Measure α) (q : α → β) (F : α → α) : Kernel β β :=
  ⟨coarseStep π q F, Measurable.of_discrete⟩

@[simp] theorem coarseKernel_apply (π : Measure α) (q : α → β) (F : α → α) (v : β) :
    coarseKernel π q F v = coarseStep π q F v := rfl

theorem isMarkovKernel_coarseKernel (π : Measure α) [IsProbabilityMeasure π] {q : α → β}
    (hq : Measurable q) {F : α → α} (hF : Measurable F) :
    IsMarkovKernel (coarseKernel π q F) := by
  refine ⟨fun v => ?_⟩
  rw [coarseKernel_apply, coarseStep]
  by_cases h0 : π (q ⁻¹' {v}) = 0
  · rw [if_pos h0]
    infer_instance
  · rw [if_neg h0]
    have : IsProbabilityMeasure (π[|q ⁻¹' {v}]) := cond_isProbabilityMeasure h0
    exact Measure.isProbabilityMeasure_map (hf := (hq.comp hF).aemeasurable)

/-- ★★ **The weighted step is the joint measure.** Multiplying one macro step by the weight of the
cell it starts from clears the conditioning, leaving the fine measure of "now in `v`, next in `s`". -/
theorem coarseStep_apply_mul (π : Measure α) [IsFiniteMeasure π] {q : α → β} (hq : Measurable q)
    {F : α → α} (hF : Measurable F) (v : β) (s : Set β) :
    π (q ⁻¹' {v}) * coarseStep π q F v s = π (q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s) := by
  have hmF : Measurable fun x : α => q (F x) := hq.comp hF
  by_cases h0 : π (q ⁻¹' {v}) = 0
  · rw [h0, zero_mul]
    exact (measure_mono_null inter_subset_left h0).symm
  · rw [coarseStep, if_neg h0, Measure.map_apply hmF (.of_discrete),
      cond_apply (hq MeasurableSet.of_discrete), ← mul_assoc,
      ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

variable [Fintype β]

/-- ★★★ **One step of the induced macro dynamics is the pushforward along `q ∘ F`.** The macro law
evolves by the macro kernel exactly as the fine measure evolves by `F` and is then read: the
conditional step loses nothing and adds nothing. -/
theorem comp_coarseLaw (π : Measure α) [IsFiniteMeasure π] {q : α → β} (hq : Measurable q)
    {F : α → α} (hF : Measurable F) :
    coarseKernel π q F ∘ₘ coarseLaw π q = π.map (fun x => q (F x)) := by
  have hmF : Measurable fun x : α => q (F x) := hq.comp hF
  ext s hs
  have hmeasA : ∀ v : β, MeasurableSet (q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s) := fun v =>
    (hq MeasurableSet.of_discrete).inter (hmF hs)
  have hdisj : Pairwise (Function.onFun Disjoint fun v : β =>
      q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s) := by
    intro v w hvw
    refine Set.disjoint_left.2 fun x hx hx' => hvw ?_
    have h1 : q x = v := hx.1
    have h2 : q x = w := hx'.1
    rw [← h1, h2]
  have hcover : (⋃ v : β, q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s)
      = (fun x => q (F x)) ⁻¹' s := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨_, _, hT⟩ => hT, fun hT => ⟨q x, rfl, hT⟩⟩
  have hpart : π (⋃ v : β, q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s)
      = ∑ v, π (q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s) := by
    rw [show (⋃ v : β, q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s)
          = ⋃ v ∈ (Finset.univ : Finset β), q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s from by simp]
    exact measure_biUnion_finset (fun v _ w _ hvw => hdisj hvw) fun v _ => hmeasA v
  have hsum : ∑ v, π (q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s)
      = π ((fun x => q (F x)) ⁻¹' s) := by
    rw [← hpart, hcover]
  calc (coarseKernel π q F ∘ₘ coarseLaw π q) s
      = ∑ v, coarseKernel π q F v s * coarseLaw π q {v} := by
        rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_fintype]
    _ = ∑ v, π (q ⁻¹' {v} ∩ (fun x => q (F x)) ⁻¹' s) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [coarseKernel_apply, coarseLaw_apply π hq MeasurableSet.of_discrete, mul_comm]
        exact coarseStep_apply_mul π hq hF v s
    _ = π ((fun x => q (F x)) ⁻¹' s) := hsum
    _ = π.map (fun x => q (F x)) s := by rw [Measure.map_apply hmF hs]

/-! ### Invariance forces the reference law, and the arrow follows -/

/-- ★★★ **Invariance of the fine measure makes the coarse law stationary.** This is what makes the
arrow a theorem rather than a posit: the reference law the divergence is measured from is not chosen,
it is the coarse-grained law itself, fixed by the invariance. -/
theorem comp_coarseLaw_of_measurePreserving (π : Measure α) [IsFiniteMeasure π] {q : α → β}
    (hq : Measurable q) {F : α → α} (hF : MeasurePreserving F π π) :
    coarseKernel π q F ∘ₘ coarseLaw π q = coarseLaw π q := by
  rw [comp_coarseLaw π hq hF.measurable, coarseLaw,
    show (fun x => q (F x)) = q ∘ F from rfl, ← Measure.map_map hq hF.measurable, hF.map_eq]

/-- ★★★ **The coarse-grained H-theorem.** Along the macro dynamics induced by a measure-preserving
fine dynamics, every macro law's relative entropy from the coarse-grained law is non-increasing, and
monotonically so in the number of steps.

No detailed balance, symmetry, double stochasticity or mixing is assumed, and **no property of the
cells**: the only input is that the fine dynamics preserves the fine measure. -/
theorem antitone_klDiv_coarseLaw (π : Measure α) [IsProbabilityMeasure π] {q : α → β}
    (hq : Measurable q) {F : α → α} (hF : MeasurePreserving F π π)
    (μ : Measure β) [IsProbabilityMeasure μ] :
    Antitone fun n : ℕ => klDiv (μ.compIterate (coarseKernel π q F) n) (coarseLaw π q) := by
  have := isMarkovKernel_coarseKernel π hq hF.measurable
  have := isProbabilityMeasure_coarseLaw π hq
  exact antitone_klDiv_compIterate _ (comp_coarseLaw_of_measurePreserving π hq hF)

/-- ★★ **The entropy form.** If the cells carry equal weight — the coarse law is uniform — the
coarse-grained Shannon entropy is non-*decreasing* along the induced dynamics, by #110. -/
theorem monotone_measureEntropy_coarseLaw [Nonempty β] (π : Measure α) [IsProbabilityMeasure π]
    {q : α → β} (hq : Measurable q) {F : α → α} (hF : MeasurePreserving F π π)
    (huniform : coarseLaw π q = uniformOn (univ : Set β))
    (μ : Measure β) [IsProbabilityMeasure μ] :
    Monotone fun n : ℕ => measureEntropy (μ.compIterate (coarseKernel π q F) n) := by
  have := isMarkovKernel_coarseKernel π hq hF.measurable
  refine monotone_measureEntropy_compIterate _ _ ?_
  rw [← huniform]
  exact comp_coarseLaw_of_measurePreserving π hq hF

end InformationTheory

end
