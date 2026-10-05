/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ArenaTransport
public import CsdLean4.Mathlib.InformationTheory.KlDivArrow
public import CsdLean4.Mathlib.InformationTheory.FiniteEntropy

/-!
# The arrow of time at the macroscopic projection

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #109, out of the records→spacetime scoping note's `ST-3`.

The corpus's second law is `Thermo`'s: coarse-grained entropy monotonicity **for a specific
coarse-graining** (pinching to a pointer basis). The scoping note said the specification wanted was
`π′`, the macroscopic-coordinate projection — and since #102 chose it and #103–#107 made it stable,
the second law can be stated *at* `π′`. That is what this file does.

## What is proved

* `recordLaw c p` — **the macroscopic law**: the pushforward of the ontic measure along the record
  string. A probability measure on the finite macrostate type;
* `macroKernel c p F` — **the macro dynamics induced by a fine dynamics**, with no extra input: the
  conditional law of the next macrostate given the present one (`dirac` on the null macrostates, so it
  is Markov on the nose), and ★★ `macroStep_apply_mul` / ★★★ `comp_recordLaw` — one step of it sends
  the macroscopic law to the pushforward along `π′ ∘ F`, which is the chain rule for this projection;
* ★★★ `comp_recordLaw_of_measurePreserving` — **Liouville forces the reference law.** If the fine
  dynamics preserves the ontic measure then the **Born record law is stationary** for the induced
  macro kernel. The arrow's reference law is therefore not posited: it is the record law itself, fixed
  by the invariance of the ontic measure;
* ★★★ `antitone_klDiv_recordLaw` — **the second law at `π′`**: along the induced dynamics, *every*
  macroscopic law's relative entropy from the Born record law is non-increasing, monotonically in the
  number of steps. A Lyapunov function, with no detailed balance, symmetry or double stochasticity
  assumed;
* ★★ `comp_recordLaw_sigmaShift` and ★★★ `antitone_klDiv_recordLaw_sigmaShift` — **and the corpus's
  own dynamics is an instance**: a record write preserves the epistemic measure (#103), so its induced
  macro kernel has the Born record law stationary and carries the arrow;
* ★★ `klDiv_recordLaw_sigmaShift` — **but the write itself produces nothing.** #103's exact invariance
  of the macroscopic law says the divergence from any reference is *unchanged* by a write, however
  large. The production is in the conditional step, never in the write;
* ★★ `measureEntropy_recordLaw_le` (added with #110) — **the macroscopic entropy of a record is at
  most its capacity**: a `k`-context record string over `N + 1` codes carries at most
  `k · log (N + 1)` of Shannon entropy, whatever the preparation and whatever the context family.
  Unconditional, and the only *entropy* statement available here — see the scope note.

## Honest scope

⚠️ **The kernel is induced, not derived from an interaction.** `macroKernel` is the conditional law of
`π′ ∘ F` given `π′`; it exists for any measurable `F` and says nothing about why `F` is the physical
dynamics. The de-isolation obligation of [`DeIsolationFlow.lean`](DeIsolationFlow.lean) and #108's
`readyPrep` hypothesis are untouched.

⚠️ **Divergence, not Shannon entropy.** The arrow here is "relative entropy from the Born record law
decreases", which is the modern form. #110 supplied the missing identity
(`klDiv μ uniform = ofReal (log card − measureEntropy μ)`), but turning the arrow into "Shannon
entropy increases" *also* needs the reference law to be **uniform**, and the Born record law is not —
for a genuine superposition it is the spread of Born weights. So the entropy form of the H-theorem is
proved in `Mathlib/InformationTheory/FiniteEntropy.lean` for a uniform-preserving kernel and is **not**
claimed for the record dynamics; what #110 buys here is the unconditional capacity bound
`measureEntropy_recordLaw_le`.

⚠️ **Monotone is not strictly decreasing, and no rate is claimed.** Nothing here says the divergence
reaches `0`, or that it decreases at all at any particular step: a kernel can be the identity. Mixing,
relaxation rates and the H-theorem's strict form are not addressed.

⚠️ **One preparation, one context family.** Everything is at a fixed `p` and a fixed `c`; nothing
varies the preparation or compares families.

⚠️ **This is not an arrow on the event order.** The monotone quantity is a divergence between
macroscopic laws under a discrete step count, not a time orientation of
[`CV/RecordCausalOrder.lean`](../CV/RecordCausalOrder.lean)'s causal order, and nothing here bears on
a metric, a volume element or a continuum limit.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `Mathlib/InformationTheory/KlDivArrow.lean`,
`Mathlib/InformationTheory/FiniteEntropy.lean` (#110),
`MacrostateStability.lean` (#103), `RecordMacrostate.lean` (#102), `MacroProjection.lean` (#99),
`ArenaTransport.lean` (#107), `Thermo/FreeEnergy.lean` (`vonNeumannEntropy_le_pinching`, the pinching
second law this stands beside); `specs/BACKLOG.md` #110, #109, #107, #103, #102, #100, #99.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set

open scoped ENNReal

namespace CSD.RecordLayer

variable {N k : ℕ}

/-! ### The macroscopic law -/

/-- **The macroscopic law** of a context family at a preparation: the pushforward of the ontic measure
along the record string of #102. -/
noncomputable def recordLaw (c : Fin k → ContextField N) (p : LF4.CPN N) :
    Measure (Fin k → Fin (N + 1)) :=
  (epistemicMeasure p).map (recordString c)

theorem recordLaw_apply (c : Fin k → ContextField N) (p : LF4.CPN N)
    {s : Set (Fin k → Fin (N + 1))} (hs : MeasurableSet s) :
    recordLaw c p s = epistemicMeasure p (recordString c ⁻¹' s) := by
  rw [recordLaw, Measure.map_apply (measurable_recordString c) hs]

instance isProbabilityMeasure_recordLaw (c : Fin k → ContextField N) (p : LF4.CPN N) :
    IsProbabilityMeasure (recordLaw c p) :=
  Measure.isProbabilityMeasure_map (measurable_recordString c).aemeasurable

/-! ### A record write produces nothing -/

/-- ★ **The macroscopic law is exactly invariant under a record write**, which is #103's
`map_recordString_sigmaShift` in the vocabulary of this file. -/
theorem recordLaw_sigmaShift (c : Fin k → ContextField N) (δ : ℝ) (p : LF4.CPN N) :
    (epistemicMeasure p).map (fun x => recordString c (sigmaShift δ x)) = recordLaw c p :=
  map_recordString_sigmaShift c δ p

/-- ★★ **So a record write produces no relative entropy**, however large it is: the divergence of the
macroscopic law from **any** reference law is unchanged. Whatever an arrow of time at `π′` comes from,
it is not the write. -/
theorem klDiv_recordLaw_sigmaShift (c : Fin k → ContextField N) (δ : ℝ) (p : LF4.CPN N)
    (ρ : Measure (Fin k → Fin (N + 1))) :
    klDiv ((epistemicMeasure p).map (fun x => recordString c (sigmaShift δ x))) ρ
      = klDiv (recordLaw c p) ρ := by
  rw [recordLaw_sigmaShift]

/-! ### The macro dynamics induced by a fine dynamics -/

/-- One step of the **induced macro dynamics**: the conditional law of the next macrostate given the
present one. On a macrostate of zero ontic measure there is nothing to condition on, and the step is
`dirac`, which keeps the kernel Markov without affecting anything (such a macrostate carries no
weight). -/
noncomputable def macroStep (c : Fin k → ContextField N) (p : LF4.CPN N)
    (F : LF4.KSigma N → LF4.KSigma N) (v : Fin k → Fin (N + 1)) :
    Measure (Fin k → Fin (N + 1)) :=
  if epistemicMeasure p (recordString c ⁻¹' {v}) = 0 then Measure.dirac v
  else ((epistemicMeasure p)[|recordString c ⁻¹' {v}]).map (fun x => recordString c (F x))

/-- **The induced macro kernel.** Measurability is free: the macrostate type is finite. -/
noncomputable def macroKernel (c : Fin k → ContextField N) (p : LF4.CPN N)
    (F : LF4.KSigma N → LF4.KSigma N) :
    Kernel (Fin k → Fin (N + 1)) (Fin k → Fin (N + 1)) :=
  ⟨macroStep c p F, Measurable.of_discrete⟩

@[simp] theorem macroKernel_apply (c : Fin k → ContextField N) (p : LF4.CPN N)
    (F : LF4.KSigma N → LF4.KSigma N) (v : Fin k → Fin (N + 1)) :
    macroKernel c p F v = macroStep c p F v := rfl

theorem isMarkovKernel_macroKernel (c : Fin k → ContextField N) (p : LF4.CPN N)
    {F : LF4.KSigma N → LF4.KSigma N} (hF : Measurable F) :
    IsMarkovKernel (macroKernel c p F) := by
  refine ⟨fun v => ?_⟩
  rw [macroKernel_apply, macroStep]
  split
  · infer_instance
  · rename_i h0
    have : IsProbabilityMeasure ((epistemicMeasure p)[|recordString c ⁻¹' {v}]) :=
      cond_isProbabilityMeasure h0
    exact Measure.isProbabilityMeasure_map
      (hf := ((measurable_recordString c).comp hF).aemeasurable)

/-- ★★ **The weighted step is the joint measure.** Multiplying one step of the macro dynamics by the
weight of the macrostate it starts from clears the conditioning, and what is left is the ontic measure
of "now in `v`, next in `s`". This is the identity the chain rule for `π′` runs on. -/
theorem macroStep_apply_mul (c : Fin k → ContextField N) (p : LF4.CPN N)
    {F : LF4.KSigma N → LF4.KSigma N} (hF : Measurable F) (v : Fin k → Fin (N + 1))
    (s : Set (Fin k → Fin (N + 1))) :
    epistemicMeasure p (recordString c ⁻¹' {v}) * macroStep c p F v s
      = epistemicMeasure p
          (recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s) := by
  have hmF : Measurable fun x : LF4.KSigma N => recordString c (F x) :=
    (measurable_recordString c).comp hF
  by_cases h0 : epistemicMeasure p (recordString c ⁻¹' {v}) = 0
  · rw [h0, zero_mul]
    exact (measure_mono_null inter_subset_left h0).symm
  · rw [macroStep, if_neg h0, Measure.map_apply hmF (.of_discrete),
      cond_apply ((measurable_recordString c) (measurableSet_singleton v)), ← mul_assoc,
      ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- ★★★ **One step of the induced macro dynamics is the pushforward along `π′ ∘ F`.** The macroscopic
law evolves by the macro kernel exactly as the ontic measure evolves by `F` and is then read: the
conditional step loses nothing and adds nothing. -/
theorem comp_recordLaw (c : Fin k → ContextField N) (p : LF4.CPN N)
    {F : LF4.KSigma N → LF4.KSigma N} (hF : Measurable F) :
    macroKernel c p F ∘ₘ recordLaw c p
      = (epistemicMeasure p).map (fun x => recordString c (F x)) := by
  have hmF : Measurable fun x : LF4.KSigma N => recordString c (F x) :=
    (measurable_recordString c).comp hF
  ext s hs
  have hmeasA : ∀ v : Fin k → Fin (N + 1), MeasurableSet
      (recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s) := fun v =>
    ((measurable_recordString c) (measurableSet_singleton v)).inter (hmF hs)
  have hdisj : Pairwise (Function.onFun Disjoint fun v : Fin k → Fin (N + 1) =>
      recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s) := by
    intro v w hvw
    refine Set.disjoint_left.2 fun x hx hx' => hvw ?_
    have h1 : recordString c x = v := hx.1
    have h2 : recordString c x = w := hx'.1
    rw [← h1, h2]
  have hcover : (⋃ v : Fin k → Fin (N + 1),
      recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s)
      = (fun x => recordString c (F x)) ⁻¹' s := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨_, _, hT⟩ => hT, fun hT => ⟨recordString c x, rfl, hT⟩⟩
  have hpart : epistemicMeasure p (⋃ v : Fin k → Fin (N + 1),
      recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s)
      = ∑ v, epistemicMeasure p
          (recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s) := by
    rw [show (⋃ v : Fin k → Fin (N + 1),
            recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s)
          = ⋃ v ∈ (Finset.univ : Finset (Fin k → Fin (N + 1))),
            recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s from by simp]
    exact measure_biUnion_finset (fun v _ w _ hvw => hdisj hvw) fun v _ => hmeasA v
  have hsum : ∑ v, epistemicMeasure p
      (recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s)
      = epistemicMeasure p ((fun x => recordString c (F x)) ⁻¹' s) := by
    rw [← hpart, hcover]
  calc (macroKernel c p F ∘ₘ recordLaw c p) s
      = ∑ v, macroKernel c p F v s * recordLaw c p {v} := by
        rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_fintype]
    _ = ∑ v, epistemicMeasure p
          (recordString c ⁻¹' {v} ∩ (fun x => recordString c (F x)) ⁻¹' s) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [macroKernel_apply, recordLaw_apply c p (measurableSet_singleton v), mul_comm]
        exact macroStep_apply_mul c p hF v s
    _ = epistemicMeasure p ((fun x => recordString c (F x)) ⁻¹' s) := hsum
    _ = (epistemicMeasure p).map (fun x => recordString c (F x)) s := by
        rw [Measure.map_apply hmF hs]

/-! ### Liouville forces the reference law, and the arrow follows -/

/-- ★★★ **Liouville forces the reference law.** If the fine dynamics preserves the ontic measure, the
**Born record law is stationary** for the macro dynamics it induces.

This is the step that makes an arrow at `π′` a theorem rather than a posit: the reference law the
divergence is measured from is not chosen, it is the macroscopic law itself, fixed by the invariance of
the ontic measure. -/
theorem comp_recordLaw_of_measurePreserving (c : Fin k → ContextField N) (p : LF4.CPN N)
    {F : LF4.KSigma N → LF4.KSigma N}
    (hF : MeasurePreserving F (epistemicMeasure p) (epistemicMeasure p)) :
    macroKernel c p F ∘ₘ recordLaw c p = recordLaw c p := by
  rw [comp_recordLaw c p hF.measurable, recordLaw,
    show (fun x => recordString c (F x)) = recordString c ∘ F from rfl,
    ← Measure.map_map (measurable_recordString c) hF.measurable, hF.map_eq]

/-- ★★★ **The second law at `π′`.** Along the macro dynamics induced by a measure-preserving fine
dynamics, every macroscopic law's relative entropy from the Born record law is non-increasing, and
monotonically so in the number of steps.

No detailed balance, symmetry or double stochasticity is assumed: the only input is that the fine
dynamics preserves the ontic measure, which is Liouville. -/
theorem antitone_klDiv_recordLaw (c : Fin k → ContextField N) (p : LF4.CPN N)
    {F : LF4.KSigma N → LF4.KSigma N}
    (hF : MeasurePreserving F (epistemicMeasure p) (epistemicMeasure p))
    (q : Measure (Fin k → Fin (N + 1))) [IsProbabilityMeasure q] :
    Antitone fun n : ℕ => klDiv (q.compIterate (macroKernel c p F) n) (recordLaw c p) := by
  have := isMarkovKernel_macroKernel c p hF.measurable
  exact antitone_klDiv_compIterate _ (comp_recordLaw_of_measurePreserving c p hF)

/-! ### The corpus's own dynamics is an instance -/

/-- ★★ **A record write is such a dynamics.** #103's `measurePreserving_sigmaShift` makes the Born
record law stationary for the macro kernel a write induces. -/
theorem comp_recordLaw_sigmaShift (c : Fin k → ContextField N) (δ : ℝ) (p : LF4.CPN N) :
    macroKernel c p (sigmaShift δ) ∘ₘ recordLaw c p = recordLaw c p :=
  comp_recordLaw_of_measurePreserving c p (measurePreserving_sigmaShift δ p)

/-- ★★★ **So the arrow holds for the corpus's own record dynamics**: under the macro kernel a record
write induces, every macroscopic law relaxes monotonically toward the Born record law.

Read together with `klDiv_recordLaw_sigmaShift` this says exactly where the production sits: the write
moves the macroscopic law not at all, and all of the monotone behaviour is the conditional step — the
coarse-graining, not the dynamics. -/
theorem antitone_klDiv_recordLaw_sigmaShift (c : Fin k → ContextField N) (δ : ℝ) (p : LF4.CPN N)
    (q : Measure (Fin k → Fin (N + 1))) [IsProbabilityMeasure q] :
    Antitone fun n : ℕ =>
      klDiv (q.compIterate (macroKernel c p (sigmaShift δ)) n) (recordLaw c p) :=
  antitone_klDiv_recordLaw c p (measurePreserving_sigmaShift δ p) q

/-! ### The capacity of a record -/

/-- ★★ **The macroscopic entropy of a record is at most its capacity.** A `k`-context record string
over `N + 1` codes carries at most `k · log (N + 1)` of Shannon entropy — whatever the preparation,
and whatever the context family.

This is #110's maximum-entropy theorem at `π′`, and it is the *only* unconditional entropy statement
available here: the arrow of this file is in divergence form, because the Born record law it is
measured from is not uniform. -/
theorem measureEntropy_recordLaw_le (c : Fin k → ContextField N) (p : LF4.CPN N) :
    measureEntropy (recordLaw c p) ≤ k * Real.log (N + 1) := by
  have h := measureEntropy_le_log_card (recordLaw c p)
  rw [show Fintype.card (Fin k → Fin (N + 1)) = (N + 1) ^ k from by simp, Nat.cast_pow,
    Real.log_pow] at h
  push_cast at h
  exact h

end CSD.RecordLayer

end
