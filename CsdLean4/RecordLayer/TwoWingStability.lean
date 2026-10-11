/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TwoWingCoarsening
public import CsdLean4.RecordLayer.MacrostateStability

/-!
# Stability of the two-wing record

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #131, obligation **(2)**: dynamical record stability, for the two-wing reading.

#103 settled what stability can mean here — not invariance, which finite unitary dynamics cannot
supply, but a measure bound on the microstates a record *write* relabels — and
[`MacrostateStability.lean`](MacrostateStability.lean) proved it for the record string of a family
of contexts: `measure_drift_recordString_ne_le` bounds the exceptional set by `k · N · ω · T`.
#131's obligation (2) asks for the same thing about the **two-wing** record, which is the coarsening
of one joint context.

## The whole content, in one sentence

**Coarsening cannot destabilise.** `wingCode` is a function of `outcomeCode`
(★ `wingCode_eq_of_outcomeCode_eq`, through `fineIndex`), so a write that leaves the fine outcome
alone leaves the two-wing reading alone — and the exceptional set for the coarse record is therefore
a **subset** of the exceptional set for the fine one (★★★ `unstable_wingCode_subset`). Every bound
#103 proved is inherited with no new argument:

* ★★ `wingCode_sigmaShift` — a write of size `δ` leaves the two-wing code intact on a microstate
  that is `δ`-robustly inside *some* basin, and ★★ `mem_wingEvent_sigmaShift_iff` says the same for
  membership in a joint record event;
* ★★★ `measure_wingCode_ne_le` — the microstates whose two-wing record a write of size `δ` changes
  have epistemic measure at most `N · δ`. **One** context, so no factor of `k`;
* ★★★ `measure_exists_wingCode_ne_le` — the same bound uniformly over the whole horizon `[0, δ]`,
  inherited from #103's observation that the margin bought at `δ` covers every smaller write;
* ★★★ `measure_drift_wingCode_ne_le` — **persistence over a horizon**: under a drift of the record
  coordinate at rate `ω`, the two-wing record survives all of `[0, T]` outside a set of measure
  `N · ω · T`. This is obligation (2) for this experiment;
* ★★★ `measure_wingA_ne_le` — and **each wing separately**, since a wing's reading is a function of
  the pair;
* ★ `tendsto_measure_wingCode_ne` — the qualitative form: the relabelled set vanishes as the write
  shrinks.

## Honest scope

⚠️ **No sharpening, and the reason is worth recording.** One might expect the coarse record to be
*more* stable in proportion — four joint outcomes rather than `N` fine cells — and the bound here
does **not** deliver that. A write pushes a microstate towards the upper endpoint of its own arc, so
it can only relabel across a *fine* cell boundary; the coarse reading survives such a crossing
exactly when the decoding gives the two adjacent cells the same value. That is a property of the
decoding's **adjacency**, and `circleCell` orders cells by index while a pointer decoding
(`LF6.pointerDecode`) groups them by the pointer half of an arbitrary index equivalence — so
adjacent fine cells need not share a coarse value, and nothing can be claimed for free. A bound
scaling with the number of *coarse* boundaries is BACKLOG #138.

⚠️ **The write is the fibre translation `sigmaShift`**, as in #103: the base and the symplectic
partner are fixed. A flow that moves the **base** moves the arcs themselves, which is
[`BaseMotionStability.lean`](BaseMotionStability.lean)'s subject and is not composed with this.

⚠️ **This is not invariance and contains no mixing claim** — inherited verbatim from #103. No cell
is an invariant set and no flow is shown to mix.

⚠️ **Obligation (2) was priced "S, conditional" and the condition stands**: cheap for the fibre
dynamics, and **absent for a general `Φ_t`**. Nothing here covers a write that is not a translation
of the record coordinate, so in particular `CV.recordStroke`'s base-dependent write is not covered.

References: [`MacrostateStability.lean`](MacrostateStability.lean) (`sigmaShift`, `robustBasin`,
`unstableSet`, `outcomeCode_sigmaShift`, `measure_unstableSet_le`,
`measure_drift_recordString_ne_le` — every bound here is inherited from it),
[`TwoWingCoarsening.lean`](TwoWingCoarsening.lean) (`fineIndex`, `wingCode`, `wingEvent`),
[`RecordMacrostate.lean`](RecordMacrostate.lean) (`outcomeCode`),
`LF6/TwoWingRecord.lean` (`pointerDecode`, the decoding this is about);
`specs/BACKLOG.md` #131 obligation (2), #103, #138;
`specs/two-wing-experiment-scoping.md` §6.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {N : ℕ} {Ω₁ Ω₂ : Type*}

/-! ### Coarsening cannot destabilise -/

/-- The fine index is a function of the outcome code, so two microstates with the same code have the
same index. -/
theorem fineIndex_eq_of_outcomeCode_eq (c : ContextField N) {x y : LF4.KSigma N}
    (h : outcomeCode c x = outcomeCode c y) : fineIndex c x = fineIndex c y := by
  show finSuccEquiv N (outcomeCode c x) = finSuccEquiv N (outcomeCode c y)
  rw [h]

/-- ★ **The two-wing code is a function of the fine outcome code.** Everything in this file follows
from this: the coarse reading cannot change unless the fine one does. -/
theorem wingCode_eq_of_outcomeCode_eq (c : ContextField N) (w : Fin N → Ω₁ × Ω₂)
    {x y : LF4.KSigma N} (h : outcomeCode c x = outcomeCode c y) :
    wingCode c w x = wingCode c w y := by
  show (fineIndex c x).map w = (fineIndex c y).map w
  rw [fineIndex_eq_of_outcomeCode_eq c h]

/-- ★★★ **The coarse exceptional set sits inside the fine one.** A write that leaves the fine
outcome code alone leaves the two-wing record alone, so *every* stability bound for the fine record
is inherited by the coarse one, with no new argument and no loss. -/
theorem unstable_wingCode_subset (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) (δ : ℝ) :
    {x : LF4.KSigma N | wingCode c w (sigmaShift δ x) ≠ wingCode c w x}
      ⊆ {x : LF4.KSigma N | outcomeCode c (sigmaShift δ x) ≠ outcomeCode c x} := by
  intro x hx
  exact fun h => hx (wingCode_eq_of_outcomeCode_eq c w h)

/-! ### The pointwise statements -/

/-- ★★ **A write leaves the two-wing record intact on a microstate with margin.** -/
theorem wingCode_sigmaShift (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : LF4.KSigma N} (hx : ∃ i, x ∈ robustBasin c δ i) :
    wingCode c w (sigmaShift δ x) = wingCode c w x := by
  obtain ⟨i, hi⟩ := hx
  exact wingCode_eq_of_outcomeCode_eq c w (outcomeCode_sigmaShift c hδ hi)

/-- **The margin bought at `δ` covers every smaller write**, as for the record string. -/
theorem wingCode_sigmaShift_of_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {δ s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ δ) {x : LF4.KSigma N} (hx : ∃ i, x ∈ robustBasin c δ i) :
    wingCode c w (sigmaShift s x) = wingCode c w x :=
  wingCode_sigmaShift c w hs0 (hx.imp fun i hi => robustBasin_mono c hs i hi)

/-- ★★ **The joint record event is stable on microstates with margin**: a write cannot move such a
microstate into or out of the event. -/
theorem mem_wingEvent_sigmaShift_iff [DecidableEq Ω₁] [DecidableEq Ω₂] (c : ContextField N)
    (w : Fin N → Ω₁ × Ω₂) (st : Ω₁ × Ω₂) {δ : ℝ} (hδ : 0 ≤ δ) {x : LF4.KSigma N}
    (hx : ∃ i, x ∈ robustBasin c δ i) :
    sigmaShift δ x ∈ wingEvent c w st ↔ x ∈ wingEvent c w st := by
  rw [mem_wingEvent_iff, mem_wingEvent_iff, wingCode_sigmaShift c w hδ hx]

/-! ### The measure bounds, all inherited -/

/-- ★★★ **The two-wing record is stable to first order in the write.** The microstates whose
two-wing reading a write of size `δ` changes have epistemic measure at most `N · δ`. One joint
context, so no factor of `k`. -/
theorem measure_wingCode_ne_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (p : LF4.CPN N) :
    epistemicMeasure p {x | wingCode c w (sigmaShift δ x) ≠ wingCode c w x}
      ≤ (N : ENNReal) * ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_) (measure_unstableSet_le c δ p)
  intro x hx
  by_contra hmem
  exact hx (wingCode_sigmaShift c w hδ (exists_robustBasin_of_notMem_unstableSet c δ hmem))

/-- ★★★ **One exceptional set serves the whole horizon**, inherited from #103: the margin bought at
`δ` covers every smaller write, so no union over times is needed. -/
theorem measure_exists_wingCode_ne_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) (δ : ℝ)
    (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ s ∈ Icc (0 : ℝ) δ, wingCode c w (sigmaShift s x) ≠ wingCode c w x}
      ≤ (N : ENNReal) * ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_) (measure_unstableSet_le c δ p)
  intro x hx
  obtain ⟨s, hs, hne⟩ := hx
  by_contra hmem
  exact hne (wingCode_sigmaShift_of_le c w hs.1 hs.2
    (exists_robustBasin_of_notMem_unstableSet c δ hmem))

/-- ★★★ **Persistence over a horizon — obligation (2) for the two-wing experiment.** Under a drift
of the record coordinate at rate `ω`, the two-wing record survives the *entire* interval `[0, T]`
outside a set of epistemic measure at most `N · ω · T`. -/
theorem measure_drift_wingCode_ne_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {ω : ℝ}
    (hω : 0 ≤ ω) (T : ℝ) (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ t ∈ Icc (0 : ℝ) T, wingCode c w (sigmaShift (ω * t) x) ≠ wingCode c w x}
      ≤ (N : ENNReal) * ENNReal.ofReal (ω * T) := by
  refine le_trans (measure_mono ?_) (measure_exists_wingCode_ne_le c w (ω * T) p)
  intro x hx
  obtain ⟨t, ht, hne⟩ := hx
  exact ⟨ω * t, ⟨mul_nonneg hω ht.1, mul_le_mul_of_nonneg_left ht.2 hω⟩, hne⟩

/-- ★★★ **Each wing separately.** A wing's reading is a function of the pair, so the same bound
holds for A's record alone — and by symmetry for B's. -/
theorem measure_wingA_ne_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (p : LF4.CPN N) :
    epistemicMeasure p
        {x | (wingCode c w (sigmaShift δ x)).map Prod.fst ≠ (wingCode c w x).map Prod.fst}
      ≤ (N : ENNReal) * ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_) (measure_wingCode_ne_le c w hδ p)
  intro x hx
  exact fun h => hx (by rw [h])

/-- ★★★ **And B's.** -/
theorem measure_wingB_ne_le (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (p : LF4.CPN N) :
    epistemicMeasure p
        {x | (wingCode c w (sigmaShift δ x)).map Prod.snd ≠ (wingCode c w x).map Prod.snd}
      ≤ (N : ENNReal) * ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_) (measure_wingCode_ne_le c w hδ p)
  intro x hx
  exact fun h => hx (by rw [h])

/-- ★ **The relabelled set vanishes as the write shrinks** — the qualitative form, with the
same proof as #103's. -/
theorem tendsto_measure_wingCode_ne (c : ContextField N) (w : Fin N → Ω₁ × Ω₂)
    (p : LF4.CPN N) :
    Filter.Tendsto
      (fun δ : ℝ => epistemicMeasure p {x | wingCode c w (sigmaShift δ x) ≠ wingCode c w x})
      (nhdsWithin 0 (Ici 0)) (nhds 0) := by
  have hofReal : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhdsWithin 0 (Ici 0))
      (nhds 0) := by
    have h : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) :=
      nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal h
  have hbound : Filter.Tendsto (fun δ : ℝ => (N : ENNReal) * ENNReal.ofReal δ)
      (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hofReal (Or.inr (by simp))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Filter.Eventually.of_forall fun δ => zero_le)
    (eventually_mem_nhdsWithin.mono fun δ hδ => measure_wingCode_ne_le c w hδ p)

end CSD.RecordLayer

end

end
