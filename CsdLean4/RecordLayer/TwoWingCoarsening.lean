/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.FlowRecordHistory

/-!
# Two wings from one joint selector

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #131, blocker **(I)**, resolved at the author's decision by option **I1**: one joint ontic
selector, four cells, the two wings read off by coarsening.

## The decision this file implements, and why it is the shape it is

The audit found that `globalBasin`'s selector is one-dimensional — it reads `x.2.1`, and
`TorusFibre.mem_torusCell_iff` records that the second torus coordinate "is genuinely free … the
symplectic partner carries no record content". A two-wing experiment needs two *records*, and the
tempting minimal choice — one selector per wing, each wing's cell geometry depending only on that
wing's setting — **fails twice over**: it is the product-partition arity
`LF6.no_product_partition_realises_singlet` kills, *and* with independent selectors the joint law
factorises, so it cannot carry correlation at all.

Option I1 takes the other route. **One** selector, a context whose rates are the *joint* outcome
probabilities, and the wings obtained by **coarsening** the fine outcome code. Two facts make this
the cheapest option that is also foundationally clean:

* `circleCell r i = rep ⁻¹' Ioc (loSum r i) (loSum r i + r i)` has **no free offset** — a cell's
  position is determined by the rate vector alone. So "whose geometry sees the joint context" is
  really "which rate vector is the joint one", and I1 answers: there is one, and it is joint;
* the architecture `sigma-fibre-contextuality.md` settles on is *probabilities Born, regions
  contextual*. Coarsening preserves both: the fine widths are Born weights, the coarse cells move
  with the joint context, the fibre law stays fixed and context-independent, and `x.2.2` keeps the
  symplectic role the corpus gives it.

## What is proved

The content is stated once, for an arbitrary decoding `u : Fin N → κ` of the fine outcomes, and the
two wings are instances of it:

* `coarseEvent c u k` — the event that the fine outcome decodes to `k`: the union of the basins `u`
  sends to `k`, with `measurableSet_coarseEvent`;
* ★★★ `measure_coarseEvent` — **the coarse law is the sum of the fine Born weights over the
  decoding's fibre**. This is the shape `LF6`'s clause (3) already uses (summing basins over the
  system index), now as a theorem about any decoding;
* ★★★ `measure_coarseEvent_comp` — **coarsening composes**: decoding further sums the coarse
  weights. ★★★ `measure_wingAEvent_eq_sum` and ★★★ `measure_wingBEvent_eq_sum` are the two wing
  marginals read off it — **each wing's marginal is the sum over the other wing's outcomes.** Not an
  assumption: a consequence of the fine cells partitioning `Σ`, through `Finset.sum_fiberwise`;
* ★★★ `measure_coarseEvent_eq_of_fineSum_eq` and its wing form
  ★★★ `measure_wingAEvent_eq_of_fineSum_eq` — **operational no-signalling, with its premise named.**
  A's marginal agrees between two joint contexts exactly when their *summed* fine weights agree. The
  construction supplies the identity; whether the premise holds is a property of the rate vector —
  for the singlet, of `P_st` — and so it is checkable rather than smuggled;
* ★★ `factorsThrough_coarseEvent` — every coarse event is **macroscopic**: it is a preimage of #102's
  record string, so the wing reading is visible at the level of `π′` and not only on the microstate;
* `fineIndex` and `wingCode` — the pointwise codes, `Option`-valued through `finSuccEquiv` so that
  all of #102's `outcomeCode` API applies unchanged, with ★ `mem_wingEvent_iff` tying the code to the
  events;
* ★ `wingCode_ne_of_mem_of_mem` — **non-vacuity against the no-go**: the coarse code genuinely moves
  between joint contexts at the same ontic point, so these outcome maps are *not* of
  product-partition arity. This is the analogue of `LF3.translation_wingA_setting_dependent`, and
  without it the construction would be the pointwise primitive in disguise.

## Honest scope

⚠️ **The two wings share one ontic selector.** That is what I1 concedes, and it is a commitment about
`Σ`, not a formalisation artefact: the "two records" are two readings of `x.2.1`, so
`CV.recordStroke₂`'s two channels are not the write mechanism for this model. It is honest for CSD —
`Σ` is unified and the apparent nonlocality sits in the projection — and it is the easiest point for
a critic to press. Options I2 (chained selectors) and I3 (a non-product partition of `T²`) are the
alternatives, and both would repurpose `x.2.2`.

⚠️ **The measurable coordinate is still `outcomeCode`.** `fineIndex` and `wingCode` are convenience
codes into `Option`, a type with no measurable structure in scope, and **no measurability is claimed
for them**. Nothing is lost: every probability statement here is about an *event*, and
`factorsThrough_coarseEvent` is what ties those events to the measurable record coordinate.

⚠️ **No `P_st` here.** Nothing in this file mentions the singlet. The decoding and the context are
arguments; instantiating them with `LF6`'s pointer-pair index and the joint Born rates is #131
obligation 1's second half, and needs the index transport of the audit's §3.

⚠️ **No-signalling is conditional on its premise**, which is the honest form:
`measure_wingAEvent_eq_of_fineSum_eq` assumes the summed weights agree. For the singlet that premise
is `P_st`'s arithmetic and is *not* discharged here.

⚠️ **Measurement independence is inherited, not removed** — as in `LF3/SettingLocality.lean`, the
statements are made against one fixed `epistemicMeasure p` across contexts, and that fixture is the
Bell premise.

⚠️ **Not `C-1`.** No causal structure; #131's adjacency is still supplied.

References: [`RecordMacrostate.lean`](RecordMacrostate.lean) (`outcomeCode`, `recordString`, and the
basin API this is built on), [`GlobalBasin.lean`](GlobalBasin.lean) (`globalBasin`,
`epistemicMeasure`, `globalBasin_pairwiseDisjoint`),
[`MacroProjection.lean`](MacroProjection.lean) (`FactorsThrough`),
[`CircleFibre.lean`](CircleFibre.lean) (`circleCell`, the no-offset fact this decision turns on),
[`TorusFibre.lean`](TorusFibre.lean) (`x.2.2` as the symplectic partner),
`LF3/SettingLocality.lean` (`RemoteSettingLocalityA`, and the non-vacuity pattern),
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`, the no-go avoided);
`specs/BACKLOG.md` #131, #102; `specs/two-wing-experiment-scoping.md` §5 blocker (I);
`specs/sigma-fibre-contextuality.md` (probabilities Born, regions contextual).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The fine index

`outcomeCode` lands in `Fin (N + 1)` with `0` for "no basin". Through `finSuccEquiv` that is an
`Option (Fin N)`, which is the convenient form for composing a decoding. -/

/-- The index of the basin a microstate lies in, `none` on the null set no basin covers: the
`Option`-valued face of `outcomeCode`.

⚠️ No measurability is claimed — `Option (Fin N)` carries no measurable structure here. The
measurable coordinate is `outcomeCode`, and the probability content below is carried by events. -/
noncomputable def fineIndex (c : ContextField N) (x : LF4.KSigma N) : Option (Fin N) :=
  finSuccEquiv N (outcomeCode c x)

theorem fineIndex_eq_some_iff (c : ContextField N) (x : LF4.KSigma N) (i : Fin N) :
    fineIndex c x = some i ↔ x ∈ globalBasin c i := by
  show finSuccEquiv N (outcomeCode c x) = some i ↔ _
  rw [← finSuccEquiv_succ i, Equiv.apply_eq_iff_eq, outcomeCode_eq_succ_iff]

theorem fineIndex_eq_none_iff (c : ContextField N) (x : LF4.KSigma N) :
    fineIndex c x = none ↔ ∀ i, x ∉ globalBasin c i := by
  show finSuccEquiv N (outcomeCode c x) = none ↔ _
  rw [← finSuccEquiv_zero (n := N), Equiv.apply_eq_iff_eq]
  constructor
  · intro h i hi
    rw [(outcomeCode_eq_succ_iff c x i).2 hi] at h
    exact Fin.succ_ne_zero i h
  · intro h
    have hx : x ∈ outcomeCode c ⁻¹' {(0 : Fin (N + 1))} := by
      rw [preimage_outcomeCode_zero]
      simpa using h
    simpa using hx

/-! ### Coarse events of a decoding -/

section Coarse

variable {κ : Type*} [DecidableEq κ]

/-- **The coarse event of a decoding**: the microstates whose fine outcome `u` sends to `k`. For a
two-wing experiment with `u` the joint decoding this is "the pair of wings recorded `k`". -/
noncomputable def coarseEvent (c : ContextField N) (u : Fin N → κ) (k : κ) :
    Set (LF4.KSigma N) :=
  ⋃ i ∈ Finset.univ.filter fun i => u i = k, globalBasin c i

theorem mem_coarseEvent_iff (c : ContextField N) (u : Fin N → κ) (k : κ) (x : LF4.KSigma N) :
    x ∈ coarseEvent c u k ↔ ∃ i, u i = k ∧ x ∈ globalBasin c i := by
  simp only [coarseEvent, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop]

theorem measurableSet_coarseEvent (c : ContextField N) (u : Fin N → κ) (k : κ) :
    MeasurableSet (coarseEvent c u k) :=
  Finset.measurableSet_biUnion _ fun i _ => measurableSet_globalBasin c i

/-- ★★★ **Coarsening sums the fine Born weights.** The probability of a coarse outcome is the sum of
the Born weights of the fine cells the decoding sends to it — the shape `LF6`'s clause (3) already
uses, here as a theorem about an arbitrary decoding. -/
theorem measure_coarseEvent (c : ContextField N) (u : Fin N → κ) (p : LF4.CPN N) (k : κ) :
    epistemicMeasure p (coarseEvent c u k)
      = ∑ i ∈ Finset.univ.filter fun i => u i = k, epistemicMeasure p (globalBasin c i) := by
  refine measure_biUnion_finset (fun i _ j _ hij => globalBasin_pairwiseDisjoint c hij) ?_
  exact fun i _ => measurableSet_globalBasin c i

/-- ★★★ **Operational no-signalling, with its premise named.** The coarse weight agrees between two
contexts exactly when their summed fine weights do. The identity is supplied by the construction;
whether the premise holds is a property of the rate vectors, so it is checkable rather than assumed
in disguise. -/
theorem measure_coarseEvent_eq_of_fineSum_eq {c c' : ContextField N} {u : Fin N → κ}
    {p : LF4.CPN N} {k : κ}
    (h : ∑ i ∈ Finset.univ.filter fun i => u i = k, epistemicMeasure p (globalBasin c i)
        = ∑ i ∈ Finset.univ.filter fun i => u i = k, epistemicMeasure p (globalBasin c' i)) :
    epistemicMeasure p (coarseEvent c u k) = epistemicMeasure p (coarseEvent c' u k) := by
  rw [measure_coarseEvent, measure_coarseEvent, h]

/-- ★★ **Coarse events are macroscopic.** Each is a union of basins, and #102's criterion presents
each basin as a preimage of the record string, so the coarse reading is visible at the level of the
macroscopic coordinate — which is what #131's obligation 5 asks of an outcome. -/
theorem factorsThrough_coarseEvent {k : ℕ} (cf : Fin k → ContextField N) (j : Fin k)
    (u : Fin N → κ) (v : κ) :
    FactorsThrough (recordString cf) (coarseEvent (cf j) u v) := by
  rw [factorsThrough_iff]
  intro x y hxy
  rw [mem_coarseEvent_iff, mem_coarseEvent_iff]
  constructor
  · rintro ⟨i, hu, hmem⟩
    exact ⟨i, hu, (factorsThrough_iff.1 (factorsThrough_globalBasin cf j i) x y hxy).1 hmem⟩
  · rintro ⟨i, hu, hmem⟩
    exact ⟨i, hu, (factorsThrough_iff.1 (factorsThrough_globalBasin cf j i) x y hxy).2 hmem⟩

end Coarse

/-- ★★★ **Coarsening composes.** Decoding a coarse outcome further sums the coarse weights over the
second decoding's fibre. The two wing marginals below are the two instances of this, so neither is an
assumption: both follow from the fine cells partitioning `Σ`. -/
theorem measure_coarseEvent_comp {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq κ']
    (c : ContextField N) (u : Fin N → κ) (g : κ → κ') (p : LF4.CPN N) (k' : κ') :
    epistemicMeasure p (coarseEvent c (g ∘ u) k')
      = ∑ k ∈ Finset.univ.filter fun k => g k = k', epistemicMeasure p (coarseEvent c u k) := by
  have hfine : ∑ k ∈ Finset.univ.filter fun k => g k = k', epistemicMeasure p (coarseEvent c u k)
      = ∑ k ∈ Finset.univ.filter fun k => g k = k',
          ∑ i ∈ Finset.univ.filter fun i => u i = k, epistemicMeasure p (globalBasin c i) :=
    Finset.sum_congr rfl fun k _ => measure_coarseEvent c u p k
  rw [hfine, Finset.sum_fiberwise_eq_sum_filter, measure_coarseEvent]
  refine Finset.sum_congr ?_ fun i _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-! ### Summing a product over one coordinate's fibre -/

/-- Summing over the fibre of the first coordinate is summing over the second: the `Finset` form of
"the A-marginal sums over B's outcomes". -/
theorem sum_filter_fst_eq {Ω₁ Ω₂ M : Type*} [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Ω₁]
    [DecidableEq Ω₂] [AddCommMonoid M] (o₁ : Ω₁) (f : Ω₁ × Ω₂ → M) :
    ∑ st ∈ Finset.univ.filter fun st : Ω₁ × Ω₂ => st.1 = o₁, f st = ∑ o₂ : Ω₂, f (o₁, o₂) := by
  have hset : (Finset.univ.filter fun st : Ω₁ × Ω₂ => st.1 = o₁)
      = Finset.univ.image fun o₂ : Ω₂ => (o₁, o₂) := by
    ext st
    constructor
    · intro hst
      refine Finset.mem_image.2 ⟨st.2, Finset.mem_univ _, ?_⟩
      rw [← (Finset.mem_filter.1 hst).2]
    · intro hst
      obtain ⟨o₂, -, heq⟩ := Finset.mem_image.1 hst
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← heq]
  have hinj : Set.InjOn (fun o₂ : Ω₂ => (o₁, o₂)) ↑(Finset.univ : Finset Ω₂) := by
    intro a _ b _ hab
    simpa using hab
  rw [hset, Finset.sum_image hinj]

/-- Summing over the fibre of the second coordinate is summing over the first. -/
theorem sum_filter_snd_eq {Ω₁ Ω₂ M : Type*} [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Ω₁]
    [DecidableEq Ω₂] [AddCommMonoid M] (o₂ : Ω₂) (f : Ω₁ × Ω₂ → M) :
    ∑ st ∈ Finset.univ.filter fun st : Ω₁ × Ω₂ => st.2 = o₂, f st = ∑ o₁ : Ω₁, f (o₁, o₂) := by
  have hset : (Finset.univ.filter fun st : Ω₁ × Ω₂ => st.2 = o₂)
      = Finset.univ.image fun o₁ : Ω₁ => (o₁, o₂) := by
    ext st
    constructor
    · intro hst
      refine Finset.mem_image.2 ⟨st.1, Finset.mem_univ _, ?_⟩
      rw [← (Finset.mem_filter.1 hst).2]
    · intro hst
      obtain ⟨o₁, -, heq⟩ := Finset.mem_image.1 hst
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← heq]
  have hinj : Set.InjOn (fun o₁ : Ω₁ => (o₁, o₂)) ↑(Finset.univ : Finset Ω₁) := by
    intro a _ b _ hab
    simpa using hab
  rw [hset, Finset.sum_image hinj]

/-! ### The two wings -/

section Wings

variable {Ω₁ Ω₂ : Type*}

/-- **The joint wing event**: the two wings together recorded the pair `st`. -/
noncomputable def wingEvent [DecidableEq Ω₁] [DecidableEq Ω₂] (c : ContextField N)
    (w : Fin N → Ω₁ × Ω₂) (st : Ω₁ × Ω₂) : Set (LF4.KSigma N) :=
  coarseEvent c w st

/-- **The A-wing event**: wing A recorded `o₁`, whatever B recorded. A coarsening of the joint
event, which is the whole content of option I1. -/
noncomputable def wingAEvent [DecidableEq Ω₁] (c : ContextField N) (w : Fin N → Ω₁ × Ω₂)
    (o₁ : Ω₁) : Set (LF4.KSigma N) :=
  coarseEvent c (Prod.fst ∘ w) o₁

/-- **The B-wing event**: wing B recorded `o₂`, whatever A recorded. -/
noncomputable def wingBEvent [DecidableEq Ω₂] (c : ContextField N) (w : Fin N → Ω₁ × Ω₂)
    (o₂ : Ω₂) : Set (LF4.KSigma N) :=
  coarseEvent c (Prod.snd ∘ w) o₂

/-- **The two-wing outcome code**: the fine index decoded into a pair of wing outcomes, `none` on
the null set no basin covers. The pointwise companion of `wingEvent`; see
★ `mem_wingEvent_iff`. -/
noncomputable def wingCode (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) (x : LF4.KSigma N) :
    Option (Ω₁ × Ω₂) :=
  (fineIndex c x).map w

/-- ★ **The joint event is exactly where the code reads `st`** — so the probability statements really
are about the coarsened two-wing outcome. -/
theorem mem_wingEvent_iff [DecidableEq Ω₁] [DecidableEq Ω₂] (c : ContextField N)
    (w : Fin N → Ω₁ × Ω₂) (st : Ω₁ × Ω₂) (x : LF4.KSigma N) :
    x ∈ wingEvent c w st ↔ wingCode c w x = some st := by
  rw [wingEvent, mem_coarseEvent_iff, wingCode]
  constructor
  · rintro ⟨i, hw, hmem⟩
    rw [(fineIndex_eq_some_iff c x i).2 hmem]
    simp [hw]
  · intro h
    cases hv : fineIndex c x with
    | none =>
        rw [hv] at h
        simp at h
    | some i =>
        rw [hv] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨i, h, (fineIndex_eq_some_iff c x i).1 hv⟩

/-- ★★★ **The A-wing's marginal is the sum over B's outcomes.** Not an assumption — a consequence of
the fine cells partitioning `Σ`, by `measure_coarseEvent_comp`. -/
theorem measure_wingAEvent_eq_sum [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Ω₁] [DecidableEq Ω₂]
    (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) (p : LF4.CPN N) (o₁ : Ω₁) :
    epistemicMeasure p (wingAEvent c w o₁)
      = ∑ o₂ : Ω₂, epistemicMeasure p (wingEvent c w (o₁, o₂)) := by
  have h := measure_coarseEvent_comp c w Prod.fst p o₁
  rw [sum_filter_fst_eq] at h
  exact h

/-- ★★★ **The B-wing's marginal is the sum over A's outcomes**, by the same theorem. -/
theorem measure_wingBEvent_eq_sum [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Ω₁] [DecidableEq Ω₂]
    (c : ContextField N) (w : Fin N → Ω₁ × Ω₂) (p : LF4.CPN N) (o₂ : Ω₂) :
    epistemicMeasure p (wingBEvent c w o₂)
      = ∑ o₁ : Ω₁, epistemicMeasure p (wingEvent c w (o₁, o₂)) := by
  have h := measure_coarseEvent_comp c w Prod.snd p o₂
  rw [sum_filter_snd_eq] at h
  exact h

/-- ★★★ **Operational no-signalling for wing A**, with its premise named: A's marginal is unchanged
between two joint contexts exactly when the fine weights A's outcome selects sum to the same thing.
Changing B's setting changes the joint context, so this is the statement a signalling claim would
have to break. -/
theorem measure_wingAEvent_eq_of_fineSum_eq [DecidableEq Ω₁] {c c' : ContextField N}
    {w : Fin N → Ω₁ × Ω₂} {p : LF4.CPN N} {o₁ : Ω₁}
    (h : ∑ i ∈ Finset.univ.filter fun i => (w i).1 = o₁, epistemicMeasure p (globalBasin c i)
        = ∑ i ∈ Finset.univ.filter fun i => (w i).1 = o₁,
            epistemicMeasure p (globalBasin c' i)) :
    epistemicMeasure p (wingAEvent c w o₁) = epistemicMeasure p (wingAEvent c' w o₁) :=
  measure_coarseEvent_eq_of_fineSum_eq h

/-- ★★★ **Operational no-signalling for wing B.** -/
theorem measure_wingBEvent_eq_of_fineSum_eq [DecidableEq Ω₂] {c c' : ContextField N}
    {w : Fin N → Ω₁ × Ω₂} {p : LF4.CPN N} {o₂ : Ω₂}
    (h : ∑ i ∈ Finset.univ.filter fun i => (w i).2 = o₂, epistemicMeasure p (globalBasin c i)
        = ∑ i ∈ Finset.univ.filter fun i => (w i).2 = o₂,
            epistemicMeasure p (globalBasin c' i)) :
    epistemicMeasure p (wingBEvent c w o₂) = epistemicMeasure p (wingBEvent c' w o₂) :=
  measure_coarseEvent_eq_of_fineSum_eq h

/-! ### Non-vacuity: the coarse code is not of product-partition arity -/

/-- ★ **The coarse code genuinely moves with the joint context.** At one ontic point two joint
contexts can return different wing pairs, so these outcome maps are **not** setting-local response
functions and `LF6.no_product_partition_realises_singlet` does not apply to them.

Without this the construction would be the pointwise primitive in disguise — the same check
`LF3.translation_wingA_setting_dependent` makes for the relabelling primitive. -/
theorem wingCode_ne_of_mem_of_mem {c c' : ContextField N} {w : Fin N → Ω₁ × Ω₂}
    {x : LF4.KSigma N} {i j : Fin N} (hi : x ∈ globalBasin c i) (hj : x ∈ globalBasin c' j)
    (hne : w i ≠ w j) : wingCode c w x ≠ wingCode c' w x := by
  rw [wingCode, wingCode, (fineIndex_eq_some_iff c x i).2 hi,
    (fineIndex_eq_some_iff c' x j).2 hj]
  simpa using hne

end Wings

end CSD.RecordLayer

end

end
