/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.RecordMacrostate

/-!
# A de-isolation flow's record history

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #131, obligation 1 — and the cheapest test of that row's blocker **(II)**.

The audit ([`specs/two-wing-experiment-scoping.md`](../../specs/two-wing-experiment-scoping.md) §5)
recorded a real obstruction: `LF6`'s de-isolation flow moves the **base** and preserves `fsMeasure`,
while the Born and record statements are made in `epistemicMeasure p = δ_p ⊗ vol`, which a
base-moving flow does **not** preserve — it moves the Dirac. The record layer's own dynamics
`sigmaShift` preserves `epistemicMeasure` but moves only the fibre. Two dynamics, two measures.

**This file resolves that, and the resolution is that "preserves" was the wrong demand.**

* `liftBase` — a base-only flow lifted to `Σ`, which is what a de-isolation flow is as a map of the
  *ontic* space: it rotates the ray and leaves the record medium alone;
* ★★★ `map_epistemicMeasure_liftBase` — **the transport law**: `(liftBase Φ)_* (epistemicMeasure p)
  = epistemicMeasure (Φ p)`. The flow does not preserve a fixed epistemic measure; it carries the
  *prepared* one to the *post-measurement* one. Since `LF6`'s Born clause is stated at the
  post-measurement ray, that is exactly the composition the experiment needs, and blocker (II)
  dissolves rather than having to be worked around;
* ★★★ `measure_preimage_liftBase` — the same law in **preimage form**, which is the form a
  statement about the *run* needs: the probability, in the prepared measure, that the microstate
  *after* the flow lies in a record event is that event's probability at the post-measurement ray.
  Any record event works, so this is what composes the flow with the coarsened two-wing events of
  [`TwoWingCoarsening.lean`](TwoWingCoarsening.lean);
* ★★★ `map_outcomeCode_liftBase` and ★★★ `measure_outcomeCode_liftBase` — **the record history**:
  the law of the outcome code *after* the flow, in the prepared measure, is its law at the
  post-measurement ray. So an outcome statement proved at `Φ p` (which is what a Naimark-dilation
  clause gives) *is* a statement about the run that starts at `p`;
* ★★★ `measure_recordString_liftBase` — the same for a whole record string, which is the
  multi-context form #102's coordinate is stated in.

## Why this is the right first brick

It needs no choice about blocker **(I)** — the one-selector/two-channel question — so it can be
built before that physics decision is taken, and it tests the measure question on its own. It is
also the step that makes "the flow produces this record" a theorem rather than a juxtaposition of a
flow clause and a volume clause.

## Honest scope

⚠️ **The outcome events are not yet tied to pointer blocks here.** That tie is `LF6`'s clause (3),
through `e (n, stIdx (s, t))`; this file transports *whatever* outcome statement holds at `Φ p` back
to the prepared measure, and does not import `LF6`. Composing the two is #131 obligation 1's second
half and needs the index transport of the audit's §3.

⚠️ **One wing.** `outcomeCode` reads a single selector (`x.2.1`), so everything here is about one
joint outcome code. The two-wing version waits on blocker **(I)**, exactly as the row says.

⚠️ **No dynamics on the fibre.** `liftBase` leaves the record medium fixed, so this says nothing
about record *writes*; those are `sigmaShift` and `MacrostateStability.lean`'s business, and the two
have not been composed.

⚠️ **Not `C-1`.** Nothing here concerns causal structure; the adjacency of #131 is still supplied.

References: [`RecordMacrostate.lean`](RecordMacrostate.lean) (`outcomeCode`, `recordString`),
[`GlobalBasin.lean`](GlobalBasin.lean) (`epistemicMeasure`, `globalBasin`),
[`MacrostateStability.lean`](MacrostateStability.lean) (`sigmaShift`, the fibre dynamics this is the
complement of), `LF6/LocalDeisolationFlow.lean` (the flow this is for, not imported);
`specs/BACKLOG.md` #131, #102; `specs/two-wing-experiment-scoping.md` §5 and §6.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### A base-only flow, lifted to `Σ` -/

/-- **A de-isolation flow as a map of the ontic space**: it acts on the ray and leaves the record
medium alone. -/
def liftBase (Φ : LF4.CPN N → LF4.CPN N) (x : LF4.KSigma N) : LF4.KSigma N :=
  Prod.map Φ id x

@[simp]
theorem liftBase_apply (Φ : LF4.CPN N → LF4.CPN N) (x : LF4.KSigma N) :
    liftBase Φ x = (Φ x.1, x.2) := rfl

theorem measurable_liftBase {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ) :
    Measurable (liftBase Φ) :=
  hΦ.prodMap measurable_id

/-! ### The transport law -/

/-- ★★★ **The flow carries the prepared epistemic measure to the post-measurement one.** It does
*not* preserve a fixed `epistemicMeasure`, and this is why that was the wrong thing to ask: the
Dirac moves with the ray, the record medium's Haar measure does not move at all, and the result is
the epistemic measure of the image ray.

This is #131's blocker (II), dissolved. -/
theorem map_epistemicMeasure_liftBase {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ)
    (p : LF4.CPN N) :
    (epistemicMeasure p).map (liftBase Φ) = epistemicMeasure (Φ p) := by
  have hfun : (liftBase Φ) = Prod.map Φ (id : LF4.KTorus → LF4.KTorus) := rfl
  rw [epistemicMeasure, epistemicMeasure, hfun,
    ← Measure.map_prod_map _ _ hΦ (measurable_id (α := LF4.KTorus)),
    Measure.map_dirac' hΦ, Measure.map_id]

/-- ★★★ **The transport law in preimage form.** The probability, in the *prepared* epistemic
measure, that the microstate *after* the flow lies in the record event `S` is `S`'s probability at
the post-measurement ray. This is the shape every statement about a run takes, and unlike
`measure_outcomeCode_liftBase` it is stated for an arbitrary measurable event, so it composes with
any record coordinate or coarsening. -/
theorem measure_preimage_liftBase {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ)
    (p : LF4.CPN N) {S : Set (LF4.KSigma N)} (hS : MeasurableSet S) :
    epistemicMeasure p (liftBase Φ ⁻¹' S) = epistemicMeasure (Φ p) S := by
  rw [← map_epistemicMeasure_liftBase hΦ p, Measure.map_apply (measurable_liftBase hΦ) hS]

/-! ### The record history of a run -/

/-- ★★★ **The outcome code's law after the flow is its law at the image ray.** An outcome statement
proved at the post-measurement ray is therefore a statement about the run that *starts* at the
prepared ray — which is what makes "the flow produces this record" a theorem. -/
theorem map_outcomeCode_liftBase {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ)
    (c : ContextField N) (p : LF4.CPN N) :
    (epistemicMeasure p).map (outcomeCode c ∘ liftBase Φ)
      = (epistemicMeasure (Φ p)).map (outcomeCode c) := by
  rw [← Measure.map_map (measurable_outcomeCode c) (measurable_liftBase hΦ),
    map_epistemicMeasure_liftBase hΦ p]

/-- ★★★ **The same, read as a probability.** The chance that the run starting at `p` records outcome
`i` is the Born-style basin weight at the post-measurement ray. -/
theorem measure_outcomeCode_liftBase {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ)
    (c : ContextField N) (p : LF4.CPN N) (i : Fin N) :
    epistemicMeasure p ((outcomeCode c ∘ liftBase Φ) ⁻¹' {i.succ})
      = epistemicMeasure (Φ p) (globalBasin c i) := by
  have hmeas : Measurable (outcomeCode c ∘ liftBase Φ) :=
    (measurable_outcomeCode c).comp (measurable_liftBase hΦ)
  have h1 : epistemicMeasure p ((outcomeCode c ∘ liftBase Φ) ⁻¹' {i.succ})
      = ((epistemicMeasure p).map (outcomeCode c ∘ liftBase Φ)) {i.succ} := by
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
  rw [h1, map_outcomeCode_liftBase hΦ c p,
    Measure.map_apply (measurable_outcomeCode c) (measurableSet_singleton _),
    preimage_outcomeCode_succ]

/-- ★★★ **The whole record string transports too**, which is the multi-context form #102's
coordinate is stated in: the law of the record string of a run is its law at the image ray. -/
theorem measure_recordString_liftBase {k : ℕ} {Φ : LF4.CPN N → LF4.CPN N} (hΦ : Measurable Φ)
    (c : Fin k → ContextField N) (p : LF4.CPN N) :
    (epistemicMeasure p).map (recordString c ∘ liftBase Φ)
      = (epistemicMeasure (Φ p)).map (recordString c) := by
  rw [← Measure.map_map (measurable_recordString c) (measurable_liftBase hΦ),
    map_epistemicMeasure_liftBase hΦ p]

end CSD.RecordLayer

end

end
