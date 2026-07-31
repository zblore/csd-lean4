/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.GlobalBasin
public import CsdLean4.SigmaLayer.CircleRecord

/-!
# SigmaLayer/GlobalRecordClosure: the record-layer capstone, on the context-fixed basins

**Category:** 7-SigmaLayer (the record layer — MD-1, the closure).

The successor to `SigmaLayer/RecordLayerClosure.lean`. That bundle certifies the record layer on the
fibre `Σ = ℝ` with `fibreTypicality`, for the context `bornContext ψ` — **built from the
preparation**. This one certifies the same five facts on the corpus's actual compact sector
`Σ = ℂℙⁿ⁻¹ × T²`, for a `ContextField` — **built from the apparatus alone**.

## What changes, and what does not

The five closure fields are the *same five*, and that is the point: nothing about the record layer's
content depended on the preparation-indexing. What changes is the arena and the context type.

| | `RecordLayerClosure` | `GlobalRecordClosure` |
|---|---|---|
| arena | `ℝ` (non-compact, odd-dim'l product) | `KSigma = ℂℙⁿ⁻¹ × T²` (compact, even) |
| context | `bornContext ψ` — the *preparation* | `ContextField` — the *apparatus* |
| measure | `fibreTypicality` (Lebesgue on `[0,1)`) | `epistemicMeasure p = δ_p ⊗ Haar` |
| `ae_total` | on `Ico 0 1`, by hand | on `univ` — the whole space has measure one |

★ **The record event is now a function of `(context, outcome, time)` and of nothing else.** That is
visible in the type of `globalRecordSemantics` and needs no theorem to state: the *same* set
`globalBasin c i` serves every preparation, and only the epistemic measure moves. Under
`fibreRecordSemantics` the event itself was `cdfCell (bornRate ψ)`, so it moved with `ψ`. This is the
defect A7 objected to, and it is what the migration removes.

★ **`globalOutcome` is literally `circleOutcome` read at the point's own base**, so the ontic
selection needs no new machinery — `globalOutcome_eq_some_iff` is `circleOutcome_eq_some_iff`
composed with the definitional unfolding of `globalBasin`.

## Scope — unchanged from `GlobalBasin.lean`, and repeated because this is the capstone

⚠️ `epistemicMeasure p = δ_p ⊗ Haar` is the **epistemic** measure, taken as a *definition* rather
than obtained by disintegration (conditioning on `p` conditions on a `μ_FS`-null set). It is not the
Liouville measure; `kMuL = μ_FS ⊗ vol` remains that.

⚠️ **KINEMATIC.** No `H_int(M)` generating these basins is constructed. The Paper D obligation
(`SigmaLayer/DeIsolationFlow.lean`) is untouched, and a certified readout is not a dynamical account
of measurement.

⚠️ This closes the **preparation-indexing** defect, not general-`N` A7 outright — whether Paper C
intends `Ωᵢ(M)` to be *base-only* (in which case the parked `ContextFixedA7` chain still governs) is
a question about the axiom, not about this file.

⚠️ **`RecordLayerClosure` is superseded, not deleted.** It remains true, and `FiniteQMClosure` still
carries the older `vnPointerOutcome` readout — swapping *that* is a separate migration on the
`productDynamics` engine, and is not done here.

## References

`SigmaLayer/RecordLayerClosure.lean` (the `ℝ` bundle this succeeds);
`SigmaLayer/GlobalBasin.lean` (`ContextField`, `globalBasin`, `epistemicMeasure`, `globalBasin_born`);
`SigmaLayer/RecordedFact.lean` (`RecordSemantics`, `compatibleSet`, and the warning that the
structure is trivially inhabited — the non-vacuity here is `ae_total` and `born_typicality`);
`SigmaLayer/CircleRecord.lean` (`circleOutcome`); `specs/record-layer-plan.md` §4 (MD-1);
`specs/BACKLOG.md` (the ★★ row).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The record semantics on the compact sector -/

/-- **The global record signature (P5 data):** contexts are `ContextField`s — rate *fields* on the
ontic base — and outcomes are `Fin N`. Contrast `fibreSignature`, whose contexts are bare rate
vectors and so had to be manufactured from a preparation. -/
def globalSignature (N : ℕ) : RecordSignature where
  Context := ContextField N
  Outcome := fun _ => Fin N

/-- **The global record semantics (P5) on `Σ = ℂℙⁿ⁻¹ × T²`.** The ontic event of "context `c`
recorded outcome `i`" is the context-fixed basin `globalBasin c i`: measurable
(`measurableSet_globalBasin`), and within one context at one time distinct outcomes are mutually
exclusive (`globalBasin_pairwiseDisjoint`).

⚠️ `RecordSemantics` is trivially inhabited (`RecordedFact.lean`), so exhibiting this instance proves
nothing on its own. The content is in `globalRecordClosure`'s `born_typicality` and `ae_total`. -/
noncomputable def globalRecordSemantics (N : ℕ) :
    RecordSemantics (LF4.KSigma N) (globalSignature N) where
  event r := globalBasin r.context r.outcome
  measurable_event r := measurableSet_globalBasin _ _
  exclusive c a b _ x ha hb := by
    by_contra hab
    exact absurd hb (Set.disjoint_left.mp (globalBasin_pairwiseDisjoint c hab) ha)

@[simp] theorem globalRecordSemantics_event (c : ContextField N) (i : Fin N) (t : OnticTime) :
    (globalRecordSemantics N).event ⟨c, i, t⟩ = globalBasin c i := rfl

/-- The compatible region of the single-record history `[⟨c, i, t⟩]` is exactly the basin: isolation
on this record conditions the ontic state onto the outcome basin (P6). -/
theorem compatibleSet_global_single (c : ContextField N) (i : Fin N) (t : OnticTime) :
    compatibleSet (globalRecordSemantics N) [⟨c, i, t⟩] = globalBasin c i := by
  rw [compatibleSet_cons, compatibleSet_nil, Set.inter_univ, globalRecordSemantics_event]

/-! ### The ontic selection -/

/-- **The ontic selection on `Σ`**: read which basin the point occupies. It is `circleOutcome`
applied to the point's *own* fibre coordinate, with the rates the context assigns at the point's
*own* base — so no new selection machinery is needed. -/
noncomputable def globalOutcome (c : ContextField N) (x : LF4.KSigma N) : Option (Fin N) :=
  circleOutcome (c.rate x.1) x.2.1

/-- **Reading the outcome and testing the record event agree**: the ontic selection *is* the
record. -/
theorem globalOutcome_eq_some_iff (c : ContextField N) (x : LF4.KSigma N) (i : Fin N) :
    globalOutcome c x = some i ↔ x ∈ globalBasin c i :=
  circleOutcome_eq_some_iff (c.rate x.1) (c.nonneg x.1) x.2.1 i

/-! ### The closure bundle -/

/-- **The global record-layer closure (MD-1).** The five record-layer facts, certified on the
corpus's compact sector for a context fixed by the apparatus and a preparation `p`.

Field-for-field the same bundle as `RecordLayerClosure`; what moved is the arena (`ℝ` → `KSigma`),
the context type (`bornContext ψ` → `ContextField`), and the measure (`fibreTypicality` →
`epistemicMeasure p`). -/
structure GlobalRecordClosure (N : ℕ) (c : ContextField N) (p : LF4.CPN N) : Prop where
  /-- Within the context, distinct outcomes have mutually exclusive record events (P5). -/
  exclusive : ∀ (i j : Fin N) (t : OnticTime) (x : LF4.KSigma N),
    x ∈ (globalRecordSemantics N).event ⟨c, i, t⟩ →
    x ∈ (globalRecordSemantics N).event ⟨c, j, t⟩ → i = j
  /-- The ontic selection `globalOutcome` is the record. -/
  selection_is_record : ∀ (i : Fin N) (t : OnticTime) (x : LF4.KSigma N),
    globalOutcome c x = some i ↔ x ∈ (globalRecordSemantics N).event ⟨c, i, t⟩
  /-- Isolation on one record conditions the ontic state onto the outcome basin (P6). -/
  isolation_is_conditioning : ∀ (i : Fin N) (t : OnticTime),
    compatibleSet (globalRecordSemantics N) [⟨c, i, t⟩]
      = (globalRecordSemantics N).event ⟨c, i, t⟩
  /-- **Born meets the record:** the epistemic probability of the record event of outcome `i` is the
  rate the context assigns at `p`. -/
  born_typicality : ∀ (i : Fin N) (t : OnticTime),
    epistemicMeasure p ((globalRecordSemantics N).event ⟨c, i, t⟩)
      = ENNReal.ofReal (c.rate p i)
  /-- The record events cover `Σ` up to a null set. ★ On `ℝ` this had to be stated relative to
  `Ico 0 1`; here it is about the **whole space**, which has measure one. -/
  ae_total : ∀ t : OnticTime,
    epistemicMeasure p (univ \ ⋃ i, (globalRecordSemantics N).event ⟨c, i, t⟩) = 0

/-- **The global record-layer closure holds for every context and every preparation.** Each field is
discharged by its source lemma in `GlobalBasin.lean`. -/
theorem globalRecordClosure (c : ContextField N) (p : LF4.CPN N) :
    GlobalRecordClosure N c p where
  exclusive i j t x hi hj := (globalRecordSemantics N).exclusive c i j t x hi hj
  selection_is_record i _ x := globalOutcome_eq_some_iff c x i
  isolation_is_conditioning i t := by
    rw [compatibleSet_global_single, globalRecordSemantics_event]
  born_typicality i _ := globalBasin_prob c i p
  ae_total _ := globalBasin_ae_total c p

/-! ### The Born rule at the capstone -/

/-- **★★ The record-layer Born rule, from a context the preparation did not build.**

For the canonical moment-map context, the epistemic probability of the record event of outcome `i` at
preparation `ψ` is exactly `‖⟨eᵢ, ψ⟩‖²`. The record event `globalBasin (momentContext N) i` is the
same set for every `ψ`; only the epistemic measure moves.

This is `RecordLayerClosure.born_typicality`'s successor, with the preparation-indexing removed. ⚠️
Still kinematic: no `H_int(M)` produces these basins. -/
theorem globalRecordClosure_born (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin N) (t : OnticTime) :
    epistemicMeasure (Projectivization.mk ℂ ψ hψ0)
        ((globalRecordSemantics N).event ⟨momentContext N, i, t⟩)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) := by
  rw [globalRecordSemantics_event]
  exact globalBasin_born ψ hψ0 hψ i

end CSD.RecordLayer
