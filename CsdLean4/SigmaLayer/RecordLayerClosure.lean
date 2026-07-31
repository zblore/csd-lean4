/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreRecord

/-!
# SigmaLayer/RecordLayerClosure: the record-layer capstone bundle (MD-1, step 5)

**Category:** 7-SigmaLayer (the record layer — the closure-level statement).

The record-layer analog of `SigmaLayer/FiniteQMClosure.lean`: a single `Prop` bundle
`RecordLayerClosure` collecting exactly the record-layer facts that are GENUINELY PROVED for the
fibre-partition readout, discharged in one theorem `recordLayerClosure`. This is the **successor
readout** to the preparation-indexed `LF5/PointerOutcome.lean` (`vnPointerOutcome`) that the closure
currently carries: unlike that engine, here the outcome **probabilities are measurement-noncontextual**
(the Born weight of outcome `i` is `‖ψ i‖²`, depending only on `(eᵢ, ψ)`), while the record events are
a genuine postulate-P5 `RecordSemantics`.

The bundle certifies, on the fibre `Σ = ℝ` with the canonical typicality measure `fibreTypicality`,
for the Born context of a unit state `ψ`:

* `exclusive` — distinct outcomes have mutually exclusive record events (P5 exclusivity);
* `selection_is_record` — the ontic selection `fibreOutcome` *is* the record;
* `isolation_is_conditioning` — isolation on one record conditions the state onto the outcome cell (P6);
* `born_typicality` — the fibre typicality of the record event of outcome `i` is exactly `‖ψ i‖²`
  (the record-layer form of the Born rule);
* `ae_total` — the record events cover the fibre up to a null set (the readout is a.e. total).

## ⚠️ SUPERSEDED 2026-07-31 by `SigmaLayer/GlobalRecordClosure.lean`

This bundle remains **true and is not deprecated**, but it is no longer the record layer's best
statement. Two defects, both fixed by the successor:

* **The context is built from the preparation.** Every field here is stated for `bornContext ψ`, so
  the record *event* is `cdfCell (bornRate ψ)` and moves with `ψ`. Paper C A7 asks for regions fixed
  by the apparatus; `GlobalRecordClosure` uses a `ContextField` — a rate field on the ontic base —
  and its event `globalBasin c i` is the same set for every preparation, with only the epistemic
  measure moving.
* **The arena is `ℝ`.** `ℂℙⁿ⁻¹ × ℝ` has odd real dimension `2n-1`, so it admits no symplectic — hence
  no Kähler — structure, and cannot be a Paper C A1 surface. (This is a *parity* fact, not a Mathlib
  gap; see `specs/reconstruction-status.md` §2a.) The successor runs on the corpus's actual compact
  sector `KSigma = ℂℙⁿ⁻¹ × T²`, of even dimension `2n`.

The five closure fields are otherwise identical, which is the evidence that neither defect was ever
load-bearing for the record layer's *content*. `ae_total` also strengthens: here it must be stated
relative to `Ico 0 1` because Lebesgue measure on the line is infinite; there it is about the whole
space, which has measure one.

Kept rather than deleted because it is consumed and true. New work should cite the successor.

## Honest scope (what step 5 does and does not do)

This is the record-layer readout as a first-class, certified bundle — the replacement candidate for
`vnPointerOutcome`. It does **not** swap the readout inside `unifiedFiniteQMClosure`'s *proved* fields:
those are theorems on the `productDynamics` engine over `ℂℙ^M × T²` (`bornRegion`/`vnPointerOutcome`),
and re-deriving them on this fibre model is the open engine-migration work, not a mechanical edit.
Likewise the physical de-isolation flow generating the cells remains open (plan §3c / step 2b′). So
step 5 lands the successor and its closure-level statement; the full migration of `FiniteQMClosure`
onto it, and the flow behind it, stay open (MD-1). Foundational-triple, no `sorry`.

## References
`specs/record-layer-plan.md` (record layer, MD-1; step 5); `SigmaLayer/FibreRecord.lean`
(the `RecordSemantics` instance); `SigmaLayer/DeIsolationFlow.lean` (`fibreTypicality`,
`fibreTypicality_uncovered`); `SigmaLayer/FiniteQMClosure.lean` (the closure this parallels, and whose
`vnPointerOutcome` readout this succeeds).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ}

/-- **The record-layer closure bundle (MD-1).** The record-layer facts genuinely proved for the
fibre-partition readout of a unit state `ψ`, collected into one `Prop` and discharged by
`recordLayerClosure`. The successor to the preparation-indexed `vnPointerOutcome` readout: the outcome
probabilities are measurement-noncontextual (`born_typicality`) and the records are a first-class
postulate-P5 `RecordSemantics`. -/
structure RecordLayerClosure (n : ℕ) (ψ : EuclideanSpace ℂ (Fin n)) : Prop where
  /-- Within the Born context, distinct outcomes have mutually exclusive record events (P5). -/
  exclusive : ∀ (i j : Fin n) (t : OnticTime) (ξ : ℝ),
    ξ ∈ (fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩ →
    ξ ∈ (fibreRecordSemantics n).event ⟨bornContext ψ, j, t⟩ → i = j
  /-- The ontic selection `fibreOutcome` is the record: it reads `i` exactly on the record event. -/
  selection_is_record : ∀ (i : Fin n) (t : OnticTime) (ξ : ℝ),
    fibreOutcome (bornContext ψ).rate ξ = some i ↔
      ξ ∈ (fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩
  /-- Isolation on one record conditions the ontic state onto the outcome cell (P6). -/
  isolation_is_conditioning : ∀ (i : Fin n) (t : OnticTime),
    compatibleSet (fibreRecordSemantics n) [⟨bornContext ψ, i, t⟩]
      = (fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩
  /-- **Born meets the record:** the fibre typicality of the record event of outcome `i` is `‖ψ i‖²`. -/
  born_typicality : ∀ (i : Fin n) (t : OnticTime),
    fibreTypicality ((fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩)
      = ENNReal.ofReal (‖ψ i‖ ^ 2)
  /-- The record events cover the fibre up to a null set: the readout is a.e. total. -/
  ae_total : ∀ t : OnticTime,
    fibreTypicality (Ico (0 : ℝ) 1 \ ⋃ i, (fibreRecordSemantics n).event ⟨bornContext ψ, i, t⟩) = 0

/-- **The record-layer closure holds for every unit state.** Each field is discharged by its source
lemma in `FibreRecord.lean` / `DeIsolationFlow.lean` — the record-layer readout is a certified bundle,
the successor to the preparation-indexed `vnPointerOutcome`. -/
theorem recordLayerClosure (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    RecordLayerClosure n ψ where
  exclusive i j t ξ hi hj := (fibreRecordSemantics n).exclusive (bornContext ψ) i j t ξ hi hj
  selection_is_record i t ξ := fibreOutcome_eq_record (bornContext ψ) i t ξ
  isolation_is_conditioning i t := by
    rw [compatibleSet_fibre_single, fibreRecordSemantics_event]
  born_typicality i t := fibreTypicality_bornRecord ψ hψ i t
  ae_total _ := fibreTypicality_uncovered ψ hψ

end CSD.RecordLayer
