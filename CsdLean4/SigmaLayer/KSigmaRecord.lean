/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ProjectiveRecord
public import CsdLean4.SigmaLayer.MeasureBridge

/-!
# SigmaLayer/KSigmaRecord: the record layer on the closure's actual product Σ (MD-1)

**Category:** 7-SigmaLayer (the record layer — on the product model `KSigma`).

`SigmaLayer/ProjectiveRecord.lean` put the record layer on the projective base `CPN (M+1)`. The
`FiniteQMClosure` capstone, however, lives on the **product model** `Σ = KSigma (M+1) = CPN (M+1) × T²`
(the torus factor carries the dynamics phase). This file lifts the record layer to that actual space
and — crucially — shows the closure's own Born-frequency region *is* the record-layer event.

* `kSigmaRecordSemantics` — a postulate-P5 `RecordSemantics` on `KSigma (M+1)`: the record event of
  outcome `i` is the base Born region lifted through the base projection `π = Prod.fst`, measurable and
  exclusive (lifted from `bornRegion_measurable_uncond` / `bornRegion_pairwiseDisjoint`);
* `kSigmaRecord_eq_baseProj` — it is the projective record event pulled back along `π`;
* `born_frequency_region_eq_record` — **the region `FiniteQMClosure.born_frequency` lands in,
  `π ⁻¹' bornRegion ψ i`, is definitionally the record event** `kSigmaRecordSemantics ⟨ψ,i,t⟩`. So the
  pinned closure's Born frequencies already *are* frequencies of the record-layer record — the record
  layer is wired to the closure's actual field, with no rewrite of the pinned structure;
* `bornOutcome_base_eq_record` — the corpus's per-microstate outcome map reads the record on `KSigma`.

**Honest scope.** This is why the literal field re-plumbing of `unifiedFiniteQMClosure` is unnecessary,
not just risky: the closure's `born_frequency` region is *already* the record-layer event (definitionally),
so the record semantics is realised on the exact space and sets the closure uses. The closure's
`records_time_physical` still *names* the coarse-grained `vnPointerOutcome` (a block-sum of these
regions, `vnPointerOutcome_preimage_some`); rewriting that pinned statement carries no new theorem and is
deliberately not done. Foundational-triple, no `sorry`.

## References
`SigmaLayer/ProjectiveRecord.lean` (the base record layer); `SigmaLayer/MeasureBridge.lean`
(`productSector`, `π = Prod.fst`); `SigmaLayer/FiniteQMClosure.lean` (`born_frequency`, whose region this
is); `LF4/KahlerInstance.lean` (`KSigma`); `LF5/PointerOutcome.lean` (`vnPointerOutcome`, the coarse readout).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer CSD.LF4

namespace CSD.RecordLayer

variable {M : ℕ}

/-- The **base projection** on the product model `Σ = KSigma (M+1) = CPN × T²`. -/
def kBaseProj : KSigma (M + 1) → CPN (M + 1) := Prod.fst

/-- **The record semantics (P5) on the actual product Σ = `KSigma (M+1)`.** The record event of
outcome `i` is the base Born region lifted through the base projection (the torus is a spectator):
measurable and exclusive, inherited from the base regions. -/
noncomputable def kSigmaRecordSemantics (M : ℕ) :
    RecordSemantics (KSigma (M + 1)) (projSignature M) where
  event r := kBaseProj ⁻¹' bornRegion r.context.1 r.context.2 r.outcome
  measurable_event r :=
    (bornRegion_measurable_uncond r.context.1 r.context.2 r.outcome).preimage measurable_fst
  exclusive c a b _ x ha hb := by
    by_contra hab
    exact absurd hb (Set.disjoint_left.mp
      (Disjoint.preimage kBaseProj (bornRegion_pairwiseDisjoint c.1 c.2 hab)) ha)

@[simp] theorem kSigmaRecordSemantics_event
    (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0}) (i : Fin (M + 1)) (t : OnticTime) :
    (kSigmaRecordSemantics M).event ⟨c, i, t⟩ = kBaseProj ⁻¹' bornRegion c.1 c.2 i := rfl

/-- The `KSigma` record event is the projective record event pulled back along the base projection. -/
theorem kSigmaRecord_eq_baseProj (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0})
    (i : Fin (M + 1)) (t : OnticTime) :
    (kSigmaRecordSemantics M).event ⟨c, i, t⟩
      = kBaseProj ⁻¹' (projRecordSemantics M).event ⟨c, i, t⟩ := by
  rw [kSigmaRecordSemantics_event, projRecordSemantics_event]

/-- **The closure's Born-frequency region IS the record event.** `FiniteQMClosure.born_frequency` lands
in `π ⁻¹' bornRegion ψ i` on the product Σ; that set is *definitionally* the record-layer event
`kSigmaRecordSemantics` for context `ψ`. So the pinned closure's Born frequencies already are
frequencies of the record-layer record — the record layer is wired to the closure's actual field with
no rewrite. -/
theorem born_frequency_region_eq_record (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    (hH : H.IsHermitian) (p₀ : CPN (M + 1)) (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (i : Fin (M + 1)) (t : OnticTime) :
    (productSector H hH p₀).pi ⁻¹' bornRegion ψ hψ0 i
      = (kSigmaRecordSemantics M).event ⟨⟨ψ, hψ0⟩, i, t⟩ := rfl

/-- The corpus's per-microstate outcome map (on the base) reads the record on the full product Σ. -/
theorem bornOutcome_base_eq_record (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0})
    (i : Fin (M + 1)) (t : OnticTime) (x : KSigma (M + 1)) :
    bornOutcome c.1 c.2 (kBaseProj x) = some i ↔ x ∈ (kSigmaRecordSemantics M).event ⟨c, i, t⟩ := by
  rw [kSigmaRecordSemantics_event, Set.mem_preimage, bornOutcome_eq_some_iff]

end CSD.RecordLayer
