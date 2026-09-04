/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.RecordedFact
public import CsdLean4.LF4.BornRegionDisjoint
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF1.GeneralFrequency
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy

/-!
# SigmaLayer/ProjectiveRecord: the record layer on the actual projective Σ (MD-1, migration)

**Category:** 7-SigmaLayer (the record layer — realised on the corpus's real model).

The record-layer framing of `RecordLayer/FibreRecord.lean` was built on an abstract fibre `Σ = ℝ`. This
file **migrates it onto the corpus's actual measurement model**: the projective space
`Σ = CPN (M+1) = ℂℙ^M`, with the corpus's own outcome regions `bornRegion` (`LF4/BornRegionDisjoint`),
its per-microstate outcome map `bornOutcome`, and the Fubini–Study measure `fubiniStudyMeasure` — the
exact objects `FiniteQMClosure.born_frequency` is stated with. So the record layer is no longer a
parallel construction; it is instantiated on the real Σ with the real Born machinery.

What is delivered, foundational-triple, no `sorry`:

* `projRecordSemantics` — a genuine postulate-P5 `RecordSemantics` on `CPN (M+1)`: the record event of
  "context `⟨ψ,·⟩` recorded outcome `i`" is `bornRegion ψ i`, **measurable** (`bornRegion_measurable_uncond`)
  and **exclusive** within a context (`bornRegion_pairwiseDisjoint`);
* `bornOutcome_eq_record` — the corpus's per-microstate outcome map `bornOutcome` *is* the record: it
  reads `i` exactly on the record event (via `bornOutcome_eq_some_iff`);
* `compatibleSet_proj_single` — isolation on one record conditions the ontic state onto the born region
  (the P6 story on the real Σ);
* `fubiniStudy_projRecord` — the FS typicality of the record event of outcome `i` is exactly `‖⟨eᵢ,ψ⟩‖²`
  (`bornRegion_fs_measure_uncond`): Born as the ontic typicality of the record event;
* `projRecord_frequency` — **Born as the law of large numbers over the unknown microstate, on the real
  Σ**: for i.i.d. FS-typical microstates, the frequency of trials whose microstate lands in the record
  event of `i` converges a.s. to `‖⟨eᵢ,ψ⟩‖²` (via `freq_tendsto_of_iid` + `bornRegion_fs_measure_uncond`).
  This is the exact `FiniteQMClosure.born_frequency` conclusion, now carried by the record-layer
  `RecordSemantics` rather than the ad-hoc `vnPointerOutcome` readout.

**Honest scope.** This connects the record-layer interface to the corpus's real model and its Born
machinery — the substantive content of "retiring `vnPointerOutcome`". It does *not* rewrite the field
wiring of `unifiedFiniteQMClosure` (that re-plumbing carries no new theorem); the closure's
`records_time_physical` still names `vnPointerOutcome`, and this file supplies the record-layer
realisation the closure's MD-1 docstring points at. The regions `bornRegion ψ` remain the corpus's
preparation-indexed cells; the probabilities are the moment map (see `MomentMapRace`), and the
statistics are LLN over the unknown microstate.

## References
`SigmaLayer/RecordedFact.lean` (`RecordSemantics`, `compatibleSet`, P5/P6); `LF4/BornRegionDisjoint.lean`
(`bornRegion`, `bornRegion_pairwiseDisjoint`, `bornOutcome`, `bornOutcome_eq_some_iff`);
`LF4/BornRegionUncond.lean` (`bornRegion_measurable_uncond`, `bornRegion_fs_measure_uncond`);
`LF1/GeneralFrequency.lean` (`freq_tendsto_of_iid`); `RecordLayer/FibreRecord.lean` (the abstract-fibre
version this migrates); `SigmaLayer/FiniteQMClosure.lean` (`born_frequency`, whose conclusion this matches).
-/

@[expose] public section

open MeasureTheory Set Matrix.UnitaryGroup
open CSD.SigmaLayer CSD.LF4

namespace CSD.RecordLayer

variable {M : ℕ}

/-- The **projective record signature (P5 data)**: a context is a nonzero preparation/measurement
reference state `ψ` (fixing the born regions); outcomes are `Fin (M+1)`. -/
def projSignature (M : ℕ) : RecordSignature where
  Context := {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0}
  Outcome := fun _ => Fin (M + 1)

/-- **The record semantics (P5) on the actual projective Σ = `CPN (M+1)`.** The ontic event of
"context `ψ` recorded outcome `i`" is the corpus's own Born region `bornRegion ψ i`: measurable
(`bornRegion_measurable_uncond`), and exclusive within a context — a microstate cannot lie in two Born
cells (`bornRegion_pairwiseDisjoint`). The corpus's measurement readout as a first-class record. -/
noncomputable def projRecordSemantics (M : ℕ) : RecordSemantics (CPN (M + 1)) (projSignature M) where
  event r := bornRegion r.context.1 r.context.2 r.outcome
  measurable_event r := bornRegion_measurable_uncond r.context.1 r.context.2 r.outcome
  exclusive c a b _ x ha hb := by
    by_contra hab
    exact absurd hb (Set.disjoint_left.mp (bornRegion_pairwiseDisjoint c.1 c.2 hab) ha)

@[simp] theorem projRecordSemantics_event (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0})
    (i : Fin (M + 1)) (t : OnticTime) :
    (projRecordSemantics M).event ⟨c, i, t⟩ = bornRegion c.1 c.2 i := rfl

/-- **The corpus's outcome map is the record.** `bornOutcome` reads outcome `i` at a microstate exactly
when the microstate lies in the record event `⟨c, i, t⟩`. -/
theorem bornOutcome_eq_record (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0})
    (i : Fin (M + 1)) (t : OnticTime) (p : CPN (M + 1)) :
    bornOutcome c.1 c.2 p = some i ↔ p ∈ (projRecordSemantics M).event ⟨c, i, t⟩ := by
  rw [projRecordSemantics_event]
  exact bornOutcome_eq_some_iff c.1 c.2 p i

/-- Isolation on one record conditions the ontic state onto the Born region (P6). -/
theorem compatibleSet_proj_single (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0})
    (i : Fin (M + 1)) (t : OnticTime) :
    compatibleSet (projRecordSemantics M) [⟨c, i, t⟩] = bornRegion c.1 c.2 i := by
  rw [compatibleSet_cons, compatibleSet_nil, Set.inter_univ, projRecordSemantics_event]

/-- **Born meets the record, on the real Σ.** For a unit state the Fubini–Study typicality of the
record event of outcome `i` is exactly `‖⟨eᵢ, ψ⟩‖²` (`bornRegion_fs_measure_uncond`). -/
theorem fubiniStudy_projRecord (p₀ : CPN (M + 1))
    (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0}) (hψ : ‖c.1‖ = 1) (i : Fin (M + 1))
    (t : OnticTime) :
    (fubiniStudyMeasure p₀ ((projRecordSemantics M).event ⟨c, i, t⟩)).toReal
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) c.1‖ ^ 2 := by
  rw [projRecordSemantics_event]
  exact bornRegion_fs_measure_uncond p₀ c.1 c.2 hψ i

/-- **Born as the law of large numbers over the unknown microstate, on the actual projective Σ.** For
i.i.d. FS-typical microstates `X k` (law `fubiniStudyMeasure p₀`), the frequency of trials whose
microstate lands in the record event of outcome `i` converges almost surely to `‖⟨eᵢ, ψ⟩‖²` — the exact
`FiniteQMClosure.born_frequency` conclusion, carried by the record-layer `RecordSemantics`. The whole
probabilistic content is the strong law over the unknown initial condition. -/
theorem projRecord_frequency (p₀ : CPN (M + 1))
    (c : {ψ : EuclideanSpace ℂ (Fin (M + 1)) // ψ ≠ 0}) (hψ : ‖c.1‖ = 1) (i : Fin (M + 1))
    (t : OnticTime) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ k, Measurable (X k))
    (hlaw : ∀ k, Measure.map (X k) P = fubiniStudyMeasure p₀)
    (hindep : Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g P)
      (fun k => Set.indicator (X k ⁻¹' (projRecordSemantics M).event ⟨c, i, t⟩)
        (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P, Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N,
        Set.indicator (X k ⁻¹' (projRecordSemantics M).event ⟨c, i, t⟩) (fun _ => (1 : ℝ)) ω)
          / (N : ℝ))
      Filter.atTop (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) c.1‖ ^ 2)) := by
  have h := CSD.LF1.freq_tendsto_of_iid hX hlaw
    ((projRecordSemantics M).measurable_event ⟨c, i, t⟩) hindep
  rwa [fubiniStudy_projRecord p₀ c hψ i t] at h

end CSD.RecordLayer
