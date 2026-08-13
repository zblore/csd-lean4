/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DynamicMeasurementClosure
public import CsdLean4.RecordLayer.DegenerateLuders

/-!
# SigmaLayer/SwapClosure: all six dynamical facts on ONE arena

**Category:** 7-SigmaLayer (the record layer — arena unification, step 1 of 2).

## Why

`DynamicMeasurementClosure` was honest about a split: its ready/record/persistence/Born fields
were **shear**-protocol statements on `Σ_sel × T²_R`, while its Lüders field was a
**swap**-protocol statement on the bank-augmented `SwapArena`. The external review (2026-08-02)
correctly listed "package all six facts on the swap arena alone" as the precursor to the engine
migration. This module does that:

* `SwapMeasurementClosure` — ready ⇒ no record, record created, outcomes exclusive, record
  persists, **dynamical Born sector weights**, and the rank-one Lüders update — every field a
  statement about `swapProtocol` on `SwapArena`, at one canonical preparation.
* `swapMeasurementClosure` — discharged, for every state, with `CorrelatesOn` /
  `PointerInvariantOn` **proved** (`swap_correlates`, `swap_pointerInvariant`), not assumed.

Two genuine upgrades over the shear-side bundle, beyond the arena move:

* **`sector_born` is the dynamical Born, not the kinematic selector Born**: the measure of the
  *outcome sector* (initial states destined for record `i`) equals the Born weight — via
  `measure_outcomeSector_eq_of_correlates`, so the correlation theorem is genuinely consumed.
* **`luders_followup` carries no `hpos` hypothesis about the measure** — positivity of the Born
  weight itself licenses the conditioning (`prep_outcome_pos`, moved here from the empirical
  layer, where it was born one layer too high).

## What remains for the engine migration (step 2, recorded)

The **operational** closure (`FiniteQMClosure`) still lives on `productDynamics` over
`ℂℙ^M × T²`. `CsdFiniteQMClosure` remains a conjunction over two arenas; this module removes
the split *within* the dynamical bundle only. See `specs/BACKLOG.md`.

## References

`SigmaLayer/DynamicMeasurementClosure.lean` (the predecessor bundle, untouched);
`SigmaLayer/SwapWitness.lean` (`swapProtocol`, `selReadyBank`, `swap_correlates`,
`swap_pointerInvariant`); `SigmaLayer/SwapLuders.lean` (`swap_luders_born`);
`SigmaLayer/MeasurementProtocol.lean` (`measure_outcomeSector_eq_of_correlates`);
`SigmaLayer/DynamicBorn.lean` (`basinIndex`, `measure_basinIndex_fibre`);
`Empirical/CSD/SequentialMeasurement.lean` (the empirical consumer); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ} [NeZero N]

/-! ### The canonical preparation and its bank -/

/-- The canonical sequential-round preparation: system at the ontic point `p`, register in the
ready arc. (Moved from `Empirical/CSD/SequentialMeasurement.lean`, 2026-08-02 — it is
`SigmaLayer` machinery.) -/
noncomputable def readyPrep (p : LF4.CPN N) : Measure (LF4.KSigma N × LF4.KTorus) :=
  (epistemicMeasure p).prod (readyMeasure N)

instance (p : LF4.CPN N) : IsProbabilityMeasure (readyPrep p) := by
  unfold readyPrep
  infer_instance

/-- The vertex-calibrated ancilla bank of the swap witness. -/
noncomputable def calibratedBank (N : ℕ) [NeZero N] : Measure (Fin N → LF4.KSigma N) :=
  Measure.pi fun k => epistemicMeasure (vertexPoint k)

instance : IsProbabilityMeasure (calibratedBank N) := by
  unfold calibratedBank
  infer_instance

/-- The full swap-arena preparation: system-and-register at `readyPrep p`, bank calibrated. -/
noncomputable def swapPrep (p : LF4.CPN N) : Measure (SwapArena (LF4.KSigma N) N) :=
  (readyPrep p).prod (calibratedBank N)

instance (p : LF4.CPN N) : IsProbabilityMeasure (swapPrep p) := by
  unfold swapPrep
  infer_instance

/-! ### `hpos` as a theorem (moved from the empirical layer) -/

/-- The ready arc has full conditional measure. -/
lemma readyMeasure_readyArc (K : ℕ) : readyMeasure K (readyArc K) = 1 := by
  rw [readyMeasure, ProbabilityTheory.cond_apply measurableSet_readyArc, Set.inter_self,
    ENNReal.inv_mul_cancel volume_readyArc_ne_zero (measure_ne_top _ _)]

/-- **`hpos` is a theorem for the canonical ready preparation.** The outcome-`i` sector has
nonzero measure whenever the Born weight `momentMap p i` is nonzero: the selector-and-ready set
sits inside the sector (`shear_correlates`) and factors as (basin fibre) × (ready arc), both of
nonzero measure. Generalises `vertex_outcome_pos`. (Moved from
`Empirical/CSD/SequentialMeasurement.lean`, 2026-08-02.) -/
theorem prep_outcome_pos (p : LF4.CPN N) (i : Fin N) (hpos : LF4.momentMap p i ≠ 0) :
    readyPrep p
      ((shearProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0 := by
  classical
  have hsub : selReady (basinIndex (momentContext N)) i
      ⊆ (shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector i :=
    shear_correlates (basinIndex (momentContext N)) (measurable_basinIndex (momentContext N)) i
  have hprod : selReady (basinIndex (momentContext N)) i
      = {x : LF4.KSigma N | basinIndex (momentContext N) x = i} ×ˢ readyArc N := by
    ext x
    simp [selReady, Set.mem_prod]
  have hbase : epistemicMeasure p {x : LF4.KSigma N | basinIndex (momentContext N) x = i}
      ≠ 0 := by
    have hset : {x : LF4.KSigma N | basinIndex (momentContext N) x = i}
        = basinIndex (momentContext N) ⁻¹' {i} := rfl
    rw [hset, measure_basinIndex_fibre, globalBasin_prob, momentContext_rate]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_le_of_ne (LF4.momentMap_nonneg p i) (Ne.symm hpos)
  have hready : readyMeasure N (readyArc N) ≠ 0 := by
    rw [readyMeasure_readyArc]
    exact one_ne_zero
  intro h0
  have hle : readyPrep p (selReady (basinIndex (momentContext N)) i)
      ≤ readyPrep p
        ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector i) :=
    measure_mono hsub
  rw [h0, le_zero_iff, hprod, readyPrep, Measure.prod_prod] at hle
  exact absurd hle (mul_ne_zero hbase hready)

/-! ### The selector-and-ready-and-bank partition, measured -/

lemma measurableSet_selReadyBank (c : ContextField N) (i : Fin N) :
    MeasurableSet (selReadyBank (basinIndex c) i) := by
  show MeasurableSet
    ((fun x : SwapArena (LF4.KSigma N) N => basinIndex c x.1.1) ⁻¹' {i}
      ∩ (fun x : SwapArena (LF4.KSigma N) N => x.1.2) ⁻¹' readyArc N)
  exact (((measurable_basinIndex c).comp (measurable_fst.comp measurable_fst))
      (measurableSet_singleton i)).inter
    ((measurable_snd.comp measurable_fst) measurableSet_readyArc)

lemma selReadyBank_pairwiseDisjoint (c : ContextField N) :
    Pairwise (Function.onFun Disjoint (selReadyBank (basinIndex c))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
  exact hij (hxi ▸ hxj ▸ rfl)

/-- The canonical preparation weights the selector-and-ready-and-bank set with exactly the Born
weight. -/
lemma swapPrep_selReadyBank (p : LF4.CPN N) (i : Fin N) :
    swapPrep p (selReadyBank (basinIndex (momentContext N)) i)
      = ENNReal.ofReal (LF4.momentMap p i) := by
  have h1 : selReadyBank (basinIndex (momentContext N)) i
      = (({x : LF4.KSigma N | basinIndex (momentContext N) x = i} ×ˢ readyArc N)
          ×ˢ (univ : Set (Fin N → LF4.KSigma N))) := by
    ext x
    simp [selReadyBank, Set.mem_prod]
  rw [swapPrep, readyPrep, h1, Measure.prod_prod, Measure.prod_prod]
  have hset : {x : LF4.KSigma N | basinIndex (momentContext N) x = i}
      = basinIndex (momentContext N) ⁻¹' {i} := rfl
  rw [hset, measure_basinIndex_fibre, globalBasin_prob, momentContext_rate,
    readyMeasure_readyArc, measure_univ, mul_one, mul_one]

lemma swapPrep_selReadyBank_cover (p : LF4.CPN N) :
    ∑ i, swapPrep p (selReadyBank (basinIndex (momentContext N)) i) = 1 := by
  simp_rw [swapPrep_selReadyBank]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => LF4.momentMap_nonneg p i),
    LF4.momentMap_sum_eq_one, ENNReal.ofReal_one]

/-! ### The dynamical Born on the swap arena -/

/-- **★ The dynamical Born weight, on the swap arena.** The measure of the outcome-`i` sector —
the initial states *destined* to display record `i` — equals the Born weight `momentMap p i`,
for every preparation. Proved through `measure_outcomeSector_eq_of_correlates`, so the
correlation theorem (`swap_correlates`) is genuinely consumed: this is Born as a *consequence of
the dynamics*, stated where the Lüders update also lives. -/
theorem swap_sector_born (p : LF4.CPN N) (i : Fin N) :
    swapPrep p
      ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector i)
      = ENNReal.ofReal (LF4.momentMap p i) := by
  rw [(swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).measure_outcomeSector_eq_of_correlates
    (measurableSet_selReadyBank (momentContext N))
    (selReadyBank_pairwiseDisjoint (momentContext N))
    (swapPrep_selReadyBank_cover p)
    (swap_correlates (basinIndex (momentContext N)) (measurable_basinIndex (momentContext N)))
    i]
  exact swapPrep_selReadyBank p i

/-! ### The closure: six facts, one arena, one preparation -/

/-- **The swap-arena measurement closure.** The six dynamical facts, every one a statement
about `swapProtocol` on `SwapArena` at the canonical preparation `swapPrep [ψ]` — the
single-arena bundle `DynamicMeasurementClosure` could not honestly be. -/
structure SwapMeasurementClosure (N : ℕ) [NeZero N]
    (ψ : EuclideanSpace ℂ (Fin N)) : Prop where
  /-- **Ready ⇒ no record.** -/
  ready_no_record : ∀ x : SwapArena (LF4.KSigma N) N, x.1.2 ∈ readyArc N →
    (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout x = none
  /-- **A record is created**, and it is the outcome the hidden selector had fixed. -/
  record_created : ∀ (i : Fin N) (x : SwapArena (LF4.KSigma N) N),
    x ∈ selReadyBank (basinIndex (momentContext N)) i →
    (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout
        ((swapProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).evolve 0 1 x) = some i
  /-- Distinct outcomes are exclusive. -/
  outcomes_exclusive : Pairwise (Function.onFun Disjoint
    (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector)
  /-- **The record persists** across the operational window. -/
  record_persists : ∀ (i : Fin N) (x : SwapArena (LF4.KSigma N) N) (t : CSD.SigmaLayer.OnticTime),
    x ∈ (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i →
    1 ≤ t → t ≤ 1 + 1 →
    (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).readout
        ((swapProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).evolve 0 t x) = some i
  /-- **★ The dynamical Born**: the outcome sector's measure is the Born weight. -/
  sector_born : ∀ (hψ0 : ψ ≠ 0), ‖ψ‖ = 1 → ∀ i : Fin N,
    swapPrep (Projectivization.mk ℂ ψ hψ0)
      ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector i)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
  /-- **★ The rank-one Lüders update**, with the conditioning licensed by the Born weight
  itself — no measure-positivity hypothesis. -/
  luders_followup : ∀ (hψ0 : ψ ≠ 0) (i : Fin N),
    LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i ≠ 0 →
    ∀ (c' : ContextField N) (j : Fin N),
    ((swapProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).postMeasure
      (swapPrep (Projectivization.mk ℂ ψ hψ0)) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j)

/-- **★ The swap-arena closure holds** — for every state, with `CorrelatesOn` and
`PointerInvariantOn` proved of the constructed propagator, never assumed. -/
theorem swapMeasurementClosure (ψ : EuclideanSpace ℂ (Fin N)) :
    SwapMeasurementClosure N ψ where
  ready_no_record _ hx :=
    (swapProtocol _ _).readout_ready_eq_none hx
  record_created i _ hx :=
    (swapProtocol _ _).readout_evolve_outcomeSector
      (swap_correlates (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N)) i hx)
  outcomes_exclusive := (swapProtocol _ _).outcomeSector_pairwiseDisjoint
  record_persists _ _ _ hx ht₁ ht₂ :=
    (swapProtocol _ _).readout_persists_on_interval
      (swap_pointerInvariant _ _) hx ht₁ ht₂
  sector_born hψ0 hψ i := by
    rw [swap_sector_born, LF4.momentMap_mk_eq_inner_sq ψ hψ0 hψ i]
  luders_followup hψ0 i hpos c' j :=
    swap_luders_born (readyPrep (Projectivization.mk ℂ ψ hψ0)) i
      (prep_outcome_pos (Projectivization.mk ℂ ψ hψ0) i hpos) c' j

end CSD.RecordLayer
