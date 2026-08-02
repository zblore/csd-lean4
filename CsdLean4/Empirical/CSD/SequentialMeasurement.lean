/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.SwapLuders
public import CsdLean4.SigmaLayer.DegenerateLuders

/-!
# Empirical/CSD/SequentialMeasurement: repeatability and sequential Born, from the dynamics

**Category:** CSD-ontic empirical (the first entry consuming the v0.7.0–v1.0.0 dynamical
measurement layer).

## What this tests

Every other entry in the empirical suite exercises the *kinematic* Born machinery — volumes,
partitions, bridge transports. This one exercises the **measurement dynamics**: the calibrated-swap
witness, in which a record is *created* by an explicit measure-preserving propagator and the
post-measurement state is a pushforward theorem (`swap_luders_born`). Two textbook empirical facts
fall out, now as consequences of the dynamics rather than as separate posits:

* **Repeatability** (`csd_repeatability`): measure in the computational basis, obtain outcome `i`,
  measure again in the *same* basis — the same outcome recurs with probability `1`, any other with
  probability `0`. Von Neumann's "a repeated measurement gives the same result", derived from the
  swap dynamics plus `momentMap_vertex` (the moment map at a vertex is its indicator).
* **Sequential Born** (`csd_sequential_born`): after outcome `i`, the follow-up statistics for
  **any** context field `c'` are the *collapsed state's* Born weights `c'.rate [eᵢ]` — not the
  preparation's. This is the empirically loaded content of the Lüders update: the second
  measurement sees `[eᵢ]`, and the original `ψ` is gone from the statistics.

## ⚠️ Honest scope

* Rank-one, computational-basis first measurement — the scope of the swap witness
  (`SwapLuders.lean`); degenerate first measurements are the recorded open construction
  (`DegenerateLuders.lean`).
* `hpos` (the first outcome has nonzero probability) is carried as a hypothesis: conditioning on a
  null outcome is undefined, as it should be. *(Upgrade 2026-08-02:)* for the **canonical ready
  preparation** `readyPrep p = epistemicMeasure p ⊗ readyMeasure N`, `prep_outcome_pos` proves
  `hpos` outright whenever the Born weight `momentMap p i` is nonzero — the preparation itself
  licenses the conditioning.
* These are theorems about the witness dynamics, inheriting the witness's own scope notes
  (calibration is a context-fixed posit; Hamiltonian origin of the propagator is §2a-scoped).

## References

`SigmaLayer/SwapLuders.lean` (`swap_luders_born` — the engine);
`SigmaLayer/DegenerateLuders.lean` (`momentMap_vertex`);
`SigmaLayer/RecordPersistence.lean` (`readout_persists_on_interval` — the *pointer-level*
repeatability this complements at the *state* level); `EMPIRICAL.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.CSDBridge.SequentialMeasurement

open CSD.RecordLayer

variable {N : ℕ} [NeZero N]

/-- The post-measurement ensemble of the calibrated-swap witness, given outcome `i` from a
computational-basis measurement on system-and-register state `μ12` with vertex-calibrated bank. -/
noncomputable def postEnsemble (μ12 : Measure (LF4.KSigma N × LF4.KTorus)) (i : Fin N) :
    Measure (SwapArena (LF4.KSigma N) N) :=
  (swapProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).postMeasure
    (μ12.prod (Measure.pi fun k => epistemicMeasure (vertexPoint k))) i

/-- **★ Sequential Born: the second measurement sees the collapsed state.** After outcome `i`, the
follow-up outcome-`j` probability for **any** context field `c'` is the Born weight of `[eᵢ]` — the
preparation `ψ` has left the statistics entirely. The Lüders update as an empirical prediction,
derived from the swap dynamics. -/
theorem csd_sequential_born (μ12 : Measure (LF4.KSigma N × LF4.KTorus))
    [IsProbabilityMeasure μ12] (i : Fin N)
    (hpos : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0)
    (c' : ContextField N) (j : Fin N) :
    postEnsemble μ12 i
        ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) :=
  swap_luders_born μ12 i hpos c' j

/-- **★★ Repeatability: a repeated measurement gives the same result.** Measure in the
computational basis, record outcome `i`, measure again in the same basis: outcome `i` recurs with
probability `1` and any other outcome has probability `0`. Derived — the follow-up context's rate
at the collapsed vertex is the vertex's indicator (`momentMap_vertex`). -/
theorem csd_repeatability (μ12 : Measure (LF4.KSigma N × LF4.KTorus))
    [IsProbabilityMeasure μ12] (i : Fin N)
    (hpos : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0)
    (j : Fin N) :
    postEnsemble μ12 i
        ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin (momentContext N) j)
      = if j = i then 1 else 0 := by
  rw [csd_sequential_born μ12 i hpos (momentContext N) j, momentContext_rate,
    momentMap_vertex]
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- The two halves of repeatability, spelled out: certainty on the recorded outcome… -/
theorem csd_repeatability_same (μ12 : Measure (LF4.KSigma N × LF4.KTorus))
    [IsProbabilityMeasure μ12] (i : Fin N)
    (hpos : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0) :
    postEnsemble μ12 i
        ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin (momentContext N) i)
      = 1 := by
  rw [csd_repeatability μ12 i hpos i, if_pos rfl]

/-- …and impossibility of every other outcome. -/
theorem csd_repeatability_other (μ12 : Measure (LF4.KSigma N × LF4.KTorus))
    [IsProbabilityMeasure μ12] (i : Fin N)
    (hpos : μ12 ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector i) ≠ 0)
    {j : Fin N} (hj : j ≠ i) :
    postEnsemble μ12 i
        ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin (momentContext N) j)
      = 0 := by
  rw [csd_repeatability μ12 i hpos j, if_neg hj]

/-! ### The canonical ready preparation, and `hpos` as a theorem -/

/-- The canonical sequential-round preparation: system at the ontic point `p`, register in the
ready arc. This is the preparation `swapPostMarg` conditions (`DegenerateLuders.lean`), exposed
for the empirical entries. -/
noncomputable def readyPrep (p : LF4.CPN N) : Measure (LF4.KSigma N × LF4.KTorus) :=
  (epistemicMeasure p).prod (readyMeasure N)

instance (p : LF4.CPN N) : IsProbabilityMeasure (readyPrep p) := by
  unfold readyPrep
  infer_instance

/-- **`hpos` is a theorem for the canonical ready preparation.** The outcome-`i` sector has
nonzero measure whenever the Born weight `momentMap p i` is nonzero: the selector-and-ready set
sits inside the sector (`shear_correlates`) and factors as (basin fibre) × (ready arc), both of
nonzero measure. Generalises `vertex_outcome_pos` from vertex preparations to arbitrary ones —
so `csd_sequential_born`/`csd_repeatability` need no carried hypothesis at a concrete
preparation. -/
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
    rw [readyMeasure, ProbabilityTheory.cond_apply measurableSet_readyArc, Set.inter_self]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) volume_readyArc_ne_zero
  intro h0
  have hle : readyPrep p (selReady (basinIndex (momentContext N)) i)
      ≤ readyPrep p
        ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector i) :=
    measure_mono hsub
  rw [h0, le_zero_iff, hprod, readyPrep, Measure.prod_prod] at hle
  exact absurd hle (mul_ne_zero hbase hready)

end CSD.Empirical.CSDBridge.SequentialMeasurement
