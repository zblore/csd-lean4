/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapClosure
public import CsdLean4.RecordLayer.MomentMapRace

/-!
# SigmaLayer/ShearDeIsolation: the de-isolation interaction of the constructed flow

**Category:** 7-SigmaLayer (the record layer — the Q12 successor question, step 2b′ assembly).

## What this closes

`specs/q12-fibre-mechanism-scoping.md` (successor question, corrected 2026-08-26) states the
standing obligation as `DeIsolationFlow.lean`'s: *exhibit a pointer `p = readout ∘ flow(H_int(M))`
whose basins carry the Born measures* — with the scoping that the cell **shapes** are bookkeeping
while the fibre, the rates and the selection are not. The corpus had two `DeIsolationInteraction`
witnesses (`cdfDeIsolationInteraction`, `raceDeIsolationInteraction`), both with **defined** cells:
the pointer *is* the ψ-indexed cell family, and no dynamics carves it.

This module supplies the third witness, and it is the one the obligation asks for in shape:

* ★★ `shearDeIsolationInteraction` — a `DeIsolationInteraction (readyPrep [ψ]) ψ` whose pointer is
  the **total readout of the constructed de-isolation propagator**: `cellPointer` over the
  flow-carved outcome sectors `Ωᵢ = Φ_{0→1}⁻¹(Bᵢ)` of the shear protocol, driven by the
  context-fixed `momentContext` basins.
* ★ `cellPointer_outcomeSector_eq_readout` — that pointer **is** `readout ∘ flow`, literally:
  `pointer x = (readout (Φ_{startTime→readoutTime} x)).getD i₀` for every point. The `p = readout ∘
  flow(H_int(M))` shape is a theorem of the construction, not a gloss.
* ★★ `shear_sector_born` — the dynamical Born on the shear arena: the **flow-carved** outcome
  sector's `readyPrep` measure is the moment-map weight, via
  `measure_outcomeSector_eq_of_correlates` — so `basin_rate` is **discharged from the constructed
  propagator**, not assumed as a hypothesis field and not read off defined cells. (The swap-arena
  analogue is `swap_sector_born`; this is the bankless mirror on `Σ_sel × T²_R`.)
* `readyPrep_selReady`, `readyPrep_selReady_cover` — the selector-and-ready sectors carry the
  moment-map weights and exhaust the canonical ready preparation.

## Where the ψ-dependence lives — the reason this is not bookkeeping

The pointer is **one context-fixed map**: the readout arcs (`pointerArc`), the basins
(`globalBasin (momentContext N)`), and the propagator are all preparation-independent. The state
enters only through the **ontic preparation measure** `readyPrep [ψ] = epistemicMeasure [ψ] ⊗
readyMeasure` — ignorance of the microstate in the prepared region, the Papers A/D typicality
story. The Born identity `readyPrep [ψ] (Ωᵢ) = ‖ψ i‖²` is a *theorem* of that preparation plus the
constructed dynamics. Contrast the CDF/race witnesses, where the ψ-dependence sits inside the
pointer itself.

The basins are not literally `cdfCell` on the abstract `[0,1)` fibre: they are the outcome sectors
on the fibred arena `Σ_sel × T²_R`, whose fibre coordinate is the uniformly-distributed register
the scoping note's `volume_circleCell` reading refers to. Per the 2026-08-26 scoping, that is the
bookkeeping difference; the fibre, the rates (moment map) and the ontic selection (which `Ωᵢ` the
microstate occupies) are exactly what is carried.

## ⚠️ Honest scope — what this does NOT close

1. **The Hamiltonian generation is stated, not formalised** — unchanged from `ShearWitness` item 1.
   The propagator is explicit, measure-preserving, and discharges `CorrelatesOn` /
   `PointerInvariantOn`; that it is the time-`T_M` flow of `H_int(t) = g(t)·(ι+1)·δ·p_R` is a
   symplectic-geometry calculation Mathlib cannot state (no manifold Hamiltonian-flow API; the
   *permanently scoped* row of `reconstruction-status.md` §2a). `basin_rate` is discharged from the
   **constructed propagator**; the "flow of `H_int(M)`" reading carries that standing caveat. Do
   not cite this as a formalised `H_int`. What remains of D1 is exactly that formalisation gap,
   plus the witness-not-derivation caveat below.
2. **The coupling is engineered** (the ontic von Neumann shape, coupled to the outcome index) — a
   witness that a de-isolation interaction with the required readout exists on the arena, not a
   derivation that a physically natural interaction must take this form (`ShearWitness` items 2–3).
3. **The seam.** The everywhere-form of the correlation is impossible
   (`no_everywhere_correlation`); the witness's correlation holds on the selector-and-ready
   sectors, whose union exhausts the ready preparation (`readyPrep_selReady_cover`) — the
   exceptional set is the null seam, exactly where the constraint said it must live.

## References

`specs/q12-fibre-mechanism-scoping.md` (the successor question this answers in its honest form);
`specs/record-layer-plan.md` §3c (step 2b′); `specs/future-work.md`;
`RecordLayer/MomentMapRace.lean` (`DeIsolationInteraction`, `bornRate_eq_momentMap`, the two prior
witnesses); `RecordLayer/DeIsolationFlow.lean` (the obligation, `map_pointer_apply`);
`RecordLayer/ShearWitness.lean` (`shearProtocol`, `selReady`, `shear_correlates`);
`RecordLayer/DynamicBorn.lean` (`basinIndex`, `measure_basinIndex_fibre`);
`RecordLayer/SwapClosure.lean` (`readyPrep`, `swap_sector_born` — the assembly pattern);
`Mathlib/MeasureTheory/CellPointer.lean` (`cellPointer`, `measure_cellPointer_preimage`).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {N : ℕ} [NeZero N]

/-! ### The selector-and-ready sectors under the canonical ready preparation -/

/-- **The canonical ready preparation weights the selector-and-ready sector by the moment map.**
The sector factors as (basin fibre) × (ready arc); the fibre carries the moment-map weight
(`measure_basinIndex_fibre` + `globalBasin_prob`) and the ready arc has full conditional measure. -/
theorem readyPrep_selReady (p : LF4.CPN N) (i : Fin N) :
    readyPrep p (selReady (basinIndex (momentContext N)) i)
      = ENNReal.ofReal (LF4.momentMap p i) := by
  rw [selReady_eq_prod, readyPrep, Measure.prod_prod, measure_basinIndex_fibre,
    globalBasin_prob, momentContext_rate, readyMeasure_readyArc, mul_one]

/-- The selector-and-ready sectors exhaust the canonical ready preparation. -/
theorem readyPrep_selReady_cover (p : LF4.CPN N) :
    ∑ i, readyPrep p (selReady (basinIndex (momentContext N)) i) = 1 := by
  simp_rw [readyPrep_selReady]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => LF4.momentMap_nonneg p i),
    LF4.momentMap_sum_eq_one, ENNReal.ofReal_one]

/-! ### The dynamical Born on the shear arena -/

/-- ★★ **The flow-carved basin carries the moment-map weight.** The outcome sector
`Ωᵢ = Φ_{0→1}⁻¹(Bᵢ)` — the initial states the constructed propagator carries into the pointer arc
for `i` — has `readyPrep` measure exactly the moment-map weight. Via
`measure_outcomeSector_eq_of_correlates`, so the discharged correlation theorem
(`shear_correlates`) is genuinely consumed: the Born weight of the basin is transported by the
interaction, not posited for it. The bankless mirror of `swap_sector_born`. -/
theorem shear_sector_born (p : LF4.CPN N) (i : Fin N) :
    readyPrep p
      ((shearProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector i)
      = ENNReal.ofReal (LF4.momentMap p i) := by
  rw [(shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).measure_outcomeSector_eq_of_correlates
    (measurableSet_selReady _ (measurable_basinIndex (momentContext N)))
    (selReady_pairwiseDisjoint _)
    (readyPrep_selReady_cover p)
    (shear_correlates _ _) i]
  exact readyPrep_selReady p i

/-! ### The pointer IS readout ∘ flow -/

/-- ★ **The total pointer of the outcome sectors is the readout composed with the flow.** For any
measurement protocol, `cellPointer` over the flow-carved outcome sectors computes
`(readout (Φ_{startTime→readoutTime} x)).getD i₀` at every point: the `p = readout ∘ flow` shape
of the step-2b′ obligation, as a pointwise theorem rather than a reading. -/
theorem cellPointer_outcomeSector_eq_readout {Sigma : Type*} [MeasurableSpace Sigma] {K : ℕ}
    (P : MeasurementProtocol Sigma K) (i₀ : Fin K) (x : Sigma) :
    cellPointer P.outcomeSector i₀ x
      = (P.readout (P.evolve P.startTime P.readoutTime x)).getD i₀ := by
  by_cases hx : ∃ i, x ∈ P.outcomeSector i
  · obtain ⟨i, hi⟩ := hx
    rw [cellPointer_eq_of_mem P.outcomeSector_pairwiseDisjoint i₀ hi,
      P.readout_evolve_outcomeSector hi]
    rfl
  · have hmem : x ∈ cellPointer P.outcomeSector i₀ ⁻¹' {i₀} := by
      rw [cellPointer_preimage P.outcomeSector_pairwiseDisjoint i₀ i₀, if_pos rfl]
      right
      simpa [Set.mem_iUnion] using hx
    rcases hro : P.readout (P.evolve P.startTime P.readoutTime x) with _ | j
    · simpa using hmem
    · exact absurd ⟨j, (P.readout_eq_some_iff _ j).mp hro⟩ hx

/-! ### The de-isolation interaction of the constructed flow -/

/-- ★★ **The de-isolation interaction of the constructed flow.** The third
`DeIsolationInteraction` witness — and the first whose pointer is the **readout of the constructed
de-isolation propagator** rather than a defined cell family: the pointer is `cellPointer` over the
flow-carved outcome sectors `Ωᵢ = Φ_{0→1}⁻¹(Bᵢ)` (pointwise `= (readout ∘ Φ_{0→1}).getD i₀`,
`cellPointer_outcomeSector_eq_readout`), and `basin_rate` is **discharged from the dynamics**
(`shear_sector_born`), not assumed.

The pointer, the readout arcs, the basins and the propagator are all context-fixed; ψ enters only
through the ontic preparation measure `readyPrep [ψ]`. ⚠️ The standing caveat is `ShearWitness`
item 1, carried not laundered: the propagator's Hamiltonian generation is stated, not formalised
(no manifold symplectic API in Mathlib) — so read this as *basin_rate discharged from the
constructed de-isolation propagator*, with the `H_int(M)` origin of that propagator the corpus's
permanently-scoped symplectic residue. -/
noncomputable def shearDeIsolationInteraction (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i₀ : Fin N) :
    DeIsolationInteraction (readyPrep (Projectivization.mk ℂ ψ hψ0)) ψ where
  pointer := cellPointer
    ((shearProtocol (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N))).outcomeSector) i₀
  measurable_pointer := measurable_cellPointer
    (fun i => MeasurementProtocol.outcomeSector_measurable _ i)
    (MeasurementProtocol.outcomeSector_pairwiseDisjoint _) i₀
  basin_rate := fun i => by
    refine measure_cellPointer_preimage
      (fun j => MeasurementProtocol.outcomeSector_measurable _ j)
      (MeasurementProtocol.outcomeSector_pairwiseDisjoint _)
      (bornRate_nonneg ψ) (fun j => ?_) (sum_bornRate_unit ψ hψ) i₀ i
    rw [shear_sector_born, ← bornRate_eq_momentMap ψ hψ0 hψ j]

/-- ★ **The instance's pointer is literally `readout ∘ flow`.** Certifies the step-2b′ shape for
the witness above: at every arena point, the pointer reads the record the propagator has created
(`startTime = 0`, `readoutTime = 1` for the shear protocol). -/
theorem shearDeIsolationInteraction_pointer (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i₀ : Fin N) (x : LF4.KSigma N × LF4.KTorus) :
    (shearDeIsolationInteraction ψ hψ0 hψ i₀).pointer x
      = ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).readout
          ((shearProtocol (basinIndex (momentContext N))
            (measurable_basinIndex (momentContext N))).evolve
            (shearProtocol (basinIndex (momentContext N))
              (measurable_basinIndex (momentContext N))).startTime
            (shearProtocol (basinIndex (momentContext N))
              (measurable_basinIndex (momentContext N))).readoutTime x)).getD i₀ :=
  cellPointer_outcomeSector_eq_readout _ i₀ x

/-- **The Born conclusion, from the flow.** The constructed de-isolation propagator's pointer
pushes the canonical ready preparation forward to the Born distribution — outcome `i` with
probability `‖ψ i‖²`. `DeIsolationInteraction.born` applied to the flow-carved witness: the
conditional's antecedent is now populated *by dynamics*. -/
theorem shearDeIsolation_born (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i₀ i : Fin N) :
    ((readyPrep (Projectivization.mk ℂ ψ hψ0)).map
        (shearDeIsolationInteraction ψ hψ0 hψ i₀).pointer) {i}
      = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
  (shearDeIsolationInteraction ψ hψ0 hψ i₀).born i

end CSD.RecordLayer
