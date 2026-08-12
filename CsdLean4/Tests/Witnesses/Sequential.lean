/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.SequentialMeasurement
public import CsdLean4.SigmaLayer.DegenerateLuders
public import CsdLean4.SigmaLayer.DynamicBorn
public import CsdLean4.LF4.ObservableFlow

/-!
# WS-G witness: sequential measurement on a concrete superposition

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-G).

The production repeatability theorems (`csd_repeatability_same` / `_other`,
riding `swap_luders_born` — the rank-one Lüders update through the record
dynamics) take the joint preparation `μ12` abstractly, with a positivity
hypothesis `hpos` on the outcome sector. This module supplies the concrete
two-step experiment:

* **Preparation**: the epistemic state at the explicit *superposition* ray
  `[e₀ + e₁]` (`obsWitnessVec`), with a ready register
  (`(epistemicMeasure …).prod (readyMeasure N)`).
  `superposition_ne_vertex` is the load-bearing nontriviality: the prepared
  ray is **not** the collapsed vertex, so the second-step certainty below is
  produced by the measurement *update*, not by having prepared an eigenstate.
* **First measurement**: outcome `obsIdx0` occurs with nonzero probability —
  `superposition_outcome_pos` discharges `hpos` concretely (the sector
  contains the selector-and-ready cylinder, whose base mass is the positive
  Born weight `momentMap [e₀+e₁] 0` and whose fibre mass is the ready-arc
  volume; the `vertex_outcome_pos` route, at a non-vertex preparation).
* **Second measurement, through the production update machinery**:
  `sequential_repeatability_concrete` — conditioned on the first outcome, the
  same-basis repeat gives the recorded outcome with probability `1` and every
  other outcome with probability `0`.

**Anti-duplication scope.** The update and its statistics are entirely the
production `csd_repeatability_same`/`_other`; the witness contribution is the
concrete preparation with `hpos` discharged and the non-vertex clause.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open CSD.LF4 CSD.RecordLayer CSD.Empirical.CSDBridge.SequentialMeasurement

namespace CSD
namespace Tests
namespace Witnesses

variable {N : ℕ}

/-- **Nontriviality: the prepared superposition is not the collapsed
vertex.** `[e₀ + e₁] ≠ [e₀]`, separated by the Born weight at index `1`
(`momentMap` is a function of the ray: positive at the superposition, zero at
the vertex by `momentMap_vertex`). -/
theorem superposition_ne_vertex [NeZero N] (hN : 1 < N) :
    Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN)
      ≠ vertexPoint (obsIdx0 hN) := by
  intro h
  have h1 : 0 < LF4.momentMap
      (Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN)) (obsIdx1 hN) := by
    rw [LF4.momentMap_mk _ (obsWitnessVec_ne_zero hN)]
    have ha : (0 : ℝ) < ‖obsWitnessVec hN (obsIdx1 hN)‖ := by
      rw [obsWitnessVec_apply_one]
      norm_num
    have hb : (0 : ℝ) < ‖obsWitnessVec hN‖ :=
      norm_pos_iff.mpr (obsWitnessVec_ne_zero hN)
    positivity
  rw [h, momentMap_vertex, if_neg (obsIdx0_ne_obsIdx1 hN).symm] at h1
  exact lt_irrefl 0 h1

/-- **The first-step positivity, discharged at the concrete superposition.**
Outcome `obsIdx0` has nonzero probability under the epistemic preparation of
`[e₀ + e₁]` with a ready register: the selector-and-ready cylinder sits inside
the outcome sector (`shear_correlates`), its base mass is the positive Born
weight, its fibre mass the ready-arc volume. -/
theorem superposition_outcome_pos [NeZero N] (hN : 1 < N) :
    ((epistemicMeasure
        (Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN))).prod
        (readyMeasure N))
      ((shearProtocol (basinIndex (momentContext N))
        (measurable_basinIndex (momentContext N))).outcomeSector (obsIdx0 hN)) ≠ 0 := by
  classical
  set p := Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN) with hp
  have hsub : selReady (basinIndex (momentContext N)) (obsIdx0 hN)
      ⊆ (shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector (obsIdx0 hN) :=
    shear_correlates (basinIndex (momentContext N))
      (measurable_basinIndex (momentContext N)) (obsIdx0 hN)
  have hprod : selReady (basinIndex (momentContext N)) (obsIdx0 hN)
      = {x : LF4.KSigma N | basinIndex (momentContext N) x = obsIdx0 hN} ×ˢ readyArc N := by
    ext x
    simp [selReady, Set.mem_prod]
  have hbase : epistemicMeasure p
      {x : LF4.KSigma N | basinIndex (momentContext N) x = obsIdx0 hN} ≠ 0 := by
    have heq : {x : LF4.KSigma N | basinIndex (momentContext N) x = obsIdx0 hN}
        = basinIndex (momentContext N) ⁻¹' {obsIdx0 hN} := rfl
    rw [heq, measure_basinIndex_fibre, globalBasin_prob, momentContext_rate]
    have hposm : 0 < LF4.momentMap p (obsIdx0 hN) := by
      rw [hp, LF4.momentMap_mk _ (obsWitnessVec_ne_zero hN)]
      have h1 : (0 : ℝ) < ‖obsWitnessVec hN (obsIdx0 hN)‖ := by
        rw [obsWitnessVec_apply_zero]
        norm_num
      have h2 : (0 : ℝ) < ‖obsWitnessVec hN‖ :=
        norm_pos_iff.mpr (obsWitnessVec_ne_zero hN)
      positivity
    simp [ENNReal.ofReal_eq_zero, not_le, hposm]
  have hready : readyMeasure N (readyArc N) ≠ 0 := by
    rw [readyMeasure, ProbabilityTheory.cond_apply measurableSet_readyArc, Set.inter_self]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      volume_readyArc_ne_zero
  intro h0
  have hle : ((epistemicMeasure p).prod (readyMeasure N))
      (selReady (basinIndex (momentContext N)) (obsIdx0 hN))
      ≤ ((epistemicMeasure p).prod (readyMeasure N))
        ((shearProtocol (basinIndex (momentContext N))
          (measurable_basinIndex (momentContext N))).outcomeSector (obsIdx0 hN)) :=
    measure_mono hsub
  rw [h0, le_zero_iff, hprod, Measure.prod_prod] at hle
  exact absurd hle (mul_ne_zero hbase hready)

/-- **WS-G headline: repeatability on the concrete superposition, through the
production update.** Prepare `[e₀ + e₁]` (a genuine superposition —
`superposition_ne_vertex`), measure in the computational basis, condition on
outcome `0` (nonzero probability — `superposition_outcome_pos`), measure
again in the same basis: the recorded outcome recurs with probability `1`,
and every other outcome has probability `0`. Instantiates
`csd_repeatability_same` / `csd_repeatability_other` (the rank-one Lüders
update through the record dynamics). -/
theorem sequential_repeatability_concrete [NeZero N] (hN : 1 < N) :
    (postEnsemble
        ((epistemicMeasure
          (Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN))).prod
          (readyMeasure N)) (obsIdx0 hN)
        ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹'
          globalBasin (momentContext N) (obsIdx0 hN)) = 1)
      ∧ ∀ j : Fin N, j ≠ obsIdx0 hN →
          postEnsemble
            ((epistemicMeasure
              (Projectivization.mk ℂ (obsWitnessVec hN) (obsWitnessVec_ne_zero hN))).prod
              (readyMeasure N)) (obsIdx0 hN)
            ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹'
              globalBasin (momentContext N) j) = 0 :=
  ⟨csd_repeatability_same _ _ (superposition_outcome_pos hN),
    fun _ hj => csd_repeatability_other _ _ (superposition_outcome_pos hN) hj⟩

end Witnesses
end Tests
end CSD
