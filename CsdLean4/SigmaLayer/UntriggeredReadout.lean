/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.UntriggeredFlow
public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# SigmaLayer/UntriggeredReadout: the record of the untriggered flow is faithful

**Category:** dynamical measurement — the statistics half of
`specs/frozen-base-obstruction-scoping.md` brick 2.

## What this closes, and what it does not

Brick 2 (`SigmaLayer/UntriggeredFlow.lean`) built a single untriggered Hamiltonian flow that
creates a record. It said nothing about whether the record carries the **right statistics** —
its own honest scope flagged that as the gap. This module closes the part of that gap the
chart can express.

* ★ `untriggeredReadout` — the pointer's displacement, `Φ_t(z).x_k − z.x_k`, as a function of
  the initial state. This is what an observer reads.
* ★★ `readoutCell_eq_observable_preimage` — the readout's level sets **are** the measured
  observable's level sets, rescaled by `t`. The pointer partitions the arena exactly the way
  the observable does.
* ★★ `measure_readoutCell` — therefore, for **every** preparation measure `μ`, the probability
  of a pointer reading is the probability the preparation already assigned to the
  corresponding observable value. **The measurement adds no probability of its own.**
* `map_untriggeredReadout` — the same statement as a pushforward: the law of the pointer is
  the law of `t · Â`.
* `untriggeredReadout_injOn_observable` — at `t ≠ 0` the reading *determines* the observable
  value, so the record is exact rather than merely correlated.

## ⚠️ Honest scope — this is the FAITHFULNESS half, not the Born half

**There is no moment map in a Darboux chart.** `shear_sector_born` says the flow-carved sector
carries `ENNReal.ofReal (momentMap p i)` — a statement about `ℂℙ^{N-1}`, Fubini–Study, and the
Kähler moment map, none of which exist on `Chart n`. So this module does **not** prove a Born
weight, and nothing here should be cited as one.

What it proves is the half that *is* chart-expressible and that the Born statement presupposes:
the readout is a faithful transport of the preparation. Born would additionally require the
preparation's own weights to be the moment-map weights, and that is exactly the content
`ℂℙ^{N-1}` supplies and `ℝ^{2n}` cannot. Supplying it is the arena-level work
(⚠️ RESIDUE(R-016)); the choice of interaction **remains open** as a permanent boundary
(⚠️ RESIDUE(R-015)).

**Measure preservation is not proved here either.** The flow is a triangular shear (unit
determinant), so it should preserve the chart volume, and `MeasurementConstraints.lean`'s
necessary conditions all assume that. Establishing it needs the linear-map volume API
transported through the product-of-pi structure, and is not attempted — so the results below
hold for an arbitrary preparation `μ` and say nothing about which `μ` the dynamics preserves.

## References

`specs/frozen-base-obstruction-scoping.md` (brick 2); `specs/future-work.md`;
`SigmaLayer/UntriggeredFlow.lean` (`untriggeredCurve`, `untriggeredCurve_records`);
`RecordLayer/ShearDeIsolation.lean` (`shear_sector_born` — the arena statement this is *not*);
`RecordLayer/MeasurementConstraints.lean` (the necessary conditions that assume measure
preservation).
-/

@[expose] public section

namespace CSD.SigmaLayer

open Set MeasureTheory

variable {n : ℕ}

/-! ### The readout, and the measured observable -/

/-- **The measured observable** `Â(z) = Σᵢ cᵢ xᵢ` — the base quantity the coupling reads. -/
noncomputable def measuredObs (c : Fin n → ℝ) (z : Chart n) : ℝ := ∑ i, c i * z.1 i

/-- **The readout**: the pointer's displacement after time `t`, as a function of the initial
state. This is what an observer of the apparatus actually sees. -/
noncomputable def untriggeredReadout (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (z : Chart n) : ℝ :=
  (untriggeredCurve c k z t).1 k - z.1 k

/-- ★ **The readout is `t` times the observable** — `untriggeredCurve_records`, packaged as a
statement about the readout map rather than about one trajectory. -/
theorem untriggeredReadout_eq (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (z : Chart n) :
    untriggeredReadout c k t z = t * measuredObs c z :=
  untriggeredCurve_records c k z t

theorem untriggeredReadout_apply (c : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    untriggeredReadout c k t = fun z => t * measuredObs c z := by
  funext z; exact untriggeredReadout_eq c k t z

/-! ### ★★ The readout partitions the arena the way the observable does -/

/-- ★★ **The readout's level sets are the observable's level sets, rescaled.** The pointer
carves the arena into exactly the cells the measured quantity does — no finer, no coarser. -/
theorem readoutCell_eq_observable_preimage (c : Fin n → ℝ) (k : Fin n) (t : ℝ) (B : Set ℝ) :
    untriggeredReadout c k t ⁻¹' B = measuredObs c ⁻¹' {a | t * a ∈ B} := by
  ext z
  simp [untriggeredReadout_eq, Set.mem_preimage]

/-- ★★ **The measurement adds no probability of its own.** For *every* preparation `μ`, the
measure of a set of pointer readings is the measure the preparation already assigned to the
corresponding set of observable values. The record transports the preparation; it does not
reweight it. -/
theorem measure_readoutCell (c : Fin n → ℝ) (k : Fin n) (t : ℝ)
    [MeasurableSpace (Chart n)] (μ : Measure (Chart n)) (B : Set ℝ) :
    μ (untriggeredReadout c k t ⁻¹' B) = μ (measuredObs c ⁻¹' {a | t * a ∈ B}) := by
  rw [readoutCell_eq_observable_preimage]

/-- The same statement as a pushforward: **the law of the pointer is the law of `t · Â`.** -/
theorem map_untriggeredReadout (c : Fin n → ℝ) (k : Fin n) (t : ℝ)
    [MeasurableSpace (Chart n)] (μ : Measure (Chart n)) :
    μ.map (untriggeredReadout c k t) = μ.map (fun z => t * measuredObs c z) := by
  rw [untriggeredReadout_apply]

/-! ### ★ The record is exact, not merely correlated -/

/-- ★ **At `t ≠ 0` the reading determines the observable value.** Two initial states producing
the same pointer displacement had the same measured value — so the record is exact, and the
observer loses nothing by reading the pointer instead of the system. -/
theorem untriggeredReadout_injOn_observable (c : Fin n → ℝ) (k : Fin n) {t : ℝ} (ht : t ≠ 0)
    {z z' : Chart n} (h : untriggeredReadout c k t z = untriggeredReadout c k t z') :
    measuredObs c z = measuredObs c z' := by
  rw [untriggeredReadout_eq, untriggeredReadout_eq] at h
  exact mul_left_cancel₀ ht h

/-- The converse, which needs no hypothesis: equal observable values give equal readings. So at
`t ≠ 0` the readout and the observable have *exactly* the same level sets. -/
theorem untriggeredReadout_congr (c : Fin n → ℝ) (k : Fin n) (t : ℝ) {z z' : Chart n}
    (h : measuredObs c z = measuredObs c z') :
    untriggeredReadout c k t z = untriggeredReadout c k t z' := by
  rw [untriggeredReadout_eq, untriggeredReadout_eq, h]

/-- **Non-degeneracy**: the readout is not constant, provided the coupling is non-trivial and
the interaction has actually run. Without this the "record" could be vacuous. -/
theorem untriggeredReadout_ne (c : Fin n → ℝ) (k : Fin n) {t : ℝ} (ht : t ≠ 0)
    {z z' : Chart n} (h : measuredObs c z ≠ measuredObs c z') :
    untriggeredReadout c k t z ≠ untriggeredReadout c k t z' := by
  intro hcon
  exact h (untriggeredReadout_injOn_observable c k ht hcon)

end CSD.SigmaLayer
