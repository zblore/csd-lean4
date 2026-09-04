/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.Measurement

/-!
# SigmaLayer/BasisMeasurement: the record layer for an arbitrary observable (MD-1)

**Category:** 7-SigmaLayer (the record layer — arbitrary measurement context).

The record layer of `RecordLayer/Measurement.lean` is stated in the computational basis
(`bornRate ψ i = ‖ψ i‖²`). This file generalises it to an **arbitrary observable** — any orthonormal
basis `b : OrthonormalBasis (Fin n) ℂ E` of a complex inner-product space `E` — with the outcome
probability the standard Born weight `‖⟨bᵢ, ψ⟩‖²`. The generalisation is a change of basis: measuring
`ψ` in context `b` is measuring the coordinate representation `b.repr ψ` in the computational basis, so
every record-layer theorem transports along the isometry `b.repr`.

* `bornRateBasis` / `bornRateBasis_eq_inner_sq` — the Born rate of outcome `i` in context `b` is
  `‖⟨bᵢ, ψ⟩‖²`;
* `sum_bornRateBasis_unit` — the rates form a probability vector on a unit state;
* `bornMeasurementBasis` / `bornMeasurementBasis_prob` — the record-layer measurement in context `b`,
  with outcome probability `‖⟨bᵢ, ψ⟩‖²`.

Foundational-triple, no `sorry`.

## References
`RecordLayer/Measurement.lean` (the computational-basis record layer, `bornMeasurement`); Mathlib
`OrthonormalBasis.repr` (the isometry to `EuclideanSpace`).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The Born rate for a general observable** (orthonormal basis `b`): the squared overlap
`‖⟨bᵢ, ψ⟩‖²`, realised as the computational-basis rate of the coordinate representation `b.repr ψ`. -/
noncomputable def bornRateBasis (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) (i : Fin n) : ℝ :=
  bornRate (b.repr ψ) i

/-- The general Born rate is the standard squared overlap `‖⟨bᵢ, ψ⟩‖²`. -/
theorem bornRateBasis_eq_inner_sq (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) (i : Fin n) :
    bornRateBasis b ψ i = ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [bornRateBasis, bornRate, b.repr_apply_apply]

/-- The coordinate representation is norm-preserving (`b.repr` is an isometry). -/
theorem norm_repr_eq (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) : ‖b.repr ψ‖ = ‖ψ‖ :=
  b.repr.norm_map ψ

/-- **The general Born rates form a probability vector on a unit state.** -/
theorem sum_bornRateBasis_unit (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) (hψ : ‖ψ‖ = 1) :
    ∑ i, bornRateBasis b ψ i = 1 :=
  sum_bornRate_unit (b.repr ψ) (by rw [norm_repr_eq]; exact hψ)

/-- **The record-layer measurement in a general observable context** `b`: the computational-basis
Born measurement of the coordinate representation `b.repr ψ`. -/
noncomputable def bornMeasurementBasis (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) (t : OnticTime) :
    Measurement n :=
  Measurement.bornMeasurement (b.repr ψ) t

/-- **The basins set the probabilities = Born, in any observable context.** The outcome-`i`
probability of the measurement in context `b` is exactly `‖⟨bᵢ, ψ⟩‖²`. -/
theorem bornMeasurementBasis_prob (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (i : Fin n) (t : OnticTime) :
    (bornMeasurementBasis b ψ t).prob i = ENNReal.ofReal (‖inner ℂ (b i) ψ‖ ^ 2) := by
  rw [bornMeasurementBasis,
    Measurement.bornMeasurement_prob (b.repr ψ) (by rw [norm_repr_eq]; exact hψ) i t,
    b.repr_apply_apply]

end CSD.RecordLayer
